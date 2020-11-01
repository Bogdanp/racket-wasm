#lang racket/base

(require (for-syntax racket/base)
         (prefix-in ra: data/ralist)
         racket/contract
         racket/list
         racket/match
         racket/port
         racket/vector
         threading
         "core.rkt")

(provide
 mod-valid?)

(define/contract (mod-valid? m)
  (-> mod? (values boolean? (or/c #f string?)))
  (with-handlers ([exn:fail:validation?
                   (lambda (e)
                     (values #f (format-error e)))])
    (~> (make-ctx m)
        (validate-imports (mod-imports m))
        (validate-tables)
        (validate-memories)
        (validate-start (mod-start m))
        (validate-functions (mod-functions m) (mod-codes m)))
    (values #t #f)))

(define (format-error e)
  (with-output-to-string
    (lambda ()
      (displayln (exn-message e))
      (define whos
        (match (exn:fail:validation-who e)
          [(list whos ...) whos]
          [who (list who)]))
      (printf "  at: ~v" (car whos))
      (for ([who (in-list (cdr whos))])
        (newline)
        (printf "  within: ~.v" who)))))

(define (validate-imports c imports)
  (for/fold ([functions null]
             [tables    null]
             [memories  null]
             [globals   null]
             #:result (let ([functions (list->vector (reverse functions))]
                            [tables    (list->vector (reverse tables))]
                            [memories  (list->vector (reverse memories))]
                            [globals   (list->vector (reverse globals))])
                        (struct-copy ctx c
                                     [functions (vector-append functions (ctx-functions c))]
                                     [tables    (vector-append tables    (ctx-tables c))]
                                     [memories  (vector-append memories  (ctx-memories c))]
                                     [globals   (vector-append globals   (ctx-globals c))])))
            ([i (in-vector imports)])
    (match i
      [(import _ _ (typeidx idx))      (values (cons (type-ref c i idx) functions) tables memories globals)]
      [(import _ _ (? tabletype?  tt)) (values functions (cons tt tables) memories globals)]
      [(import _ _ (? memtype?    mt)) (values functions tables (cons mt memories) globals)]
      [(import _ _ (? globaltype? gt)) (values functions tables memories (cons gt globals))])))

(define max-memsize (expt 2 16))
(define max-tblsize (expt 2 32))

(define (validate-limits who l k)
  (match l
    [(limits lo #f) #:when (> lo k)  (raise-validation-error who "min exceeds ~a" k)]
    [(limits _  hi) #:when (> hi k)  (raise-validation-error who "max exceeds ~a" k)]
    [(limits lo hi) #:when (> lo hi) (raise-validation-error who "min greater than max")]
    [_ (void)]))

(define (validate-tables c)
  (begin0 c
    (for ([(t idx) (in-indexed (ctx-tables c))])
      (validate-limits (tableidx idx) t max-tblsize))))

(define (validate-memories c)
  (begin0 c
    (for ([(m idx) (in-indexed (ctx-memories c))])
      (validate-limits (memidx idx) m max-memsize))))

(define (validate-start c s)
  (define who "start function")
  (match s
    [#f c]
    [(funcidx idx)
     (match (func-ref c who idx)
       [(functype '() '()) c]
       [(functype params results)
        (raise-validation-error who
                                "start function must have type [] -> []~n  found: [~a] -> [~a]"
                                (pp-ts params)
                                (pp-ts results))])]))

(define (validate-functions c functions codes)
  (begin0 c
    (for ([(tidx fidx) (in-indexed functions)]
          [code (in-vector codes)])
      (define who (funcidx fidx))
      (define here (list who))
      (define type (type-ref c who tidx))
      (define func-c
        (struct-copy ctx c
                     [locals (make-locals type code)]
                     [labels (ra:list type)]
                     [return (functype-results type)]))
      (validate-code func-c here (code-instrs code)))))

(define (validate-block c who type instrs)
  (define block-c
    (struct-copy ctx c
                 [labels (ra:cons type (ctx-labels c))]
                 [return (functype-results type)]))
  (validate-code block-c who instrs))

(define (validate-code c where instrs)
  (define stack null)

  (define (push! . vts)
    (set! stack (append vts stack)))

  (define (pop! who . vts)
    (define-values (ets remaining-stack)
      (split-at stack (min (length vts)
                           (length stack))))
    (check-types who vts ets)
    (begin0 ets
      (set! stack remaining-stack)))

  (define (tc! who ft)
    (apply pop! who (functype-params ft))
    (apply push! (functype-results ft)))

  ;; [t*    ] -> [   ]
  ;; [t* a  ] -> [a  ]
  ;; [t* a b] -> [a b]
  (define (keep! who . vts)
    (set! stack (apply pop! who vts)))

  (define (check! who instr)
    #;(printf "instr: ~.s stack: ~a~n" instr stack)
    (match instr
      ;; Control Instructions
      ;; [t1*] [t2*]
      [(instr:unreachable)
       (set! stack (ctx-return c))]

      ;; [t1* t*] -> [t2*]
      [(instr:br lbl)
       (define ft (label-ref c who lbl))
       (apply keep! who (functype-results ft))]

      ;; [t* i32] -> [t*]
      [(instr:br_if lbl)
       (pop! who i32)
       (define ft (label-ref c who lbl))
       (check-types who (functype-results ft) stack)]

      ;; [t1* t* i32] -> [t2*]
      [(instr:br_table tbl lN)
       (pop! who i32)
       (define ft (label-ref c who lN))
       (for ([l (in-vector tbl)])
         (check-types who
                      (functype-results ft)
                      (functype-results (label-ref c who l))))
       (apply keep! who (functype-results ft))]

      ;; [t1* t*] -> [t2*]
      [(instr:return)
       (apply keep! who (ctx-return c))]

      ;; [t1*] -> [t2*]
      [(instr:block (typeidx idx) block-code)
       (define ft (type-ref c who idx))
       (check! who (instr:block ft block-code))]

      ;; [t1*] -> [t2*]
      [(instr:block ft block-code)
       (when block-code (validate-block c who ft block-code))
       (apply push! (functype-results ft))]

      ;; [t1*] -> [t2*]
      [(instr:loop (typeidx idx) block-code)
       (define ft (type-ref c who idx))
       (check! who (instr:loop ft block-code))]

      ;; [t1*] -> [t2*]
      [(instr:loop ft block-code)
       (when block-code (validate-block c who ft block-code))
       (apply push! (functype-results ft))]

      ;; [t1* i32] -> [t2*]
      [(instr:if (typeidx idx) then-code else-code)
       (define ft (type-ref c who idx))
       (check! who (instr:if ft then-code else-code))]

      ;; [t1* i32] -> [t2*]
      [(instr:if ft then-code else-code)
       (pop! who i32)
       (when then-code (validate-block c who ft then-code))
       (when else-code (validate-block c who ft else-code))
       (apply push! (functype-results ft))]

      ;; [t1*] -> [t2*]
      [(instr:call idx)
       (tc! who (func-ref c who idx))]

      ;; [t1* i32] -> [t2*]
      [(instr:call_indirect idx tblidx)
       (match (table-ref c who tblidx)
         [(tabletype (? funcref?) _)
          (pop! who i32)
          (tc! who (type-ref c who idx))]

         [_
          (raise-validation-error who "table elemtype is not funcref")])]

      ;; Variable Instructions
      [(instr:local.get idx)
       (push! (local-ref c who idx))]

      [(instr:local.set idx)
       (pop! who (local-ref c who idx))]

      [(instr:local.tee idx)
       (define vt (local-ref c who idx))
       (pop! who vt)
       (push! vt)]

      [(instr:global.get idx)
       (define g (global-ref c who idx))
       (define gt (global-type g))
       (push! (globaltype-valtype gt))]

      [(instr:global.set idx)
       (define g (global-ref c who idx))
       (define gt (global-type g))
       (unless (globaltype-mutable? gt)
         (raise-validation-error who "cannot mutate constant"))
       (pop! who (globaltype-valtype gt))]

      ;; Memory Instructions
      [(or (instr:i32.load8_s arg)
           (instr:i32.load8_u arg)
           (instr:i64.load8_s arg)
           (instr:i64.load8_u arg)
           (instr:i32.store8 arg)
           (instr:i64.store8 arg))
       (memory-ref c who 0)
       (check-alignment who arg 8)
       (tc! who (instruction-type instr))]

      [(or (instr:i32.load16_s arg)
           (instr:i32.load16_u arg)
           (instr:i64.load16_s arg)
           (instr:i64.load16_u arg)
           (instr:i32.store16 arg)
           (instr:i64.store16 arg))
       (memory-ref c who 0)
       (check-alignment who arg 16)
       (tc! who (instruction-type instr))]

      [(or (instr:i32.load arg)
           (instr:f32.load arg)
           (instr:i64.load32_s arg)
           (instr:i64.load32_u arg)
           (instr:i32.store arg)
           (instr:f32.store arg)
           (instr:i64.store32 arg))
       (memory-ref c who 0)
       (check-alignment who arg 32)
       (tc! who (instruction-type instr))]

      [(or (instr:i64.load arg)
           (instr:f64.load arg)
           (instr:i64.store arg)
           (instr:f64.store arg))
       (memory-ref c who 0)
       (check-alignment who arg 64)
       (tc! who (instruction-type instr))]

      [(instr:memory.size idx)
       (memory-ref c who idx)
       (tc! who (instruction-type instr))]

      [(instr:memory.grow idx)
       (memory-ref c who idx)
       (tc! who (instruction-type instr))]

      ;; Everything Else
      [_ (tc! who (instruction-type instr))]))

  (for ([instr (in-vector instrs)])
    (check! (cons instr where) instr))

  (check-types where (ctx-return c) stack "result "))

(define (make-locals t c)
  (apply
   vector-append
   (list->vector (functype-params t))
   (for/list ([l (in-vector (code-locals c))])
     (make-vector (locals-n l) (locals-valtype l)))))

(define (check-alignment who arg bits)
  (define align (memarg-align arg))
  (unless (<= (expt 2 align) (quotient bits 8))
    (raise-validation-error who "invalid alignment ~v" align)))

(define (check-types who expected found [context ""])
  (cond
    [(= (length expected) (length found))
     (for ([(et idx) (in-indexed expected)]
           [ft (in-list found)]
           #:unless (type-unify et ft))
       (raise-validation-error who
                               "~atype error~n  expected: ~v~n  found: ~v~n  at index: ~a~n  in: [~a]"
                               context et ft idx (pp-ts found)))]

    [else
     (raise-validation-error who
                             "~aarity error~n  expected: [~a]~n  found: [~a]"
                             context
                             (pp-ts expected)
                             (pp-ts found))]))

(define (pp-ts ts)
  (call-with-output-string
   (lambda (out)
     (for ([(t idx) (in-indexed (reverse ts))])
       (print t out)
       (unless (= idx (sub1 (length ts)))
         (display " " out))))))


;; validation error ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct exn:fail:validation exn:fail (who)
  #:transparent)

(define (raise-validation-error who message . args)
  (raise (exn:fail:validation
          (apply format message args)
          (current-continuation-marks)
          who)))


;; context ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct ctx (types functions tables memories globals locals labels return)
  #:transparent)

(define (make-ctx m)
  (define c
    (ctx (mod-types m)
         (vector)
         (mod-tables m)
         (mod-memories m)
         (mod-globals m)
         (vector)
         (ra:list)
         (list)))
  (struct-copy ctx c [functions (for/vector ([(tidx fidx) (in-indexed (mod-functions m))])
                                  (define who (funcidx fidx))
                                  (type-ref c who tidx))]))


;; accessors ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ((make-ref accessor len-fn ref-fn) ob who idx)
  (define xs (accessor ob))
  (define max-idx (sub1 (len-fn xs)))
  (when (> idx max-idx)
    (raise-validation-error who "index out of bounds (max: ~a)" max-idx))
  (ref-fn xs idx))

(define-syntax-rule (define-ref name accessor len-fn ref-fn)
  (define name (make-ref accessor len-fn ref-fn)))

(define-syntax-rule (define-vector-refs [name accessor] ...)
  (begin (define-ref name accessor vector-length vector-ref) ...))

(define-vector-refs
  [type-ref ctx-types]
  [func-ref ctx-functions]
  [table-ref ctx-tables]
  [memory-ref ctx-memories]
  [global-ref ctx-globals]
  [local-ref ctx-locals])

(define-ref label-ref ctx-labels ra:length ra:list-ref)
