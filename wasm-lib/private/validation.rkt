#lang racket/base

(require (for-syntax racket/base)
         (prefix-in ra: data/ralist)
         racket/contract
         racket/list
         racket/match
         (submod racket/performance-hint begin-encourage-inline)
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
        (validate-globals)
        (validate-elements (mod-elements m))
        (validate-datas (mod-datas m))
        (validate-start (mod-start m))
        (validate-functions (mod-functions m) (mod-codes m))
        (validate-exports (mod-exports m)))
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

(define (validate-exports c exports)
  (begin0 c
    (for ([e (in-vector exports)])
      (match e
        [(export _ (funcidx   idx)) (func-ref c e idx)]
        [(export _ (tableidx  idx)) (table-ref c e idx)]
        [(export _ (memidx    idx)) (memory-ref c e idx)]
        [(export _ (globalidx idx)) (global-ref c e idx)]))))

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
    (match (ctx-tables c)
      [(vector) (void)]
      [(vector lim) (validate-limits (tableidx 0) lim max-tblsize)]
      [(vector _ lims ...) (raise-validation-error lims "only one table allowed")])))

(define (validate-memories c)
  (begin0 c
    (match (ctx-memories c)
      [(vector) (void)]
      [(vector lim) (validate-limits (memidx 0) lim max-memsize)]
      [(vector _ lims ...) (raise-validation-error lims "only one memory block allowed")])))

(define (validate-globals c)
  (begin0 c
    (for ([g (in-vector (ctx-globals c))])
      (match g
        [(global (globaltype vt _) (vector instr))
         (unless (instr-constant? c instr)
           (raise-validation-error g "global definition instructions must be constant"))
         (check-types g (list vt) (functype-results (instruction-type instr)) "result ")]

        [(global _ _)
         (raise-validation-error g "global definitions require exactly one instruction")]))))

(define (validate-elements c elements)
  (begin0 c
    (for ([e (in-vector elements)])
      (match e
        [(element idx (vector instr) funcs)
         (table-ref c e idx)
         (unless (instr-constant? c instr)
           (raise-validation-error e "element definition instructions must be constant"))
         (check-types e (list i32) (functype-results (instruction-type instr)) "result ")
         (for ([f (in-vector funcs)])
           (func-ref c e (funcidx-idx f)))]

        [(element _ _ _)
         (raise-validation-error e "element definitions require exactly one instruction")]))))

(define (validate-datas c datas)
  (begin0 c
    (for ([d (in-vector datas)])
      (match d
        [(data idx (vector instr) _)
         (memory-ref c d idx)
         (unless (instr-constant? c instr)
           (raise-validation-error d "data definition instructions must be constant"))
         (check-types d (list i32) (functype-results (instruction-type instr)) "result ")]

        [(data _ _ _)
         (raise-validation-error d "data definitions require exactly one instruction")]))))

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

(define (validate-code c who instrs)
  (define stack
    (for/fold ([stack null])
              ([instr (in-vector instrs)])
      (validate-instr c (cons instr who) stack instr)))

  (check-types who (ctx-return c) stack "result "))

(define (validate-instr c who stack instr)
  (match instr
    ;; Control Instructions
    ;; [t1*] [t2*]
    [(instr:unreachable)
     (ctx-return c)]

    ;; [t1* t*] -> [t2*]
    [(instr:br lbl)
     (define ft (label-ref c who lbl))
     (apply keep who stack (functype-results ft))]

    ;; [t* i32] -> [t*]
    [(instr:br_if lbl)
     (define ft (label-ref c who lbl))
     (define s (pop who stack i32))
     (begin0 s
       (check-types who (functype-results ft) s))]

    ;; [t1* t* i32] -> [t2*]
    [(instr:br_table tbl lN)
     (define ft (label-ref c who lN))
     (for ([l (in-vector tbl)])
       (check-types who
                    (functype-results ft)
                    (functype-results (label-ref c who l))))
     (apply keep who (pop who stack i32) (functype-results ft))]

    ;; [t1* t*] -> [t2*]
    [(instr:return)
     (apply keep who stack (ctx-return c))]

    ;; [t1*] -> [t2*]
    [(instr:block (typeidx idx) block-code)
     (validate-instr c who stack (instr:block (type-ref c who idx) block-code))]

    ;; [t1*] -> [t2*]
    [(instr:block ft block-code)
     (when block-code (validate-block c who ft block-code))
     (apply push stack (functype-results ft))]

    ;; [t1*] -> [t2*]
    [(instr:loop (typeidx idx) block-code)
     (validate-instr c who stack (instr:loop (type-ref c who idx) block-code))]

    ;; [t1*] -> [t2*]
    [(instr:loop ft block-code)
     (when block-code (validate-block c who ft block-code))
     (apply push stack (functype-results ft))]

    ;; [t1* i32] -> [t2*]
    [(instr:if (typeidx idx) then-code else-code)
     (validate-instr c who stack (instr:if (type-ref c who idx) then-code else-code))]

    ;; [t1* i32] -> [t2*]
    [(instr:if ft then-code else-code)
     (define s (pop who stack i32))
     (when then-code (validate-block c who ft then-code))
     (when else-code (validate-block c who ft else-code))
     (apply push s (functype-results ft))]

    ;; [t1*] -> [t2*]
    [(instr:call idx)
     (validate-type who stack (func-ref c who idx))]

    ;; [t1* i32] -> [t2*]
    [(instr:call_indirect idx tblidx)
     (match (table-ref c who tblidx)
       [(tabletype (? funcref?) _)
        (validate-type who (pop who stack i32) (type-ref c who idx))]

       [_
        (raise-validation-error who "table elemtype is not funcref")])]

    ;; Variable Instructions
    [(instr:local.get idx)
     (push stack (local-ref c who idx))]

    [(instr:local.set idx)
     (pop who stack (local-ref c who idx))]

    [(instr:local.tee idx)
     (define vt (local-ref c who idx))
     (push (pop who stack vt) vt)]

    [(instr:global.get idx)
     (define g (global-ref c who idx))
     (define gt (global-type g))
     (push stack (globaltype-valtype gt))]

    [(instr:global.set idx)
     (define g (global-ref c who idx))
     (define gt (global-type g))
     (unless (globaltype-mutable? gt)
       (raise-validation-error who "cannot mutate constant"))
     (pop who stack (globaltype-valtype gt))]

    ;; Memory Instructions
    [(or (instr:i32.load8_s arg)
         (instr:i32.load8_u arg)
         (instr:i64.load8_s arg)
         (instr:i64.load8_u arg)
         (instr:i32.store8 arg)
         (instr:i64.store8 arg))
     (memory-ref c who 0)
     (check-alignment who arg 8)
     (validate-type who stack (instruction-type instr))]

    [(or (instr:i32.load16_s arg)
         (instr:i32.load16_u arg)
         (instr:i64.load16_s arg)
         (instr:i64.load16_u arg)
         (instr:i32.store16 arg)
         (instr:i64.store16 arg))
     (memory-ref c who 0)
     (check-alignment who arg 16)
     (validate-type who stack (instruction-type instr))]

    [(or (instr:i32.load arg)
         (instr:f32.load arg)
         (instr:i64.load32_s arg)
         (instr:i64.load32_u arg)
         (instr:i32.store arg)
         (instr:f32.store arg)
         (instr:i64.store32 arg))
     (memory-ref c who 0)
     (check-alignment who arg 32)
     (validate-type who stack (instruction-type instr))]

    [(or (instr:i64.load arg)
         (instr:f64.load arg)
         (instr:i64.store arg)
         (instr:f64.store arg))
     (memory-ref c who 0)
     (check-alignment who arg 64)
     (validate-type who stack (instruction-type instr))]

    [(instr:memory.size idx)
     (memory-ref c who idx)
     (validate-type who stack (instruction-type instr))]

    [(instr:memory.grow idx)
     (memory-ref c who idx)
     (validate-type who stack (instruction-type instr))]

    ;; Everything Else
    [_
     (validate-type who stack (instruction-type instr))]))

(begin-encourage-inline
  (define (push s . vts)
    (append vts s))

  (define (pop* who s . vts)
    (define-values (ets remaining-stack)
      (split-at s (min (length vts)
                       (length s))))
    (begin0 (values ets remaining-stack)
      (check-types who vts ets)))

  (define (pop who s . vts)
    (define-values (_ remaining-stack)
      (apply pop* who s vts))
    remaining-stack)

  ;; [t*    ] -> [   ]
  ;; [t* a  ] -> [a  ]
  ;; [t* a b] -> [a b]
  (define (keep who s . vts)
    (define-values (ets _)
      (apply pop* who s vts))
    ets)

  (define (validate-type who s ft)
    (define remaining-stack
      (apply pop who s (functype-params ft)))
    (append (functype-results ft) remaining-stack))

  (define (check-alignment who arg bits)
    (define align (memarg-align arg))
    (unless (<= (expt 2 align) (quotient bits 8))
      (raise-validation-error who "invalid alignment ~v" align))))

(define (check-types who expected found [context ""])
  (unless (= (length expected) (length found))
    (raise-validation-error who
                            "~aarity error~n  expected: [~a]~n  found: [~a]"
                            context
                            (pp-ts expected)
                            (pp-ts found)))

  (for ([(et idx) (in-indexed expected)]
        [ft (in-list found)]
        #:unless (type-unify et ft))
    (raise-validation-error who
                            "~atype error~n  expected: ~v~n  found: ~v~n  at index: ~a~n  in: [~a]"
                            context et ft idx (pp-ts found))))

(define (pp-ts ts)
  (call-with-output-string
   (lambda (out)
     (for ([(t idx) (in-indexed (reverse ts))])
       (print t out)
       (unless (= idx (sub1 (length ts)))
         (display " " out))))))

(define (make-locals t c)
  (apply
   vector-append
   (list->vector (functype-params t))
   (for/list ([l (in-vector (code-locals c))])
     (make-vector (locals-n l) (locals-valtype l)))))

(define (instr-constant? c i)
  (match i
    [(instr:global.get idx)
     (not (globaltype-mutable? (global-ref c i idx)))]
    [(instr:i32.const _) #t]
    [(instr:f32.const _) #t]
    [(instr:i64.const _) #t]
    [(instr:f64.const _) #t]
    [_ #f]))


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

(define ((make-ref what accessor len-fn ref-fn) ob who idx)
  (define xs (accessor ob))
  (define max-idx (sub1 (len-fn xs)))
  (when (> idx max-idx)
    (if (> max-idx 0)
        (raise-validation-error who "~a index out of bounds (max: ~a)" what max-idx)
        (raise-validation-error who "~a index out of bounds (no items)" what)))
  (ref-fn xs idx))

(define-syntax-rule (define-ref name what accessor len-fn ref-fn)
  (define name (make-ref what accessor len-fn ref-fn)))

(define-syntax-rule (define-vector-refs [name what accessor] ...)
  (begin (define-ref name what accessor vector-length vector-ref) ...))

(define-vector-refs
  [type-ref "type" ctx-types]
  [func-ref "function" ctx-functions]
  [table-ref "table" ctx-tables]
  [memory-ref "memory" ctx-memories]
  [global-ref "global" ctx-globals]
  [local-ref "local" ctx-locals])

(define-ref label-ref "label" ctx-labels ra:length ra:list-ref)
