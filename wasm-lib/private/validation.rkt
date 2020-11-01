#lang racket/base

(require (for-syntax racket/base)
         (prefix-in ra: data/ralist)
         racket/contract
         racket/list
         racket/match
         racket/port
         racket/vector
         "core.rkt")

(provide
 mod-valid?)

(define/contract (mod-valid? m)
  (-> mod? (values boolean? (or/c #f string?)))
  (with-handlers ([exn:fail:validation?
                   (lambda (e)
                     (values #f (format-error e)))])
    (validate-imports! m)
    (validate-tables! m)
    (validate-memories! m)
    (validate-globals! m)
    (validate-exports! m)
    (validate-start! m)
    (validate-elements! m)
    (validate-codes! m)
    (validate-datas! m)
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

(define (validate-limit! who l k)
  (match l
    [(limits lo #f) #:when (> lo k)  (raise-validation-error who "min exceeds ~a" k)]
    [(limits _  hi) #:when (> hi k)  (raise-validation-error who "max exceeds ~a" k)]
    [(limits lo hi) #:when (> lo hi) (raise-validation-error who "min greater than max")]
    [_ (void)]))

;; TODO
(define (validate-imports! m)
  (void))

(define (validate-tables! m)
  (define k (expt 2 32))
  (for ([(t idx) (in-indexed (mod-tables m))])
    (validate-limit! (tableidx idx) t k)))

(define (validate-memories! m)
  (define k (expt 2 16))
  (for ([(m idx) (in-indexed (mod-memories m))])
    (validate-limit! (memidx idx) m k)))

;; TODO
(define (validate-globals! m)
  (void))

;; TODO
(define (validate-exports! m)
  (void))

(define (validate-start! m)
  (define who "start function")
  (match (mod-start m)
    [#f (void)]
    [(funcidx idx)
     (match (type-ref m who (func-ref* m who idx))
       [(functype '() '()) (void)]
       [(functype params results)
        (raise-validation-error who
                                "start function must have type [] -> []~n  found: [~a] -> [~a]"
                                (pp-ts params)
                                (pp-ts results))])]))

;; TODO
(define (validate-elements! m)
  (void))

;; TODO
(define (validate-datas! m)
  (void))

(define (validate-codes! m)
  (for* ([(ftypeidx idx) (in-indexed (mod-functions m))]
         [here (in-value (list (funcidx idx)))]
         [type (in-value (type-ref m here ftypeidx))]
         [code (in-value (code-ref m here idx))])
    (define locals (make-locals type code))
    (define local-ref (make-static-ref locals vector-length vector-ref))
    (let validate-code! ([where here]
                         [type type]
                         [instrs (code-instrs code)]
                         [labels (ra:list type)])
      (define label-ref (make-static-ref labels ra:length ra:list-ref))

      (define (validate-block! who ftype block-instrs)
        (validate-code! who ftype block-instrs (ra:cons ftype labels)))

      (define stack null)

      (define (push! . vts)
        (set! stack (append vts stack)))

      (define (pop! who . vts)
        (define-values (ets remaining-stack)
          (split-at stack (min (length vts)
                               (length stack))))
        (typecheck! who vts ets)
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
           (set! stack (functype-results type))]

          ;; [t1* t*] -> [t2*]
          [(instr:br lbl)
           (define ft (label-ref who lbl))
           (apply keep! who (functype-results ft))]

          ;; [t* i32] -> [t*]
          [(instr:br_if lbl)
           (pop! who i32)
           (define ft (label-ref who lbl))
           (typecheck! who (functype-results ft) stack)]

          ;; [t1* t* i32] -> [t2*]
          [(instr:br_table tbl lN)
           (pop! who i32)
           (define ft (label-ref who lN))
           (for ([l (in-vector tbl)])
             (typecheck! who
                         (functype-results ft)
                         (functype-results (label-ref who l))))
           (apply keep! who (functype-results ft))]

          ;; [t1* t*] -> [t2*]
          [(instr:return)
           (apply keep! who (functype-results type))]

          ;; [t1*] -> [t2*]
          [(instr:block (typeidx idx) block-code)
           (define ft (type-ref m who idx))
           (check! who (instr:block ft block-code))]

          ;; [t1*] -> [t2*]
          [(instr:block ft block-code)
           (when block-code (validate-block! who ft block-code))
           (apply push! (functype-results ft))]

          ;; [t1*] -> [t2*]
          [(instr:loop (typeidx idx) block-code)
           (define ft (type-ref m who idx))
           (check! who (instr:loop ft block-code))]

          ;; [t1*] -> [t2*]
          [(instr:loop ft block-code)
           (when block-code (validate-block! who ft block-code))
           (apply push! (functype-results ft))]

          ;; [t1* i32] -> [t2*]
          [(instr:if (typeidx idx) then-code else-code)
           (define ft (type-ref m who idx))
           (check! who (instr:if ft then-code else-code))]

          ;; [t1* i32] -> [t2*]
          [(instr:if ft then-code else-code)
           (pop! who i32)
           (when then-code (validate-block! who ft then-code))
           (when else-code (validate-block! who ft else-code))
           (apply push! (functype-results ft))]

          ;; [t1*] -> [t2*]
          [(instr:call idx)
           (tc! who (func-ref m who idx))]

          ;; [t1* i32] -> [t2*]
          [(instr:call_indirect idx tblidx)
           (match (table-ref m who tblidx)
             [(tabletype (? funcref?) _)
              (pop! who i32)
              (tc! who (type-ref m who idx))]

             [_
              (raise-validation-error who "table elemtype is not funcref")])]

          ;; Variable Instructions
          [(instr:local.get idx)
           (push! (local-ref who idx))]

          [(instr:local.set idx)
           (pop! who (local-ref who idx))]

          [(instr:local.tee idx)
           (define vt (local-ref who idx))
           (pop! who vt)
           (push! vt)]

          [(instr:global.get idx)
           (define g (global-ref m who idx))
           (define gt (global-type g))
           (push! (globaltype-valtype gt))]

          [(instr:global.set idx)
           (define g (global-ref m who idx))
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
           (memory-ref m who 0)
           (check-alignment! who arg 8)
           (tc! who (instruction-type instr))]

          [(or (instr:i32.load16_s arg)
               (instr:i32.load16_u arg)
               (instr:i64.load16_s arg)
               (instr:i64.load16_u arg)
               (instr:i32.store16 arg)
               (instr:i64.store16 arg))
           (memory-ref m who 0)
           (check-alignment! who arg 16)
           (tc! who (instruction-type instr))]

          [(or (instr:i32.load arg)
               (instr:f32.load arg)
               (instr:i64.load32_s arg)
               (instr:i64.load32_u arg)
               (instr:i32.store arg)
               (instr:f32.store arg)
               (instr:i64.store32 arg))
           (memory-ref m who 0)
           (check-alignment! who arg 32)
           (tc! who (instruction-type instr))]

          [(or (instr:i64.load arg)
               (instr:f64.load arg)
               (instr:i64.store arg)
               (instr:f64.store arg))
           (memory-ref m who 0)
           (check-alignment! who arg 64)
           (tc! who (instruction-type instr))]

          [(instr:memory.size idx)
           (memory-ref m who idx)
           (tc! who (instruction-type instr))]

          [(instr:memory.grow idx)
           (memory-ref m who idx)
           (tc! who (instruction-type instr))]

          ;; Everything Else
          [_ (tc! who (instruction-type instr))]))

      (for ([instr (in-vector instrs)])
        (check! (cons instr where) instr))

      (typecheck! where (functype-results type) stack "result "))))

(define (make-locals t c)
  (apply
   vector-append
   (list->vector (functype-params t))
   (for/list ([l (in-vector (code-locals c))])
     (make-vector (locals-n l) (locals-valtype l)))))

(define (check-alignment! who arg bits)
  (define align (memarg-align arg))
  (unless (<= (expt 2 align) (quotient bits 8))
    (raise-validation-error who "invalid alignment ~v" align)))

(define (typecheck! who expected found [context ""])
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


;; accessors ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ((make-ref accessor len-fn ref-fn) ob who idx)
  (define xs (accessor ob))
  (define max-idx (sub1 (len-fn xs)))
  (when (> idx max-idx)
    (raise-validation-error who "index out of bounds (max: ~a)" max-idx))
  (ref-fn xs idx))

(define (make-static-ref ob len-fn ref-fn)
  (define ref (make-ref values len-fn ref-fn))
  (lambda (who idx)
    (ref ob who idx)))

(define-syntax-rule (define-ref name accessor len-fn ref-fn)
  (define name (make-ref accessor len-fn ref-fn)))

(define-syntax-rule (define-vector-refs [name accessor] ...)
  (begin (define-ref name accessor vector-length vector-ref) ...))

(define-vector-refs
  [type-ref mod-types]
  [import-ref mod-imports]
  [func-ref* mod-functions]
  [table-ref mod-tables]
  [memory-ref mod-memories]
  [global-ref mod-globals]
  [code-ref mod-codes])

(define (func-ref m who idx)
  (define imports/max (vector-length (mod-imports m)))
  (cond
    [(< idx imports/max)
     (match (import-ref m who idx)
       [(import _ _ (typeidx tidx)) (type-ref m who tidx)]
       [(import mod name _) (raise-validation-error who "import ~a.~a is not a function" mod name)])]
    [else (type-ref m who (func-ref* m who (- idx imports/max)))]))
