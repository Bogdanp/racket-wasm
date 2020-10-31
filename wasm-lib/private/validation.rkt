#lang racket/base

(require (for-syntax racket/base)
         racket/contract
         racket/function
         racket/list
         racket/match
         racket/port
         racket/string
         racket/vector
         syntax/parse/define
         "core.rkt")

(provide
 mod-valid?)

(define/contract (mod-valid? m)
  (-> mod? (values boolean? (or/c #f string?)))
  (define validators
    (list validate-tables!
          validate-memories!
          validate-functions!))
  (with-handlers ([exn:fail:validation?
                   (lambda (e)
                     (define message
                       (string-trim
                        (with-output-to-string
                          (lambda ()
                            (displayln (exn-message e))
                            (define whos
                              (match (exn:fail:validation-who e)
                                [(list whos ...) whos]
                                [who (list who)]))
                            (printf "  at: ~v~n" (car whos))
                            (for ([who (in-list (cdr whos))])
                              (printf "  within: ~.v~n" who))))))
                     (values #f message))])
    (for ([validate (in-list validators)])
      (validate m))
    (values #t #f)))

(define (validate-limit! who l k)
  (match l
    [(limits lo #f) #:when (> lo k)  (raise-validation-error who "min exceeds ~a" k)]
    [(limits _  hi) #:when (> hi k)  (raise-validation-error who "max exceeds ~a" k)]
    [(limits lo hi) #:when (> lo hi) (raise-validation-error who "min greater than max")]
    [_ (void)]))

(define (validate-tables! m)
  (define k (expt 2 32))
  (for ([(t idx) (in-indexed (mod-tables m))])
    (validate-limit! (tableidx idx) t k)))

(define (validate-memories! m)
  (define k (expt 2 16))
  (for ([(m idx) (in-indexed (mod-memories m))])
    (validate-limit! (memidx idx) m k)))

(define (validate-functions! m)
  (define-vector-refs m
    [type-ref mod-types]
    [import-ref mod-imports]
    [func-ref* mod-functions]
    [table-ref mod-tables]
    [memory-ref mod-memories]
    [global-ref mod-globals]
    [code-ref mod-codes])

  (define imports/max (vector-length (mod-imports m)))
  (define (func-ref who idx)
    (cond
      [(< idx imports/max)
       (match (import-ref who idx)
         [(import _ _ (typeidx tidx)) (type-ref who tidx)]
         [(import mod name _) (raise-validation-error who "import ~a.~a is not a function" mod name)])]
      [else (type-ref who (func-ref* who (- idx imports/max)))]))

  (for* ([(ftypeidx idx) (in-indexed (mod-functions m))]
         [here (in-value (list (funcidx idx)))]
         [type (in-value (type-ref here ftypeidx))]
         [code (in-value (code-ref here idx))])
    (define locals (make-locals type code))
    (define-vector-ref local-ref m (const locals))
    (let validate-code! ([where here]
                         [type type]
                         [instrs (code-instrs code)]
                         [labels (list type)])
      (define-list-ref label-ref m (const labels))

      (define (validate-block! who ftype block-instrs)
        (validate-code! who ftype block-instrs (cons ftype labels)))

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

      (define (tc! who instr)
        (define it (instruction-type instr))
        (apply pop! who (functype-params it))
        (apply push! (functype-results it)))

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
           (define ft (type-ref who idx))
           (check! who (instr:block ft block-code))]

          ;; [t1*] -> [t2*]
          [(instr:block ft block-code)
           (when block-code (validate-block! who ft block-code))
           (apply push! (functype-results ft))]

          ;; [t1*] -> [t2*]
          [(instr:loop (typeidx idx) block-code)
           (define ft (type-ref who idx))
           (check! who (instr:loop ft block-code))]

          ;; [t1*] -> [t2*]
          [(instr:loop ft block-code)
           (when block-code (validate-block! who ft block-code))
           (apply push! (functype-results ft))]

          ;; [t1* i32] -> [t2*]
          [(instr:if (typeidx idx) then-code else-code)
           (define ft (type-ref who idx))
           (check! who (instr:if ft then-code else-code))]

          ;; [t1* i32] -> [t2*]
          [(instr:if ft then-code else-code)
           (pop! who i32)
           (when then-code (validate-block! who ft then-code))
           (when else-code (validate-block! who ft else-code))
           (apply push! (functype-results ft))]

          ;; [t1*] -> [t2*]
          [(instr:call idx)
           (define ft (func-ref who idx))
           (apply pop! who (functype-params ft))
           (apply push! (functype-results ft))]

          ;; [t1* i32] -> [t2*]
          [(instr:call_indirect idx tblidx)
           (match (table-ref who tblidx)
             [(tabletype (? funcref?) _)
              (pop! who i32)
              (define ft (type-ref who idx))
              (apply pop! who (functype-params ft))
              (apply push! (functype-results ft))]

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
           (define g (global-ref who idx))
           (define gt (global-type g))
           (push! (globaltype-valtype gt))]

          [(instr:global.set idx)
           (define g (global-ref who idx))
           (define gt (global-type g))
           (unless (globaltype-mutable? gt)
             (raise-validation-error who "cannot mutate constant"))
           (pop! who (globaltype-valtype gt))]

          ;; Memory Instructions
          [(instr:memory.size idx)
           (memory-ref who idx)
           (push! i32)]

          [(instr:memory.grow idx)
           (memory-ref who idx)
           (pop! who i32)
           (push! i32)]

          ;; Everything Else
          [_ (tc! who instr)]))

      (for ([instr (in-vector instrs)])
        (check! (cons instr where) instr))

      (typecheck! where (functype-results type) stack "result "))))

(define (make-locals t c)
  (apply
   vector-append
   (list->vector (functype-params t))
   (for/list ([l (in-vector (code-locals c))])
     (make-vector (locals-n l) (locals-valtype l)))))

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
     (for ([(t idx) (in-indexed ts)])
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

(define (make-ref m accessor len-fn ref-fn)
  (define xs (accessor m))
  (define max-idx (sub1 (len-fn xs)))
  (lambda (who idx)
    (when (> idx max-idx)
      (raise-validation-error who "index out of bounds (max: ~a)" max-idx))
    (ref-fn xs idx)))

(define-syntax-parser define-ref
  [(_ name:id m:expr accessor:expr len-fn:expr ref-fn:expr)
   #'(define name (make-ref m accessor len-fn ref-fn))])

(define-syntax-parser define-list-ref
  [(_ name:id m:expr accessor:expr)
   #'(define-ref name m accessor length list-ref)])

(define-syntax-parser define-vector-ref
  [(_ name:id m:expr accessor:expr)
   #'(define-ref name m accessor vector-length vector-ref)])

(define-syntax-parser define-list-refs
  [(_ m:expr [name:id accessor:expr] ...+)
   #'(begin (define-list-ref name m accessor) ...)])

(define-syntax-parser define-vector-refs
  [(_ m:expr [name:id accessor:expr] ...+)
   #'(begin (define-vector-ref name m accessor) ...)])
