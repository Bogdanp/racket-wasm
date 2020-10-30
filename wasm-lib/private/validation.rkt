#lang racket/base

(require racket/contract
         racket/list
         racket/match
         racket/port
         racket/vector
         "core.rkt")

(provide
 (struct-out validation-error)
 mod-validation-errors)

(struct validation-error (where description)
  #:transparent)

(define (err where description . args)
  (validation-error where (apply format description args)))

(define/contract (mod-validation-errors m)
  (-> mod? (listof validation-error?))
  (for/fold ([errors null])
            ([validate (in-list (list table-errors
                                      memory-errors
                                      function-errors))])
    (append errors (validate m))))

(define (limit-errors where l k)
  (match l
    [(limits lo #f) #:when (> lo k)  (list (err where "min exceeds ~a" k))]
    [(limits _  hi) #:when (> hi k)  (list (err where "max exceeds ~a" k))]
    [(limits lo hi) #:when (> lo hi) (list (err where "min greater than max"))]
    [_ null]))

(define (table-errors m)
  (define k (expt 2 32))
  (for/fold ([errors null])
            ([(t idx) (in-indexed (or (mod-tables m) null))])
    (append errors (limit-errors (tableidx idx) t k))))

(define (memory-errors m)
  (define k (expt 2 16))
  (for/fold ([errors null])
            ([(m idx) (in-indexed (or (mod-memories m) null))])
    (append errors (limit-errors (memidx idx) m k))))

(define (function-errors m)
  (define types (or (mod-types m) (vector)))
  (define codes (or (mod-codes m) (vector)))
  (define globals (or (mod-globals m) (vector)))
  (let/ec return
    (define types/max (sub1 (vector-length types)))
    (define (type-ref who idx)
      (when (> idx types/max)
        (return (list (err who "type index out of bounds ~a (max: ~a)" idx types/max))))
      (vector-ref types idx))
    (define codes/max (sub1 (vector-length codes)))
    (define (code-ref who idx)
      (when (> idx codes/max)
        (return (list (err who "missing code at index ~a (max: ~a)" idx codes/max))))
      (vector-ref codes idx))
    (for*/fold ([errors null])
               ([(typeidx idx) (in-indexed (or (mod-functions m) null))]
                [here (in-value (funcidx idx))]
                [t (in-value (type-ref here typeidx))]
                [c (in-value (code-ref here idx))])
      (define locals
        (apply
         vector-append
         (list->vector (functype-params t))
         (for/list ([l (in-vector (code-locals c))])
           (make-vector (locals-n l) (locals-valtype l)))))
      (append errors (type-errors here types globals locals t (code-instrs c))))))

(define (type-errors where types globals locals type instrs [labels (list type)])
  (let/ec return
    (define locals/max (sub1 (vector-length locals)))
    (define (local-ref who idx)
      (when (> idx locals/max)
        (return (list (err who "local index out of bounds"))))
      (vector-ref locals idx))

    (define globals/max (sub1 (vector-length globals)))
    (define (global-ref who idx)
      (when (> idx globals/max)
        (return (list (err who "global index out of bounds"))))
      (vector-ref globals idx))

    (define labels/max (sub1 (length labels)))
    (define (label-ref who lbl)
      (when (> lbl labels/max)
        (return (list (err who "invalid label (max: ~a)" labels/max))))
      (list-ref labels lbl))

    (define types/max (sub1 (vector-length types)))
    (define (type-ref who idx)
      (when (> idx types/max)
        (return (list (err who "type index out of bounds ~a (max: ~a)" idx types/max))))
      (vector-ref types idx))

    (define (block-errors who ftype block-instrs)
      (type-errors who types globals locals ftype block-instrs (cons ftype labels)))

    (define stack null)

    (define (push! . vts)
      (set! stack (append vts stack)))

    (define (pop! who . vts)
      (define-values (ets remaining-stack)
        (split-at stack (min (length vts)
                             (length stack))))
      (define errors (typecheck who vts ets))
      (unless (null? errors)
        (return errors))
      (begin0 ets
        (set! stack remaining-stack)))

    ;; [t*    ] -> [   ]
    ;; [t* a  ] -> [a  ]
    ;; [t* a b] -> [a b]
    (define (keep! who . vts)
      (set! stack (apply pop! who vts)))

    (define (check! instr)
      (match instr
        [(instr:unreachable)
         (void)]

        ;; [t1* t*] -> [t2*]
        [(instr:br lbl)
         (define ft (label-ref instr lbl))
         (apply keep! instr (functype-results ft))]

        ;; [t* i32] -> [t*]
        [(instr:br_if lbl)
         (pop! instr i32)
         (define ft (label-ref instr lbl))
         (define errors
           (typecheck instr (functype-results ft) stack))
         (unless (null? errors)
           (return errors))]

        ;; [t1* t*] -> [t2*]
        [(instr:return)
         (apply keep! instr (functype-results type))]

        [(instr:block (typeidx idx) block-code)
         (define ft (type-ref instr idx))
         (check! (instr:block ft block-code))]

        [(instr:block ft block-code)
         (when block-code
           (define errors (block-errors instr ft block-code))
           (unless (null? errors)
             (return errors)))
         (apply push! (functype-results ft))]

        [(instr:if (typeidx idx) then-code else-code)
         (define ft (type-ref instr idx))
         (check! (instr:if ft then-code else-code))]

        [(instr:if ft then-code else-code)
         (pop! instr i32)
         (when then-code
           (define then-errors (block-errors instr ft then-code))
           (unless (null? then-errors)
             (return then-errors)))
         (when else-code
           (define else-errors (block-errors instr ft else-code))
           (unless (null? else-errors)
             (return else-errors)))
         (apply push! (functype-results ft))]

        [(instr:local.get idx)
         (push! (local-ref instr idx))]

        [(instr:local.set idx)
         (pop! instr (local-ref instr idx))]

        [(instr:local.tee idx)
         (define vt (local-ref instr idx))
         (pop! instr vt)
         (push! vt)]

        [(instr:global.get idx)
         (define g (global-ref instr idx))
         (define gt (global-type g))
         (push! (globaltype-valtype gt))]

        [(instr:global.set idx)
         (define g (global-ref instr idx))
         (define gt (global-type g))
         (unless (globaltype-mutable? gt)
           (return (list (err instr "cannot set immutable global ~a" idx))))
         (pop! instr (globaltype-valtype gt))]

        [_
         (define it (instruction-type instr))
         (apply pop! instr (functype-params it))
         (apply push! (functype-results it))]))

    (for ([instr (in-vector instrs)])
      (check! instr))

    (typecheck where (functype-results type) stack)))

(define (typecheck who expected found)
  (cond
    [(= (length expected) (length found))
     (for/list ([et (in-list expected)]
                [ft (in-list found)]
                #:unless (type-unify et ft))
       (err who "type error~n  expected: ~v~n  found: ~v" et ft))]

    [else
     (list (err who
                "arity error~n  expected: [~a]~n  found: [~a]"
                (pp-ts expected)
                (pp-ts found)))]))

(define (pp-ts ts)
  (call-with-output-string
   (lambda (out)
     (for ([(t idx) (in-indexed ts)])
       (print t out)
       (unless (= idx (sub1 (length ts)))
         (display " " out))))))
