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
  (define types (mod-types m))
  (define codes (mod-codes m))
  (let/ec return
    (define (type-ref who idx)
      (when (> idx (vector-length types))
        (return (list (err who "invalid typeidx ~a" idx))))
      (vector-ref types idx))
    (define (code-ref who idx)
      (when (> idx (vector-length codes))
        (return (list (err who "missing code at index ~a" idx))))
      (vector-ref codes idx))
    (for*/fold ([errors null])
               ([(typeidx idx) (in-indexed (or (mod-functions m) null))]
                [here (in-value (funcidx idx))]
                [t (in-value (type-ref here typeidx))]
                [c (in-value (code-ref here idx))])
      (define globals
        (or (mod-globals m) (vector)))
      (define locals
        (apply
         vector-append
         (list->vector (functype-params t))
         (for/list ([l (in-vector (code-locals c))])
           (make-vector (locals-n l) (locals-valtype l)))))
      (append errors (type-errors here globals locals t (code-instrs c))))))

(define (type-errors where globals locals type instrs [labels (list type)])
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

    (define (label-ref who lbl)
      (unless (< lbl (length labels))
        (return (list (err who "invalid label"))))
      (list-ref labels lbl))

    (define (block-errors who ftype block-instrs)
      (type-errors who globals locals ftype block-instrs (cons ftype labels)))

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
      (set! stack remaining-stack))

    (define (tc! instr)
      (define it (instruction-type instr))
      (apply pop! instr (functype-params it))
      (apply push! (functype-results it)))

    (define (check! instr)
      (match instr
        [(instr:unreachable)
         (void)]

        [(instr:br lbl)
         (define ft (label-ref instr lbl))
         (define errors
           (typecheck instr (functype-results ft) stack))
         (unless (null? errors)
           (return errors))]

        [(instr:br_if lbl)
         (tc! instr)
         (check! (instr:br lbl))]

        [(instr:block type block-code)
         (define ftype (functype null (if type (list type) null)))
         (when block-code
           (define errors (block-errors instr ftype block-code))
           (unless (null? errors)
             (return errors)))
         (when type
           (push! type))]

        [(instr:if type then-code else-code)
         (pop! instr i32)
         (define ftype (functype null (if type (list type) null)))
         (when then-code
           (define then-errors (block-errors instr ftype then-code))
           (unless (null? then-errors)
             (return then-errors)))
         (when else-code
           (define else-errors (block-errors instr ftype else-code))
           (unless (null? else-errors)
             (return else-errors)))
         (when type
           (push! type))]

        [(instr:local.get idx)
         (push! (local-ref instr idx))]

        [(instr:local.set idx)
         (pop! instr (local-ref instr idx))]

        [(instr:local.tee idx)
         (define vt (local-ref instr idx))
         (pop! instr vt)
         (push! vt)]

        [(instr:global.get idx)
         (define gt (global-ref instr idx))
         (push! (globaltype-valtype gt))]

        [(instr:global.set idx)
         (define gt (global-ref instr idx))
         (unless (globaltype-mutable? gt)
           (return (list (err instr "cannot set immutable global ~a" idx))))
         (pop! instr (globaltype-valtype gt))]

        [instr (tc! instr)]))

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
