#lang racket/base

(require racket/contract
         racket/match
         "core.rkt"
         "error.rkt")

(provide
 vm?
 make-vm
 vm-ref)

(define PAGESIZE (* 64 1024))

(struct vm (mod links pages)
  #:transparent)

(define (make-memory-pages n)
  (for/vector ([_ (in-range n)])
    (make-vector PAGESIZE 0)))

(define/contract (make-vm m links)
  (-> mod? (hash/c string? (hash/c string? procedure?)) vm?)
  (define pages
    (match (mod-memories m)
      [(vector (memtype (limits lo _)))
       (make-memory-pages lo)]
      [(vector)
       (vector)]))
  (vm m links pages))

(define/contract (vm-ref v name)
  (-> vm? string? (or/c #f procedure?))
  (define description
    (for*/first ([e (in-vector (mod-exports (vm-mod v)))]
                 #:when (string=? (export-name e) name))
      (export-description e)))

  (match description
    [#f #f]

    [(funcidx idx)
     (lambda args
       (vm-apply v idx args))]))

(define (vm-apply v idx args)
  (define m (vm-mod v))
  (define code (vector-ref (mod-codes m) idx))
  (define instrs (code-instrs code))
  (define locals
    ;; TOOD: Take type into account.
    (make-vector (+ (length args)
                    (for/sum ([l (in-vector (code-locals code))])
                      (locals-n l)))))
  (for ([(arg posn) (in-indexed args)])
    (vector-set! locals posn arg))
  (vm-exec v instrs locals))

(define (vm-exec v instrs locals [stack null])
  (define m (vm-mod v))
  (define fns (mod-functions m))
  (define types (mod-types m))
  (define maxip (sub1 (vector-length instrs)))
  (let loop ([ip 0] [stack stack])
    #;(printf "ip: ~s instr: ~.s stack: ~s~n" ip (vector-ref instrs ip) stack)
    (define new-stack
      (match (vector-ref instrs ip)
        [(instr:local.get idx)
         (cons (vector-ref locals idx) stack)]

        [(instr:local.set idx)
         (vector-set! locals idx (car stack))
         (cdr stack)]

        [(instr:local.tee idx)
         (begin0 stack
           (vector-set! locals idx (car stack)))]

        [(instr:drop)
         (cdr stack)]

        [(instr:select)
         (match stack
           [(list* 0 v2 v1 stack-remainder) (cons v1 stack-remainder)]
           [(list* _ v2 v1 stack-remainder) (cons v2 stack-remainder)])]

        [(instr:nop)
         stack]

        [(instr:unreachable)
         (trap "unreachable")]

        [(instr:i32.const n)
         (cons n stack)]

        [(instr:i32.gt_s)
         (cons (if (> (cadr stack) (car stack)) 1 0) (cddr stack))]

        [(instr:i32.sub)
         (cons (- (cadr stack) (car stack)) (cddr stack))]

        [(instr:i32.add)
         (cons (+ (cadr stack) (car stack)) (cddr stack))]

        [(instr:if _ then-b else-b)
         (match stack
           [(cons 0 stack-remainder) (vm-exec v else-b locals stack-remainder)]
           [(cons _ stack-remainder) (vm-exec v then-b locals stack-remainder)])]

        [(instr:call funcidx)
         (define typeidx (vector-ref fns funcidx))
         (define type (vector-ref types typeidx))
         (define-values (args stack-remainder)
           (split-at stack (length (functype-params type))))
         (append (vm-apply v funcidx args) stack-remainder)]))

    (if (< ip maxip)
        (loop (add1 ip) new-stack)
        new-stack)))

(define (split-at ys pos)
  (for/fold ([xs null] [ys ys]
                       #:result (values (reverse xs) ys))
            ([_ (in-range pos)])
    (values (cons (car ys) xs)
            (cdr ys))))

(define i32?
  (integer-in
   (- (expt 2 31))
   (sub1 (expt 2 32))))

(define i64?
  (integer-in
   (- (expt 2 63))
   (sub1 (expt 2 64))))
