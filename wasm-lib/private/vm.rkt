#lang racket/base

(require racket/contract
         racket/match
         "core.rkt"
         "error.rkt"
         "memory.rkt")

(provide
 vm?
 make-vm
 vm-ref)

(struct vm (mod mem links)
  #:transparent)

(define/contract (make-vm m links)
  (-> mod? (hash/c string? (hash/c string? procedure?)) vm?)
  (define mem
    (match (mod-memories m)
      [(vector (memtype (limits min-pages max-pages)))
       (make-memory min-pages max-pages)]
      [(vector)
       #f]))
  (vm m mem links))

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
    (make-vector (+ (length args)
                    (for/sum ([l (in-vector (code-locals code))])
                      (locals-n l)))))
  (for ([(arg posn) (in-indexed args)])
    (vector-set! locals posn arg))
  (vm-exec v instrs locals))

(define (vm-exec v instrs locals)
  (define m (vm-mod v))
  (define fns (mod-functions m))
  (define types (mod-types m))
  (for/fold ([stack null])
            ([instr (in-vector instrs)])
    #;(printf "ip: ~s instr: ~.s stack: ~s~n" ip (vector-ref instrs ip) stack)
    (match instr
      [(instr:unreachable)
       (trap "unreachable")]

      [(instr:nop)
       null]

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
         [(list* 0 _ v stack-remainder) (cons v stack-remainder)]
         [(list* _ v _ stack-remainder) (cons v stack-remainder)])]

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
         [(cons 0 _) (vm-exec v else-b locals)]
         [(cons _ _) (vm-exec v then-b locals)])]

      [(instr:call funcidx)
       (define typeidx (vector-ref fns funcidx))
       (define type (vector-ref types typeidx))
       (define-values (args stack-remainder)
         (split-at stack (length (functype-params type))))
       (append (vm-apply v funcidx args) stack-remainder)])))

(define (split-at ys pos)
  (for/fold ([xs null] [ys ys]
                       #:result (values (reverse xs) ys))
            ([_ (in-range pos)])
    (values (cons (car ys) xs)
            (cdr ys))))
