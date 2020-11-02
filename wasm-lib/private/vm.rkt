#lang racket/base

(require (prefix-in ra: data/ralist)
         racket/contract
         racket/match
         racket/vector
         threading
         "core.rkt"
         "error.rkt"
         "memory.rkt")

(provide
 vm?
 make-vm
 vm-ref)

(struct vm (mod store)
  #:transparent)

(define/contract (make-vm m links)
  (-> mod? (hash/c string? (hash/c string? procedure?)) vm?)
  (vm m (~> (make-store m links)
            (store-add-table m)
            (store-add-memory m)
            (store-add-functions m)
            (store-add-globals m))))

(define/contract (vm-ref v name)
  (-> vm? string? (or/c #f procedure?))
  (define s (vm-store v))
  (define description
    (for*/first ([e (in-vector (mod-exports (vm-mod v)))]
                 #:when (string=? (export-name e) name))
      (export-description e)))

  (match description
    [#f #f]

    [(funcidx idx)
     (define func (vector-ref (store-functions s) idx))
     (lambda args
       (vm-apply v func args))]))

(define (vm-apply v func args)
  (match func
    [(hostfunc _ f) (apply f args)]
    [(localfunc _ code)
     (define types (mod-types (vm-mod v)))
     (define instrs (code-instrs code))
     (define locals
       (make-vector (+ (length args)
                       (for/sum ([l (in-vector (code-locals code))])
                         (locals-n l)))))
     (for ([(arg posn) (in-indexed args)])
       (vector-set! locals posn arg))
     (let/ec return
       (vm-exec v instrs types locals (ra:list return)))]))

(define (vm-exec v instrs types locals labels)
  (define funcs (store-functions (vm-store v)))
  (for/fold ([stack null])
            ([instr (in-vector instrs)])
    #;(printf "instr: ~.s stack: ~s~n" instr stack)
    (vm-eval v instr stack types funcs locals labels)))

(define (vm-eval v instr stack types funcs locals labels)
  (let retry ([instr instr])
    (match instr
      ;; Control instructions
      [(instr:unreachable)
       (trap "unreachable")]

      [(instr:nop)
       null]

      [(instr:block (typeidx idx) block-code)
       (retry (instr:block (vector-ref types idx) block-code))]

      [(instr:block type block-code)
       (define result-count (length (functype-results type)))
       (define result-stack
         (let/ec return
           (vm-exec v block-code types locals (ra:cons return labels))))
       (append (take result-stack result-count) stack)]

      [(instr:loop (typeidx idx) loop-code)
       (retry (instr:loop (vector-ref types idx) loop-code))]

      [(instr:loop type loop-code)
       (define result-count (length (functype-results type)))
       (define result-stack
         (let/ec return
           (let loop ()
             (vm-exec v loop-code types locals (ra:cons return labels))
             (loop))))
       (append (take result-stack result-count) stack)]

      [(instr:if (typeidx idx) then-code else-code)
       (retry (instr:if (vector-ref types idx) then-code else-code))]

      [(instr:if type then-code else-code)
       (define result-count (length (functype-results type)))
       (define result-stack
         (let/ec return
           (match stack
             [(cons 0 _) (vm-exec v else-code types locals (ra:cons return labels))]
             [(cons _ _) (vm-exec v then-code types locals (ra:cons return labels))])))
       (append (take result-stack result-count) (cdr stack))]

      [(instr:return)
       ((ra:car labels) stack)]

      [(instr:br idx)
       ((ra:list-ref labels idx) stack)]

      [(instr:br_if idx)
       (match stack
         [(cons 0 _) (cdr stack)]
         [(cons _ _) ((ra:list-ref labels idx) (cdr stack))])]

      [(instr:br_table tbl idx)
       (define i (car stack))
       (if (< i (vector-length tbl))
           ((ra:list-ref (vector-ref tbl i)) stack)
           ((ra:list-ref idx) stack))]

      [(instr:call idx)
       (define-values (type func)
         (match (vector-ref funcs idx)
           [(and (hostfunc  type _) func) (values type func)]
           [(and (localfunc type _) func) (values type func)]))
       (define-values (args stack-remainder)
         (split-at stack (length (functype-params type))))
       (append (vm-apply v func args) stack-remainder)]

      [(instr:call_indirect idx _)
       (trap "not implemented")]

      ;; Parameteric Instructions
      [(instr:drop)
       (cdr stack)]

      [(instr:select)
       (match stack
         [(list* 0 _ v stack-remainder) (cons v stack-remainder)]
         [(list* _ v _ stack-remainder) (cons v stack-remainder)])]

      ;; Variable Instructions
      [(instr:local.get idx)
       (cons (vector-ref locals idx) stack)]

      [(instr:local.set idx)
       (begin0 (cdr stack)
         (vector-set! locals idx (car stack)))]

      [(instr:local.tee idx)
       (begin0 stack
         (vector-set! locals idx (car stack)))]

      ;; Numeric Instructions
      [(instr:i32.const n)
       (cons n stack)]

      [(instr:i32.gt_s)
       (cons (if (> (cadr stack) (car stack)) 1 0) (cddr stack))]

      [(instr:i32.sub)
       (cons (- (cadr stack) (car stack)) (cddr stack))]

      [(instr:i32.add)
       (cons (+ (cadr stack) (car stack)) (cddr stack))])))

(define (take xs n)
  (cond
    [(zero? n) null]
    [else (let loop ([n n]
                     [xs xs]
                     [ys null])
            (cond
              [(zero? n) (reverse ys)]
              [else (loop (sub1 n) (cdr xs) (cons (car xs) ys))]))]))

(define (split-at ys pos)
  (for/fold ([xs null] [ys ys]
                       #:result (values (reverse xs) ys))
            ([_ (in-range pos)])
    (values (cons (car ys) xs)
            (cdr ys))))


;; store ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct store (functions table memory globals)
  #:transparent)

(struct hostfunc (type f)
  #:transparent)

(struct localfunc (type code)
  #:transparent)

(define (make-store m links)
  (define types (mod-types m))
  (define (lookup what mod name)
    (~> links
        (hash-ref mod  (lambda () (trap "module ~a not present in links" mod)))
        (hash-ref name (lambda () (trap "~a ~a not present in module ~a" what name mod)))))
  (for/fold ([functions null]
             [table #f]
             [memory #f]
             [globals null]
             #:result (let ([functions (list->vector (reverse functions))]
                            [globals   (list->vector (reverse globals))])
                        (store functions table memory globals)))
            ([imp (in-vector (mod-imports m))])
    (match imp
      [(import mod name (typeidx idx))
       (define func (hostfunc (vector-ref types idx) (lookup "function" mod name)))
       (values (cons func functions) table memory globals)]
      [(import mod name (? tabletype?))
       (values functions (lookup "table" mod name) memory globals)]
      [(import mod name (? memtype?))
       (values functions table (lookup "memory" mod name) globals)]
      [(import mod name (? globaltype?))
       (values functions table memory (lookup "global" mod name))])))

(define (store-add-table s m)
  (match (mod-tables m)
    [(vector) s]
    [(vector (tabletype _ _)) (struct-copy store s [table (hash)])]))

(define (store-add-memory s m)
  (match (mod-memories m)
    [(vector) s]
    [(vector (memtype (limits min-pages max-pages)))
     (struct-copy store s [memory (make-memory min-pages max-pages)])]))

(define (store-add-functions s m)
  (define types (mod-types m))
  (for/fold ([functions null]
             #:result (let ([functions (list->vector (reverse functions))])
                        (struct-copy store s [functions (vector-append (store-functions s) functions)])))
            ([typeidx (in-vector (mod-functions m))]
             [code (in-vector (mod-codes m))])
    (cons (localfunc (vector-ref types typeidx) code) functions)))

(define (store-add-globals s m)
  (define globals (make-vector (vector-length (mod-globals m))))
  (struct-copy store s [globals (vector-append (store-globals s) globals)]))
