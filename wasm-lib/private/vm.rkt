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
     (define instrs (code-instrs code))
     (define locals
       (make-vector (+ (length args)
                       (for/sum ([l (in-vector (code-locals code))])
                         (locals-n l)))))
     (for ([(arg posn) (in-indexed args)])
       (vector-set! locals posn arg))
     (let/ec return
       (vm-exec v instrs locals (ra:list return)))]))

(define (vm-exec v instrs locals labels)
  (define buf (make-bytes 8))
  (define s (vm-store v))
  (define types (mod-types (vm-mod v)))
  (define funcs (store-functions s))
  (define memory (store-memory s))
  (define globals (store-globals s))
  (for/fold ([stack null])
            ([instr (in-vector instrs)])
    (printf "instr: ~.s stack: ~s~n" instr stack)
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
             (vm-exec v block-code locals (ra:cons return labels))))
         (append (take result-stack result-count) stack)]

        [(instr:loop (typeidx idx) loop-code)
         (retry (instr:loop (vector-ref types idx) loop-code))]

        [(instr:loop type loop-code)
         (define result-count (length (functype-results type)))
         (define result-stack
           (let/ec return
             (let loop ()
               (vm-exec v loop-code locals (ra:cons return labels))
               (loop))))
         (append (take result-stack result-count) stack)]

        [(instr:if (typeidx idx) then-code else-code)
         (retry (instr:if (vector-ref types idx) then-code else-code))]

        [(instr:if type then-code else-code)
         (define result-count (length (functype-results type)))
         (define result-stack
           (let/ec return
             (match stack
               [(cons 0 _) (if else-code (vm-exec v else-code locals (ra:cons return labels)) null)]
               [(cons _ _) (if then-code (vm-exec v then-code locals (ra:cons return labels)) null)])))
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
             ((ra:list-ref labels (vector-ref tbl i)) stack)
             ((ra:list-ref labels idx) stack))]

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

        [(instr:global.set idx)
         (begin0 (cdr stack)
           (vector-set! globals idx (car stack)))]

        [(instr:global.get idx)
         (cons (vector-ref globals idx) stack)]

        ;; Memory Instructions
        [(or (instr:i32.load (memarg _ offset))
             (instr:i64.load32_s (memarg _ offset)))
         (match stack
           [(list* addr stack-remainder)
            (define ea (+ addr offset))
            (memory-load! memory buf ea 4)
            (cons (integer-bytes->integer buf #t #f 0 4) stack-remainder)])]

        [(instr:i64.load (memarg _ offset))
         (match stack
           [(list* addr stack-remainder)
            (define ea (+ addr offset))
            (memory-load! memory buf ea 8)
            (cons (integer-bytes->integer buf #t #f 0 8) stack-remainder)])]

        [(instr:i32.store (memarg _ offset))
         (match stack
           [(list* n addr stack-remainder)
            (define ea (+ addr offset))
            (begin0 stack-remainder
              (memory-store! memory ea (integer->integer-bytes n 4 #t #f buf) 4))])]

        [(instr:f32.store (memarg _ offset))
         (match stack
           [(list* n addr stack-remainder)
            (define ea (+ addr offset))
            (begin0 stack-remainder
              (memory-store! memory ea (real->floating-point-bytes n 4 #f buf) 4))])]

        [(instr:i64.store (memarg _ offset))
         (match stack
           [(list* n addr stack-remainder)
            (define ea (+ addr offset))
            (begin0 stack-remainder
              (memory-store! memory ea (integer->integer-bytes n 8 #t #f buf) 8))])]

        [(instr:f64.store (memarg _ offset))
         (match stack
           [(list* n addr stack-remainder)
            (define ea (+ addr offset))
            (begin0 stack-remainder
              (memory-store! memory ea (real->floating-point-bytes n 8 #f buf) 8))])]

        [(instr:i64.store32 (memarg _ offset))
         (match stack
           [(list* n addr stack-remainder)
            (define ea (+ addr offset))
            (begin0 stack-remainder
              (memory-store! memory ea (integer->integer-bytes n 4 #t #f buf) 4))])]

        [(instr:memory.size _)
         (cons (memory-size memory) stack)]

        [(instr:memory.grow _)
         (match stack
           [(list* n stack-remainder)
            (cons (memory-grow! memory n) stack)])]

        ;; Numeric Instructions
        [(or (instr:i32.const n)
             (instr:f32.const n)
             (instr:i64.const n)
             (instr:f64.const n))
         (cons n stack)]

        [(or (instr:i32.lt_s)
             (instr:i32.lt_u)
             (instr:i64.lt_s)
             (instr:i64.lt_u)
             (instr:f32.lt)
             (instr:f64.lt))
         (match stack
           [(list* b a stack-remainder)
            (cons (if (< a b) 1 0) stack-remainder)])]

        [(or (instr:i32.le_s)
             (instr:i32.le_u)
             (instr:i64.le_s)
             (instr:i64.le_u)
             (instr:f32.le)
             (instr:f64.le))
         (match stack
           [(list* b a stack-remainder)
            (cons (if (<= a b) 1 0) stack-remainder)])]

        [(or (instr:i32.gt_s)
             (instr:i32.gt_u)
             (instr:i64.gt_s)
             (instr:i64.gt_u)
             (instr:f32.gt)
             (instr:f64.gt))
         (match stack
           [(list* b a stack-remainder)
            (cons (if (> a b) 1 0) stack-remainder)])]

        [(or (instr:i32.ge_s)
             (instr:i32.ge_u)
             (instr:i64.ge_s)
             (instr:i64.ge_u)
             (instr:f32.ge)
             (instr:f64.ge))
         (match stack
           [(list* b a stack-remainder)
            (cons (if (>= a b) 1 0) stack-remainder)])]

        [(or (instr:i32.sub)
             (instr:f32.sub)
             (instr:i64.sub)
             (instr:f64.sub))
         (match stack
           [(list* b a stack-remainder)
            (cons (- a b) stack-remainder)])]

        [(or (instr:i32.add)
             (instr:f32.add)
             (instr:i64.add)
             (instr:f64.add))
         (match stack
           [(list* b a stack-remainder)
            (cons (+ a b) stack-remainder)])]

        [(instr:i32.wrap_i64)
         (match stack
           [(list* n stack-remainder)
            (cons (modulo n (expt 2 32)) stack-remainder)])]

        [(instr:i64.extend_i32_u)
         stack]

        [(instr:f32.demote_f64)
         (match stack
           [(list* n stack-remainder)
            ;; FIXME
            (cons n stack-remainder)])]

        [_
         (trap "~e not implemented" instr)]))))

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
