#lang racket/base

(require (prefix-in ra: data/ralist)
         racket/contract
         racket/match
         racket/vector
         threading
         "core.rkt"
         "error.rkt"
         "memory.rkt"
         (submod "runtime.rkt" i32)
         (submod "runtime.rkt" i64)
         (submod "runtime.rkt" f32)
         (submod "runtime.rkt" f64))

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
            (store-add-data m)
            (store-add-functions m)
            (store-add-elements m)
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
     (define stack
       (let/ec return
         (vm-exec v instrs locals (ra:list return))))
     stack]))

(define (vm-exec v instrs locals labels)
  (define buf (make-bytes 8))
  (define s (vm-store v))
  (define types (mod-types (vm-mod v)))
  (define table (store-table s))
  (define funcs (store-functions s))
  (define memory (store-memory s))
  (define globals (store-globals s))
  (for/fold ([stack null])
            ([instr (in-vector instrs)])
    (define-syntax-rule (sconsume (var ...) e ...)
      (match stack [(list* var ... st) e ... st]))
    (define-syntax-rule (smatch (var ...) e ... eN)
      (match stack [(list* var ... st) e ... (cons eN st)]))
    (printf "stack: ~s instr: ~e~n" stack instr)
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
           (let loop ()
             (let/ec continue
               (vm-exec v loop-code locals (ra:cons continue labels)))
             (loop)))
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
         ((ra:last labels) stack)]

        [(instr:br idx)
         ((ra:list-ref labels idx) stack)]

        [(instr:br_if idx)
         (match stack
           [(cons 0 st) st]
           [(cons _ st) ((ra:list-ref labels idx) st)])]

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

        [(instr:call_indirect typeidx _)
         (match stack
           [(cons idx stack)
            (define type (vector-ref types typeidx))
            (define func (vector-ref table idx))
            (define-values (args stack-remainder)
              (split-at stack (length (functype-params type))))
            (append (vm-apply v func args) stack-remainder)])]

        ;; Parameteric Instructions
        [(instr:drop)
         (sconsume [_])]

        [(instr:select)
         (match stack
           [(list* 0 _ v st) (cons v st)]
           [(list* _ v _ st) (cons v st)])]

        ;; Variable Instructions
        [(instr:local.get idx)
         (smatch []
           (vector-ref locals idx))]

        [(instr:local.set idx)
         (sconsume [v]
           (vector-set! locals idx v))]

        [(instr:local.tee idx)
         (smatch [v]
           (begin0 v
             (vector-set! locals idx v)))]

        [(instr:global.set idx)
         (sconsume [v]
           (vector-set! globals idx v))]

        [(instr:global.get idx)
         (cons (vector-ref globals idx) stack)]

        ;; Memory Instructions
        [(or (instr:i32.load     (memarg _ offset))
             (instr:i32.load8_s  (memarg _ offset))
             (instr:i32.load16_s (memarg _ offset))
             (instr:i64.load8_s  (memarg _ offset))
             (instr:i64.load16_s (memarg _ offset))
             (instr:i64.load32_s (memarg _ offset)))
         (smatch [addr]
           (define ea (+ addr offset))
           (memory-load! memory buf ea 4)
           (bytes->i32 buf))]

        [(instr:i64.load8_u (memarg _ offset))
         (smatch [addr]
           (define ea (+ addr offset))
           (memory-load! memory buf ea 1)
           (bytes->u8 buf))]

        [(instr:i64.load16_u (memarg _ offset))
         (smatch [addr]
           (define ea (+ addr offset))
           (memory-load! memory buf ea 2)
           (bytes->u16 buf))]

        [(instr:i64.load32_u (memarg _ offset))
         (smatch [addr]
           (define ea (+ addr offset))
           (memory-load! memory buf ea 4)
           (bytes->u64 buf))]

        [(instr:i64.load (memarg _ offset))
         (smatch [addr]
           (define ea (+ addr offset))
           (memory-load! memory buf ea 8)
           (bytes->i64 buf))]

        [(instr:i32.store (memarg _ offset))
         (sconsume [n addr]
           (define ea (+ addr offset))
           (memory-store! memory ea (i32->bytes n buf) 4))]

        [(instr:i64.store (memarg _ offset))
         (sconsume [n addr]
           (define ea (+ addr offset))
           (memory-store! memory ea (i64->bytes n buf) 8))]

        [(instr:i64.store8 (memarg _ offset))
         (sconsume [n addr]
           (define ea (+ addr offset))
           (memory-store! memory ea (i64->bytes8 n buf) 1))]

        [(instr:i64.store16 (memarg _ offset))
         (sconsume [n addr]
           (define ea (+ addr offset))
           (memory-store! memory ea (i64->bytes16 n buf) 2))]

        [(instr:i64.store32 (memarg _ offset))
         (sconsume [n addr]
           (define ea (+ addr offset))
           (memory-store! memory ea (i64->bytes32 n buf) 4))]

        [(instr:f32.store (memarg _ offset))
         (sconsume [n addr]
           (define ea (+ addr offset))
           (memory-store! memory ea (f32->bytes n buf) 4))]

        [(instr:f64.store (memarg _ offset))
         (sconsume [n addr]
           (define ea (+ addr offset))
           (memory-store! memory ea (f64->bytes n buf) 8))]

        [(instr:memory.size _)
         (cons (memory-size memory) stack)]

        [(instr:memory.grow _)
         (smatch [n]
           (begin0 (memory-size memory)
             (memory-grow! memory n)))]

        ;; Numeric Instructions
        [(or (instr:i32.const n)
             (instr:i64.const n)
             (instr:f32.const n)
             (instr:f64.const n))
         (smatch [] n)]

        [(instr:i32.add)      (smatch [b a] (iadd32   a b))]
        [(instr:i32.sub)      (smatch [b a] (isub32   a b))]
        [(instr:i32.mul)      (smatch [b a] (imul32   a b))]
        [(instr:i32.div_u)    (smatch [b a] (idiv32_u a b buf))]
        [(instr:i32.div_s)    (smatch [b a] (idiv32_s a b buf))]
        [(instr:i32.rem_u)    (smatch [b a] (irem32_u a b buf))]
        [(instr:i32.rem_s)    (smatch [b a] (irem32_s a b buf))]
        [(instr:i32.and)      (smatch [b a] (iand32   a b))]
        [(instr:i32.or)       (smatch [b a] (ior32    a b))]
        [(instr:i32.xor)      (smatch [b a] (ixor32   a b))]
        [(instr:i32.shl)      (smatch [b a] (ishl32   a b))]
        [(instr:i32.shr_u)    (smatch [b a] (ishr32_u a b buf))]
        [(instr:i32.shr_s)    (smatch [b a] (ishr32_s a b buf))]
        [(instr:i32.clz)      (smatch [n]   (iclz32     n))]
        [(instr:i32.ctz)      (smatch [n]   (ictz32     n))]
        [(instr:i32.popcnt)   (smatch [n]   (ipopcnt32  n))]
        [(instr:i32.eqz)      (smatch [n]   (ieqz32     n))]
        [(instr:i32.eq)       (smatch [b a] (ieq32    a b))]
        [(instr:i32.ne)       (smatch [b a] (ine32    a b))]
        [(instr:i32.lt_u)     (smatch [b a] (ilt32_u  a b buf))]
        [(instr:i32.lt_s)     (smatch [b a] (ilt32_s  a b buf))]
        [(instr:i32.gt_u)     (smatch [b a] (igt32_u  a b buf))]
        [(instr:i32.gt_s)     (smatch [b a] (igt32_s  a b buf))]
        [(instr:i32.le_u)     (smatch [b a] (ile32_u  a b buf))]
        [(instr:i32.le_s)     (smatch [b a] (ile32_s  a b buf))]
        [(instr:i32.ge_u)     (smatch [b a] (ige32_u  a b buf))]
        [(instr:i32.ge_s)     (smatch [b a] (ige32_s  a b buf))]
        [(instr:i32.wrap_i64) (smatch [n]   (iwrap32  n))]

        [(instr:i64.add)      (smatch [b a] (iadd64   a b))]
        [(instr:i64.sub)      (smatch [b a] (isub64   a b))]
        [(instr:i64.mul)      (smatch [b a] (imul64   a b))]
        [(instr:i64.div_u)    (smatch [b a] (idiv64_u a b buf))]
        [(instr:i64.div_s)    (smatch [b a] (idiv64_s a b buf))]
        [(instr:i64.rem_u)    (smatch [b a] (irem64_u a b buf))]
        [(instr:i64.rem_s)    (smatch [b a] (irem64_s a b buf))]
        [(instr:i64.and)      (smatch [b a] (iand64   a b))]
        [(instr:i64.or)       (smatch [b a] (ior64    a b))]
        [(instr:i64.xor)      (smatch [b a] (ixor64   a b))]
        [(instr:i64.shl)      (smatch [b a] (ishl64   a b))]
        [(instr:i64.shr_u)    (smatch [b a] (ishr64_u a b buf))]
        [(instr:i64.shr_s)    (smatch [b a] (ishr64_s a b buf))]
        [(instr:i64.clz)      (smatch [n]   (iclz64     n))]
        [(instr:i64.ctz)      (smatch [n]   (ictz64     n))]
        [(instr:i64.popcnt)   (smatch [n]   (ipopcnt64  n))]
        [(instr:i64.eqz)      (smatch [n]   (ieqz64     n))]
        [(instr:i64.eq)       (smatch [b a] (ieq64    a b))]
        [(instr:i64.ne)       (smatch [b a] (ine64    a b))]
        [(instr:i64.lt_u)     (smatch [b a] (ilt64_u  a b buf))]
        [(instr:i64.lt_s)     (smatch [b a] (ilt64_s  a b buf))]
        [(instr:i64.gt_u)     (smatch [b a] (igt64_u  a b buf))]
        [(instr:i64.gt_s)     (smatch [b a] (igt64_s  a b buf))]
        [(instr:i64.le_u)     (smatch [b a] (ile64_u  a b buf))]
        [(instr:i64.le_s)     (smatch [b a] (ile64_s  a b buf))]
        [(instr:i64.ge_u)     (smatch [b a] (ige64_u  a b buf))]
        [(instr:i64.ge_s)     (smatch [b a] (ige64_s  a b buf))]

        [(instr:f32.demote_f64) (smatch [n] (fdemote64 n))]

        [(instr:i64.extend_i32_u)
         stack]

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

;; FIXME: size
(define (store-add-table s m)
  (match (mod-tables m)
    [(vector) s]
    [(vector (tabletype _ _))
     (struct-copy store s [table (make-vector 65535)])]))

(define (store-add-memory s m)
  (match (mod-memories m)
    [(vector) s]
    [(vector (memtype (limits min-pages max-pages)))
     (struct-copy store s [memory (make-memory min-pages max-pages)])]))

(define (store-add-data s m)
  (begin0 s
    (for ([d (in-vector (mod-datas m))])
      (match-define (data _ (vector (instr:i32.const offset)) bs) d)
      (memory-store! (store-memory s) offset bs))))

(define (store-add-elements s m)
  (define table (store-table s))
  (define functions (store-functions s))
  (begin0 s
    (for ([e (in-vector (mod-elements m))])
      (match-define (element _ (vector (instr:i32.const offset)) init) e)
      (for ([it  (in-vector init)]
            [tblidx (in-naturals offset)])
        (match-define (funcidx idx) it)
        (vector-set! table tblidx (vector-ref functions idx))))))

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

;; Local Variables:
;; eval: (put 'sconsume 'racket-indent-function #'defun)
;; eval: (put 'smatch 'racket-indent-function #'defun)
;; End:
