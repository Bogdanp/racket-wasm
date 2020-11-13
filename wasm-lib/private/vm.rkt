#lang racket/base

(require racket/contract
         racket/list
         racket/match
         (submod racket/performance-hint begin-encourage-inline)
         racket/vector
         threading
         "core.rkt"
         "error.rkt"
         "memory.rkt"
         "runtime.rkt")

(provide
 vm?
 make-vm
 vm-logger
 vm-ref)

;; Debugger hooks ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-logger vm)

(begin-encourage-inline
  (define (debug what data)
    (log-message vm-logger 'debug what "" data #f)))


;; VM ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
  (-> vm? string? (or/c #f procedure? memory?))
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
       (vm-apply v func args))]

    [(memidx _)
     (store-memory s)]))

(define (vm-apply v func args)
  (match-define (vm m (store funcs table memory globals)) v)
  (define types (mod-types m))
  (define buf (make-bytes 8))
  (let vm-apply* ([func func]
                  [args args])
    (match func
      [(externfunc _ f) (apply f args)]
      [(localfunc _ code)
       (define instrs (code-instrs code))
       (define locals
         (make-vector (+ (length args)
                         (for/sum ([l (in-vector (code-locals code))])
                           (locals-n l)))))
       (for ([(arg posn) (in-indexed args)])
         (vector-set! locals posn arg))
       (define stack
         (let/cc return
           (let vm-exec ([instrs instrs]
                         [labels (list return)])
             (for/fold ([stack null])
                       ([instr (in-vector instrs)])
               (define-syntax-rule (sconsume (var ...) e ...)
                 (match stack [(list* var ... st) e ... st]))
               (define-syntax-rule (smatch (var ...) e ... eN)
                 (match stack [(list* var ... st) e ... (cons eN st)]))
               (debug 'vm-exec (list v stack instr))
               (let retry ()
                 (match instr
                   ;; Control instructions
                   [(instr:unreachable _)
                    (trap "unreachable")]

                   [(instr:nop _)
                    null]

                   [(instr:block _ (typeidx idx) _)
                    (set-instr:block-type! instr (vector-ref types idx))
                    (retry)]

                   [(instr:block _ type block-code)
                    (define result-count (length (functype-results type)))
                    (define result-stack
                      (let/cc return
                        (vm-exec block-code (cons return labels))))
                    (append (take result-stack result-count) stack)]

                   [(instr:loop _ (typeidx idx) _)
                    (set-instr:loop-type! instr (vector-ref types idx))
                    (retry)]

                   [(instr:loop _ type loop-code)
                    (define result-count (length (functype-results type)))
                    (define result-stack
                      (let/cc return
                        (let loop ()
                          (let/cc continue
                            (return (vm-exec loop-code (cons continue labels))))
                          (loop))))
                    (append (take result-stack result-count) stack)]

                   [(instr:if _ (typeidx idx) _ _)
                    (set-instr:if-type! (vector-ref types idx))
                    (retry)]

                   [(instr:if _ type then-code else-code)
                    (define result-count (length (functype-results type)))
                    (define result-stack
                      (let/cc return
                        (match stack
                          [(cons 0 _) (if else-code (vm-exec else-code (cons return labels)) null)]
                          [(cons _ _) (if then-code (vm-exec then-code (cons return labels)) null)])))
                    (append (take result-stack result-count) (cdr stack))]

                   [(instr:return _)
                    ((last labels) stack)]

                   [(instr:br _ idx)
                    ((list-ref labels idx) stack)]

                   [(instr:br_if _ idx)
                    (match stack
                      [(cons 0 st) st]
                      [(cons _ st) ((list-ref labels idx) st)])]

                   [(instr:br_table _ tbl idx)
                    (define i (car stack))
                    (if (< i (vector-length tbl))
                        ((list-ref labels (vector-ref tbl i)) stack)
                        ((list-ref labels idx) stack))]

                   [(instr:call _ idx)
                    (define-values (type func)
                      (match (vector-ref funcs idx)
                        [(and (externfunc type _) func) (values type func)]
                        [(and (localfunc  type _) func) (values type func)]))
                    (define-values (args stack-remainder)
                      (split-at stack (length (functype-params type))))
                    (define args* (reverse args))
                    (debug 'call (list idx args*))
                    (append (vm-apply* func args*) stack-remainder)]

                   [(instr:call_indirect _ typeidx _)
                    (match stack
                      [(cons idx stack)
                       (define type (vector-ref types typeidx))
                       (define func (vector-ref table idx))
                       (define-values (args stack-remainder)
                         (split-at stack (length (functype-params type))))
                       (append (vm-apply* func (reverse args)) stack-remainder)])]

                   ;; Parameteric Instructions
                   [(instr:drop _)
                    (sconsume [_])]

                   [(instr:select _)
                    (match stack
                      [(list* 0 v2 _  st) (cons v2 st)]
                      [(list* _ _  v1 st) (cons v1 st)])]

                   ;; Variable Instructions
                   [(instr:local.get _ idx)
                    (smatch []
                      (vector-ref locals idx))]

                   [(instr:local.set _ idx)
                    (sconsume [v]
                      (vector-set! locals idx v))]

                   [(instr:local.tee _ idx)
                    (smatch [v]
                      (begin0 v
                        (vector-set! locals idx v)))]

                   [(instr:global.set _ idx)
                    (sconsume [v]
                      (vector-set! globals idx v))]

                   [(instr:global.get _ idx)
                    (cons (vector-ref globals idx) stack)]

                   ;; Memory Instructions
                   [(or (instr:i32.load     _ (memarg _ offset))
                        (instr:i32.load8_s  _ (memarg _ offset))
                        (instr:i32.load16_s _ (memarg _ offset)))
                    (smatch [addr]
                      (define ea (+ addr offset))
                      (define size
                        (match instr
                          [(instr:i32.load     _ _) 4]
                          [(instr:i32.load8_s  _ _) 1]
                          [(instr:i32.load16_s _ _) 2]))
                      (memory-load! memory buf ea size)
                      (bytes->i32 buf size))]

                   [(or (instr:i32.load8_u  _ (memarg _ offset))
                        (instr:i32.load16_u _ (memarg _ offset)))
                    (smatch [addr]
                      (define ea (+ addr offset))
                      (define size
                        (match instr
                          [(instr:i32.load8_u  _ _) 1]
                          [(instr:i32.load16_u _ _) 2]))
                      (memory-load! memory buf ea size)
                      (bytes->u32 buf size))]

                   [(or (instr:i64.load     _ (memarg _ offset))
                        (instr:i64.load8_s  _ (memarg _ offset))
                        (instr:i64.load16_s _ (memarg _ offset))
                        (instr:i64.load32_s _ (memarg _ offset)))
                    (smatch [addr]
                      (define ea (+ addr offset))
                      (define size
                        (match instr
                          [(instr:i64.load     _ _) 8]
                          [(instr:i64.load8_s  _ _) 1]
                          [(instr:i64.load16_s _ _) 2]
                          [(instr:i64.load32_s _ _) 4]))
                      (memory-load! memory buf ea size)
                      (bytes->i64 buf size))]

                   [(or (instr:i64.load8_u  _ (memarg _ offset))
                        (instr:i64.load16_u _ (memarg _ offset))
                        (instr:i64.load32_u _ (memarg _ offset)))
                    (smatch [addr]
                      (define ea (+ addr offset))
                      (define size
                        (match instr
                          [(instr:i64.load8_u  _ _) 1]
                          [(instr:i64.load16_u _ _) 2]
                          [(instr:i64.load32_u _ _) 4]))
                      (memory-load! memory buf ea size)
                      (bytes->u64 buf size))]

                   [(instr:f32.load _ (memarg _ offset))
                    (smatch [addr]
                      (define ea (+ addr offset))
                      (memory-load! memory buf ea 4)
                      (bytes->f32 buf))]

                   [(instr:f64.load _ (memarg _ offset))
                    (smatch [addr]
                      (define ea (+ addr offset))
                      (memory-load! memory buf ea 8)
                      (bytes->f64 buf))]

                   [(or (instr:i32.store   _ (memarg _ offset))
                        (instr:i32.store8  _ (memarg _ offset))
                        (instr:i32.store16 _ (memarg _ offset)))
                    (sconsume [n addr]
                      (define ea (+ addr offset))
                      (define size
                        (match instr
                          [(instr:i32.store   _ _) 4]
                          [(instr:i32.store8  _ _) 1]
                          [(instr:i32.store16 _ _) 2]))
                      (memory-store! memory ea (i32->bytes n buf) size))]

                   [(or (instr:i64.store   _ (memarg _ offset))
                        (instr:i64.store8  _ (memarg _ offset))
                        (instr:i64.store16 _ (memarg _ offset))
                        (instr:i64.store32 _ (memarg _ offset)))
                    (sconsume [n addr]
                      (define ea (+ addr offset))
                      (define size
                        (match instr
                          [(instr:i64.store   _ _) 8]
                          [(instr:i64.store8  _ _) 1]
                          [(instr:i64.store16 _ _) 2]
                          [(instr:i64.store32 _ _) 4]))
                      (memory-store! memory ea (i64->bytes n buf) size))]

                   [(instr:f32.store _ (memarg _ offset))
                    (sconsume [n addr]
                      (define ea (+ addr offset))
                      (memory-store! memory ea (f32->bytes n buf) 4))]

                   [(instr:f64.store _ (memarg _ offset))
                    (sconsume [n addr]
                      (define ea (+ addr offset))
                      (memory-store! memory ea (f64->bytes n buf) 8))]

                   [(instr:memory.size _ _)
                    (cons (memory-size memory) stack)]

                   [(instr:memory.grow _ _)
                    (smatch [n]
                      (begin0 (memory-size memory)
                        (memory-grow! memory n)))]

                   ;; Numeric Instructions
                   [(or (instr:i32.const _ n)
                        (instr:i64.const _ n)
                        (instr:f32.const _ n)
                        (instr:f64.const _ n))
                    (smatch [] n)]

                   [(instr:i32.add      _) (smatch [b a] (iadd32   a b))]
                   [(instr:i32.sub      _) (smatch [b a] (isub32   a b))]
                   [(instr:i32.mul      _) (smatch [b a] (imul32   a b))]
                   [(instr:i32.div_u    _) (smatch [b a] (idiv32_u a b))]
                   [(instr:i32.div_s    _) (smatch [b a] (idiv32_s a b))]
                   [(instr:i32.rem_u    _) (smatch [b a] (irem32_u a b))]
                   [(instr:i32.rem_s    _) (smatch [b a] (irem32_s a b))]
                   [(instr:i32.and      _) (smatch [b a] (iand32   a b))]
                   [(instr:i32.or       _) (smatch [b a] (ior32    a b))]
                   [(instr:i32.xor      _) (smatch [b a] (ixor32   a b))]
                   [(instr:i32.shl      _) (smatch [b a] (ishl32   a b))]
                   [(instr:i32.shr_u    _) (smatch [b a] (ishr32_u a b))]
                   [(instr:i32.shr_s    _) (smatch [b a] (ishr32_s a b))]
                   [(instr:i32.rotl     _) (smatch [b a] (irotl32  a b))]
                   [(instr:i32.rotr     _) (smatch [b a] (irotr32  a b))]
                   [(instr:i32.clz      _) (smatch [n]   (iclz32     n))]
                   [(instr:i32.ctz      _) (smatch [n]   (ictz32     n))]
                   [(instr:i32.popcnt   _) (smatch [n]   (ipopcnt32  n))]
                   [(instr:i32.eqz      _) (smatch [n]   (ieqz32     n))]
                   [(instr:i32.eq       _) (smatch [b a] (ieq32    a b))]
                   [(instr:i32.ne       _) (smatch [b a] (ine32    a b))]
                   [(instr:i32.lt_u     _) (smatch [b a] (ilt32_u  a b))]
                   [(instr:i32.lt_s     _) (smatch [b a] (ilt32_s  a b))]
                   [(instr:i32.gt_u     _) (smatch [b a] (igt32_u  a b))]
                   [(instr:i32.gt_s     _) (smatch [b a] (igt32_s  a b))]
                   [(instr:i32.le_u     _) (smatch [b a] (ile32_u  a b))]
                   [(instr:i32.le_s     _) (smatch [b a] (ile32_s  a b))]
                   [(instr:i32.ge_u     _) (smatch [b a] (ige32_u  a b))]
                   [(instr:i32.ge_s     _) (smatch [b a] (ige32_s  a b))]

                   [(instr:i64.add    _) (smatch [b a] (iadd64   a b))]
                   [(instr:i64.sub    _) (smatch [b a] (isub64   a b))]
                   [(instr:i64.mul    _) (smatch [b a] (imul64   a b))]
                   [(instr:i64.div_u  _) (smatch [b a] (idiv64_u a b))]
                   [(instr:i64.div_s  _) (smatch [b a] (idiv64_s a b))]
                   [(instr:i64.rem_u  _) (smatch [b a] (irem64_u a b))]
                   [(instr:i64.rem_s  _) (smatch [b a] (irem64_s a b))]
                   [(instr:i64.and    _) (smatch [b a] (iand64   a b))]
                   [(instr:i64.or     _) (smatch [b a] (ior64    a b))]
                   [(instr:i64.xor    _) (smatch [b a] (ixor64   a b))]
                   [(instr:i64.shl    _) (smatch [b a] (ishl64   a b))]
                   [(instr:i64.shr_u  _) (smatch [b a] (ishr64_u a b))]
                   [(instr:i64.shr_s  _) (smatch [b a] (ishr64_s a b))]
                   [(instr:i64.rotl   _) (smatch [b a] (irotl64  a b))]
                   [(instr:i64.rotr   _) (smatch [b a] (irotr64  a b))]
                   [(instr:i64.clz    _) (smatch [n]   (iclz64     n))]
                   [(instr:i64.ctz    _) (smatch [n]   (ictz64     n))]
                   [(instr:i64.popcnt _) (smatch [n]   (ipopcnt64  n))]
                   [(instr:i64.eqz    _) (smatch [n]   (ieqz64     n))]
                   [(instr:i64.eq     _) (smatch [b a] (ieq64    a b))]
                   [(instr:i64.ne     _) (smatch [b a] (ine64    a b))]
                   [(instr:i64.lt_u   _) (smatch [b a] (ilt64_u  a b))]
                   [(instr:i64.lt_s   _) (smatch [b a] (ilt64_s  a b))]
                   [(instr:i64.gt_u   _) (smatch [b a] (igt64_u  a b))]
                   [(instr:i64.gt_s   _) (smatch [b a] (igt64_s  a b))]
                   [(instr:i64.le_u   _) (smatch [b a] (ile64_u  a b))]
                   [(instr:i64.le_s   _) (smatch [b a] (ile64_s  a b))]
                   [(instr:i64.ge_u   _) (smatch [b a] (ige64_u  a b))]
                   [(instr:i64.ge_s   _) (smatch [b a] (ige64_s  a b))]

                   [(instr:f32.abs      _) (smatch [  a] (fabs32      a))]
                   [(instr:f32.neg      _) (smatch [  a] (fneg32      a))]
                   [(instr:f32.ceil     _) (smatch [  a] (fceil32     a))]
                   [(instr:f32.floor    _) (smatch [  a] (ffloor32    a))]
                   [(instr:f32.trunc    _) (smatch [  a] (ftrunc32    a))]
                   [(instr:f32.nearest  _) (smatch [  a] (fnearest32  a))]
                   [(instr:f32.sqrt     _) (smatch [  a] (fsqrt32     a))]
                   [(instr:f32.add      _) (smatch [b a] (fadd32      a b))]
                   [(instr:f32.sub      _) (smatch [b a] (fsub32      a b))]
                   [(instr:f32.mul      _) (smatch [b a] (fmul32      a b))]
                   [(instr:f32.div      _) (smatch [b a] (fdiv32      a b))]
                   [(instr:f32.min      _) (smatch [b a] (fmin32      a b))]
                   [(instr:f32.max      _) (smatch [b a] (fmax32      a b))]
                   [(instr:f32.copysign _) (smatch [b a] (fcopysign32 a b))]
                   [(instr:f32.eq       _) (smatch [b a] (feq32       a b))]
                   [(instr:f32.ne       _) (smatch [b a] (fne32       a b))]
                   [(instr:f32.lt       _) (smatch [b a] (flt32       a b))]
                   [(instr:f32.gt       _) (smatch [b a] (fgt32       a b))]
                   [(instr:f32.le       _) (smatch [b a] (fle32       a b))]
                   [(instr:f32.ge       _) (smatch [b a] (fge32       a b))]

                   [(instr:f64.abs      _) (smatch [  a] (fabs64      a))]
                   [(instr:f64.neg      _) (smatch [  a] (fneg64      a))]
                   [(instr:f64.ceil     _) (smatch [  a] (fceil64     a))]
                   [(instr:f64.floor    _) (smatch [  a] (ffloor64    a))]
                   [(instr:f64.trunc    _) (smatch [  a] (ftrunc64    a))]
                   [(instr:f64.nearest  _) (smatch [  a] (fnearest64  a))]
                   [(instr:f64.sqrt     _) (smatch [  a] (fsqrt64     a))]
                   [(instr:f64.add      _) (smatch [b a] (fadd64      a b))]
                   [(instr:f64.sub      _) (smatch [b a] (fsub64      a b))]
                   [(instr:f64.mul      _) (smatch [b a] (fmul64      a b))]
                   [(instr:f64.div      _) (smatch [b a] (fdiv64      a b))]
                   [(instr:f64.min      _) (smatch [b a] (fmin64      a b))]
                   [(instr:f64.max      _) (smatch [b a] (fmax64      a b))]
                   [(instr:f64.copysign _) (smatch [b a] (fcopysign64 a b))]
                   [(instr:f64.eq       _) (smatch [b a] (feq64       a b))]
                   [(instr:f64.ne       _) (smatch [b a] (fne64       a b))]
                   [(instr:f64.lt       _) (smatch [b a] (flt64       a b))]
                   [(instr:f64.gt       _) (smatch [b a] (fgt64       a b))]
                   [(instr:f64.le       _) (smatch [b a] (fle64       a b))]
                   [(instr:f64.ge       _) (smatch [b a] (fge64       a b))]

                   [(instr:i32.wrap_i64      _) (smatch [n] (iwrap32       n))]
                   [(instr:i32.trunc_f32_u   _) (smatch [n] (itrunc32_32_u n))]
                   [(instr:i32.trunc_f32_s   _) (smatch [n] (itrunc32_32_s n))]
                   [(instr:i32.trunc_f64_u   _) (smatch [n] (itrunc32_64_u n))]
                   [(instr:i32.trunc_f64_s   _) (smatch [n] (itrunc32_64_s n))]
                   [(instr:i64.extend_i32_u  _) (smatch [n] (iextend32_u   n))]
                   [(instr:i64.extend_i32_s  _) (smatch [n] (iextend32_s   n))]
                   [(instr:i64.trunc_f32_u   _) (smatch [n] (itrunc64_32_u n))]
                   [(instr:i64.trunc_f32_s   _) (smatch [n] (itrunc64_32_s n))]
                   [(instr:i64.trunc_f64_u   _) (smatch [n] (itrunc64_64_u n))]
                   [(instr:i64.trunc_f64_s   _) (smatch [n] (itrunc64_64_s n))]
                   [(instr:f32.demote_f64    _) (smatch [n] (fdemote64     n))]
                   [(instr:f64.promote_f32   _) (smatch [n] (fpromote32    n))]
                   [(instr:f64.convert_i64_u _) (smatch [n] (fconvert64_u  n))]
                   [(instr:f64.convert_i64_s _) (smatch [n] (fconvert64_s  n))]

                   [_
                    (trap "~e not implemented" instr)]))))))
       stack])))

(define (take xs n)
  (let loop ([n n]
             [xs xs]
             [ys null])
    (cond
      [(zero? n) (reverse ys)]
      [else (loop (sub1 n) (cdr xs) (cons (car xs) ys))])))

(define (split-at ys pos)
  (for/fold ([xs null] [ys ys] #:result (values (reverse xs) ys))
            ([_ (in-range pos)])
    (values (cons (car ys) xs) (cdr ys))))


;; store ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct store (functions table memory globals)
  #:transparent)

(struct externfunc (type f)
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
       (define func (externfunc (vector-ref types idx) (lookup "function" mod name)))
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
    [(vector (tabletype _ (limits min-size max-size)))
     (struct-copy store s [table (make-vector (or max-size min-size))])]))

(define (store-add-memory s m)
  (match (mod-memories m)
    [(vector) s]
    [(vector (memtype (limits min-pages max-pages)))
     (struct-copy store s [memory (make-memory min-pages max-pages)])]))

(define (store-add-data s m)
  (begin0 s
    (for ([d (in-vector (mod-datas m))])
      (match-define (data _ (vector (instr:i32.const _ offset)) bs) d)
      (memory-store! (store-memory s) offset bs))))

(define (store-add-elements s m)
  (define table (store-table s))
  (define functions (store-functions s))
  (begin0 s
    (for ([e (in-vector (mod-elements m))])
      (match-define (element _ (vector (instr:i32.const _ offset)) init) e)
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
