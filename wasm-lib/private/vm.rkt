#lang racket/base

(require racket/contract
         racket/match
         (submod racket/performance-hint begin-encourage-inline)
         racket/vector
         threading
         "core.rkt"
         "error.rkt"
         "memory.rkt"
         "opcase.rkt"
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

(define (vm-ref v name [debug debug])
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
       (vm-apply v func args debug))]

    [(memidx _)
     (store-memory s)]))

(define (vm-apply v func args [debug debug] [buf (make-bytes 8)])
  (define m (vm-mod v))
  (define s (vm-store v))
  (define types (mod-types m))
  (define funcs (store-functions s))
  (define table (store-table s))
  (define memory (store-memory s))
  (define globals (store-globals s))
  (define-syntax-rule (debug* arg ...)
    (and debug (debug arg ...)))
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
       (define-values (_ stack)
         (let vm-exec ([instrs instrs]
                       [labels 0]
                       [stack null])
           (cond
             [(vector-empty? instrs)
              (values #f stack)]

             [else
              (let loop ([pc 0] [stack stack])
                (define instr (vector-ref instrs pc))
                (define-syntax-rule (sconsume (var ...) e ...)
                  (match stack [(list* var ... st) e ... (values #f #f st)]))
                (define-syntax-rule (smatch (var ...) e ... eN)
                  (match stack [(list* var ... st) e ... (values #f #f (cons eN st))]))
                (debug* 'vm-exec (list v stack instr))
                (define-values (break? return-label new-stack)
                  (opcase (opcode instr)
                    ;; Control instructions
                    [op:unreachable
                     (trap "unreachable")]

                    [op:nop
                     (values #f #f null)]

                    [op:block
                     (define type (instr:block-type instr))
                     (define-values (params stack-remainder)
                       (split-at stack (length (functype-params type))))
                     (define-values (return-label results)
                       (vm-exec (instr:block-code instr) (add1 labels) params))
                     (if (and return-label (> return-label 0))
                         (values #t (sub1 return-label) results)
                         (values #f #f (append results stack-remainder)))]

                    [op:loop
                     (define type (instr:loop-type instr))
                     (define-values (params stack-remainder)
                       (split-at stack (length (functype-params type))))
                     (let inner-loop ()
                       (define-values (return-label results)
                         (vm-exec (instr:loop-code instr) (add1 labels) params))
                       (cond
                         [(not return-label) (values #f #f (append results stack))]
                         [(zero? return-label) (inner-loop)]
                         [else (values #t (sub1 return-label) results)]))]

                    [op:if
                     (define type (instr:if-type instr))
                     (define c (car stack))
                     (define st (cdr stack))
                     (define-values (params stack-remainder)
                       (split-at st (length (functype-params type))))
                     (define-values (return-label results)
                       (cond
                         [(zero? c)
                          (define else-code (instr:if-else-code instr))
                          (if else-code
                              (vm-exec else-code (add1 labels) params)
                              (values #f null))]
                         [else
                          (define then-code (instr:if-then-code instr))
                          (if then-code
                              (vm-exec then-code (add1 labels) params)
                              (values #f null))]))
                     (if (and return-label (> return-label 0))
                         (values #t (sub1 return-label) results)
                         (values #f #f (append results stack-remainder)))]

                    [op:return
                     (values #t labels stack)]

                    [op:br
                     (values #t (instr:br-lbl instr) stack)]

                    [op:br_if
                     (match stack
                       [(cons 0 st) (values #f #f st)]
                       [(cons _ st) (values #t (instr:br_if-lbl instr) st)])]

                    [op:br_table
                     (define i (car stack))
                     (define tbl (instr:br_table-tbl instr))
                     (define lbl (instr:br_table-lbl instr))
                     (if (< i (vector-length tbl))
                         (values #t (vector-ref tbl i) (cdr stack))
                         (values #t lbl (cdr stack)))]

                    [op:call
                     (define-values (type func)
                       (match (vector-ref funcs (instr:call-idx instr))
                         [(and (externfunc type _) func) (values type func)]
                         [(and (localfunc  type _) func) (values type func)]))
                     (define-values (args stack-remainder)
                       (split-at stack (length (functype-params type))))
                     (define args* (reverse args))
                     (debug* 'call (list (instr:call-idx instr) args*))
                     (values #f #f (append (vm-apply* func args*) stack-remainder))]

                    [op:call_indirect
                     (define typeidx (instr:call_indirect-idx instr))
                     (match stack
                       [(cons idx stack)
                        (define type (vector-ref types typeidx))
                        (define func (vector-ref table idx))
                        (define-values (args stack-remainder)
                          (split-at stack (length (functype-params type))))
                        (values #f #f (append (vm-apply* func (reverse args)) stack-remainder))])]

                    ;; Parameteric Instructions
                    [op:drop
                     (sconsume [_])]

                    [op:select
                     (smatch [c v2 v1]
                       (if (zero? c) v2 v1))]

                    ;; Variable Instructions
                    [op:local.get
                     (smatch []
                       (vector-ref locals (instr:local.get-idx instr)))]

                    [op:local.set
                     (sconsume [v]
                       (vector-set! locals (instr:local.set-idx instr) v))]

                    [op:local.tee
                     (smatch [v]
                       (begin0 v
                         (vector-set! locals (instr:local.tee-idx instr) v)))]

                    [op:global.set
                     (sconsume [v]
                       (vector-set! globals (instr:global.set-idx instr) v))]

                    [op:global.get
                     (smatch []
                       (vector-ref globals (instr:global.get-idx instr)))]

                    ;; Memory Instructions
                    [op:i32.load
                     (smatch [addr]
                       (define ea (+ addr (memarg-offset (instr:i32.load-arg instr))))
                       (memory-load! memory buf ea 4)
                       (bytes->i32 buf 4))]

                    [op:i32.load8_s
                     (smatch [addr]
                       (define ea (+ addr (memarg-offset (instr:i32.load8_s-arg instr))))
                       (memory-load! memory buf ea 1)
                       (bytes->i32 buf 1))]

                    [op:i32.load8_u
                     (smatch [addr]
                       (define ea (+ addr (memarg-offset (instr:i32.load8_u-arg instr))))
                       (memory-load! memory buf ea 1)
                       (bytes->u32 buf 1))]

                    [op:i32.load16_s
                     (smatch [addr]
                       (define ea (+ addr (memarg-offset (instr:i32.load16_s-arg instr))))
                       (memory-load! memory buf ea 2)
                       (bytes->i32 buf 2))]

                    [op:i32.load16_u
                     (smatch [addr]
                       (define ea (+ addr (memarg-offset (instr:i32.load16_u-arg instr))))
                       (memory-load! memory buf ea 2)
                       (bytes->u32 buf 2))]

                    [op:i64.load
                     (smatch [addr]
                       (define ea (+ addr (memarg-offset (instr:i64.load-arg instr))))
                       (memory-load! memory buf ea 8)
                       (bytes->i64 buf 8))]

                    [op:i64.load8_s
                     (smatch [addr]
                       (define ea (+ addr (memarg-offset (instr:i64.load8_s-arg instr))))
                       (memory-load! memory buf ea 1)
                       (bytes->i64 buf 1))]

                    [op:i64.load8_u
                     (smatch [addr]
                       (define ea (+ addr (memarg-offset (instr:i64.load8_u-arg instr))))
                       (memory-load! memory buf ea 1)
                       (bytes->u64 buf 1))]

                    [op:i64.load16_s
                     (smatch [addr]
                       (define ea (+ addr (memarg-offset (instr:i64.load16_s-arg instr))))
                       (memory-load! memory buf ea 2)
                       (bytes->i64 buf 2))]

                    [op:i64.load16_u
                     (smatch [addr]
                       (define ea (+ addr (memarg-offset (instr:i64.load16_u-arg instr))))
                       (memory-load! memory buf ea 2)
                       (bytes->u64 buf 2))]

                    [op:i64.load32_s
                     (smatch [addr]
                       (define ea (+ addr (memarg-offset (instr:i64.load32_s-arg instr))))
                       (memory-load! memory buf ea 4)
                       (bytes->i64 buf 4))]

                    [op:i64.load32_u
                     (smatch [addr]
                       (define ea (+ addr (memarg-offset (instr:i64.load32_u-arg instr))))
                       (memory-load! memory buf ea 4)
                       (bytes->u64 buf 4))]

                    [op:f32.load
                     (smatch [addr]
                       (define ea (+ addr (memarg-offset (instr:f32.load-arg instr))))
                       (memory-load! memory buf ea 4)
                       (bytes->f32 buf))]

                    [op:f64.load
                     (smatch [addr]
                       (define ea (+ addr (memarg-offset (instr:f64.load-arg instr))))
                       (memory-load! memory buf ea 8)
                       (bytes->f64 buf))]

                    [op:i32.store
                     (sconsume [n addr]
                       (define ea (+ addr (memarg-offset (instr:i32.store-arg instr))))
                       (memory-store! memory ea (i32->bytes n buf) 4))]

                    [op:i32.store8
                     (sconsume [n addr]
                       (define ea (+ addr (memarg-offset (instr:i32.store8-arg instr))))
                       (memory-store! memory ea (i32->bytes n buf) 1))]

                    [op:i32.store16
                     (sconsume [n addr]
                       (define ea (+ addr (memarg-offset (instr:i32.store16-arg instr))))
                       (memory-store! memory ea (i32->bytes n buf) 2))]

                    [op:i64.store
                     (sconsume [n addr]
                       (define ea (+ addr (memarg-offset (instr:i64.store-arg instr))))
                       (memory-store! memory ea (i64->bytes n buf) 8))]

                    [op:i64.store8
                     (sconsume [n addr]
                       (define ea (+ addr (memarg-offset (instr:i64.store8-arg instr))))
                       (memory-store! memory ea (i64->bytes n buf) 1))]

                    [op:i64.store16
                     (sconsume [n addr]
                       (define ea (+ addr (memarg-offset (instr:i64.store16-arg instr))))
                       (memory-store! memory ea (i64->bytes n buf) 2))]

                    [op:i64.store32
                     (sconsume [n addr]
                       (define ea (+ addr (memarg-offset (instr:i64.store32-arg instr))))
                       (memory-store! memory ea (i64->bytes n buf) 4))]

                    [op:f32.store
                     (sconsume [n addr]
                       (define ea (+ addr (memarg-offset (instr:f32.store-arg instr))))
                       (memory-store! memory ea (f32->bytes n buf) 4))]

                    [op:f64.store
                     (sconsume [n addr]
                       (define ea (+ addr (memarg-offset (instr:f64.store-arg instr))))
                       (memory-store! memory ea (f64->bytes n buf) 8))]

                    [op:memory.size
                     (smatch []
                       (memory-size memory))]

                    [op:memory.grow
                     (smatch [n]
                       (begin0 (memory-size memory)
                         (memory-grow! memory n)))]

                    ;; Numeric Instructions
                    [op:i32.const (smatch [] (instr:i32.const-n instr))]
                    [op:i64.const (smatch [] (instr:i64.const-n instr))]
                    [op:f32.const (smatch [] (instr:f32.const-n instr))]
                    [op:f64.const (smatch [] (instr:f64.const-n instr))]

                    [op:i32.add    (smatch [b a] (iadd32   a b))]
                    [op:i32.sub    (smatch [b a] (isub32   a b))]
                    [op:i32.mul    (smatch [b a] (imul32   a b))]
                    [op:i32.div_u  (smatch [b a] (idiv32_u a b))]
                    [op:i32.div_s  (smatch [b a] (idiv32_s a b))]
                    [op:i32.rem_u  (smatch [b a] (irem32_u a b))]
                    [op:i32.rem_s  (smatch [b a] (irem32_s a b))]
                    [op:i32.and    (smatch [b a] (iand32   a b))]
                    [op:i32.or     (smatch [b a] (ior32    a b))]
                    [op:i32.xor    (smatch [b a] (ixor32   a b))]
                    [op:i32.shl    (smatch [b a] (ishl32   a b))]
                    [op:i32.shr_u  (smatch [b a] (ishr32_u a b))]
                    [op:i32.shr_s  (smatch [b a] (ishr32_s a b))]
                    [op:i32.rotl   (smatch [b a] (irotl32  a b))]
                    [op:i32.rotr   (smatch [b a] (irotr32  a b))]
                    [op:i32.clz    (smatch [  a] (iclz32     a))]
                    [op:i32.ctz    (smatch [  a] (ictz32     a))]
                    [op:i32.popcnt (smatch [  a] (ipopcnt32  a))]
                    [op:i32.eqz    (smatch [  a] (ieqz32     a))]
                    [op:i32.eq     (smatch [b a] (ieq32    a b))]
                    [op:i32.ne     (smatch [b a] (ine32    a b))]
                    [op:i32.lt_u   (smatch [b a] (ilt32_u  a b))]
                    [op:i32.lt_s   (smatch [b a] (ilt32_s  a b))]
                    [op:i32.gt_u   (smatch [b a] (igt32_u  a b))]
                    [op:i32.gt_s   (smatch [b a] (igt32_s  a b))]
                    [op:i32.le_u   (smatch [b a] (ile32_u  a b))]
                    [op:i32.le_s   (smatch [b a] (ile32_s  a b))]
                    [op:i32.ge_u   (smatch [b a] (ige32_u  a b))]
                    [op:i32.ge_s   (smatch [b a] (ige32_s  a b))]

                    [op:i64.add    (smatch [b a] (iadd64   a b))]
                    [op:i64.sub    (smatch [b a] (isub64   a b))]
                    [op:i64.mul    (smatch [b a] (imul64   a b))]
                    [op:i64.div_u  (smatch [b a] (idiv64_u a b))]
                    [op:i64.div_s  (smatch [b a] (idiv64_s a b))]
                    [op:i64.rem_u  (smatch [b a] (irem64_u a b))]
                    [op:i64.rem_s  (smatch [b a] (irem64_s a b))]
                    [op:i64.and    (smatch [b a] (iand64   a b))]
                    [op:i64.or     (smatch [b a] (ior64    a b))]
                    [op:i64.xor    (smatch [b a] (ixor64   a b))]
                    [op:i64.shl    (smatch [b a] (ishl64   a b))]
                    [op:i64.shr_u  (smatch [b a] (ishr64_u a b))]
                    [op:i64.shr_s  (smatch [b a] (ishr64_s a b))]
                    [op:i64.rotl   (smatch [b a] (irotl64  a b))]
                    [op:i64.rotr   (smatch [b a] (irotr64  a b))]
                    [op:i64.clz    (smatch [  a] (iclz64     a))]
                    [op:i64.ctz    (smatch [  a] (ictz64     a))]
                    [op:i64.popcnt (smatch [  a] (ipopcnt64  a))]
                    [op:i64.eqz    (smatch [  a] (ieqz64     a))]
                    [op:i64.eq     (smatch [b a] (ieq64    a b))]
                    [op:i64.ne     (smatch [b a] (ine64    a b))]
                    [op:i64.lt_u   (smatch [b a] (ilt64_u  a b))]
                    [op:i64.lt_s   (smatch [b a] (ilt64_s  a b))]
                    [op:i64.gt_u   (smatch [b a] (igt64_u  a b))]
                    [op:i64.gt_s   (smatch [b a] (igt64_s  a b))]
                    [op:i64.le_u   (smatch [b a] (ile64_u  a b))]
                    [op:i64.le_s   (smatch [b a] (ile64_s  a b))]
                    [op:i64.ge_u   (smatch [b a] (ige64_u  a b))]
                    [op:i64.ge_s   (smatch [b a] (ige64_s  a b))]

                    [op:f32.abs      (smatch [  a] (fabs32      a))]
                    [op:f32.neg      (smatch [  a] (fneg32      a))]
                    [op:f32.ceil     (smatch [  a] (fceil32     a))]
                    [op:f32.floor    (smatch [  a] (ffloor32    a))]
                    [op:f32.trunc    (smatch [  a] (ftrunc32    a))]
                    [op:f32.nearest  (smatch [  a] (fnearest32  a))]
                    [op:f32.sqrt     (smatch [  a] (fsqrt32     a))]
                    [op:f32.add      (smatch [b a] (fadd32      a b))]
                    [op:f32.sub      (smatch [b a] (fsub32      a b))]
                    [op:f32.mul      (smatch [b a] (fmul32      a b))]
                    [op:f32.div      (smatch [b a] (fdiv32      a b))]
                    [op:f32.min      (smatch [b a] (fmin32      a b))]
                    [op:f32.max      (smatch [b a] (fmax32      a b))]
                    [op:f32.copysign (smatch [b a] (fcopysign32 a b))]
                    [op:f32.eq       (smatch [b a] (feq32       a b))]
                    [op:f32.ne       (smatch [b a] (fne32       a b))]
                    [op:f32.lt       (smatch [b a] (flt32       a b))]
                    [op:f32.gt       (smatch [b a] (fgt32       a b))]
                    [op:f32.le       (smatch [b a] (fle32       a b))]
                    [op:f32.ge       (smatch [b a] (fge32       a b))]

                    [op:f64.abs      (smatch [  a] (fabs64      a))]
                    [op:f64.neg      (smatch [  a] (fneg64      a))]
                    [op:f64.ceil     (smatch [  a] (fceil64     a))]
                    [op:f64.floor    (smatch [  a] (ffloor64    a))]
                    [op:f64.trunc    (smatch [  a] (ftrunc64    a))]
                    [op:f64.nearest  (smatch [  a] (fnearest64  a))]
                    [op:f64.sqrt     (smatch [  a] (fsqrt64     a))]
                    [op:f64.add      (smatch [b a] (fadd64      a b))]
                    [op:f64.sub      (smatch [b a] (fsub64      a b))]
                    [op:f64.mul      (smatch [b a] (fmul64      a b))]
                    [op:f64.div      (smatch [b a] (fdiv64      a b))]
                    [op:f64.min      (smatch [b a] (fmin64      a b))]
                    [op:f64.max      (smatch [b a] (fmax64      a b))]
                    [op:f64.copysign (smatch [b a] (fcopysign64 a b))]
                    [op:f64.eq       (smatch [b a] (feq64       a b))]
                    [op:f64.ne       (smatch [b a] (fne64       a b))]
                    [op:f64.lt       (smatch [b a] (flt64       a b))]
                    [op:f64.gt       (smatch [b a] (fgt64       a b))]
                    [op:f64.le       (smatch [b a] (fle64       a b))]
                    [op:f64.ge       (smatch [b a] (fge64       a b))]

                    [op:i32.wrap_i64        (smatch [a] (iwrap32         a))]
                    [op:i32.trunc_f32_s     (smatch [a] (itrunc32_32_s   a))]
                    [op:i32.trunc_f32_u     (smatch [a] (itrunc32_32_u   a))]
                    [op:i32.trunc_f64_s     (smatch [a] (itrunc32_64_s   a))]
                    [op:i32.trunc_f64_u     (smatch [a] (itrunc32_64_u   a))]
                    [op:i64.extend_i32_s    (smatch [a] (iextend32_s     a))]
                    [op:i64.extend_i32_u    (smatch [a] (iextend32_u     a))]
                    [op:i64.trunc_f32_s     (smatch [a] (itrunc64_32_s   a))]
                    [op:i64.trunc_f32_u     (smatch [a] (itrunc64_32_u   a))]
                    [op:i64.trunc_f64_s     (smatch [a] (itrunc64_64_s   a))]
                    [op:i64.trunc_f64_u     (smatch [a] (itrunc64_64_u   a))]
                    [op:f32.convert_i32_s   (smatch [a] (fconvert32_32_s a))]
                    [op:f32.convert_i32_u   (smatch [a] (fconvert32_32_u a))]
                    [op:f32.convert_i64_s   (smatch [a] (fconvert32_64_s a))]
                    [op:f32.convert_i64_u   (smatch [a] (fconvert32_64_u a))]
                    [op:f32.demote_f64      (smatch [a] (fdemote64       a))]
                    [op:f64.convert_i32_s   (smatch [a] (fconvert64_32_s a))]
                    [op:f64.convert_i32_u   (smatch [a] (fconvert64_32_u a))]
                    [op:f64.convert_i64_s   (smatch [a] (fconvert64_64_s a))]
                    [op:f64.convert_i64_u   (smatch [a] (fconvert64_64_u a))]
                    [op:f64.promote_f32     (smatch [a] (fpromote32      a))]
                    [op:i32.reinterpret_f32 (smatch [a] (ireinterpret32  a))]
                    [op:i64.reinterpret_f64 (smatch [a] (ireinterpret64  a))]
                    [op:f32.reinterpret_i32 (smatch [a] (freinterpret32  a))]
                    [op:f64.reinterpret_i64 (smatch [a] (freinterpret64  a))]

                    [else (trap "~e not implemented" instr)]))

                (define next-pc (add1 pc))
                (cond
                  [break? (values return-label new-stack)]
                  [(= next-pc (vector-length instrs)) (values #f new-stack)]
                  [else (loop next-pc new-stack)]))])))
       stack])))

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
;; eval: (put 'opcase 'racket-indent-function #'defun)
;; eval: (put 'sconsume 'racket-indent-function #'defun)
;; eval: (put 'smatch 'racket-indent-function #'defun)
;; End:
