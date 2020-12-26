#lang racket/base

#|review: ignore|#

(require racket/match
         wasm/private/error
         wasm/private/memory
         wasm/private/runtime
         wasm/private/store
         wasm/private/switch
         "core.rkt"
         "opcase.rkt")

(provide
 compile-mod)

(define (compile-mod m links [name 'wasm])
  (define s (make-store m links))
  (define ns (make-base-namespace))
  (define caller-ns (current-namespace))
  (parameterize ([current-namespace ns])
    (namespace-attach-module caller-ns 'wasm/private/error)
    (namespace-attach-module caller-ns 'wasm/private/memory)
    (namespace-attach-module caller-ns 'wasm/private/runtime)
    (namespace-attach-module caller-ns 'wasm/private/store)
    (namespace-attach-module caller-ns 'wasm/private/switch)
    (define the-mod
      `(module ,name racket/base
         (require racket/fixnum
                  (only-in wasm/private/error trap)
                  wasm/private/memory
                  wasm/private/runtime
                  wasm/private/store
                  wasm/private/switch)

         (define-namespace-anchor $anchor)

         (define $ns (namespace-anchor->namespace $anchor))
         (define $buf (make-bytes 8))
         (define $tbl #f)
         (define $mem #f)

         ,@(for/list ([_ (in-vector (store-globals s))]
                      [i (in-naturals)])
             `(define ,(global-name i) 0))

         ,@(for/list ([f (in-vector (store-functions s))]
                      [i (in-naturals)])
             #:break (localfunc? f)
             `(define ,(func-name i) #f))

         (provide $init)
         (define ($init table memory functions)
           (set! $tbl table)
           (set! $mem memory)
           ,@(for/list ([f (in-vector (store-functions s))]
                        [i (in-naturals)])
               #:break (localfunc? f)
               `(set! ,(func-name i) (externfunc-f (vector-ref functions ,i)))))

         (define ($indirect idx . args)
           (define funcidx (vector-ref $tbl idx))
           (define funcsym (string->symbol (format "$f~a" funcidx)))
           (apply (eval funcsym $ns) args))

         ,@(for/list ([e (in-vector (mod-exports m))])
             (define export-id (string->symbol (export-name e)))
             (match (export-description e)
               [(funcidx idx)
                `(provide (rename-out [,(func-name idx) ,export-id]))]
               [(memidx _)
                `(provide (rename-out [$mem ,export-id]))]))

         ,@(for/list ([f (in-vector (store-functions s))]
                      [i (in-naturals)]
                      #:when (localfunc? f))
             (define type (localfunc-type f))
             (define code (localfunc-code f))
             (define argc (length (functype-params type)))
             (define arg-regs (for/list ([idx (in-range argc)])
                                (local-name idx)))
             (define localc (for/sum ([l (in-vector (code-locals code))])
                              (locals-n l)))
             (define local-regs (for/list ([idx (in-range argc (+ argc localc))])
                                  (local-name idx)))
             `(define (,(func-name i) ,@arg-regs)
                ,(resugar
                  (try-eliminate-label
                   `(let/cc $return
                      ,@(for/list ([id (in-list local-regs)])
                          `(define ,id #f))
                      ,@(let compile-block ([instrs (code-instrs code)]
                                            [labels '($return)]
                                            [stack null])
                          (let* ([push! (lambda (e)
                                          (set! stack (cons e stack)))]
                                 [pop! (lambda ()
                                         (begin0 (car stack)
                                           (set! stack (cdr stack))))]
                                 [split! (lambda (t)
                                           (let loop ([block-stack null]
                                                      [remaining (length (functype-params t))])
                                             (if (zero? remaining)
                                                 (reverse block-stack)
                                                 (loop (cons (pop!) block-stack) (sub1 remaining)))))]
                                 [gen-store! (lambda (off size convert)
                                               (define n (pop!))
                                               (define addr (pop!))
                                               `(memory-store! $mem (fx+ ,addr ,off) (,convert ,n $buf) ,size))]
                                 [push-load! (lambda (off size convert [sized? #f])
                                               (define res-name (gensym 'r))
                                               (define addr (pop!))
                                               (begin0 `(define ,res-name
                                                          (let ()
                                                            (memory-load! $mem $buf (fx+ ,addr ,off) ,size)
                                                            ,(if sized?
                                                                 `(,convert $buf ,size)
                                                                 `(,convert $buf))))
                                                 (push! res-name)))]
                                 [push-call1! (lambda (e)
                                                (push! `(,e ,(pop!))))]
                                 [push-call2! (lambda (e)
                                                (define b (pop!))
                                                (define a (pop!))
                                                (push! `(,e ,a ,b)))])
                            (define exprs
                              (for/fold ([exprs null] #:result (reverse exprs))
                                        ([instr (in-vector instrs)])
                                (define e
                                  (opcase (opcode instr)
                                    ;; Control Instructions
                                    [op:unreachable
                                     '(trap "unreachable")]

                                    [op:nop
                                     (set! stack null)]

                                    [op:block
                                     (define type (instr:block-type instr))
                                     (define block-stack (split! type))
                                     (define res-names (make-res-names type))
                                     (define lbl-name (gensym '$lbl))
                                     (define block
                                       (try-rewrite-switch
                                        (try-eliminate-label
                                         `(let/cc ,lbl-name
                                            ,@(cond
                                                [(instr:block-code instr)
                                                 => (lambda (block-instrs)
                                                      (compile-block block-instrs (cons lbl-name labels) block-stack))]
                                                [else '((void))])))))
                                     (cond
                                       [(null? res-names) block]
                                       [else
                                        (begin0 `(define-values (,@res-names) ,block)
                                          (for-each push! res-names))])]

                                    [op:loop
                                     (define type (instr:loop-type instr))
                                     (define block-stack (split! type))
                                     (define res-names (make-res-names type))
                                     (define lbl-name (gensym '$loop))
                                     (define block
                                       (cond
                                         [(instr:loop-code instr)
                                          => (lambda (loop-instrs)
                                               (define code (compile-block loop-instrs (cons lbl-name labels) block-stack))
                                               `(let ,lbl-name () ,@code))]
                                         [else '(void)]))
                                     (cond
                                       [(null? res-names) block]
                                       [else
                                        (begin0 `(define-values (,@res-names) ,block)
                                          (for-each push! res-names))])]

                                    [op:if
                                     (define type (instr:if-type instr))
                                     (define block-stack (split! type))
                                     (define res-names (make-res-names type))
                                     (define lbl-name (gensym '$lbl))
                                     (define block
                                       (try-eliminate-label
                                        `(let/cc ,lbl-name
                                           (cond
                                             [(zero? ,(pop!))
                                              ,@(cond
                                                  [(instr:if-else-code instr)
                                                   => (lambda (else-instrs)
                                                        (compile-block else-instrs (cons lbl-name labels) block-stack))]
                                                  [else '((void))])]

                                             [else
                                              ,@(cond
                                                  [(instr:if-then-code instr)
                                                   => (lambda (then-instrs)
                                                        (compile-block then-instrs (cons lbl-name labels) block-stack))]
                                                  [else '((void))])]))))
                                     (cond
                                       [(null? res-names) block]
                                       [else
                                        (begin0 `(define-values (,@res-names) ,block)
                                          (for-each push! res-names))])]

                                    [op:return
                                     (begin0 `($return ,@stack)
                                       (set! stack null))]

                                    [op:br
                                     (define lbl (instr:br-lbl instr))
                                     (define lbl-name (list-ref labels lbl))
                                     `(,lbl-name ,@stack)]

                                    [op:br_if
                                     (define lbl (instr:br_if-lbl instr))
                                     (define lbl-name (list-ref labels lbl))
                                     `(unless (zero? ,(pop!))
                                        (,lbl-name ,@stack))]

                                    [op:br_table
                                     (define cond-e (pop!))
                                     (define clauses
                                       (for/list ([lbl (in-vector (instr:br_table-tbl instr))]
                                                  [idx (in-naturals)])
                                         (define clause-lbl-name
                                           (list-ref labels lbl))
                                         `[(,idx) (,clause-lbl-name ,@stack)]))
                                     (define fallthrough-lbl-name
                                       (list-ref labels (instr:br_table-lbl instr)))
                                     `(case ,cond-e
                                        ,@clauses
                                        [else (,fallthrough-lbl-name ,@stack)])]

                                    [op:call
                                     (define idx (instr:call-idx instr))
                                     (define-values (type name)
                                       (match (vector-ref (store-functions s) idx)
                                         [(externfunc type _) (values type (func-name idx))]
                                         [(localfunc  type _) (values type (func-name idx))]))
                                     (define arg-names (make-arg-names type))
                                     (define res-names (make-res-names type))
                                     (define arg-binders
                                       (for/list ([arg-name (in-list arg-names)])
                                         `(,arg-name ,(pop!))))
                                     (define call
                                       `(let (,@arg-binders)
                                          (,name ,@(reverse arg-names))))
                                     (cond
                                       [(null? res-names) call]
                                       [else
                                        (begin0 `(define-values (,@res-names) ,call)
                                          (for-each push! res-names))])]

                                    [op:call_indirect
                                     (define typeidx (instr:call_indirect-idx instr))
                                     (define type (vector-ref (mod-types m) typeidx))
                                     (define arg-names (make-arg-names type))
                                     (define res-names (make-res-names type))
                                     (define idx-e (pop!))
                                     (define arg-binders
                                       (for/list ([arg-name (in-list arg-names)])
                                         `[,arg-name ,(pop!)]))
                                     (define call
                                       `(let (,@arg-binders)
                                          ($indirect ,idx-e ,@(reverse arg-names))))
                                     (cond
                                       [(null? res-names) call]
                                       [else
                                        (begin0 `(define-values (,@res-names) ,call)
                                          (for-each push! res-names))])]

                                    ;; Parametric Instructions
                                    [op:drop
                                     (void (pop!))]

                                    [op:select
                                     (define c  (pop!))
                                     (define v2 (pop!))
                                     (define v1 (pop!))
                                     (push! `(if (zero? ,c) ,v2 ,v1))]

                                    ;; Variable Instructions
                                    [op:local.get
                                     (push! (local-name (instr:local.get-idx instr)))]

                                    [op:local.set
                                     `(set! ,(local-name (instr:local.set-idx instr)) ,(pop!))]

                                    [op:local.tee
                                     (push! `(let ([a ,(pop!)])
                                               (begin0 a
                                                 (set! ,(local-name (instr:local.tee-idx instr)) a))))]

                                    [op:global.set
                                     `(set! ,(global-name (instr:global.set-idx instr)) ,(pop!))]

                                    [op:global.get
                                     (push! (global-name (instr:global.get-idx instr)))]

                                    ;; Memory Instructions
                                    [op:i32.load     (push-load! (instr:i32.load-offset     instr) 4 'bytes->i32)]
                                    [op:i32.load8_s  (push-load! (instr:i32.load8_s-offset  instr) 1 'bytes->i32 #t)]
                                    [op:i32.load8_u  (push-load! (instr:i32.load8_u-offset  instr) 1 'bytes->u32 #t)]
                                    [op:i32.load16_s (push-load! (instr:i32.load16_s-offset instr) 2 'bytes->i32 #t)]
                                    [op:i32.load16_u (push-load! (instr:i32.load16_u-offset instr) 2 'bytes->u32 #t)]
                                    [op:i64.load     (push-load! (instr:i64.load-offset     instr) 8 'bytes->i64)]
                                    [op:i64.load8_s  (push-load! (instr:i64.load8_s-offset  instr) 1 'bytes->i64 #t)]
                                    [op:i64.load8_u  (push-load! (instr:i64.load8_u-offset  instr) 1 'bytes->u64 #t)]
                                    [op:i64.load16_s (push-load! (instr:i64.load16_s-offset instr) 2 'bytes->i64 #t)]
                                    [op:i64.load16_u (push-load! (instr:i64.load16_u-offset instr) 2 'bytes->u64 #t)]
                                    [op:i64.load32_s (push-load! (instr:i64.load32_s-offset instr) 4 'bytes->i64 #t)]
                                    [op:i64.load32_u (push-load! (instr:i64.load32_u-offset instr) 4 'bytes->u64 #t)]
                                    [op:f32.load     (push-load! (instr:f32.load-offset     instr) 4 'bytes->f32)]
                                    [op:f64.load     (push-load! (instr:f64.load-offset     instr) 8 'bytes->f64)]

                                    [op:i32.store   (gen-store! (instr:i32.store-offset   instr) 4 'i32->bytes)]
                                    [op:i32.store8  (gen-store! (instr:i32.store8-offset  instr) 1 'i32->bytes)]
                                    [op:i32.store16 (gen-store! (instr:i32.store16-offset instr) 2 'i32->bytes)]
                                    [op:i64.store   (gen-store! (instr:i64.store-offset   instr) 8 'i64->bytes)]
                                    [op:i64.store8  (gen-store! (instr:i64.store8-offset  instr) 1 'i64->bytes)]
                                    [op:i64.store16 (gen-store! (instr:i64.store16-offset instr) 2 'i64->bytes)]
                                    [op:i64.store32 (gen-store! (instr:i64.store32-offset instr) 4 'i64->bytes)]
                                    [op:f32.store   (gen-store! (instr:f32.store-offset   instr) 4 'f32->bytes)]
                                    [op:f64.store   (gen-store! (instr:f64.store-offset   instr) 8 'f64->bytes)]

                                    [op:memory.size
                                     (push! '(memory-size $mem))]

                                    [op:memory.grow
                                     (define res-name (gensym 'res))
                                     (begin0 `(define ,res-name
                                                (begin0 (memory-size $mem)
                                                  (memory-grow! $mem ,(pop!))))
                                       (push! res-name))]

                                    ;; Numeric Instructions
                                    [op:i32.const (push! (instr:i32.const-n instr))]
                                    [op:i64.const (push! (instr:i64.const-n instr))]
                                    [op:f32.const (push! (instr:f32.const-n instr))]
                                    [op:f64.const (push! (instr:f64.const-n instr))]

                                    [op:i32.add    (push-call2! 'iadd32)]
                                    [op:i32.sub    (push-call2! 'isub32)]
                                    [op:i32.mul    (push-call2! 'imul32)]
                                    [op:i32.div_u  (push-call2! 'idiv32_u)]
                                    [op:i32.div_s  (push-call2! 'idiv32_s)]
                                    [op:i32.rem_u  (push-call2! 'irem32_u)]
                                    [op:i32.rem_s  (push-call2! 'irem32_s)]
                                    [op:i32.and    (push-call2! 'iand32)]
                                    [op:i32.or     (push-call2! 'ior32)]
                                    [op:i32.xor    (push-call2! 'ixor32)]
                                    [op:i32.shl    (push-call2! 'ishl32)]
                                    [op:i32.shr_u  (push-call2! 'ishr32_u)]
                                    [op:i32.shr_s  (push-call2! 'ishr32_s)]
                                    [op:i32.rotl   (push-call2! 'irotl32)]
                                    [op:i32.rotr   (push-call2! 'irotr32)]
                                    [op:i32.clz    (push-call1! 'iclz32)]
                                    [op:i32.ctz    (push-call1! 'ictz32)]
                                    [op:i32.popcnt (push-call1! 'ipopcnt32)]
                                    [op:i32.eqz    (push-call1! 'ieqz32)]
                                    [op:i32.eq     (push-call2! 'ieq32)]
                                    [op:i32.ne     (push-call2! 'ine32)]
                                    [op:i32.lt_u   (push-call2! 'ilt32_u)]
                                    [op:i32.lt_s   (push-call2! 'ilt32_s)]
                                    [op:i32.gt_u   (push-call2! 'igt32_u)]
                                    [op:i32.gt_s   (push-call2! 'igt32_s)]
                                    [op:i32.le_u   (push-call2! 'ile32_u)]
                                    [op:i32.le_s   (push-call2! 'ile32_s)]
                                    [op:i32.ge_u   (push-call2! 'ige32_u)]
                                    [op:i32.ge_s   (push-call2! 'ige32_s)]

                                    [op:i64.add    (push-call2! 'iadd64)]
                                    [op:i64.sub    (push-call2! 'isub64)]
                                    [op:i64.mul    (push-call2! 'imul64)]
                                    [op:i64.div_u  (push-call2! 'idiv64_u)]
                                    [op:i64.div_s  (push-call2! 'idiv64_s)]
                                    [op:i64.rem_u  (push-call2! 'irem64_u)]
                                    [op:i64.rem_s  (push-call2! 'irem64_s)]
                                    [op:i64.and    (push-call2! 'iand64)]
                                    [op:i64.or     (push-call2! 'ior64)]
                                    [op:i64.xor    (push-call2! 'ixor64)]
                                    [op:i64.shl    (push-call2! 'ishl64)]
                                    [op:i64.shr_u  (push-call2! 'ishr64_u)]
                                    [op:i64.shr_s  (push-call2! 'ishr64_s)]
                                    [op:i64.rotl   (push-call2! 'irotl64)]
                                    [op:i64.rotr   (push-call2! 'irotr64)]
                                    [op:i64.clz    (push-call1! 'iclz64)]
                                    [op:i64.ctz    (push-call1! 'ictz64)]
                                    [op:i64.popcnt (push-call1! 'ipopcnt64)]
                                    [op:i64.eqz    (push-call1! 'ieqz64)]
                                    [op:i64.eq     (push-call2! 'ieq64)]
                                    [op:i64.ne     (push-call2! 'ine64)]
                                    [op:i64.lt_u   (push-call2! 'ilt64_u)]
                                    [op:i64.lt_s   (push-call2! 'ilt64_s)]
                                    [op:i64.gt_u   (push-call2! 'igt64_u)]
                                    [op:i64.gt_s   (push-call2! 'igt64_s)]
                                    [op:i64.le_u   (push-call2! 'ile64_u)]
                                    [op:i64.le_s   (push-call2! 'ile64_s)]
                                    [op:i64.ge_u   (push-call2! 'ige64_u)]
                                    [op:i64.ge_s   (push-call2! 'ige64_s)]

                                    [op:f32.abs      (push-call1! 'fabs32)]
                                    [op:f32.neg      (push-call1! 'fneg32)]
                                    [op:f32.ceil     (push-call1! 'fceil32)]
                                    [op:f32.floor    (push-call1! 'ffloor32)]
                                    [op:f32.trunc    (push-call1! 'ftrunc32)]
                                    [op:f32.nearest  (push-call1! 'fnearest32)]
                                    [op:f32.sqrt     (push-call1! 'fsqrt32)]
                                    [op:f32.add      (push-call2! 'fadd32)]
                                    [op:f32.sub      (push-call2! 'fsub32)]
                                    [op:f32.mul      (push-call2! 'fmul32)]
                                    [op:f32.div      (push-call2! 'fdiv32)]
                                    [op:f32.min      (push-call2! 'fmin32)]
                                    [op:f32.max      (push-call2! 'fmax32)]
                                    [op:f32.copysign (push-call2! 'fcopysign32)]
                                    [op:f32.eq       (push-call2! 'feq32)]
                                    [op:f32.ne       (push-call2! 'fne32)]
                                    [op:f32.lt       (push-call2! 'flt32)]
                                    [op:f32.gt       (push-call2! 'fgt32)]
                                    [op:f32.le       (push-call2! 'fle32)]
                                    [op:f32.ge       (push-call2! 'fge32)]

                                    [op:f64.abs      (push-call1! 'fabs64)]
                                    [op:f64.neg      (push-call1! 'fneg64)]
                                    [op:f64.ceil     (push-call1! 'fceil64)]
                                    [op:f64.floor    (push-call1! 'ffloor64)]
                                    [op:f64.trunc    (push-call1! 'ftrunc64)]
                                    [op:f64.nearest  (push-call1! 'fnearest64)]
                                    [op:f64.sqrt     (push-call1! 'fsqrt64)]
                                    [op:f64.add      (push-call2! 'fadd64)]
                                    [op:f64.sub      (push-call2! 'fsub64)]
                                    [op:f64.mul      (push-call2! 'fmul64)]
                                    [op:f64.div      (push-call2! 'fdiv64)]
                                    [op:f64.min      (push-call2! 'fmin64)]
                                    [op:f64.max      (push-call2! 'fmax64)]
                                    [op:f64.copysign (push-call2! 'fcopysign64)]
                                    [op:f64.eq       (push-call2! 'feq64)]
                                    [op:f64.ne       (push-call2! 'fne64)]
                                    [op:f64.lt       (push-call2! 'flt64)]
                                    [op:f64.gt       (push-call2! 'fgt64)]
                                    [op:f64.le       (push-call2! 'fle64)]
                                    [op:f64.ge       (push-call2! 'fge64)]

                                    [op:i32.wrap_i64        (push-call1! 'iwrap32)]
                                    [op:i32.trunc_f32_s     (push-call1! 'itrunc32_32_s)]
                                    [op:i32.trunc_f32_u     (push-call1! 'itrunc32_32_u)]
                                    [op:i32.trunc_f64_s     (push-call1! 'itrunc32_64_s)]
                                    [op:i32.trunc_f64_u     (push-call1! 'itrunc32_64_u)]
                                    [op:i64.extend_i32_s    (push-call1! 'iextend64_32_s)]
                                    [op:i64.extend_i32_u    (push-call1! 'iextend64_32_u)]
                                    [op:i64.trunc_f32_s     (push-call1! 'itrunc64_32_s)]
                                    [op:i64.trunc_f32_u     (push-call1! 'itrunc64_32_u)]
                                    [op:i64.trunc_f64_s     (push-call1! 'itrunc64_64_s)]
                                    [op:i64.trunc_f64_u     (push-call1! 'itrunc64_64_u)]
                                    [op:f32.convert_i32_s   (push-call1! 'fconvert32_32_s)]
                                    [op:f32.convert_i32_u   (push-call1! 'fconvert32_32_u)]
                                    [op:f32.convert_i64_s   (push-call1! 'fconvert32_64_s)]
                                    [op:f32.convert_i64_u   (push-call1! 'fconvert32_64_u)]
                                    [op:f32.demote_f64      (push-call1! 'fdemote64)]
                                    [op:f64.convert_i32_s   (push-call1! 'fconvert64_32_s)]
                                    [op:f64.convert_i32_u   (push-call1! 'fconvert64_32_u)]
                                    [op:f64.convert_i64_s   (push-call1! 'fconvert64_64_s)]
                                    [op:f64.convert_i64_u   (push-call1! 'fconvert64_64_u)]
                                    [op:f64.promote_f32     (push-call1! 'fpromote32)]
                                    [op:i32.reinterpret_f32 (push-call1! 'ireinterpret32)]
                                    [op:i64.reinterpret_f64 (push-call1! 'ireinterpret64)]
                                    [op:f32.reinterpret_i32 (push-call1! 'freinterpret32)]
                                    [op:f64.reinterpret_i64 (push-call1! 'freinterpret64)]

                                    [op:i32.extend8_s   (push-call1! 'iextend32_8_s)]
                                    [op:i32.extend16_s  (push-call1! 'iextend32_16_s)]
                                    [op:i64.extend8_s   (push-call1! 'iextend64_8_s)]
                                    [op:i64.extend16_s  (push-call1! 'iextend64_16_s)]
                                    [op:i64.extend32_s  (push-call1! 'iextend64_32_s)]

                                    [op:i32.trunc_sat_f32_s (push-call1! 'itrunc_sat32_32_s)]
                                    [op:i32.trunc_sat_f32_u (push-call1! 'itrunc_sat32_32_u)]
                                    [op:i32.trunc_sat_f64_s (push-call1! 'itrunc_sat32_64_s)]
                                    [op:i32.trunc_sat_f64_u (push-call1! 'itrunc_sat32_64_u)]
                                    [op:i64.trunc_sat_f32_s (push-call1! 'itrunc_sat64_32_s)]
                                    [op:i64.trunc_sat_f32_u (push-call1! 'itrunc_sat64_32_u)]
                                    [op:i64.trunc_sat_f64_s (push-call1! 'itrunc_sat64_64_s)]
                                    [op:i64.trunc_sat_f64_u (push-call1! 'itrunc_sat64_64_u)]

                                    [else
                                     (trap "~e not implemented" instr)]))

                                (cond
                                  [(void? e) exprs]
                                  [else (cons e exprs)])))

                            (cond
                              [(null? stack) exprs]
                              [(= (length stack) 1) (append exprs (list (car stack)))]
                              [else (append exprs `((values ,@(reverse stack))))]))))))))))

    (values ns the-mod (lambda ()
                         (namespace-require `(quote ,name))
                         ((namespace-variable-value '$init)
                          (store-table s)
                          (store-memory s)
                          (store-functions s))))))

(define (try-eliminate-label e)
  (match e
    [`(let/cc ,lbl ,body ...)
     (define used?
       (let loop ([e body])
         (cond
           [(symbol? e) (eq? lbl e)]
           [(list? e) (ormap loop e)]
           [else #f])))
     (cond
       [used? e]
       [else `(let () ,@body)])]))

(define (try-rewrite-switch e)
  (match e
    [`(let/cc ,outer-lbl
        (let/cc ,inner-lbl
          ,(and `(case ,_ ,_ ...) the-case))
        ,outer-body ...)
     `(let/cc ,outer-lbl
        (switch/todo ,the-case ((,inner-lbl ,outer-body))))]

    [`(let/cc ,outer-lbl
        (let/cc ,inner-lbl
          (switch/todo ,the-case ,parts))
        ,outer-body ...)
     `(let/cc ,outer-lbl
        (switch/todo ,the-case ((,inner-lbl ,outer-body) ,@parts)))]

    [_ e]))

(define (resugar e)
  (match e
    [`(switch/todo (case ,case-e ,clauses ...) ,parts)
     (define (get-code label)
       (define code
         (for/first ([p (in-list parts)] #:when (eq? (car p) label))
           (cadr p)))
       (cond
         [(not code) `((,label))]
         [(null? code) '((void))]
         [else code]))

     `(switch ,case-e
        ,@(for/fold ([res-clauses null]
                     [last-label #f]
                     #:result (reverse res-clauses))
                    ([clause (in-list clauses)])
            (define-values (label res-clause)
              (match clause
                [`((,lit) (,label))
                 (values label `[(,lit) ,@(get-code label)])]
                [`(else (,label))
                 (values label `[else ,@(get-code label)])]))
            (cond
              [(eq? label last-label)
               (define new-res-clauses
                 (match* (res-clauses res-clause)
                   [(`([,lits ,code ...] ,res-clauses ...)
                     `((,lit) ,_ ...))
                    (cons `[(,@(cons lit lits)) ,@code] res-clauses)]))
               (values new-res-clauses label)]
              [else
               (values (cons res-clause res-clauses) label)])))]

    [(? list?)
     (map resugar e)]

    [_ e]))

(define (make-arg-names type)
  (for/list ([i (in-range (sub1 (length (functype-params type))) -1 -1)])
    (arg-name i)))

(define (make-res-names type)
  (for/list ([_ (in-range (length (functype-results type)))])
    (gensym '$r)))

(define (func-name idx)
  (string->symbol (format "$f~a" idx)))

(define (arg-name idx)
  (string->symbol (format "$a~a" idx)))

(define (global-name idx)
  (string->symbol (format "$g~a" idx)))

(define (local-name idx)
  (string->symbol (format "$l~a" idx)))
