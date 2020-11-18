#lang racket/base

(require racket/match
         racket/pretty
         wasm/private/error
         wasm/private/memory
         wasm/private/runtime
         wasm/private/store
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
    (define the-mod
      `(module ,name racket/base
         (require (only-in wasm/private/error trap)
                  wasm/private/memory
                  wasm/private/runtime
                  wasm/private/store)

         (define-namespace-anchor $anchor)

         (define $table #f)
         (define $memory #f)

         ,@(for/list ([_ (in-vector (store-globals s))]
                      [i (in-naturals)])
             `(define ,(global-name i) 0))

         ,@(for/list ([f (in-vector (store-functions s))]
                      [i (in-naturals)])
             #:break (localfunc? f)
             `(define ,(func-name i) #f))

         (provide $init)
         (define ($init table memory functions)
           (set! $table table)
           (set! $memory memory)
           ,@(for/list ([f (in-vector (store-functions s))]
                        [i (in-naturals)])
               #:break (localfunc? f)
               `(set! ,(func-name i) (externfunc-f (vector-ref functions ,i)))))

         ,@(for/list ([e (in-vector (mod-exports m))])
             (define export-id (string->symbol (export-name e)))
             (match (export-description e)
               [(funcidx idx)
                `(provide (rename-out [,(func-name idx) ,export-id]))]
               [(memidx _)
                `(provide (rename-out [$memory ,export-id]))]))

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
                (define $buf (make-bytes 8))
                (let/cc $return
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
                             [split-stack! (lambda (type)
                                             (let loop ([block-stack null]
                                                        [remaining (length (functype-params type))])
                                               (cond
                                                 [(zero? remaining) (reverse block-stack)]
                                                 [else (loop (cons (pop!) block-stack) (sub1 remaining))])))]
                             [push-call1! (lambda (e)
                                            (push! `(,e ,(pop!))))]
                             [push-call2! (lambda (e)
                                            (push! `(let ([b ,(pop!)]
                                                          [a ,(pop!)])
                                                      (,e a b))))])
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
                                 (define block-stack (split-stack! type))
                                 (define res-names (make-res-names type))
                                 (define lbl-name (gensym 'label))
                                 (define block
                                   `(let/cc ,lbl-name
                                      ,@(cond
                                          [(instr:block-code instr)
                                           => (lambda (block-instrs)
                                                (compile-block block-instrs (cons lbl-name labels) block-stack))]
                                          [else '((void))])))
                                 (cond
                                   [(null? res-names) block]
                                   [else
                                    (begin0 `(define-values (,@res-names) ,block)
                                      (for-each push! res-names))])]

                                [op:loop
                                 (define type (instr:loop-type instr))
                                 (define block-stack (split-stack! type))
                                 (define res-names (make-res-names type))
                                 (define lbl-name (gensym 'label))
                                 (define block
                                   (cond
                                     [(instr:loop-code instr)
                                      => (lambda (loop-instrs)
                                           `(let/cc $break
                                              (let loop ()
                                                (let/cc ,lbl-name
                                                  (call-with-values
                                                   (lambda ()
                                                     ,@(compile-block loop-instrs (cons lbl-name labels) block-stack))
                                                   $break))
                                                (loop))))]
                                     [else '(void)]))
                                 (cond
                                   [(null? res-names) block]
                                   [else
                                    (begin0 `(define-values (,@res-names) ,block)
                                      (for-each push! res-names))])]

                                [op:if
                                 (define type (instr:if-type instr))
                                 (define block-stack (split-stack! type))
                                 (define res-names (make-res-names type))
                                 (define lbl-name (gensym 'label))
                                 (define block
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
                                             [else '((void))])])))
                                 (cond
                                   [(null? res-names) block]
                                   [else
                                    (begin0 `(define-values (,@res-names) ,block)
                                      (for-each push! res-names))])]

                                [op:return
                                 `($return ,@stack)]

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
                                   `(let* ([idx ,idx-e]
                                           [funcidx (vector-ref $table idx)]
                                           [funcsym (string->symbol (format "$func.~a" funcidx))])
                                      (let (,@arg-binders)
                                        ((eval funcsym (namespace-anchor->namespace $anchor)) ,@(reverse arg-names)))))
                                 (cond
                                   [(null? res-names) call]
                                   [else
                                    (begin0 `(define-values (,@res-names) ,call)
                                      (for-each push! res-names))])]

                                ;; Parametric Instructions
                                [op:drop
                                 (void (pop!))]

                                [op:select
                                 (define res-name (gensym 'res))
                                 (begin0 `(define ,res-name
                                            (let ([c  ,(pop!)]
                                                  [v2 ,(pop!)]
                                                  [v1 ,(pop!)])
                                              (if (zero? c) v2 v1)))
                                   (push! res-name))]

                                ;; Variable Instructions
                                [op:local.get
                                 (push! (local-name (instr:local.get-idx instr)))]

                                [op:local.set
                                 `(set! ,(local-name (instr:local.set-idx instr)) ,(pop!))]

                                [op:local.tee
                                 (define res-name (gensym 'res))
                                 (begin0 `(define ,res-name
                                            (let ([a ,(pop!)])
                                              (begin0 a
                                                (set! ,(local-name (instr:local.tee-idx instr)) a))))
                                   (push! res-name))]

                                [op:global.set
                                 `(set! ,(global-name (instr:global.set-idx instr)) ,(pop!))]

                                [op:global.get
                                 (push! (global-name (instr:global.get-idx instr)))]

                                ;; Memory Instructions
                                [op:i32.load
                                 (define res-name (gensym 'res))
                                 (begin0 `(define ,res-name
                                            (let ([ea (+ ,(pop!) ,(instr:i32.load-offset instr))])
                                              (memory-load! $memory $buf ea 4)
                                              (bytes->i32 $buf 4)))
                                   (push! res-name))]

                                [op:i32.load8_u
                                 (define res-name (gensym 'res))
                                 (begin0 `(define ,res-name
                                            (let ([ea (+ ,(pop!) ,(instr:i32.load8_u-offset instr))])
                                              (memory-load! $memory $buf ea 1)
                                              (bytes->u32 $buf 1)))
                                   (push! res-name))]

                                [op:i32.load8_s
                                 (define res-name (gensym 'res))
                                 (begin0 `(define ,res-name
                                            (let ([ea (+ ,(pop!) ,(instr:i32.load8_s-offset instr))])
                                              (memory-load! $memory $buf ea 1)
                                              (bytes->i32 $buf 1)))
                                   (push! res-name))]

                                [op:i32.load16_s
                                 (define res-name (gensym 'res))
                                 (begin0 `(define ,res-name
                                            (let ([ea (+ ,(pop!) ,(instr:i32.load16_s-offset instr))])
                                              (memory-load! $memory $buf ea 2)
                                              (bytes->i32 $buf 2)))
                                   (push! res-name))]

                                [op:i32.load16_u
                                 (define res-name (gensym 'res))
                                 (begin0 `(define ,res-name
                                            (let ([ea (+ ,(pop!) ,(instr:i32.load16_u-offset instr))])
                                              (memory-load! $memory $buf ea 2)
                                              (bytes->u32 $buf 2)))
                                   (push! res-name))]

                                [op:i64.load
                                 (define res-name (gensym 'res))
                                 (begin0 `(define ,res-name
                                            (let ([ea (+ ,(pop!) ,(instr:i64.load-offset instr))])
                                              (memory-load! $memory $buf ea 8)
                                              (bytes->i64 $buf 8)))
                                   (push! res-name))]

                                [op:i64.load8_u
                                 (define res-name (gensym 'res))
                                 (begin0 `(define ,res-name
                                            (let ([ea (+ ,(pop!) ,(instr:i64.load8_u-offset instr))])
                                              (memory-load! $memory $buf ea 1)
                                              (bytes->u64 $buf 1)))
                                   (push! res-name))]

                                [op:i64.load8_s
                                 (define res-name (gensym 'res))
                                 (begin0 `(define ,res-name
                                            (let ([ea (+ ,(pop!) ,(instr:i64.load8_s-offset instr))])
                                              (memory-load! $memory $buf ea 1)
                                              (bytes->i64 $buf 1)))
                                   (push! res-name))]

                                [op:i64.load16_s
                                 (define res-name (gensym 'res))
                                 (begin0 `(define ,res-name
                                            (let ([ea (+ ,(pop!) ,(instr:i64.load16_s-offset instr))])
                                              (memory-load! $memory $buf ea 2)
                                              (bytes->i64 $buf 2)))
                                   (push! res-name))]

                                [op:i64.load16_u
                                 (define res-name (gensym 'res))
                                 (begin0 `(define ,res-name
                                            (let ([ea (+ ,(pop!) ,(instr:i64.load16_u-offset instr))])
                                              (memory-load! $memory $buf ea 2)
                                              (bytes->u64 $buf 2)))
                                   (push! res-name))]

                                [op:i64.load32_s
                                 (define res-name (gensym 'res))
                                 (begin0 `(define ,res-name
                                            (let ([ea (+ ,(pop!) ,(instr:i64.load32_s-offset instr))])
                                              (memory-load! $memory $buf ea 4)
                                              (bytes->i64 $buf 4)))
                                   (push! res-name))]

                                [op:i64.load32_u
                                 (define res-name (gensym 'res))
                                 (begin0 `(define ,res-name
                                            (let ([ea (+ ,(pop!) ,(instr:i64.load32_u-offset instr))])
                                              (memory-load! $memory $buf ea 4)
                                              (bytes->u64 $buf 4)))
                                   (push! res-name))]

                                [op:f32.load
                                 (define res-name (gensym 'res))
                                 (begin0 `(define ,res-name
                                            (let ([ea (+ ,(pop!) ,(instr:f32.load-offset instr))])
                                              (memory-load! $memory $buf ea 4)
                                              (bytes->f32 $buf)))
                                   (push! res-name))]

                                [op:f64.load
                                 (define res-name (gensym 'res))
                                 (begin0 `(define ,res-name
                                            (let ([ea (+ ,(pop!) ,(instr:f64.load-offset instr))])
                                              (memory-load! $memory $buf ea 8)
                                              (bytes->f64 $buf)))
                                   (push! res-name))]

                                [op:i32.store
                                 `(let ([n ,(pop!)]
                                        [ea (+ ,(pop!) ,(instr:i32.store-offset instr))])
                                    (memory-store! $memory ea (i32->bytes n $buf) 4))]

                                [op:i32.store8
                                 `(let ([n ,(pop!)]
                                        [ea (+ ,(pop!) ,(instr:i32.store8-offset instr))])
                                    (memory-store! $memory ea (i32->bytes n $buf) 1))]

                                [op:i32.store16
                                 `(let ([n ,(pop!)]
                                        [ea (+ ,(pop!) ,(instr:i32.store16-offset instr))])
                                    (memory-store! $memory ea (i32->bytes n $buf) 2))]

                                [op:i64.store
                                 `(let ([n ,(pop!)]
                                        [ea (+ ,(pop!) ,(instr:i64.store-offset instr))])
                                    (memory-store! $memory ea (i64->bytes n $buf) 8))]

                                [op:i64.store8
                                 `(let ([n ,(pop!)]
                                        [ea (+ ,(pop!) ,(instr:i64.store8-offset instr))])
                                    (memory-store! $memory ea (i64->bytes n $buf) 1))]

                                [op:i64.store16
                                 `(let ([n ,(pop!)]
                                        [ea (+ ,(pop!) ,(instr:i64.store16-offset instr))])
                                    (memory-store! $memory ea (i64->bytes n $buf) 2))]

                                [op:i64.store32
                                 `(let ([n ,(pop!)]
                                        [ea (+ ,(pop!) ,(instr:i64.store32-offset instr))])
                                    (memory-store! $memory ea (i64->bytes n $buf) 4))]

                                [op:f32.store
                                 `(let ([n ,(pop!)]
                                        [ea (+ ,(pop!) ,(instr:f32.store-offset instr))])
                                    (memory-store! $memory ea (f32->bytes n $buf) 4))]

                                [op:f64.store
                                 `(let ([n ,(pop!)]
                                        [ea (+ ,(pop!) ,(instr:f64.store-offset instr))])
                                    (memory-store! $memory ea (f64->bytes n $buf) 8))]

                                [op:memory.size
                                 (push! '(memory-size $memory))]

                                [op:memory.grow
                                 (define res-name (gensym 'res))
                                 (begin0 `(define ,res-name
                                            (begin0 (memory-size $memory)
                                              (memory-grow! $memory ,(pop!))))
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
                          [else (append exprs `((values ,@(reverse stack))))]))))))))

    (pretty-print the-mod)

    (values ns
            (compile the-mod)
            (lambda ()
              (namespace-require `(quote ,name))
              ((namespace-variable-value '$init)
               (store-table s)
               (store-memory s)
               (store-functions s))))))

(define (make-arg-names type)
  (for/list ([i (in-range (sub1 (length (functype-params type))) -1 -1)])
    (arg-name i)))

(define (make-res-names type)
  (for/list ([_ (in-range (length (functype-results type)))])
    (gensym 'res)))

(define (func-name idx)
  (string->symbol (format "$func.~a" idx)))

(define (arg-name idx)
  (string->symbol (format "$arg.~a" idx)))

(define (global-name idx)
  (string->symbol (format "$global.~a" idx)))

(define (local-name idx)
  (string->symbol (format "$local.~a" idx)))
