#lang racket/base

(require racket/match
         "core.rkt"
         "error.rkt"
         "opcase.rkt"
         "store.rkt")

(provide
 compile-mod)

(define (compile-mod m links [name 'wasm])
  (define s (make-store m links))
  (define ns (make-base-namespace))
  (parameterize ([current-namespace ns])
    (when (store-table s)
      (namespace-set-variable-value! '$table (store-table s)))
    (when (store-memory s)
      (namespace-set-variable-value! '$memory (store-memory s)))
    (when (store-globals s)
      (namespace-set-variable-value! '$globals (store-globals s)))
    (for ([f (in-vector (store-functions s))]
          [i (in-naturals)])
      #:break (localfunc? f)
      (namespace-set-variable-value! (extern-name i) (externfunc-f f)))
    (define the-mod
      `(module ,name racket/base
         (require (only-in wasm/private/error trap)
                  wasm/private/memory
                  wasm/private/runtime)

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
                ,@(for/list ([id (in-list local-regs)])
                    `(define ,id #f))
                ,@(let compile-block ([instrs (code-instrs code)]
                                      [stack null])
                    (let* ([push! (lambda (e)
                                    (set! stack (cons e stack)))]
                           [pop! (lambda ()
                                   (begin0 (car stack)
                                     (set! stack (cdr stack))))]
                           [push-call/2! (lambda (e)
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

                              [op:if
                               `(cond
                                  [(zero? ,(pop!))
                                   ,@(cond
                                       [(instr:if-else-code instr)
                                        => (lambda (else-instrs)
                                             (compile-block else-instrs stack))]
                                       [else '(void)])]

                                  [else
                                   ,@(cond
                                       [(instr:if-then-code instr)
                                        => (lambda (then-instrs)
                                             (compile-block then-instrs stack))]
                                       [else '(void)])])]

                              [op:call
                               (define idx (instr:call-idx instr))
                               (define-values (type name)
                                 (match (vector-ref (store-functions s) idx)
                                   [(externfunc type _) (values type (extern-name idx))]
                                   [(localfunc  type _) (values type (func-name   idx))]))
                               (define arg-names
                                 (for/list ([i (in-range (sub1 (length (functype-params type))) -1 -1)])
                                   (arg-name i)))
                               (define res-names
                                 (for/list ([_ (in-range (length (functype-results type)))])
                                   (gensym 'res)))
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
                                    (for ([res-name (in-list res-names)])
                                      (push! res-name)))])]

                              ;; Variable Instructions
                              [op:local.get (push! (local-name (instr:local.get-idx instr)))]

                              ;; Numeric Instructions
                              [op:i32.const (push! (instr:i32.const-n instr))]
                              [op:i64.const (push! (instr:i64.const-n instr))]
                              [op:f32.const (push! (instr:f32.const-n instr))]
                              [op:f64.const (push! (instr:f64.const-n instr))]

                              [op:i32.add  (push-call/2! 'iadd32)]
                              [op:i32.sub  (push-call/2! 'isub32)]
                              [op:i32.lt_s (push-call/2! 'ilt32_s)]
                              [op:i32.lt_u (push-call/2! 'ilt32_u)]
                              [op:i32.gt_s (push-call/2! 'igt32_s)]
                              [op:i32.gt_u (push-call/2! 'igt32_u)]
                              [op:i32.le_s (push-call/2! 'ile32_s)]
                              [op:i32.le_u (push-call/2! 'ile32_u)]
                              [op:i32.ge_s (push-call/2! 'ige32_s)]
                              [op:i32.ge_u (push-call/2! 'ige32_u)]

                              [else
                               (trap "~e not implemented" instr)]))

                          (cond
                            [(void? e) exprs]
                            [else (cons e exprs)])))

                      (cond
                        [(null? stack) exprs]
                        [else (append exprs `((values ,@(reverse stack))))])))))))

    (values ns the-mod)))

(define (extern-name idx)
  (string->symbol (format "$extern.~a" idx)))

(define (func-name idx)
  (string->symbol (format "$func.~a" idx)))

(define (arg-name idx)
  (string->symbol (format "$arg.~a" idx)))

(define (local-name idx)
  (string->symbol (format "$local.~a" idx)))
