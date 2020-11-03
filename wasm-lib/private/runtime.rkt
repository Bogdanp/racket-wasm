#lang racket/base

(require (for-syntax racket/base
                     racket/syntax)
         (submod racket/performance-hint begin-encourage-inline)
         racket/unsafe/ops
         syntax/parse/define)

;; On 64bit systems, all the unsafe ops can safely operate on i32
;; values so use those when possible.  64bit fixnums can't fully
;; represent i64 values so the same optimization is not possible
;; there.
(define-syntax-parser define-i32-op
  [(_ op:id)
   #:with name (format-id #'op "i32~a" #'op)
   #:with unsafe-op (format-id #'op "unsafe-fx~a" #'op)
   (case (system-type 'word)
     [(32) #'(define name op)]
     [(64) #'(define name unsafe-op)])])

;; Dito for single flonums on 64bit systems.
(define-syntax-parser define-f32-op
  [(_ op:id)
   #:with name (format-id #'op "f32~a" #'op)
   #:with unsafe-op (format-id #'op "unsafe-fl~a" #'op)
   (case (system-type 'word)
     [(32) #'(define name op)]
     [(64) #'(define name unsafe-op)])])

(define-syntax-rule (define-i32-ops op ...) (begin (define-i32-op op) ...))
(define-syntax-rule (define-f32-ops op ...) (begin (define-f32-op op) ...))

(define-i32-ops = < <= > >= + - * quotient modulo remainder and ior xor lshift rshift)
(define-f32-ops = < <= > >= + - * /)

(define conversion-buf (make-bytes 8))

(define (u->s n [size 4])
  (integer->integer-bytes n size #f #f conversion-buf)
  (integer-bytes->integer conversion-buf #t #f 0 size))

(define (s->u n [size 4])
  (integer->integer-bytes n size #t #f conversion-buf)
  (integer-bytes->integer conversion-buf #f #f 0 size))

(define-syntax-parser define-clz
  [(_ (name:id v:id)
      (~seq #:bits bits:number)
      (~seq #:<-fn <-fn:expr))
   #:with ((clause cnt) ...) (let ([bits (syntax->datum #'bits)])
                               (for/list ([n (in-range bits)])
                                 (with-syntax ([n (datum->syntax #'bits (- bits n))]
                                               [e (datum->syntax #'bits (expt 2 n))])
                                   (list #'(<-fn v e) #'n))))
   #'(define (name v)
       (cond [clause cnt] ...))])

(define-syntax-parser define-ctz
  [(_ (name:id v:id)
      (~seq #:bits bits:number)
      (~seq #:=-fn =-fn:expr)
      (~seq #:&-fn &-fn:expr))
   #:with ((clause cnt) ...) (let ([bits (syntax->datum #'bits)])
                               (for/list ([n (in-range bits)])
                                 (with-syntax ([n (datum->syntax #'bits n)]
                                               [e (datum->syntax #'bits (expt 2 n))])
                                   (list #'(=-fn e (&-fn v e)) #'n))))
   #'(define (name v)
       (cond
         [(=-fn v 0) bits]
         [clause cnt] ...))])

(define ((make-popcnt bits rsh &) n)
  (let loop ([n n]
             [pop 0]
             [bits bits])
    (cond
      [(i32= bits 0) pop]
      [else (loop (rsh n 1)
                  (if (i32= 1 (& n 1)) (i32+ pop 1) pop)
                  (i32- bits 1))])))

(define i32max #xFFFFFFFF)
(define i32popcnt (make-popcnt 32 i32rshift i32and))
(define-clz (i32clz v)
  #:bits 32
  #:<-fn i32<)
(define-ctz (i32ctz v)
  #:bits 32
  #:=-fn i32=
  #:&-fn i32and)

(define i64max #xFFFFFFFFFFFFFFFF)
(define i64popcnt (make-popcnt 64
                               (lambda (n amt)
                                 (arithmetic-shift n (- amt)))
                               bitwise-and))
(define-clz (i64clz v)
  #:bits 64
  #:<-fn <)
(define-ctz (i64ctz v)
  #:bits 64
  #:=-fn =
  #:&-fn bitwise-and)

(module+ i32
  (provide (all-defined-out))
  (begin-encourage-inline
    (define (iadd32 a b)   (i32modulo (i32+ a b) i32max))
    (define (isub32 a b)   (i32modulo (i32+ (i32- a b) i32max) i32max))
    (define (imul32 a b)   (i32modulo (i32* a b) i32max))
    (define (idiv32_u a b) (i32quotient a b))
    (define (idiv32_s a b) (i32quotient (u->s a) (u->s b)))
    (define (irem32_u a b) (i32remainder a b))
    (define (irem32_s a b) (i32remainder (u->s a) (u->s b)))
    (define (iand32 a b)   (i32and a b))
    (define (ior32 a b)    (i32ior a b))
    (define (ixor32 a b)   (i32xor a b))
    (define (ishl32 a b)   (i32lshift a (i32modulo b 32)))
    (define (ishr32_u a b) (i32rshift a (i32modulo b 32)))
    (define (ishr32_s a b) (i32rshift a (i32modulo b 32))) ;; FIXME: sign extension
    (define (iclz32 a)     (i32clz a))
    (define (ictz32 a)     (i32ctz a))
    (define (ipopcnt32 a)  (i32popcnt a))
    (define (ieqz32 a)     (if (i32= a 0) 1 0))
    (define (ieq32 a b)    (if (i32= a b) 1 0))
    (define (ine32 a b)    (if (i32= a b) 0 1))))

(module+ i64
  (provide (all-defined-out))
  (begin-encourage-inline
    (define (iadd64 a b)   (modulo (+ a b) i64max))
    (define (isub64 a b)   (modulo (+ (- a b) i64max) i64max))
    (define (imul64 a b)   (modulo (* a b) i64max))
    (define (idiv64_u a b) (quotient a b))
    (define (idiv64_s a b) (quotient (u->s a) (u->s b)))
    (define (irem64_u a b) (remainder a b))
    (define (irem64_s a b) (remainder (u->s a) (u->s b)))
    (define (iand64 a b)   (bitwise-and a b))
    (define (ior64 a b)    (bitwise-ior a b))
    (define (ixor64 a b)   (bitwise-xor a b))
    (define (ishl64 a b)   (arithmetic-shift a (modulo b 64)))
    (define (ishr64_u a b) (arithmetic-shift a (- (modulo b 64))))
    (define (ishr64_s a b) (arithmetic-shift a (- (modulo b 64)))) ;; FIXME: signe extension
    (define (iclz64 a)     (i64clz a))
    (define (ictz64 a)     (i64ctz a))
    (define (ipopcnt64 a)  (i64popcnt a))
    (define (ieqz64 a)     (if (= a 0) 1 0))
    (define (ieq64 a b)    (if (= a b) 1 0))
    (define (ine64 a b)    (if (= a b) 0 1))))