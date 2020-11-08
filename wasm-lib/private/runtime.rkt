#lang racket/base

(require (for-syntax racket/base
                     racket/syntax)
         (submod racket/performance-hint begin-encourage-inline)
         racket/flonum
         racket/math
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

;; Ditto for single flonums on 64bit systems.
(define-syntax-parser define-f32-op
  [(_ op:id)
   #:with name (format-id #'op "f32~a" #'op)
   #:with unsafe-op (format-id #'op "unsafe-fl~a" #'op)
   (case (system-type 'word)
     [(32) #'(define name op)]
     [(64) #'(define name unsafe-op)])])

(define-syntax-rule (define-i32-ops op ...) (begin (define-i32-op op) ...))
(define-syntax-rule (define-f32-ops op ...) (begin (define-f32-op op) ...))

(define-i32-ops = < <= > >= + - * quotient remainder and ior xor lshift rshift)
(define-f32-ops = < <= > >= + - * /)

(begin-encourage-inline
  (define (u->s n [size 4] [buf (make-bytes size)])
    (integer->integer-bytes n size #f #f buf)
    (integer-bytes->integer buf #t #f 0 size))

  (define (s->u n [size 4] [buf (make-bytes size)])
    (integer->integer-bytes n size #t #f buf)
    (integer-bytes->integer buf #f #f 0 size))

  (define (u32->s32 n [buf #f]) (u->s n 4 (or buf (make-bytes 4))))
  (define (u64->s64 n [buf #f]) (u->s n 8 (or buf (make-bytes 8))))
  (define (s32->u32 n [buf #f]) (s->u n 4 (or buf (make-bytes 4))))
  (define (s64->u64 n [buf #f]) (s->u n 8 (or buf (make-bytes 8)))))

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

(define i8max  #xFF)
(define i16max #xFFFFF)
(define i32max #xFFFFFFFF)
(define i64max #xFFFFFFFFFFFFFFFF)

(define i32popcnt (make-popcnt 32 i32rshift i32and))
(define-clz (i32clz v)
  #:bits 32
  #:<-fn i32<)
(define-ctz (i32ctz v)
  #:bits 32
  #:=-fn i32=
  #:&-fn i32and)

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

(begin-encourage-inline
  (define (integer->bytes n [size 4] [buf (make-bytes size)])
    (integer->integer-bytes n size #t #f buf))

  (define (bytes->integer buf [size 4] [signed? #t])
    (integer-bytes->integer buf signed? #f 0 size))

  (define (real->bytes n [size 4] [buf (make-bytes size)])
    (real->floating-point-bytes n size #f buf))

  (define (bytes->real buf [size 4])
    (floating-point-bytes->real buf #f 0 size)))

(module+ i32
  (provide (all-defined-out))
  (begin-encourage-inline
    (define (i32->bytes n buf)        (integer->bytes n 4 buf))
    (define (bytes->i32 buf [size 4]) (bytes->integer buf size))
    (define (bytes->u32 buf [size 4]) (u32->s32 (bytes->integer buf size #f)))

    (define (iadd32 a b)       (i32remainder (i32+ a b) i32max))
    (define (isub32 a b)       (i32remainder (i32- a b) i32max))
    (define (imul32 a b)       (i32remainder (i32* a b) i32max))
    (define (idiv32_u a b buf) (u32->s32 (i32quotient (s32->u32 a buf) (s32->u32 b buf)) buf))
    (define (idiv32_s a b buf) (i32quotient a b))
    (define (irem32_u a b buf) (u32->s32 (i32remainder (s32->u32 a buf) (s32->u32 b buf))))
    (define (irem32_s a b buf) (i32remainder a b))
    (define (iand32 a b)       (i32and a b))
    (define (ior32 a b)        (i32ior a b))
    (define (ixor32 a b)       (i32xor a b))
    (define (ishl32 a b)       (i32lshift a (i32remainder b 32)))
    (define (ishr32_u a b buf) (i32rshift a (i32remainder b 32))) ;; FIXME
    (define (ishr32_s a b buf) (i32rshift a (i32remainder b 32))) ;; FIXME: sign extension
    (define (iclz32 a)         (i32clz a))
    (define (ictz32 a)         (i32ctz a))
    (define (ipopcnt32 a)      (i32popcnt a))
    (define (ieqz32 a)         (if (i32= a 0) 1 0))
    (define (ieq32 a b)        (if (i32= a b) 1 0))
    (define (ine32 a b)        (if (i32= a b) 0 1))
    (define (ilt32_u a b buf)  (if (i32< (s32->u32 a buf) (s32->u32 b buf)) 1 0))
    (define (ilt32_s a b buf)  (if (i32< a b) 1 0))
    (define (igt32_u a b buf)  (if (i32> (s32->u32 a buf) (s32->u32 b buf)) 1 0))
    (define (igt32_s a b buf)  (if (i32> a b) 1 0))
    (define (ile32_u a b buf)  (if (i32<= (s32->u32 a buf) (s32->u32 b buf)) 1 0))
    (define (ile32_s a b buf)  (if (i32<= a b) 1 0))
    (define (ige32_u a b buf)  (if (i32>= (s32->u32 a buf) (s32->u32 b buf)) 1 0))
    (define (ige32_s a b buf)  (if (i32>= a b) 1 0))
    (define (iwrap32 n)        (remainder n i32max))))

(module+ i64
  (provide (all-defined-out))
  (begin-encourage-inline
    (define (i64->bytes n buf)        (integer->bytes n 8 buf))
    (define (bytes->i64 buf [size 8]) (bytes->integer buf size))
    (define (bytes->u64 buf [size 8]) (u64->s64 (bytes->integer buf size #f)))

    (define (iadd64 a b)       (remainder (+ a b) i64max))
    (define (isub64 a b)       (remainder (- a b) i64max))
    (define (imul64 a b)       (remainder (* a b) i64max))
    (define (idiv64_u a b buf) (u64->s64 (quotient (s64->u64 a buf) (s64->u64 b buf))))
    (define (idiv64_s a b buf) (quotient a b))
    (define (irem64_u a b buf) (u64->s64 (remainder (s64->u64 a buf) (s64->u64 b buf))))
    (define (irem64_s a b buf) (remainder a b))
    (define (iand64 a b)       (bitwise-and a b))
    (define (ior64 a b)        (bitwise-ior a b))
    (define (ixor64 a b)       (bitwise-xor a b))
    (define (ishl64 a b)       (arithmetic-shift a (remainder b 64)))
    (define (ishr64_u a b buf) (arithmetic-shift a (- (remainder b 64)))) ;; FIXME
    (define (ishr64_s a b buf) (arithmetic-shift a (- (remainder b 64)))) ;; FIXME: sign extension
    (define (iclz64 a)         (i64clz a))
    (define (ictz64 a)         (i64ctz a))
    (define (ipopcnt64 a)      (i64popcnt a))
    (define (ieqz64 a)         (if (= a 0) 1 0))
    (define (ieq64 a b)        (if (= a b) 1 0))
    (define (ine64 a b)        (if (= a b) 0 1))
    (define (ilt64_u a b buf)  (if (<  (s64->u64 a buf) (s64->u64 b buf)) 1 0))
    (define (ilt64_s a b buf)  (if (<  a b) 1 0))
    (define (igt64_u a b buf)  (if (>  (s64->u64 a buf) (s64->u64 b buf)) 1 0))
    (define (igt64_s a b buf)  (if (>  a b) 1 0))
    (define (ile64_u a b buf)  (if (<= (s64->u64 a buf) (s64->u64 b buf)) 1 0))
    (define (ile64_s a b buf)  (if (<= a b) 1 0))
    (define (ige64_u a b buf)  (if (>= (s64->u64 a buf) (s64->u64 b buf)) 1 0))
    (define (ige64_s a b buf)  (if (>= a b) 1 0))

    (define (itrunc64_u n buf) (u64->s64 (s64->u64 (inexact->exact (truncate n)) buf) buf))
    (define (itrunc64_s n buf) (inexact->exact (truncate n)))))

(module+ f32
  (provide (all-defined-out))
  (begin-encourage-inline
    (define (f32->bytes n buf) (real->bytes n 4 buf))
    (define (bytes->f32 buf)   (bytes->real buf 4))

    (define (fdemote64 n buf) n)))

(module+ f64
  (provide (all-defined-out))
  (begin-encourage-inline
    (define (f64->bytes n buf) (real->bytes n 8 buf))
    (define (bytes->f64 buf)   (bytes->real buf 8))

    (define (fadd64 a b) (fl+  a b))
    (define (fsub64 a b) (fl-  a b))
    (define (fmul64 a b) (fl*  a b))
    (define (fdiv64 a b) (fl/  a b))
    (define (feq64  a b) (if (=    a b) 1 0))
    (define (fne64  a b) (if (=    a b) 0 1))
    (define (flt64  a b) (if (fl<  a b) 1 0))
    (define (fgt64  a b) (if (fl>  a b) 1 0))
    (define (fle64  a b) (if (fl<= a b) 1 0))
    (define (fge64  a b) (if (fl>= a b) 1 0))

    (define (fpromote32   n buf) n)
    (define (fconvert64_u n buf) (exact->inexact (s64->u64 n)))
    (define (fconvert64_s n buf) (exact->inexact n))))
