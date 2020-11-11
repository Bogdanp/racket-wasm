#lang racket/base

(require (for-syntax racket/base)
         (submod racket/performance-hint begin-encourage-inline)
         ffi/unsafe
         ffi/unsafe/define
         racket/runtime-path)

(define-runtime-path libdir "lib")
(define-ffi-definer define-runtime
  (ffi-lib (build-path libdir "runtime")))

(begin-encourage-inline
  (define (u->s n [size 4] [buf (make-bytes size)])
    (integer->integer-bytes n size #f #f buf)
    (integer-bytes->integer buf #t #f 0 size))

  (define (u32->s32 n [buf #f]) (u->s n 4 (or buf (make-bytes 4))))
  (define (u64->s64 n [buf #f]) (u->s n 8 (or buf (make-bytes 8)))))

(begin-encourage-inline
  (define (integer->bytes n [size 4] [buf (make-bytes size)])
    (integer->integer-bytes n size #t #f buf))

  (define (bytes->integer buf [size 4] [signed? #t])
    (integer-bytes->integer buf signed? #f 0 size))

  (define (real->bytes n [size 4] [buf (make-bytes size)])
    (real->floating-point-bytes n size #f buf))

  (define (bytes->real buf [size 4])
    (floating-point-bytes->real buf #f 0 size)))

(define-syntax-rule (define-i32-unop id) (define-runtime id (_fun _int32  -> _int32)))
(define-syntax-rule (define-i64-unop id) (define-runtime id (_fun _int64  -> _int64)))
(define-syntax-rule (define-i32-unops id ...) (begin (define-i32-unop id) ...))
(define-syntax-rule (define-i64-unops id ...) (begin (define-i64-unop id) ...))
(define-syntax-rule (define-f32-unop id) (define-runtime id (_fun _double*  -> _double*)))
(define-syntax-rule (define-f64-unop id) (define-runtime id (_fun _double*  -> _double*)))
(define-syntax-rule (define-f32-unops id ...) (begin (define-f32-unop id) ...))
(define-syntax-rule (define-f64-unops id ...) (begin (define-f64-unop id) ...))

(define-syntax-rule (define-i32-binop id) (define-runtime id (_fun _int32  _int32    -> _int32)))
(define-syntax-rule (define-i64-binop id) (define-runtime id (_fun _int64  _int64    -> _int64)))
(define-syntax-rule (define-f32-binop id) (define-runtime id (_fun _double* _double* -> _double*)))
(define-syntax-rule (define-f64-binop id) (define-runtime id (_fun _double* _double* -> _double*)))
(define-syntax-rule (define-i32-binops id ...) (begin (define-i32-binop id) ...))
(define-syntax-rule (define-i64-binops id ...) (begin (define-i64-binop id) ...))
(define-syntax-rule (define-f32-binops id ...) (begin (define-f32-binop id) ...))
(define-syntax-rule (define-f64-binops id ...) (begin (define-f64-binop id) ...))

(define-syntax-rule (define-f32-cmpop id) (define-runtime id (_fun _double* _double* -> _int64)))
(define-syntax-rule (define-f64-cmpop id) (define-runtime id (_fun _double* _double* -> _int64)))
(define-syntax-rule (define-f32-cmpops id ...) (begin (define-f32-cmpop id) ...))
(define-syntax-rule (define-f64-cmpops id ...) (begin (define-f64-cmpop id) ...))

(module+ i32
  (provide (all-defined-out))
  (begin-encourage-inline
    (define (i32->bytes n buf)        (integer->bytes n 4 buf))
    (define (bytes->i32 buf [size 4]) (bytes->integer buf size))
    (define (bytes->u32 buf [size 4]) (u32->s32 (bytes->integer buf size #f)))

    (define-i32-binops
      iadd32 isub32 imul32 idiv32_u idiv32_s irem32_u irem32_s
      iand32 ior32 ixor32 ishl32 ishr32_u ishr32_s
      ieq32 ine32 ilt32_u ilt32_s igt32_u igt32_s ile32_u ile32_s ige32_u ige32_s)

    (define-i32-unops
      ieqz32 iclz32 ictz32 ipopcnt32)

    (define-runtime iwrap32 (_fun _int64 -> _int32))))

(module+ i64
  (provide (all-defined-out))
  (begin-encourage-inline
    (define (i64->bytes n buf)        (integer->bytes n 8 buf))
    (define (bytes->i64 buf [size 8]) (bytes->integer buf size))
    (define (bytes->u64 buf [size 8]) (u64->s64 (bytes->integer buf size #f)))

    (define-i64-binops
      iadd64 isub64 imul64 idiv64_u idiv64_s irem64_u irem64_s
      iand64 ior64 ixor64 ishl64 ishr64_u ishr64_s
      ieq64 ine64 ilt64_u ilt64_s igt64_u igt64_s ile64_u ile64_s ige64_u ige64_s)

    (define-i64-unops
      ieqz64 iclz64 ictz64 ipopcnt64)

    (define-runtime iextend32_u (_fun _int32  -> _int64))
    (define-runtime iextend32_s (_fun _int32  -> _int64))
    (define-runtime itrunc64_u  (_fun _double -> _int64))
    (define-runtime itrunc64_s  (_fun _double -> _int64))))

(module+ f32
  (provide (all-defined-out))
  (begin-encourage-inline
    (define (f32->bytes n buf) (real->bytes n 4 buf))
    (define (bytes->f32 buf)   (bytes->real buf 4))

    (define-f32-binops
      fadd32 fsub32 fmul32 fdiv32)

    (define-f32-cmpops
      feq32 fne32 flt32 fgt32 fle32 fge32)

    (define-runtime fdemote64 (_fun _double -> _float))))

(module+ f64
  (provide (all-defined-out))
  (begin-encourage-inline
    (define (f64->bytes n buf) (real->bytes n 8 buf))
    (define (bytes->f64 buf)   (bytes->real buf 8))

    (define-f64-unops
      fabs64)

    (define-f64-binops
      fadd64 fsub64 fmul64 fdiv64)

    (define-f64-cmpops
      feq64 fne64 flt64 fgt64 fle64 fge64)

    (define-runtime fpromote32   (_fun _float -> _double))
    (define-runtime fconvert64_u (_fun _int64 -> _double))
    (define-runtime fconvert64_s (_fun _int64 -> _double))))
