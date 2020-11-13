#lang racket/base

(require (for-syntax racket/base
                     syntax/parse/lib/function-header)
         (submod racket/performance-hint begin-encourage-inline)
         ffi/unsafe
         ffi/unsafe/define
         racket/runtime-path
         syntax/parse/define)

(define-runtime-path libdir "lib")
(define-ffi-definer define-runtime
  (ffi-lib (build-path libdir "runtime")))

(define-syntax-parser define/provide
  [(_ hd:function-header body ...+)
   #'(begin
       (provide hd.name)
       (define hd body ...))])

(define-syntax-parser define-runtime/provide
  [(_ name:id e)
   #'(begin
       (provide name)
       (define-runtime name e))])

(define-syntax-rule (define-i32-unop id) (define-runtime/provide id (_fun _int32  -> _int32)))
(define-syntax-rule (define-i64-unop id) (define-runtime/provide id (_fun _int64  -> _int64)))
(define-syntax-rule (define-i32-unops id ...) (begin (define-i32-unop id) ...))
(define-syntax-rule (define-i64-unops id ...) (begin (define-i64-unop id) ...))
(define-syntax-rule (define-f32-unop id) (define-runtime/provide id (_fun _double*  -> _double*)))
(define-syntax-rule (define-f64-unop id) (define-runtime/provide id (_fun _double*  -> _double*)))
(define-syntax-rule (define-f32-unops id ...) (begin (define-f32-unop id) ...))
(define-syntax-rule (define-f64-unops id ...) (begin (define-f64-unop id) ...))

(define-syntax-rule (define-i32-binop id) (define-runtime/provide id (_fun _int32  _int32    -> _int32)))
(define-syntax-rule (define-i64-binop id) (define-runtime/provide id (_fun _int64  _int64    -> _int64)))
(define-syntax-rule (define-f32-binop id) (define-runtime/provide id (_fun _double* _double* -> _double*)))
(define-syntax-rule (define-f64-binop id) (define-runtime/provide id (_fun _double* _double* -> _double*)))
(define-syntax-rule (define-i32-binops id ...) (begin (define-i32-binop id) ...))
(define-syntax-rule (define-i64-binops id ...) (begin (define-i64-binop id) ...))
(define-syntax-rule (define-f32-binops id ...) (begin (define-f32-binop id) ...))
(define-syntax-rule (define-f64-binops id ...) (begin (define-f64-binop id) ...))

(define-syntax-rule (define-f32-cmpop id) (define-runtime/provide id (_fun _double* _double* -> _int64)))
(define-syntax-rule (define-f64-cmpop id) (define-runtime/provide id (_fun _double* _double* -> _int64)))
(define-syntax-rule (define-f32-cmpops id ...) (begin (define-f32-cmpop id) ...))
(define-syntax-rule (define-f64-cmpops id ...) (begin (define-f64-cmpop id) ...))

(define-syntax-rule (define-cvtops-definer name)
  (define-syntax-parser name
    #:datum-literals (: ->)
    [(_ [id : from -> to] ...+)
     #'(begin (define-runtime/provide id (_fun from -> to)) (... ...))]))

(define-cvtops-definer define-i32-cvtops)
(define-cvtops-definer define-i64-cvtops)
(define-cvtops-definer define-f32-cvtops)
(define-cvtops-definer define-f64-cvtops)

(begin-encourage-inline
  (define (u->s n [size 4] [buf (make-bytes size)])
    (integer->integer-bytes n size #f #f buf)
    (integer-bytes->integer buf #t #f 0 size))

  (define (u32->s32 n [buf #f]) (u->s n 4 (or buf (make-bytes 4))))
  (define (u64->s64 n [buf #f]) (u->s n 8 (or buf (make-bytes 8))))

  (define (integer->bytes n [size 4] [buf (make-bytes size)])
    (integer->integer-bytes n size #t #f buf))

  (define (bytes->integer buf [size 4] [signed? #t])
    (integer-bytes->integer buf signed? #f 0 size))

  (define (real->bytes n [size 4] [buf (make-bytes size)])
    (real->floating-point-bytes n size #f buf))

  (define (bytes->real buf [size 4])
    (floating-point-bytes->real buf #f 0 size))


  ;; i32 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define/provide (i32->bytes n buf)        (integer->bytes n 4 buf))
  (define/provide (bytes->i32 buf [size 4]) (bytes->integer buf size))
  (define/provide (bytes->u32 buf [size 4]) (u32->s32 (bytes->integer buf size #f)))

  (define-i32-binops
    iadd32 isub32 imul32 idiv32_u idiv32_s irem32_u irem32_s
    iand32 ior32 ixor32 ishl32 ishr32_u ishr32_s irotl32 irotr32
    ieq32 ine32 ilt32_u ilt32_s igt32_u igt32_s ile32_u ile32_s ige32_u ige32_s)

  (define-i32-unops
    ieqz32 iclz32 ictz32 ipopcnt32)

  (define-i32-cvtops
    [iwrap32       :   _int64 -> _int32]
    [itrunc32_32_u : _double* -> _int32]
    [itrunc32_32_s : _double* -> _int32]
    [itrunc32_64_u : _double* -> _int32]
    [itrunc32_64_s : _double* -> _int32])


  ;; i64 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define/provide (i64->bytes n buf)        (integer->bytes n 8 buf))
  (define/provide (bytes->i64 buf [size 8]) (bytes->integer buf size))
  (define/provide (bytes->u64 buf [size 8]) (u64->s64 (bytes->integer buf size #f)))

  (define-i64-binops
    iadd64 isub64 imul64 idiv64_u idiv64_s irem64_u irem64_s
    iand64 ior64 ixor64 ishl64 ishr64_u ishr64_s irotl64 irotr64
    ieq64 ine64 ilt64_u ilt64_s igt64_u igt64_s ile64_u ile64_s ige64_u ige64_s)

  (define-i64-unops
    ieqz64 iclz64 ictz64 ipopcnt64)

  (define-i64-cvtops
    [iextend32_u   :  _int32  -> _int64]
    [iextend32_s   :  _int32  -> _int64]
    [itrunc64_32_u : _double* -> _int64]
    [itrunc64_32_s : _double* -> _int64]
    [itrunc64_64_u : _double* -> _int64]
    [itrunc64_64_s : _double* -> _int64])


  ;; f32 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define/provide (f32->bytes n buf) (real->bytes n 4 buf))
  (define/provide (bytes->f32 buf)   (bytes->real buf 4))

  (define-f32-unops
    fabs32 fneg32 fceil32 ffloor32 ftrunc32 fnearest32 fsqrt32)

  (define-f32-binops
    fadd32 fsub32 fmul32 fdiv32 fmin32 fmax32 fcopysign32)

  (define-f32-cmpops
    feq32 fne32 flt32 fgt32 fle32 fge32)

  (define-f32-cvtops
    [fdemote64 : _double* -> _double*])


  ;; f64 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define/provide (f64->bytes n buf) (real->bytes n 8 buf))
  (define/provide (bytes->f64 buf)   (bytes->real buf 8))

  (define-f64-unops
    fabs64 fneg64 fceil64 ffloor64 ftrunc64 fnearest64 fsqrt64)

  (define-f64-binops
    fadd64 fsub64 fmul64 fdiv64 fmin64 fmax64 fcopysign64)

  (define-f64-cmpops
    feq64 fne64 flt64 fgt64 fle64 fge64)

  (define-f64-cvtops
    [fpromote32   : _double* -> _double*]
    [fconvert64_u :   _int64 -> _double*]
    [fconvert64_s :   _int64 -> _double*]))
