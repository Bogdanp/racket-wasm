#lang racket/base

(require racket/match
         "core.rkt"
         "error.rkt"
         "location.rkt"
         "opcase.rkt")

(provide
 current-custom-section-reader
 track-source-location?
 read-wasm
 read-name!
 read-u32!
 skip-len!)

(define (oops! in message . args)
  (define-values (_line _col pos)
    (port-next-location in))
  (define offset (sub1 pos))
  (raise-wasm-read-error
   "~a~n  in: ~a~n  at position: ~a (0x~a)"
   (apply format message args)
   (object-name in)
   offset
   (number->string offset 16)))

(define MAGIC   #"\x00\x61\x73\x6d")
(define VERSION #"\x01\x00\x00\x00")

(define current-custom-section-reader
  (make-parameter
   (lambda (buf len in)
     (skip-n-bytes! "custom section" buf len in)
     (custom-section #f))))

(define current-types
  (make-parameter (vector)))

(define track-source-location?
  (make-parameter #t))

(define (read-wasm in [buf (make-bytes (* 64 1024))])
  (read-n-bytes! "magic header" buf 4 in)
  (define magic-header (subbytes buf 0 4))
  (unless (bytes=? magic-header MAGIC)
    (oops! in "invalid magic header: ~a" magic-header))
  (read-n-bytes! "version" buf 4 in)
  (define version (subbytes buf 0 4))
  (unless (bytes=? version VERSION)
    (oops! in "unsupported version: ~a" version))
  (let loop ([customs   null]
             [types     (vector)]
             [imports   (vector)]
             [functions (vector)]
             [tables    (vector)]
             [memories  (vector)]
             [globals   (vector)]
             [exports   (vector)]
             [start     #f]
             [elements  (vector)]
             [codes     (vector)]
             [datas     (vector)])
    (match (read-section! buf in types)
      [(? eof-object?)              (mod customs types imports functions tables memories globals exports start elements codes datas)]
      [(custom-section data)        (loop (cons data customs) types imports functions tables memories globals exports start elements codes datas)]
      [(type-section types)         (loop customs types imports functions tables memories globals exports start elements codes datas)]
      [(import-section imports)     (loop customs types imports functions tables memories globals exports start elements codes datas)]
      [(function-section functions) (loop customs types imports functions tables memories globals exports start elements codes datas)]
      [(table-section tables)       (loop customs types imports functions tables memories globals exports start elements codes datas)]
      [(memory-section memories)    (loop customs types imports functions tables memories globals exports start elements codes datas)]
      [(global-section globals)     (loop customs types imports functions tables memories globals exports start elements codes datas)]
      [(export-section exports)     (loop customs types imports functions tables memories globals exports start elements codes datas)]
      [(start-section start)        (loop customs types imports functions tables memories globals exports start elements codes datas)]
      [(element-section elements)   (loop customs types imports functions tables memories globals exports start elements codes datas)]
      [(code-section codes)         (loop customs types imports functions tables memories globals exports start elements codes datas)]
      [(data-section datas)         (loop customs types imports functions tables memories globals exports start elements codes datas)])))

(define (read-section! buf in types)
  (parameterize ([current-types types])
    (define idx (read-byte in))
    (case idx
      [(0) (read-custom-section! buf in)]
      [(1) (read-type-section! buf in)]
      [(2) (read-import-section! buf in)]
      [(3) (read-function-section! buf in)]
      [(4) (read-table-section! buf in)]
      [(5) (read-memory-section! buf in)]
      [(6) (read-global-section! buf in)]
      [(7) (read-export-section! buf in)]
      [(8) (read-start-section! buf in)]
      [(9) (read-element-section! buf in)]
      [(10) (read-code-section! buf in)]
      [(11) (read-data-section! buf in)]
      [else
       (cond
         [(eof-object? idx) eof]
         [else (oops! in "unexpected section idx ~a" idx)])])))

(define (read-custom-section! buf in)
  (define len (read-u32! buf in))
  ((current-custom-section-reader) buf len in))

(define (read-type-section! buf in)
  (skip-len! buf in)
  (type-section (read-vectorof! read-functype! buf in)))

(define (read-import-section! buf in)
  (skip-len! buf in)
  (import-section (read-vectorof! read-import! buf in)))

(define (read-function-section! buf in)
  (skip-len! buf in)
  (function-section (read-vectorof! read-u32! buf in)))

(define (read-table-section! buf in)
  (skip-len! buf in)
  (table-section (read-vectorof! read-tabletype! buf in)))

(define (read-memory-section! buf in)
  (skip-len! buf in)
  (memory-section (read-vectorof! read-memtype! buf in)))

(define (read-global-section! buf in)
  (skip-len! buf in)
  (global-section (read-vectorof! read-global! buf in)))

(define (read-export-section! buf in)
  (skip-len! buf in)
  (export-section (read-vectorof! read-export! buf in)))

(define (read-start-section! buf in)
  (skip-len! buf in)
  (start-section (funcidx (read-u32! buf in))))

(define (read-element-section! buf in)
  (skip-len! buf in)
  (element-section (read-vectorof! read-elem! buf in)))

(define (read-code-section! buf in)
  (skip-len! buf in)
  (code-section (read-vectorof! read-code! buf in)))

(define (read-data-section! buf in)
  (skip-len! buf in)
  (data-section (read-vectorof! read-data! buf in)))

(define (read-name! buf in)
  (define len (read-u32! buf in))
  (read-n-bytes! "name" buf len in)
  (bytes->string/utf-8 buf #f 0 len))

(define (read-code! buf in)
  (skip-len! buf in)
  (define localss (read-vectorof! read-locals! buf in))
  (define-values (expr _)
    (read-expr! buf in))
  (code localss expr))

(define (read-locals! buf in)
  (locals (read-u32! buf in)
          (read-valtype! buf in)))

(define (expr-ender? b)
  (= b #x0B))

(define (if-expr-ender? b)
  (or (= b #x05)
      (= b #x0B)))

(define (read-expr! buf in [ender? expr-ender?])
  (define track-srcloc? (track-source-location?))
  (define source-name (and track-srcloc? (object-name in)))
  (let loop ([instrs null])
    (define b (read-byte! "instr" buf in))
    (define l
      (if track-srcloc?
          (loc source-name (file-position* in))
          (loc-unknown source-name)))
    (define instr
      (opcase b
        ;; Control instructions
        [op:unreachable (instr:unreachable l)]
        [op:nop         (instr:nop         l)]

        [op:block (let-values ([(type) (read-blocktype! buf in)]
                               [(code _) (read-expr! buf in)])
                    (instr:block l type code))]

        [op:loop (let-values ([(type) (read-blocktype! buf in)]
                              [(code _) (read-expr! buf in)])
                   (instr:loop l type code))]

        [op:if (let-values ([(type) (read-blocktype! buf in)]
                            [(then-code end) (read-expr! buf in if-expr-ender?)])
                 (instr:if l type then-code (and (= end #x05)
                                                 (let-values ([(else-code _) (read-expr! buf in)])
                                                   else-code))))]

        [op:br       (instr:br       l (read-u32! buf in))]
        [op:br_if    (instr:br_if    l (read-u32! buf in))]
        [op:br_table (instr:br_table l (read-vectorof! read-u32! buf in) (read-u32! buf in))]

        [op:return (instr:return l)]

        [op:call          (instr:call          l (read-u32! buf in))]
        [op:call_indirect (instr:call_indirect l (read-u32! buf in) (read-u32! buf in))]

        ;; Parametric instructions
        [op:drop   (instr:drop   l)]
        [op:select (instr:select l)]

        ;; Variable instructions
        [op:local.get  (instr:local.get  l (read-u32! buf in))]
        [op:local.set  (instr:local.set  l (read-u32! buf in))]
        [op:local.tee  (instr:local.tee  l (read-u32! buf in))]
        [op:global.get (instr:global.get l (read-u32! buf in))]
        [op:global.set (instr:global.set l (read-u32! buf in))]

        ;; Memory instructions
        [op:i32.load     (instr:i32.load     l (read-memarg! buf in))]
        [op:i64.load     (instr:i64.load     l (read-memarg! buf in))]
        [op:f32.load     (instr:f32.load     l (read-memarg! buf in))]
        [op:f64.load     (instr:f64.load     l (read-memarg! buf in))]
        [op:i32.load8_s  (instr:i32.load8_s  l (read-memarg! buf in))]
        [op:i32.load8_u  (instr:i32.load8_u  l (read-memarg! buf in))]
        [op:i32.load16_s (instr:i32.load16_s l (read-memarg! buf in))]
        [op:i32.load16_u (instr:i32.load16_u l (read-memarg! buf in))]
        [op:i64.load8_s  (instr:i64.load8_s  l (read-memarg! buf in))]
        [op:i64.load8_u  (instr:i64.load8_u  l (read-memarg! buf in))]
        [op:i64.load16_s (instr:i64.load16_s l (read-memarg! buf in))]
        [op:i64.load16_u (instr:i64.load16_u l (read-memarg! buf in))]
        [op:i64.load32_s (instr:i64.load32_s l (read-memarg! buf in))]
        [op:i64.load32_u (instr:i64.load32_u l (read-memarg! buf in))]
        [op:i32.store    (instr:i32.store    l (read-memarg! buf in))]
        [op:i64.store    (instr:i64.store    l (read-memarg! buf in))]
        [op:f32.store    (instr:f32.store    l (read-memarg! buf in))]
        [op:f64.store    (instr:f64.store    l (read-memarg! buf in))]
        [op:i32.store8   (instr:i32.store8   l (read-memarg! buf in))]
        [op:i32.store16  (instr:i32.store16  l (read-memarg! buf in))]
        [op:i64.store8   (instr:i64.store8   l (read-memarg! buf in))]
        [op:i64.store16  (instr:i64.store16  l (read-memarg! buf in))]
        [op:i64.store32  (instr:i64.store32  l (read-memarg! buf in))]

        [op:memory.size (instr:memory.size l (read-u32! buf in))]
        [op:memory.grow (instr:memory.grow l (read-u32! buf in))]

        ;; Numeric instructions
        [op:i32.const (instr:i32.const l (read-i32! buf in))]
        [op:i64.const (instr:i64.const l (read-i64! buf in))]
        [op:f32.const (instr:f32.const l (read-f32! buf in))]
        [op:f64.const (instr:f64.const l (read-f64! buf in))]

        [op:i32.eqz  (instr:i32.eqz  l)]
        [op:i32.eq   (instr:i32.eq   l)]
        [op:i32.ne   (instr:i32.ne   l)]
        [op:i32.lt_s (instr:i32.lt_s l)]
        [op:i32.lt_u (instr:i32.lt_u l)]
        [op:i32.gt_s (instr:i32.gt_s l)]
        [op:i32.gt_u (instr:i32.gt_u l)]
        [op:i32.le_s (instr:i32.le_s l)]
        [op:i32.le_u (instr:i32.le_u l)]
        [op:i32.ge_s (instr:i32.ge_s l)]
        [op:i32.ge_u (instr:i32.ge_u l)]

        [op:i64.eqz  (instr:i64.eqz  l)]
        [op:i64.eq   (instr:i64.eq   l)]
        [op:i64.ne   (instr:i64.ne   l)]
        [op:i64.lt_s (instr:i64.lt_s l)]
        [op:i64.lt_u (instr:i64.lt_u l)]
        [op:i64.gt_s (instr:i64.gt_s l)]
        [op:i64.gt_u (instr:i64.gt_u l)]
        [op:i64.le_s (instr:i64.le_s l)]
        [op:i64.le_u (instr:i64.le_u l)]
        [op:i64.ge_s (instr:i64.ge_s l)]
        [op:i64.ge_u (instr:i64.ge_u l)]

        [op:f32.eq (instr:f32.eq l)]
        [op:f32.ne (instr:f32.ne l)]
        [op:f32.lt (instr:f32.lt l)]
        [op:f32.gt (instr:f32.gt l)]
        [op:f32.le (instr:f32.le l)]
        [op:f32.ge (instr:f32.ge l)]

        [op:f64.eq (instr:f64.eq l)]
        [op:f64.ne (instr:f64.ne l)]
        [op:f64.lt (instr:f64.lt l)]
        [op:f64.gt (instr:f64.gt l)]
        [op:f64.le (instr:f64.le l)]
        [op:f64.ge (instr:f64.ge l)]

        [op:i32.clz    (instr:i32.clz    l)]
        [op:i32.ctz    (instr:i32.ctz    l)]
        [op:i32.popcnt (instr:i32.popcnt l)]
        [op:i32.add    (instr:i32.add    l)]
        [op:i32.sub    (instr:i32.sub    l)]
        [op:i32.mul    (instr:i32.mul    l)]
        [op:i32.div_s  (instr:i32.div_s  l)]
        [op:i32.div_u  (instr:i32.div_u  l)]
        [op:i32.rem_s  (instr:i32.rem_s  l)]
        [op:i32.rem_u  (instr:i32.rem_u  l)]
        [op:i32.and    (instr:i32.and    l)]
        [op:i32.or     (instr:i32.or     l)]
        [op:i32.xor    (instr:i32.xor    l)]
        [op:i32.shl    (instr:i32.shl    l)]
        [op:i32.shr_s  (instr:i32.shr_s  l)]
        [op:i32.shr_u  (instr:i32.shr_u  l)]
        [op:i32.rotl   (instr:i32.rotl   l)]
        [op:i32.rotl   (instr:i32.rotl   l)]

        [op:i64.clz    (instr:i64.clz    l)]
        [op:i64.ctz    (instr:i64.ctz    l)]
        [op:i64.popcnt (instr:i64.popcnt l)]
        [op:i64.add    (instr:i64.add    l)]
        [op:i64.sub    (instr:i64.sub    l)]
        [op:i64.mul    (instr:i64.mul    l)]
        [op:i64.div_s  (instr:i64.div_s  l)]
        [op:i64.div_u  (instr:i64.div_u  l)]
        [op:i64.rem_s  (instr:i64.rem_s  l)]
        [op:i64.rem_u  (instr:i64.rem_u  l)]
        [op:i64.and    (instr:i64.and    l)]
        [op:i64.or     (instr:i64.or     l)]
        [op:i64.xor    (instr:i64.xor    l)]
        [op:i64.shl    (instr:i64.shl    l)]
        [op:i64.shr_s  (instr:i64.shr_s  l)]
        [op:i64.shr_u  (instr:i64.shr_u  l)]
        [op:i64.rotl   (instr:i64.rotl   l)]
        [op:i64.rotl   (instr:i64.rotl   l)]

        [op:f32.abs      (instr:f32.abs      l)]
        [op:f32.neg      (instr:f32.neg      l)]
        [op:f32.ceil     (instr:f32.ceil     l)]
        [op:f32.floor    (instr:f32.floor    l)]
        [op:f32.trunc    (instr:f32.trunc    l)]
        [op:f32.nearest  (instr:f32.nearest  l)]
        [op:f32.sqrt     (instr:f32.sqrt     l)]
        [op:f32.add      (instr:f32.add      l)]
        [op:f32.sub      (instr:f32.sub      l)]
        [op:f32.mul      (instr:f32.mul      l)]
        [op:f32.div      (instr:f32.div      l)]
        [op:f32.min      (instr:f32.min      l)]
        [op:f32.max      (instr:f32.max      l)]
        [op:f32.copysign (instr:f32.copysign l)]

        [op:f64.abs      (instr:f64.abs      l)]
        [op:f64.neg      (instr:f64.neg      l)]
        [op:f64.ceil     (instr:f64.ceil     l)]
        [op:f64.floor    (instr:f64.floor    l)]
        [op:f64.trunc    (instr:f64.trunc    l)]
        [op:f64.nearest  (instr:f64.nearest  l)]
        [op:f64.sqrt     (instr:f64.sqrt     l)]
        [op:f64.add      (instr:f64.add      l)]
        [op:f64.sub      (instr:f64.sub      l)]
        [op:f64.mul      (instr:f64.mul      l)]
        [op:f64.div      (instr:f64.div      l)]
        [op:f64.min      (instr:f64.min      l)]
        [op:f64.max      (instr:f64.max      l)]
        [op:f64.copysign (instr:f64.copysign l)]

        [op:i32.wrap_i64        (instr:i32.wrap_i64        l)]
        [op:i32.trunc_f32_s     (instr:i32.trunc_f32_s     l)]
        [op:i32.trunc_f32_u     (instr:i32.trunc_f32_u     l)]
        [op:i32.trunc_f64_s     (instr:i32.trunc_f64_s     l)]
        [op:i32.trunc_f64_u     (instr:i32.trunc_f64_u     l)]
        [op:i64.extend_i32_s    (instr:i64.extend_i32_s    l)]
        [op:i64.extend_i32_u    (instr:i64.extend_i32_u    l)]
        [op:i64.trunc_f32_s     (instr:i64.trunc_f32_s     l)]
        [op:i64.trunc_f32_u     (instr:i64.trunc_f32_u     l)]
        [op:i64.trunc_f64_s     (instr:i64.trunc_f64_s     l)]
        [op:i64.trunc_f64_u     (instr:i64.trunc_f64_u     l)]
        [op:f32.convert_i32_s   (instr:f32.convert_i32_s   l)]
        [op:f32.convert_i32_u   (instr:f32.convert_i32_u   l)]
        [op:f32.convert_i64_s   (instr:f32.convert_i64_s   l)]
        [op:f32.convert_i64_u   (instr:f32.convert_i64_u   l)]
        [op:f32.demote_f64      (instr:f32.demote_f64      l)]
        [op:f64.convert_i32_s   (instr:f64.convert_i32_s   l)]
        [op:f64.convert_i32_u   (instr:f64.convert_i32_u   l)]
        [op:f64.convert_i64_s   (instr:f64.convert_i64_s   l)]
        [op:f64.convert_i64_u   (instr:f64.convert_i64_u   l)]
        [op:f64.promote_f32     (instr:f64.promote_f32     l)]
        [op:i32.reinterpret_f32 (instr:i32.reinterpret_f32 l)]
        [op:i64.reinterpret_f64 (instr:i64.reinterpret_f64 l)]
        [op:f32.reinterpret_i32 (instr:f32.reinterpret_i32 l)]
        [op:f64.reinterpret_i64 (instr:f64.reinterpret_i64 l)]

        [op:i32.extend8_s  (instr:i32.extend8_s  l)]
        [op:i32.extend16_s (instr:i32.extend16_s l)]
        [op:i64.extend8_s  (instr:i64.extend8_s  l)]
        [op:i64.extend16_s (instr:i64.extend16_s l)]
        [op:i64.extend32_s (instr:i64.extend32_s l)]

        [op:trunc_sat (let ([opcode (read-u32! buf in)])
                        (case opcode
                          [(0) (instr:i32.trunc_sat_f32_s l)]
                          [(1) (instr:i32.trunc_sat_f32_u l)]
                          [(2) (instr:i32.trunc_sat_f64_s l)]
                          [(3) (instr:i32.trunc_sat_f64_u l)]
                          [(4) (instr:i64.trunc_sat_f32_s l)]
                          [(5) (instr:i64.trunc_sat_f32_u l)]
                          [(6) (instr:i64.trunc_sat_f64_s l)]
                          [(7) (instr:i64.trunc_sat_f64_u l)]
                          [else (oops! in "unexpected saturating truncation opcode: ~s" opcode)]))]

        [else
         (cond
           [(ender? b) 'end]
           [else (oops! in "unexpected opcode: ~s" b)])]))

    (cond
      [(eq? instr 'end)
       (define len (length instrs))
       (define res (make-vector len))
       (for ([instr (in-list instrs)]
             [idx (in-range (sub1 len) -1 -1)])
         (vector-set! res idx instr))
       (values res b)]
      [else
       (loop (cons instr instrs))])))

(define (read-blocktype! buf in)
  (case (peek-byte in)
    [(#x40)
     (begin0 (functype null null)
       (read-byte in))]

    [(#x7F #x7E #x7D #x7C)
     (functype null (list (read-valtype! buf in)))]

    [else
     (define idx (read-sint! "33bit signed integer" buf in))
     (vector-ref (current-types) idx)]))

(define (read-memarg! buf in)
  (memarg (read-u32! buf in)
          (read-u32! buf in)))

(define (read-data! buf in)
  (define idx (read-u32! buf in))
  (define-values (code _)
    (read-expr! buf in))
  (data idx code (read-bytevector! buf in)))

(define (read-import! buf in)
  (import (read-name! buf in)
          (read-name! buf in)
          (read-importdesc! buf in)))

(define (read-export! buf in)
  (export (read-name! buf in)
          (read-exportdesc! buf in)))

(define (read-global! buf in)
  (define type (read-globaltype! buf in))
  (define-values (code _)
    (read-expr! buf in))
  (global type code))

(define (read-importdesc! buf in)
  (define b (read-byte! "importdesc" buf in))
  (case b
    [(#x00) (typeidx (read-u32! buf in))]
    [(#x01) (read-tabletype! buf in)]
    [(#x02) (read-memtype! buf in)]
    [(#x03) (read-globaltype! buf in)]
    [else (oops! in "unexpected value while reading importdesc: ~s" b)]))

(define (read-exportdesc! buf in)
  (define b (read-byte! "exportdesc" buf in))
  (case b
    [(#x00) (read-funcidx! buf in)]
    [(#x01) (read-tableidx! buf in)]
    [(#x02) (read-memidx! buf in)]
    [(#x03) (read-globalidx! buf in)]
    [else (oops! in "unexpected value while reading exportdesc: ~s" b)]))

(define (read-elem! buf in)
  (define idx (read-u32! buf in))
  (define-values (code _)
    (read-expr! buf in))
  (element idx code (read-vectorof! read-funcidx! buf in)))

(define (read-tableidx! buf in)
  (tableidx (read-u32! buf in)))

(define (read-funcidx! buf in)
  (funcidx (read-u32! buf in)))

(define (read-memidx! buf in)
  (memidx (read-u32! buf in)))

(define (read-globalidx! buf in)
  (globalidx (read-u32! buf in)))

(define (read-tabletype! buf in)
  (tabletype (read-elemtype! buf in)
             (read-limits! buf in)))

(define (read-memtype! buf in)
  (memtype (read-limits! buf in)))

(define (read-globaltype! buf in)
  (globaltype (read-valtype! buf in)
              (read-mut! buf in)))

(define (read-elemtype! buf in)
  (define b (read-byte! "elemtype" buf in))
  (case b
    [(#x70) funcref]
    [else (oops! in "unexpected value while reading elemtype: ~s" b)]))

(define (read-limits! buf in)
  (define b (read-byte! "limits" buf in))
  (case b
    [(#x00) (limits (read-u32! buf in) #f)]
    [(#x01) (limits (read-u32! buf in) (read-u32! buf in))]
    [else (oops! in "unexpected value while reading limits: ~s" b)]))

(define (read-valtype! buf in)
  (define b (read-byte! "valtype" buf in))
  (case b
    [(#x7F) i32]
    [(#x7E) i64]
    [(#x7D) f32]
    [(#x7C) f64]
    [else (oops! in "unexpected value while reading valtype: ~s" b)]))

(define (read-mut! buf in)
  (define b (read-byte! "mut" buf in))
  (case b
    [(#x00) #f]
    [(#x01) #t]
    [else (oops! in "unexpected value while reading mut: ~s" b)]))

(define (read-functype! buf in)
  (define b (read-byte! "functype" buf in))
  (unless (eqv? b #x60)
    (oops! in "unexpected value while reading functype: ~s" b))
  (define params (read-restype! buf in))
  (define results (read-restype! buf in))
  (functype params results))

(define (read-restype! buf in)
  (let loop ([types null]
             [remaining (read-u32! buf in)])
    (cond
      [(zero? remaining) types]
      [else (loop (cons (read-valtype! buf in) types) (sub1 remaining))])))


;; core readers ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (skip-len! buf in)
  (let loop ()
    (define b (read-byte! "length" buf in))
    (unless (zero? (bitwise-and b #x80))
      (loop))))

(define (read-bytevector! buf in)
  (read-bytes (read-u32! buf in) in))

(define (read-vectorof! f buf in)
  (for/vector ([_ (in-range (read-u32! buf in))])
    (f buf in)))

(define (skip-n-bytes! what buf n in)
  (let loop ([remaining n])
    (unless (zero? remaining)
      (define n-read (read-bytes! buf in 0 (min remaining (bytes-length buf))))
      (if (eof-object? n-read)
          (oops! in "unexpected EOF while reading ~a" what)
          (loop (- remaining n-read))))))

(define (read-n-bytes! what buf n in)
  (let loop ([offset 0]
             [remaining n])
    (define n-read (read-bytes! buf in offset (+ offset remaining)))
    (when (eof-object? n-read)
      (oops! in "unexpected EOF while reading ~a" what))
    (define new-remaining (- remaining n-read))
    (unless (zero? new-remaining)
      (loop (+ offset n-read) new-remaining))))

(define (read-byte! what buf in)
  (read-n-bytes! what buf 1 in)
  (bytes-ref buf 0))

(define (read-uint! buf in)
  (let loop ([n 0]
             [s 0])
    (define b (read-byte! "unsigned integer" buf in))
    (define new-n (bitwise-ior n (arithmetic-shift (bitwise-and b #x7F) s)))
    (cond
      [(zero? (bitwise-and b #x80)) new-n]
      [else (loop new-n (+ s 7))])))

(define (read-sint! what buf in)
  (let loop ([n 0]
             [s 0])
    (define b (read-byte! what buf in))
    (define new-n (bitwise-ior n (arithmetic-shift (bitwise-and b #x7F) s)))
    (define new-shift (+ s 7))
    (cond
      [(> (bitwise-and b #x80) 0) (loop new-n new-shift)]
      [(zero? (bitwise-and b #x40)) new-n]
      [else (bitwise-ior new-n (arithmetic-shift -1 new-shift))])))

(define u32max (sub1 (expt 2 32)))

(define (read-u32! buf in)
  (define n (read-uint! buf in))
  (begin0 n
    (when (> n u32max)
      (oops! in "unsigned 32bit integer out of bounds"))))

(define (read-i32! buf in)
  (read-sint! "32bit signed integer" buf in))

(define (read-i64! buf in)
  (read-sint! "64bit signed integer" buf in))

(define (read-f32! buf in)
  (read-n-bytes! "f32" buf 4 in)
  (floating-point-bytes->real buf #f 0 4))

(define (read-f64! buf in)
  (read-n-bytes! "f64" buf 8 in)
  (floating-point-bytes->real buf #f 0 8))

;; Local Variables:
;; eval: (put 'opcase 'racket-indent-function #'defun)
;; End:
