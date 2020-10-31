#lang racket/base

(require racket/match
         "core.rkt"
         "error.rkt")

(provide
 current-custom-section-reader
 read-wasm)

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
   (lambda (len in buf)
     (skip-n-bytes! "custom section" len in buf)
     (custom-section #f))))

(define (read-wasm in [buf (make-bytes (* 64 1024))])
  (read-n-bytes! "magic header" buf 4 in)
  (define magic-header (subbytes buf 0 4))
  (unless (bytes=? magic-header MAGIC)
    (oops! in "invalid magic header: ~a" magic-header))
  (read-n-bytes! "version" buf 4 in)
  (define version (subbytes buf 0 4))
  (unless (bytes=? version VERSION)
    (oops! in "unsupported version: ~a" version))
  (let loop ([sections (make-mod-hash)])
    (match (read-section! in buf)
      [(? eof-object?) (mod-hash->mod sections)]
      [section (loop (with-handlers ([exn:fail? (lambda (e)
                                                  (oops! in "~a" (exn-message e)))])
                       (mod-hash-add-section sections section)))])))

(define (read-section! in buf)
  (match (read-byte in)
    [(? eof-object?) eof]
    [0 (read-custom-section! in buf)]
    [1 (read-type-section! in buf)]
    [2 (read-import-section! in buf)]
    [3 (read-function-section! in buf)]
    [4 (read-table-section! in buf)]
    [5 (read-memory-section! in buf)]
    [6 (read-global-section! in buf)]
    [7 (read-export-section! in buf)]
    [8 (read-start-section! in buf)]
    [9 (read-element-section! in buf)]
    [10 (read-code-section! in buf)]
    [11 (read-data-section! in buf)]
    [idx (oops! in "unexpected section idx ~a" idx)]))

(define (read-custom-section! in buf)
  (define len (read-u32! in buf))
  ((current-custom-section-reader) len in buf))

(define (read-type-section! in buf)
  (skip-len! in buf)
  (type-section (read-vectorof! read-functype! in buf)))

(define (read-import-section! in buf)
  (skip-len! in buf)
  (import-section (read-vectorof! read-import! in buf)))

(define (read-function-section! in buf)
  (skip-len! in buf)
  (function-section (read-vectorof! read-u32! in buf)))

(define (read-table-section! in buf)
  (skip-len! in buf)
  (table-section (read-vectorof! read-tabletype! in buf)))

(define (read-memory-section! in buf)
  (skip-len! in buf)
  (memory-section (read-vectorof! read-memtype! in buf)))

(define (read-global-section! in buf)
  (skip-len! in buf)
  (global-section (read-vectorof! read-global! in buf)))

(define (read-export-section! in buf)
  (skip-len! in buf)
  (export-section (read-vectorof! read-export! in buf)))

(define (read-start-section! in buf)
  (skip-len! in buf)
  (start-section (funcidx (read-u32! in buf))))

(define (read-element-section! in buf)
  (skip-len! in buf)
  (element-section (read-vectorof! read-elem! in buf)))

(define (read-code-section! in buf)
  (skip-len! in buf)
  (code-section (read-vectorof! read-code! in buf)))

(define (read-data-section! in buf)
  (skip-len! in buf)
  (data-section (read-vectorof! read-data! in buf)))

(define (read-name! in buf)
  (define len (read-u32! in buf))
  (read-n-bytes! "name" buf len in)
  (bytes->string/utf-8 buf #f 0 len))

(define (read-code! in buf)
  (skip-len! in buf)
  (define localss (read-vectorof! read-locals! in buf))
  (define-values (expr _)
    (read-expr! in buf))
  (code localss expr))

(define (read-locals! in buf)
  (locals (read-u32! in buf)
          (read-valtype! in buf)))

(define (read-expr! in buf [ender? (lambda (b)
                                     (= b #x0B))])
  (let loop ([instrs null])
    (define b (read-byte! "exprt" buf in))
    (define instr
      (match b
        ;; Control instructions
        [#x00 (instr:unreachable)]
        [#x01 (instr:nop)]
        [#x02 (let-values ([(type) (read-blocktype! in buf)]
                           [(code _) (read-expr! in buf)])
                (instr:block type code))]
        [#x03 (let-values ([(type) (read-blocktype! in buf)]
                           [(code _) (read-expr! in buf)])
                (instr:loop type code))]
        [#x04 (let-values ([(type) (read-blocktype! in buf)]
                           [(then-code end) (read-expr! in buf (lambda (opcode)
                                                                 (or (= opcode #x05)
                                                                     (= opcode #x0B))))])
                (instr:if type then-code (and (= end #x05)
                                              (let-values ([(else-code _) (read-expr! in buf)])
                                                else-code))))]
        [#x0C (instr:br (read-u32! in buf))]
        [#x0D (instr:br_if (read-u32! in buf))]
        [#x0E (instr:br_table
               (read-vectorof! read-u32! in buf)
               (read-u32! in buf))]
        [#x0F (instr:return)]
        [#x10 (instr:call (read-u32! in buf))]
        [#x11 (instr:call_indirect
               (read-u32! in buf)
               (read-u32! in buf))]

        ;; Parametric instructions
        [#x1A (instr:drop)]
        [#x1B (instr:select)]

        ;; Variable instructions
        [#x20 (instr:local.get (read-u32! in buf))]
        [#x21 (instr:local.set (read-u32! in buf))]
        [#x22 (instr:local.tee (read-u32! in buf))]
        [#x23 (instr:global.get (read-u32! in buf))]
        [#x24 (instr:global.set (read-u32! in buf))]

        ;; Memory instructions
        [#x28 (instr:i32.load (read-memarg! in buf))]
        [#x29 (instr:i64.load (read-memarg! in buf))]
        [#x2A (instr:f32.load (read-memarg! in buf))]
        [#x2B (instr:f64.load (read-memarg! in buf))]
        [#x2C (instr:i32.load8_s (read-memarg! in buf))]
        [#x2D (instr:i32.load8_u (read-memarg! in buf))]
        [#x2E (instr:i32.load16_s (read-memarg! in buf))]
        [#x2F (instr:i32.load16_u (read-memarg! in buf))]
        [#x30 (instr:i64.load8_s (read-memarg! in buf))]
        [#x31 (instr:i64.load8_u (read-memarg! in buf))]
        [#x32 (instr:i64.load16_s (read-memarg! in buf))]
        [#x33 (instr:i64.load16_u (read-memarg! in buf))]
        [#x34 (instr:i64.load32_s (read-memarg! in buf))]
        [#x35 (instr:i64.load32_u (read-memarg! in buf))]
        [#x36 (instr:i32.store (read-memarg! in buf))]
        [#x37 (instr:i64.store (read-memarg! in buf))]
        [#x38 (instr:f32.store (read-memarg! in buf))]
        [#x39 (instr:f64.store (read-memarg! in buf))]
        [#x3A (instr:i32.store8 (read-memarg! in buf))]
        [#x3B (instr:i32.store16 (read-memarg! in buf))]
        [#x3C (instr:i64.store8 (read-memarg! in buf))]
        [#x3D (instr:i64.store16 (read-memarg! in buf))]
        [#x3E (instr:i64.store32 (read-memarg! in buf))]
        [#x3F (instr:memory.size (read-u32! in buf))]
        [#x40 (instr:memory.grow (read-u32! in buf))]

        ;; Numeric instructions
        [#x41 (instr:i32.const (read-i32! in buf))]
        [#x42 (instr:i64.const (read-i64! in buf))]
        [#x43 (instr:f32.const (read-f32! in buf))]
        [#x44 (instr:f64.const (read-f64! in buf))]

        [#x45 (instr:i32.eqz)]
        [#x46 (instr:i32.eq)]
        [#x47 (instr:i32.ne)]
        [#x48 (instr:i32.lt_s)]
        [#x49 (instr:i32.lt_u)]
        [#x4A (instr:i32.gt_s)]
        [#x4B (instr:i32.gt_u)]
        [#x4C (instr:i32.le_s)]
        [#x4D (instr:i32.le_u)]
        [#x4E (instr:i32.ge_s)]
        [#x4F (instr:i32.ge_u)]

        [#x50 (instr:i64.eqz)]
        [#x51 (instr:i64.eq)]
        [#x52 (instr:i64.ne)]
        [#x53 (instr:i64.lt_s)]
        [#x54 (instr:i64.lt_u)]
        [#x55 (instr:i64.gt_s)]
        [#x56 (instr:i64.gt_u)]
        [#x57 (instr:i64.le_s)]
        [#x58 (instr:i64.le_u)]
        [#x59 (instr:i64.ge_s)]
        [#x5A (instr:i64.ge_u)]

        [#x5B (instr:f32.eq)]
        [#x5C (instr:f32.ne)]
        [#x5D (instr:f32.lt)]
        [#x5E (instr:f32.gt)]
        [#x5F (instr:f32.le)]
        [#x60 (instr:f32.ge)]

        [#x61 (instr:f64.eq)]
        [#x62 (instr:f64.ne)]
        [#x63 (instr:f64.lt)]
        [#x64 (instr:f64.gt)]
        [#x65 (instr:f64.le)]
        [#x66 (instr:f64.ge)]

        [#x67 (instr:i32.clz)]
        [#x68 (instr:i32.ctz)]
        [#x69 (instr:i32.popcnt)]
        [#x6A (instr:i32.add)]
        [#x6B (instr:i32.sub)]
        [#x6C (instr:i32.mul)]
        [#x6D (instr:i32.div_s)]
        [#x6E (instr:i32.div_u)]
        [#x6F (instr:i32.rem_s)]
        [#x70 (instr:i32.rem_u)]
        [#x71 (instr:i32.and)]
        [#x72 (instr:i32.or)]
        [#x73 (instr:i32.xor)]
        [#x74 (instr:i32.shl)]
        [#x75 (instr:i32.shr_s)]
        [#x76 (instr:i32.shr_u)]
        [#x77 (instr:i32.rotl)]
        [#x78 (instr:i32.rotl)]

        [#x79 (instr:i64.clz)]
        [#x7A (instr:i64.ctz)]
        [#x7B (instr:i64.popcnt)]
        [#x7C (instr:i64.add)]
        [#x7D (instr:i64.sub)]
        [#x7E (instr:i64.mul)]
        [#x7F (instr:i64.div_s)]
        [#x80 (instr:i64.div_u)]
        [#x81 (instr:i64.rem_s)]
        [#x82 (instr:i64.rem_u)]
        [#x83 (instr:i64.and)]
        [#x84 (instr:i64.or)]
        [#x85 (instr:i64.xor)]
        [#x86 (instr:i64.shl)]
        [#x87 (instr:i64.shr_s)]
        [#x88 (instr:i64.shr_u)]
        [#x89 (instr:i64.rotl)]
        [#x8A (instr:i64.rotl)]

        [#x8B (instr:f32.abs)]
        [#x8C (instr:f32.neg)]
        [#x8D (instr:f32.ceil)]
        [#x8E (instr:f32.floor)]
        [#x8F (instr:f32.trunc)]
        [#x90 (instr:f32.nearest)]
        [#x91 (instr:f32.sqrt)]
        [#x92 (instr:f32.add)]
        [#x93 (instr:f32.sub)]
        [#x94 (instr:f32.mul)]
        [#x95 (instr:f32.div)]
        [#x96 (instr:f32.min)]
        [#x97 (instr:f32.max)]
        [#x98 (instr:f32.copysign)]

        [#x99 (instr:f64.abs)]
        [#x9A (instr:f64.neg)]
        [#x9B (instr:f64.ceil)]
        [#x9C (instr:f64.floor)]
        [#x9D (instr:f64.trunc)]
        [#x9E (instr:f64.nearest)]
        [#x9F (instr:f64.sqrt)]
        [#xA0 (instr:f64.add)]
        [#xA1 (instr:f64.sub)]
        [#xA2 (instr:f64.mul)]
        [#xA3 (instr:f64.div)]
        [#xA4 (instr:f64.min)]
        [#xA5 (instr:f64.max)]
        [#xA6 (instr:f64.copysign)]

        [#xA7 (instr:i32.wrap_i64)]
        [#xA8 (instr:i32.trunc_f32_s)]
        [#xA9 (instr:i32.trunc_f32_u)]
        [#xAA (instr:i32.trunc_f64_s)]
        [#xAB (instr:i32.trunc_f64_u)]
        [#xAC (instr:i64.extend_i32_s)]
        [#xAD (instr:i64.extend_i32_u)]
        [#xAE (instr:i64.trunc_f32_s)]
        [#xAF (instr:i64.trunc_f32_u)]
        [#xB0 (instr:i64.trunc_f64_s)]
        [#xB1 (instr:i64.trunc_f64_u)]
        [#xB2 (instr:f32.convert_i32_s)]
        [#xB3 (instr:f32.convert_i32_u)]
        [#xB4 (instr:f32.convert_i64_s)]
        [#xB5 (instr:f32.convert_i64_u)]
        [#xB6 (instr:f32.demote_f64)]
        [#xB7 (instr:f64.convert_i32_s)]
        [#xB8 (instr:f64.convert_i32_u)]
        [#xB9 (instr:f64.convert_i64_s)]
        [#xBA (instr:f64.convert_i64_u)]
        [#xBB (instr:f64.promote_f32)]
        [#xBC (instr:i32.reinterpret_f32)]
        [#xBD (instr:i64.reinterpret_f64)]
        [#xBE (instr:f32.reinterpret_i32)]
        [#xBF (instr:f64.reinterpret_i64)]

        [#xC0 (instr:i32.extend8_s)]
        [#xC1 (instr:i32.extend16_s)]
        [#xC2 (instr:i64.extend8_s)]
        [#xC3 (instr:i64.extend16_s)]
        [#xC4 (instr:i64.extend32_s)]

        [#xFC (match (read-u32! in buf)
                [0 (instr:i32.trunc_sat_f32_s)]
                [1 (instr:i32.trunc_sat_f32_u)]
                [2 (instr:i32.trunc_sat_f64_s)]
                [3 (instr:i32.trunc_sat_f64_u)]
                [4 (instr:i64.trunc_sat_f32_s)]
                [5 (instr:i64.trunc_sat_f32_u)]
                [6 (instr:i64.trunc_sat_f64_s)]
                [7 (instr:i64.trunc_sat_f64_u)]
                [opcode (oops! in "unexpected saturating truncation opcode: ~s" opcode)])]

        [(? ender?) 'end]

        [opcode (oops! in "unexpected opcode: ~s" opcode)]))
    (if (eq? instr 'end)
        (values (list->vector (reverse instrs)) b)
        (loop (cons instr instrs)))))

(define (read-blocktype! in buf)
  (case (peek-byte in)
    [(#x40)
     (begin0 (functype null null)
       (read-byte in))]

    [(#x7F #x7E #x7D #x7C)
     (functype null (list (read-valtype! in buf)))]

    [else
     (typeidx (read-sint! 33 in buf))]))

(define (read-memarg! in buf)
  (memarg (read-u32! in buf)
          (read-u32! in buf)))

(define (read-data! in buf)
  (define idx (read-u32! in buf))
  (define-values (code _)
    (read-expr! in buf))
  (data idx code (read-bytevector! in buf)))

(define (read-import! in buf)
  (import (read-name! in buf)
          (read-name! in buf)
          (read-importdesc! in buf)))

(define (read-export! in buf)
  (export (read-name! in buf)
          (read-exportdesc! in buf)))

(define (read-global! in buf)
  (define type (read-globaltype! in buf))
  (define-values (code _)
    (read-expr! in buf))
  (global type code))

(define (read-importdesc! in buf)
  (match (read-byte! "importdesc" buf in)
    [#x00 (typeidx (read-u32! in buf))]
    [#x01 (read-tabletype! in buf)]
    [#x02 (read-memtype! in buf)]
    [#x03 (read-globaltype! in buf)]
    [b (oops! in "unexpected value while reading importdesc: ~s" b)]))

(define (read-exportdesc! in buf)
  (match (read-byte! "exportdesc" buf in)
    [#x00 (read-funcidx! in buf)]
    [#x01 (read-tableidx! in buf)]
    [#x02 (read-memidx! in buf)]
    [#x03 (read-globalidx! in buf)]
    [b (oops! in "unexpected value while reading exportdesc: ~s" b)]))

(define (read-elem! in buf)
  (define idx (read-u32! in buf))
  (define-values (code _)
    (read-expr! in buf))
  (element idx code (read-vectorof! read-funcidx! in buf)))

(define (read-tableidx! in buf)
  (tableidx (read-u32! in buf)))

(define (read-funcidx! in buf)
  (funcidx (read-u32! in buf)))

(define (read-memidx! in buf)
  (memidx (read-u32! in buf)))

(define (read-globalidx! in buf)
  (globalidx (read-u32! in buf)))

(define (read-tabletype! in buf)
  (tabletype (read-elemtype! in buf)
             (read-limits! in buf)))

(define (read-memtype! in buf)
  (memtype (read-limits! in buf)))

(define (read-globaltype! in buf)
  (globaltype (read-valtype! in buf)
              (read-mut! in buf)))

(define (read-elemtype! in buf)
  (match (read-byte! "elemtype" buf in)
    [#x70 funcref]
    [b (oops! in "unexpected value while reading elemtype: ~s" b)]))

(define (read-limits! in buf)
  (match (read-byte! "limits" buf in)
    [#x00 (limits (read-u32! in buf) #f)]
    [#x01 (limits (read-u32! in buf) (read-u32! in buf))]
    [b (oops! in "unexpected value while reading limits: ~s" b)]))

(define (read-valtype! in buf)
  (match (read-byte! "valtype" buf in)
    [#x7F i32]
    [#x7E i64]
    [#x7D f32]
    [#x7C f64]
    [b (oops! in "unexpected value while reading valtype: ~s" b)]))

(define (read-mut! in buf)
  (match (read-byte! "mut" buf in)
    [#x00 #f]
    [#x01 #t]
    [b (oops! in "unexpected value while reading mut: ~s" b)]))

(define (read-functype! in buf)
  (define b (read-byte! "functype" buf in))
  (unless (eqv? b #x60)
    (oops! in "unexpected value while reading functype: ~s" b))
  (define params (read-restype! in buf))
  (define results (read-restype! in buf))
  (functype params results))

(define (read-restype! in buf)
  (reverse (read-listof! read-valtype! in buf)))


;; core readers ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (skip-len! in buf)
  (read-u32! in buf))

(define (read-bytevector! in buf)
  (read-bytes (read-u32! in buf) in))

(define (read-listof! f in buf)
  (for/list ([_ (in-range (read-u32! in buf))])
    (f in buf)))

(define (read-vectorof! f in buf)
  (for/vector ([_ (in-range (read-u32! in buf))])
    (f in buf)))

(define (skip-n-bytes! what n in buf)
  (let loop ([remaining n])
    (unless (zero? remaining)
      (define n-read (read-bytes! buf in 0 (min remaining (bytes-length buf))))
      (if (eof-object? n-read)
          (oops! in "unexpected EOF while reading ~a" what)
          (loop (- remaining n-read))))))

(define (read-n-bytes! what buf n in)
  (let loop ([offset 0]
             [remaining n])
    (unless (zero? remaining)
      (define n-read (read-bytes! buf in offset (+ offset remaining)))
      (if (eof-object? n-read)
          (oops! in "unexpected EOF while reading ~a" what)
          (loop (+ offset n-read)
                (- remaining n-read))))))

(define (read-byte! what buf in)
  (read-n-bytes! what buf 1 in)
  (bytes-ref buf 0))

(define (read-uint! in buf)
  (let loop ([n 0]
             [s 0])
    (define b (read-byte! "unsigned integer" buf in))
    (define new-n (bitwise-ior n (arithmetic-shift (bitwise-and b #x7F) s)))
    (cond
      [(zero? (bitwise-and b #x80)) new-n]
      [else (loop new-n (+ s 7))])))

(define (read-sint! bits in buf)
  (define what (format "signed ~abit integer" bits))
  (let loop ([n 0]
             [s 0])
    (define b (read-byte! what buf in))
    (define new-n (bitwise-ior n (arithmetic-shift (bitwise-and b #x7F) s)))
    (cond
      [(zero? (bitwise-and b #x80))
       (cond
         [(>= s bits) new-n]
         [(zero? (bitwise-and b #x40)) new-n]
         [else (bitwise-ior new-n (arithmetic-shift (bitwise-not 0) s))])]

      [else
       (loop new-n (+ s 7))])))

(define (read-u32! in buf)
  (define n (read-uint! in buf))
  (begin0 n
    (when (> n (sub1 (expt 2 32)))
      (oops! in "unsigned 32bit integer out of bounds"))))

(define (read-i32! in buf)
  (read-sint! 32 in buf))

(define (read-i64! in buf)
  (read-sint! 64 in buf))

(define (read-f32! in buf)
  (read-n-bytes! "f32" buf 4 in)
  (floating-point-bytes->real buf #f 0 4))

(define (read-f64! in buf)
  (read-n-bytes! "f64" buf 8 in)
  (floating-point-bytes->real buf #f 0 8))
