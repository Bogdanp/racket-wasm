#lang racket/base

(require racket/match
         "core.rkt"
         "error.rkt"
         "location.rkt")

(provide
 current-custom-section-reader
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
    (match (read-section! buf in)
      [(? eof-object?) (mod-hash->mod sections)]
      [section (loop (with-handlers ([exn:fail? (lambda (e)
                                                  (oops! in "~a" (exn-message e)))])
                       (mod-hash-add-section sections section)))])))

(define (read-section! buf in)
  (match (read-byte in)
    [(? eof-object?) eof]
    [0 (read-custom-section! buf in)]
    [1 (read-type-section! buf in)]
    [2 (read-import-section! buf in)]
    [3 (read-function-section! buf in)]
    [4 (read-table-section! buf in)]
    [5 (read-memory-section! buf in)]
    [6 (read-global-section! buf in)]
    [7 (read-export-section! buf in)]
    [8 (read-start-section! buf in)]
    [9 (read-element-section! buf in)]
    [10 (read-code-section! buf in)]
    [11 (read-data-section! buf in)]
    [idx (oops! in "unexpected section idx ~a" idx)]))

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

(define (read-expr! buf in [ender? (λ (b) (= b #x0B))])
  (let loop ([instrs null])
    (define l (port-loc in))
    (define b (read-byte! "exprt" buf in))
    (define instr
      (match b
        ;; Control instructions
        [#x00 (instr:unreachable l)]
        [#x01 (instr:nop l)]
        [#x02 (let-values ([(type) (read-blocktype! buf in)]
                           [(code _) (read-expr! buf in)])
                (instr:block l type code))]
        [#x03 (let-values ([(type) (read-blocktype! buf in)]
                           [(code _) (read-expr! buf in)])
                (instr:loop l type code))]
        [#x04 (let-values ([(type) (read-blocktype! buf in)]
                           [(then-code end) (read-expr! buf in (lambda (opcode)
                                                                 (or (= opcode #x05)
                                                                     (= opcode #x0B))))])
                (instr:if l type then-code (and (= end #x05)
                                                (let-values ([(else-code _) (read-expr! buf in)])
                                                  else-code))))]
        [#x0C (instr:br l (read-u32! buf in))]
        [#x0D (instr:br_if l (read-u32! buf in))]
        [#x0E (instr:br_table l (read-vectorof! read-u32! buf in) (read-u32! buf in))]
        [#x0F (instr:return l)]
        [#x10 (instr:call l (read-u32! buf in))]
        [#x11 (instr:call_indirect l (read-u32! buf in) (read-u32! buf in))]

        ;; Parametric instructions
        [#x1A (instr:drop l)]
        [#x1B (instr:select l)]

        ;; Variable instructions
        [#x20 (instr:local.get l (read-u32! buf in))]
        [#x21 (instr:local.set l (read-u32! buf in))]
        [#x22 (instr:local.tee l (read-u32! buf in))]
        [#x23 (instr:global.get l (read-u32! buf in))]
        [#x24 (instr:global.set l (read-u32! buf in))]

        ;; Memory instructions
        [#x28 (instr:i32.load l (read-memarg! buf in))]
        [#x29 (instr:i64.load l (read-memarg! buf in))]
        [#x2A (instr:f32.load l (read-memarg! buf in))]
        [#x2B (instr:f64.load l (read-memarg! buf in))]
        [#x2C (instr:i32.load8_s l (read-memarg! buf in))]
        [#x2D (instr:i32.load8_u l (read-memarg! buf in))]
        [#x2E (instr:i32.load16_s l (read-memarg! buf in))]
        [#x2F (instr:i32.load16_u l (read-memarg! buf in))]
        [#x30 (instr:i64.load8_s l (read-memarg! buf in))]
        [#x31 (instr:i64.load8_u l (read-memarg! buf in))]
        [#x32 (instr:i64.load16_s l (read-memarg! buf in))]
        [#x33 (instr:i64.load16_u l (read-memarg! buf in))]
        [#x34 (instr:i64.load32_s l (read-memarg! buf in))]
        [#x35 (instr:i64.load32_u l (read-memarg! buf in))]
        [#x36 (instr:i32.store l (read-memarg! buf in))]
        [#x37 (instr:i64.store l (read-memarg! buf in))]
        [#x38 (instr:f32.store l (read-memarg! buf in))]
        [#x39 (instr:f64.store l (read-memarg! buf in))]
        [#x3A (instr:i32.store8 l (read-memarg! buf in))]
        [#x3B (instr:i32.store16 l (read-memarg! buf in))]
        [#x3C (instr:i64.store8 l (read-memarg! buf in))]
        [#x3D (instr:i64.store16 l (read-memarg! buf in))]
        [#x3E (instr:i64.store32 l (read-memarg! buf in))]
        [#x3F (instr:memory.size l (read-u32! buf in))]
        [#x40 (instr:memory.grow l (read-u32! buf in))]

        ;; Numeric instructions
        [#x41 (instr:i32.const l (read-i32! buf in))]
        [#x42 (instr:i64.const l (read-i64! buf in))]
        [#x43 (instr:f32.const l (read-f32! buf in))]
        [#x44 (instr:f64.const l (read-f64! buf in))]

        [#x45 (instr:i32.eqz l)]
        [#x46 (instr:i32.eq l)]
        [#x47 (instr:i32.ne l)]
        [#x48 (instr:i32.lt_s l)]
        [#x49 (instr:i32.lt_u l)]
        [#x4A (instr:i32.gt_s l)]
        [#x4B (instr:i32.gt_u l)]
        [#x4C (instr:i32.le_s l)]
        [#x4D (instr:i32.le_u l)]
        [#x4E (instr:i32.ge_s l)]
        [#x4F (instr:i32.ge_u l)]

        [#x50 (instr:i64.eqz l)]
        [#x51 (instr:i64.eq l)]
        [#x52 (instr:i64.ne l)]
        [#x53 (instr:i64.lt_s l)]
        [#x54 (instr:i64.lt_u l)]
        [#x55 (instr:i64.gt_s l)]
        [#x56 (instr:i64.gt_u l)]
        [#x57 (instr:i64.le_s l)]
        [#x58 (instr:i64.le_u l)]
        [#x59 (instr:i64.ge_s l)]
        [#x5A (instr:i64.ge_u l)]

        [#x5B (instr:f32.eq l)]
        [#x5C (instr:f32.ne l)]
        [#x5D (instr:f32.lt l)]
        [#x5E (instr:f32.gt l)]
        [#x5F (instr:f32.le l)]
        [#x60 (instr:f32.ge l)]

        [#x61 (instr:f64.eq l)]
        [#x62 (instr:f64.ne l)]
        [#x63 (instr:f64.lt l)]
        [#x64 (instr:f64.gt l)]
        [#x65 (instr:f64.le l)]
        [#x66 (instr:f64.ge l)]

        [#x67 (instr:i32.clz l)]
        [#x68 (instr:i32.ctz l)]
        [#x69 (instr:i32.popcnt l)]
        [#x6A (instr:i32.add l)]
        [#x6B (instr:i32.sub l)]
        [#x6C (instr:i32.mul l)]
        [#x6D (instr:i32.div_s l)]
        [#x6E (instr:i32.div_u l)]
        [#x6F (instr:i32.rem_s l)]
        [#x70 (instr:i32.rem_u l)]
        [#x71 (instr:i32.and l)]
        [#x72 (instr:i32.or l)]
        [#x73 (instr:i32.xor l)]
        [#x74 (instr:i32.shl l)]
        [#x75 (instr:i32.shr_s l)]
        [#x76 (instr:i32.shr_u l)]
        [#x77 (instr:i32.rotl l)]
        [#x78 (instr:i32.rotl l)]

        [#x79 (instr:i64.clz l)]
        [#x7A (instr:i64.ctz l)]
        [#x7B (instr:i64.popcnt l)]
        [#x7C (instr:i64.add l)]
        [#x7D (instr:i64.sub l)]
        [#x7E (instr:i64.mul l)]
        [#x7F (instr:i64.div_s l)]
        [#x80 (instr:i64.div_u l)]
        [#x81 (instr:i64.rem_s l)]
        [#x82 (instr:i64.rem_u l)]
        [#x83 (instr:i64.and l)]
        [#x84 (instr:i64.or l)]
        [#x85 (instr:i64.xor l)]
        [#x86 (instr:i64.shl l)]
        [#x87 (instr:i64.shr_s l)]
        [#x88 (instr:i64.shr_u l)]
        [#x89 (instr:i64.rotl l)]
        [#x8A (instr:i64.rotl l)]

        [#x8B (instr:f32.abs l)]
        [#x8C (instr:f32.neg l)]
        [#x8D (instr:f32.ceil l)]
        [#x8E (instr:f32.floor l)]
        [#x8F (instr:f32.trunc l)]
        [#x90 (instr:f32.nearest l)]
        [#x91 (instr:f32.sqrt l)]
        [#x92 (instr:f32.add l)]
        [#x93 (instr:f32.sub l)]
        [#x94 (instr:f32.mul l)]
        [#x95 (instr:f32.div l)]
        [#x96 (instr:f32.min l)]
        [#x97 (instr:f32.max l)]
        [#x98 (instr:f32.copysign l)]

        [#x99 (instr:f64.abs l)]
        [#x9A (instr:f64.neg l)]
        [#x9B (instr:f64.ceil l)]
        [#x9C (instr:f64.floor l)]
        [#x9D (instr:f64.trunc l)]
        [#x9E (instr:f64.nearest l)]
        [#x9F (instr:f64.sqrt l)]
        [#xA0 (instr:f64.add l)]
        [#xA1 (instr:f64.sub l)]
        [#xA2 (instr:f64.mul l)]
        [#xA3 (instr:f64.div l)]
        [#xA4 (instr:f64.min l)]
        [#xA5 (instr:f64.max l)]
        [#xA6 (instr:f64.copysign l)]

        [#xA7 (instr:i32.wrap_i64 l)]
        [#xA8 (instr:i32.trunc_f32_s l)]
        [#xA9 (instr:i32.trunc_f32_u l)]
        [#xAA (instr:i32.trunc_f64_s l)]
        [#xAB (instr:i32.trunc_f64_u l)]
        [#xAC (instr:i64.extend_i32_s l)]
        [#xAD (instr:i64.extend_i32_u l)]
        [#xAE (instr:i64.trunc_f32_s l)]
        [#xAF (instr:i64.trunc_f32_u l)]
        [#xB0 (instr:i64.trunc_f64_s l)]
        [#xB1 (instr:i64.trunc_f64_u l)]
        [#xB2 (instr:f32.convert_i32_s l)]
        [#xB3 (instr:f32.convert_i32_u l)]
        [#xB4 (instr:f32.convert_i64_s l)]
        [#xB5 (instr:f32.convert_i64_u l)]
        [#xB6 (instr:f32.demote_f64 l)]
        [#xB7 (instr:f64.convert_i32_s l)]
        [#xB8 (instr:f64.convert_i32_u l)]
        [#xB9 (instr:f64.convert_i64_s l)]
        [#xBA (instr:f64.convert_i64_u l)]
        [#xBB (instr:f64.promote_f32 l)]
        [#xBC (instr:i32.reinterpret_f32 l)]
        [#xBD (instr:i64.reinterpret_f64 l)]
        [#xBE (instr:f32.reinterpret_i32 l)]
        [#xBF (instr:f64.reinterpret_i64 l)]

        [#xC0 (instr:i32.extend8_s l)]
        [#xC1 (instr:i32.extend16_s l)]
        [#xC2 (instr:i64.extend8_s l)]
        [#xC3 (instr:i64.extend16_s l)]
        [#xC4 (instr:i64.extend32_s l)]

        [#xFC (match (read-u32! buf in)
                [0 (instr:i32.trunc_sat_f32_s l)]
                [1 (instr:i32.trunc_sat_f32_u l)]
                [2 (instr:i32.trunc_sat_f64_s l)]
                [3 (instr:i32.trunc_sat_f64_u l)]
                [4 (instr:i64.trunc_sat_f32_s l)]
                [5 (instr:i64.trunc_sat_f32_u l)]
                [6 (instr:i64.trunc_sat_f64_s l)]
                [7 (instr:i64.trunc_sat_f64_u l)]
                [opcode (oops! in "unexpected saturating truncation opcode: ~s" opcode)])]

        [(? ender?) 'end]

        [opcode (oops! in "unexpected opcode: ~s" opcode)]))
    (if (eq? instr 'end)
        (values (list->vector (reverse instrs)) b)
        (loop (cons instr instrs)))))

(define (read-blocktype! buf in)
  (case (peek-byte in)
    [(#x40)
     (begin0 (functype null null)
       (read-byte in))]

    [(#x7F #x7E #x7D #x7C)
     (functype null (list (read-valtype! buf in)))]

    [else
     (typeidx (read-sint! buf 33 in))]))

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
  (match (read-byte! "importdesc" buf in)
    [#x00 (typeidx (read-u32! buf in))]
    [#x01 (read-tabletype! buf in)]
    [#x02 (read-memtype! buf in)]
    [#x03 (read-globaltype! buf in)]
    [b (oops! in "unexpected value while reading importdesc: ~s" b)]))

(define (read-exportdesc! buf in)
  (match (read-byte! "exportdesc" buf in)
    [#x00 (read-funcidx! buf in)]
    [#x01 (read-tableidx! buf in)]
    [#x02 (read-memidx! buf in)]
    [#x03 (read-globalidx! buf in)]
    [b (oops! in "unexpected value while reading exportdesc: ~s" b)]))

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
  (match (read-byte! "elemtype" buf in)
    [#x70 funcref]
    [b (oops! in "unexpected value while reading elemtype: ~s" b)]))

(define (read-limits! buf in)
  (match (read-byte! "limits" buf in)
    [#x00 (limits (read-u32! buf in) #f)]
    [#x01 (limits (read-u32! buf in) (read-u32! buf in))]
    [b (oops! in "unexpected value while reading limits: ~s" b)]))

(define (read-valtype! buf in)
  (match (read-byte! "valtype" buf in)
    [#x7F i32]
    [#x7E i64]
    [#x7D f32]
    [#x7C f64]
    [b (oops! in "unexpected value while reading valtype: ~s" b)]))

(define (read-mut! buf in)
  (match (read-byte! "mut" buf in)
    [#x00 #f]
    [#x01 #t]
    [b (oops! in "unexpected value while reading mut: ~s" b)]))

(define (read-functype! buf in)
  (define b (read-byte! "functype" buf in))
  (unless (eqv? b #x60)
    (oops! in "unexpected value while reading functype: ~s" b))
  (define params (read-restype! buf in))
  (define results (read-restype! buf in))
  (functype params results))

(define (read-restype! buf in)
  (reverse (read-listof! read-valtype! buf in)))


;; core readers ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (skip-len! buf in)
  (read-u32! buf in))

(define (read-bytevector! buf in)
  (read-bytes (read-u32! buf in) in))

(define (read-listof! f buf in)
  (for/list ([_ (in-range (read-u32! buf in))])
    (f buf in)))

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
    (unless (zero? remaining)
      (define n-read (read-bytes! buf in offset (+ offset remaining)))
      (if (eof-object? n-read)
          (oops! in "unexpected EOF while reading ~a" what)
          (loop (+ offset n-read)
                (- remaining n-read))))))

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

(define (read-sint! buf bits in)
  (define what (format "signed ~abit integer" bits))
  (let loop ([n 0]
             [s 0])
    (define b (read-byte! what buf in))
    (define new-n (bitwise-ior n (arithmetic-shift (bitwise-and b #x7F) s)))
    (define new-shift (+ s 7))
    (cond
      [(> (bitwise-and b #x80) 0) (loop new-n new-shift)]
      [(>= new-shift bits) new-n]
      [(zero? (bitwise-and b #x40)) new-n]
      [else (bitwise-ior new-n (arithmetic-shift -1 new-shift))])))

(define (read-u32! buf in)
  (define n (read-uint! buf in))
  (begin0 n
    (when (> n (sub1 (expt 2 32)))
      (oops! in "unsigned 32bit integer out of bounds"))))

(define (read-i32! buf in)
  (read-sint! buf 32 in))

(define (read-i64! buf in)
  (read-sint! buf 64 in))

(define (read-f32! buf in)
  (read-n-bytes! "f32" buf 4 in)
  (floating-point-bytes->real buf #f 0 4))

(define (read-f64! buf in)
  (read-n-bytes! "f64" buf 8 in)
  (floating-point-bytes->real buf #f 0 8))
