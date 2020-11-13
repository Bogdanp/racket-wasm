#lang racket/base

(require (for-syntax racket/base
                     racket/syntax)
         racket/function
         racket/generic
         racket/match
         syntax/parse
         syntax/parse/define)

;; values ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(provide
 type-unify)

(define-generics type
  (type-unify type other))

(struct valtype (id)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc t out _mode)
     (display (valtype-id t) out))]
  #:methods gen:type
  [(define/generic super-unify type-unify)
   (define (type-unify t other)
     (cond
       [(valtype? other) (eq? t other)]
       [(typevar? other) (super-unify other t)]
       [else #f]))])

(struct typevar (id [vt #:mutable])
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc t out _mode)
     (define id (typevar-id t))
     (define vt (typevar-vt t))
     (display `(typevar ,id ,(or vt '_)) out))]
  #:methods gen:type
  [(define/generic super-unify type-unify)
   (define (type-unify t other)
     (match t
       [(typevar _ #f) (begin0 #t (set-typevar-vt! t other))]
       [(typevar _ vt) (super-unify vt other)]))])

(define-syntax-parser define-valtype
  [(_ name:id)
   #:with name? (format-id #'name "~a?" #'name)
   #'(begin
       (define name (valtype 'name))
       (define (name? v) (eq? v name))
       (provide name name?))])

(define-syntax-parser define-typevar
  [(_ name:id)
   #:with name? (format-id #'name "~a?" #'name)
   #'(begin
       (define name (typevar 'name #f))
       (define (name? v) (eq? v name)))])

(define-syntax-rule (define-valtypes name ...)
  (begin (define-valtype name) ...))

(define-valtypes i32 i64 f32 f64)


;; elems ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-syntax-parser define-elemtype
  [(_ name:id)
   #:with name? (format-id #'name "~a?" #'name)
   #'(begin
       (define name '(elemtype name))
       (define (name? v) (eq? v name))
       (provide name name?))])

(define-elemtype funcref)


;; records ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-syntax-rule (define-record name (f ...))
  (begin
    (struct name (f ...) #:transparent)
    (provide (struct-out name))))

(define-record limits (lo hi))
(define-record funcidx (idx))
(define-record typeidx (idx))
(define-record tableidx (idx))
(define-record memidx (idx))
(define-record globalidx (idx))
(define-record tabletype (elemtype limits))
(define-record memtype (limits))
(define-record globaltype (valtype mutable?))
(define-record memarg (align offset))
(define-record import (mod name description))
(define-record export (name description))
(define-record global (type code))
(define-record functype (params results))
(define-record element (table offset init))
(define-record locals (n valtype))
(define-record code (locals instrs))
(define-record data (idx offset bs))


;; instructions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(provide
 instruction?
 instruction-loc
 instruction-type
 opcode
 op:trunc_sat)

(struct instruction (loc)
  #:transparent)

(define-values (prop:opcode prop:opcode? opcode)
  (make-struct-type-property 'opcode))

(define op:trunc_sat #xFC)

(begin-for-syntax
  (define (raise-instruction-literal-error stx)
    (raise-syntax-error #f "may only be used within an instruction definition" stx)))

(define-syntax-rule (define-instruction-literals set-id (id ...))
  (begin
    (define-syntax id raise-instruction-literal-error) ...
    (begin-for-syntax
      (define-literal-set set-id (id ...)))))

(define-instruction-literals instruction-literals
  [: -> forall])

(define-generics typed
  (instruction-type typed))

(define-syntax-parser define-instruction
  #:literal-sets (instruction-literals)
  [(_ opcode:number name:id
      (~optional (f:id ...))
      (~optional (~seq : (~optional (~seq forall v:id ...+)) [t ...] -> [rt ...])))
   #:with id (format-id #'name "instr:~a" #'name)
   #:with opcode-id (format-id #'name "op:~a" #'name)
   #'(begin
       (provide opcode-id (struct-out id))
       (define opcode-id opcode)
       (struct id instruction (~? (f ...) ())
         #:transparent
         #:property prop:opcode opcode-id
         #:methods gen:typed
         [(define (instruction-type _)
            (~? (begin (define-typevar v) ...))
            (functype (~? (reverse (list t ...)) null)
                      (~? (reverse (list rt ...)) null)))]))])

(define-syntax-rule (define-instructions (def ...) ...)
  (begin (define-instruction def ...) ...))

;; The spec and both formats use the notation [a b] to denote a result
;; type where "b" is the top of the stack.  We do the same below, but
;; interally we store these types in reverse so that their order
;; matches our list-based stacks.

;; instdef
;;  ::= '[' opcode id maybe-immediates maybe-type ']'
;; maybe-immediates
;;  ::=
;;   | '(' id* ')'
;; maybe-type
;;  ::=
;;   | ':' maybe-typevardefs types '->' types
;; maybe-typevardefs
;;  ::=
;;   | 'forall' id+
;; types
;;  ::= '(' id* ')'
(define-instructions
  ;; Control instructions
  [#x00 unreachable]

  [#x01 nop : [] -> []]

  [#x02 block (type code)]
  [#x03 loop  (type code)]
  [#x04 if    (type then-code else-code)]

  [#x0C br       (lbl)]
  [#x0D br_if    (lbl)]
  [#x0E br_table (tbl lbl)]

  [#x0F return]
  [#x10 call          (idx)]
  [#x11 call_indirect (idx tbl)]

  ;; Parametric instructions
  [#x1A drop   : forall t [t      ] -> [ ]]
  [#x1B select : forall t [t t i32] -> [t]]

  ;; Variable instructions
  [#x20 local.get  (idx) : forall t [ ] -> [t]]
  [#x21 local.set  (idx) : forall t [t] -> [ ]]
  [#x22 local.tee  (idx) : forall t [t] -> [t]]
  [#x23 global.get (idx) : forall t [ ] -> [t]]
  [#x24 global.set (idx) : forall t [t] -> [t]]

  ;; Memory instructions
  [#x28 i32.load     (arg) : [i32    ] -> [i32]]
  [#x29 i64.load     (arg) : [i32    ] -> [i64]]
  [#x2A f32.load     (arg) : [i32    ] -> [f32]]
  [#x2B f64.load     (arg) : [i32    ] -> [f64]]
  [#x2C i32.load8_s  (arg) : [i32    ] -> [i32]]
  [#x2D i32.load8_u  (arg) : [i32    ] -> [i32]]
  [#x2E i32.load16_s (arg) : [i32    ] -> [i32]]
  [#x2F i32.load16_u (arg) : [i32    ] -> [i32]]
  [#x30 i64.load8_s  (arg) : [i32    ] -> [i64]]
  [#x31 i64.load8_u  (arg) : [i32    ] -> [i64]]
  [#x32 i64.load16_s (arg) : [i32    ] -> [i64]]
  [#x33 i64.load16_u (arg) : [i32    ] -> [i64]]
  [#x34 i64.load32_s (arg) : [i32    ] -> [i64]]
  [#x35 i64.load32_u (arg) : [i32    ] -> [i64]]
  [#x36 i32.store    (arg) : [i32 i32] -> [   ]]
  [#x37 i64.store    (arg) : [i32 i64] -> [   ]]
  [#x38 f32.store    (arg) : [i32 f32] -> [   ]]
  [#x39 f64.store    (arg) : [i32 f64] -> [   ]]
  [#x3A i32.store8   (arg) : [i32 i32] -> [   ]]
  [#x3B i32.store16  (arg) : [i32 i32] -> [   ]]
  [#x3C i64.store8   (arg) : [i32 i64] -> [   ]]
  [#x3D i64.store16  (arg) : [i32 i64] -> [   ]]
  [#x3E i64.store32  (arg) : [i32 i64] -> [   ]]

  [#x3F memory.size (idx) : [   ] -> [i32]]
  [#x40 memory.grow (idx) : [i32] -> [i32]]

  ;; Numeric instructions
  [#x41 i32.const (n) : [] -> [i32]]
  [#x42 i64.const (n) : [] -> [i64]]
  [#x43 f32.const (n) : [] -> [f32]]
  [#x44 f64.const (n) : [] -> [f64]]

  [#x45 i32.eqz  : [i32    ] -> [i32]]
  [#x46 i32.eq   : [i32 i32] -> [i32]]
  [#x47 i32.ne   : [i32 i32] -> [i32]]
  [#x48 i32.lt_s : [i32 i32] -> [i32]]
  [#x49 i32.lt_u : [i32 i32] -> [i32]]
  [#x4A i32.gt_s : [i32 i32] -> [i32]]
  [#x4B i32.gt_u : [i32 i32] -> [i32]]
  [#x4C i32.le_s : [i32 i32] -> [i32]]
  [#x4D i32.le_u : [i32 i32] -> [i32]]
  [#x4E i32.ge_s : [i32 i32] -> [i32]]
  [#x4F i32.ge_u : [i32 i32] -> [i32]]

  [#x50 i64.eqz  : [i64    ] -> [i32]]
  [#x51 i64.eq   : [i64 i64] -> [i32]]
  [#x52 i64.ne   : [i64 i64] -> [i32]]
  [#x53 i64.lt_s : [i64 i64] -> [i32]]
  [#x54 i64.lt_u : [i64 i64] -> [i32]]
  [#x55 i64.gt_s : [i64 i64] -> [i32]]
  [#x56 i64.gt_u : [i64 i64] -> [i32]]
  [#x57 i64.le_s : [i64 i64] -> [i32]]
  [#x58 i64.le_u : [i64 i64] -> [i32]]
  [#x59 i64.ge_s : [i64 i64] -> [i32]]
  [#x5A i64.ge_u : [i64 i64] -> [i32]]

  [#x5B f32.eq : [f32 f32] -> [i32]]
  [#x5C f32.ne : [f32 f32] -> [i32]]
  [#x5D f32.lt : [f32 f32] -> [i32]]
  [#x5E f32.gt : [f32 f32] -> [i32]]
  [#x5F f32.le : [f32 f32] -> [i32]]
  [#x60 f32.ge : [f32 f32] -> [i32]]

  [#x61 f64.eq : [f64 f64] -> [i32]]
  [#x62 f64.ne : [f64 f64] -> [i32]]
  [#x63 f64.lt : [f64 f64] -> [i32]]
  [#x64 f64.gt : [f64 f64] -> [i32]]
  [#x65 f64.le : [f64 f64] -> [i32]]
  [#x66 f64.ge : [f64 f64] -> [i32]]

  [#x67 i32.clz    : [i32    ] -> [i32]]
  [#x68 i32.ctz    : [i32    ] -> [i32]]
  [#x69 i32.popcnt : [i32    ] -> [i32]]
  [#x6A i32.add    : [i32 i32] -> [i32]]
  [#x6B i32.sub    : [i32 i32] -> [i32]]
  [#x6C i32.mul    : [i32 i32] -> [i32]]
  [#x6D i32.div_s  : [i32 i32] -> [i32]]
  [#x6E i32.div_u  : [i32 i32] -> [i32]]
  [#x6F i32.rem_s  : [i32 i32] -> [i32]]
  [#x70 i32.rem_u  : [i32 i32] -> [i32]]
  [#x71 i32.and    : [i32 i32] -> [i32]]
  [#x72 i32.or     : [i32 i32] -> [i32]]
  [#x73 i32.xor    : [i32 i32] -> [i32]]
  [#x74 i32.shl    : [i32 i32] -> [i32]]
  [#x75 i32.shr_s  : [i32 i32] -> [i32]]
  [#x76 i32.shr_u  : [i32 i32] -> [i32]]
  [#x77 i32.rotl   : [i32 i32] -> [i32]]
  [#x78 i32.rotr   : [i32 i32] -> [i32]]

  [#x79 i64.clz    : [i64    ] -> [i64]]
  [#x7A i64.ctz    : [i64    ] -> [i64]]
  [#x7B i64.popcnt : [i64    ] -> [i64]]
  [#x7C i64.add    : [i64 i64] -> [i64]]
  [#x7D i64.sub    : [i64 i64] -> [i64]]
  [#x7E i64.mul    : [i64 i64] -> [i64]]
  [#x7F i64.div_s  : [i64 i64] -> [i64]]
  [#x80 i64.div_u  : [i64 i64] -> [i64]]
  [#x81 i64.rem_s  : [i64 i64] -> [i64]]
  [#x82 i64.rem_u  : [i64 i64] -> [i64]]
  [#x83 i64.and    : [i64 i64] -> [i64]]
  [#x84 i64.or     : [i64 i64] -> [i64]]
  [#x85 i64.xor    : [i64 i64] -> [i64]]
  [#x86 i64.shl    : [i64 i64] -> [i64]]
  [#x87 i64.shr_s  : [i64 i64] -> [i64]]
  [#x88 i64.shr_u  : [i64 i64] -> [i64]]
  [#x89 i64.rotl   : [i64 i64] -> [i64]]
  [#x8A i64.rotr   : [i64 i64] -> [i64]]

  [#x8B f32.abs      : [f32    ] -> [f32]]
  [#x8C f32.neg      : [f32    ] -> [f32]]
  [#x8D f32.ceil     : [f32    ] -> [f32]]
  [#x8E f32.floor    : [f32    ] -> [f32]]
  [#x8F f32.trunc    : [f32    ] -> [f32]]
  [#x90 f32.nearest  : [f32    ] -> [f32]]
  [#x91 f32.sqrt     : [f32    ] -> [f32]]
  [#x92 f32.add      : [f32 f32] -> [f32]]
  [#x93 f32.sub      : [f32 f32] -> [f32]]
  [#x94 f32.mul      : [f32 f32] -> [f32]]
  [#x95 f32.div      : [f32 f32] -> [f32]]
  [#x96 f32.min      : [f32 f32] -> [f32]]
  [#x97 f32.max      : [f32 f32] -> [f32]]
  [#x98 f32.copysign : [f32 f32] -> [f32]]

  [#x99 f64.abs      : [f64    ] -> [f64]]
  [#x9A f64.neg      : [f64    ] -> [f64]]
  [#x9B f64.ceil     : [f64    ] -> [f64]]
  [#x9C f64.floor    : [f64    ] -> [f64]]
  [#x9D f64.trunc    : [f64    ] -> [f64]]
  [#x9E f64.nearest  : [f64    ] -> [f64]]
  [#x9F f64.sqrt     : [f64    ] -> [f64]]
  [#xA0 f64.add      : [f64 f64] -> [f64]]
  [#xA1 f64.sub      : [f64 f64] -> [f64]]
  [#xA2 f64.mul      : [f64 f64] -> [f64]]
  [#xA3 f64.div      : [f64 f64] -> [f64]]
  [#xA4 f64.min      : [f64 f64] -> [f64]]
  [#xA5 f64.max      : [f64 f64] -> [f64]]
  [#xA6 f64.copysign : [f64 f64] -> [f64]]

  [#xA7 i32.wrap_i64        : [i64] -> [i32]]
  [#xA8 i32.trunc_f32_s     : [f32] -> [i32]]
  [#xA9 i32.trunc_f32_u     : [f32] -> [i32]]
  [#xAA i32.trunc_f64_s     : [f64] -> [i32]]
  [#xAB i32.trunc_f64_u     : [f64] -> [i32]]
  [#xAC i64.extend_i32_s    : [i32] -> [i64]]
  [#xAD i64.extend_i32_u    : [i32] -> [i64]]
  [#xAE i64.trunc_f32_s     : [f32] -> [i64]]
  [#xAF i64.trunc_f32_u     : [f32] -> [i64]]
  [#xB0 i64.trunc_f64_s     : [f64] -> [i64]]
  [#xB1 i64.trunc_f64_u     : [f64] -> [i64]]
  [#xB2 f32.convert_i32_s   : [i32] -> [f32]]
  [#xB3 f32.convert_i32_u   : [i32] -> [f32]]
  [#xB4 f32.convert_i64_s   : [i64] -> [f32]]
  [#xB5 f32.convert_i64_u   : [i64] -> [f32]]
  [#xB6 f32.demote_f64      : [f64] -> [f32]]
  [#xB7 f64.convert_i32_s   : [i32] -> [f64]]
  [#xB8 f64.convert_i32_u   : [i32] -> [f64]]
  [#xB9 f64.convert_i64_s   : [i64] -> [f64]]
  [#xBA f64.convert_i64_u   : [i64] -> [f64]]
  [#xBB f64.promote_f32     : [f32] -> [f64]]
  [#xBC i32.reinterpret_f32 : [f32] -> [i32]]
  [#xBD i64.reinterpret_f64 : [f64] -> [i64]]
  [#xBE f32.reinterpret_i32 : [i32] -> [f32]]
  [#xBF f64.reinterpret_i64 : [i64] -> [f64]]

  [#xC0 i32.extend8_s  : forall t [t] -> [i32]]
  [#xC1 i32.extend16_s : forall t [t] -> [i32]]
  [#xC2 i64.extend8_s  : forall t [t] -> [i64]]
  [#xC3 i64.extend16_s : forall t [t] -> [i64]]
  [#xC4 i64.extend32_s : forall t [t] -> [i64]]

  [#xFC00 i32.trunc_sat_f32_s : [f32] -> [i32]]
  [#xFC01 i32.trunc_sat_f32_u : [f32] -> [i32]]
  [#xFC02 i32.trunc_sat_f64_s : [f64] -> [i32]]
  [#xFC03 i32.trunc_sat_f64_u : [f64] -> [i32]]
  [#xFC04 i64.trunc_sat_f32_s : [f32] -> [i64]]
  [#xFC05 i64.trunc_sat_f32_u : [f32] -> [i64]]
  [#xFC06 i64.trunc_sat_f64_s : [f64] -> [i64]]
  [#xFC07 i64.trunc_sat_f64_u : [f64] -> [i64]])


;; sections ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-syntax-rule (define-sections [name (f ...)] ...)
  (begin
    (struct name (f ...) #:transparent) ...
    (provide (struct-out name) ...)))

(define-sections
  [custom-section (data)]
  [type-section (functypes)]
  [import-section (imports)]
  [function-section (typeidxs)]
  [table-section (tables)]
  [memory-section (memories)]
  [global-section (globals)]
  [export-section (exports)]
  [start-section (funcidx)]
  [element-section (elements)]
  [code-section (codes)]
  [data-section (datas)])


;; modules ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(provide
 (struct-out mod))

(struct mod
  (customs
   types
   imports
   functions
   tables
   memories
   globals
   exports
   start
   elements
   codes
   datas)
  #:transparent)
