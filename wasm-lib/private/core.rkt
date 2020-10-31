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
 instruction-type)

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

(define-generics instruction
  (instruction-type instruction))

(define-syntax-parser define-instruction
  #:literal-sets (instruction-literals)
  [(_ name:id
      (~optional (f:id ...))
      (~optional (~seq : (~optional (~seq forall v:id ...+)) [t ...] -> [rt ...])))
   #:with id (format-id #'name "instr:~a" #'name)
   #'(begin
       (provide (struct-out id))
       (struct id (~? (f ...) ())
         #:transparent
         #:methods gen:instruction
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
;;  ::= id maybe-immediates maybe-type
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
  [unreachable]

  [nop : [] -> []]

  [block (type code)]
  [loop  (type code)]
  [if    (type then-code else-code)]

  [br       (lbl)]
  [br_if    (lbl)]
  [br_table (tbl lbl)]

  [return]
  [call          (idx)]
  [call_indirect (idx tableidx)]

  ;; Parametric instructions
  [drop   : forall t [t      ] -> [ ]]
  [select : forall t [t t i32] -> [t]]

  ;; Variable instructions
  [local.get  (idx) : forall t [ ] -> [t]]
  [local.set  (idx) : forall t [t] -> [ ]]
  [local.tee  (idx) : forall t [t] -> [t]]
  [global.get (idx) : forall t [ ] -> [t]]
  [global.set (idx) : forall t [t] -> [t]]

  ;; Memory instructions
  [i32.load     (arg) : [i32    ] -> [i32]]
  [i64.load     (arg) : [i32    ] -> [i64]]
  [f32.load     (arg) : [i32    ] -> [f32]]
  [f64.load     (arg) : [i32    ] -> [f64]]
  [i32.load8_s  (arg) : [i32    ] -> [i32]]
  [i32.load8_u  (arg) : [i32    ] -> [i32]]
  [i32.load16_s (arg) : [i32    ] -> [i32]]
  [i32.load16_u (arg) : [i32    ] -> [i32]]
  [i64.load8_s  (arg) : [i32    ] -> [i64]]
  [i64.load8_u  (arg) : [i32    ] -> [i64]]
  [i64.load16_s (arg) : [i32    ] -> [i64]]
  [i64.load16_u (arg) : [i32    ] -> [i64]]
  [i64.load32_s (arg) : [i32    ] -> [i64]]
  [i64.load32_u (arg) : [i32    ] -> [i64]]
  [i32.store    (arg) : [i32 i32] -> [   ]]
  [i64.store    (arg) : [i32 i64] -> [   ]]
  [f32.store    (arg) : [i32 f32] -> [   ]]
  [f64.store    (arg) : [i32 f64] -> [   ]]
  [i32.store8   (arg) : [i32 i32] -> [   ]]
  [i32.store16  (arg) : [i32 i32] -> [   ]]
  [i64.store8   (arg) : [i32 i64] -> [   ]]
  [i64.store16  (arg) : [i32 i64] -> [   ]]
  [i64.store32  (arg) : [i32 i64] -> [   ]]

  [memory.size (idx) : [   ] -> [i32]]
  [memory.grow (idx) : [i32] -> [i32]]

  ;; Numeric instructions
  [i32.const (n) : [] -> [i32]]
  [i64.const (n) : [] -> [i64]]
  [f32.const (n) : [] -> [f32]]
  [f64.const (n) : [] -> [f64]]

  [i32.eqz  : [i32    ] -> [i32]]
  [i32.eq   : [i32 i32] -> [i32]]
  [i32.ne   : [i32 i32] -> [i32]]
  [i32.lt_s : [i32 i32] -> [i32]]
  [i32.lt_u : [i32 i32] -> [i32]]
  [i32.gt_s : [i32 i32] -> [i32]]
  [i32.gt_u : [i32 i32] -> [i32]]
  [i32.le_s : [i32 i32] -> [i32]]
  [i32.le_u : [i32 i32] -> [i32]]
  [i32.ge_s : [i32 i32] -> [i32]]
  [i32.ge_u : [i32 i32] -> [i32]]

  [i64.eqz  : [i64    ] -> [i32]]
  [i64.eq   : [i64 i64] -> [i32]]
  [i64.ne   : [i64 i64] -> [i32]]
  [i64.lt_s : [i64 i64] -> [i32]]
  [i64.lt_u : [i64 i64] -> [i32]]
  [i64.gt_s : [i64 i64] -> [i32]]
  [i64.gt_u : [i64 i64] -> [i32]]
  [i64.le_s : [i64 i64] -> [i32]]
  [i64.le_u : [i64 i64] -> [i32]]
  [i64.ge_s : [i64 i64] -> [i32]]
  [i64.ge_u : [i64 i64] -> [i32]]

  [f32.eq : [f32 f32] -> [i32]]
  [f32.ne : [f32 f32] -> [i32]]
  [f32.lt : [f32 f32] -> [i32]]
  [f32.gt : [f32 f32] -> [i32]]
  [f32.le : [f32 f32] -> [i32]]
  [f32.ge : [f32 f32] -> [i32]]

  [f64.eq : [f64 f64] -> [i32]]
  [f64.ne : [f64 f64] -> [i32]]
  [f64.lt : [f64 f64] -> [i32]]
  [f64.gt : [f64 f64] -> [i32]]
  [f64.le : [f64 f64] -> [i32]]
  [f64.ge : [f64 f64] -> [i32]]

  [i32.clz    : [i32    ] -> [i32]]
  [i32.ctz    : [i32    ] -> [i32]]
  [i32.popcnt : [i32    ] -> [i32]]
  [i32.add    : [i32 i32] -> [i32]]
  [i32.sub    : [i32 i32] -> [i32]]
  [i32.mul    : [i32 i32] -> [i32]]
  [i32.div_s  : [i32 i32] -> [i32]]
  [i32.div_u  : [i32 i32] -> [i32]]
  [i32.rem_s  : [i32 i32] -> [i32]]
  [i32.rem_u  : [i32 i32] -> [i32]]
  [i32.and    : [i32 i32] -> [i32]]
  [i32.or     : [i32 i32] -> [i32]]
  [i32.xor    : [i32 i32] -> [i32]]
  [i32.shl    : [i32 i32] -> [i32]]
  [i32.shr_s  : [i32 i32] -> [i32]]
  [i32.shr_u  : [i32 i32] -> [i32]]
  [i32.rotl   : [i32 i32] -> [i32]]
  [i32.rotr   : [i32 i32] -> [i32]]

  [i64.clz    : [i64    ] -> [i64]]
  [i64.ctz    : [i64    ] -> [i64]]
  [i64.popcnt : [i64    ] -> [i64]]
  [i64.add    : [i64 i64] -> [i64]]
  [i64.sub    : [i64 i64] -> [i64]]
  [i64.mul    : [i64 i64] -> [i64]]
  [i64.div_s  : [i64 i64] -> [i64]]
  [i64.div_u  : [i64 i64] -> [i64]]
  [i64.rem_s  : [i64 i64] -> [i64]]
  [i64.rem_u  : [i64 i64] -> [i64]]
  [i64.and    : [i64 i64] -> [i64]]
  [i64.or     : [i64 i64] -> [i64]]
  [i64.xor    : [i64 i64] -> [i64]]
  [i64.shl    : [i64 i64] -> [i64]]
  [i64.shr_s  : [i64 i64] -> [i64]]
  [i64.shr_u  : [i64 i64] -> [i64]]
  [i64.rotl   : [i64 i64] -> [i64]]
  [i64.rotr   : [i64 i64] -> [i64]]

  [f32.abs      : [f32    ] -> [f32]]
  [f32.neg      : [f32    ] -> [f32]]
  [f32.ceil     : [f32    ] -> [f32]]
  [f32.floor    : [f32    ] -> [f32]]
  [f32.trunc    : [f32    ] -> [f32]]
  [f32.nearest  : [f32    ] -> [f32]]
  [f32.sqrt     : [f32    ] -> [f32]]
  [f32.add      : [f32 f32] -> [f32]]
  [f32.sub      : [f32 f32] -> [f32]]
  [f32.mul      : [f32 f32] -> [f32]]
  [f32.div      : [f32 f32] -> [f32]]
  [f32.min      : [f32 f32] -> [f32]]
  [f32.max      : [f32 f32] -> [f32]]
  [f32.copysign : [f32 f32] -> [f32]]

  [f64.abs      : [f64    ] -> [f64]]
  [f64.neg      : [f64    ] -> [f64]]
  [f64.ceil     : [f64    ] -> [f64]]
  [f64.floor    : [f64    ] -> [f64]]
  [f64.trunc    : [f64    ] -> [f64]]
  [f64.nearest  : [f64    ] -> [f64]]
  [f64.sqrt     : [f64    ] -> [f64]]
  [f64.add      : [f64 f64] -> [f64]]
  [f64.sub      : [f64 f64] -> [f64]]
  [f64.mul      : [f64 f64] -> [f64]]
  [f64.div      : [f64 f64] -> [f64]]
  [f64.min      : [f64 f64] -> [f64]]
  [f64.max      : [f64 f64] -> [f64]]
  [f64.copysign : [f64 f64] -> [f64]]

  [i32.wrap_i64        : [i64] -> [i32]]
  [i32.trunc_f32_s     : [f32] -> [i32]]
  [i32.trunc_f32_u     : [f32] -> [i32]]
  [i32.trunc_f64_s     : [f64] -> [i32]]
  [i32.trunc_f64_u     : [f64] -> [i32]]
  [i64.extend_i32_s    : [i32] -> [i64]]
  [i64.extend_i32_u    : [i32] -> [i64]]
  [i64.trunc_f32_s     : [f32] -> [i64]]
  [i64.trunc_f32_u     : [f32] -> [i64]]
  [i64.trunc_f64_s     : [f64] -> [i64]]
  [i64.trunc_f64_u     : [f64] -> [i64]]
  [f32.convert_i32_s   : [i32] -> [f32]]
  [f32.convert_i32_u   : [i32] -> [f32]]
  [f32.convert_i64_s   : [i64] -> [f32]]
  [f32.convert_i64_u   : [i64] -> [f32]]
  [f32.demote_f64      : [f64] -> [f32]]
  [f64.convert_i32_s   : [i32] -> [f64]]
  [f64.convert_i32_u   : [i32] -> [f64]]
  [f64.convert_i64_s   : [i64] -> [f64]]
  [f64.convert_i64_u   : [i64] -> [f64]]
  [f64.promote_f32     : [f32] -> [f64]]
  [i32.reinterpret_f32 : [f32] -> [i32]]
  [i64.reinterpret_f64 : [f64] -> [i64]]
  [f32.reinterpret_i32 : [i32] -> [f32]]
  [f64.reinterpret_i64 : [i64] -> [f64]]

  [i32.extend8_s  : forall t [t] -> [i32]]
  [i32.extend16_s : forall t [t] -> [i32]]
  [i64.extend8_s  : forall t [t] -> [i64]]
  [i64.extend16_s : forall t [t] -> [i64]]
  [i64.extend32_s : forall t [t] -> [i64]]

  [i32.trunc_sat_f32_s : [f32] -> [i32]]
  [i32.trunc_sat_f32_u : [f32] -> [i32]]
  [i32.trunc_sat_f64_s : [f64] -> [i32]]
  [i32.trunc_sat_f64_u : [f64] -> [i32]]
  [i64.trunc_sat_f32_s : [f32] -> [i64]]
  [i64.trunc_sat_f32_u : [f32] -> [i64]]
  [i64.trunc_sat_f64_s : [f64] -> [i64]]
  [i64.trunc_sat_f64_u : [f64] -> [i64]])


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
 (struct-out mod)
 make-mod-hash
 mod-hash-add-section
 mod-hash->mod)

(define (hash-add-section-help h k v multi?)
  (cond
    [multi?
     (hash-update h k (curry cons v) null)]
    [else
     (when (hash-has-key? h k)
       (raise-arguments-error 'mod-hash-add-section
                              "duplicate section"
                              "name" (symbol->string k)))
     (hash-set h k v)]))

(begin-for-syntax
  (define-syntax-class mod-section
    (pattern name:id #:with default #'(vector))
    (pattern (name:id default:expr))))

(define-syntax-parser define-mod-struct
  [(_ name:id
      [section:mod-section
       (~optional (~and #:multi multi))
       section-type?:expr
       section-accessor:expr] ...+)
   #:with (multi? ...) (for/list ([stx (in-list (syntax-e #'((~? multi #f) ...)))])
                         (if (syntax->datum stx) #'#t #'#f))
   #:with make-hash-name (format-id #'name "make-~a-hash" #'name)
   #:with hash-add-section-name (format-id #'name "~a-hash-add-section" #'name)
   #:with hash->name (format-id #'name "~a-hash->~a" #'name #'name)
   #'(begin
       (define (make-hash-name) (hasheq))
       (define (hash-add-section-name h v)
         (cond
           [(section-type? v) (hash-add-section-help h 'section.name (section-accessor v) multi?)] ...
           [else (raise-argument-error 'hash-add-section-name "section?" v)]))
       (define (hash->name h)
         (name (hash-ref h 'section.name section.default) ...))
       (struct name (section.name ...)
         #:transparent))])

(define-mod-struct mod
  [(customs null) #:multi custom-section? custom-section-data]
  [types type-section? type-section-functypes]
  [imports import-section? import-section-imports]
  [functions function-section? function-section-typeidxs]
  [tables table-section? table-section-tables]
  [memories memory-section? memory-section-memories]
  [globals global-section? global-section-globals]
  [exports export-section? export-section-exports]
  [(start #f) start-section? start-section-funcidx]
  [elements element-section? element-section-elements]
  [codes code-section? code-section-codes]
  [datas data-section? data-section-datas])
