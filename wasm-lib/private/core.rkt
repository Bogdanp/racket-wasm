#lang racket/base

(require (for-syntax racket/base
                     racket/syntax)
         racket/generic
         racket/match
         racket/struct
         syntax/parse/define
         "error.rkt")

;; values ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(provide
 type-unify)

(define-generics type
  (type-unify type other))

(define-syntax-parser define-valtype
  [(_ name:id)
   #:with name? (format-id #'name "~a?" #'name)
   #'(begin
       (define-values (name name?)
         (let ()
           (struct name ()
             #:transparent
             #:methods gen:custom-write
             [(define write-proc
                (make-constructor-style-printer
                 (lambda (o) 'name)
                 (lambda (o) null)))]
             #:methods gen:type
             [(define (type-unify t other)
                (and (eq? t other) t))])
           (values (name) name?)))
       (provide name name?))])

(define-syntax-parser define-typevar
  [(_ name:id)
   #:with name? (format-id #'name "~a?" #'name)
   #:with name-vt (format-id #'name "~a-vt" #'name)
   #:with set-name-vt! (format-id #'name "set-~a-vt!" #'name)
   #'(define-values (name name?)
       (let ()
         (struct name ([vt #:mutable])
           #:transparent
           #:methods gen:custom-write
           [(define write-proc
              (make-constructor-style-printer
               (lambda (o) 'name)
               (lambda (o) (list (or (name-vt o) '_)))))]
           #:methods gen:type
           [(define/generic super-type-unify type-unify)
            (define (type-unify t other)
              (match t
                [(name #f) (begin0 t (set-name-vt! t other))]
                [(name vt) (super-type-unify vt other)]))])
         (values (name #f) name?)))])

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
(define-record import (mod name description))
(define-record export (name description))
(define-record functype (params results))
(define-record element (table offset init))
(define-record locals (n valtype))
(define-record code (locals instrs))
(define-record data (idx offset bs))


;; instructions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(provide
 instruction-type)

(define-generics instruction
  (instruction-type instruction))

(define-syntax-parser define-instruction
  #:datum-literals (: -> forall)
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
            (functype (~? (list t ...) null)
                      (~? (list rt ...) null)))]))])

(define-syntax-rule (define-instructions (def ...) ...)
  (begin (define-instruction def ...) ...))

;; instdef := id maybe-immediates maybe-type
;; maybe-immediates
;;  :=
;;   | '(' id* ')'
;; maybe-type
;;  :=
;;   | ':' maybe-typevardefs types '->' types
;; maybe-typevardefs
;;  :=
;;   | 'forall' id+
;; types
;;   := '(' id* ')'
(define-instructions
  ;; Control instructions
  [unreachable]

  [nop : [] -> []]

  [block (type code)]
  [loop  (type code)]
  [if    (type then-code else-code)]

  [br       (lbl)]
  [br_if    (lbl)]
  [br_table (from to)]

  [return]
  [call          (idx)]
  [call_indirect (idx tableidx)]

  ;; Parametric instructions
  [drop   : forall t [t      ] -> [   ]]
  [select : forall t [t t i32] -> [i32]]

  ;; Variable instructions
  [local.get  (idx) : forall t [ ] -> [t]]
  [local.set  (idx) : forall t [t] -> [ ]]
  [local.tee  (idx) : forall t [t] -> [t]]
  [global.get (idx) : forall t [ ] -> [t]]
  [global.set (idx) : forall t [t] -> [t]]

  ;; Memory instructions
  [i32.load     (align offset) : [   ] -> [i32]]
  [i64.load     (align offset) : [   ] -> [i64]]
  [f32.load     (align offset) : [   ] -> [f32]]
  [f64.load     (align offset) : [   ] -> [f64]]
  [i32.load8_s  (align offset) : [   ] -> [i32]]
  [i32.load8_u  (align offset) : [   ] -> [i32]]
  [i32.load16_s (align offset) : [   ] -> [i32]]
  [i32.load16_u (align offset) : [   ] -> [i32]]
  [i64.load8_s  (align offset) : [   ] -> [i64]]
  [i64.load8_u  (align offset) : [   ] -> [i64]]
  [i64.load16_s (align offset) : [   ] -> [i64]]
  [i64.load16_u (align offset) : [   ] -> [i64]]
  [i64.load32_s (align offset) : [   ] -> [i64]]
  [i64.load32_u (align offset) : [   ] -> [i64]]
  [i32.store    (align offset) : [i32] -> [   ]]
  [i64.store    (align offset) : [i64] -> [   ]]
  [f32.store    (align offset) : [f32] -> [   ]]
  [f64.store    (align offset) : [f64] -> [   ]]
  [i32.store8   (align offset) : [i32] -> [   ]]
  [i32.store16  (align offset) : [i32] -> [   ]]
  [i64.store8   (align offset) : [i64] -> [   ]]
  [i64.store16  (align offset) : [i64] -> [   ]]
  [i64.store32  (align offset) : [i64] -> [   ]]

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
  [i64.eq   : [i64 i64] -> [i64]]
  [i64.ne   : [i64 i64] -> [i64]]
  [i64.lt_s : [i64 i64] -> [i64]]
  [i64.lt_u : [i64 i64] -> [i64]]
  [i64.gt_s : [i64 i64] -> [i64]]
  [i64.gt_u : [i64 i64] -> [i64]]
  [i64.le_s : [i64 i64] -> [i64]]
  [i64.le_u : [i64 i64] -> [i64]]
  [i64.ge_s : [i64 i64] -> [i64]]
  [i64.ge_u : [i64 i64] -> [i64]]

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
  [custom-section (name data)]
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
 make-empty-mod
 mod-add-section!)

(struct mod (customs types imports functions tables memories globals exports start elements codes datas)
  #:transparent
  #:mutable)

(define-syntax-rule (define-mod-section-adder id (section-type accessor setter) ...)
  (define (id m s)
    (match s
      [(section-type v)
       (define existing (accessor m))
       (when existing
         (raise-wasm-read-error "duplicate section~n  at: ~.s~n  existing: ~.s" s existing))
       (setter m v)] ...)))

(define (make-empty-mod)
  (mod (make-hash) #f #f #f #f #f #f #f #f #f #f #f))

(define-mod-section-adder mod-add-section-once!
  [type-section mod-types set-mod-types!]
  [import-section mod-imports set-mod-imports!]
  [function-section mod-functions set-mod-functions!]
  [table-section mod-tables set-mod-tables!]
  [memory-section mod-memories set-mod-memories!]
  [global-section mod-globals set-mod-globals!]
  [export-section mod-exports set-mod-exports!]
  [start-section mod-start set-mod-start!]
  [element-section mod-elements set-mod-elements!]
  [code-section mod-codes set-mod-codes!]
  [data-section mod-datas set-mod-datas!])

(define (mod-add-section! m s)
  (match s
    [(custom-section name data)
     (hash-set! (mod-customs m) name data)]

    [_
     (mod-add-section-once! m s)]))
