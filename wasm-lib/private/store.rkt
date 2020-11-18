#lang racket/base

(require racket/match
         racket/vector
         threading
         "core.rkt"
         "error.rkt"
         "memory.rkt")

(provide
 (struct-out externfunc)
 (struct-out localfunc)
 (struct-out store)
 make-store)

(struct externfunc (type f) #:transparent)
(struct localfunc (type code) #:transparent)

(struct store (functions table memory globals)
  #:transparent)

(define (make-store m links)
  (define types (mod-types m))
  (define (lookup what mod name)
    (~> links
        (hash-ref mod  (lambda () (trap "module ~a not present in links" mod)))
        (hash-ref name (lambda () (trap "~a ~a not present in module ~a" what name mod)))))
  (define s
    (for/fold ([functions null]
               [table #f]
               [memory #f]
               [globals null]
               #:result (let ([functions (list->vector (reverse functions))]
                              [globals   (list->vector (reverse globals))])
                          (store functions table memory globals)))
              ([imp (in-vector (mod-imports m))])
      (match imp
        [(import mod name (typeidx idx))
         (define func (externfunc (vector-ref types idx) (lookup "function" mod name)))
         (values (cons func functions) table memory globals)]
        [(import mod name (? tabletype?))
         (values functions (lookup "table" mod name) memory globals)]
        [(import mod name (? memtype?))
         (values functions table (lookup "memory" mod name) globals)]
        [(import mod name (? globaltype?))
         (values functions table memory (lookup "global" mod name))])))
  (~> s
      (store-add-table m)
      (store-add-memory m)
      (store-add-data m)
      (store-add-functions m)
      (store-add-elements m)
      (store-add-globals m)))

(define (store-add-table s m)
  (match (mod-tables m)
    [(vector) s]
    [(vector (tabletype _ (limits min-size max-size)))
     (struct-copy store s [table (make-vector (or max-size min-size))])]))

(define (store-add-memory s m)
  (match (mod-memories m)
    [(vector) s]
    [(vector (memtype (limits min-pages max-pages)))
     (struct-copy store s [memory (make-memory min-pages max-pages)])]))

(define (store-add-data s m)
  (begin0 s
    (for ([d (in-vector (mod-datas m))])
      (match-define (data _ (vector (instr:i32.const _ offset)) bs) d)
      (memory-store! (store-memory s) offset bs))))

(define (store-add-elements s m)
  (define table (store-table s))
  (begin0 s
    (for ([e (in-vector (mod-elements m))])
      (match-define (element _ (vector (instr:i32.const _ offset)) init) e)
      (for ([it (in-vector init)]
            [tblidx (in-naturals offset)])
        (match-define (funcidx idx) it)
        (vector-set! table tblidx idx)))))

(define (store-add-functions s m)
  (define types (mod-types m))
  (for/fold ([functions null]
             #:result (let ([functions (list->vector (reverse functions))])
                        (struct-copy store s [functions (vector-append (store-functions s) functions)])))
            ([typeidx (in-vector (mod-functions m))]
             [code (in-vector (mod-codes m))])
    (cons (localfunc (vector-ref types typeidx) code) functions)))

(define (store-add-globals s m)
  (define globals (make-vector (vector-length (mod-globals m))))
  (struct-copy store s [globals (vector-append (store-globals s) globals)]))
