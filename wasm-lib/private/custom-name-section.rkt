#lang racket/base

(require racket/match
         "binary-read.rkt"
         "core.rkt"
         "error.rkt")

(provide
 (struct-out name-section)
 read-name-section!)

(struct name-section
  (module-name
   function-names
   local-names)
  #:transparent)

(define (read-name-section! buf in)
  (custom-section
   (let loop ([module-name #f]
              [function-names (hash)]
              [local-names (hash)])
     (match (read-byte in)
       [(? eof-object?) (name-section module-name function-names local-names)]
       [0 (loop (read-module-name! buf in) function-names local-names)]
       [1 (loop module-name (read-name-map! buf in) local-names)]
       [2 (loop module-name function-names (read-indirect-name-map! buf in))]
       [s (raise-wasm-read-error "unexpected section id while reading name section: ~a" s)]))))

(define (read-module-name! buf in)
  (skip-len! buf in)
  (read-name! buf in))

(define (read-name-map! buf in)
  (skip-len! buf in)
  (for/hash ([_ (in-range (read-u32! buf in))])
    (values (read-u32! buf in) (read-name! buf in))))

(define (read-indirect-name-map! buf in)
  (skip-len! buf in)
  (for/hash ([_ (in-range (read-u32! buf in))])
    (values (read-u32! buf in) (read-name-map! buf in))))
