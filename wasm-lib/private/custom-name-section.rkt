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

(define (read-name-section! in buf)
  (custom-section
   (let loop ([module-name #f]
              [function-names (hash)]
              [local-names (hash)])
     (match (read-byte in)
       [(? eof-object?) (name-section module-name function-names local-names)]
       [0 (loop (read-module-name! in buf) function-names local-names)]
       [1 (loop module-name (read-name-map! in buf) local-names)]
       [2 (loop module-name function-names (read-indirect-name-map! in buf))]
       [s (raise-wasm-read-error "unexpected section id while reading name section: ~a" s)]))))

(define (read-module-name! in buf)
  (skip-len! in buf)
  (read-name! in buf))

(define (read-name-map! in buf)
  (skip-len! in buf)
  (for/hash ([_ (in-range (read-u32! in buf))])
    (values (read-u32! in buf) (read-name! in buf))))

(define (read-indirect-name-map! in buf)
  (skip-len! in buf)
  (for/hash ([_ (in-range (read-u32! in buf))])
    (values (read-u32! in buf) (read-name-map! in buf))))
