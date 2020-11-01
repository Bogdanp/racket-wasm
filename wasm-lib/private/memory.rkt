#lang racket/base

(require (for-syntax racket/base)
         data/gvector
         racket/require
         (filtered-in
          (lambda (name)
            (and (regexp-match? #rx"^unsafe-fx" name)
                 (regexp-replace #rx"^unsafe-" name "")))
          racket/unsafe/ops)
         "error.rkt")

(provide
 make-memory
 memory?
 memory-size
 memory-grow!
 memory-store!
 memory-load!)

(define page-size 65536)

(struct memory (pages max-pages [end #:mutable]))

(define (make-page)
  (make-bytes page-size 0))

(define (make-memory [min-pages 1] [max-pages #f])
  (define pages
    (for/gvector ([_ (in-range min-pages)])
      (make-page)))
  (memory pages max-pages (* min-pages page-size)))

(define (memory-size m)
  (gvector-count (memory-pages m)))

(define (memory-grow! m amt)
  (define pages (memory-pages m))
  (define new-size (fx+ amt (gvector-count pages)))
  (define max-pages (memory-max-pages m))
  (when (and max-pages (> new-size max-pages))
    (error 'memory-grow "grow exceeds max size"))
  (define added-pages
    (for/list ([_ (in-range amt)])
      (make-page)))
  (set-memory-end! m (fx* new-size page-size))
  (apply gvector-add! pages added-pages))

(define (memory-store! m start-addr buf [size (bytes-length buf)])
  (define end-addr (fx+ start-addr size))
  (when (fx> end-addr (memory-end m))
    (trap "memory range [0x~a..0x~a] exceeds size of memory"
          (number->string start-addr 16)
          (number->string end-addr 16)))
  (define pages (memory-pages m))
  (define page-idx (fxquotient start-addr page-size))
  (define page (gvector-ref pages page-idx))
  (let loop ([pos 0]
             [addr start-addr]
             [remaining size])
    (unless (fx= 0 remaining)
      (define new-page-idx (fxquotient addr page-size))
      (when (fx> new-page-idx page-idx)
        (set! page-idx new-page-idx)
        (set! page (gvector-ref pages new-page-idx)))
      (define offset (fxremainder addr page-size))
      (bytes-set! page offset (bytes-ref buf pos))
      (loop (fx+ pos 1)
            (fx+ addr 1)
            (fx- remaining 1)))))

(define (memory-load! m start-addr addr [size (bytes-length start-addr)])
  (define end-addr (fx+ addr size))
  (when (fx> end-addr (memory-end m))
    (trap "memory range [0x~a..0x~a] exceeds size of memory"
          (number->string addr 16)
          (number->string end-addr 16)))
  (define pages (memory-pages m))
  (define page-idx (fxquotient addr page-size))
  (define page (gvector-ref pages page-idx))
  (let loop ([pos 0]
             [addr addr]
             [remaining size])
    (unless (fx= 0 remaining)
      (define new-page-idx (fxquotient addr page-size))
      (when (fx> new-page-idx page-idx)
        (set! page-idx new-page-idx)
        (set! page (gvector-ref pages new-page-idx)))
      (define offset (fxremainder addr page-size))
      (bytes-set! start-addr pos (bytes-ref page offset))
      (loop (fx+ pos 1)
            (fx+ addr 1)
            (fx- remaining 1)))))
