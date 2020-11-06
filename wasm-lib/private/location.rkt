#lang racket/base

(provide
 (struct-out loc)
 port-loc)

(struct loc (source position))

(define (port-loc in)
  (define-values (_line _column pos)
    (port-next-location in))
  (loc (object-name in) pos))
