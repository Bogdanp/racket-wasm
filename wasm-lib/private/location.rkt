#lang racket/base

(provide
 (struct-out loc)
 (struct-out loc-unknown)
 track-source-location?
 port-loc)

(define track-source-location?
  (make-parameter #f))

(struct loc (source position))
(struct loc-unknown (source))

(define (port-loc in)
  (cond
    [(track-source-location?)
     (define-values (_line _column pos)
       (port-next-location in))
     (loc (object-name in) pos)]

    [else
     (loc-unknown (object-name in))]))
