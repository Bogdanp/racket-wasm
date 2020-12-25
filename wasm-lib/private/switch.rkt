#lang racket/base

(require (for-syntax racket/base
                     racket/syntax)
         syntax/parse/define)

(provide
 switch)

(begin-for-syntax
  (define-syntax-class clause
    (pattern [(lit:expr ...+) e ...+])))

(define-syntax-parser switch
  #:literals (else)
  [(_ e:expr c:clause ... [else else-e ...+])
   (define ids (for/list ([c (in-list (syntax-e #'(c ...)))]
                          [id (in-naturals)])
                 (format-id c "$case~a" id)))
   (with-syntax ([(label ...) ids]
                 [(label+1 ...) (append (cdr ids) (list #'$fallthrough))])
     #'(letrec ([$fallthrough (lambda () else-e ...)]
                [label (lambda () c.e ... (label+1))] ...)
         (case e
           [(c.lit ...) (label)] ...
           [else ($fallthrough)])))])
