#lang racket/base

(require (for-syntax racket/base
                     "core.rkt")
         syntax/parse/define)

(provide opcase)

(begin-for-syntax
  (define ns (current-namespace)))

(define-syntax-parser opcase
  #:literals (else)
  [(_ e:expr [opcode-id:id rhs ...] ... [else else-rhs ...])
   #:with (opcode ...) (for/list ([id (in-list (syntax-e #'(opcode-id ...)))])
                         (datum->syntax id (namespace-variable-value (syntax->datum id) #t #f ns)))
   #'(case e
       [(opcode) rhs ...] ...
       [else else-rhs ...])])
