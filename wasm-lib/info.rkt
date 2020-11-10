#lang info

(define collection "wasm")
(define version "0.0.0")
(define deps '("base"
               "data-lib"
               "ralist"
               "threading-lib"))
(define build-deps '())
(define pre-install-collection "private/lib/install.rkt")
(define compile-omit-files '("private/lib/install.rkt"))
