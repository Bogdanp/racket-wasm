#lang info

(define license 'BSD-3-Clause)
(define collection "wasm")
(define version "0.1")
(define deps '("base"
               "data-lib"
               "threading-lib"))
(define build-deps '())
(define pre-install-collection "private/lib/install.rkt")
(define compile-omit-files '("private/lib/install.rkt"))
