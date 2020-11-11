#lang racket/base

(require dynext/file
         racket/system)

(provide pre-installer)

(define cc
  (for/first ([name '("clang" "gcc" "cc")])
    (find-executable-path name)))

(define (pre-installer _collections-top-path this-collection-path)
  (define lib-path (build-path this-collection-path "private" "lib"))
  (define source-path (build-path lib-path "runtime.c"))
  (define output-path (build-path lib-path (append-extension-suffix "runtime")))
  (parameterize ([current-directory lib-path])
    (system* cc
             "-Wall" "-Werror" "-O3" "-fPIC" "-shared"
             "-o" output-path source-path)))
