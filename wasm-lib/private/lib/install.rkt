#lang racket/base

(require dynext/file
         racket/system)

(provide pre-installer)

(define (pre-installer _collections-top-path this-collection-path)
  (define lib-path (build-path this-collection-path "private" "lib"))
  (define source-path (build-path lib-path "runtime.c"))
  (define output-path (build-path lib-path (append-extension-suffix "runtime")))
  (parameterize ([current-directory lib-path])
    (system* (find-executable-path "clang")
             "-Wall" "-Werror" "-O3" "-fPIC" "-shared"
             "-o" output-path source-path)))
