#lang racket/base

(require racket/file
         racket/match
         racket/path
         rackunit
         wasm/private/binary
         wasm/private/validation)

(define here
  (simplify-path (build-path (syntax-source #'here) 'up)))

(define (wasm-path? p)
  (equal? (path-get-extension p) #".wasm"))

(define (check-file path)
  (test-case (format "validate ~a" path)
    (define out-path (path-replace-extension path #".out"))
    (define m (call-with-input-file path read-wasm))
    (define-values (valid? validation-error)
      (mod-valid? m))
    (cond
      [(file-exists? out-path)
       (match-define (cons expected-valid? expected-validation-error)
         (call-with-input-file out-path read))
       (test-case (format "~a valid?" path)
         (check-equal? valid? expected-valid?))
       (test-case (format "~a error message" path)
         (check-equal? validation-error expected-validation-error))]
      [else
       (with-output-to-file out-path
         #:exists 'replace
         (lambda ()
           (write (cons valid? validation-error))))])))

(for ([path (find-files wasm-path? here)])
  (check-file path))
