#lang racket/base

(provide
 exn:fail:wasm?
 exn:fail:wasm:exec?
 exn:fail:wasm:exec:trap?
 exn:fail:wasm:read?
 trap
 raise-wasm-exec-error
 raise-wasm-read-error)

(struct exn:fail:wasm exn:fail ())
(struct exn:fail:wasm:exec exn:fail:wasm ())
(struct exn:fail:wasm:exec:trap exn:fail:wasm:exec ())
(struct exn:fail:wasm:read exn:fail:wasm ())

(define (trap message . args)
  (raise (exn:fail:wasm:exec:trap
          (apply format message args)
          (current-continuation-marks))))

(define (raise-wasm-exec-error message . args)
  (raise (exn:fail:wasm:exec
          (apply format message args)
          (current-continuation-marks))))

(define (raise-wasm-read-error message . args)
  (raise (exn:fail:wasm:read
          (apply format message args)
          (current-continuation-marks))))
