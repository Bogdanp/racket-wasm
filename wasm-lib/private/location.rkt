#lang racket/base

(provide
 (struct-out loc))

(struct loc (source position))
