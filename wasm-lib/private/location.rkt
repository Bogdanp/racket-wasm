#lang racket/base

(provide
 (struct-out loc)
 (struct-out loc-unknown))

(struct loc (source position))
(struct loc-unknown (source))
