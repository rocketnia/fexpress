#lang info

(define collection "fexpress")

(define deps (list "base"))
(define build-deps (list "fexpress-lib" "racket-doc" "scribble-lib"))

(define scribblings (list (list "scribblings/fexpress.scrbl" (list))))
