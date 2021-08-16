#lang racket/base

; fexpress/tests
;
; Unit tests.

;   Copyright 2021 The Fexpress Authors
;
;   Licensed under the Apache License, Version 2.0 (the "License");
;   you may not use this file except in compliance with the License.
;   You may obtain a copy of the License at
;
;       http://www.apache.org/licenses/LICENSE-2.0
;
;   Unless required by applicable law or agreed to in writing,
;   software distributed under the License is distributed on an
;   "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
;   either express or implied. See the License for the specific
;   language governing permissions and limitations under the License.


(require (only-in rackunit check-equal?))

(require fexpress/proof-of-concept)

; (We provide nothing from this module.)


(check-equal?
  (fexpress-eval-in-base-env
    '(+ 1 2))
  3)

(check-equal?
  (fexpress-eval-in-base-env
    '((ilambda (x y) (+ x y 3)) 1 2))
  6)

(check-equal?
  (fexpress-eval-in-base-env
    '((clambda (x y) (+ x y 3)) 1 2))
  6)

(check-equal?
  (fexpress-eval-in-base-env
    '(app
       (clambda (square)
         (app
           (clambda (double)
             (app double
               (app double (+ (app square 3) (app square 4)))))
           (clambda (x) (+ x x))))
       (clambda (x) (* x x))))
  100)

(check-equal?
  (fexpress-eval-in-base-env
    '(((clambda (x y) (clambda (z) (+ x y z))) 1 2) 3))
  6)

(check-equal?
  (
    (
      (
        (fexpress-eval-in-base-env

          ; This should evaluate to a curried composition function.
          ;
          ; TODO: Make a convincing test that shows that this compiles
          ; down efficiently and that a version without an annotation
          ; as specific as this does not.
          ;
          `(the ,(->/t_ (list (non-fexpr-value/t+))
                   (->/t_ (list (non-fexpr-value/t+))
                     (any-value/t_)))
             (clambda (f)
               (clambda (g)
                 (clambda (x)
                   (f (g x)))))))
        (lambda (x) (+ 2 x)))
      (lambda (x) (+ 3 x)))
    1)
  6)
