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

(require
  (only-in fexpress/proof-of-concept fexpress-eval-in-base-env))

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