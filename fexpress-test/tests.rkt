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


(require (only-in data/queue enqueue! make-queue queue->list))
(require (only-in racket/match match-define))

(require (only-in rackunit check-equal?))

(require fexpress/proof-of-concept)

; (We provide nothing from this module.)


(define (logging-for-test-fn body)
  (define log (make-queue))
  (define result
    (parameterize ([current-fexpress-logger
                    (lambda (msg) (enqueue! log msg))])
      (body)))
  (list (queue->list log) result))

(define-syntax-rule (logging-for-test body)
  (logging-for-test-fn (lambda () body)))

(define test-env
  (env-of-specific-values
    (hash 'the fexpress-the
          'ilambda fexpress-ilambda
          'clambda fexpress-clambda
          'funcall (lambda (f . args) (apply f args))
          '+ +
          '* *)))


; NOTE: This example is in the docs.
(check-equal?
  (logging-for-test
    (fexpress-eval test-env
      '(+ 1 2)))
  (list '() 3))

; NOTE: This example is in the docs.
(check-equal?
  (logging-for-test
    (fexpress-eval test-env
      '((ilambda (x y) (+ x y 3)) 1 2)))
  (list '() 6))

; NOTE: This example is in the docs.
(check-equal?
  (logging-for-test
    (fexpress-eval test-env
      '((clambda (x y) (+ x y 3)) 1 2)))
  (list
    '(("Evaluating Racket code:"
       (lambda (env -+)
         (lambda (-x -y) (#%app -+ -x -y (#%datum . 3))))))
    6))

; NOTE: This example is in the docs.
(check-equal?
  (logging-for-test
    (fexpress-eval test-env
      '(funcall
         (clambda (square)
           (funcall
             (clambda (double)
               (funcall double
                 (funcall double
                   (+ (funcall square 3) (funcall square 4)))))
             (clambda (x) (+ x x))))
         (clambda (x) (* x x)))))
  (list
    '(("Evaluating Racket code:"
       (lambda (env -funcall -+)
         (lambda (-square)
           (#%app -funcall
             (lambda (-double)
               (#%app -funcall -double
                 (#%app -funcall -double
                   (#%app -+
                     (#%app -funcall -square (#%datum . 3))
                     (#%app -funcall -square (#%datum . 4))))))
             (lambda (-x) (#%app -+ -x -x))))))
      ("Evaluating Racket code:"
       (lambda (env -*) (lambda (-x) (#%app -* -x -x)))))
    100))

(check-equal?
  (fexpress-eval test-env
    '(((clambda (x y) (clambda (z) (+ x y z))) 1 2) 3))
  6)


; NOTE: This example is in the docs.

(match-define (list my-compose-log my-compose)
  (logging-for-test
    (fexpress-eval test-env
      ; This should evaluate to a curried composition function.
      `(the ,(->/t_ (list (non-fexpr-value/t+))
               (->/t_ (list (non-fexpr-value/t+))
                 (any-value/t_)))
         (clambda (f)
           (clambda (g)
             (clambda (x)
               (f (g x)))))))))

(check-equal? my-compose-log
  '(("Evaluating Racket code:"
     (lambda (env)
       (lambda (-f)
         (lambda (-g) (lambda (-x) (#%app -f (#%app -g -x))))))))
  "Using `fexpress-the` allows certain Lisp-1-style code to be efficient")

(check-equal?
  (logging-for-test (((my-compose sqrt) add1) 8))
  (list '() 3)
  "Using `fexpress-the` allows certain Lisp-1-style code to not reenter the interpreter")


; NOTE: This example is in the docs.

(match-define (list my-less-typed-compose-log my-less-typed-compose)
  (logging-for-test
    (fexpress-eval test-env
      `(the ,(->/t_ (list (non-fexpr-value/t+))
               (->/t_ (list (any-value/t+))
                 (any-value/t_)))
         (clambda (f)
           (clambda (g)
             (clambda (x)
               (f (g x)))))))))

(check-equal? my-less-typed-compose-log
  '(("Evaluating Racket code:"
     (lambda (env)
       (lambda (-f)
         (let ([env
                (hash-set* env 'f
                  (at-variable/t+ 'f (specific-value/t+ -f)))])
           (lambda (-g)
             (let ([env
                    (hash-set* env 'g
                      (at-variable/t+ 'g (specific-value/t+ -g)))])
               (lambda (-x)
                 (let ([env
                        (hash-set* env 'x
                          (at-variable/t+ 'x
                            (specific-value/t+ -x)))])
                   (#%app -f
                     (begin
                       ((current-fexpress-logger)
                        "Reentering the interpreter")
                       (type+-eval
                         (type+-continue-eval/t+ env
                           (apply/ce '(x) (done/ce (any-value/t_)))
                           (specific-value/t+ -g))))))))))))))
  "Using `fexpress-the` with a less specific type admits fewer optimizations")

(check-equal?
  (logging-for-test (((my-less-typed-compose sqrt) add1) 8))
  (list '("Reentering the interpreter") 3)
  "Using `fexpress-the` with a less specific type causes the code to reenter the interpreter")


; NOTE: This example is in the docs.

(match-define (list my-untyped-compose-log my-untyped-compose)
  (logging-for-test
    (fexpress-eval test-env
      `(clambda (f)
         (clambda (g)
           (clambda (x)
             (f (g x))))))))

(check-equal? my-untyped-compose-log
  '(("Evaluating Racket code:"
     (lambda (env)
       (lambda (-f)
         (let ([env
                (hash-set* env 'f
                  (at-variable/t+ 'f (specific-value/t+ -f)))])
           (lambda (-g)
             (let ([env
                    (hash-set* env 'g
                      (at-variable/t+ 'g (specific-value/t+ -g)))])
               (lambda (-x)
                 (let ([env
                        (hash-set* env 'x
                          (at-variable/t+ 'x
                            (specific-value/t+ -x)))])
                   (begin
                     ((current-fexpress-logger)
                      "Reentering the interpreter")
                     (type+-eval
                       (type+-continue-eval/t+ env
                         (apply/ce '((g x)) (done/ce (any-value/t_)))
                         (specific-value/t+ -f)))))))))))))
  "Opting not to use `fexpress-the` admits fewer optimizations")

(check-equal?
  (logging-for-test (((my-untyped-compose sqrt) add1) 8))
  (list '("Reentering the interpreter") 3)
  "Opting not to use `fexpress-the` causes the code to reenter the interpreter")
