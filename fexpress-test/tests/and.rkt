#lang racket/base

; fexpress/tests/and
;
; Unit tests for an example `my-and` operator that works as a Racket
; macro, an Fexpress fexpr, and a procedure depending on how it's
; used.

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


(require (for-syntax racket/base))
(require (for-syntax (only-in syntax/parse expr id syntax-parse)))

(require (only-in data/queue enqueue! make-queue queue->list))
(require (only-in racket/function identity))
(require (only-in racket/hash hash-union))
(require (only-in racket/match match match-lambda**))
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



; The docs mention that languages with pervasive fexprs allow `and` to
; be passed to `map` with some success. It's a reasonable idea to
; disallow this, but it can sometimes look snazzy to allow it. The
; reason it almost makes sense is because `and`, unlike most other
; fexprs, actually resembles a procedure; it's basically a procedure
; with its own custom evaluation strategy.
;
; If we want to achieve some of the punning that allows `and` to work
; with `map` in pervasively fexpr-based languages, we can actually
; achieve most of it in Racket without using Fexpress at all:
;
;   (define (my-and-procedure . args)
;     (andmap identity args))
;  
;   (define-syntax (my-and stx)
;     (syntax-parse stx
;       [_:id #'my-and-procedure]
;       [(_ args:expr ...) #'(and args ...)]))
;
; If `my-and` is used in operator position, it works like `and`. If
; it's used in an expression position, it works like a first-class
; procedure. Of course, as soon as we pass it anywhere as a procedure,
; that procedure carries no memory of what the custom evaluation
; strategy was.
;
; With Fexpress, we can do a little more punning than that, allowing
; `my-and` to work like a Racket macro, an Fexpress fexpr, or a
; procedure. The first-class value carries the fexpr and procedure
; behaviors at the same time, and the fexpr behavior means it still
; has some memory of its custom evaluation strategy, even if there's
; no way to turn it back from a run-time first-class value into a
; compile-time Racket syntax binding.
;
; Calling `my-and` using (my-and ...) from Racket code will always
; call it as either a Racket macro or a procedure. It's only within
; Fexpress code that the fexpr behavior can be invoked.

(define (my-and-procedure . args)
  (andmap identity args))

(struct my-and-fexpr-representation ()
  ; If we're invoking `my-and` as a procedure, we use a dedicated code
  ; path for that.
  #:property prop:procedure
  (lambda (self . args)
    (apply my-and-procedure args))
  #:methods gen:fexpr
  [(define (fexpr-apply/t+ env cont op/t+ op args)
     (define arg-type+-list
       (for/list ([arg (in-list args)])
         (fexpress-eval/t+ env (done/ce (any-value/t_)) arg)))
     (lazy-value/t+
       (lambda ()
         ; If we're interpreting an fexpr call to `my-and`, we
         ; interpret the arguments, short-circuiting as soon as any of
         ; them is true.
         (for/and ([arg/t+ (in-list arg-type+-list)])
           (type+-eval arg/t+)))
       (lambda ()
         ; If we're compiling an fexpr call to `my-and`, we compile
         ; the arguments, and we put them into a Racket `and` form.
         (define arg-compilation-results
           (for/list ([arg/t+ (in-list arg-type+-list)])
             (type+-compile arg/t+)))
         (let next ([depends-on-env? #f]
                    [free-vars (hashalw)]
                    [rev-args-compiled (list)]
                    [arg-compilation-results
                     arg-compilation-results])
           (match arg-compilation-results
             [(list)
              (compilation-result depends-on-env? free-vars
                `(,#'and ,@(reverse rev-args-compiled)))]
             [(cons
                (compilation-result
                  arg-depends-on-env? arg-free-vars arg-compiled)
                arg-compilation-results)
              (next (or depends-on-env? arg-depends-on-env?)
                    (hash-union free-vars arg-free-vars
                                #:combine (match-lambda**
                                            [(#t #t) #t]))
                    (cons arg-compiled rev-args-compiled)
                    arg-compilation-results)])))))])

(define my-and-fexpr (my-and-fexpr-representation))

(define-syntax (my-and stx)
  (syntax-parse stx
    [_:id #'my-and-fexpr]
    ; If we're invoking `my-and` as a Racket macro, we use a dedicated
    ; code path for that.
    [(_ args:expr ...) #'(and args ...)]))


(define test-env
  (env-of-specific-values
    (hashalw
      'clambda fexpress-clambda
      'and my-and
      'get-false (lambda () #f)
      'err (lambda () (error "Shouldn't have called this")))))


(check-equal?
  (let ([mutable-variable 1])
    (define and-result (my-and #f (set! mutable-variable 2)))
    (list mutable-variable and-result))
  (list 1 #f)
  "Using `my-and` as a Racket macro works and does short-circuiting.")

(check-equal?
  (let ([mutable-variable 1])
    (define and-result
      ((car (list my-and)) #f (set! mutable-variable 2)))
    (list mutable-variable and-result))
  (list 2 #f)
  "Using `my-and` as a first-class function works, but it doesn't do short-circuiting.")

(check-equal?
  (let ([mutable-variable 1])
    (define and-result
      (map my-and (list #t #f) (list #f (set! mutable-variable 2))))
    (list mutable-variable and-result))
  (list 2 (list #f #f))
  "Passing `my-and` to something that calls it like a function works. The arguments of that higher-order function are, however, evaluated as usual.")

(check-equal?
  (logging-for-test
    (fexpress-eval test-env
      '(and (get-false) (err))))
  (list '() #f)
  "Interpreting an Fexpress fexpr call to `my-and` works and does short-circuiting.")

(check-equal?
  (logging-for-test
    (fexpress-eval test-env
      '((clambda (x) (and x (err))) (get-false))))
  (list
    '(("Evaluating Racket code:"
       (lambda (env -err) (lambda (-x) (and -x (#%app -err))))))
    #f)
  "Compiling an Fexpress fexpr call to `my-and` works and does short-circuiting.")
