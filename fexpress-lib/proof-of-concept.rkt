#lang racket/base

; fexpress/proof-of-concept
;
; The Fexpress proof-of-concept, a minimalist, compilation-friendly
; fexpr language.

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


(require (only-in racket/contract/base -> any/c contract-out))
(require (only-in racket/list append*))
(require (only-in racket/match match match-define match-lambda**))
; TODO: Figure out a better way to make this conditional than
; commenting it out.
;(require (only-in racket/pretty pretty-print))
(require (only-in racket/generic define/generic define-generics))
(require (only-in racket/hash hash-union))
(require (only-in racket/syntax format-symbol))


(provide
  (contract-out
    [fexpress-eval-in-base-env (-> any/c any/c)]))
; TODO: See if we should provide more things from this module.

; TODO: Reorganize this code. It's pretty messy.


(define-namespace-anchor here)


(define-generics fexpr
  (fexpr-macroexpand macro-env local-env op-var fexpr args)
  (fexpr-apply env cont fexpr args))

(define-generics continuation-expr
  (continuation-expr-continue-eval continuation-expr val))

; Positive types
(define-generics type+
  (type+-continue-eval type+ val))

(struct any-value/t+ () #:transparent
  #:methods gen:type+
  [(define (type+-continue-eval type+ val)
     val)])

(struct continuation-expr-done (type+)
  #:transparent
  #:methods gen:continuation-expr
  [(define (continuation-expr-continue-eval cont val)
     (match-define (continuation-expr-done type+) cont)
     (type+-continue-eval type+ val))])

(struct continuation-expr-apply (env args next)
  #:transparent
  #:methods gen:continuation-expr
  [(define/generic continuation-expr-continue-eval-
     continuation-expr-continue-eval)
   (define (continuation-expr-continue-eval cont val)
     (match-define (continuation-expr-apply apply-env args next) cont)
     (continuation-expr-continue-eval- next
       (fexpress-apply apply-env next val args)))])

(struct makeshift-fexpr (macroexpand apply) #:transparent
  #:methods gen:fexpr
  [(define (fexpr-macroexpand macro-env local-env op-var op-val args)
     (match-define (makeshift-fexpr macroexpand apply) op-val)
     (macroexpand macro-env local-env op-var args))
   (define (fexpr-apply env cont op args)
     (match-define (makeshift-fexpr macroexpand apply) op)
     (apply env cont args))])

(define (literal? v)
  (exact-integer? v))

(define (fexpress-eval env cont expr)
  (match expr
    [`(,op-expr . ,args)
     (fexpress-eval
       env (continuation-expr-apply env args cont) op-expr)]
    [(? symbol? var)
     (continuation-expr-continue-eval cont (environment-get env var))]
    [(? literal? val) (continuation-expr-continue-eval cont val)]
    [_ (error "Unrecognized expression")]))

(define (environment-get env var)
  (hash-ref env var (lambda () (error "Unbound variable"))))

(define (fexpress-apply env cont op args)
  (cond
    [(fexpr? op) (fexpr-apply env cont op args)]
    [(procedure? op)
     (unless (and (list? args)
                  (procedure-arity-includes? op (length args)))
       (error "Wrong number of arguments to a procedure"))
     (apply op
       (for/list ([arg (in-list args)])
         (fexpress-eval env (continuation-expr-done (any-value/t+))
                        arg)))]
    [#t (error "Uncallable value")]))

(struct compilation-result (depends-on-env? free-vars expr))

(define (format-local-symbol sym)
  (format-symbol "-~a" sym))

(define (fexpress-fail-to-compile expr)
  (compilation-result #t (hash)
    `(,#'fexpress-eval env
                       (,#'continuation-expr-done (,#'any-value/t+))
                       ',expr)))

(define (fexpress-macroexpand macro-env local-env op-var op-val args)
  (cond
    [(fexpr? op-val)
     (fexpr-macroexpand macro-env local-env op-var op-val args)]
    [(procedure? op-val)
     (unless (and (list? args)
                  (procedure-arity-includes? op-val (length args)))
       (error "Wrong number of arguments to a procedure"))
     (let next ([depends-on-env? #f]
                [free-vars (hash)]
                [rev-compiled-args (list)]
                [args args])
       (match args
         [(list)
          (compilation-result depends-on-env?
                              (hash-set free-vars op-var #t)
                              `(,#'#%app
                                  ,(format-local-symbol op-var)
                                  ,@(reverse rev-compiled-args)))]
         [(cons arg args)
          (match-define
            (compilation-result
              arg-depends-on-env? arg-free-vars compiled-arg)
            (fexpress-compile macro-env local-env arg))
          (next (or depends-on-env? arg-depends-on-env?)
                (hash-union free-vars arg-free-vars
                            #:combine (match-lambda**
                                        [(#t #t) #t]))
                (cons compiled-arg rev-compiled-args)
                args)]))]
    [#t (error "Uncallable value")]))

(define (fexpress-compile macro-env local-env expr)
  (match expr
    [`(,op-expr . ,args)
     (cond
       [(not (symbol? op-expr))
        (match-define (compilation-result _ free-vars op-compiled)
          (fexpress-compile macro-env local-env op-expr))
        (compilation-result #t free-vars
          ; TODO: We probably want to pass a better continuation here.
          `(,#'fexpress-apply
             env
             (,#'continuation-expr-done (,#'any-value/t+))
             ,op-compiled
             ',args))]
       [(hash-has-key? local-env op-expr)
        (fexpress-fail-to-compile expr)]
       [#t
        (define op-val (environment-get macro-env op-expr))
        (or
          (fexpress-macroexpand
            macro-env local-env op-expr op-val args)
          (fexpress-fail-to-compile expr))])]
    [(? symbol? var)
     (if (hash-has-key? local-env var)
       (compilation-result #f (hash var #t) (format-local-symbol var))
       (begin
         ; NOTE: We call this just for the errors.
         (environment-get macro-env var)
         (compilation-result #f (hash var #t)
           (format-local-symbol var))))]
    [(? literal? val)
     (compilation-result #f (hash) `(,#'#%datum . ,val))]
    [_ (error "Unrecognized expression")]))

(struct parsed-lambda-args (n arg-vars body) #:transparent)

(define (parse-lambda-args args)
  (match args
    [`(,arg-vars ,body)
     (unless (list? arg-vars)
       (error "ilambda: expected the argument list to be a list"))
     (unless (andmap symbol? arg-vars)
       (error "ilambda: expected the argument list to be a list of symbols"))
     (define n (length arg-vars))
     (unless (equal? n (hash-count
                         (for/hash ([arg (in-list arg-vars)])
                           (values arg #t))))
       (error "ilambda: expected the argument list to be a list of mutually unique symbols"))
     (parsed-lambda-args n arg-vars body)]
    [_ (error "ilambda: expected an argument list and a body")]))

; An interpreted lambda. This doesn't attempt to compile the body. It
; evaluates the body each time it's called.
(define fexpress-ilambda
  (makeshift-fexpr
    #;compile
    (lambda (macro-env local-env op-var args)
      #f)
    #;apply
    (lambda (env cont args)
      (match-define (parsed-lambda-args n arg-vars body)
        (parse-lambda-args args))
      (lambda arg-values
        (unless (equal? n (length arg-values))
          (error "ilambda: wrong number of arguments at call time"))
        (define local-env
          (for/fold ([env env])
                    ([arg-var (in-list arg-vars)]
                     [arg-value (in-list arg-values)])
            (hash-set env arg-var arg-value)))
        (fexpress-eval
          local-env (continuation-expr-done (any-value/t+)) body)))))

(define (compile-clambda macro-env local-env args)
  (match-define (parsed-lambda-args n arg-vars body)
    (parse-lambda-args args))
  (define body-local-env
    (for/fold ([body-local-env local-env])
              ([arg-var (in-list arg-vars)])
      (hash-set body-local-env arg-var #t)))
  (match-define
    (compilation-result depends-on-env? body-free-vars body-compiled)
    (fexpress-compile macro-env body-local-env body))
  (define body-with-env-compiled
    (if depends-on-env?
      `(,#'let ([env
                 (,#'hash-set* env
                   ,@(append*
                       (for/list ([arg-var (in-list arg-vars)])
                         (define local-arg-var
                           (format-local-symbol arg-var))
                         `(',arg-var ,local-arg-var))))])
         ,body-compiled)
      body-compiled))
  (define free-vars
    (for/fold ([free-vars body-free-vars])
              ([arg-var (in-list arg-vars)])
      (hash-remove free-vars arg-var)))
  (define lambda-compiled
    `(,#'lambda
       ,(for/list ([arg-var (in-list arg-vars)])
          (format-local-symbol arg-var))
       ,body-with-env-compiled))
  (compilation-result depends-on-env? free-vars lambda-compiled))

; A compiled lambda. This doesn't attempt to compile the body. It
; evaluates the body each time it's called.
(define fexpress-clambda
  (makeshift-fexpr
    #;macroexpand
    (lambda (macro-env local-env op-var args)
      (compile-clambda macro-env local-env args))
    #;apply
    (lambda (env cont args)
      (match-define
        (compilation-result depends-on-env? free-vars lambda-compiled)
        (compile-clambda env (hash) args))
      (define free-vars-list (hash-keys free-vars))
      (define lambda-maker-compiled
        `(,#'lambda
           (
             env
             ,@(for/list ([free-var (in-list free-vars-list)])
                 (format-local-symbol free-var)))
           ,lambda-compiled))
      ; TODO: Figure out a better way to make these conditional than
      ; commenting them out.
;      (displayln "about to eval")
;      (pretty-print (syntax->datum (datum->syntax #f lambda-maker-compiled)))
      (define lambda-maker
        (eval lambda-maker-compiled
              (namespace-anchor->namespace here)))
      (apply lambda-maker env
        (for/list ([free-var (in-list free-vars-list)])
          (environment-get env free-var))))))

(define (fexpress-make-base-env)
  (hash 'eval fexpress-eval
        'continuation-expr-done continuation-expr-done
        'any-value/t+ any-value/t+
        'make-base-env fexpress-make-base-env
        'ilambda fexpress-ilambda
        'clambda fexpress-clambda
        '+ +
        '* *
        'app (lambda (op . args) (apply op args))))

(define (fexpress-eval-in-base-env expr)
  (fexpress-eval (fexpress-make-base-env)
                 (continuation-expr-done (any-value/t+))
                 expr))
