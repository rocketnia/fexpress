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
(require (only-in racket/generic define-generics))
(require (only-in racket/hash hash-union))
(require (only-in racket/syntax format-symbol))


(provide
  (contract-out
    [fexpress-eval-in-base-env (-> any/c any/c)]))

; TODO: Reorganize this code. It's pretty messy.


(define-namespace-anchor here)


(define-generics fexpr
  (fexpr-macroexpand env cont op-var fexpr args)
  (fexpr-apply env cont fexpr args))

(define-generics continuation-expr
  (continuation-expr-continue-compile continuation-expr val-compiled)
  (continuation-expr-continue-eval continuation-expr val-symbolic))

; Positive types.
(define-generics type+
  (type+-continue-compile type+ val-compiled)
  (type+-continue-eval type+ val-symbolic))

(struct any-value/t+ () #:transparent
  #:methods gen:type+
  [(define (type+-continue-compile type+ val-compiled)
     val-compiled)
   (define (type+-continue-eval type+ val-symbolic)
     val-symbolic)])

; Negative types.
(define-generics type_
  (type_-eval type_))

(struct specific-value/t_ (value) #:transparent
  #:methods gen:type_
  [(define (type_-eval type_)
     (match-define (specific-value/t_ value) type_)
     value)])

(struct local-value/t_ () #:transparent
  #:methods gen:type_
  [(define (type_-eval type_)
     (error "Tried to evaluate something that represented a local variable during compilation. This may be an internal bug in the Fexpress proof of concept."))])

(struct symbolic (type_ compilation-result) #:transparent)

(define (symbolic-get-value val-symbolic)
  (match-define (symbolic type_ _) val-symbolic)
  (type_-eval type_))

(struct done/ce (type+) #:transparent
  #:methods gen:continuation-expr
  [(define (continuation-expr-continue-compile cont val-compiled)
     (match-define (done/ce type+) cont)
     (type+-continue-compile type+ val-compiled))
   (define (continuation-expr-continue-eval cont val-symbolic)
     (match-define (done/ce type+) cont)
     (type+-continue-eval type+ val-symbolic))])

(struct apply/ce (env args next) #:transparent
  #:methods gen:continuation-expr
  [(define (continuation-expr-continue-compile cont val-compiled)
     (match-define (apply/ce env args next) cont)
     (match-define (compilation-result _ free-vars op-compiled)
       val-compiled)
     (continuation-expr-continue-compile next
       (compilation-result #t free-vars
         ; TODO LANGUAGE: We probably want to pass a better
         ; continuation here.
         ; TODO LANGUAGE: Hmm, the `env` we pass here should probably
         ; depend on the `env` field of the `apply/ce`.
         `(,#'symbolic-get-value
            (,#'fexpress-apply env
                               (,#'done/ce (,#'any-value/t+))
                               ,op-compiled
                               (,#'quote ,args))))))
   (define (continuation-expr-continue-eval cont val-symbolic)
     (match-define (apply/ce env args next) cont)
     (fexpress-apply env next (symbolic-get-value val-symbolic)
                     args))])

(struct makeshift-fexpr (macroexpand apply) #:transparent
  #:methods gen:fexpr
  [(define (fexpr-macroexpand env cont op-var op-val args)
     (match-define (makeshift-fexpr macroexpand apply) op-val)
     (macroexpand env cont op-var args))
   (define (fexpr-apply env cont op args)
     (match-define (makeshift-fexpr macroexpand apply) op)
     (apply env cont args))])

(define (literal? v)
  (exact-integer? v))

; TODO LANGUAGE: See if we should keep using `#f` in place of a
; missing compilation result like this. We only do this in results of
; evaluation, where it's the expression that's the important part
; anyway. We'll probably need to change it once we have fexprs whose
; macroexpansion behavior relies on being able to insert references to
; themselves into the code at run time. By then, perhaps
; `fexpress-eval` and `fexpress-compile` will have been completely
; merged somehow, making this moot.
(define (not-actually-symbolic value)
  (symbolic (specific-value/t_ value) #f))

(define (fexpress-eval env cont expr)
  (match expr
    [`(,op-expr . ,args)
     (fexpress-eval env (apply/ce env args cont) op-expr)]
    [(? symbol? var)
     (continuation-expr-continue-eval cont (environment-get env var))]
    [(? literal? val)
     (continuation-expr-continue-eval cont
       (not-actually-symbolic val))]
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
     (continuation-expr-continue-eval cont
       (not-actually-symbolic
         (apply op
           (for/list ([arg (in-list args)])
             (symbolic-get-value
               (fexpress-eval env (done/ce (any-value/t+)) arg))))))]
    [#t (error "Uncallable value")]))

(struct compilation-result (depends-on-env? free-vars expr)
  #:transparent)

(define (format-local-symbol sym)
  (format-symbol "-~a" sym))

(define (local-compilation-result-already-formatted var formatted-var)
  (compilation-result #f (hash var #t) formatted-var))

(define (local-compilation-result var)
  (local-compilation-result-already-formatted
    var
    (format-local-symbol var)))

(define (gen-local-compilation-result var formatted-var)
  `(.#'local-compilation-result-already-formatted
     (,#'quote ,var)
     (,#'quote ,formatted-var)))

(define (fexpress-fail-to-compile cont expr)
  (continuation-expr-continue-compile cont
    (compilation-result #t (hash)
      `(,#'symbolic-get-value
         (,#'fexpress-eval
           env (,#'done/ce (,#'any-value/t+)) (,#'quote ,expr))))))

; TODO LANGUAGE: We only call this in one place. See if we should
; inline it.
(define (fexpress-macroexpand env cont op-var op-symbolic args)
  ; TODO LANGUAGE: We shouldn't really be getting the value here. We
  ; should invoke the negative type's own macroexpansion behavior.
  (define op-val (symbolic-get-value op-symbolic))
  (cond
    [(fexpr? op-val) (fexpr-macroexpand env cont op-var op-val args)]
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
          (continuation-expr-continue-compile cont
            (compilation-result depends-on-env?
                                (hash-set free-vars op-var #t)
                                `(,#'#%app
                                   ,(format-local-symbol op-var)
                                   ,@(reverse rev-compiled-args))))]
         [(cons arg args)
          (match-define
            (compilation-result
              arg-depends-on-env? arg-free-vars compiled-arg)
            (fexpress-compile env (done/ce (any-value/t+)) arg))
          (next (or depends-on-env? arg-depends-on-env?)
                (hash-union free-vars arg-free-vars
                            #:combine (match-lambda**
                                        [(#t #t) #t]))
                (cons compiled-arg rev-compiled-args)
                args)]))]
    [#t (error "Uncallable value")]))

(define (fexpress-compile env cont expr)
  (match expr
    [`(,op-expr . ,args)
     (cond
       [(not (symbol? op-expr))
        (fexpress-compile env (apply/ce env args cont) op-expr)]
       [#t
        (define op-symbolic (environment-get env op-expr))
        (or
          (fexpress-macroexpand env cont op-expr op-symbolic args)
          (fexpress-fail-to-compile cont expr))])]
    [(? symbol? var)
     (match-define (symbolic _ var-compiled)
       (environment-get env var))
     (continuation-expr-continue-compile cont var-compiled)]
    [(? literal? val)
     (continuation-expr-continue-compile cont
       (compilation-result #f (hash) `(,#'#%datum . ,val)))]
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
    #;macroexpand
    (lambda (env cont op-var args)
      #f)
    #;apply
    (lambda (env cont args)
      (match-define (parsed-lambda-args n arg-vars body)
        (parse-lambda-args args))
      (continuation-expr-continue-eval cont
        (not-actually-symbolic
          (lambda arg-values
            (unless (equal? n (length arg-values))
              (error "ilambda: wrong number of arguments at call time"))
            (define body-env
              (for/fold ([env env])
                        ([arg-var (in-list arg-vars)]
                        [arg-value (in-list arg-values)])
                (hash-set env arg-var
                  (symbolic (specific-value/t_ arg-value)
                            (local-compilation-result arg-var)))))
            (symbolic-get-value
              (fexpress-eval body-env (done/ce (any-value/t+))
                             body))))))))

(define (compile-clambda env cont args)
  (match-define (parsed-lambda-args n arg-vars body)
    (parse-lambda-args args))
  (define body-env
    (for/fold ([env env])
              ([arg-var (in-list arg-vars)])
      (hash-set env arg-var
        ; TODO LANGUAGE: Make the negative types here depend on
        ; `cont`.
        (symbolic (local-value/t_)
                  (local-compilation-result arg-var)))))
  (match-define
    (compilation-result depends-on-env? body-free-vars body-compiled)
    ; TODO LANGUAGE: Make the continuation here depend on `cont`.
    (fexpress-compile body-env (done/ce (any-value/t+)) body))
  (define body-with-env-compiled
    (if depends-on-env?
      `(,#'let
         ([env
           (,#'hash-set* env
             ,@(append*
                 (for/list ([arg-var (in-list arg-vars)])
                   (define local-arg-var
                     (format-local-symbol arg-var))
                   `(',arg-var
                      (,#'symbolic
                        (,#'specific-value/t_ ,local-arg-var)
                        ,(gen-local-compilation-result
                           arg-var
                           local-arg-var))))))])
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
    (lambda (env cont op-var args)
      (continuation-expr-continue-compile cont
        (compile-clambda env cont args)))
    #;apply
    (lambda (env cont args)
      (match-define
        (compilation-result depends-on-env? free-vars lambda-compiled)
        (compile-clambda env cont args))
      (define free-vars-list (hash-keys free-vars))
      (define local-free-vars-list
        (for/list ([free-var (in-list free-vars-list)])
          (format-local-symbol free-var)))
      (define lambda-maker-compiled
        `(,#'lambda (env ,@local-free-vars-list)
           ,lambda-compiled))
      ; TODO: Figure out a better way to make these conditional than
      ; commenting them out.
;      (displayln "about to eval")
;      (pretty-print (syntax->datum (datum->syntax #f lambda-maker-compiled)))
      (define lambda-maker
        (eval lambda-maker-compiled
              (namespace-anchor->namespace here)))
      (continuation-expr-continue-eval cont
        (not-actually-symbolic
          (apply lambda-maker
            (for/fold ([lambda-maker-env env])
                      ([free-var (in-list free-vars-list)]
                      [local-free-var (in-list local-free-vars-list)])
              (match-define (symbolic existing-type_ existing-compiled)
                (hash-ref env free-var
                  (lambda ()
                    (error "Internal error in the Fexpress proof of concept"))))
              (hash-set lambda-maker-env free-var
                (symbolic existing-type_
                          (local-compilation-result-already-formatted
                            free-var local-free-var))))
            (for/list ([free-var (in-list free-vars-list)])
              (symbolic-get-value
                (environment-get env free-var)))))))))

(define (fexpress-make-base-env)
  (define naive-env
    (hash 'symbolic-get-value symbolic-get-value
          'eval fexpress-eval
          'done/ce done/ce
          'any-value/t+ any-value/t+
          'make-base-env fexpress-make-base-env
          'ilambda fexpress-ilambda
          'clambda fexpress-clambda
          '+ +
          '* *
          'app (lambda (op . args) (apply op args))))
  (for/hash ([(var val) (in-hash naive-env)])
    (values var
            (symbolic (specific-value/t_ val)
                      (local-compilation-result var)))))

(define (fexpress-eval-in-base-env expr)
  (symbolic-get-value
    (fexpress-eval (fexpress-make-base-env) (done/ce (any-value/t+))
                   expr)))
