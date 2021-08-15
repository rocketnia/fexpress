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
  (fexpr-continue-eval/t_ env cont fexpr/t_ fexpr))

(define-generics continuation-expr
  (continuation-expr-continue-eval/t_ env continuation-expr val/t_))

; Positive types.
(define-generics type+
  (type+-continue-eval/t_ env type+ val/t_))

(struct any-value/t+ () #:transparent
  #:methods gen:type+
  [(define (type+-continue-eval/t_ env type+ val/t_)
     val/t_)])

; Negative types.
(define-generics type_
  (type_-eval type_)
  (type_-compile type_)
  (at-variable/t_ var type_)
  (type_-continue-eval/t_ env cont type_))

(struct specific-variable-bound-value/t_ (var val) #:transparent
  #:methods gen:type_
  [(define (type_-eval type_)
     (match-define (specific-variable-bound-value/t_ var val) type_)
     val)
   (define (type_-compile type_)
     (match-define (specific-variable-bound-value/t_ var val) type_)
     (local-compilation-result var))
   (define (at-variable/t_ var type_)
     (match-define (specific-variable-bound-value/t_ original-var val)
       type_)
     (specific-variable-bound-value/t_ var val))
   (define (type_-continue-eval/t_ env cont val/t_)
     (match-define (specific-variable-bound-value/t_ var val) val/t_)
     (fexpress-continue-eval/t_ env cont val/t_ val))])

(struct specific-value/t_ (value) #:transparent
  #:methods gen:type_
  [(define (type_-eval type_)
     (match-define (specific-value/t_ value) type_)
     value)
   (define (type_-compile type_)
     (error "Tried to compile the a value level of a negative type that represented a reified first-class value that didn't have a known compiled form. This may be an internal bug in the Fexpress proof of concept."))
   (define (at-variable/t_ var type_)
     (match-define (specific-value/t_ value) type_)
     (specific-variable-bound-value/t_ var value))
   (define (type_-continue-eval/t_ env cont val/t_)
     (match-define (specific-value/t_ value) val/t_)
     (fexpress-continue-eval/t_ env cont val/t_ value))])

(struct unknown-value/t_ (val-compiled) #:transparent
  #:methods gen:type_
  [(define (type_-eval type_)
     (raise-arguments-error 'type_-eval
       "Tried to evaluate the value level of a negative type that represented a run-time value during compilation. This may be an internal bug in the Fexpress proof of concept."
       "negative type" type_))
   (define (type_-compile type_)
     (match-define (unknown-value/t_ val-compiled) type_)
     val-compiled)
   (define (at-variable/t_ var type_)
     (unknown-value/t_ (local-compilation-result var)))
   (define (type_-continue-eval/t_ env cont val/t_)
     (continuation-expr-continue-eval/t_ env cont val/t_))])

(define (const0 result)
  (lambda ()
    result))

(struct lazy-value/t_ (eval compile) #:transparent
  #:methods gen:type_
  [(define (type_-eval type_)
     (match-define (lazy-value/t_ eval compile) type_)
     (eval))
   (define (type_-compile type_)
     (match-define (lazy-value/t_ eval compile) type_)
     (compile))
   (define (at-variable/t_ var type_)
     (match-define (lazy-value/t_ eval compile) type_)
     (lazy-value/t_ eval (const0 (local-compilation-result var))))
   (define (type_-continue-eval/t_ env cont val/t_)
     (continuation-expr-continue-eval/t_ env cont val/t_))])

(struct done/ce (type+) #:transparent
  #:methods gen:continuation-expr
  [(define (continuation-expr-continue-eval/t_ env cont val/t_)
     (match-define (done/ce type+) cont)
     (type+-continue-eval/t_ env type+ val/t_))])

(struct apply/ce (args next) #:transparent
  #:methods gen:continuation-expr
  [(define (continuation-expr-continue-eval/t_ env cont val/t_)
     (match-define (apply/ce args next) cont)
     (type_-continue-eval/t_ env next
       (lazy-value/t_
         (lambda ()
           (type_-eval
             (fexpress-continue-eval/t_
               env
               (apply/ce args (done/ce (any-value/t+)))
               val/t_
               (type_-eval val/t_))))
         (lambda ()
           (match-define (compilation-result _ free-vars op-compiled)
             (type_-compile val/t_))
           (compilation-result #t free-vars

             ; NOTE: Since we're just going to `type_-eval` it anyway,
             ; we don't need anything more than `specific-value/t_`
             ; here. The `val/t_` type may know extra things like how
             ; to compile the value, but we don't need to make any
             ; effort to reify that information here.
             ;
             `(,#'type_-eval
                 (,#'type_-continue-eval/t_
                   env
                   (,#'apply/ce (,#'quote ,args)
                     (,#'done/ce (,#'any-value/t+)))
                   (,#'specific-value/t_ ,op-compiled))))))))])

(struct makeshift-fexpr (continue-eval/t_) #:transparent
  #:methods gen:fexpr
  [(define (fexpr-continue-eval/t_ env cont op/t_ op)
     (match-define (makeshift-fexpr continue-eval/t_) op)
     (continue-eval/t_ env cont op/t_))])

(define (literal? v)
  (exact-integer? v))

(define (fexpress-eval/t_ env cont expr)
  (match expr
    [`(,op-expr . ,args)
     (fexpress-eval/t_ env (apply/ce args cont) op-expr)]
    [(? symbol? var)
     (type_-continue-eval/t_ env cont (environment-get/t_ env var))]
    [(? literal? val)
     (type_-continue-eval/t_ env cont
       ; TODO LAZY: Rather than just using `lazy-value/t_` here, we
       ; could also specialize `type_-continue-eval/t_` to raise an
       ; error if a literal is used in functional position.
       (lazy-value/t_
         (const0 val)
         (const0
           (compilation-result #f (hash) `(,#'#%datum . ,val)))))]
    [_ (error "Unrecognized expression")]))

(define (environment-get/t_ env var)
  (hash-ref env var (lambda () (error "Unbound variable"))))

(define (fexpress-continue-eval/t_ env cont val/t_ val)
  (cond
    [(fexpr? val) (fexpr-continue-eval/t_ env cont val/t_ val)]
    [#t
     ; TODO CLEANUP: Consider moving this branch to a
     ; `continuation-expr-continue-eval-value/t_` method.
     (match cont
       [(apply/ce args cont)
        (cond
          [(procedure? val)
           (unless (and (list? args)
                        (procedure-arity-includes? val (length args)))
             (error "Wrong number of arguments to a procedure"))
           (define arg-type_-list
             (for/list ([arg (in-list args)])
               (fexpress-eval/t_ env (done/ce (any-value/t+)) arg)))
           (type_-continue-eval/t_ env cont

             ; TODO LAZY: Rather than just using `lazy-value/t_` here,
             ; we could also specialize `type_-continue-eval/t_` to
             ; treat certain procedures as being guaranteed not to
             ; return an fexpr. That could let us use those procedure
             ; calls in  functional position without inhibiting
             ; compilation.
             ;
             (lazy-value/t_
               (lambda ()
                 (apply val
                   (for/list ([arg/t_ (in-list arg-type_-list)])
                     (type_-eval arg/t_))))
               (lambda ()
                 (define op-compilation-result (type_-compile val/t_))
                 (define arg-compilation-results
                   (for/list ([arg/t_ (in-list arg-type_-list)])
                     (type_-compile arg/t_)))
                 (match-define
                   (compilation-result
                     op-depends-on-env? op-free-vars op-compiled)
                   op-compilation-result)
                 (let next ([depends-on-env? op-depends-on-env?]
                            [free-vars op-free-vars]
                            [rev-compiled-args (list)]
                            [arg-compilation-results
                             arg-compilation-results])
                   (match arg-compilation-results
                     [(list)
                      (compilation-result depends-on-env? free-vars
                        `(,#'#%app ,op-compiled
                                   ,@(reverse rev-compiled-args)))]
                     [(cons
                        (compilation-result arg-depends-on-env?
                                            arg-free-vars
                                            compiled-arg)
                        arg-compilation-results)
                      (next (or depends-on-env? arg-depends-on-env?)
                            (hash-union free-vars arg-free-vars
                                        #:combine (match-lambda**
                                                    [(#t #t) #t]))
                            (cons compiled-arg rev-compiled-args)
                            arg-compilation-results)])))))]
          [#t (error "Uncallable value")])]
       [_ (continuation-expr-continue-eval/t_ env cont val/t_)])]))

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

(struct parsed-lambda-args (n arg-vars body) #:transparent)

(define (parse-lambda-args err-name args)
  (match args
    [`(,arg-vars ,body)
     (unless (list? arg-vars)
       (raise-arguments-error err-name
         "expected the argument list to be a list"
         "argument list" arg-vars))
     (unless (andmap symbol? arg-vars)
       (raise-arguments-error err-name
         "expected the argument list to be a list of symbols"
         "argument list" arg-vars))
     (define n (length arg-vars))
     (unless (equal? n (hash-count
                         (for/hash ([arg (in-list arg-vars)])
                           (values arg #t))))
       (raise-arguments-error err-name
         "expected the argument list to be a list of mutually unique symbols"
         "argument list" arg-vars))
     (parsed-lambda-args n arg-vars body)]
    [_
     (raise-arguments-error err-name
       "expected an argument list and a body"
       "subforms" args)]))

; An interpreted lambda. This doesn't attempt to compile the body. It
; evaluates the body each time it's called.
(define fexpress-ilambda
  (makeshift-fexpr
    #;continue-eval/t_
    (lambda (env cont op/t_)
      ; TODO CLEANUP: Consider moving this branch to methods on the
      ; `gen:continuation-expr` generic interface.
      (match cont
        [(apply/ce args cont)
         (match-define (parsed-lambda-args n arg-vars body)
           (parse-lambda-args 'ilambda args))
         (type_-continue-eval/t_ env cont
           (specific-value/t_
             (lambda arg-values
               (define received-n (length arg-values))
               (unless (equal? n received-n)
                 (raise-arguments-error 'ilambda
                   "wrong number of arguments at call time"
                   "number expected" n
                   "number received" received-n
                   "arguments expected" arg-vars
                   "arguments received" arg-values))
               (define body-env
                 (for/fold ([env env])
                           ([arg-var (in-list arg-vars)]
                            [arg-value (in-list arg-values)])
                   (hash-set env arg-var
                     (specific-variable-bound-value/t_ arg-var
                                                       arg-value))))
               (type_-eval
                 (fexpress-eval/t_ body-env (done/ce (any-value/t+))
                                   body)))))]
        [_ (continuation-expr-continue-eval/t_ env cont op/t_)]))))

(define (compile-clambda env cont args)
  (match-define (parsed-lambda-args n arg-vars body)
    (parse-lambda-args 'clambda args))
  (define body-env
    (for/fold ([env env])
              ([arg-var (in-list arg-vars)])
      (hash-set env arg-var
        ; TODO TYPED ARGUMENTS: Make the negative types here depend on
        ; `cont`.
        (unknown-value/t_ (local-compilation-result arg-var)))))
  (match-define
    (compilation-result depends-on-env? body-free-vars body-compiled)
    (type_-compile
      ; TODO TYPED ARGUMENTS: Make the continuation here depend on
      ; `cont`.
      (fexpress-eval/t_ body-env (done/ce (any-value/t+)) body)))
  (define body-with-env-compiled
    (if depends-on-env?
      `(,#'let
         ([env
           (,#'hash-set* env
             ,@(append*
                 (for/list ([arg-var (in-list arg-vars)])
                   `(
                      ',arg-var
                      (,#'specific-variable-bound-value/t_
                        (,#'quote ,arg-var)
                        ,(format-local-symbol arg-var))))))])
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

(define (compilation-result-eval env compiled)
  (match-define
    (compilation-result depends-on-env? free-vars lambda-compiled)
    compiled)
  (define free-vars-list (hash-keys free-vars))
  (define local-free-vars-list
    (for/list ([free-var (in-list free-vars-list)])
      (format-local-symbol free-var)))
  (define lambda-maker-compiled
    `(,#'lambda (env ,@local-free-vars-list)
       ,lambda-compiled))
  ; TODO: Figure out a better way to make these conditional than
  ; commenting them out.
;  (displayln "about to eval")
;  (pretty-print (syntax->datum (datum->syntax #f lambda-maker-compiled)))
  (define lambda-maker
    (eval lambda-maker-compiled
          (namespace-anchor->namespace here)))
  (define free-var-type_-list
    (for/list ([free-var (in-list free-vars-list)])
      (environment-get/t_ env free-var)))
  (define free-var-val-list
    (for/list ([val/t_ (in-list free-var-type_-list)])
      (type_-eval val/t_)))
  (apply lambda-maker
    (for/fold ([lambda-maker-env env])
              ([free-var (in-list free-vars-list)]
               [val/t_ (in-list free-var-type_-list)])
      (hash-set lambda-maker-env free-var
        (at-variable/t_ free-var val/t_)))
    free-var-val-list))


; A compiled lambda. This doesn't attempt to compile the body. It
; evaluates the body each time it's called.
(define fexpress-clambda
  (makeshift-fexpr
    #;continue-eval/t_
    (lambda (env cont op/t_)
      ; TODO CLEANUP: Consider moving this branch to methods on the
      ; `gen:continuation-expr` generic interface.
      (match cont
        [(apply/ce args cont)
         (define compiled-clambda (compile-clambda env cont args))
         (type_-continue-eval/t_ env cont

           ; TODO LAZY: Rather than just using `lazy-value/t_` here,
           ; we could also specialize `type_-continue-eval/t_` to
           ; treat a `clambda` as being guaranteed not to return an
           ; fexpr. That could let us use them in functional position
           ; without inhibiting compilation.
           ;
           (lazy-value/t_
             (lambda ()
               (compilation-result-eval env compiled-clambda))
             (const0 compiled-clambda)))]
        [_ (continuation-expr-continue-eval/t_ env cont op/t_)]))))

(define (fexpress-make-base-env)
  (define naive-env
    (hash 'type_-eval type_-eval
          'eval/t_ fexpress-eval/t_
          'done/ce done/ce
          'any-value/t+ any-value/t+
          'make-base-env fexpress-make-base-env
          'ilambda fexpress-ilambda
          'clambda fexpress-clambda
          '+ +
          '* *
          'app (lambda (op . args) (apply op args))))
  (for/hash ([(var val) (in-hash naive-env)])
    (values var (specific-variable-bound-value/t_ var val))))

(define (fexpress-eval-in-base-env expr)
  (type_-eval
    (fexpress-eval/t_ (fexpress-make-base-env)
                      (done/ce (any-value/t+))
                      expr)))
