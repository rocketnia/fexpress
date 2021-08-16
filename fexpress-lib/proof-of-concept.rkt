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


(require (only-in racket/contract/base -> any/c contract-out listof))
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
    [fexpress-eval-in-base-env (-> any/c any/c)]

    ; TODO: Document these other exports.
    [type+? (-> any/c boolean?)]
    [type_? (-> any/c boolean?)]
    [any-value/t+ (-> type+?)]
    [any-value/t_ (-> type_?)]
    [non-fexpr-value/t+ (-> type+?)]
    [->/t_ (-> (listof type+?) type_? type_?)]))

; TODO: Reorganize this code. It's pretty messy.


(define-namespace-anchor here)


(define (const0 result)
  (lambda ()
    result))


(define-generics fexpr
  (fexpr-continue-eval/t+ env cont fexpr/t+ fexpr))

(struct makeshift-fexpr (continue-eval/t+) #:transparent
  #:methods gen:fexpr
  [(define (fexpr-continue-eval/t+ env cont op/t+ op)
     (match-define (makeshift-fexpr continue-eval/t+) op)
     (continue-eval/t+ env cont op/t+))])

(define-generics continuation-expr
  (continuation-expr-continue-eval/t+ env continuation-expr val/t+))

; Negative types.
(define-generics type+
  (type+-eval type+)
  (type+-compile type+)
  (at-variable/t+ var type+)
  (type+-continue-eval/t+ env cont type+))

(define (format-local-symbol sym)
  (format-symbol "-~a" sym))

(define (environment-get/t+ env var)
  (hash-ref env var
    (lambda ()
      (raise-arguments-error 'environment-get/t+
        "Unbound variable"
        "var" var
        "env" env))))

(struct compilation-result (depends-on-env? free-vars expr)
  #:transparent)

(define (local-compilation-result var)
  (compilation-result #f (hash var #t) (format-local-symbol var)))

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
  (define free-var-type+-list
    (for/list ([free-var (in-list free-vars-list)])
      (environment-get/t+ env free-var)))
  (define free-var-val-list
    (for/list ([val/t+ (in-list free-var-type+-list)])
      (type+-eval val/t+)))
  (apply lambda-maker
    (for/fold ([lambda-maker-env env])
              ([free-var (in-list free-vars-list)]
               [val/t+ (in-list free-var-type+-list)])
      (hash-set lambda-maker-env free-var
        (at-variable/t+ free-var val/t+)))
    free-var-val-list))

; Positive types.
(define-generics type_
  (type_-continue-eval/t+ env type_ val/t+))

(struct any-value/t_ () #:transparent
  #:methods gen:type_
  [(define (type_-continue-eval/t+ env type_ val/t+)
     val/t+)])

; TODO LANGUAGE: Consider letting it be an error for this type to be
; ascribed to a non-function (e.g., a number or an fexpr). Currently,
; it's just used opportunistically to optimize the body of a
; `clambda`, and the only way it can raise an error is by having a
; number of arguments that doesn't match the length of the `clambda`'s
; argument list.
;
(struct ->/t_ (arg-type+-list return/t_) #:transparent
  #:methods gen:type_
  [(define (type_-continue-eval/t+ env type_ val/t+)
     val/t+)])

(struct lazy-value/t+ (eval compile) #:transparent
  #:methods gen:type+
  [(define (type+-eval type+)
     (match-define (lazy-value/t+ eval compile) type+)
     (eval))
   (define (type+-compile type+)
     (match-define (lazy-value/t+ eval compile) type+)
     (compile))
   (define (at-variable/t+ var type+)
     (match-define (lazy-value/t+ eval compile) type+)
     (lazy-value/t+ eval (const0 (local-compilation-result var))))
   (define (type+-continue-eval/t+ env cont val/t+)
     (continuation-expr-continue-eval/t+ env cont val/t+))])

(struct unknown-value/t+ (val-compiled) #:transparent
  #:methods gen:type+
  [(define (type+-eval type+)
     (raise-arguments-error 'type+-eval
       "Tried to evaluate the value level of a positive type that represented a run-time value during compilation. This may be an internal bug in the Fexpress proof of concept."
       "positive type" type+))
   (define (type+-compile type+)
     (match-define (unknown-value/t+ val-compiled) type+)
     val-compiled)
   (define (at-variable/t+ var type+)
     (unknown-value/t+ (local-compilation-result var)))
   (define (type+-continue-eval/t+ env cont val/t+)
     (continuation-expr-continue-eval/t+ env cont val/t+))])

(struct any-value/t+ () #:transparent
  #:methods gen:type+
  [(define (type+-eval type+)
     (error "tried to evaluate the value level of the ascribed type `(any-value/t+)`"))
   (define (type+-compile type+)
     (error "tried to compile the value level of the ascribed type `(any-value/t+)`"))
   (define (at-variable/t+ var type+)
     (unknown-value/t+ (local-compilation-result var)))
   (define (type+-continue-eval/t+ env cont val/t+)
     (continuation-expr-continue-eval/t+ env cont val/t+))])

(struct specific-variable-bound-value/t+ (var val) #:transparent
  #:methods gen:type+
  [(define (type+-eval type+)
     (match-define (specific-variable-bound-value/t+ var val) type+)
     val)
   (define (type+-compile type+)
     (match-define (specific-variable-bound-value/t+ var val) type+)
     (local-compilation-result var))
   (define (at-variable/t+ var type+)
     (match-define (specific-variable-bound-value/t+ original-var val)
       type+)
     (specific-variable-bound-value/t+ var val))
   (define (type+-continue-eval/t+ env cont val/t+)
     (match-define (specific-variable-bound-value/t+ var val) val/t+)
     (fexpress-continue-eval/t+ env cont val/t+ val))])

(struct specific-value/t+ (value) #:transparent
  #:methods gen:type+
  [(define (type+-eval type+)
     (match-define (specific-value/t+ value) type+)
     value)
   (define (type+-compile type+)
     (error "Tried to compile the a value level of a positive type that represented a reified first-class value that didn't have a known compiled form. This may be an internal bug in the Fexpress proof of concept."))
   (define (at-variable/t+ var type+)
     (match-define (specific-value/t+ value) type+)
     (specific-variable-bound-value/t+ var value))
   (define (type+-continue-eval/t+ env cont val/t+)
     (match-define (specific-value/t+ value) val/t+)
     (fexpress-continue-eval/t+ env cont val/t+ value))])

(struct done/ce (type_) #:transparent
  #:methods gen:continuation-expr
  [(define (continuation-expr-continue-eval/t+ env cont val/t+)
     (match-define (done/ce type_) cont)
     (type_-continue-eval/t+ env type_ val/t+))])

(struct apply/ce (args next) #:transparent
  #:methods gen:continuation-expr
  [(define (continuation-expr-continue-eval/t+ env cont val/t+)
     (match-define (apply/ce args next) cont)
     (type+-continue-eval/t+ env next
       (lazy-value/t+
         (lambda ()
           (type+-eval
             (fexpress-continue-eval/t+
               env
               (apply/ce args (done/ce (any-value/t_)))
               val/t+
               (type+-eval val/t+))))
         (lambda ()
           (match-define (compilation-result _ free-vars op-compiled)
             (type+-compile val/t+))
           (compilation-result #t free-vars

             ; NOTE: Since we're just going to `type+-eval` it anyway,
             ; we don't need anything more than `specific-value/t+`
             ; here. The `val/t+` type may know extra things like how
             ; to compile the value, but we don't need to make any
             ; effort to reify that information here.
             ;
             `(,#'type+-eval
                 (,#'type+-continue-eval/t+
                   env
                   (,#'apply/ce (,#'quote ,args)
                     (,#'done/ce (,#'any-value/t_)))
                   (,#'specific-value/t+ ,op-compiled))))))))])

(define (literal? v)
  (exact-integer? v))

(define (fexpress-eval/t+ env cont expr)
  (match expr
    [`(,op-expr . ,args)
     (fexpress-eval/t+ env (apply/ce args cont) op-expr)]
    [(? symbol? var)
     (type+-continue-eval/t+ env cont (environment-get/t+ env var))]
    [(? literal? val)
     (type+-continue-eval/t+ env cont
       ; TODO LAZY: Rather than just using `lazy-value/t+` here, we
       ; could also specialize `type+-continue-eval/t+` to raise an
       ; error if a literal is used in functional position.
       (lazy-value/t+
         (const0 val)
         (const0
           (compilation-result #f (hash) `(,#'#%datum . ,val)))))]
    [_ (error "Unrecognized expression")]))

(define (unknown-non-fexpr-apply/t+
          env cont val-to-eval/t+ val-to-compile/t+ args)
  (define arg-type+-list
    (for/list ([arg (in-list args)])
      (fexpress-eval/t+ env (done/ce (any-value/t_)) arg)))
  (type+-continue-eval/t+ env cont

    ; TODO LAZY: Rather than just using `lazy-value/t+` here, we could
    ; also specialize `type+-continue-eval/t+` to treat certain
    ; procedures as being guaranteed not to return an fexpr. That
    ; could let us use those procedure calls in functional position
    ; without inhibiting compilation.
    ;
    (lazy-value/t+
      (lambda ()
        (apply (type+-eval val-to-eval/t+)
          (for/list ([arg/t+ (in-list arg-type+-list)])
            (type+-eval arg/t+))))
      (lambda ()
        (define op-compilation-result
          (type+-compile val-to-compile/t+))
        (define arg-compilation-results
          (for/list ([arg/t+ (in-list arg-type+-list)])
            (type+-compile arg/t+)))
        (match-define
          (compilation-result
            op-depends-on-env? op-free-vars op-compiled)
          op-compilation-result)
        (let next ([depends-on-env? op-depends-on-env?]
                   [free-vars op-free-vars]
                   [rev-compiled-args (list)]
                   [arg-compilation-results arg-compilation-results])
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
                   arg-compilation-results)]))))))

(define (fexpress-continue-eval/t+ env cont val/t+ val)
  (cond
    [(fexpr? val) (fexpr-continue-eval/t+ env cont val/t+ val)]
    [#t
     ; TODO CLEANUP: Consider moving this branch to a
     ; `continuation-expr-continue-eval-value/t+` method.
     (match cont
       [(apply/ce args cont)
        (cond
          [(procedure? val)
           (unless (and (list? args)
                        (procedure-arity-includes? val (length args)))
             (error "Wrong number of arguments to a procedure"))
           (unknown-non-fexpr-apply/t+
             env cont (specific-value/t+ val) val/t+ args)]
          [#t (error "Uncallable value")])]
       [_ (continuation-expr-continue-eval/t+ env cont val/t+)])]))

(define (non-fexpr-continue-eval/t+ env cont val/t+)
  ; TODO CLEANUP: Consider moving this branch to a
  ; `continuation-expr-continue-eval-value/t+` method.
  (match cont
    [(apply/ce args cont)
     (unknown-non-fexpr-apply/t+ env cont val/t+ val/t+ args)]
    [_ (continuation-expr-continue-eval/t+ env cont val/t+)]))

; TODO LANGUAGE: Consider letting it be an error for this type to be
; ascribed to an fexpr. Currently, it's just used opportunistically to
; optimize the body of a `clambda`.
(struct variable-bound-non-fexpr-value/t+ (var) #:transparent
  #:methods gen:type+
  [(define (type+-eval type+)
     ; TODO: Figure out if we should report this error in terms of
     ; `variable-bound-non-fexpr-value/t+` even though it's more of an
     ; implementation detail.
     (error "tried to evaluate the value level of the ascribed type `(non-fexpr-value/t+)`"))
   (define (type+-compile type+)
     (match-define (variable-bound-non-fexpr-value/t+ var) type+)
     (local-compilation-result var))
   (define (at-variable/t+ var type+)
     (variable-bound-non-fexpr-value/t+ var))
   (define (type+-continue-eval/t+ env cont val/t+)
     (non-fexpr-continue-eval/t+ env cont val/t+))])

; TODO LANGUAGE: Consider letting it be an error for this type to be
; ascribed to an fexpr. Currently, it's just used opportunistically to
; optimize the body of a `clambda`.
(struct non-fexpr-value/t+ () #:transparent
  #:methods gen:type+
  [(define (type+-eval type+)
     (error "tried to evaluate the value level of the ascribed type `(non-fexpr-value/t+)`"))
   (define (type+-compile type+)
     (error "tried to compile the value level of the ascribed type `(non-fexpr-value/t+)`"))
   (define (at-variable/t+ var type+)
     (variable-bound-non-fexpr-value/t+ var))
   (define (type+-continue-eval/t+ env cont val/t+)
     (non-fexpr-continue-eval/t+ env cont val/t+))])

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
    #;continue-eval/t+
    (lambda (env cont op/t+)
      ; TODO CLEANUP: Consider moving this branch to methods on the
      ; `gen:continuation-expr` generic interface.
      (match cont
        [(apply/ce args cont)
         (match-define (parsed-lambda-args n arg-vars body)
           (parse-lambda-args 'ilambda args))
         (type+-continue-eval/t+ env cont
           (specific-value/t+
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
                     (specific-variable-bound-value/t+ arg-var
                                                       arg-value))))
               (type+-eval
                 (fexpress-eval/t+ body-env (done/ce (any-value/t_))
                                   body)))))]
        [_ (continuation-expr-continue-eval/t+ env cont op/t+)]))))

(define (compile-clambda env cont args)
  (match-define (parsed-lambda-args n arg-vars body)
    (parse-lambda-args 'clambda args))
  (match-define (list arg-type+-list return-val/t_)
    (match cont
      ; TODO CLEANUP: Consider moving this branch to methods on the
      ; `gen:continuation-expr` and `gen:type_` generic interfaces.
      [(done/ce (->/t_ arg-type+-list return-val/t_))
       (unless (equal? n (length arg-type+-list))
         (error "Expected the type of a function to have just as many arguments as the argument list of the function"))
       (list
         (for/list ([arg-var (in-list arg-vars)]
                    [arg/t+ (in-list arg-type+-list)])
           (at-variable/t+ arg-var arg/t+))
         return-val/t_)]
      [_
       (list
         (for/list ([arg-var (in-list arg-vars)])
           (unknown-value/t+ (local-compilation-result arg-var)))
         (any-value/t_))]))
  (define body-env
    (for/fold ([env env])
              ([arg-var (in-list arg-vars)]
               [arg/t+ (in-list arg-type+-list)])
      (hash-set env arg-var arg/t+)))
  (match-define
    (compilation-result depends-on-env? body-free-vars body-compiled)
    (type+-compile
      (fexpress-eval/t+ body-env (done/ce return-val/t_) body)))
  (define body-with-env-compiled
    (if depends-on-env?
      `(,#'let
         ([env
           (,#'hash-set* env
             ,@(append*
                 (for/list ([arg-var (in-list arg-vars)])
                   `(
                      ',arg-var
                      (,#'specific-variable-bound-value/t+
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

; A compiled lambda. This doesn't attempt to compile the body. It
; evaluates the body each time it's called.
(define fexpress-clambda
  (makeshift-fexpr
    #;continue-eval/t+
    (lambda (env cont op/t+)
      ; TODO CLEANUP: Consider moving this branch to methods on the
      ; `gen:continuation-expr` generic interface.
      (match cont
        [(apply/ce args cont)
         (define compiled-clambda (compile-clambda env cont args))
         (type+-continue-eval/t+ env cont

           ; TODO LAZY: Rather than just using `lazy-value/t+` here,
           ; we could also specialize `type+-continue-eval/t+` to
           ; treat a `clambda` as being guaranteed not to return an
           ; fexpr. That could let us use them in functional position
           ; without inhibiting compilation.
           ;
           (lazy-value/t+
             (lambda ()
               (compilation-result-eval env compiled-clambda))
             (const0 compiled-clambda)))]
        [_ (continuation-expr-continue-eval/t+ env cont op/t+)]))))

; Type ascription. The usage is `(the val/t_ val)`, where `val/t_` is
; syntactically a negative type (not just an expression that evaluates
; to one) and `val` is an expression the type applies to. This is
; mainly used to allow function bodies to use Lisp-1-style function
; application on local variables without inhibiting compilation.
;
(define fexpress-the
  (makeshift-fexpr
    #;continue-eval/t+
    (lambda (env cont op/t+)
      ; TODO CLEANUP: Consider moving this branch to methods on the
      ; `gen:continuation-expr` generic interface.
      (match cont
        [(apply/ce args cont)
         (match args
           [`(,expr/t_ ,expr)
            (unless (type_? expr/t_)
              (error "the: expected the type to be a negative type value, syntactically, and not merely an expression that evaluated to one"))
            (type+-continue-eval/t+ env cont
              (fexpress-eval/t+ env (done/ce expr/t_) expr))]
           [_
            (error "the: expected a literal negative type and an expression")])]
        [_ (continuation-expr-continue-eval/t+ env cont op/t+)]))))

(define (fexpress-make-base-env)
  (define naive-env
    (hash 'type+-eval type+-eval
          'eval/t+ fexpress-eval/t+
          'done/ce done/ce
          'any-value/t_ any-value/t_
          'make-base-env fexpress-make-base-env
          'ilambda fexpress-ilambda
          'clambda fexpress-clambda
          'the fexpress-the
          '+ +
          '* *
          'app (lambda (op . args) (apply op args))))
  (for/hash ([(var val) (in-hash naive-env)])
    (values var (specific-variable-bound-value/t+ var val))))

(define (fexpress-eval-in-base-env expr)
  (type+-eval
    (fexpress-eval/t+ (fexpress-make-base-env)
                      (done/ce (any-value/t_))
                      expr)))
