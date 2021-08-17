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


(require
  (only-in racket/contract/base -> any/c contract-out hash/c listof))
(require (only-in racket/function const))
(require (only-in racket/generic define-generics))
(require (only-in racket/hash hash-union))
(require (only-in racket/list append*))
(require (only-in racket/match match match-define match-lambda**))
; TODO: Figure out a better way to make this conditional than
; commenting it out.
;(require (only-in racket/pretty pretty-print))
(require (only-in racket/syntax format-symbol))


(provide

  ; Contracts
  (contract-out
    [var? (-> any/c boolean?)]
    [env? (-> any/c boolean?)]
    [free-vars? (-> any/c boolean?)])

  ; Generic interfaces to serve as extension points
  ; TODO DOCS: Document the negative type interface in its respective
  ; section.
  gen:fexpr
  (contract-out
    [fexpr? (-> any/c boolean?)]
    [fexpr-continue-eval/t+
     (-> env? continuation-expr? type+? fexpr? type+?)])
  ; NOTE: Instead of exporting this as a struct, we export only the
  ; constructor.
  #;
  (struct-out makeshift-fexpr)
  (contract-out
    [makeshift-fexpr
     (-> (-> env? continuation-expr? type+? type+?) fexpr?)])
  gen:continuation-expr
  (contract-out
    [continuation-expr? (-> any/c boolean?)]
    [continuation-expr-continue-eval/t+
     (-> env? continuation-expr? type+? type+?)])
  gen:type+
  (contract-out
    [type+? (-> any/c boolean?)]
    [type+-eval (-> type+? any/c)]
    [type+-compile (-> type+? compilation-result?)]
    [at-variable/t+ (-> var? type+? type+?)]
    [type+-continue-eval/t+
     (-> env? continuation-expr? type+? type+?)])
  gen:type_
  (contract-out
    [type_? (-> any/c boolean?)])

  ; Utilities for compiling to Racket
  ; TODO DOCS: Document these.
  (contract-out
    [env-get/t+ (-> env? var? type+?)]
    [var-representation-in-racket (-> var? symbol?)])
  (struct-out compilation-result)
  (contract-out
    [var-compile (-> var? compilation-result?)]
    [compilation-result-eval (-> env? compilation-result? any/c)])

  ; Negative types
  ; TODO DOCS: Document these.
  (struct-out any-value/t_)
  (struct-out ->/t_)

  ; Positive types
  ;
  ; NOTE: Instead of exporting all of these as structs, we export just
  ; some of them, and we export only the constructors. This seems to
  ; be sufficient; nothing we've built so far needs to know the
  ; identity of a positive type, just invoke its own methods.
  ;
;  (struct-out lazy-value/t+)
;  (struct-out any-variable-bound-value/t+)
;  (struct-out any-value/t+)
;  (struct-out variable-bound-non-fexpr-value/t+)
;  (struct-out non-fexpr-value/t+)
;  (struct-out specific-variable-bound-value/t+)
;  (struct-out specific-value/t+)
  (contract-out
    [lazy-value/t+ (-> (-> any/c) (-> compilation-result?) type+?)]
    [any-value/t+ (-> type+?)]
    [non-fexpr-value/t+ (-> type+?)]
    [specific-value/t+ (-> any/c type+?)])

  ; Continuation expressions
  (struct-out done/ce)
  (struct-out apply/ce)

  ; The Fexpress combination evaluator-compiler
  (contract-out
    [literal? (-> any/c boolean?)]
    [fexpress-eval/t+ (-> env? continuation-expr? any/c type+?)]
    [unknown-non-fexpr-apply/t+
     (-> env? continuation-expr? type+? type+? any/c type+?)]
    [specific-value-continue-eval/t+
     (-> env? continuation-expr? type+? any/c type+?)]
    [non-fexpr-continue-eval/t+
     (-> env? continuation-expr? type+? type+?)])

  ; Fexprs for lambda operations
  (struct-out parsed-lambda-args)
  (contract-out
    [parse-lambda-args (-> symbol? any/c parsed-lambda-args?)]
    [fexpress-ilambda fexpr?]

    ; NOTE: We treat this as internal.
    #;
    [compile-clambda
     (-> env? continuation-expr? any/c compilation-result?)]

    [fexpress-clambda fexpr?])

  ; An fexpr for type ascription
  (contract-out
    [fexpress-the fexpr?])

  ; The Fexpress entrypoint
  (contract-out
    [env-of-specific-values (-> (hash/c var? any/c) env?)]
    [fexpress-eval (-> env? any/c any/c)])

  )


(define-namespace-anchor here)



; ===== Contracts ====================================================

; A contract that recognizes this language's variable names, which are
; represented by interned symbols.
(define (var? v)
  (and (symbol? v) (symbol-interned? v)))

; A contract that recognizes this language's lexical environments,
; which are represented by immutable hashes from variable names to
; positive types. Besides being positive types, the values of the hash
; should also have successful `type+-compile` behavior, and it should
; be equivalent to `var-compile` for the same Fexpress variable.
(define (env? v)
  (and (hash? v) (immutable? v)
    (for/and ([(k v) (in-hash v)])
      (and (var? k) (type+? v)))))

; A contract that recognizes Fexpress free variable sets, which are
; represented by immutable hashes from variable names to `#t`.
(define (free-vars? v)
  (and (hash? v) (immutable? v)
    (for/and ([(k v) (in-hash v)])
      (and (var? k) (equal? #t v)))))



; ===== Generic interfaces to serve as extension points ==============

; An fexpr. In Fexpress, the calling convention for fexprs is a bit
; different than it might be in other fexpr languages. They receive
; their arguments on a continuation expression, and they can implement
; both compilation behavior and dynamic behavior via the interface of
; the positive types they return.
;
(define-generics fexpr

  ; (Calls fexprs, namely this one.) Returns a positive type for the
  ; potential values which result from transforming the given positive
  ; type and the given value (this fexpr) of that type according to
  ; the series of steps and the target negative type listed in the
  ; given continuation expression.
  ;
  ; There are many `...-continue-eval/t+` operations in Fexpress, and
  ; this is the one to call when the actual *value* of the original
  ; type is known and is definitely an fexpr. The fexpr can implement
  ; its own operation-specific behavior here, or it can dispatch again
  ; to `continuation-expr-continue-eval/t+` to handle a continuation
  ; expression it doesn't know how to interpret itself.
  ;
  ; Contract:
  ; (-> env? continuation-expr? type+? fexpr? type+?)
  ;
  ; The given positive type should evaluate to a value that is this
  ; fexpr.
  ;
  (fexpr-continue-eval/t+ env cont fexpr/t+ fexpr))

; An fexpr. This way of creating an fexpr is good for when it isn't
; necessary to give the fexpr other structure type properties. Where
; the `gen:fexpr` interface is like `prop:procedure`, the
; `makeshift-fexpr` interface is like `lambda`.
;
; Field contract:
; (-> env? continuation-expr? type+? type+?)
;
(struct makeshift-fexpr (continue-eval/t+) #:transparent
  #:methods gen:fexpr
  [(define (fexpr-continue-eval/t+ env cont op/t+ op)
     (match-define (makeshift-fexpr continue-eval/t+) op)
     (continue-eval/t+ env cont op/t+))]
  #:property prop:procedure
  (lambda (fexpr . args)
    (error "attempted to call an Fexpress fexpr from Racket code, which is not supported")))

; A continuation expression, which is a representation of the syntax
; around the evaluating part of an Fexpress expression.
;
; Usually, this is a series of pending fexpr applications (`apply/ce`)
; to perform in the current environment, followed by an ascribed
; negative type to optimize the overall result by (`done/ce`). Other
; kinds of copatterns or spine elements, like field or method accessor
; syntaxes, could fit in here as well.
;
(define-generics continuation-expr

  ; (Calls fexprs.) Assuming the given positive type will have no
  ; known fexpr-calling behavior until we witness its potential
  ; values, returns another positive type for the potential values
  ; which result from transforming those according to the series of
  ; steps and the target negative type listed in the given
  ; continuation expression.
  ;
  ; There are many `...-continue-eval/t+` operations in Fexpress, and
  ; this is the one to call when the positive type's fexpr-calling
  ; behavior should be ignored but its values' fexpr-calling behavior,
  ; if any, should not be ignored. This will usually result in code
  ; that consults the value at run time and makes fexpr calls to it
  ; dynamically. A positive type usually dispatches to this itself
  ; when its `type+-continue-eval/t+` behavior has no better idea for
  ; what to do.
  ;
  ; Contract:
  ; (-> env? continuation-expr? type+? type+?)
  ;
  (continuation-expr-continue-eval/t+ env continuation-expr val/t+))

; A positive type. Positive types in Fexpress arguably act less like
; types and more like symbolic values.
(define-generics type+

  ; Attempts to compute a value of the type.
  ;
  ; Contract:
  ; (-> type+? any/c)
  ;
  (type+-eval type+)

  ; Attempts to produce a compilation result that evaluates to values
  ; of the given type in the environment the type belongs to.
  ;
  ; Contract:
  ; (-> type+? compilation-result?)
  ;
  (type+-compile type+)

  ; Replaces the type's compilation result so that it refers to the
  ; given Fexpress variable. The variable's potential bindings must be
  ; among the type's potential values, but nothing is done to verify
  ; this.
  ;
  ; Any type that's added to an environment should be transformed this
  ; way, since it's now in scope under a dedicated name.
  ;
  ; Contract:
  ; (-> var? type+? type+?)
  ;
  (at-variable/t+ var type+)

  ; (Calls fexprs.) Returns a positive type for the potential values
  ; which result from transforming this type according to a series of
  ; steps and a target negative type listed in the given continuation
  ; expression.
  ;
  ; There are many `...-continue-eval/t+` operations in Fexpress, and
  ; this is the most general one; it dispatches to the others.
  ;
  ; Contract:
  ; (-> env? continuation-expr? type+? type+?)
  ;
  (type+-continue-eval/t+ env cont type+))

; A negative type. Fexpress's fexprs can use these as optimization
; hints. There are no methods because each fexpr may have different
; kinds of special cases it's looking to optimize. (That's not to say
; we wouldn't add methods if we turned out to have a use for them.)
;
(define-generics type_
  )



; ===== Utilities for compiling to Racket ============================

; Contract:
; (-> env? var? type+?)
(define (env-get/t+ env var)
  (hash-ref env var
    (lambda ()
      (raise-arguments-error 'env-get/t+
        "Unbound variable"
        "var" var
        "env" env))))

; Converts an Fexpress variable name into the symbol it should be
; represented as in compiled Racket code for `compilation-result?`
; values. Currently, it's the same symbol but with "-" prepended to
; it.
;
; Contract:
; (-> var? symbol?)
;
(define (var-representation-in-racket sym)
  (format-symbol "-~a" sym))

; Field contracts:
; boolean? free-vars? any/c
;
; The `expr` should be an s-expression of Racket code. It may have
; free variables corresponding to the `var-representation-in-racket`
; versions of what the Fexpress free variables would be. It may also
; have the free variable `env` if `depends-on-env?` is `#t`. The `env`
; variable refers to the current lexical environment. It may also have
; Racket syntax objects, so as to refer unambiguously to Racket module
; imports.
;
; Depending on the lexical environment using `depends-on-env?` can
; lead to performance degradation in code that results, since an
; up-to-date first-class environment value must be constructed
; whenever variables come into scope.
;
; While we could make more extensive use of Racket syntax objects, we
; keep their use to a minimum here to demonstrate this language in a
; way that can be easily ported to other Lisp dialects.
;
(struct compilation-result (depends-on-env? free-vars expr)
  #:transparent)

; Compiles an expression that just refers to the given Fexpress
; variable.
;
; Contract:
; (-> var? compilation-result?)
;
(define (var-compile var)
  (compilation-result #f (hash var #t)
    (var-representation-in-racket var)))

; TODO CLEANUP: Consider implementing some `compilation-result` monad
; operations here. They might make parts of the code more
; straightforward for people used to monads, but I'm not sure if
; that's the audience.

; Evaluates a compilation result in a given Fexpress environment. We
; use this to delegate to Racket's own compiler to give us optimized
; code.
;
; Contract:
; (-> env? compilation-result? any/c)
;
(define (compilation-result-eval env compiled)
  (match-define
    (compilation-result depends-on-env? free-vars lambda-compiled)
    compiled)
  (define free-vars-list (hash-keys free-vars))
  (define local-free-vars-list
    (for/list ([free-var (in-list free-vars-list)])
      (var-representation-in-racket free-var)))
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
      (env-get/t+ env free-var)))
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



; ===== Negative types ===============================================

(struct any-value/t_ () #:transparent
  #:methods gen:type_
  [])

; Creates a negative type for functions, given a list of positive
; types for the arguments and a single negative type for the result.
;
; If we unpack the meaning of positive and negative types in Fexpress,
; this is a compilation hint for expressions that return functions.
; It supposes the given symbolic values for the arguments, and it
; gives the given compilation hint for the function's result. For a
; lambda form, the hint can be used for compiling the body, as
; `fexpress-clambda` demonstrates.
;
; Field contracts:
; (listof type+?) type_?
;
(struct ->/t_ (arg-type+-list return/t_) #:transparent
  #:methods gen:type_
  [])



; ===== Positive types ===============================================

; Field contracts:
; (-> any/c) (-> compilation-result?)
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
     (lazy-value/t+ eval (const (var-compile var))))
   (define (type+-continue-eval/t+ env cont val/t+)
     (continuation-expr-continue-eval/t+ env cont val/t+))])

; (A helper for `any-value/t+`.)
;
; Field contract:
; var?
;
(struct any-variable-bound-value/t+ (var) #:transparent
  #:methods gen:type+
  [(define (type+-eval type+)
     (error "tried to evaluate the value level of the ascribed type `(any-value/t+)`"))
   (define (type+-compile type+)
     (match-define (any-variable-bound-value/t+ var) type+)
     (var-compile var))
   (define (at-variable/t+ var type+)
     (any-variable-bound-value/t+ var))
   (define (type+-continue-eval/t+ env cont val/t+)
     (continuation-expr-continue-eval/t+ env cont val/t+))])

(struct any-value/t+ () #:transparent
  #:methods gen:type+
  [(define (type+-eval type+)
     (error "tried to evaluate the value level of the ascribed type `(any-value/t+)`"))
   (define (type+-compile type+)
     (error "tried to compile the value level of the ascribed type `(any-value/t+)`"))
   (define (at-variable/t+ var type+)
     (any-variable-bound-value/t+ var))
   (define (type+-continue-eval/t+ env cont val/t+)
     (continuation-expr-continue-eval/t+ env cont val/t+))])

; -----
; NOTE: Past this point, a few things are mutually recursive.
;
; Each element of the of the following 6-cycle depends on the one
; before (wrapping around from the first to the last):
;
;   * `specific-variable-bound-value/t+`
;   * `specific-value/t+`
;   * `apply/ce`
;   * `fexpress-eval/t+`
;   * `unknown-non-fexpr-apply/t+`
;   * `specific-value-continue-eval/t+`
;
; Each element of the following 3-path depends on each one adjacent to
; it (without wrapping):
;
;   * `specific-value/t+`
;   * `specific-value-continue-eval/t+`
;   * `apply/ce`
;
; Cycles of other lengths may be traced through the relationships
; already described.
;
; We also place `variable-bound-non-fexpr-value/t+` and
; `non-fexpr-value/t+` here, although they depend on
; `non-fexpr-continue-eval/t+` defined further below. We could put
; them just after `non-fexpr-continue-eval/t+`, but we put them here
; for code organization purposes, to group all the positive type
; definitions together.
; -----

; (A helper for `non-fexpr-value/t+`.)
;
; A positive type of values that we're allowing ourselves to assume to
; be non-fexprs for optimization purposes, and which are also known to
; be bound to the specified Fexpress variable.
;
; Field contract:
; var?
;
(struct variable-bound-non-fexpr-value/t+ (var) #:transparent
  #:methods gen:type+
  [(define (type+-eval type+)
     (error "tried to evaluate the value level of the ascribed type `(non-fexpr-value/t+)`"))
   (define (type+-compile type+)
     (match-define (variable-bound-non-fexpr-value/t+ var) type+)
     (var-compile var))
   (define (at-variable/t+ var type+)
     (variable-bound-non-fexpr-value/t+ var))
   (define (type+-continue-eval/t+ env cont val/t+)
     (non-fexpr-continue-eval/t+ env cont val/t+))])

; A positive type of values that we're allowing ourselves to assume to
; be non-fexprs for optimization purposes.
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

; (A helper for `specific-value/t+`.)
;
; Field contracts:
; var? any/c
;
(struct specific-variable-bound-value/t+ (var val) #:transparent
  #:methods gen:type+
  [(define (type+-eval type+)
     (match-define (specific-variable-bound-value/t+ var val) type+)
     val)
   (define (type+-compile type+)
     (match-define (specific-variable-bound-value/t+ var val) type+)
     (var-compile var))
   (define (at-variable/t+ var type+)
     (match-define (specific-variable-bound-value/t+ original-var val)
       type+)
     (specific-variable-bound-value/t+ var val))
   (define (type+-continue-eval/t+ env cont val/t+)
     (match-define (specific-variable-bound-value/t+ var val) val/t+)
     (specific-value-continue-eval/t+ env cont val/t+ val))])

; Field contract:
; any/c
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
     (specific-value-continue-eval/t+ env cont val/t+ value))])



; ===== Continuation expressions =====================================

; A continuation expression that represents that there's nothing left
; to do except return a value. The specified negative type can serve
; as a hint for optimizing the value.
;
; Field contract:
; type_?
;
(struct done/ce (type_) #:transparent
  #:methods gen:continuation-expr
  [(define (continuation-expr-continue-eval/t+ env cont val/t+)
     val/t+)])

; A continuation expression that represents that the next thing to do
; to the value is to invoke it as an fexpr with certain arguments.
;
; Field contracts:
; any/c continuation-expr?
;
; In typical code, the `args` to an fexpr call are usually a proper
; list.
;
(struct apply/ce (args next) #:transparent
  #:methods gen:continuation-expr
  [(define (continuation-expr-continue-eval/t+ env cont val/t+)
     (match-define (apply/ce args next) cont)
     (type+-continue-eval/t+ env next
       (lazy-value/t+
         (lambda ()
           (type+-eval
             (specific-value-continue-eval/t+
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



; ===== The Fexpress combination evaluator-compiler ==================

; Returns whether the given value can be used as a datum literal in
; the Fexpress proof of concept. For this simple demonstration, we
; just support integers.
;
; Contract:
; (-> any/c boolean?)
;
(define (literal? v)
  (exact-integer? v))

; Reduces the given Fexpress expression and continuation expression in
; the given environment to a positive type. The resulting positive
; type can be transformed into an evaluated result using `type+-eval`
; or a compiled result using `type+-compile`.
;
; Contract:
; (-> env continuation-expr? any/c type+?)
;
; The `expr` should be an s-expression of Fexpress code.
;
(define (fexpress-eval/t+ env cont expr)
  (match expr
    [`(,op-expr . ,args)
     (fexpress-eval/t+ env (apply/ce args cont) op-expr)]
    [(? symbol? var)
     (type+-continue-eval/t+ env cont (env-get/t+ env var))]
    [(? literal? val)
     (type+-continue-eval/t+ env cont
       ; TODO LAZY: Rather than just using `lazy-value/t+` here, we
       ; could also specialize `type+-continue-eval/t+` to raise an
       ; error if a literal is used in functional position.
       (lazy-value/t+
         (const val)
         (const
           (compilation-result #f (hash) `(,#'#%datum . ,val)))))]
    [_ (error "Unrecognized expression")]))

; Given unevaluated arguments, performs a Racket-like procedure call
; behavor, which first evaluates the arguments. This is a fallback for
; when a value that's called like an fexpr turns out to be a general
; Racket value rather than an Fexpress `fexpr?`.
;
; Contract:
; (-> env? continuation-expr? type+? type+? any/c type+?)
;
; The `val-to-eval/t+` type will only be used for its `type+-eval`
; behavior. The `val-to-compile/t+` type will only be used for its
; `type+-compile` behavior. These can be the same type.
;
; In typical code, the `args` to an fexpr call are usually a proper
; list. This operation raises an error if they're not.
;
(define (unknown-non-fexpr-apply/t+
          env cont val-to-eval/t+ val-to-compile/t+ args)
  (unless (list? args)
    (error "found an improper list of arguments when processing a procedure call"))
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

; (Calls fexprs.) Returns a positive type for the potential values
; which result from transforming the given positive type and the given
; value of that type according to the series of steps and the target
; negative type listed in the given continuation expression.
;
; There are many `...-continue-eval/t+` operations in Fexpress, and
; this is the one to call when the actual *value* being called is
; known and can potentially be an fexpr with its own idea of how to
; proceed. A positive type processing a `type+-continue-eval/t+` call
; usually dispatches to this itself when the type's value is known at
; compile time, and a continuation expression processing a
; `continuation-expr-continue-eval/t+` call usually dispatches to this
; itself once the value is finally known at run time.
;
; Contract:
; (-> env? continuation-expr? type+? any/c type+?)
;
; The given `val/t+` type should be a type which evaluates to the
; value `val`.
;
(define (specific-value-continue-eval/t+ env cont val/t+ val)
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

; -----
; NOTE COUPLING: Above this point, several things are mutually
; recursive. See the other NOTE COUPLING to see where this starts and
; for more details.
; -----

; (Calls fexprs.) Assuming the given positive type and its values have
; no custom fexpr-calling behavior, returns a positive type for the
; potential values which result from transforming the given one
; according to the series of steps and the target negative type listed
; in the given continuation expression.
;
; There are many `...-continue-eval/t+` operations in Fexpress, and
; this is the one to call when the positive type *and* its values
; should have their custom fexpr-calling behavior ignored. Fexpress
; doesn't usually ignore values' fexpr-calling behavior like this, but
; since this can lead to better performance, it can be explicitly
; requested by using `(the ...)` to ascribe a type that uses
; `non-fexpr-value/t+`.
;
; Contract:
; (-> env? continuation-expr? type+? type+?)
;
(define (non-fexpr-continue-eval/t+ env cont val/t+)
  ; TODO CLEANUP: Consider moving this branch to a
  ; `continuation-expr-continue-eval-value/t+` method.
  (match cont
    [(apply/ce args cont)
     (unknown-non-fexpr-apply/t+ env cont val/t+ val/t+ args)]
    [_ (continuation-expr-continue-eval/t+ env cont val/t+)]))



; ===== Fexprs for lambda operations =================================

; A return value of `parse-lambda-args`.
;
; Field contracts:
; natural? (listof var?) any/c
;
; The number `n` should be the length of `arg-vars`.
;
; The `arg-vars` should be mutually unique.
;
; The `body` should be an s-expression representing an Fexpress
; expression.
;
(struct parsed-lambda-args (n arg-vars body) #:transparent)

; Asserts that the given subforms are in the format expected for a
; lambda form -- namely, a list of two elements, the first of which is
; a list of mutually unique variables and the second of which, the
; body, is any value. (The body is usually an s-expression
; representing an Fexpress expression.) If the subforms do fit this
; format, returns a `parsed-lambda-args` struct carrying the number of
; arguments, the argument variable names, and the body. If they don't,
; an error attributed to the operation name given by `err-name` will
; be raised.
;
; Contract:
; (-> symbol? any/c parsed-lambda-args?)
;
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

; An fexpr implementing an interpreted lambda operation. This doesn't
; attempt to compile the body. The resulting function evaluates the
; body dynamically every time it's called.
;
; When calling this fexpr, the subforms should be parseable according
; to `parse-lambda-args`.
;
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
                     (at-variable/t+ arg-var
                       (specific-value/t+ arg-value)))))
               (type+-eval
                 (fexpress-eval/t+ body-env (done/ce (any-value/t_))
                                   body)))))]
        [_ (continuation-expr-continue-eval/t+ env cont op/t+)]))))

; (A helper for `fexpress-clambda`.)
;
; Compiles a lambda form into a `compilation-result?`. The resulting
; function is likely to be as fast as the equivalent Racket code
; unless it uses Fexpress features that inhibit compilation, in which
; case it falls back to interpreting the relevant Fexpress code.
;
; Contract:
; (-> env? continuation-expr? any/c compilation-result?)
;
; The `args` should be parseable according to `parse-lambda-args`. If
; they're not, an error attributed to the operation name "`clambda`"
; will be raised.
;
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
           (at-variable/t+ arg-var (any-value/t+)))
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
                      (,#'at-variable/t+ (,#'quote ,arg-var)
                        (,#'specific-value/t+
                          ,(var-representation-in-racket
                             arg-var)))))))])
         ,body-compiled)
      body-compiled))
  (define free-vars
    (for/fold ([free-vars body-free-vars])
              ([arg-var (in-list arg-vars)])
      (hash-remove free-vars arg-var)))
  (define lambda-compiled
    `(,#'lambda
       ,(for/list ([arg-var (in-list arg-vars)])
          (var-representation-in-racket arg-var))
       ,body-with-env-compiled))
  (compilation-result depends-on-env? free-vars lambda-compiled))

; An fexpr implementing a compiled lambda operation. This attempts to
; compile the body. The resulting function is likely to be as fast as
; the equivalent Racket code unless it uses Fexpress features that
; inhibit compilation, in which case it falls back to interpreting the
; relevant Fexpress code.
;
; When calling this fexpr, the subforms should be parseable according
; to `parse-lambda-args`.
;
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
             (const compiled-clambda)))]
        [_ (continuation-expr-continue-eval/t+ env cont op/t+)]))))



; ===== An fexpr for type ascription =================================

; An fexpr implementing a type ascription operation. The usage is
; `(the val/t_ val)`, where `val/t_` is syntactically a negative type
; (not just an expression that evaluates to one) and `val` is an
; expression the type applies to. The purpose of `the` is mainly to
; allow function bodies to use Lisp-1-style function application on
; local variables without inhibiting compilation.
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



; ===== The Fexpress entrypoint ======================================

; Contract:
; (-> (hash/c var? any/c) env?)
(define (env-of-specific-values specific-values)
  (for/fold ([env (hash)]) ([(var val) (in-hash specific-values)])
    (hash-set env var (at-variable/t+ var (specific-value/t+ val)))))

; Contract:
; (-> env? any/c any/c)
;
; The `expr` should be an s-expression of Fexpress code.
;
(define (fexpress-eval env expr)
  (type+-eval (fexpress-eval/t+ env (done/ce (any-value/t_)) expr)))
