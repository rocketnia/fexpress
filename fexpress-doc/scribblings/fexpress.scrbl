#lang scribble/manual

@; fexpress/scribblings/fexpress.scrbl
@;
@; Fexpress, a compilation-friendly fexpr language.

@;   Copyright 2021, 2023 The Fexpress Authors
@;
@;   Licensed under the Apache License, Version 2.0 (the "License");
@;   you may not use this file except in compliance with the License.
@;   You may obtain a copy of the License at
@;
@;       http://www.apache.org/licenses/LICENSE-2.0
@;
@;   Unless required by applicable law or agreed to in writing,
@;   software distributed under the License is distributed on an
@;   "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
@;   either express or implied. See the License for the specific
@;   language governing permissions and limitations under the License.


@(require
   (for-label
     (only-in racket/base
       + * add1 and apply boolean? define eval exact-integer? hash
       hash-ref identifier? lambda list map parameterize sqrt
       symbol?)))
@(require
   (for-label
     (only-in racket/contract/base
       -> any any/c hash/c listof parameter/c)))
@(require (for-label (only-in racket/pretty pretty-print)))
@(require (for-label (only-in racket/math natural?)))

@(require (for-label fexpress/proof-of-concept))

@(require (only-in scribble/example examples make-eval-factory))

@(define example-eval
   (make-eval-factory (list 'racket/base
                            'racket/pretty
                            'fexpress/proof-of-concept)))

@(define persistent-example-eval (example-eval))


@title{Fexpress}

Fexpress is a compilation-friendly @tech{fexpr} language. As far as feasible, it macroexpands expressions ahead of time instead of just interpreting everything.

At some point, there may be two variants of Fexpress.

The current variant---@racketmodname[fexpress/proof-of-concept]---is intended to help demonstrate the principles at work. For this reason, it has only a minimalistic set of features, it doesn't have deep library dependencies, and we haven't gone to any special effort to harden its API for future stability. If the concepts that need to be demonstrated change, we might add newly needed methods to some of the generic interfaces, might allow an @racket[env?] to be something more expressive or restrictive than a hash table, and so on.

The other variant of Fexpress---potentially the @tt{fexpress} module proper, once it exists---could be a more full-fledged system for using fexprs in Racket programs. This variant could better preserve Racket syntax object metadata for error reporting and Racket-style hygiene, and it could introduce features like editor highlighting to show what subexpressions of a program are making unoptimized fexpr calls. We can test the limits of how seamless an addition they can be to the Racket language.

However, there's a certain kind of seamlessness Fexpress won't attempt: Racket's @racket[and] can't be passed into Racket's @racket[map], and sometimes this surprises people who expect macros to act like functions. In languages with fexprs as the default abstraction, it tends to be easy to implement @racket[and] and @racket[map] in such a way that this interaction succeeds. However, that amounts to a much different design for these operations, and not a better one. If Racket's @racket[map] refuses to pass its internal code to an fexpr, that's good encapsulation of its implementation details. And Racket's @racket[and] is designed to operate on input that's an unevaluated syntax object (along with various macroexpansion-time parameters), so if the input it receives is actually a run-time collection of positional and keyword arguments, it's quite reasonable for it to reject that input as a likely mistake by the user. These would be good design choices even in a language that had fexprs in it, and we don't intend to circumvent them with Fexpress.

Anyhow, the Fexpress that exists now is the simplified proof of concept. Our hope is to demonstrate that a viable strategy exists for mixing fexprs with compilation. Thanks to extension points like @racket[gen:fexpr], it could be put to some fun use, but keep in mind the instability of the API.

(TODO: Currently, there isn't a dedicated operation for writing simple fexprs. Fexpress users can build one out of @racket[gen:fexpr], or just use @racket[makeshift-fexpr] in Fexpress code directly, but let's provide one at some point to ease the analogy between Fexpress and other fexpr-equipped languages.)



@table-of-contents[]



@section[#:tag "proof-of-concept"]{The Fexpress Proof of Concept}

@defmodule[fexpress/proof-of-concept]

This module provides an open-faced implementation of a minimalistic, experimental Fexpress language. Not all the contracts documented here are completely enforced, nor are they stable.

The building blocks provided here make the language capable of doing simple lambda calculus, with more or less efficiency depending on the use of @racket[fexpress-ilambda] or @racket[fexpress-clambda]. This language can be extended by implementing more @racket[gen:fexpr] values in Racket, and possibly more @racket[gen:continuation-expr], @racket[gen:type+], and @racket[gen:type_] values for them to interact with.


@subsection[#:tag "entrypoint"]{Entrypoint}

@defproc[(fexpress-eval [env env?] [expr any/c]) any/c]{
  Given an s-expression representing Fexpress code, return the result of evaluating it in the given @racket[env?].
  
  
  @examples[
    #:eval persistent-example-eval
    
    (define _test-env
      (env-of-specific-values
        (hash 'the fexpress-the
              'ilambda fexpress-ilambda
              'clambda fexpress-clambda
              'funcall (lambda (_f . _args) (apply _f _args))
              '+ +
              '* *)))
    
    (define (_logging _body)
      (parameterize ([current-fexpress-logger pretty-print])
        (_body)))
    
    (define (_fexpress-eval-and-log _expr)
      (_logging (lambda () (fexpress-eval _test-env _expr))))
    
    (_fexpress-eval-and-log
      '(+ 1 2))
    (_fexpress-eval-and-log
      '((ilambda (x y) (+ x y 3)) 1 2))
    (_fexpress-eval-and-log
      '((clambda (x y) (+ x y 3)) 1 2))
    (_fexpress-eval-and-log
      '(funcall
         (clambda (square)
           (funcall
             (clambda (double)
               (funcall double
                 (funcall double
                   (+ (funcall square 3) (funcall square 4)))))
             (clambda (x) (+ x x))))
         (clambda (x) (* x x))))
  ]
}

@defproc[
  (env-of-specific-values [specific-values (hash/c var? any/c)])
  env?
]{
  Creates an @racket[env?] from a hash that maps Fexpress variables to values.
  
  An @racket[env?] maps Fexpress variables to @tech{positive types} that compile to references to the same variables, so this wraps up the values in @racket[specific-value/t+] and sets up their compilation behavior with @racket[at-variable/t+].
}

@defthing[current-fexpress-logger (parameter/c (-> any/c any))]{
  A parameter holding a procedure that the Fexpress proof of concept uses to log diagnostic messages in s-expression form. Currently, we log two things:
  
  @itemlist[
    @item{Evaluation of Racket code, so that we can inspect what kind of Racket code Fexpress produces.}
    @item{Moments where the compiled Racket code reenters the interpreter in order to call an fexpr. These moments are worth knowing about so we can optimize them away.}
  ]
}


@subsection[#:tag "fexpr"]{Fexprs}

An @deftech{fexpr} (sometimes known as a @deftech{first-class macro}) is a kind of abstraction that's existed since the earliest implementations of Lisp.

An fexpr is something in between a function and a macro. Like a function, it's a first-class value that can do its work at run time. Like a macro, it receives its arguments unevaluated, and---at least in the better incarnations---it also receives some kind of access to its caller's local scope with which to understand these arguments' intended semantics.

This combination lets programmers express a few things that they can't express with functions and macros, since fexprs can compute their results based on a synthesis of run-time information and source code information.

However, this combination generally means programs can't be compiled effectively, because certain expressions need to be preserved as-is until run time. If a programmer wants to @emph{express} a compilable program, fexprs usually get in the way of that, and the combination of macros and functions is arguably more expressive than fexprs for that task.

The Fexpress proof of concept shows how to get around this limitation by giving fexprs even more information to work with. These fexprs receive a @tech{continuation expression} which contains a @tech{negative type} where they can find optimization hints to apply in their behavior.

There are also @tech{positive type} values, which are types that can perform some fexpr-calling behavior on behalf of their potential values. Positive types are the tool the fexpr evaluator needs to proceed into binding forms like @racket[fexpress-clambda] and implement some of their behavior early, before the actual values of the variables are known. With careful programming, the remaining part of the behavior is compiled code, allowing Fexpress to express compilable programs.

(TODO: How new are the things we're demonstrating here? Fexprs have been in active use in the newLISP, PicoLisp, and (arguably) R communities. There's been a lot of research on compiling reflective languages, as seen in "Collapsing Towers of Interpreters." There's also a potential connection to JIT in general, and possibly to the compilation of algebraic effect systems.)

@defproc[(fexpr? [v any/c]) boolean?]{
  Returns whether the given value is an Fexpress @tech{fexpr}.
}

@defthing[gen:fexpr any/c]{
  A generic interface for Fexpress @tech{fexprs}, which must implement the method @racket[fexpr-apply/t+].
}

@defproc[
  (fexpr-apply/t+ [env env?]
                  [cont continuation-expr?]
                  [val/t+ type+?]
                  [val fexpr?]
                  [args any/c])
  type+?
]{
  (Makes @tech{fexpr} calls, namely to the given one.) Returns a @tech{positive type} for the potential values which result from transforming the given positive type and the given value (an @racket[fexpr?]) of that type according to an fexpr call with the given arguments followed by the series of steps and the target @tech{negative type} listed in the given @tech{continuation expression}.
  
  There are many @tt{...-continue-eval/t+} and @tt{...-apply/t+} operations in Fexpress, and this is the one to call when the actual @emph{value} of the original type is known and is definitely an fexpr that is definitely being invoked.
  
  The given @racket[val/t+] type should be a type which evaluates to the value @racket[val].
}

@defproc[
  (makeshift-fexpr [apply/t+
                    (-> env? continuation-expr? type+? any/c type+?)])
  fexpr?
]{
  Returns an @tech{fexpr} that has the given behavior for @racket[fexpr-apply/t+].
  
  This may be more convenient than defining an instance of @racket[gen:fexpr].
}


@subsubsection[#:tag "fexprs-for-lambda"]{
  Fexprs for Lambda Operations
}

@defform[#:kind "fexpr" (fexpress-ilambda (arg-id ...) body-expr)]{
  An @tech{fexpr} implementing an interpreted @racket[lambda] operation. This doesn't attempt to compile the body. The resulting function evaluates the body dynamically every time it's called.

  When calling this fexpr, the subforms should be parseable according to @racket[parse-lambda-args].
}

@defform[#:kind "fexpr" (fexpress-clambda (arg-id ...) body-expr)]{
  An @tech{fexpr} implementing a compiled @racket[lambda] operation. This attempts to compile the body. The resulting function is likely to be as fast as the equivalent Racket code unless it uses Fexpress features that inhibit compilation, in which case it falls back to interpreting the relevant Fexpress code.

  When calling this fexpr, the subforms should be parseable according to @racket[parse-lambda-args].
}

@defproc[
  (parse-lambda-args [err-name symbol?] [args any/c])
  parsed-lambda-args?
]{
  Asserts that the given subforms are in the format expected for an @racket[fexpress-ilambda] or @racket[fexpress-clambda] form---namely, a list of two elements, the first of which is a list of mutually unique variables and the second of which, the body, is any value. (The body is usually an s-expression representing an Fexpress expression.) If the subforms do fit this format, returns a @racket[parsed-lambda-args] struct carrying the number of arguments, the argument variable names, and the body. If they don't, an error attributed to the operation name given by @racket[err-name] will be raised.
}

@defstruct*[
  parsed-lambda-args
  ([n natural?] [arg-vars (listof var?)] [body any/c])
]{
  A return value of @racket[parse-lambda-args].
  
  The number @racket[_n] should be the length of @racket[_arg-vars].
  
  The @racket[_arg-vars] should be mutually unique.

  The @racket[_body] should be an s-expression representing an Fexpress expression.
}


@subsubsection[#:tag "an-fexpr-for-type-ascription"]{
  An Fexpr for Type Ascription
}

@defform[#:kind "fexpr" (fexpress-the val/t_ val-expr)]{
  An @tech{fexpr} implementing a type ascription operation. The subform @racket[val/t_] must be a @tech{negative type} syntactically, not just an expression that evaluates to one. The subform @racket[val-expr] is an expression the type applies to. The purpose of @tt{fexpress-the} is mainly to allow function bodies to use Lisp-1-style function application on local variables without inhibiting compilation.
  
  As the following example shows, it's possible to use @tt{fexpress-the} to declare that the local variables @racket[_f] and @racket[_g] are non-@tech{fexprs}. This allows their use sites to be compiled into procedure calls rather than less efficient fexpr calls:
  
  @examples[
    #:label #f
    #:eval persistent-example-eval
    
    (define _my-compose
      (_fexpress-eval-and-log
        `(the ,(->/t_ (list (non-fexpr-value/t+))
                 (->/t_ (list (non-fexpr-value/t+))
                   (any-value/t_)))
           (clambda (f)
             (clambda (g)
               (clambda (x)
                 (f (g x))))))))
    
    (_logging (lambda () (((_my-compose sqrt) add1) 8)))
  ]
  
  If we don't declare that @racket[_g] is a non-fexpr, what happens is that the call to @racket[_g] is compiled into an invocation of the Fexpress interpreter. In order to pass a lexical environment into that interpreter, each surrounding @racket[fexpress-clambda] (or similar binding syntax) updates the local binding of @tt{env} so that the bindings held in @tt{env} always correspond to the lexical scope:
  
  @examples[
    #:label #f
    #:eval persistent-example-eval
    
    (define _my-less-typed-compose
      (_fexpress-eval-and-log
        `(the ,(->/t_ (list (non-fexpr-value/t+))
                 (->/t_ (list (any-value/t+))
                   (any-value/t_)))
           (clambda (f)
             (clambda (g)
               (clambda (x)
                 (f (g x))))))))
    
    (_logging (lambda () (((_my-less-typed-compose sqrt) add1) 8)))
  ]
  
  If we don't use @tt{fexpress-the} at all, then we get the least optimized version of the code. This time, the call to @racket[_f] reenters the interpreter, and the call to @racket[_g] is just taken care of during that interpretation:
  
  @examples[
    #:label #f
    #:eval persistent-example-eval
    
    (define _my-untyped-compose
      (_fexpress-eval-and-log
        `(clambda (f)
           (clambda (g)
             (clambda (x)
               (f (g x)))))))
    
    (_logging (lambda () (((_my-untyped-compose sqrt) add1) 8)))
  ]
}


@subsection[#:tag "continuation-expr"]{Continuation Expressions}

An Fexpress @deftech{continuation expression} is a representation of the syntax around the evaluating part of an Fexpress expression.

Usually, this is a series of pending @tech{fexpr} applications (@racket[apply/ce]) to perform in the current @racket[env?], followed by an ascribed @tech{negative type} to optimize the overall result by (@racket[done/ce]). Other kinds of copatterns or spine elements, like field or method accessor syntaxes, could fit in here as well.

@defproc[(continuation-expr? [v any/c]) boolean?]{
  Returns whether the given value is a @tech{continuation expression}.
}

@defthing[gen:continuation-expr any/c]{
  A generic interface for @tech{continuation expressions}, which must implement the method @racket[continuation-expr-continue-eval/t+].
  
  In order to perform compilation, Fexpress @tech{fexprs} usually need to know the structural details of the continuation expression that holds their arguments. Thus, when defining new continuation expressions, it's typical to define a structure type that does more than just implement the @racket[gen:continuation-expr] interface. For instance, it can also provide its predicate and field accessors as part of its intended API, or it can implement other interfaces on the side.
}

@defproc[
  (continuation-expr-continue-eval/t+ [env env?]
                                      [cont continuation-expr?]
                                      [val/t+ type+?])
  type+?
]{
  (Makes @tech{fexpr} calls.) Assuming the given @tech{positive type} will have no known fexpr-calling behavior until we witness its potential values, returns another positive type for the potential values which result from transforming those according to the series of steps and the target @tech{negative type} listed in the given @tech{continuation expression}.
  
  There are many @tt{...-continue-eval/t+} and @tt{...-apply/t+} operations in Fexpress, and this is the one to call when the positive type's fexpr-calling behavior should be ignored but its values' fexpr-calling behavior, if any, should not be ignored. This will usually result in code that consults the value at run time and makes fexpr calls to it dynamically. A positive type usually delegates to this itself when its @racket[type+-continue-eval/t+] behavior has no better idea for what to do.
}


@subsubsection[#:tag "essential-continuation-exprs"]{
  Essential Continuation Expressions
}

@defstruct*[done/ce ([type_ type_?])]{
  A @tech{continuation expression} that represents that there's nothing left to do except return a value. The specified @tech{negative type} can serve as a hint for optimizing the value.
}

@defstruct*[apply/ce ([args any/c] [next continuation-expr?])]{
  A @tech{continuation expression} that represents that the next thing to do to the value is to invoke it as an @tech{fexpr} with certain arguments.
  
  In typical code, the @racket[_args] to an fexpr call are usually a proper list.
}


@subsection[#:tag "type+"]{Positive Types}

A @deftech{positive type} in Fexpress essentially acts like a symbolic value. Like other type systems, this kind of type designates a set of potential values. Depending on what assumptions it carries, it can produce a value (@racket[type+-eval]) and/or a @racket[compilation-result?] that evaluates to a value (@racket[type+-compile]).

The type system in the Fexpress proof of concept exists only for the purpose of optimization, and it has only the bells and whistles that serve that purpose. In particular, this type system makes no attempt to be sound. A variable associated with a positive type can turn out to have a value that defies that type's assumptions or has been computed in a different way than the type would have computed it.

@defproc[(type+? [v any/c]) boolean?]{
  Returns whether the given value is a @tech{positive type}.
}

@defthing[gen:type+ any/c]{
  A generic interface for @tech{positive types}, which must implement the following methods:
  
  @itemlist[
    @item{@racket[type+-eval]}
    @item{@racket[type+-compile]}
    @item{@racket[at-variable/t+]}
    @item{@racket[type+-continue-eval/t+]}
  ]
  
  The implementations of these methods should satisfy certain algebraic laws:
  
  If both @racket[type+-eval] and @racket[type+-compile] both successfully produce results and don't perform any side effects along the way, the evaluation result should be the same as running the compilation result with @racket[compilation-result-eval] in any @racket[env?] where the bindings for its free variables have their own successful and pure @racket[type+-eval] and @racket[type+-compile] behaviors.
  
  The @racket[at-variable/t+] method should observe the lens laws with respect to @racket[type+-compile]: The result of getting a compilation result with @racket[type+-compile] after it's been replaced with @racket[at-variable/t+] should be the same as just calling @racket[var-compile] on the variable that was passed to the replacer. The result of replacing a compilation result with itself should be the same as not using @racket[at-variable/t+] at all. The result of replacing a compilation result and replacing it a second time should be the same as just skipping to the second replacement.
}

@defproc[(type+-eval [type+ type+?]) any/c]{
  Attempt to compute a value of the given @tech{positive type}.
}

@defproc[(type+-compile [type+ type+?]) compilation-result?]{
  Attempt to produce a @racket[compilation-result?] that evaluates to values of the given @tech{positive type} in the @racket[env?] the type belongs to.
}

@defproc[(at-variable/t+ [var var?] [type+ type+?]) type+?]{
  Replaces the given @tech{positive type}'s compilation result so that it refers to the given Fexpress variable. The variable's potential bindings must be among the type's potential values, but nothing is done to verify this.
  
  Any type that's added to an @racket[env?] should be transformed this way, since it's now in scope under a dedicated name.
}

@defproc[
  (type+-continue-eval/t+ [env env?]
                          [cont continuation-expr?]
                          [type+ type+?])
  type+?
]{
  (Makes @tech{fexpr} calls.) Returns a @tech{positive type} for the potential values which result from transforming the given @tech{positive type} according to a series of steps and a target @tech{negative type} listed in the given @tech{continuation expression}.
  
  There are many @tt{...-continue-eval/t+} and @tt{...-apply/t+} operations in Fexpress, and this is the most general one; it delegates to the others.
}

@defproc[
  (lazy-value/t+ [eval (-> any/c)] [compile (-> compilation-result?)])
  type+?
]{
  Returns a @tech{positive type} with the given implementations of @racket[type+-eval] and @racket[type+-compile]. These should satisfy the algebraic laws described at @racket[gen:type+].
  
  The resulting type doesn't carry any assumptions about the potential values' @tech{fexpr}-calling behavior. That is to say, its @racket[type+-continue-eval/t+] behavior only gives up and delegates to @racket[continuation-expr-continue-eval/t+].
}


@subsubsection[#:tag "essential-positive-types"]{
  Essential Positive Types
}

@defproc[(any-value/t+) type+?]{
  Returns a @tech{positive type} which carries no assumptions about its potential values.
}

@defproc[(non-fexpr-value/t+) type+?]{
  Returns a @tech{positive type} which carries an assumption that its potential values will not be @racket[fexpr?] values. This isn't necessarily a sound assumption, but certain operations will use this information to allow compilation to proceed even if a value of this type is invoked like an @tech{fexpr}.
}

@defproc[(specific-value/t+ [value any/c]) type+?]{
  Returns a @tech{positive type} which carries an assumption that its potential values will all be the given value. It can also @racket[type+-eval] to that value.
}


@subsection[#:tag "type_"]{Negative Types}

A @deftech{negative type} in Fexpress essentially acts like an optimization hint for compiling an expression of that type.

@defproc[(type_? [v any/c]) boolean?]{
  Returns whether the given value is a @tech{negative type}.
}

@defthing[gen:type_ any/c]{
  A generic interface for @tech{negative types}. This interface doesn't have any methods. (It's not that it couldn't have methods, but we don't seem to need any for this proof of concept.)
  
  In order to perform compilation, Fexpress @tech{fexprs} sometimes need to know the structural details of the negative type they're expected to create a value in. Thus, when defining new negative types, it's typical to define a structure type that does more than just implement the @racket[gen:type_] interface. For instance, it can also provide its predicate and field accessors as part of its intended API, or it can implement other interfaces on the side.
}


@subsubsection[#:tag "essential-negative-types"]{
  Essential Negative Types
}

@defstruct*[any-value/t_ ()]{
  A @tech{negative type} which provides no hints as to what its potential values should be like.
}

@defstruct*[
  ->/t_
  ([arg-type+-list (listof type+?)] [return/t_ type_?])
]{
  A @tech{negative type} for functions that have the specified list of @tech{positive types} for their arguments and the single specified negative type for their results.
  
  If we unpack the meaning of positive and negative types in Fexpress, this is a compilation hint for expressions that return functions. It offers the given symbolic values as approximations for the function arguments, and it offers further hints for compiling the function body.
}


@subsection[#:tag "phases"]{Phases of the Language}


@subsubsection[#:tag "representing-source"]{Representing Concepts in the Source}

@defproc[(var? [v any/c]) boolean?]{
  Returns whether the given value is an Fexpress variable name, which is represented by an interned symbol.
}

@defproc[(env? [v any/c]) boolean?]{
  Returns whether the given value is an Fexpress lexical environment, which is represented by an immutable hash from variable names to @tech{positive types}. Besides being positive types, the values of the hash should also have successful @racket[type+-compile] behavior, and they should be equivalent to @racket[var-compile] for the same Fexpress variable.
}

@defproc[(free-vars? [v any/c]) boolean?]{
  Returns whether the given value is an Fexpress free variable set, which is represented by an immutable hash from variable names to @racket[#t].
}

@defproc[(env-get/t+ [env env?] [var var?]) type+?]{
  Gets the @tech{positive type} associated with the given variable name in the given environment. Unlike simply calling @racket[hash-ref], this raises an informative error if the variable doesn't have a binding in the environment.
}


@subsubsection[#:tag "evaluator-compiler"]{The Combination Evaluator-Compiler}

@defproc[
  (fexpress-eval/t+ [env env?] [cont continuation-expr?] [expr any/c])
  type+?
]{
  Reduces the given Fexpress expression and @tech{continuation expression} in the given @racket[env?] to a @tech{positive type}. The resulting positive type can be transformed into an evaluated result using @racket[type+-eval] or a compiled result using @racket[type+-compile].
}

@defproc[(literal? [v any/c]) boolean?]{
  Returns whether the given value can be used as a datum literal in the Fexpress proof of concept. For this simple demonstration, we just support @racket[exact-integer?] values.
}

@defproc[
  (unknown-non-fexpr-apply/t+ [env env?]
                              [cont continuation-expr?]
                              [op/t+ type+?]
                              [get-op (-> any/c)]
                              [args any/c])
  type+?
]{
  (Makes @tech{fexpr} calls, namely to an assumed non-fexpr value.) Returns a @tech{positive type} for the potential values which result from transforming the given positive type and the given function (for getting the value of that type) according to a @emph{procedure} call with the evaluated forms of the given arguments, followed by the series of additional steps and the target negative type listed in the given @tech{continuation expression}.
  
  There are many @tt{...-continue-eval/t+} and @tt{...-apply/t+} operations in Fexpress, and this is the one to call when a type's potential values are assumed not to be fexprs and yet they're definitely being invoked with an fexpr call. This is called either when a value turns out to be a non-fexpr at run time or when it's assumed to be a non-fexpr using @racket[non-fexpr-value/t+].
  
  The given @racket[op/t+] type should be a type which evaluates to the result of @racket[get-op].
  
  In typical code, the @racket[args] to an fexpr call are usually a proper list. This operation raises an error if they're not.
}

@defproc[
  (specific-value-continue-eval/t+ [env env?]
                                   [cont continuation-expr?]
                                   [val/t+ type+?]
                                   [val any/c])
  type+?
]{
  (Makes @tech{fexpr} calls.) Returns a @tech{positive type} for the potential values which result from transforming the given positive type and the given value of that type according to the series of steps and the target @tech{negative type} listed in the given @tech{continuation expression}.
  
  There are many @tt{...-continue-eval/t+} and @tt{...-apply/t+} operations in Fexpress, and this is the one to call when the actual @emph{value} being called is known and can potentially be an fexpr with its own idea of how to proceed. A positive type processing a @racket[type+-continue-eval/t+] call usually delegates to this itself when the type's value is known at compile time, and a continuation expression processing a @racket[continuation-expr-continue-eval/t+] call usually delegates to this itself once the value is finally known at run time.
  
  The given @racket[val/t+] type should be a type which evaluates to the value @racket[val].
}

@defproc[
  (non-fexpr-continue-eval/t+ [env env?]
                              [cont continuation-expr?]
                              [val/t+ type+?])
  type+?
]{
  (Makes @tech{fexpr} calls.) Assuming the given @tech{positive type} and its values have no custom fexpr-calling behavior, returns a positive type for the potential values which result from transforming the given one according to the series of steps and the target @tech{negative type} listed in the given @tech{continuation expression}.
  
  There are many @tt{...-continue-eval/t+} and @tt{...-apply/t+} operations in Fexpress, and this is the one to call when the positive type @emph{and} its values should have their custom fexpr-calling behavior ignored. Fexpress doesn't usually ignore values' fexpr-calling behavior like this, but since this can lead to better performance, it can be explicitly requested by using @racket[(fexpress-the _...)] to ascribe a type that uses @racket[non-fexpr-value/t+].
}


@subsubsection[#:tag "compiling-to-racket"]{Compiling to Racket}

@defproc[(var-representation-in-racket [var var?]) symbol?]{
  Converts an Fexpress variable name into the symbol it should be represented as in compiled Racket code for @racket[compilation-result?] values. Currently, it's the same symbol but with @racket["-"] prepended to it.
}

@defstruct*[
  compilation-result
  ([depends-on-env? boolean?] [free-vars free-vars?] [expr any/c])
]{
  A bundle containing an s-expression ready to compile as Racket code and some information about its dependencies. If it depends on the variable @tt{env} being bound to a first-class representation of the entire lexical environment, the @racket[_depends-on-env?] field should be @racket[#t]. If it depends on Fexpress variables, those should be accounted for in the @racket[_free-vars] field.
  
  The @racket[_expr] should be an s-expression of Racket code. It may have free variables corresponding to the @racket[var-representation-in-racket] versions of the Fexpress free variables listed in @racket[_free-vars]. It may also have the free variable @tt{env} if @racket[_depends-on-env?] is @racket[#t]. The @tt{env} variable refers to the current lexical environment. It should not have other free variables, but if it needs to refer to Racket module bindings, it may do so with an embedded @racket[identifier?] syntax object.
  
  Depending on the lexical environment using @racket[_depends-on-env?] can lead to performance degradation in the surrounding parts of the Fexpress program, since an up-to-date first-class environment value must be constructed whenever variables come into scope.
  
  While we could make more extensive use of Racket syntax objects, we keep their use to a minimum here to demonstrate this language in a way that can be easily ported to other Lisp dialects and other languages with @racket[eval] variants available.
}

@defproc[(var-compile [var var?]) compilation-result?]{
  Compiles an expression that just refers to the given Fexpress variable.
}

@defproc[
  (compilation-result-eval [env env?] [compiled compilation-result?])
  any/c
]{
  Evaluates the given Fexpress compilation result, using the given Fexpress @racket[env?] to resolve its references to free variables. This uses Racket's @racket[eval], which fully compiles the Racket code before executing it.
}
