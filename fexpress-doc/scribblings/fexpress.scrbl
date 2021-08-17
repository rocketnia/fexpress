#lang scribble/manual

@; fexpress/scribblings/fexpress.scrbl
@;
@; Fexpress, a compilation-friendly fexpr language.

@;   Copyright 2021 The Fexpress Authors
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
       + * apply boolean? define exact-integer? hash lambda list
       symbol?)))
@(require
   (for-label (only-in racket/contract/base any/c hash/c listof)))
@(require (for-label (only-in racket/math natural?)))

@(require (for-label fexpress/proof-of-concept))

@(require (only-in scribble/example examples make-eval-factory))

@(define example-eval
   (make-eval-factory (list 'racket/base 'fexpress/proof-of-concept)))


@title{Fexpress}

Fexpress is a compilation-friendly fexpr language. As far as feasible, it macroexpands expressions ahead of time instead of just interpreting everything.

At some point, there may be two variants of Fexpress: a minimalistic and unstable version for ease of understanding the internals, and a more full-featured version for convenient integration of fexprs with Racket programming. For now, only the first exists.

(TODO: Finish documenting it.)

(TODO: Currently, there isn't actually an operation for writing simple fexprs. Fexpress users can build one, but let's have one that's built in.)



@table-of-contents[]



@section[#:tag "proof-of-concept"]{The Fexpress Proof of Concept}

@defmodule[fexpress/proof-of-concept]

This module provides an open-faced implementation of a minimalistic, experimental Fexpress language. Not all the contracts are completely enforced, nor are they stable.

The building blocks provided here make the language capable of doing simple lambda calculus, with more or less efficiency. It can be extended by writing more @racket[fexpr?] values.


@subsection[#:tag "entrypoint"]{Entrypoint}

@defproc[(fexpress-eval [env env?] [expr any/c]) any/c]{
  Given an s-expression representing Fexpress code, return the result of evaluating it in the given @racket[env?].
  
  
  @examples[
    #:eval (example-eval)
    
    (define _test-env
      (env-of-specific-values
        (hash 'the fexpress-the
              'ilambda fexpress-ilambda
              'clambda fexpress-clambda
              'funcall (lambda (_f . _args) (apply _f _args))
              '+ +
              '* *)))
    
    (fexpress-eval _test-env
      '(+ 1 2))
    (fexpress-eval _test-env
      '((ilambda (x y) (+ x y 3)) 1 2))
    (fexpress-eval _test-env
      '((clambda (x y) (+ x y 3)) 1 2))
    (fexpress-eval _test-env
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


@subsection[#:tag "fexprs"]{Fexprs}

@defproc[(fexpr? [v any/c]) boolean?]{
  Returns whether the given value is an Fexpress fexpr.
}

@defthing[gen:fexpr any/c]{
  A generic interface for Fexpress fexprs, which must implement the method @racket[fexpr-continue-eval/t+].
}

@defproc[
  (fexpr-continue-eval/t+ [env env?]
                          [cont continuation-expr?]
                          [val/t+ type+?]
                          [val fexpr?])
  type+?
]{
  (Calls fexprs, namely the given one.) Returns a @tech{positive type} for the potential values which result from transforming the given singleton positive type and its given value (an fexpr) according to the series of steps and the target @tech{negative type} listed in the given @tech{continuation expression}.
  
  There are many @tt{...-continue-eval/t+} operations in Fexpress, and this is the one to call when the actual @emph{value} of the original type is known and is definitely an fexpr. The fexpr can implement its own operation-specific behavior here, or it can dispatch again to @racket[continuation-expr-continue-eval/t+] to handle a continuation expression it doesn't know how to interpret itself.
  
  The given @racket[val/t+] type should be a type which evaluates to the value @racket[val].
}

@defproc[
  (makeshift-fexpr [continue-eval/t+
                    (-> env? continuation-expr? type+? type+?)])
  fexpr?
]{
  Returns an Fexpress fexpr that has the given behavior for @racket[fexpr-continue-eval/t+].
  
  This may be more convenient than defining an instance of @racket[gen:fexpr].
}


@subsubsection[#:tag "fexprs-for-lambda"]{
  Fexprs for Lambda Operations
}

@defform[#:kind "fexpr" (fexpress-ilambda (arg-id ...) body-expr)]{
  An Fexpress @racket[fexpr?] implementing an interpreted @racket[lambda] operation. This doesn't attempt to compile the body. The resulting function evaluates the body dynamically every time it's called.

  When calling this fexpr, the subforms should be parseable according to @racket[parse-lambda-args].
}

@defform[#:kind "fexpr" (fexpress-clambda (arg-id ...) body-expr)]{
  An Fexpress @racket[fexpr?] implementing a compiled @racket[lambda] operation. This attempts to compile the body. The resulting function is likely to be as fast as the equivalent Racket code unless it uses Fexpress features that inhibit compilation, in which case it falls back to interpreting the relevant Fexpress code.

  When calling this fexpr, the subforms should be parseable according to @racket[parse-lambda-args].
}

@defproc[
  (parse-lambda-args [err-name symbol?] [args any/c])
  parsed-lambda-args?
]{
  Asserts that the given subforms are in the format expected for an @racket[fexpress-ilambda] or @racket[fexpress-clambda] form---namely, a list of two elements, the first of which is a list of mutually unique variables and the second of which, the body, is any value. (The body is usually an s-expression representing an Fexpress expression.) If the subforms do fit this format, returns a @racket[parsed-lambda-args] struct carrying the number of arguments, the argument variable names, and the body. If they don't, an error attributed to the operation name given by `err-name` will be raised.
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
  An Fexpress @racket[fexpr?] implementing a type ascription operation. The subform @racket[val/t_] must be a @tech{negative type} syntactically, not just an expression that evaluates to one. The subform @racket[val-expr] is an expression the type applies to. The purpose of @tt{fexpress-the} is mainly to allow function bodies to use Lisp-1-style function application on local variables without inhibiting compilation.
  
  
  @examples[
    #:eval (example-eval)
    
    (define _test-env
      (env-of-specific-values
        (hash 'the fexpress-the
              'ilambda fexpress-ilambda
              'clambda fexpress-clambda
              'funcall (lambda (_f . _args) (apply _f _args))
              '+ +
              '* *)))
    
    (define _my-compose
      (fexpress-eval _test-env
        `(the ,(->/t_ (list (non-fexpr-value/t+))
                 (->/t_ (list (non-fexpr-value/t+))
                   (any-value/t_)))
           (clambda (f)
             (clambda (g)
               (clambda (x)
                 (f (g x))))))))
    
    (((_my-compose (lambda (_x) (+ 2 _x))) (lambda (_x) (+ 3 _x))) 1)
  ]
  
  (TODO: Demonstrate that the above example is able to compile without being inhibited by dynamic fexpr features.)
}


@subsection[#:tag "evaluating-and-compiling"]{Evaluating and Compiling}

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
                              [val-to-eval/t+ type+?]
                              [val-to-compile/t+ type+?]
                              [args any/c])
  type+?
]{
  Given unevaluated arguments, performs a Racket-like procedure call behavor, which first evaluates the arguments. This is a fallback for when a value that's called like an fexpr turns out to be a general Racket value rather than an Fexpress @racket[fexpr?].
  
  The @racket[val-to-eval/t+] type will only be used for its @racket[type+-eval] behavior. The @racket[val-to-compile/t+] type will only be used for its @racket[type+-compile] behavior. These can be the same type.
  
  In typical code, the @racket[args] to an fexpr call are usually a proper list. This operation raises an error if they're not.
}

@defproc[
  (specific-value-continue-eval/t+ [env env?]
                                   [cont continuation-expr?]
                                   [val/t+ type+?]
                                   [val any/c])
  type+?
]{
  (Calls fexprs.) Returns a @tech{positive type} for the potential values which result from transforming the given singleton positive type and its given value according to the series of steps and the target @tech{negative type} listed in the given @tech{continuation expression}.
  
  There are many @tt{...-continue-eval/t+} operations in Fexpress, and this is the one to call when the actual @emph{value} of the original type is known and can potentially be an fexpr with its own idea of how to proceed. A positive type processing a @racket[type+-continue-eval/t+] call usually dispatches to this itself when the type's value is known at compile time, and a continuation expression processing a @racket[continuation-expr-continue-eval/t+] call usually dispatches to this itself once the value is finally known at run time.
  
  The given @racket[val/t+] type should be a type which evaluates to the value @racket[val].
}

@defproc[
  (non-fexpr-continue-eval/t+ [env env?]
                              [cont continuation-expr?]
                              [val/t+ type+?])
  type+?
]{
  (Calls fexprs.) Assuming the given @tech{positive type} and its values have no custom fexpr-calling behavior, returns a positive type for the potential values which result from transforming the given one according to the series of steps and the target @tech{negative type} listed in the given @tech{continuation expression}.
  
  There are many @tt{...-continue-eval/t+} operations in Fexpress, and this is the one to call when the positive type @emph{and} its values should have their custom fexpr-calling behavior ignored. Fexpress doesn't usually ignore values' fexpr-calling behavior like this, but since this can lead to better performance, it can be explicitly requested by using @racket[(fexpress-the _...)] to ascribe a type that uses @racket[non-fexpr-value/t+].
}


@subsection[#:tag "contracts"]{Contracts}

@defproc[(var? [v any/c]) boolean?]{
  Returns whether the given value is an Fexpress variable name, which is represented by an interned symbol.
}

@defproc[(env? [v any/c]) boolean?]{
  Returns whether the given value is an Fexpress lexical environment, which is represented by an immutable hash from variable names to @tech{positive types}. Besides being positive types, the values of the hash should also have successful @racket[type+-compile] behavior, and they should be equivalent to @racket[var-compile] for the same Fexpress variable.
}

@defproc[(free-vars? [v any/c]) boolean?]{
  Returns whether the given value is an Fexpress free variable set, which is represented by an immutable hash from variable names to @racket[#t].
}
