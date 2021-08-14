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


@(require (for-label (only-in racket/contract/base any/c)))

@(require (for-label fexpress/proof-of-concept))

@(require (only-in scribble/example examples make-eval-factory))

@(define example-eval
   (make-eval-factory (list 'racket/base 'fexpress/proof-of-concept)))


@title{Fexpress}

Fexpress is a compilation-friendly fexpr language. As far as feasible, it macroexpands expressions ahead of time instead of just interpreting everything. Currently, the macroexpandable part includes a subset with the operations of lambda calculus (variable references, application, and lambda abstraction).

TODO: Currently, there isn't actually a way to write fexprs, at least not in the public API.

TODO: Currently, the public API is completely unstable... and not very powerful.



@table-of-contents[]



@section[#:tag "proof-of-concept"]{Proof of concept}

@defmodule[fexpress/proof-of-concept]

This module provides a single entrypoint into a minimalistic, experimental Fexpress language. At this point, it can basically only do simple lambda calculus, with more or less efficiency.

TODO: Let it express more things.


@defproc[(fexpress-eval-in-base-env [v any/c]) any/c]{
  Given an s-expression, return the result of evaluating it as an Fexpress program.
  
  
  @examples[
    #:eval (example-eval)
    
    (fexpress-eval-in-base-env
      '(+ 1 2))
    (fexpress-eval-in-base-env
      '((ilambda (x y) (+ x y 3)) 1 2))
    (fexpress-eval-in-base-env
      '((clambda (x y) (+ x y 3)) 1 2))
    (fexpress-eval-in-base-env
      '(app
         (clambda (square)
           (app
             (clambda (double)
               (app double
                 (app double (+ (app square 3) (app square 4)))))
             (clambda (x) (+ x x))))
         (clambda (x) (* x x))))
  ]
}
