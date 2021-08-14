# Fexpress

[![CI](https://github.com/rocketnia/fexpress/actions/workflows/ci.yml/badge.svg)](https://github.com/rocketnia/fexpress/actions/workflows/ci.yml)

Fexprs are well-known to make compilation difficult in the general case. If the behavior of an abstraction could depend on the combination of run-time information and the exact source code the abstraction was called with, then the source code must survive as-is until run time.

Fexpress takes a simple approach: Fexpress's operations provide both a way to compile their calls macro-style (if possible) and a way to interpret their calls fexpr-style. Most operations in Fexpress support compilation, so fexprs are only an occasional fallback. Even when an expression is being interpreted, most Fexpress operations compile any computations they might repeat (like lambda or loop bodies), so falling back to interpretation doesn't mean the program has to stay there.

Fexpress's compiler may not be sophisticated enough to optimize hallmark examples of fexpr programming. Instead of using the full breadth of what fexprs have to offer or resembling programs in other fexpr languages, Fexpress programs are likely to mainly use other techniques that support better optimization.


## Installation and use

This is a library for Racket. To install it from the Racket package index, run `raco pkg install fexpress`. Then you can put an import like `(require fexpress/proof-of-concept)` in your Racket program.

To install it from source, run `raco pkg install` from the `fexpress-lib/` directory.

[Documentation for Fexpress](http://docs.racket-lang.org/fexpress/index.html) is available at the Racket documentation website, and it's maintained in the `fexpress-doc/` directory.
