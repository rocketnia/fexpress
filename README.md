# Fexpress

[![CI](https://github.com/rocketnia/fexpress/actions/workflows/ci.yml/badge.svg)](https://github.com/rocketnia/fexpress/actions/workflows/ci.yml)

Fexprs are well-known to make compilation difficult in the general case. If the behavior of an abstraction can depend on the combination of run-time information and the exact source code the abstraction was called with, then some of the source code must survive as-is until run time.

*Some* of the source code. With Fexpress, we demonstrate that by adding cetain features to fexprs, we can compile code that doesn't depend on dynamic fexpr use:

```racket
> (define test-env
    (env-of-specific-values
      (hashalw
        'the fexpress-the
        'ilambda fexpress-ilambda
        'clambda fexpress-clambda
        'funcall (lambda (f . args) (apply f args))
        '+ +
        '* *)))
> (define (logging body)
    (parameterize ([current-fexpress-logger pretty-print])
      (body)))
> (define (fexpress-eval-and-log expr)
    (logging (lambda () (fexpress-eval test-env expr))))
> (fexpress-eval-and-log
    '(funcall
       (clambda (square)
         (funcall
           (clambda (double)
             (funcall double
               (funcall double
                 (+ (funcall square 3) (funcall square 4)))))
           (clambda (x) (+ x x))))
       (clambda (x) (* x x))))
'("Evaluating Racket code:"
  (lambda (env -funcall -+)
    (lambda (-square)
      (#%app
       -funcall
       (lambda (-double)
         (#%app
          -funcall
          -double
          (#%app
           -funcall
           -double
           (#%app
            -+
            (#%app -funcall -square (#%datum . 3))
            (#%app -funcall -square (#%datum . 4))))))
       (lambda (-x) (#%app -+ -x -x))))))
'("Evaluating Racket code:" (lambda (env -*) (lambda (-x) (#%app -* -x -x))))
100
```

The above code only invoked global variables, and those global variables were procedures and a certain fexpr (`fexpr-clambda`) which implemented its own compilation support, so the result was fully compiled code.

To invoke only global variables, that code uses a Lisp-2-style `funcall` operation. If it had invoked the local variables directly, Lisp-1 style, Fexpress's implementation wouldn't figure out that they weren't fexprs, so it would have generated code that called back into the interpreter for those calls.

But Fexpress shows off another solution for that. Using rudimentary type annotations, even the Lisp-1 style can turn into efficient code:

```racket
> (define my-compose
    (fexpress-eval-and-log
      `(the ,(->/t_ (list (non-fexpr-value/t+))
               (->/t_ (list (non-fexpr-value/t+))
                 (any-value/t_)))
         (clambda (f)
           (clambda (g)
             (clambda (x)
               (f (g x))))))))
'("Evaluating Racket code:"
  (lambda (env)
    (lambda (-f) (lambda (-g) (lambda (-x) (#%app -f (#%app -g -x)))))))
> (logging (lambda () (((my-compose sqrt) add1) 8)))
3
```

For more information on the way Fexpress is built, what extension points and building blocks it has available, and where it might go from here, [see the documentation](http://docs.racket-lang.org/fexpress/index.html).

The current incarnation of Fexpress is merely a proof of concept. We've prioritized simple and direct implementation to demonstrate the concepts, and the API may be unstable as a result. This version will stick around and keep serving as a demonstration, but we also envision making a more full-featured and stable Fexpress alongside it.


## Installation and use

This is a library for Racket. To install it from the Racket package index, run `raco pkg install fexpress`. Then you can put an import like `(require fexpress/proof-of-concept)` in your Racket program.

To install it from source, run `raco pkg install` from the `fexpress-lib/` directory.

[Documentation for Fexpress](http://docs.racket-lang.org/fexpress/index.html) is available at the Racket documentation website, and it's maintained in the `fexpress-doc/` directory.
