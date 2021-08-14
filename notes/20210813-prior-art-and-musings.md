# Prior art and musings

There have been approaches that make fexprs tamer.

* Kernel is a language that allows fexprs to have lexical scope, unlike the traditional dynamically scoped Lisp dialects fexprs originated in. It does this by explicitly passing them the caller's lexical environment so they can evaluate their arguments in that scope.

* A topic that often comes up with fexprs is partial evaluation. I'm not aware of specific projects that succeed at this.

I've occasionally tried to tackle this. As early as November 14, 2009, in [my 7th Arc Forum comment ever](http://arclanguage.org/item?id=10739) -- nostalgic -- I was proposing combining fexprs with static types to be able to optimize them. On November 13, 2011, I started up this repo with an attempt to write a partial evaluator.
