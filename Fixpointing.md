1. The reason Haskell's `Fix` is convenient is because it lets one use a single `cata` applicable to all recursive types produced with Fix.

1. Now, it's possible to write non-general catamorphisms for Coq recursive types, but that'll be inconvenient as soon as you have more than one.

1. So, you _do_ want to have a generic Fix. Also, you might want to write cata's destructors through recursive principles, or through direct matching.

1. Now, you can't just do Fix f = f (Fix f), that's not well-founded and Coq will object with positivity checking.
1. We think making Fix f graded with a nat should solve the problem, though Coq does not immediately agree, so we `Unset Positivity Checking.` briefly.
1. Now, how can we get `cata` to work? It....somehow.....does not want to realize that it's decreasing on the Fix's layer, or that this argument is the same as the decreasing one, or...