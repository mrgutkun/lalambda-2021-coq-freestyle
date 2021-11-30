# Intro
What is here:
- b,e: a simple expression language, a simple stack machine, compilation, correctness of compiled programs (matching semantics)
- c,d,f: same, but semantics of the stack machine are less convenient; there's some typing of programs involved and, again, correctness of compilation

- g is a bit too much.
    - more expressions and more instructions.
    - expressions do not have total semantics any more.
    - compilation is there, if harder; proofs of correctness....try to rely on several well-typing lemmas, but these are only sketched, and there's no final proof.
    - there's a section about a better dep-typed expression language w/ total semantics, transpilable into the main one.
    - there's hope that well-formedness of expressions can be somehow reflected into types, and then all non-total semantics and compilations can be made total.

How to reproduce:
- you need a local opam switch, and to launch code via `code .`; then it works.
- inside the switch:
    ```bash
    opam repo add coq-released https://coq.inria.fr/opam/released
    opam pin add coq 8.13.2 --no-action
    opam pin add coq-mathcomp-ssreflect 1.12.0 --no-action
    opam install coq coq-mathcomp-ssreflect coq-mathcomp-zify coq-equations coq-quickchick coq-deriving
    ```

# Dep-typed reflection sketch

1. As we have seen in `g`, having non-dependent type of expressions is really annoying, as it makes evaluation and everything non-total. At the same time, we hear that dep-type indices are annoying to work with in proofs. Let's test this empirically.
1. The plan is to have 3 attempts to implement and prove correct the same expression language and its compiler into a stack machine. Expressions will be dependently-typed, flat-typed, and...either as the whim strikes, if we figure how to do this.
1. The purpose of the exercise is to make apparent how both approaches are annoying somewhere, and hopefully construct the third approach to go around problems of either by switching between dep-typed and flat representation freely.

---

1. Approximate structure of all three:
    1. Definition of the expression-type
    1. (Shared value-type)
    1. Evaluator of expressions into values
    1. (Shared types of: stack instructions, stack programs, stack of ints)
    1. (Shared: runner of stack programs on stacks)
    1. Compiler of expressions into stack programs
    1. (QuickChick for the hypothesis that compiler is correct)
    1. Proof that running a compiled expression on an empty stack has the same result as evaluating that expression
1. Proofs are complicated enough to deserve a sketched structure of their own:
    1. a very common lemma: running 2 programs on a stack is the same as running their concatenation.
        1. For simplest languages and convenient stack semantics, that's pretty much enough to ≈cata over the compiled expr in its shape.
    1. When stack semantics are less forgiving, the lemma only works with a precondition that programs are stack-safe, that is, do not run into its end.
        1. to have this, we start keeping track of how much stack programs consume and produce
        1. then, with some lemma-wrangling, we observe that in fact all expressions compile into stack-safe programs, and we're golden.
    1. In the third language with ifs, we need even more.
        1. (TODO)

---

1. Now, doing fixpoint-based dep-types on a language with equalities and ifs is quite a bit of difficulty spikes simultaneously, so let's sketch a gentler path.
1. First, fixpointing the simplest language; second, same for less convenient stack semantics.
1. Third, fix-based dep-typed language with equalities only.
1. Fourth, the full thing.

---

1. Another curiosity:
    1. is there a way to copy less code, by making lemmas and functions work in a slightly more general setting? Something something language extendable with operations, modular semantics, and modular proofs of correctness?