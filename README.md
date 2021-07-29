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