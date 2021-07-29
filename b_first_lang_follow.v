Set Warnings "-extraction-opaque-accessed,-extraction,-notation-overridden".
From Equations Require Import Equations.
From deriving Require Import deriving.

From QuickChick Require Import QuickChick.
Import GenLow GenHigh.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import zify. (* coq-mathcomp-zify *)

Global Set Bullet Behavior "None".
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Equations Transparent.

Inductive exp :=
  | ENum of nat
  (* | ENum (n : nat) *)
  (* | ENum : nat -> exp *)
  | EAdd (e1 e2 : exp)
  (* | EAdd of exp & exp *)
  | ESub (e1 e2 : exp)
  | EMul (e1 e2 : exp)
.

Definition exp_indDef := [indDef for exp_rect].
Canonical exp_indType := IndType exp exp_indDef.
Definition exp_eqMixin := [derive eqMixin for exp].
Canonical exp_eqType := EqType exp exp_eqMixin.

Derive (Arbitrary, Show) for exp.

Implicit Type e : exp.

Equations eval e : nat :=
  eval (ENum n) := n;
  eval (EAdd e1 e2) := eval e1 + eval e2;
  eval (ESub e1 e2) := eval e1 - eval e2;
  eval (EMul e1 e2) := eval e1 * eval e2.

Inductive instr : Type :=
  | IPush (n : nat)
  | IAdd
  | ISub
  | IMul
.

Derive (Arbitrary, Show) for instr.


Definition prog := seq instr.
Definition stack := seq nat.


Implicit Type i : instr.
Implicit Type p : prog.
Implicit Type s : stack.


Equations run p s : stack :=
  run (IPush n :: p) s := run p (n :: s);
  run (IAdd :: p) (x :: y :: s) := run p (y + x :: s);
  run (ISub :: p) (x :: y :: s) := run p (y - x :: s);
  run (IMul :: p) (x :: y :: s) := run p (y * x :: s);
  run [::] s := s;
  run (i::p) s := run p s. (* if the op does not have prereq stack, skip it*)
  
Equations compile e : prog :=
  compile (ENum n) := [:: IPush n];
  compile (EAdd e1 e2) := compile e1 ++ compile e2 ++ [:: IAdd];
  compile (ESub e1 e2) := compile e1 ++ compile e2 ++ [:: ISub];
  compile (EMul e1 e2) := compile e1 ++ compile e2 ++ [:: IMul].

QuickChick (fun e => [:: eval e] == run (compile e) [::]).

Time QuickChickWith (updMaxSize (updMaxSuccess stdArgs 100) 10)
  (fun e => [:: eval e] == run (compile e) [::]).


Time QuickChickWith (updMaxSize (updMaxSuccess stdArgs 100) 10)
  (fun e s => eval e :: s == run (compile e) s).



Lemma run_cat p1 p2 s : run (p1 ++ p2) s = run p2 (run p1 s).
Proof.
  elim: p1 s=> [//|i p1 IHp1 s].
  case: i=> //=. (* //= can! // can't. *)
  all: case: s=> [|x [|y s]] //.
Qed.

Lemma compile_correct e s :
  eval e :: s = run (compile e) s.
Proof.
elim: e s=> //= e1 IHe1 e2 IHe2 s.
all: by rewrite !run_cat -IHe1 -IHe2.
Qed.