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
  run _ s := s. 
  (* semantics: if an op occured that can't run, stop processing entirely *)
  (* note: this is simple, but we have no error-handling *)
  
Equations compile e : prog :=
  compile (ENum n) := [:: IPush n];
  compile (EAdd e1 e2) := compile e1 ++ compile e2 ++ [:: IAdd];
  compile (ESub e1 e2) := compile e1 ++ compile e2 ++ [:: ISub];
  compile (EMul e1 e2) := compile e1 ++ compile e2 ++ [:: IMul].

QuickChick (fun e => [:: eval e] == run (compile e) [::]).

Record stype := mk_stype 
  { inp : nat
  ; out : nat
  }.

Notation "i ~~> o" := (mk_stype i o) (at level 50, no associativity).

Definition smerge st1 st2 :=
  let: i1 ~~> o1 := st1 in
  let: i2 ~~> o2 := st2 in
  (i1 + (i2 - o1)) ~~> (o2 + (o1 - i2)).

Equations sinfer_i i : stype :=
  sinfer_i (IPush _) := 0 ~~> 1;
  sinfer_i IAdd := 2 ~~> 1;
  sinfer_i IMul := 2 ~~> 1;
  sinfer_i ISub := 2 ~~> 1.

Definition sinfer p :=
  foldr (fun i st => smerge (sinfer_i i) st) (0 ~~> 0) p.

QuickChick (fun p1 p2 s =>
  implication
    (inp (sinfer p1) <= seq.size s)
    (run (p1 ++ p2) s == run p2 (run p1 s))
).

Lemma run_cat p1 p2 s : run (p1 ++ p2) s = run p2 (run p1 s).
Proof.
  elim: p1 s=> [//|i p1 IHp1 s].
  case: i=> //=. (* //= can! // can't. *)
  all: case: s=> [|x [|y s]] //=.
Qed.

Lemma sinfer_cat p1 p2 : 
  sinfer (p1 ++ p2) = smerge (sinfer p1) (sinfer p2).
Admitted.
(* QuickChick (fun p1 p2 => 
  sinfer (p1 ++ p2) == smerge (sinfer p1) (sinfer p2)
). *)

Lemma compile_sinfer e :
  sinfer (compile e) = 0 ~~> 1.
Proof.
  elim: e=>// e1 IHe1 e2 IHe2.
  rewrite sinfer_cat.
  rewrite /sinfer. rewrite foldr_cat.

Lemma compile_correct e :
  [:: eval e] = run (compile e) [::].
Proof.
move: [::].
elim: e=> //= e1 IHe1 e2 IHe2 s.
all: by rewrite !run_cat -IHe1 -IHe2.
Qed.