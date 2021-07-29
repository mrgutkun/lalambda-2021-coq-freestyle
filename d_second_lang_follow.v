Set Warnings "-extraction-opaque-accessed,-extraction,-notation-overridden".
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq. (* coq-mathcomp-ssreflect *)
From Equations Require Import Equations. (* coq-equations *)
From QuickChick Require Import QuickChick. (* coq-quickchick *)
Import GenLow GenHigh. (* from QuickChick *)
From mathcomp Require Import zify. (* coq-mathcomp-zify *)
From deriving Require Import deriving. (* coq-deriving *)

Global Set Bullet Behavior "None".
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Set Equations Transparent.

(* =================== *)
(*  Compiler 2         *)
(* =================== *)

Module Compiler2.
Inductive exp :=
  | ENum (n : nat)
  | EPlus (e1 e2 : exp)
  | EMinus (e1 e2 : exp)
  | ETimes (e1 e2 : exp)
.
Implicit Type e : exp.
Definition exp_indDef := [indDef for exp_rect].
Canonical exp_indType := IndType exp exp_indDef.
Definition exp_eqMixin := [derive eqMixin for exp].
Canonical exp_eqType := EqType exp exp_eqMixin.
Derive (Arbitrary, Show) for exp. (* Derive comes from QuickChick *)

Equations eval e : nat :=
  eval (ENum n) := n;
  eval (EPlus e1 e2) := eval e1 + eval e2;
  eval (EMinus e1 e2) := eval e1 - eval e2;
  eval (ETimes e1 e2) := eval e1 * eval e2.

Inductive instr : Type :=
  | IPush (n : nat)
  | IAdd
  | ISub
  | IMul.
Implicit Type i : instr.
Derive (Arbitrary, Show) for instr. (* Derive comes from QuickChick *)

Definition prog := seq instr.
Implicit Type p : prog.
Definition stack := seq nat.
Implicit Type s : stack.

(* Stack machine v2: stops processing its
   program when there is an error *)
Equations run p s : stack :=
  run (IPush n :: p) s := run p (n :: s);
  run (IAdd :: p) (x :: y :: s) := run p (y + x :: s);
  run (ISub :: p) (x :: y :: s) := run p (y - x :: s);
  run (IMul :: p) (x :: y :: s) := run p (y * x :: s);
  run _ s := s.

Arguments run : simpl nomatch.

Equations compile e : prog :=
  compile (ENum n) := [:: IPush n];
  compile (EPlus e1 e2) := compile e1 ++ compile e2 ++ [:: IAdd];
  compile (EMinus e1 e2) := compile e1 ++ compile e2 ++ [:: ISub];
  compile (ETimes e1 e2) := compile e1 ++ compile e2 ++ [:: IMul].

QuickChick (fun e =>
  [:: eval e] == run (compile e) [::]).

Time QuickChickWith (updMaxSize (updMaxSuccess stdArgs 100) 10)
  (fun e => [:: eval e] == run (compile e) [::]).

Record stype := mk_stype {
                    inp : nat;
                    out : nat;
                  }.
Notation "i ~~> o" := (mk_stype i o) (at level 50, no associativity).

Definition smerge st1 st2 :=
  let: (i1 ~~> o1) := st1 in
  let: (i2 ~~> o2) := st2 in
  (i1 + (i2 - o1)) ~~> (o2 + (o1 - i2)).
Notation "x ⊞ y" := (smerge x y) (at level 50, left associativity).

(* \longrightsquigarrow *)
Equations sinfer_i i : stype :=
  sinfer_i (IPush _) := 0 ~~> 1;
  sinfer_i _ := 2 ~~> 1.

Definition sinfer p :=
  foldr (fun i st => (sinfer_i i) ⊞ st) (0 ~~> 0) p.

QuickChick (fun p1 p2 s =>
  implication
    (inp (sinfer p1) <= seq.size s)
    (run (p1 ++ p2) s == run p2 (run p1 s))).

Lemma run_cat p1 p2 s :
  inp (sinfer p1) <= seq.size s ->
  run (p1 ++ p2) s = run p2 (run p1 s).
Proof.
elim: p1 s=> //= i p1 IHp1 s.
case: i=> //=.
- case: (sinfer p1) IHp1 => /= i1 _ IHp1 n I1.
  rewrite IHp1 //=; lia.

- case: (sinfer p1) IHp1 => /= i1 _ IHp1.
  case: s=> //= x [|y s] /=. lia. admit.

- case: (sinfer p1) IHp1 => /= i1 _ IHp1.
  case: s=> //= x [|y s] /=. lia. admit.

- case: (sinfer p1) IHp1 => /= i1 _ IHp1.
  case: s=> //= x [|y s] /=. lia. admit.

(* move/IHp1. *)
Admitted.

Lemma smergeA : associative smerge.
Proof.
  move=> [i1 o1] [i2 o2] [i3 o3];
  congr mk_stype; lia.
Qed.

Lemma sinfer_cat p1 p2 :
  sinfer (p1 ++ p2) = (sinfer p1) ⊞ (sinfer p2).
Proof.
elim: p1=> /= [|i1 p1 IHp1].
- case: (sinfer p2)=> i2 o2.
  (* by rewrite subn0 addn0. *)
  congr mk_stype; lia. (* congr splits; lia solves; lia can't split. *)

by rewrite IHp1 smergeA.
Qed.

Lemma compile_sinfer e :
  sinfer (compile e) = 0 ~~> 1.
Proof.
elim: e=> //= e1 IHe1 e2 IHe2.
all: by rewrite !sinfer_cat /= IHe1 IHe2.
Qed.
  

Lemma compile_correct e :
  run (compile e) [::] = [:: eval e].
Proof.
move: [::].
elim: e=> //= e1 IHe1 e2 IHe2 s.
- rewrite run_cat ?IHe1 ?compile_sinfer //.
  by rewrite run_cat ?IHe2 ?compile_sinfer.
- rewrite run_cat ?IHe1 ?compile_sinfer //.
  by rewrite run_cat ?IHe2 ?compile_sinfer.
- rewrite run_cat ?IHe1 ?compile_sinfer //.
  by rewrite run_cat ?IHe2 ?compile_sinfer.
Qed.
End Compiler2.