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
  | ENum (n: nat)
  | EAdd (e1 e2 : exp)
  | ESub (e1 e2 : exp)
  | EMul (e1 e2 : exp)
  .

Definition exp_indDef := [indDef for exp_rect].
Canonical exp_indType := IndType exp exp_indDef.
Definition exp_eqMixin := [derive eqMixin for exp].
Canonical exp_eqType := EqType exp exp_eqMixin.

Implicit Type e : exp.
Derive (Arbitrary, Show) for exp.

Equations eval e : nat :=
  eval (ENum n) := n;
  eval (EAdd el er) := eval el + eval er;
  eval (EMul el er) := eval el * eval er;
  eval (ESub el er) := eval el - eval er.

(* ====================== *)

Inductive instr :=
  | IPush (n : nat)
  | IAdd
  | ISub
  | IMul
  .

Implicit Type i : instr.
Derive (Arbitrary, Show) for instr.

Definition prog := seq instr.
Implicit Type p : prog.

Definition stack := seq nat.
Implicit Type s : stack.

Equations run p s : stack :=
  run [::] s := s;
  run (IPush n :: p) s := run p (n :: s);
  run (IAdd :: p) (x :: y :: s) := run p (y+x :: s);
  run (ISub :: p) (x :: y :: s) := run p (y-x :: s);
  run (IMul :: p) (x :: y :: s) := run p (y*x :: s);
  (* run (_ :: p) s := run p s. *)
  run (_ :: p) s := [::].
  (* error semantics: if a command does not have prereqs, die. *)

Equations compile e : prog :=
  compile (ENum n) := [:: IPush n];
  compile (EAdd el er) := compile el ++ compile er ++ [:: IAdd];
  compile (ESub el er) := compile el ++ compile er ++ [:: ISub];
  compile (EMul el er) := compile el ++ compile er ++ [:: IMul].

QuickChick (fun e => 
  run (compile e) [::] == [:: eval e]
).

Record stype := mk_stype {
  inp : nat; (* depth of the stack a prog consumes *)
  out : nat; (* height of the stack a prog leaves on top of unconsumed *)
}.

Notation "i ~~> o" :=
  (mk_stype i o)
  (at level 50, no associativity).

Definition s_merge st1 st2 : stype :=
  let: inp1 ~~> out1 := st1 in
  let: inp2 ~~> out2 := st2 in
    (inp1 + (inp2 - out1)) ~~> (out2 + (out1 - inp2)).


Equations s_infer_i i : stype :=
  s_infer_i (IPush _) := (0 ~~> 1);
  s_infer_i IAdd := 2 ~~> 1;
  s_infer_i ISub := 2 ~~> 1;
  s_infer_i IMul := 2 ~~> 1.


Definition s_infer p : stype := 
  foldr (fun i st => s_merge (s_infer_i i) st) (0 ~~> 0) p.
  (* s_infer [::] := 0 ~~> 0;  
  s_infer (i :: p) := s_infer_i *)

Lemma s_mergeA : associative s_merge.
Proof.
  move=> [i1 o1] [i2 o2] [i3 o3].
  by congr mk_stype; lia.
Qed.

Lemma s_infer_cat p1 p2 : 
  s_infer (p1 ++ p2) = s_merge (s_infer p1) (s_infer p2).
Proof.
  elim: p1 => /= [| i s IHp1].
  - case: (s_infer p2) => i o. 
    by congr mk_stype; lia.
  by rewrite IHp1 s_mergeA.
Qed.

Lemma compile_typecheck e :
  s_infer (compile e) = 0 ~~> 1.
Proof.
  elim: e=> // e1 IHe1 e2 IHe2 /=;
  by rewrite !s_infer_cat IHe1 IHe2 //=.
Qed.

Lemma run_cat p1 p2 s :
  inp (s_infer p1) <= seq.size s ->
    run (p1 ++ p2) s = run p2 (run p1 s).
Proof.
  elim: p1 s=> // i p1 IHp1 s.
  case: i=> /=.
  - case: (s_infer p1) IHp1 => /= i o IHp1 n I1. 
    rewrite IHp1 //=; lia.
  all: case: (s_infer p1) IHp1 => /= i o IHp1.
  all: case: s=> [| x [| y s]] //= I1.
  all: by rewrite IHp1 //=; lia.
Qed.

Lemma compile_correct e :
  run (compile e) [::] = [:: eval e].
Proof.
  move: [::].
  elim: e=> //= e1 IHe1 e2 IHe2 s;
  by rewrite !run_cat ?IHe2 ?IHe1 ?compile_typecheck.
Qed.
