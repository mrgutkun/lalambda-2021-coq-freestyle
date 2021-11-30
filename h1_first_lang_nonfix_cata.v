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

Inductive expr :=
  | ENum (n: nat)
  | EAdd (e1 e2 : expr)
  | ESub (e1 e2 : expr)
  | EMul (e1 e2 : expr)
.



Definition expr_indDef := [indDef for expr_rect].
Canonical expr_indType := IndType expr expr_indDef.
Definition expr_eqMixin := [derive eqMixin for expr].
Canonical expr_eqType := EqType expr expr_eqMixin.

Implicit Type e : expr.
Derive (Arbitrary, Show) for expr.

Definition expr_cata {A} natf addf mulf subf : expr -> A :=
  expr_rect 
    natf
    (* simply ignore available expr args *)
    (fun _ left _ right => addf left right)
    (fun _ left _ right => mulf left right)
    (fun _ left _ right => subf left right)
.

Definition eval : expr -> nat := 
  expr_cata id addn muln subn.

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
  run (_ :: p) s := run p s.
  (* error semantics: if a command does not have prereqs, skip it. *)

Equations compile e : prog :=
  compile (ENum n) := [:: IPush n];
  compile (EAdd el er) := compile el ++ compile er ++ [:: IAdd];
  compile (ESub el er) := compile el ++ compile er ++ [:: ISub];
  compile (EMul el er) := compile el ++ compile er ++ [:: IMul].

QuickChick (fun e => 
  run (compile e) [::] == [:: eval e]
).

Lemma run_cat p1 p2 s :
  run (p1 ++ p2) s = run p2 (run p1 s).
  elim: p1 p2 s=> [//| i p1 IHp1 p2 s].
  case: i=> [//=|||].
  (* case: s=> [//=| x [//=| y s]] //=. *)
  all: by case: s=> [| x [| y s]] /=.
Qed.

Lemma compile_correct e :
  run (compile e) [::] = [:: eval e].
Proof.
  move: [::].
  elim: e=> //= e1 IHe1 e2 IHe2 s;
  by rewrite !run_cat IHe2 IHe1.
Qed.
