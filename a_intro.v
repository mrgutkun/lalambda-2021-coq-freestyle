(* From Equations Require Import Equations. *)
(* From QuickChick Require Import QuickChick. *)
(* Import GenLow GenHigh. *)
(* From deriving Require Import deriving. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
(* From mathcomp Require Import zify. *)

Global Set Bullet Behavior "None".
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Set Equations Transparent. *)

Lemma addnA : associative addn.
Proof.
rewrite /associative. 
move=> m n p.
move:m.
elim.
- done.
move=> m.
move=> IHm /=.

Search (_.+1 + _).

rewrite addSn IHm => //.

Restart.

by elim=> // ? IHm ? ?; rewrite addSn IHm.
Qed. 

Lemma addnC : commutative addn.
Search (_ + 0).
Search right_id addn.

move=> m n; elim: m; first by rewrite addn0.
move=> m IHm.
Search (_.+1 + _).
by rewrite addSn addnS IHm.
Qed.