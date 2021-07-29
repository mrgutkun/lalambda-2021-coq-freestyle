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


Module Compile3.
(* Improving derived generator:
https://github.com/QuickChick/QuickChick/issues/229 *)
Inductive binop : Type :=
| Plus
| Minus
| Times
| And
| Or
| Eq
| Leq.
Derive (Arbitrary, Show) for binop.
(* TODO See if introducing `binop` simplifies some repetitive proofs.
   COMMENT: no, it does not, grouping operations by types would probably do *)

Inductive exp : Type :=
| ENum of nat
| ETrue
| EFalse
| ENeg of exp
| EBinOp of binop & exp & exp
| EIf of exp & exp & exp.

Derive (Arbitrary, Show) for exp.
Implicit Type e : exp.

Inductive val : Type :=
| VNat (n : nat)
| VBool (b : bool).
Derive (Arbitrary, Show) for val.
Implicit Type v : val.

(*| Derive an instance of decidable equality structure using the *deriving*
package. |*)
Definition val_indDef := [indDef for val_rect].
Canonical val_indType := IndType val val_indDef.
Definition val_eqMixin := [derive eqMixin for val].
Canonical val_eqType := EqType val val_eqMixin.

Section Evaluator.

Definition addv ov1 ov2 :=
  match ov1, ov2 with
  | Some (VNat n1), Some (VNat n2) => Some (VNat (n1 + n2))
  | _, _ => None
  end.

Definition subv ov1 ov2 :=
  match ov1, ov2 with
  | Some (VNat n1), Some (VNat n2) => Some (VNat (n1 - n2))
  | _, _ => None
  end.

Definition mulv ov1 ov2 :=
  match ov1, ov2 with
  | Some (VNat n1), Some (VNat n2) => Some (VNat (n1 * n2))
  | _, _ => None
  end.

Definition andv ov1 ov2 :=
  match ov1, ov2 with
  | Some (VBool b1), Some (VBool b2) => Some (VBool (b1 && b2))
  | _, _ => None
  end.

Definition orv ov1 ov2 :=
  match ov1, ov2 with
  | Some (VBool b1), Some (VBool b2) => Some (VBool (b1 || b2))
  | _, _ => None
  end.

Definition negv ov :=
  match ov with
  | Some (VBool b) => Some (VBool (~~ b))
  | _ => None
  end.

 (* polymorphic equality *)
Definition eqv ov1 ov2 :=
  match ov1, ov2 with
  | Some (VNat n1), Some (VNat n2) => Some (VBool (n1 == n2))
  | Some (VBool b1), Some (VBool b2) => Some (VBool (b1 == b2))
  | _, _ => None
  end.

Definition leqv ov1 ov2 :=
  match ov1, ov2 with
  | Some (VNat n1), Some (VNat n2) => Some (VBool (n1 <= n2))
  | _, _ => None
  end.

Definition gtv ov1 ov2 :=
  match ov1, ov2 with
  | Some (VNat n1), Some (VNat n2) => Some (VBool (n1 > n2))
  | _, _ => None
  end.

Definition ifv condv thenv elsev : option val :=
  match condv with
  | Some (VBool true) => thenv
  | Some (VBool false) => elsev
  | _ => None
  end.

Reserved Notation "[[ e ]]" (at level 9, no associativity).

(*| Computable big-step semantics for arithmetic expressions: |*)
Equations eval (e : exp) : option val :=
  eval (ENum n) := Some (VNat n);
  eval (EBinOp Plus e1 e2) := addv (eval e1) (eval e2);
  eval (EBinOp Minus e1 e2) := subv (eval e1) (eval e2);
  eval (EBinOp Times e1 e2) := mulv (eval e1) (eval e2);
  eval ETrue := Some (VBool true);
  eval EFalse := Some (VBool false);
  eval (EBinOp And e1 e2) := andv (eval e1) (eval e2);
  eval (EBinOp Or e1 e2) := orv (eval e1) (eval e2);
  eval (ENeg e) := negv (eval e);
  eval (EBinOp Eq e1 e2) := eqv (eval e1) (eval e2);
  eval (EBinOp Leq e1 e2) := leqv (eval e1) (eval e2);
  eval (EIf cond then_ else_) := ifv (eval cond) (eval then_) (eval else_).

End Evaluator.

(*| The usual Oxford brackets notation for the evaluator: |*)
Notation "[[ e ]]" := (eval e) (at level 9, no associativity).



(*|
Stack machine
------------- |*)


(*| The stack machine instructions: |*)
Inductive instr : Type :=
| IPush of nat | IPop
| IAdd | ISub | IMul | IEq | INeq | ILeq | IGt
| ISkip (offset : nat) | ISkipIf (non_zero : bool) (offset : nat).
Derive (Arbitrary, Show) for instr.
Implicit Type i : instr.
(*| Both source natural numbers and booleans are mapped into numbers in the stack
machine. ``true`` is represented as a non-zero number and ``false`` is represented as zero. |*)

Definition prog := seq instr.
Definition stack := seq nat.
Implicit Types (p : prog) (s : stack).

Equations run p s : stack :=
  run (IPush v :: p) s := run p (v :: s);
  run (IPop :: p) (_ :: s) := run p s;
  run (IAdd :: p) (x :: y :: s) := run p (y + x :: s);
  run (ISub :: p) (x :: y :: s) := run p (y - x :: s);
  run (IMul :: p) (x :: y :: s) := run p (y * x :: s);
  run (IEq :: p) (x :: y :: s) := run p (nat_of_bool (y == x) :: s);
  run (INeq :: p) (x :: y :: s) := run p (nat_of_bool (y != x) :: s);
  run (ILeq :: p) (x :: y :: s) := run p (nat_of_bool (y <= x) :: s);
  run (IGt :: p) (x :: y :: s) := run p (nat_of_bool (y > x) :: s);
  run (ISkip n :: p) s := run (drop n p) s;
  run (ISkipIf true n :: p) (0 :: s) := run p (0 :: s);
  run (ISkipIf true n :: p) (b :: s) := run (drop n p) (b :: s);
  run (ISkipIf false n :: p) (0 :: s) := run (drop n p) (0 :: s);
  run (ISkipIf false n :: p) (b :: s) := run p (b :: s);
  run _ s := s.

Arguments run : simpl nomatch.

Notation "ma >>= f" := (obind f ma) (at level 9, no associativity).
Definition pure {A} := @Some A.


Section ExprTyping.

Inductive etype :=
  | ETNat
  | ETBool
  .

Equations e_infer e : option etype :=
  e_infer (ENum _) := Some ETNat;
  e_infer ETrue := Some ETBool;
  e_infer EFalse := Some ETBool;
  e_infer (ENeg e) := 
    if (e_infer e) is (Some ETBool) 
    then Some ETBool
    else None;
  e_infer (EIf cond then_ else_) :=
    match (e_infer cond), (e_infer then_), (e_infer else_) with
    | Some ETBool, Some ETBool, Some ETBool => Some ETBool
    | Some ETBool, Some ETNat, Some ETNat => Some ETNat
    | _, _, _ => None
    end;
  e_infer (EBinOp Plus e1 e2) := 
    match (e_infer e1), (e_infer e2) with
    | Some ETNat, Some ETNat => Some ETNat
    | _, _ => None
    end;
  e_infer (EBinOp Minus e1 e2) := 
    match (e_infer e1), (e_infer e2) with
    | Some ETNat, Some ETNat => Some ETNat
    | _, _ => None
    end;
  e_infer (EBinOp Times e1 e2) := 
    match (e_infer e1), (e_infer e2) with
    | Some ETNat, Some ETNat => Some ETNat
    | _, _ => None
    end;
  e_infer (EBinOp And e1 e2) := 
    match (e_infer e1), (e_infer e2) with
    | Some ETBool, Some ETBool => Some ETBool
    | _, _ => None
    end;
  e_infer (EBinOp Or e1 e2) := 
    match (e_infer e1), (e_infer e2) with
    | Some ETBool, Some ETBool => Some ETBool
    | _, _ => None
    end;
  e_infer (EBinOp Eq e1 e2) := 
    match (e_infer e1), (e_infer e2) with
    | Some ETBool, Some ETBool => Some ETBool
    | Some ETNat, Some ETNat => Some ETBool
    | _, _ => None
    end;
  e_infer (EBinOp Leq e1 e2) := 
    match (e_infer e1), (e_infer e2) with
    | Some ETNat, Some ETNat => Some ETBool
    | _, _ => None
    end.

Definition well_typed e : bool :=
  if (e_infer e) is (Some _) 
  then true else false.

End ExprTyping.

QuickChick ( fun e =>
  match (e_infer e), (eval e) with
  | Some ETBool, Some (VBool _) => true
  | Some ETNat, Some (VNat _) => true
  | None, None => true
  | None, _ => true
  (* typechecker is less powerful than evaluator *)
  | _, _ => false
  end
).
(* 
Definition test_case := EBinOp Leq (ENum 0) (ENum 0).
Compute (well_typed test_case).
Compute (if (eval test_case) is None then false else true). *)


Section Compiler.

(* Search (seq (seq _) -> seq _). *)

Equations compile e : option prog :=
  compile (ENum n) := Some [:: IPush n];
  compile ETrue := Some [:: IPush 1];
  compile EFalse := Some [:: IPush 0];
  compile (ENeg e) := 
    (compile e) >>= fun p => 
    pure (p ++ [:: IPush 0; IEq]);
  compile (EIf cond then_ else_) := 
    (compile cond) >>= fun pcond =>
    (compile then_) >>= fun pthen =>
    (compile else_) >>= fun pelse =>
    pure (
      pcond 
      (* ISkipIf drops from _program_ *)
      (* if condition is true: pop, then run the then, 
      then drop the other pop and the second branch.
      if condition is false: skip over the pop and the first branch
      and the skip, then pop and do the second branch.
      *)

      ++ [:: ISkipIf false ((seq.size pthen) .+2); IPop] ++ pthen
      ++ [:: ISkip ((seq.size pelse) .+1); IPop] ++ pelse
    );
  compile (EBinOp Plus e1 e2) :=
    (compile e1) >>= fun p1 =>
    (compile e2) >>= fun p2 =>
    pure (p1 ++ p2 ++ [:: IAdd]);
  compile (EBinOp Minus e1 e2) :=
    (compile e1) >>= fun p1 =>
    (compile e2) >>= fun p2 =>
    pure (p1 ++ p2 ++ [:: ISub]);
  compile (EBinOp Times e1 e2) :=
    (compile e1) >>= fun p1 =>
    (compile e2) >>= fun p2 =>
    pure (p1 ++ p2 ++ [:: IMul]);
  compile (EBinOp And e1 e2) :=
    (compile e1) >>= fun p1 =>
    (compile e2) >>= fun p2 =>
    pure (p1 ++ p2 ++ [:: IMul]);
  compile (EBinOp Or e1 e2) :=
    (compile e1) >>= fun p1 =>
    (compile e2) >>= fun p2 =>
    pure (
      p1 ++ p2 ++ [:: IAdd] ++ 
      p1 ++ p2 ++ [:: IMul; ISub]
      (* pretty bad if p1 and p2 are expensive. *)
    );
  compile (EBinOp Leq e1 e2) := 
    (compile e1) >>= fun p1 =>
    (compile e2) >>= fun p2 =>
    pure (p1 ++ p2 ++ [:: ILeq]);
  compile (EBinOp Eq e1 e2) := 
    (compile e1) >>= fun p1 =>
    (compile e2) >>= fun p2 =>
    pure (p1 ++ p2 ++ [:: IEq]).
  (* compile _ := None. *)

End Compiler.

Definition run' := fun p => run p [::].

Equations convert (ov:option val) : option nat :=
  convert None := None;
  convert (Some (VNat n)) := Some n;
  convert (Some (VBool b)) := Some (nat_of_bool b).

QuickChick (
  let: pack := fun ost =>
    match ost return seq (option _) with
    | None => [::]
    | Some st => map Some st
    end in
  fun e => 
  implication
    (well_typed e)
    (pack (omap run' (compile e)) == [:: convert (eval e)])
).

Section ProgTyping.


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


Equations s_infer p : option stype :=
  s_infer [::] := Some (0 ~~> 0);
  s_infer (IPush _ :: p) := 
    (s_infer p) >>= fun st => 
      Some (s_merge (0 ~~> 1) st);
  s_infer (IPop :: p) :=
    (s_infer p) >>= fun st => 
      Some (s_merge (1 ~~> 0) st);
  s_infer (IAdd :: p) :=
    (s_infer p) >>= fun st => 
      Some (s_merge (2 ~~> 1) st);
  s_infer (ISub :: p) :=
    (s_infer p) >>= fun st => 
      Some (s_merge (2 ~~> 1) st);
  s_infer (IMul :: p) :=
    (s_infer p) >>= fun st => 
      Some (s_merge (2 ~~> 1) st);
  s_infer (IEq :: p)  :=
    (s_infer p) >>= fun st => 
      Some (s_merge (2 ~~> 1) st);
  s_infer (INeq :: p) :=
    (s_infer p) >>= fun st => 
      Some (s_merge (2 ~~> 1) st);
  s_infer (ILeq :: p) :=
    (s_infer p) >>= fun st => 
      Some (s_merge (2 ~~> 1) st);
  s_infer (IGt :: p)  :=
    (s_infer p) >>= fun st => 
      Some (s_merge (2 ~~> 1) st);
  
  s_infer (ISkip n :: p) := 
    (s_infer (drop n p)) >>= fun st => 
      Some (s_merge (1 ~~> 0) st);
  s_infer (ISkipIf _ n :: p) := 
    (s_infer p) >>= fun st1 => 
    (s_infer (drop n p)) >>= fun st2 => 
      let: i1 ~~> o1 := st1 in
      let: i2 ~~> o2 := st2 in
      if o2 - i2 == o1 - i1 then 
        (* if branches have the same diff, 
        then the if can at most consume the biggest 
        & will return the same diff. *)
        Some (max i1 i2 ~~> max o1 o2)
      else
        None
  .

Equations safe p : bool :=
  | [::] => true
  | (i :: p) => 
    match i with
    | ISkip n | ISkipIf _ n => 
        n <= seq.size p
    | IAdd | ISub | IMul | IEq | INeq | ILeq | IGt | IPush _ | IPop => 
        true
    end
  .

Definition stack_safe p s : bool :=
  match s_infer p with
  | None => false
  | Some (i ~~> o) => i <= seq.size s
  end.
  
End ProgTyping.

Section DepExp.

Inductive dep_exp : etype -> Type := 
  | EDNum (n:nat) : dep_exp ETNat
  | EDTrue : dep_exp ETBool
  | EDFalse : dep_exp ETBool
  | EDNeg : dep_exp ETBool -> dep_exp ETBool
  | EDIf {t} (cond: dep_exp ETBool) (then_ else_ : dep_exp t) : dep_exp t
  | EDPlus : dep_exp ETNat -> dep_exp ETNat -> dep_exp ETNat
  | EDMinus : dep_exp ETNat -> dep_exp ETNat -> dep_exp ETNat
  | EDTimes : dep_exp ETNat -> dep_exp ETNat -> dep_exp ETNat
  | EDAnd : dep_exp ETBool -> dep_exp ETBool -> dep_exp ETBool
  | EDOr : dep_exp ETBool -> dep_exp ETBool -> dep_exp ETBool
  | EDEq {t} : dep_exp t -> dep_exp t -> dep_exp ETBool
  | EDLeq : dep_exp ETNat -> dep_exp ETNat -> dep_exp ETBool
  .

Fixpoint translate {t} (de : dep_exp t) : exp :=
  match de with
  | EDNum n => ENum n
  | EDTrue => ETrue
  | EDFalse => EFalse
  | EDNeg e => ENeg (translate e)
  | EDIf c t e => EIf (translate c) (translate t) (translate e)
  | EDPlus e1 e2 => EBinOp Plus (translate e1) (translate e2)
  | EDMinus e1 e2 => EBinOp Minus (translate e1) (translate e2)
  | EDTimes e1 e2 => EBinOp Times (translate e1) (translate e2)
  | EDAnd e1 e2 => EBinOp And (translate e1) (translate e2)
  | EDOr e1 e2 => EBinOp Or (translate e1) (translate e2)
  | EDEq e1 e2 => EBinOp Eq (translate e1) (translate e2)
  | EDLeq e1 e2 => EBinOp Leq (translate e1) (translate e2)
  end.

Lemma dep_wt {t} (de: dep_exp t) : e_infer (translate de) = Some t.
Proof.
  elim:de=> //=.
  - move=> d IHd. by rewrite IHd.
  - move=> t' c IHcond th IHthen e IHelse.
    rewrite {}IHcond {}IHthen {}IHelse.
    move: th e. by case: t'.
  1,2,3,4,5,7: move=> ? IHl ? IHr; by rewrite IHl IHr.
  move=> t' d IHd d' IHd'. rewrite {}IHd {}IHd'.
  move: d d'; by case t'.
Qed.

End DepExp.

Section Totality.

(* In which we will reflect well-typedness into something *)
(* and use that to compile things totally. *)

Inductive WellTyped : exp -> etype -> Type := 
  | WTNum {n} : WellTyped (ENum n) ETNat
  | WTTrue : WellTyped ETrue ETBool
  | WTFalse : WellTyped EFalse ETBool
  | WTNeg e : WellTyped e ETBool -> WellTyped (ENeg e) ETBool
  | WTPlus e1 e2 : WellTyped e1 ETNat -> WellTyped e2 ETNat -> WellTyped (EBinOp Plus e1 e2) ETNat
  | WTMinus e1 e2 : WellTyped e1 ETNat -> WellTyped e2 ETNat -> WellTyped (EBinOp Minus e1 e2) ETNat
  | WTTimes e1 e2 : WellTyped e1 ETNat -> WellTyped e2 ETNat -> WellTyped (EBinOp Times e1 e2) ETNat
  | WTAnd e1 e2 : WellTyped e1 ETBool -> WellTyped e2 ETBool -> WellTyped (EBinOp And e1 e2) ETBool
  | WTOr e1 e2 : WellTyped e1 ETBool -> WellTyped e2 ETBool -> WellTyped (EBinOp Plus e1 e2) ETBool
  | WTEq {t} e1 e2 : WellTyped e1 t -> WellTyped e2 t -> WellTyped (EBinOp Plus e1 e2) ETBool
  | WTLeq e1 e2 : WellTyped e1 ETNat -> WellTyped e2 ETNat -> WellTyped (EBinOp Plus e1 e2) ETBool
  .

Equations compile' e (wte: WellTyped e) : prog :=
  compile' _ := [::].



End Totality.

Section Correctness.

Lemma run_cat p1 p2 s :
  safe p1 -> stack_safe p1 s -> 
  run (p1 ++ p2) s = run p2 (run p1 s).
Admitted.

Lemma compile_safe e wte : 
  safe (compile' e wte).
Admitted.

Lemma compile_stack_safe e s wte : 
  stack_safe (compile' e wte) s.
Admitted.

Lemma compile_correct de :
  run (compile' de _) [::] = [:: eval (translate de)].

End Correctness.

End Compile3.

