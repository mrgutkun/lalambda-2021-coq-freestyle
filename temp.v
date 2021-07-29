From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.


Structure eqType := Pack {
  sort : Type;
  eq_op : sort -> sort -> bool;
  spec : forall x y, reflect (x=y) (eq_op x y)
}.

Coercion sort : eqType >-> Sortclass.

Lemma eq_sym (T : eqType) (x y : T) :
  eq_op T x y -> eq_op T y x.