Require Import ZArith.


Notation Byte := Z.
Notation Label := Z.

Set Implicit Arguments.
Axiom ext_eq:forall A B:Type, forall f g:A->B,
(forall a:A,f a=g a)-> f = g.

Theorem ext_eqS : forall A B:Set,forall f g: A -> B,
  (forall a:A, f a =g a) -> f = g.
intros.
rewrite (ext_eq f g).
trivial.
auto.
Qed.

