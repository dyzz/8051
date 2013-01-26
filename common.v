Require Import ZArith.
Require Export int8.

Notation Byte := int8.
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

Module Type StateVal.
Parameter carrier:Type.
End StateVal.

Module StateMonad(Val:StateVal).
Definition s := Val.carrier.

Definition StM (a : Type) : Type := s -> (a*s) .

Definition Return (a:Type):a->StM a := fun x s => (x,s) .

Definition Bind (a b:Type):StM a -> (a -> StM b) -> (StM b):=
  fun c1 c2 s1 => let (x,s2) := c1 s1 in c2 x s2.


Definition Bind'(a b:Type):=
  fun (c1:StM a)(c2:StM b) => Bind c1 (fun _ => c2).


Definition Get : StM s := fun s => (s,s).

Definition Put : s -> StM unit := fun s _ => (tt,s).

Infix ">>=" := Bind(at level 60).

Infix ">>"  := Bind'(at level 60).

End StateMonad.

(* Module NatVal <: StateVal. *)
(* Definition carrier:=nat. *)
(* End NatVal. *)

(* Module NStM:=StateMonad(NatVal). *)

(* Import NStM. *)

