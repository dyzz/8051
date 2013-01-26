Require Import common.
Require Import ZArith.
Open Scope int8_scope.
Definition ptr := Byte.

Definition null := 0. (*NULL Pointer*)

Definition ptr_eq_dec := eqb8.

Definition val := Byte.

Definition heap := ptr -> option val.

Definition empty : heap := fun _ => None.

Definition singleton (p : ptr) (v : val) : heap :=
  fun p' => if ptr_eq_dec p' p then Some v else None.

Definition read (h : heap) (p : ptr) : option val := h p.
Definition read' (h : heap) (p : ptr) : val :=
  match h p with 
      | Some v => v
      | None => On
  end.


Definition write (h : heap) (p : ptr) (v : val) : heap :=
  fun p' => if ptr_eq_dec p' p then Some v else h p'.

Definition free (h : heap) (p : ptr) : heap :=
  fun p' => if ptr_eq_dec p' p then None else h p'.

Infix "#" := read (right associativity, at level 60) .

Notation "h ## p <- v" := (write h p v) (no associativity, at level 60, p at next level) .

Definition join (h1 h2:heap) :=
  fun p =>
    match h1 p with
      | Some v=> h1 p
      | None => h2 p
    end.

Infix "+^+" := join (no associativity, at level 40).

Lemma read_dec: forall h:heap,forall p:ptr, (exists v,h # p=Some v) \/ h # p=None.
intros.
destruct (h # p).
left.
exists v;auto.
right;auto.
Qed.

Lemma id_join1: forall h:heap,empty +^+ h = h.
unfold heap.
intros.
apply ext_eq.
intro.
unfold empty.
unfold join.
simpl.
trivial.
Qed.

Lemma id_join2: forall h:heap, h +^+ empty =h.
unfold heap.
intros.
apply ext_eq.
intros.
unfold join.
unfold empty.
destruct (h a).
auto.
auto.
Qed.


Lemma heap_join_assoc : forall h1 h2 h3, h1 +^+ (h2 +^+ h3) = (h1 +^+ h2) +^+ h3.
Proof.
unfold heap.
intros.
apply ext_eq.
intro.
unfold join.
destruct (h1 a); auto.
Qed.




