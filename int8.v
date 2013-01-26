Require Import NaryFunctions.
Require Import Wf_nat.
Require Export ZArith.


Definition size := 8%nat.

(** Digits *)

Inductive digits : Type := D0 | D1.

Definition digits8 t := Eval compute in nfun digits size t.

Inductive int8 : Type := I8 : digits8 int8.

Delimit Scope int8_scope with int8.
Bind Scope int8_scope with int8.
Local Open Scope int8_scope.

Definition On : int8 := Eval compute in napply_cst _ _ D0 size I8.

Definition In : int8 := Eval compute in (napply_cst _ _ D0 (size-1) I8) D1.

Definition Tn : int8 := Eval compute in napply_cst _ _ D1 size I8.

Definition Twon : int8 := Eval compute in (napply_cst _ _ D0 (size-2) I8) D1 D0.

(** * Bits manipulation *)


(** [sneakr b x] shifts [x] to the right by one bit.
   Rightmost digit is lost while leftmost digit becomes [b].
   Pseudo-code is
    [ match x with (I8 d0 ... dN) => I8 b d0 ... d(N-1) end ]
*)

Definition sneakr : digits -> int8 -> int8 := Eval compute in
 fun b => int8_rect _ (napply_except_last _ _ (size-1) (I8 b)).

(** [sneakl b x] shifts [x] to the left by one bit.
   Leftmost digit is lost while rightmost digit becomes [b].
   Pseudo-code is
    [ match x with (I8 d0 ... dN) => I8 d1 ... dN b end ]
*)

Definition sneakl : digits -> int8 -> int8 := Eval compute in
 fun b => int8_rect _ (fun _ => napply_then_last _ _ b (size-1) I8).


(** [shiftl], [shiftr], [twice] and [twice_plus_one] are direct
    consequences of [sneakl] and [sneakr]. *)

Definition shiftl := sneakl D0.
Definition shiftr := sneakr D0.
Definition twice := sneakl D0.
Definition twice_plus_one := sneakl D1.

(** [firstl x] returns the leftmost digit of number [x].
    Pseudo-code is [ match x with (I8 d0 ... dN) => d0 end ] *)

Definition firstl : int8 -> digits := Eval compute in
 int8_rect _ (fun d => napply_discard _ _ d (size-1)).

(** [firstr x] returns the rightmost digit of number [x].
    Pseudo-code is [ match x with (I8 d0 ... dN) => dN end ] *)

Definition firstr : int8 -> digits := Eval compute in
 int8_rect _ (napply_discard _ _ (fun d=>d) (size-1)).

(** [iszero x] is true iff [x = I8 D0 ... D0]. Pseudo-code is
    [ match x with (I8 D0 ... D0) => true | _ => false end ] *)

Definition iszero : int8 -> bool := Eval compute in
 let f d b := match d with D0 => b | D1 => false end
 in int8_rect _ (nfold_bis _ _ f true size).

(* NB: DO NOT transform the above match in a nicer (if then else).
   It seems to work, but later "unfold iszero" takes forever. *)


(** [base] is [2^8], obtained via iterations of [Z.double].
   It can also be seen as the smallest b > 0 s.t. phi_inv b = 0
   (see below) *)

Definition base := Eval compute in
 iter_nat size Z Z.double 1%Z.

(** * Recursors *)

Fixpoint recl_aux (n:nat)(A:Type)(case0:A)(caserec:digits->int8->A->A)
 (i:int8) : A :=
  match n with
  | O => case0
  | S next =>
          if iszero i then
             case0
          else
             let si := shiftl i in
             caserec (firstl i) si (recl_aux next A case0 caserec si)
  end.

Fixpoint recr_aux (n:nat)(A:Type)(case0:A)(caserec:digits->int8->A->A)
 (i:int8) : A :=
  match n with
  | O => case0
  | S next =>
          if iszero i then
             case0
          else
             let si := shiftr i in
             caserec (firstr i) si (recr_aux next A case0 caserec si)
  end.

Definition recl := recl_aux size.
Definition recr := recr_aux size.

(** * Conversions *)

(** From int8 to Z, we simply iterates [Z.double] or [Z.succ_double]. *)

Definition phi : int8 -> Z :=
 recr Z (0%Z)
  (fun b _ => match b with D0 => Z.double | D1 => Z.succ_double end).

(** From positive to int8. An abstract definition could be :
      [ phi_inv (2n) = 2*(phi_inv n) /\
        phi_inv 2n+1 = 2*(phi_inv n) + 1 ] *)

Fixpoint phi_inv_positive p :=
  match p with
    | xI q => twice_plus_one (phi_inv_positive q)
    | xO q => twice (phi_inv_positive q)
    | xH => In
  end.

(** The negative part : 2-complement  *)

Fixpoint complement_negative p :=
  match p with
    | xI q => twice (complement_negative q)
    | xO q => twice_plus_one (complement_negative q)
    | xH => twice Tn
  end.

(** A simple incrementation function *)

Definition incr : int8 -> int8 :=
 recr int8 In
   (fun b si rec => match b with
     | D0 => sneakl D1 si
     | D1 => sneakl D0 rec end).

(** We can now define the conversion from Z to int8. *)

Definition phi_inv : Z -> int8 := fun n =>
 match n with
 | Z0 => On
 | Zpos p => phi_inv_positive p
 | Zneg p => incr (complement_negative p)
 end.


Definition lor8 n m := phi_inv (Z.lor (phi n) (phi m)).
Definition land8 n m := phi_inv (Z.land (phi n) (phi m)).
Definition lxor8 n m := phi_inv (Z.lxor (phi n) (phi m)).
Definition lnot8 n := lxor8 Tn n.
Definition ldiff8 n m := land8 n (lnot8 m).

(** * Addition *)

(** Addition modulo [2^8] *)

Definition add8 (n m : int8) := phi_inv ((phi n)+(phi m)).
Notation "n + m" := (add8 n m) : int8_scope.


Definition sub8 (n m : int8) := phi_inv ((phi n)-(phi m)).
Notation "n - m" := (sub8 n m) : int8_scope.

(** Opposite *)

Definition opp8 x := On - x.
Notation "- x" := (opp8 x) : int8_scope.

(** Multiplication *)

(** multiplication modulo [2^8] *)

Definition mul8 (n m : int8) := phi_inv ((phi n)*(phi m)).
Notation "n * m" := (mul8 n m) : int8_scope.

Definition compare8 (n m : int8) := ((phi n)?=(phi m))%Z.
Notation "n ?= m" := (compare8 n m) (at level 70, no associativity) : int8_scope.

Definition eqb8 (n m : int8) :=
 match n ?= m with Eq => true | _ => false end.


(** Computing the [i]-th iterate of a function:
    [iter_int8 i A f = f^i] *)

Definition iter_int8 i A f :=
  recr (A->A) (fun x => x)
   (fun b si rec => match b with
      | D0 => fun x => rec (rec x)
      | D1 => fun x => f (rec (rec x))
    end)
    i.

