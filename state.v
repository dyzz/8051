Require Import common.
Require Import reg.
Require Import heap.

Definition Mem := heap.

Definition State := ( Mem * Regs * Flags ) %type.

Definition S_Mem (s : State) : Mem :=
  match s with
    | (m, _, _) => m
  end.

Definition S_Reg (s : State) : Regs :=
  match s with
    | (_, rf, _) => rf
  end.

Definition S_Flag (s : State) : Flags :=
  match s with
    | (_, _, ff) => ff
  end.


Definition S_Mem_Upd (s : State) (m: Mem) : State :=
  (m, S_Reg s, S_Flag s).

Definition S_Reg_Upd (s : State) (rf : Regs) : State :=
  (S_Mem s, rf, S_Flag s).

Definition S_Flag_Upd (s : State) (ff : Flags) : State :=
  (S_Mem s, S_Reg s, ff).

Lemma state_eq : 
  forall (m m' : Mem) (rf rf' : Regs) (ff ff' : Flags) ,
    (m, rf, ff) = (m', rf', ff') ->
    m = m' /\ rf = rf' /\ ff = ff' .
Proof.
intros.
inversion H.
repeat split;trivial.
Qed.