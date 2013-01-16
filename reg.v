Require Import common.

Inductive Reg : Set :=
  RA | RB | R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7 | DPTR | PC | SP .

Inductive Flag : Set :=
  FlagC | FlagAC | FlagOV .


Definition beq_reg(r r' : Reg) :=
  match r, r' with
    | RA, RA => true
    | RB, RB => true
    | R0, R0 => true
    | R1, R1 => true
    | R2, R2 => true
    | R3, R3 => true
    | R4, R4 => true
    | R5, R5 => true
    | R6, R6 => true
    | R7, R7 => true
    | _, _     => false
  end.
  


Definition beq_flag(f f' : Flag) :=
  match f, f' with
    | FlagC, FlagC => true
    | FlagAC, FlagAC => true
    | FlagOV, FlagOV => true
    | _, _ => false
  end.


Definition Regs := Reg -> Byte.

Definition Flags := Flag -> bool.

Definition getReg (rf : Regs) (r : Reg) := rf r.

Definition setReg (rf : Regs) (r : Reg) (v : Byte) :=
  fun r' => if beq_reg r' r then v else rf r'.

Definition getFlag (ff : Flags) (f : Flag) := ff f.

Definition setFlag (ff : Flags) (f : Flag) :=
  fun f' => if beq_flag f' f then true else ff f'.

Definition clearFlag (ff : Flags) (f : Flag) :=
  fun f' => if beq_flag f' f then false else ff f'.