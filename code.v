Require Import common.
Require Import reg.
Require Import state.
Require Import map.
Require Import ZArith.

Parameter Imm:Set.
Parameter Dir:Set.
Parameter Register:Set.
Parameter Dptr:Set.
Parameter Code:Set.
Parameter Any:Set.
(* Addressing Modes *)

Inductive Addr(Mode:Set):Set:=
  | A_Imm : Byte -> Addr Mode
  | A_Dir : Byte -> Addr Mode
  | A_Reg : Reg -> Addr Mode
  | A_DPTR : Addr Mode
  | A_Code : Addr Mode
.

(* Needs to refine Addr with correct addressing mode *)
Inductive Instr:Set:=
  | acall : Label -> Instr (* Absolute Call *)
  | add   : Addr Any -> Instr  (* ADDC: Add Accumulator (With Carry) *)
  | addc  : Addr Any -> Instr  (* ADDC: Add Accumulator (With Carry) *)
  | ajmp  : Label -> Instr (* Absolute Jump *)
  | anl : Addr Any -> Addr Any -> Instr (* Bitwise AND *)
  | cjne : Addr Any -> Addr Any -> Label -> Instr (* Compare and Jump if Not Equal *)
  | clr : Reg -> Instr (* Clear Register *)
  | cpl : Reg -> Instr (* Complement Register *)
  | da : Instr (* Decimal Adjust *)
  | dec : Addr Any -> Instr (* Decrement Register *)
  | div : Instr (* Divide Accumulator by B *)
  | djnz : Reg -> Label -> Instr (* Decrement Register and Jump if Not Zero *)
  | inc : Reg -> Instr (* Increment Register *)
  (* | jb : (* Jump if Bit Set *) *)
  (* | jbc : (* Jump if Bit Set and Clear Bit *) *)
  | jc : Label -> Instr (* Jump if Carry Set *)
  | jmp : Instr (* Jump to Addr Anyess @A+DPTR *)
  (* | jnb : (* Jump if Bit Not Set *) *)
  | jnc : Label -> Instr (* Jump if Carry Not Set *)
  | jnz : Label -> Instr (* Jump if Accumulator Not Zero *)
  | jz : Label -> Instr (* Jump if Accumulator Zero *)
  | lcall : Label -> Instr (* Long Call *)
  | ljmp : Label -> Instr (* Long Jump *)
  | mov : Addr Any -> Addr Any -> Instr (* Move Memory *)
  | movc_dptr : Instr (* Move Code Memory *)
  | movc_pc : Instr
  | movx_dptr_a : Instr (* Move Extended Memory *)
  | movx_r0_a : Instr
  | movx_r1_a : Instr
  | movx_a_dptr : Instr
  | movx_a_r0 : Instr
  | movx_a_r1 : Instr
  | mul : Instr (* Multiply Accumulator by B *)
  | nop : Instr (* No Operation *)
  (* | orl : Addr -> Addr -> Instr (* Bitwise OR *) *)
  | pop : Addr Any -> Instr (* Pop Value From Stack *)
  | push : Addr Any -> Instr (* Push Value Onto Stack *)
  | ret : Instr(* Return From Subroutine *)
  | reti : Instr (* Return From Interrupt *)
  (* | rl : (* Rotate Accumulator Left *) *)
  (* | rlc : (* Rotate Accumulator Left Through Carry *) *)
  (* | rr : (* Rotate Accumulator Right *) *)
  (* | rrc : (* Rotate Accumulator Right Through Carry *) *)
  (* | setb : (* Set Bit *) *)
  | sjmp : Label -> Instr(* Short Jump *)
  (* | subb : (* Subtract From Accumulator With Borrow *) *)
  | swap : Addr Any -> Addr Any -> Instr (* Swap Accumulator Nibbles *)
  (* | xch : (* Exchange Bytes *) *)
  (* | xchd : (* Exchange Digits *) *)
  (* | xrl : (* Bitwise Exclusive OR       *) *)
.

Inductive CodeBlock : Set :=
  | Seq : Instr -> CodeBlock -> CodeBlock
  | Call : Label -> CodeBlock
  | Jump : Label -> CodeBlock
  | Ret : CodeBlock.


Module CodeHeapSpec <: MapSpec.
  Definition domain := Label.
  Definition image  := CodeBlock.
  Definition beq_Domain := Z_eq_dec.
End CodeHeapSpec.


Module CodeHeapMod := MapFun (CodeHeapSpec).

Definition CodeHeap := CodeHeapMod.Map.

Definition in_codeheap (ch : CodeHeap) (l : Label) : Prop :=
  CodeHeapMod.in_dom l ch.

Definition lookupCH : CodeHeap -> Label -> CodeBlock -> Prop := CodeHeapMod.maps_to.

Definition disjoint_codeheap : CodeHeap -> CodeHeap -> Prop := CodeHeapMod.disjoint.

Definition merge_codeheap : CodeHeap -> CodeHeap -> CodeHeap := CodeHeapMod.merge.
