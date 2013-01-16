Require Import ZArith.
Require Import common.
Require Import heap.
Require Import reg.
Require Import code.
Require Import state.
Set Implicit Arguments.


(* could try CodeHeap*State*PC *)
Definition World := (CodeHeap * State * CodeBlock)%type.

Definition W_CodeHeap (w : World) : CodeHeap :=
  match w with
    | (ch, _, _) => ch
  end.

Definition W_State (w : World) : State :=
  match w with
    | (_, s, _) => s
  end.

Definition W_Block (w : World) : CodeBlock :=
  match w with
    | (_, _, b) => b
  end.

Definition GetVal (M:Set)(addr:Addr M)(m:Mem)(rf:Regs)(ff:Flags) :=
  match addr with 
    | A_Imm v => v
    | A_Dir i => read' m i
    | A_Reg r => getReg rf r
    (* | A_DPTR =>  *)
    (* | A_COde => *)
    | _ => 0
end.


(* operational semantics for all the Instr *)
Definition NextState (c:Instr)(s:State):option State :=
  let m := S_Mem s in
    let rf := S_Reg s in
      let ff := S_Flag s in
        match c with 
            | add addr =>
              Some (m, setReg rf RA (rf RA + GetVal addr m rf ff) , ff)
            (* lots of instructions here *)
            | _ => None
        end.


Definition Next (c:Instr)(s s':State):Prop :=
  NextState c s = Some s'.

(* rules for jumps *)
Inductive NextWorld : World -> World -> Prop :=
  | nextW_jmp :
      forall (ch:CodeHeap)(M:Mem)(R:Regs)(F:Flags)(code:CodeBlock)(L:Label),
        lookupCH ch L code ->
        NextWorld (ch,(M,R,F),Jump L) (ch,(M,R,F),code)
  | nextW_jnz_eq :
      forall (ch:CodeHeap)(M:Mem)(R:Regs)(F:Flags)(code:CodeBlock)(L:Label),
      R RA = 0 ->
      NextWorld (ch,(M,R,F), Seq (jnz L) code)
                (ch,(M,R,F), code)
  | nextW_jnz_neq :
      forall (ch:CodeHeap)(M:Mem)(R:Regs)(F:Flags)(code newcode:CodeBlock)(L:Label),
        lookupCH ch L code ->
        R RA <> 0 ->
        NextWorld (ch,(M,R,F), Seq (jnz L) code)
                (ch,(M,R,F), newcode)

(* all the other jumps *)
.
  
