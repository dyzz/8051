Require Import heap.
Require Import common.
Require Import reg.
Require Import state.
Require Import code.
Require Import machine.
Require Import ZArith.
Require Import List.
Require Import map.

Definition PreCondition := State -> Prop.
Definition Guarantee := State -> State -> Prop.

Definition Pre:=PreCondition.
Definition Gua:=Guarantee.
Definition Spec := (Pre*Gua)%type.

Definition S_Pre (s : Spec) : Pre :=
  match s with
    | (p, _) => p
  end.

Definition S_Gua (s : Spec) : Gua :=
  match s with
    | (_, g) => g
  end.

Definition init_state:State :=
  (empty, fun r:Reg => On, fun f:Flag => false ).


(* Spec Heap which looks like Code Heap *)
Module SHSpec <: MapSpec.
  Definition domain := Label.
  Definition image  := Spec.
  Definition beq_Domain := Z_eq_dec.
End SHSpec.

Module SHMod := MapFun (SHSpec).
Definition SpecHeap := SHMod.Map.

Definition in_specheap (sh : SpecHeap) (l : Label) : Prop :=
  SHMod.in_dom l sh.

Definition lookupSH : SpecHeap -> Label -> Spec -> Prop := SHMod.maps_to.

Definition disjoint_specheap : SpecHeap -> SpecHeap -> Prop := SHMod.disjoint.

Definition merge_specheap : SpecHeap -> SpecHeap -> SpecHeap := SHMod.merge.


Fixpoint infer(sh:SpecHeap)(spec:Spec)(code:CodeBlock) : Prop :=
  let p := S_Pre spec in 
  let g := S_Gua spec in 
  match code with 
      | Jump l =>
        exists p' : Pre , 
          exists g' : Gua ,
            lookupSH sh l (p',g') /\
            (forall s:State, p s -> p' s) /\
            (forall s s':State, p s -> g' s s' -> g s s')
      | Seq (jnz l) code' =>
        exists p1:Pre, exists g1:Gua,
          exists p2:Pre, exists g2:Gua,
            lookupSH sh l (p1,g1) /\
            (forall s : State, p s -> (S_Reg s RA = On) ->
               (p1 s /\ (forall s' : State, g1 s s' -> g s s'))) /\
            (forall s : State, p s -> (S_Reg s RA <> On) ->
               (p2 s /\ (forall s' : State, g2 s s' -> g s s'))) /\
            infer sh (p2,g2) code'
      (* lots of rules here *)
      | Seq c block =>
        exists p' : Pre, exists g' : Gua,
            (forall s, p s -> exists s', Next c s s') /\
            (forall s s': State,(p s -> Next c s s' -> p' s')) /\ 
            (forall s s' s'': State, Next c s s' -> (p s -> g' s' s'' -> g s s'')) /\
            infer sh (p',g') block 
      | _ => True
  end.
            

(* Well formed code heap *)
Definition WF_CH (sh : SpecHeap) (ch : CodeHeap) (sh' : SpecHeap) : Prop :=
  SHMod.sub_dom sh' sh /\ 
  forall (l : Label) (p : Pre) (g : Gua),
    lookupSH sh' l (p, g) -> 
    (exists b, lookupCH ch l b /\ infer sh (p, g) b).


          