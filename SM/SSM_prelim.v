(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Definition(s): 
    Deterministic Simple Stack Machines
*)

Require Import List.
Require Import Relation_Operators.

Definition stack : Set := list bool.
Definition state : Set := nat.
(* configuration: left stack, state, right stack *)
Definition config : Set := stack * state * stack. 
(* direction: true = move left, false = move right *)
Definition dir : Set := bool. 
(* stack symbol: true = 1, false = 0 *)
Definition symbol : Set := bool. 
(* instruction: 
  (x, y, a, b, true ) = ax -> by 
  (x, y, b, a, false ) = xb -> ay *)
Definition instruction : Set := state * state * symbol * symbol * dir.
(* simple stack machine: list of instructions *)
Definition ssm : Set := list instruction. 

Inductive step (M : ssm) : config -> config -> Prop :=
  (* transition AaxB -> AybB *)
  | step_l (x y: state) (a b: symbol) (A B: stack) : 
    In (x, y, a, b, true) M -> step M (a::A, x, B) (A, y, b::B)
  (* transition AxbB -> AayB *)
  | step_r (x y: state) (a b: symbol) (A B: stack) : 
    In (x, y, b, a, false) M -> step M (A, x, b::B) (a::A, y, B).

(* step is functional *)
Definition deterministic (M: ssm) := forall (X Y Z: config), step M X Y -> step M X Z -> Y = Z.

(* deterministic simple stack machine *)
Definition dssm := { M : ssm | deterministic M }.

(* reflexive transitive closure of step *)
Definition reachable (M: ssm) : config -> config -> Prop := clos_refl_trans config (step M).
