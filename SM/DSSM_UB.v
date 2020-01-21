(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Problem: 
    Uniform Boundedness of Deterministic Simple Stack Machines
*)

Require Import List.
(* definition of deterministic simple stack machines *)
From Undecidability.SM Require Import SSM_prelim.

(* uniform bound for the number of reachable configurations *)
Definition bounded (M: ssm) (n: nat) : Prop := 
  forall (X: config), exists (L: list config), (forall (Y: config), reachable M X Y -> In Y L) /\ length L <= n.

(* given a deterministic simple stack machine M, 
  is M uniformly bounded by some n? *)
Definition DSSM_UB (M : dssm) := exists (n: nat), bounded (proj1_sig M) n.
