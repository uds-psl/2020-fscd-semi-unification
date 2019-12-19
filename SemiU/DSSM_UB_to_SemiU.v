(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland Informatics Campus, Saarland University, Saarbrücken, Germany
*)

(* 
  Reduction from:
    Uniform Boundedness of Deterministic Simple Stack Machines (DSSM_UB)
  to:
    Semi-unification (SemiU)
*)

(* uniform boundedness of deterministic simple stack machines *)
From Undecidability.SM Require Import SSM_prelim DSSM_UB.
(* simple semi-unification *)
From Undecidability.SemiU Require Import SemiU_prelim SemiU SSemiU.
(* reduction argument *)
From Undecidability.SemiU Require Import DSSM_UB_to_SSemiU SSemiU_to_SemiU.

From Undecidability Require Import Reduction.

Theorem DSSM_UB_to_SemiU : DSSM_UB ⪯ SemiU.
Proof.
  apply (reduces_transitive DSSM_UB_to_SSemiU).
  exact SSemiU_to_SemiU.
Qed.

Check DSSM_UB_to_SemiU.
Print Assumptions DSSM_UB_to_SemiU.
