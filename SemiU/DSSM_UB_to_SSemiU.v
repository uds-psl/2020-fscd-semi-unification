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
    Simple Semi-unification (SSemiU)
*)

(* uniform boundedness of deterministic simple stack machines *)
From Undecidability.SM Require Import SSM_prelim DSSM_UB.
(* simple semi-unification *)
From Undecidability.SemiU Require Import SemiU_prelim SSemiU.
(* reduction argument *)
From Undecidability.SemiU.SSemiU Require DSSM_UB_to_SSemiU_argument. 
Module Reduction := DSSM_UB_to_SSemiU_argument.

From Undecidability Require Import Reduction.

Theorem DSSM_UB_to_SSemiU : DSSM_UB ⪯ SSemiU.
Proof.
  exists (fun dM => Reduction.SM_to_SUcs (proj1_sig dM)).
  intros [M HM]. constructor.
  exact Reduction.soundness.
  exact Reduction.completeness.
Qed.

Check DSSM_UB_to_SSemiU.
Print Assumptions DSSM_UB_to_SSemiU.
