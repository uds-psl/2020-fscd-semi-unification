(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Reduction from:
    Simple Semi-unification (SSemiU)
  to:
    Semi-unification (SemiU)
*)

Require Import List.

(* semi-unification *)
From Undecidability.SemiU Require Import SemiU_prelim SemiU SSemiU.
(* reduction argument *)
From Undecidability.SemiU.SemiU Require SSemiU_to_SemiU_argument.
Module Reduction := SSemiU_to_SemiU_argument.

From Undecidability Require Import Reduction.

(* reduction from simple semi-unification to semi-unification *)
Theorem SSemiU_to_SemiU : SSemiU ⪯ SemiU.
Proof.
  exists (fun p => (Reduction.SSU_to_SU0 p) :: (Reduction.SSU_to_SU1 p) :: nil).
  intro p. constructor.
  exact Reduction.soundness.
  exact Reduction.completeness.
Qed.

Check SSemiU_to_SemiU.
Print Assumptions SSemiU_to_SemiU.
