(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland Informatics Campus, Saarland University, Saarbrücken, Germany
*)

(* 
  Problem(s):
    Semi-unification
*)

Require Import List.

From Undecidability.SemiU Require Import SemiU_prelim.

(* inequality: s ≤ t *)
Definition inequality : Set := (term * term).

(* φ solves s ≤ t, if there is ψ such that ψ (φ (s)) = φ (s) *)
Definition solution (φ : valuation) : inequality -> Prop := 
  fun '(s, t) => exists (ψ : valuation), substitute ψ (substitute φ s) = substitute φ t.

(* is there a substitution φ that solves all inequalities? *)
Definition SemiU (p: list inequality) := exists (φ: valuation), forall (c: inequality), In c p -> solution φ c.
