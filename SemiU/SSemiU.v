(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland Informatics Campus, Saarland University, Saarbrücken, Germany
*)

(* 
  Problem(s):
    Simple Semi-unification
*)

Require Import List.

(* definitions of terms and valuations *)
From Undecidability.SemiU Require Import SemiU_prelim.

(* simple semi unification constraint
  ((a, x), (y, b)) = (a|x|ϵ ≐ ϵ|y|b) *)
Definition constraint : Set := ((bool * nat) * (nat * bool)).

(* constraint semantics, a|x|ϵ ≐ ϵ|y|b is satisfied iff ψa (φ (x)) = πb (φ (y)) *)
Definition sem (φ ψ0 ψ1: valuation) : constraint -> Prop :=
  fun '((a, x), (y, b)) => 
    match φ y with
    | atom _ => False
    | arr s t => (if b then t else s) = substitute (if a then ψ1 else ψ0) (φ x)
    end.

(* is there a substitution φ that solves each constraint? *)
Definition SSemiU (p : list constraint) := exists (φ ψ0 ψ1: valuation), forall (c : constraint), In c p -> sem φ ψ0 ψ1 c.
