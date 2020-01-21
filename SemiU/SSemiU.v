(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Problem(s):
    Simple Semi-unification
*)

Require Import List.

(* definitions of terms and valuations *)
From Undecidability.SemiU Require Import SemiU_prelim.

(* simple semi unification constraint
  ((a, x), (y, b)) mechanizes the constraint (a|x|ϵ ≐ ϵ|y|b) *)
Definition constraint : Set := ((bool * nat) * (nat * bool)).

(* constraint semantics, 
  (φ, ψ0, ψ1) models a|x|ϵ ≐ ϵ|y|b if ψa (φ (x)) = πb (φ (y)) *)
Definition models (φ ψ0 ψ1: valuation) : constraint -> Prop :=
  fun '((a, x), (y, b)) => 
    match φ y with
    | atom _ => False
    | arr s t => (if b then t else s) = substitute (if a then ψ1 else ψ0) (φ x)
    end.

(* are there substitutions (φ, ψ0, ψ1) that model each constraint? *)
Definition SSemiU (p : list constraint) := 
  exists (φ ψ0 ψ1: valuation), forall (c : constraint), In c p -> models φ ψ0 ψ1 c.
