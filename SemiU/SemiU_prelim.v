(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland Informatics Campus, Saarland University, Saarbrücken, Germany
*)

(* 
  Definition(s):
    Terms
    Valuations
*)

(* terms are built up from atoms and a binary term constructor arr *)
Inductive term : Set :=
  | atom : nat -> term
  | arr : term -> term -> term.

Definition valuation : Set := nat -> term.

(* substitute atomic leaves by corresponding valuation *)
Fixpoint substitute (f: valuation) (t: term) : term :=
  match t with
  | atom n => f n
  | arr s t => arr (substitute f s) (substitute f t)
  end.
