(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland Informatics Campus, Saarland University, Saarbrücken, Germany
*)

Require Import ssreflect ssrbool ssrfun.
Require Import Arith Psatz.
Require Import List.
Import ListNotations.

(* duplicates argument *)
Lemma copy {A: Prop} : A -> A * A.
Proof. done. Qed.

Lemma itebP {X: Type} {P: bool -> X} {b: bool} : (if b then P true else P false) = P b.
Proof. by case: b. Qed.

(* Forall facts *)
Lemma Forall_nil_iff {X: Type} {P: X -> Prop} : Forall P [] <-> True.
Proof. by constructor. Qed.

Lemma Forall_cons_iff {T: Type} {P: T -> Prop} {a l} :
  Forall P (a :: l) <-> P a /\ Forall P l.
Proof.
  constructor. 
    move=> H. by inversion H.
  move=> [? ?]. by constructor.
Qed.

Lemma Forall_singleton_iff {X: Type} {P: X -> Prop} {x} : Forall P [x] <-> P x.
Proof.
  rewrite Forall_cons_iff. by constructor; [case |].
Qed.

Lemma Forall_app_iff {T: Type} {P: T -> Prop} {A B}: Forall P (A ++ B) <-> Forall P A /\ Forall P B.
Proof.
  elim: A.
    constructor; by [|case].
  move=> ? ? IH /=. rewrite ? Forall_cons_iff ? IH.
  by tauto.
Qed.

(* usage: rewrite ? Forall_norm *)
Definition Forall_norm := (@Forall_app_iff, @Forall_singleton_iff, @Forall_cons_iff, @Forall_nil_iff).
