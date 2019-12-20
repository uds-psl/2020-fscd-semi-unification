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

Require Import List.
Import ListNotations.
Require Import PeanoNat Psatz.
Require Import Relations.Relation_Operators Relations.Operators_Properties.

Require Import ssreflect ssrfun ssrbool.

(* uniform boundedness of deterministic simple stack machines *)
From Undecidability.SM Require Import SSM_prelim DSSM_UB.
From Undecidability.SM.DSSM Require Import DSSM_facts.

(* simple semi-unification *)
From Undecidability.SemiU Require Import SemiU_prelim SSemiU. 
From Undecidability.SemiU.SSemiU Require Import Enumerable Utils.

(* inject configuration into nat *)
Definition embed : config -> nat := to_nat.
Definition unembed : nat -> config := of_nat.
Definition embedP {X: config} : (unembed (embed X) = X) := enumP.

(* step relation to semi-unification constraints *)
Definition SM_to_SUcs (M: ssm) : list constraint := 
  map (fun '(x, y, a, b, d) => 
    if d then ((a, embed ([], x, [])), (embed ([], y, []), b)) (* ax -> yb *)
    else ((b, embed ([], y, [])), (embed ([], x, []), a)) (* xa -> by *)
    ) M.

Lemma arr_eqI {s t: bool -> term} : (forall (a: bool), s a = t a) -> 
  arr (s false) (s true) = arr (t false) (t true).
Proof. move=> H. by rewrite ? H. Qed.

Section SM.

Context {M : ssm}.
Variable detM : deterministic M.

Notation equiv := (@equiv M).
Notation equiv_dec := (equiv_dec detM).
Notation narrow_dec := (narrow_dec detM).
Notation bound := (@bound M).

Fixpoint nf_aux (i: nat) (X: config) : config :=
  match i with
  | 0 => X
  | S i => if equiv_dec (unembed i) X then nf_aux i (unembed i) else nf_aux i X
  end.

(* normal form, lowest Y such that equiv X Y, definitely exists *)
Definition nf (X: config) : config := nf_aux (embed X) X.

Lemma nf_equiv (X: config) : equiv X (nf X).
Proof.
  rewrite /nf. move: (embed X) => i. elim: i X.
    move=> X /=. by apply: equiv_refl.
  move=> i IH X /=.
  case: (equiv_dec (unembed i) X).
    move=> /equiv_sym H /=. apply: (equiv_trans detM H). by apply: IH.
  move=> /= _. by apply: IH.
Qed.

Lemma nf_equiv_eq_ind (X Y: config) (j: nat) : equiv X Y -> embed X < j -> nf_aux j Y = nf_aux (embed X) X.
Proof.
  elim: j X Y.
    move=> *. by lia.
  move=> i IH X Y HXY HXi /=.
  case: (equiv_dec (unembed i) Y)=> /=.
    move=> /equiv_sym HYi.
    have: (embed X = i \/ embed X < i) by lia. case.
      move=> /copy [+ ->]. move /(f_equal unembed). rewrite embedP. by move=> ->.
    move=> ?. apply: IH.
      apply: equiv_trans; by eassumption.
    done.
  move=> HiY. have: (embed X = i \/ embed X < i) by lia. case.
    move /(f_equal unembed). rewrite embedP. move=> ?. by subst X.
  move=> ?. by apply: IH.
Qed.

Lemma nf_equiv_eq (X Y: config) : equiv X Y -> nf X = nf Y.
Proof.
  have: (embed X = embed Y \/ embed X < embed Y \/ embed Y < embed X) by lia.
  case.
    move /(f_equal unembed). rewrite ? embedP. by move=> ->.
  case.
    move=> + H. move /nf_equiv_eq_ind. by move /(_ _ H).
  move=> + /equiv_sym H. move /nf_equiv_eq_ind. by move /(_ _ H).
Qed.

(* n is 1 + bound - length X.2 *)
Fixpoint ζ (n: nat) (X: config) : term := 
  match n with
  | 0 => atom (embed (nf X))
  | S n => 
      match X with
      | (A, x, B) => 
        if narrow_dec (A, x, B) then arr (ζ n (A, x, B++[false])) (ζ n (A, x, B++[true])) 
        else atom (embed (nf X))
      end
  end.

Definition ψ (a: bool) (n: nat) (i: nat): term := 
  match unembed i with
  | (A, x, B) => ζ (n - length B) (A++[a], x, B)
  end.

Lemma ζ_nilP {n: nat} {x: state} : ζ (S n) ([], x, []) = arr (ζ n ([], x, [false])) (ζ n ([], x, [true])).
Proof. 
  move=> /=. case: (narrow_dec ([], x, [])).
    done.
  move=> H. exfalso. apply: H. exists x, []. by apply: equiv_refl.
Qed. 

Lemma ζ_0P {X: config} : ζ 0 X = atom (embed (nf X)).
Proof. done. Qed.

Lemma ζ_SnP {n: nat} {x: state} {A B: stack} : ζ (S n) (A, x, B) = 
  if narrow_dec (A, x, B) then arr (ζ n (A, x, B++[false])) (ζ n (A, x, B++[true])) else atom (embed (nf (A, x, B))).
Proof. done. Qed.

Lemma SM_to_SUcsP {x y: state} {a b: symbol} : In (a, x, (y, b)) (SM_to_SUcs M) -> exists x' y', 
  x = (embed ([], x', [])) /\
  y = (embed ([], y', [])) /\
  equiv ([a], x', []) ([], y', [b]).
Proof.
  rewrite /SM_to_SUcs in_map_iff. move=> [[[[[x' y'] a'] b'] d]]. case: d.
  - case. case=> <- <- <- <- H.
    exists x', y'. constructor; first done. constructor; first done.
    exists ([], y', [b']). constructor.
      apply: rt_step. by apply: step_l.
    by apply: rt_refl.
  - case. case=> <- <- <- <- H.
    exists y', x'. constructor; first done. constructor; first done.
    exists ([b'], y', []). constructor.
      by apply: rt_refl.
    apply: rt_step. by apply: step_r.
Qed.


Lemma ζ_equivP {n: nat} {x x': state} {A B A' B': stack} : bound n -> equiv (A, x, B) (A', x', B') -> 
  ζ (S n - length B) (A, x, B) = ζ (S n - length B') (A', x', B').
Proof.
  move=> Hn. move Hm: (S n - length B)=> m.
  elim: m A B A' B' Hm.
  - move=> A B A' B' HnB Hxx'.
    have: (S n - length B' = 0 \/ S n - length B' = (S (n - length B'))) by lia. case.
      move=> ->. rewrite ? ζ_0P. f_equal. f_equal. by apply: nf_equiv_eq.
    move=> HnB'. rewrite HnB' ζ_0P ζ_SnP.
    case: (narrow_dec (A', x', B')) => /=; first last.
      move=> _. f_equal. f_equal. by apply: nf_equiv_eq.
    move /equiv_sym in Hxx'.
    move /(narrow_equiv detM Hxx') /Hn. by lia.
  - move=> m IH A B A' B' Hm Hxx'.
    have: (S n - length B' = 0 \/ S n - length B' = S (n - length B')) by lia. case.
      move=> HnB'. rewrite HnB' ζ_0P ζ_SnP.
      case: (narrow_dec (A, x, B)) => /=; first last.
        move=> _. f_equal. f_equal. by apply: nf_equiv_eq.
      move /(narrow_equiv detM Hxx') /Hn. by lia.
    move=> ->. rewrite ? ζ_SnP.
    case: (narrow_dec (A, x, B)); case: (narrow_dec (A', x', B'))=> /=.
    + move=> _ _. apply: (arr_eqI (s := fun=> ζ _ _) (t := fun=> ζ _ _)).
      move=> b. have -> : n - length B' = S n - length (B' ++ [b]).
          rewrite app_length /length. by lia.
      apply: IH. 
        rewrite app_length /length -/(length _). by lia.
      by apply: equiv_appR.
    + by move=> + /(narrow_equiv detM Hxx').
    + by move=> /(narrow_equiv detM ((iffLR equiv_sym) Hxx')).
    + move=> _ _. f_equal. f_equal. by apply: nf_equiv_eq.
Qed.

Lemma ψP {a: bool} {n: nat} {X: config} : ψ a n (embed X) = 
  match X with
  | (A, x, B) => ζ (n - length B) (A++[a], x, B)
  end.
Proof. by rewrite /ψ embedP. Qed.

Lemma ψζP {n: nat} {x: state} {A B: stack} {a: bool} : bound n -> 
  ζ (S n - length B) (A ++ [a], x, B) = substitute (ψ a (S n)) (ζ (S n - length B) (A, x, B)).
Proof.
  rewrite /bound => Hn. move Hm: (S n - length B)=> m.
  elim: m x A B Hm.
  - move=> x A B Hm.
    rewrite ? ζ_0P => /=. rewrite ψP.
    move HAxB: (nf (A, x, B)) => [[A' x'] B'].
    have: S n - length B' = 0 \/ S n - length B' > 0 by lia. case.
      move=> ->. rewrite ζ_0P. f_equal. f_equal. 
      apply: nf_equiv_eq. apply: equiv_appL. 
      rewrite -HAxB. by apply: nf_equiv.
    move=> ?.
    have Hxx': equiv (A' ++ [a], x', B') (A ++ [a], x, B).
      apply: equiv_appL. rewrite equiv_sym -HAxB. by apply: nf_equiv.
    rewrite (ζ_equivP Hn Hxx').
    by rewrite Hm ζ_0P.
  - move=> m IH x A B Hm.
    rewrite ? ζ_SnP. case: (narrow_dec (A, x, B)).
    (* AxB is narrow *)
    + move=> /= /(narrow_appL (a := a)) => ?. case: (narrow_dec (A ++ [a], x, B)); first last.
        done.
      move=> _ /=. apply: (arr_eqI (s := fun => ζ _ _) (t := fun => substitute _ _)).
      move=> b. apply: IH. rewrite app_length /length -/(length _). by lia.
    + move=> _ /=. rewrite -(ζ_SnP (A := A ++ [a])).
      rewrite ψP.  move HAxB: (nf (A, x, B)) => [[A' x'] B'].
      rewrite -Hm.
      (* prove before induction*)
      have Hxx': equiv (A ++ [a], x, B) (A' ++ [a], x', B').
        apply: equiv_appL. rewrite -HAxB. by apply: nf_equiv.
      by rewrite (ζ_equivP Hn Hxx').
Qed.

End SM.

(* if M is uniformly bounded, 
  then the constructed simple semi-unification instance has a solution *)
Lemma soundness {M: dssm} : DSSM_UB M -> SSemiU (SM_to_SUcs (proj1_sig M)).
Proof.
  Opaque ζ ψ.
  case: M=> M detM. rewrite /DSSM_UB /SSemiU. move=> /= [n /(actual_bounded_narrow detM)].
  move: (n+n) => {}n HnM.
  exists (fun i => ζ detM (S n) (unembed i)), (ψ detM false (S n)), (ψ detM true (S n)).
  case=> [[a x]] => [[y b]] /=. move /SM_to_SUcsP => [x' [y' [? [?]]]]. 
  subst x y. move: x' y' => x y.
  move /equiv_sym => Hxy. rewrite ? embedP. 
  rewrite ζ_nilP. rewrite (itebP (P := fun _ => ζ _ _ _)).
  have {1}-> : (n = S n - 1) by lia.
  rewrite (ζ_equivP _ HnM Hxy) => /=.
  rewrite (itebP (P := fun=> ψ _ _ _)).
  have {1 3}->: S n = S n - 0 by lia.
  have := (ψζP _ HnM (A := []) (B := [])). apply.
Qed.

(* reduction completeness *)

Fixpoint term_depth_bound (t: term) : nat :=
  match t with
  | atom _ => 1
  | arr s t => 1 + (term_depth_bound s) + (term_depth_bound t)
  end.

Fixpoint depth_bound (φ: valuation) (xs: list state) : nat :=
  match xs with
  | [] => 1
  | x :: xs => 1 + term_depth_bound (φ x) + depth_bound φ xs
  end.

Lemma depth_boundP {φ: valuation} {x: state} {xs: list state} : In x xs -> term_depth_bound (φ x) <= depth_bound φ xs.
Proof.
  elim: xs.
    done.
  move=> y xs IH /=. case.
    move=> ?. subst. by lia.
  move /IH. by lia.
Qed.

Fixpoint descend (t: term) (B: stack) {struct B} : option term :=
  match B with
  | [] => Some t
  | b :: B => 
    match t with
    | atom _ => None
    | arr s t => descend (if b then t else s) B
    end
  end.

Fixpoint ascend (ψ0 ψ1: valuation) (t: term) (A: stack) : term :=
  match A with
  | [] => t
  | a :: A => ascend ψ0 ψ1 (substitute (if a then ψ1 else ψ0) t) A
  end.

Lemma ascend_arr {ψ0 ψ1: valuation} {s t: term} {A: stack} : 
  ascend ψ0 ψ1 (arr s t) A = arr (ascend ψ0 ψ1 s A) (ascend ψ0 ψ1 t A).
Proof.
  elim: A s t.
    done.
  move=> a A IH s t /=. by rewrite IH.
Qed.

Definition interpret (φ ψ0 ψ1: valuation) (X: config) : option term :=
  match X with 
  | (A, x, B) => descend (ascend ψ0 ψ1 (φ (embed ([], x, []))) A) B
  end.

Lemma Forall_mapP {X Y : Type} {P : Y -> Prop} {f : X -> Y} {l : list X} : 
  Forall P (map f l) <-> Forall (fun x => P (f x)) l.
Proof.
  elim: l.
    move=> /=. by constructor.
  move=> a l IH /=. by rewrite ? Forall_norm IH.
Qed.

Lemma interpretP {M: ssm} {X Y: config} {φ ψ0 ψ1: valuation} : 
  Forall (sem φ ψ0 ψ1) (SM_to_SUcs M) -> reachable M X Y -> interpret φ ψ0 ψ1 X = interpret φ ψ0 ψ1 Y.
Proof.
  move=> HM. elim.
  - move=> {}X {}Y. case.
    + move=> x y a b A B.
      move: HM. rewrite /SM_to_SUcs. rewrite Forall_mapP Forall_forall => HM. 
      move /HM. rewrite /sem /interpret.
      case: (φ (embed ([], y, []))).
        done.
      move=> s t. case: a; case: b; move=> -> /=.
      all: by rewrite ascend_arr=> /=.
    + move=> x y a b A B.
      move: HM. rewrite /SM_to_SUcs. rewrite Forall_mapP Forall_forall => HM. 
      move /HM. rewrite /sem /interpret.
      case: (φ (embed ([], x, []))).
        done.
      move=> s t. case: a; case: b; move=> -> /=.
      all: by rewrite ascend_arr=> /=.
  - done.
  - by move=> > ? ->.
Qed.

Lemma descendP {s t: term} {B: list symbol} : descend s B = Some t -> length B <= term_depth_bound s.
Proof.
  elim: B s t.
    move=> /= *. by lia.
  move=> b B IH. case=> /=. 
    done.
  move=> > /IH. case: b; by lia.
Qed.

(* if the constructed simple semi-unification instance has a solution, 
  then M is uniformly bounded *)
Lemma completeness {M: dssm}: SSemiU (SM_to_SUcs (proj1_sig M)) -> DSSM_UB M.
Proof.
  case: M=> M detM /=. rewrite /SSemiU /DSSM_UB.
  move=> [φ [ψ0 [ψ1]]]. rewrite -Forall_forall => Hφ.
  pose f x := embed (([], x, []) : config).
  apply: (bounded_actual_bounded detM (n := depth_bound φ (map f (enum_states M)))).
  move=> /= Z x y A B Hx Hy.
  have: @equiv M ([], y, B) (A, x, []).
    eexists. constructor; by eassumption.
  move /enum_states_equiv. case.
    case=> *. subst=> /=. by lia.
  move=> /= /(in_map f) /depth_boundP => /(_ φ) Hfy. 
  move: Hx => /interpretP. move /(_ _ _ _ Hφ)=> Hx.
  move: Hy => /interpretP. move /(_ _ _ _ Hφ). rewrite -Hx /interpret.
  move=> /=. move /descendP.
  move: Hfy. rewrite /f. move: (length B) => ?.
  clear. by lia.
Qed.
