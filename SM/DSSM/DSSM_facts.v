(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Facts on:
    Deterministic Simple Stack Machines
*)

Require Import List.
Import ListNotations.
Require Import PeanoNat Psatz.
Require Import Relations.Relation_Operators Relations.Operators_Properties.

Require Import ssreflect ssrfun ssrbool.

(* uniform boundedness of deterministic simple stack machines *)
From Undecidability.SM Require Import SSM_prelim DSSM_UB.

From Undecidability.SM.DSSM Require Import Utils.

(* width of a configuration *)
Definition width : config -> nat := fun '(A, _, B) => length A + length B.

Section DSSM.

Context {M : ssm}.
Variable detM : deterministic M.

(* reachability is monotone wrt. stacks *)
Lemma reachable_app {x x': state} {A B A' B' C D: stack} :
  reachable M (A, x, B) (A', x', B') -> reachable M (A++C, x, B++D) (A'++C, x', B'++D).
Proof.
  move HX: (A, x, B) => X. move HX': (A', x', B') => X'.
  move=> H. elim: H C D x x' A B A' B' HX HX'; clear.
  - move=> X X'. case; clear. 
    + move=> > H >. case=> -> -> ->. case=> -> -> ->.
      apply: rt_step. by apply: step_l.
    + move=> > H >. case=> -> -> ->. case=> -> -> ->.
      apply: rt_step. by apply: step_r.
  - move=> > <-. case=> -> -> ->.
    by apply: rt_refl.
  - move=> X [[A' x'] B'] Z HXY IHXY HYZ IHYZ *.
    apply: rt_trans; [by apply: IHXY | by apply: IHYZ].
Qed.

(* step is confluent *)
Lemma reachable_confluent {X X1 X2: config} : reachable M X X1 -> reachable M X X2 -> 
  exists (Y: config), reachable M X1 Y /\ reachable M X2 Y.
Proof.
  move=> /(clos_rt_rt1n config) H /(clos_rt_rt1n config).
  elim: H X2; move: detM; clear=> detM.
    move=> X X2 HX.
    exists X2. constructor; [by apply: clos_rt1n_rt | by apply: rt_refl].
  move=> X Y Z HXY HYZ IH X2. case.
    exists Z. constructor.
      by apply: rt_refl.
    apply: clos_rt1n_rt.
    apply: Relation_Operators.rt1n_trans; by eassumption.
  move=> Y' Z'. move /(detM _ _ _ HXY)=> ?. subst Y'.
  by move /IH.
Qed.

(* joinability of configurations *)
Definition equiv (X Y: config) := exists (Z: config), reachable M X Z /\ reachable M Y Z. 

Lemma equiv_refl {X: config} : equiv X X.
Proof. exists X. constructor; by apply: rt_refl. Qed.

Lemma equiv_sym {X Y: config} : equiv X Y <-> equiv Y X.
Proof. constructor; move=> [Z [? ?]]; exists Z; by constructor. Qed.

Lemma equiv_trans {X Y Z: config} : equiv X Y -> equiv Y Z -> equiv X Z.
Proof.
  move=> [Z0 [? HYZ0]] [Z1 [HYZ1 ?]].
  have [Z2 [? ?]] := (reachable_confluent HYZ0 HYZ1).
  exists Z2. constructor; apply: rt_trans; by eassumption.
Qed.

(* joinability is monotone wrt. stacks *)
Lemma equiv_app {x x': state} {A B A' B' C D: stack} : equiv (A, x, B) (A', x', B') -> 
  equiv (A++C, x, B++D) (A'++C, x', B'++D).
Proof.
  move=> [[[A'' x''] B''] [? ?]].
  exists (A''++C, x'', B''++D). constructor; by apply: reachable_app. 
Qed.

Corollary equiv_appR {x x': state} {A B A' B': stack} {b: bool} : equiv (A, x, B) (A', x', B') -> 
  equiv (A, x, B ++ [b]) (A', x', B' ++ [b]).
Proof. move /(equiv_app (C := []) (D := [b])). by rewrite ? app_nil_r. Qed.

Corollary equiv_appL {x x': state} {A B A' B': stack} {a: bool} : equiv (A, x, B) (A', x', B') -> 
  equiv (A++[a], x, B) (A'++[a], x', B').
Proof. move /(equiv_app (C := [a]) (D := [])). by rewrite ? app_nil_r. Qed.

(* list all stacks of length n *)
Fixpoint enum_stacks (n: nat) : list stack :=
  if n is S n then (map (cons true) (enum_stacks n)) ++ (map (cons false) (enum_stacks n)) else [[]].

(* all stacks of fixed length are enumerated *)
Lemma enum_stacksP {A: stack} : In A (enum_stacks (length A)).
Proof.
  elim: A => /=.
    by left.
  move=> a A IH. rewrite in_app_iff ? in_map_iff. 
  case: a; [left | right]; exists A; by constructor.
Qed.

(* list all states occurring in M' *)
Fixpoint enum_states (M': ssm) : list state := 
  match M' with
  | [] => []
  | (x, y, _, _, _) :: M' => x :: y :: enum_states M'
  end.

Lemma enum_statesP {x y: state} {a b: symbol} {d: dir} : In (x, y, a, b, d) M -> 
  In x (enum_states M) /\ In y (enum_states M).
Proof.
  elim: M x y a b d=> /=; clear; first done.
  move=> i M IH >. case.
    move=> ->. constructor; [by left | by right; left].
  move /IH=> [? ?]. move: i=> [[[[? ?] ?] ?] ?]. constructor; right; by right.
Qed.

Definition get_state : config -> state :=
  fun '(_, x, _) => x.

Lemma enum_states_step {X Y: config} : step M X Y -> 
  In (get_state X) (enum_states M) /\ In (get_state Y) (enum_states M).
Proof.
  case=> > /enum_statesP [? ?]; by constructor.
Qed. 

(* reachable configuration are either equal or have a state occurring in M *)
Lemma enum_states_reachable {X Y: config} : reachable M X Y -> 
  X = Y \/ (In (get_state X) (enum_states M) /\ In (get_state Y) (enum_states M)).
Proof.
  elim.
  - move=> ? ? /enum_states_step ?. by right.
  - move=> ?. by left.
  - move=> > _ + _. case.
      move=> ->. case.
        move=> ->. by left.
      move=> ?. by right.
    move=> [? ?]. case.
      move=> <-. by right.
    move=> [? ?]. by right.
Qed.  

(* list all configurations with stack lengths lA and lB *)
Definition enum_configs (lA lB: nat) : list config := 
  list_prod (list_prod (enum_stacks lA) (enum_states M)) (enum_stacks lB).

(* all configurations with states occurring in M are listed *)
Lemma enum_configsP (x: state) (A B: stack) : In x (enum_states M) -> 
  In (A, x, B) (enum_configs (length A) (length B)).
Proof.
  move=> Hx. rewrite /enum_configs ? in_prod_iff.
  have ? := enum_stacksP. by constructor; first constructor.
Qed.

(* space X is an overapproximation of reachable states from X *)
Definition space (X: config) : list config :=
  X :: flat_map (fun i => enum_configs i (width X - i)) (seq 0 (width X + 1)).

(* reachability preserves configuration width *)
Lemma reachable_width {X Y: config} : reachable M X Y -> width X = width Y.
Proof.
  elim; clear.
  - move=> X Y. case=> *; rewrite /width /length; by lia.
  - done.
  - move=> *. by lia.
Qed.

Lemma spaceP {X Y: config} : In (get_state X) (enum_states M) -> width X = width Y -> In X (space Y).
Proof.
  rewrite /space. case: X => [[A x] B]. move=> HX <-. right.
  apply /in_flat_map. exists (length A). constructor=> /=.
    apply /in_seq. by lia.
  have -> : (length A + length B - length A = length B) by lia.
  by apply: enum_configsP.
Qed.

Lemma spaceP0 {X Y: config} : reachable M X Y -> In Y (space X).
Proof.
  move=> /copy [/enum_states_reachable + /reachable_width]. case.
    move=> <- _. by left.
  move=> [_ /spaceP] + ?. by apply.
Qed.

Lemma spaceP1 {X Y: config} : reachable M X Y -> In X (space Y).
Proof.
  move=> /copy [/enum_states_reachable + /reachable_width]. case.
  move=> <- _. by left.
  move=> [/spaceP + _] ?. by apply.
Qed.

Lemma space_equivP {X Y: config} : equiv X Y -> In Y (space X).
Proof.
  move=> [Z] /copy [[/reachable_width + /reachable_width]] => <- /spaceP HY. 
  move=> [/enum_states_reachable + /enum_states_reachable]. case.
    move=> <-. case.
      move=> <-. by left.
    move=> [? ?]. by apply: HY.
  move=> [? ?]. case.
    move=> ?. subst Z. by apply: HY.
  move=> [? ?]. by apply: HY.
Qed.

Definition get_left : config -> stack :=
  fun '(A, _, _) => A.

Definition get_right : config -> stack :=
  fun '(_, _, B) => B.

(* step relation is decidable *)
Lemma step_dec (X Y: config) : decidable (step M X Y).
Proof.
  case: (Exists_dec (fun '(x, y, a, b, d) => 
    (get_state X, get_state Y, if d then get_left X else b :: get_left X, if d then b :: get_right X else get_right X) =
    (x, y, if d then a :: get_left Y else get_left Y, if d then get_right Y else a :: get_right Y)) M).
  - move=> [[[[x y] a] b] d]. do 4 (decide equality).
  - move=> H. left. move: H. rewrite Exists_exists.
    move=> [[[[[x y] a] b] d]]. case: d.
      move=> [?]. move: X Y => [[A ?] ?] [[? ?] B] /=. case: A; case: B=> //=.
      move=> >. case=> *. subst.
      by apply: step_l.
    move=> [?]. move: X Y => [[? ?] B] [[A ?] ?] /=. case: A; case: B=> //=.
    move=> >. case=> *. subst.
    by apply: step_r.
  - move=> H. right. move=> HXY. apply: H. rewrite Exists_exists. case: HXY.
      move=> x y a b A B H. exists (x, y, a, b, true) => /=. by constructor.
    move=> x y a b A B H. exists (x, y, b, a, false) => /=. by constructor.
Qed.

(* deterministic step function *)
Definition step_f (X: config) : config :=
  if find (fun Z => step_dec X Z) (space X) is Some Y then Y else X.

Lemma step_fI {X Y: config} : step M X Y -> step_f X = Y.
Proof.
  move /copy => [HXY] /(rt_step config) /spaceP0. rewrite /step_f.
  move: (space X) => L. elim: L HXY; first done.
  move=> Z L IH HXY /=. case.
    move=> ?. subst Z. by case: (step_dec X Y).
  move /IH => {}IH. case: (step_dec X Z) => /=.
    by move /detM => /(_ _ HXY) ->.
  move=> _. by apply: IH.
Qed.

Lemma step_fE {X: config} : step_f X = X \/ step M X (step_f X).
Proof.
  rewrite /step_f.
  move HoZ: (find (fun Z : config => step_dec X Z) (space X)) => oZ.
  case: oZ HoZ.
    move=> Z /(@find_some config) [_]. case: (step_dec X Z); last done.
    move=> *. by right.
  move=> *. by left.
Qed.

Lemma reachable_fE {X Y: config} : reachable M X Y -> 
  exists (n: nat), Nat.iter n step_f X = Y.
Proof.
  rewrite /reachable. move /(clos_rt_rtn1 config). elim.
  + by exists 0.
  + move=> > /step_fI ? _ [n ?]. exists (S n) => /=. by subst.
Qed.

Lemma reachable_fI {X: config} {n: nat}: reachable M X (Nat.iter n step_f X).
Proof.
  elim: n X.
    move=> ?. by apply: rt_refl.
  move=> n IH X /=. rewrite /reachable. 
  apply: rt_trans.
    apply: IH.
  move: (Nat.iter n step_f X)=> Y.
  rewrite /step_f. elim: (space Y) => /=.
    by apply: rt_refl.
  move=> Z L IH2. case: (step_dec Y Z)=> /=.
    move=> ?. by apply: rt_step.
  move=> _. by apply: IH2.
Qed.

Lemma step_f_bounded {X Y: config} {n: nat} {L: list config} : 
  (Forall (fun i => In (Nat.iter i step_f X) L) (seq 0 n)) -> Nat.iter n step_f X = Y -> 
  exists (m: nat), m <= length L /\ Nat.iter m step_f X = Y.
Proof.
  elim /(measure_ind id): n L X Y. case.
    move=> /= *. exists 0. constructor; last done.
    by lia.
  move=> n IH L X Y. rewrite seq_last.
  move=> /=. move HZ: (Nat.iter n step_f X) => Z.
  rewrite ? Forall_norm. move=> [HL /(@in_split config)]. move=> [L1 [L2 ?]].
  case: (Exists_dec (fun i => Nat.iter i step_f X = Z) (seq 0 n)).
  - do 4 (decide equality).
  - rewrite Exists_exists => [[i]]. rewrite in_seq => [[? ?]] ?.
    have: Nat.iter (1+i) step_f X = Y. 
      subst => /=. by f_equal.
    apply /IH; first by lia.
    move: HL. rewrite ? Forall_forall. move=> + j => /(_ j). rewrite ? in_seq.
    move=> + ?. apply. by lia.
  - move=> HnZ ?. subst L. move: (HZ). move /(IH n ltac:(lia) (L1++L2)). apply: unnest.
      move: HL. rewrite ? Forall_forall. move=> + j => /(_ j). rewrite ? in_seq.
      move=> + Hj => /(_ Hj). rewrite ? in_app_iff => /=.
      { case; last case.
        + move=> ?. by left.
        + move=> H. exfalso. apply: HnZ. rewrite Exists_exists.
          exists j. rewrite in_seq. subst. by constructor.
        + move=> ?. by right. }
    move=> [m]. rewrite ? app_length. move=> [? ?] /=.
    exists (S m) => /=. constructor; first by lia.
    clear HZ. by subst.
Qed.

Corollary step_f_space {X Y: config} : reachable M X Y -> 
  exists (n: nat), n <= length (space X) /\ Nat.iter n step_f X = Y.
Proof.
  move /reachable_fE => [n]. move /(step_f_bounded (L := (space X))).
  apply.
  rewrite Forall_forall. move=> i _. move HZ: (Nat.iter i step_f X)=> Z.
  apply: spaceP0. subst Z. by apply: reachable_fI.
Qed.

(* reachability is decidable *)
Lemma reachable_dec (X Y: config) : decidable (reachable M X Y).
Proof.
  case: (Exists_dec (fun i => Nat.iter i step_f X = Y) (seq 0 (1+ length (space X)))).
  - move=> i. do 4 (decide equality).
  - move=> + /ltac:(left). rewrite Exists_exists. move=> [n [_ <-]]. by apply: reachable_fI.
  - move=> + /ltac:(right) /step_f_space => + [n [? ?]]. apply.
    rewrite Exists_exists. exists n. constructor; last done.
    rewrite in_seq. by lia.
Qed.

(* joinability is decidable *)
Lemma equiv_dec (X Y: config) : decidable (equiv X Y).
Proof.
  case: (Exists_dec (fun Z => reachable M X Z /\ reachable M Y Z) (space X)).
  - move=> Z. case: (reachable_dec X Z) => ?; case: (reachable_dec Y Z) => ?; by firstorder done.
  - move=> + /ltac:(left). rewrite Exists_exists. move=> [Z [? ?]].
    eexists. by eassumption.
  - move=> + /ltac:(right) => + [Z [? ?]]. apply. rewrite Exists_exists.
    exists Z. constructor.
      by apply: spaceP0.
    by constructor.
Qed.

(* X is narrow iff X ~ A|x|ϵ *)
Definition narrow (X: config) := exists (x: state) (A: stack), equiv X (A, x, []). 

(* narrow X is decidable *)
Lemma narrow_dec (X: config) : decidable (narrow X).
Proof. 
  case: (Exists_dec (fun Y => get_right Y = [] /\ equiv X Y) (space X)).
  - move=> [[A y]]. case; first last.
      move=> >. right. by move=> [+].
    case: (equiv_dec X (A, y, [])).
      move=> ?. by left.
    move=> ?. right. by move=> [_].
  - move=> + /ltac:(left). rewrite Exists_exists. move=> [[[A y] B] [_]] /= [->] ?.
    by exists y, A.
  - move=> + /ltac:(right) => + [y [A HX]]. rewrite Exists_exists. apply.
    exists (A, y, []). constructor; last done.
    by apply: space_equivP.
Qed.

Lemma narrow_appL {x: state} {A B: stack} {a: bool} : narrow (A, x, B) -> narrow (A ++ [a], x, B).
Proof.
  move=> [y [A']].
  move /(equiv_app (C := [a]) (D := [])). rewrite ? app_nil_r => ?.
  do 2 eexists. by eassumption.
Qed.


Lemma step_rendundant_prefix {x y: state} {A B C D: stack} {a: symbol}: 
  step M (A++[a], x, B) (C++[a], y, D) -> step M (A, x, B) (C, y, D).
Proof.
  move HX: (A ++ [a], x, B) => X. move HY: (C ++ [a], y, D) => Y.
  move=> H. case: H HX HY.
  - move=> > ?. move=> H1 H2. case: H2 H1.
    move=> <- ? ->. case. rewrite app_comm_cons. move /app_inv_tail => -> *.
    subst. by apply: step_l.
  - move=> > ?. case=> <- ? ->. case. rewrite app_comm_cons. move /app_inv_tail => -> *.
    subst. by apply: step_r.
Qed.
  

Lemma remove_rendundant_suffix0 {x y: state} {A B C D: stack} {a: symbol}: reachable M (A++[a], x, B) (C, y, D) -> 
  (exists (x': state) (B': stack), reachable M (A++[a], x, B) ([], x', B')) \/
  (exists (C': stack), C = C' ++ [a] /\ reachable M (A, x, B) (C', y, D)).
Proof.
  move HX: (A ++ [a], x, B) => X. move HY: (C, y, D) => Y.
  move=> H. elim: H x y A B C D a HX HY.
  - move=> ? ?. case.
    + move=> x y a b. case.
      * move=> B ? > _ _. left. exists y, (b::B). apply: rt_step. by apply: step_l.
      * move=> a' A B ? >.
        have [A'' [a'' HA]] := (@exists_last _ (a' :: A) ltac:(done)).
        rewrite HA.
        case. rewrite app_comm_cons. move /(@app_inj_tail symbol). case=> ? ? ? ?. case=> ? ? ?. subst.
        right. exists A''. constructor; first done.
        apply: rt_step. by apply: step_l. 
    + move=> > ? >. case=> <- -> ->. case=> -> -> ->. right. eexists. constructor.
        rewrite app_comm_cons. by reflexivity.
      apply: rt_step. by apply: step_r.  
  - move=> > <-. case=> -> -> ->. right. eexists. constructor.
      by reflexivity.
    by apply: rt_refl.
  - move=> {}X {}[[A' x'] B'] Z. move=> _ IH1 _ IH2 x y A B C D a ? ?. subst.
    have := (IH1 x x' A B A'  B' a ltac:(done) ltac:(done)). case.
      move=> ?. by left.
    move=> [C' [? Hxx']]. subst.
    have := (IH2 x' y C' B' C D a ltac:(done) ltac:(done)). case.
      move=> [x'' [B'' ?]]. left.
      exists x'', B''. apply: rt_trans; last by eassumption.
      have -> : (B = B ++ []) by rewrite app_nil_r.
      have -> : (B' = B' ++ []) by rewrite app_nil_r.
      by apply: reachable_app.
    move=> [C'' [? ?]]. subst. right.
    exists C''. constructor; first done.
    apply: rt_trans; by eassumption.
Qed.

Lemma remove_rendundant_suffix1 {x y: state} {A B C D: stack} {b: symbol}: reachable M (A, x, B++[b]) (C, y, D) -> 
  (exists (x': state) (A': stack), reachable M (A, x, B++[b]) (A', x', [])) \/
  (exists (D': stack), D = D' ++ [b] /\ reachable M (A, x, B) (C, y, D')).
Proof.
  move HX: (A, x, B ++ [b]) => X. move HY: (C, y, D) => Y.
  move=> H. elim: H x y A B C D b HX HY.
  - move=> ? ?. case.
    + move=> > ? >. case=> -> -> <-. case=> -> -> ->. right. eexists. constructor.
        rewrite app_comm_cons. by reflexivity.
      apply: rt_step. by apply: step_l.    
    + move=> x y a b A. case.
      * move=> ? > _ _. left. exists y, (a::A). apply: rt_step. by apply: step_r.
      * move=> b' B ? >.
        have [B'' [b'' HB]] := (@exists_last _ (b' :: B) ltac:(done)).
        rewrite HB.
        case=> ? ?. rewrite app_comm_cons. move /(@app_inj_tail symbol). case=> ? ?. case=> ? ? ?. subst.
        right. exists B''. constructor; first done.
        apply: rt_step. by apply: step_r. 
  - move=> > <-. case=> -> -> ->. right. eexists. constructor.
      by reflexivity.
    by apply: rt_refl.
  - move=> {}X {}[[A' x'] B'] Z. move=> _ IH1 _ IH2 x y A B C D b ? ?. subst.
    have := (IH1 x x' A B A'  B' b ltac:(done) ltac:(done)). case.
      move=> ?. by left.
    move=> [D' [? Hxx']]. subst.
    have := (IH2 x' y A' D' C D b ltac:(done) ltac:(done)). case.
      move=> [x'' [A'' ?]]. left.
      exists x'', A''. apply: rt_trans; last by eassumption.
      have -> : (A = A ++ []) by rewrite app_nil_r.
      have -> : (A' = A' ++ []) by rewrite app_nil_r.
      by apply: reachable_app.
    move=> [D'' [? ?]]. subst. right.
    exists D''. constructor; first done.
    apply: rt_trans; by eassumption.
Qed.

(* if M is bounded, then the sizes of right stacks of reachable configurations differ at most by n *)
Lemma actual_bounded_length {n: nat} {x y: state} {A B C D: stack} : bounded M n -> reachable M (A, x, B) (C, y, D) -> 
  length B <= length D + n /\ length D <= length B + n.
Proof.
  move /(_ (A, x, B)) => [L [HL1 HL2]].
  move /reachable_fE => [m]. move /(step_f_bounded (L := L)).
  apply: unnest.
    rewrite Forall_forall => m' _. apply: HL1. by apply: reachable_fI.
  move=> [{}m [?]].
  move=> H. suff: length B <= length D + m /\ length D <= length B + m by lia.
  move: detM H. clear=> detM.
  elim: m x y A B C D.
    move=> > /=. case=> *. subst. by lia.
  move=> m IH x y A B C D /=.
  move HZ: (Nat.iter m step_f (A, x, B)) => [[A' x'] B'].
  move: HZ. move /IH => [HBB' HB'B].
  case: (step_fE (X := (A', x', B'))).
    move=> ->. case=> *. subst. by lia.
  move=> + H. move: H => ->. move HX: (A', x', B') => X. move HY: (C, y, D) => Y.
  move=> H. case: H HX HY.
  - move=> > ?. case=> ? ? ?. case=> ? ? ?. subst. move=> /=. by lia.
  - move=> > ?. case=> ? ? ?. case=> ? ? ?. subst. move: HBB' HB'B => /=. by lia.
Qed.

(* bound on size of the right stack for narrow configurations with empty left stack *)
Definition bounded' (n: nat) : Prop := forall (c: config) (x y: state) (A B: stack), 
  reachable M (A, x, []) c -> reachable M ([], y, B) c -> length B <= n.

Lemma bounded_reachable_length0 {n: nat} {x y: state} {A B D: stack} : 
  bounded' n -> reachable M (A, x, B) ([], y, D) -> length A <= n.
Proof.
  move=> Hn. elim /(measure_ind (@length symbol)) : B D. case.
    move=> ? D. move /copy => [/reachable_width] /=.
    rewrite Nat.add_0_r => ->. move /Hn. apply. by apply: rt_refl.
  move=> b B. have [B' [b' ->]] := (@exists_last _ (b :: B) ltac:(done)).
  move=> IH D. move /copy => [Hx].
  move /remove_rendundant_suffix1. case.
    move=> [x' [A']]. move /reachable_confluent. move /(_ _ ltac:(eassumption)).
    move=> [Y [HY1]]. move /copy => [HY2]. move /Hn. move /(_ _ _ ltac:(eassumption)).
    move: Hx => /reachable_width /=. by lia.
  move=> [D' [?]]. subst. move /IH => /=. apply. rewrite app_length /length. by lia.
Qed.

Lemma bounded_reachable_length1 {n: nat} {x y: state} {A B C: stack} : 
  bounded' n -> reachable M (A, x, B) (C, y, []) -> length B <= n.
Proof.
  move=> Hn. elim /(measure_ind (@length symbol)) : A C. case.
    move=> ? C /Hn. apply. by apply: rt_refl.
  move=> a A. have [A' [a' ->]] := (@exists_last _ (a :: A) ltac:(done)).
  move=> IH C. move /copy => [Hx].
  move /remove_rendundant_suffix0. case.
    move=> [x' [B']]. move /reachable_confluent. move /(_ _ ltac:(eassumption)).
    move=> [Y [HY1]]. move /copy => [HY2]. move /Hn. move /(_ _ _ ltac:(eassumption)).
    move: HY2 => /reachable_width. move: HY1 => /reachable_width <-.
    move: Hx => /reachable_width /=. by lia.
  move=> [C' [?]]. subst. move /IH => /=. apply. rewrite app_length /length. by lia.
Qed.
  
Lemma bounded_removelast0 {n: nat} {x y: state} {A B C D: stack} {a: symbol}: 
  bounded' n -> reachable M (A++[a], x, B) (C, y, D) -> length A >= n ->
  exists (C': stack), C = C' ++ [a] /\ reachable M (A, x, B) (C', y, D).
Proof.
  move=> Hn /remove_rendundant_suffix0. case.
  - move=> [x' [B']]. move /(bounded_reachable_length0 Hn).
    rewrite app_length /length. by lia.
  - move=> [?] ? _. eexists. by eassumption.
Qed.

Lemma bounded_removelast1 {n: nat} {x y: state} {A B C D: stack} {b: symbol}: 
  bounded' n -> reachable M (A, x, B++[b]) (C, y, D) -> length B >= n ->
  exists D', D = D' ++ [b] /\ reachable M (A, x, B) (C, y, D').
Proof.
  move=> Hn /remove_rendundant_suffix1. case.
  - move=> [x' [A']]. move /(bounded_reachable_length1 Hn).
    rewrite app_length /length. by lia.
  - move=> [?] ? _. eexists. by eassumption.
Qed.

Lemma length_flat_map_le {X: Type} {f g: nat -> list X} {l1 l2: nat} : l1 <= l2 -> 
  (forall i, length (f i) <= length (g i)) ->
  length (flat_map f (seq 0 l1)) <= length (flat_map g (seq 0 l2)).
Proof.
  move: (X in (seq X)) => i.
  move=> + Hfg.
  elim: l1 l2 i.
    move=> /= *. by lia.
  move=> l1 IH l2 i ?. have -> : (l2 = S (l2 - 1)) by lia.
  move=> /=. rewrite ? app_length.
  have := (IH (l2 - 1) (S i) ltac:(lia)).
  have := (Hfg i).
  by lia.
Qed.

Lemma length_enum_stacks {l: nat} : length (enum_stacks l) = Nat.pow 2 l.
Proof.
  elim: l; first done.
  move=> l /=. rewrite app_length ? map_length. move=> ->. by lia.
Qed.

Lemma length_enum_configs {lA lB} : length (enum_configs lA lB) = length (enum_stacks lA) * length (enum_states M) * length (enum_stacks lB).
Proof.
  by rewrite /enum_configs ? prod_length.
Qed.

(* size of space is monotonous in configuration width *)
Lemma space_length {X Y: config} : 
  width X <= width Y -> length (space X) <= length (space Y).
Proof.
  rewrite /space => /=. 
  move: (width X) => l1.
  move: (width Y) => l2. clear.
  move=> H.
  have: (forall x y, x <= y -> S x <= S y) by (move=> *; lia). apply.
  apply: length_flat_map_le.
    by lia.
  move=> i. rewrite ? length_enum_configs ? length_enum_stacks.
  have: 2 ^ (l1 - i) <= 2 ^ (l2 - i).
    apply: Nat.pow_le_mono_r; by lia.
  by nia.
Qed.

(* if sizes of right stacks of narrow configurations with empty left stack are bounded by m,
  then M is bounded *)
Lemma bounded_of_bounded' {n: nat}: bounded' n -> exists (m: nat), bounded M m.
Proof.
  move=> Hn.
  pose W := (repeat false (n+n), 0, repeat false (n+n)) : config.
  exists (length (space W)). elim /(measure_ind width).
  move=> [[A x] B] IH.
  have : (length A + length B <= n+n \/ length A > n \/ length B > n) by lia.
  case.
    move=> ?. exists (space (A, x, B)). constructor.
      by move=> ? /spaceP0.
    subst W. apply: space_length => /=. rewrite repeat_length. by lia.
  case.
    move=> HAn. have : (A <> []).
      move: HAn. clear. case: A; last done.
      move=> /=. by lia.
    move /exists_last => [A' [a ?]]. subst A. rename A' into A.
    case: (IH (A, x, B)).
      rewrite /width app_length /length. by lia.
    move=> L [HL1 HL2]. exists (map (fun '(A, x, B) => (A ++ [a], x, B)) L). 
    constructor; last by rewrite map_length.
    rewrite app_length /length -/(length _) in HAn.
    move=> [[C y] D] /(bounded_removelast0 Hn). case; first by lia.
    move=> C' [-> /HL1 ?]. apply /in_map_iff. by exists (C', y, D).
  move=> HBn. have : (B <> []).
    move: HBn. clear. case: B; last done.
    move=> /=. by lia.
  move /exists_last => [B' [b ?]]. subst B. rename B' into B.
  case: (IH (A, x, B)).
    rewrite /width app_length /length. by lia.
  move=> L [HL1 HL2]. exists (map (fun '(A, x, B) => (A, x, B ++ [b])) L). 
  constructor; last by rewrite map_length.
  rewrite app_length /length -/(length _) in HBn.
  move=> [[C y] D] /(bounded_removelast1 Hn). case; first by lia.
  move=> D' [-> /HL1 ?]. apply /in_map_iff. by exists (C, y, D').
Qed.

Lemma bounded_to_bounded' {n: nat}: bounded M n -> exists (m: nat), bounded' m.
Proof.
  move=> Hn. exists (n+n). rewrite /bounded'.
  move=> [[A' z] B'] x y A B /(actual_bounded_length Hn) + /(actual_bounded_length Hn) => /=.
  by lia.
Qed.


(* right stack size bound translates to all narrow configurations *)
Lemma extend_bounded' {n: nat} {X: config} : bounded' n -> narrow X -> length (get_right X) <= n.
Proof.
  move: X => [[A x] B] Hn. elim /(measure_ind (@length bool)) : A => A IH.
  have: ({A = []} + {A <> []}).
    by do 2 (decide equality).
  case.
    move=> -> [y [A']] [Z [+ ?]]. move /Hn. apply. by eassumption.
  move /exists_last => [A' [a HA]]. subst A. rename A' into A.
  move=> [y [A']] [Z [Hx]]. have: ({A' = []} + {A' <> []}).
    by do 2 (decide equality).
  case.
    move=> ->. move: Hx => /reachable_width + /reachable_width => <- /=. by lia.
  move /exists_last => [A'' [a' HA']]. subst A'. rename A'' into A'.
  move: Z Hx => [[A'' z] B''] /copy [/remove_rendundant_suffix0]. case.
    move=> [x' [B']] /copy [/reachable_width] /= HB Hx1 Hx2 Hy.
    have [Y [HY1 HY2]] := (reachable_confluent Hx1 Hx2).
    move: Hy HY2 HY1 => /(@rt_trans config). move=> H /H{H}.
    move /Hn => H /H{H}. by lia.
  move=> [A''' [? Hx]]. subst A''. rename A''' into A''.
  move=> _ /copy [/remove_rendundant_suffix0]. case.
    move=> [x' [B']]. move=> /copy [/reachable_width] /=. 
    rewrite app_length => /= ?. move /Hn. 
    move /(_ _ _ ltac:(apply: rt_refl)) => ?.
    move: Hx => /reachable_width + /reachable_width => /=.
    rewrite ?app_length => /=. by lia.
  move=> [A''']. move=> [/(@app_inj_tail bool) [? ?]]. subst.
  move=> ? _. apply: (IH A).
    rewrite app_length /length. by lia.
  do 3 eexists. constructor; by eassumption.
Qed.

(* equivalent characterizations of boundedness *)
Theorem boundedP : (exists n, bounded M n) <-> (exists m, bounded' m).
Proof.
  constructor.
    move=> [?]. by apply /bounded_to_bounded'.
  move=> [?]. by apply /bounded_of_bounded'.
Qed.

Lemma narrow_equiv {X Y: config} : equiv X Y -> narrow X -> narrow Y.
Proof.
  move=> /equiv_sym HXY [x [A HX]]. exists x, A.
  apply: (equiv_trans); by eassumption.
Qed.

End DSSM.
