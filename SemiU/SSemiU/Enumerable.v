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

(* Enumerable X allows injection into nat *)
Class Enumerable (X: Type) :=
  {
    to_nat : X -> nat;
    of_nat : nat -> X;
    enumP {x: X} : of_nat (to_nat x) = x
  }.

Module Nat2Enum.

(* 0 + 1 + ... + n *)
Definition big_sum (n : nat) : nat := nat_rec _ 0 (fun i m => m + (S i)) n.

(* bijection from nat * nat to nat *)
Definition nat2_to_nat '(x, y) : nat := (big_sum (x + y)) + y.

Definition next_nat2 '(x, y) : nat * nat := if x is S x then (x, S y) else (S y, 0).

(* bijection from nat to nat * nat *)
Definition nat_to_nat2 (n : nat) : nat * nat := Nat.iter n next_nat2 (0, 0).

Lemma nat_nat2_cancel : cancel nat2_to_nat nat_to_nat2.
Proof.
  move=> a. move Hn: (nat2_to_nat a) => n.
  elim: n a Hn.
    case; case=> [|?]; case=> [|?]=> /=; by [|lia].
  move=> n IH [x y]. case: y => [|y] /=. case: x => [|x] //=.
  all: rewrite ? (Nat.add_0_r, Nat.add_succ_r); case.
    rewrite -/(nat2_to_nat (0, x)). by move /IH ->.
  rewrite -/(nat2_to_nat (S x, y)). by move /IH ->.
Qed.

Lemma nat2_nat_cancel : cancel nat_to_nat2 nat2_to_nat.
Proof.
  elim=> //=.
  move=> n. move: (nat_to_nat2 n) => [+ ?].
  case=> /= => [|?]; rewrite ? (Nat.add_0_r, Nat.add_succ_r) => /=; by lia.
Qed.

Lemma nat_to_nat2_non_increasing {n} : fst (nat_to_nat2 n) + snd (nat_to_nat2 n) < S n.
Proof.
  elim: n=> [|n] //=.
  move: (nat_to_nat2 n) => [x y].
  case: y => [|y]; case: x => [|x] /=; by lia.
Qed.

End Nat2Enum.

Inductive tree : Set :=
  | leaf : tree
  | node : nat -> tree -> tree -> tree.

Module TreeEnum.

Import Nat2Enum.

Fixpoint tree_to_nat (t: tree) : nat :=
  match t with
  | leaf => 0
  | node n t u => S (nat2_to_nat (n, nat2_to_nat ((tree_to_nat t), (tree_to_nat u))))
  end.

Lemma nat_to_tree_fst_lt {n} : (fst (nat_to_nat2 (snd (nat_to_nat2 n)))) < S n.
Proof. 
  have ? := @nat_to_nat2_non_increasing n.
  have ? := @nat_to_nat2_non_increasing (snd (nat_to_nat2 n)).
  by lia.
Qed.

Lemma nat_to_tree_snd_lt {n} : (snd (nat_to_nat2 (snd (nat_to_nat2 n)))) < S n.
Proof. 
  have ? := @nat_to_nat2_non_increasing n.
  have ? := @nat_to_nat2_non_increasing (snd (nat_to_nat2 n)).
  by lia.
Qed.
  
Definition nat_to_tree : nat -> tree.
Proof.
  apply: (Fix lt_wf _). case.
    exact (fun _ => leaf).
  move=> n f.
  pose m := snd (nat_to_nat2 n).
  refine (node (fst (nat_to_nat2 n)) (f (fst (nat_to_nat2 m)) _) (f (snd (nat_to_nat2 m)) _)).
    exact nat_to_tree_fst_lt.
  exact nat_to_tree_snd_lt.
Defined.

Lemma nat_to_tree_S_nP {n} : 
  nat_to_tree (S n) = 
    node (fst (nat_to_nat2 n)) 
      (nat_to_tree (fst (nat_to_nat2 (snd (nat_to_nat2 n)))))
      (nat_to_tree (snd (nat_to_nat2 (snd (nat_to_nat2 n))))).
Proof.
  rewrite /nat_to_tree Fix_eq=> //. elim=> // *. by f_equal.
Qed.
    
Lemma nat_tree_cancel {t} : nat_to_tree (tree_to_nat t) = t.
Proof.
  elim: t=> // *.
  rewrite /tree_to_nat nat_to_tree_S_nP nat_nat2_cancel.
  rewrite -/tree_to_nat /fst /snd -/(fst _) -/(snd _) nat_nat2_cancel. 
  by f_equal.
Qed.
    
Lemma tree_nat_cancel {n} : tree_to_nat (nat_to_tree n) = n.
Proof.
  elim /lt_wf_ind: n. case=> //.
  move=> n IH. rewrite nat_to_tree_S_nP /tree_to_nat -/tree_to_nat ? IH.
    1,2: have ? := @nat_to_nat2_non_increasing n.
    1,2: have ? := @nat_to_nat2_non_increasing (snd (nat_to_nat2 n)).
    1,2: by lia.
  rewrite - surjective_pairing nat2_nat_cancel.
  by rewrite - surjective_pairing nat2_nat_cancel.
Qed.

End TreeEnum.

Instance nat_Enumerable : Enumerable nat.
Proof.
  by exists id id.
Qed.

Instance bool_Enumerable : Enumerable bool.
Proof.
  exists (fun b => if b then 1 else 0) (fun n => if n is 0 then false else true).
  by case.
Qed.

Instance nat2_Enumerable : Enumerable (nat * nat).
Proof.
  exists Nat2Enum.nat2_to_nat Nat2Enum.nat_to_nat2.
  by apply: Nat2Enum.nat_nat2_cancel.
Qed.

Instance tree_Enumerable : Enumerable tree.
Proof.
  exists TreeEnum.tree_to_nat TreeEnum.nat_to_tree.
  move=> ?. by apply: TreeEnum.nat_tree_cancel.
Qed.

Lemma enumarableI {X Y: Type} {enum: Enumerable X} (to_X: Y -> X) (of_X: X -> Y) : 
  (forall (y: Y), of_X (to_X y) = y) -> Enumerable Y.
Proof.
  move=> cancel. exists (fun y => to_nat (to_X y)) (fun x => of_X (of_nat x)).
  move=> y. by rewrite enumP cancel.
Qed.

Module ListEnum.

Fixpoint list_to_tree {X: Type} {enumX: Enumerable X} (L: list X) : tree :=
  match L with
  | [] => leaf
  | x :: L => node (to_nat x) (list_to_tree L) leaf
  end.

Fixpoint list_of_tree {X: Type} {enumX: Enumerable X} (t: tree) : list X :=
  match t with
  | node n t leaf => (of_nat n) :: (list_of_tree t)
  | _ => []
  end.

End ListEnum.

Instance list_Enumerable {X: Type} {enumX: Enumerable X} : Enumerable (list X).
Proof.
  apply: (enumarableI ListEnum.list_to_tree ListEnum.list_of_tree).
  elim.
    done.
  move=> x L IH /=. rewrite enumP. by f_equal.
Qed.

Instance prod_Enumerable {X Y: Type} {enumX: Enumerable X} {enumY: Enumerable Y} : Enumerable (X * Y).
Proof.
  exists 
    (fun '(x, y) => to_nat (to_nat x, to_nat y))
    (fun n => 
      match of_nat n with 
      | (n1, n2) => (of_nat n1, of_nat n2)
      end).
  move=> [x y]. by rewrite ?enumP.
Qed.

Opaque to_nat of_nat.
