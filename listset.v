(* Copyright (c) 2012, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file implements finite as unordered lists without duplicates.
Although this implementation is slow, it is very useful as decidable equality
is the only constraint on the carrier set. *)
Require Export base decidable collections list.

Definition listset A := sig (@NoDup A).

Section list_collection.
Context {A : Type} `{∀ x y : A, Decision (x = y)}.

Global Instance listset_elem_of: ElemOf A (listset A) := λ x l, In x (`l).
Global Instance listset_empty: Empty (listset A) := []↾@NoDup_nil _.
Global Instance listset_singleton: Singleton A (listset A) := λ x,
  [x]↾NoDup_singleton x.

Fixpoint listset_difference_raw (l k : list A) :=
  match l with
  | [] => []
  | x :: l =>
    if decide_rel In x k
    then listset_difference_raw l k
    else x :: listset_difference_raw l k
  end.
Lemma listset_difference_raw_in l k x :
  In x (listset_difference_raw l k) ↔ In x l ∧ ¬In x k.
Proof.
  split; induction l; simpl; try case_decide; simpl; intuition congruence.
Qed.
Lemma listset_difference_raw_nodup l k :
  NoDup l → NoDup (listset_difference_raw l k).
Proof.
  induction 1; simpl; try case_decide.
  * constructor.
  * done.
  * constructor. rewrite listset_difference_raw_in; intuition. done.
Qed.
Global Instance listset_difference: Difference (listset A) := λ l k,
  listset_difference_raw (`l) (`k)↾
    listset_difference_raw_nodup (`l) (`k) (proj2_sig l).

Definition listset_union_raw (l k : list A) := listset_difference_raw l k ++ k.
Lemma listset_union_raw_in l k x :
  In x (listset_union_raw l k) ↔ In x l ∨ In x k.
Proof.
  unfold listset_union_raw. rewrite in_app_iff, listset_difference_raw_in.
  intuition. case (decide (In x k)); intuition.
Qed.
Lemma listset_union_raw_nodup l k :
  NoDup l → NoDup k → NoDup (listset_union_raw l k).
Proof.
  intros. apply NoDup_app.
  * by apply listset_difference_raw_nodup.
  * done.
  * intro. rewrite listset_difference_raw_in. intuition.
Qed.
Global Instance listset_union: Union (listset A) := λ l k,
  listset_union_raw (`l) (`k)↾
    listset_union_raw_nodup (`l) (`k) (proj2_sig l) (proj2_sig k).

Fixpoint listset_intersection_raw (l k : list A) :=
  match l with
  | [] => []
  | x :: l =>
    if decide_rel In x k
    then x :: listset_intersection_raw l k
    else listset_intersection_raw l k
  end.
Lemma listset_intersection_raw_in l k x :
  In x (listset_intersection_raw l k) ↔ In x l ∧ In x k.
Proof.
  split; induction l; simpl; try case_decide; simpl; intuition congruence.
Qed.
Lemma listset_intersection_raw_nodup l k :
  NoDup l → NoDup (listset_intersection_raw l k).
Proof.
  induction 1; simpl; try case_decide.
  * constructor.
  * constructor. rewrite listset_intersection_raw_in; intuition. done.
  * done.
Qed.
Global Instance listset_intersection: Intersection (listset A) := λ l k,
  listset_intersection_raw (`l) (`k)↾
    listset_intersection_raw_nodup (`l) (`k) (proj2_sig l).

Definition listset_add_raw x (l : list A) : list A :=
  if decide_rel In x l then l else x :: l.
Lemma listset_add_raw_in x l y : In y (listset_add_raw x l) ↔ y = x ∨ In y l.
Proof. unfold listset_add_raw. case_decide; firstorder congruence. Qed.
Lemma listset_add_raw_nodup x l : NoDup l → NoDup (listset_add_raw x l).
Proof.
  unfold listset_add_raw. case_decide; try constructor; firstorder.
Qed.

Fixpoint listset_map_raw (f : A → A) (l : list A) :=
  match l with
  | [] => []
  | x :: l => listset_add_raw (f x) (listset_map_raw f l)
  end.
Lemma listset_map_raw_nodup f l : NoDup (listset_map_raw f l).
Proof. induction l; simpl. constructor. by apply listset_add_raw_nodup. Qed.
Lemma listset_map_raw_in f l x :
  In x (listset_map_raw f l) ↔ ∃ y, x = f y ∧ In y l.
Proof.
  split.
  * induction l; simpl; [done |].
    rewrite listset_add_raw_in. firstorder.
  * intros [?[??]]. subst. induction l; simpl in *; [done |].
    rewrite listset_add_raw_in. firstorder congruence.
Qed.
Global Instance listset_map: Map A (listset A) := λ f l,
  listset_map_raw f (`l)↾listset_map_raw_nodup f (`l).

Global Instance: Collection A (listset A).
Proof.
  split.
  * intros ? [].
  * compute. intuition.
  * intros. apply listset_union_raw_in.
  * intros. apply listset_intersection_raw_in.
  * intros. apply listset_difference_raw_in.
  * intros. apply listset_map_raw_in.
Qed.

Global Instance listset_elems: Elements A (listset A) := @proj1_sig _ _.

Global Instance: FinCollection A (listset A).
Proof. split. apply _. done. by intros [??]. Qed.
End list_collection.
