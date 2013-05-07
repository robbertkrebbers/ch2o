(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file implements finite as unordered lists without duplicates.
Although this implementation is slow, it is very useful as decidable equality
is the only constraint on the carrier set. *)
Require Export base decidable collections list.

Record listset_nodup A := ListsetNoDup {
  listset_nodup_car : list A;
  listset_nodup_prf : NoDup listset_nodup_car
}.
Arguments ListsetNoDup {_} _ _.
Arguments listset_nodup_car {_} _.
Arguments listset_nodup_prf {_} _.

Section list_collection.
Context {A : Type} `{∀ x y : A, Decision (x = y)}.

Notation C := (listset_nodup A).
Notation LS := ListsetNoDup.

Instance listset_nodup_elem_of: ElemOf A C := λ x l, x ∈ listset_nodup_car l.
Instance listset_nodup_empty: Empty C := LS [] (@NoDup_nil_2 _).
Instance listset_nodup_singleton: Singleton A C := λ x,
  LS [x] (NoDup_singleton x).
Instance listset_nodup_difference: Difference C := λ l k,
  LS _ (list_difference_nodup _ (listset_nodup_car k) (listset_nodup_prf l)).

Definition listset_nodup_union_raw (l k : list A) : list A :=
  list_difference l k ++ k.
Lemma elem_of_listset_nodup_union_raw l k x :
  x ∈ listset_nodup_union_raw l k ↔ x ∈ l ∨ x ∈ k.
Proof.
  unfold listset_nodup_union_raw.
  rewrite elem_of_app, elem_of_list_difference.
  intuition. case (decide (x ∈ k)); intuition.
Qed.
Lemma listset_nodup_union_raw_nodup l k :
  NoDup l → NoDup k → NoDup (listset_nodup_union_raw l k).
Proof.
  intros. apply NoDup_app. repeat split.
  * by apply list_difference_nodup.
  * intro. rewrite elem_of_list_difference. intuition.
  * done.
Qed.
Instance listset_nodup_union: Union C := λ l k,
  LS _ (listset_nodup_union_raw_nodup _ _
     (listset_nodup_prf l) (listset_nodup_prf k)).
Instance listset_nodup_intersection: Intersection C := λ l k,
  LS _ (list_intersection_nodup _
     (listset_nodup_car k) (listset_nodup_prf l)).
Instance listset_nodup_intersection_with:
    IntersectionWith A C := λ f l k,
  LS (remove_dups
      (list_intersection_with f (listset_nodup_car l) (listset_nodup_car k)))
    (remove_dups_nodup _).
Instance listset_nodup_filter: Filter A C :=
  λ P _ l, LS _ (filter_nodup P _ (listset_nodup_prf l)).

Instance: Collection A C.
Proof.
  split; [split | | ].
  * by apply not_elem_of_nil.
  * by apply elem_of_list_singleton.
  * intros. apply elem_of_listset_nodup_union_raw.
  * intros. apply elem_of_list_intersection.
  * intros. apply elem_of_list_difference.
Qed.

Global Instance listset_nodup_elems: Elements A C := listset_nodup_car.

Global Instance: FinCollection A C.
Proof.
  split.
  * apply _.
  * done.
  * by intros [??].
Qed.

Global Instance: CollectionOps A C.
Proof.
  split.
  * apply _.
  * intros. unfold intersection_with, listset_nodup_intersection_with,
      elem_of, listset_nodup_elem_of. simpl.
    rewrite elem_of_remove_dups. by apply elem_of_list_intersection_with.
  * intros. apply elem_of_list_filter.
Qed.
End list_collection.

Hint Extern 1 (ElemOf _ (listset_nodup _)) =>
  eapply @listset_nodup_elem_of : typeclass_instances.
Hint Extern 1 (Empty (listset_nodup _)) =>
  eapply @listset_nodup_empty : typeclass_instances.
Hint Extern 1 (Singleton _ (listset_nodup _)) =>
  eapply @listset_nodup_singleton : typeclass_instances.
Hint Extern 1 (Union (listset_nodup _)) =>
  eapply @listset_nodup_union : typeclass_instances.
Hint Extern 1 (Intersection (listset_nodup _)) =>
  eapply @listset_nodup_intersection : typeclass_instances.
Hint Extern 1 (Difference (listset_nodup _)) =>
  eapply @listset_nodup_difference : typeclass_instances.
Hint Extern 1 (Elements _ (listset_nodup _)) =>
  eapply @listset_nodup_elems : typeclass_instances.
Hint Extern 1 (Filter _ (listset_nodup _)) =>
  eapply @listset_nodup_filter : typeclass_instances.
