(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file implements finite as unordered lists without duplicates.
Although this implementation is slow, it is very useful as decidable equality
is the only constraint on the carrier set. *)
Require Export base decidable collections list.

Record listset_nodup A := ListsetNoDup {
  listset_nodup_car : list A; listset_nodup_prf : NoDup listset_nodup_car
}.
Arguments ListsetNoDup {_} _ _.
Arguments listset_nodup_car {_} _.
Arguments listset_nodup_prf {_} _.

Section list_collection.
Context {A : Type} `{∀ x y : A, Decision (x = y)}.
Notation C := (listset_nodup A).

Instance listset_nodup_elem_of: ElemOf A C := λ x l, x ∈ listset_nodup_car l.
Instance listset_nodup_empty: Empty C := ListsetNoDup [] (@NoDup_nil_2 _).
Instance listset_nodup_singleton: Singleton A C := λ x,
  ListsetNoDup [x] (NoDup_singleton x).
Instance listset_nodup_union: Union C := λ l k,
  let (l',Hl) := l in let (k',Hk) := k
  in ListsetNoDup _ (NoDup_list_union _ _ Hl Hk).
Instance listset_nodup_intersection: Intersection C := λ l k,
  let (l',Hl) := l in let (k',Hk) := k
  in ListsetNoDup _ (NoDup_list_intersection _ k' Hl).
Instance listset_nodup_difference: Difference C := λ l k,
  let (l',Hl) := l in let (k',Hk) := k
  in ListsetNoDup _ (NoDup_list_difference _ k' Hl).
Instance listset_nodup_intersection_with: IntersectionWith A C := λ f l k,
  let (l',Hl) := l in let (k',Hk) := k
  in ListsetNoDup
    (remove_dups (list_intersection_with f l' k')) (NoDup_remove_dups _).
Instance listset_nodup_filter: Filter A C := λ P _ l,
  let (l',Hl) := l in ListsetNoDup _ (NoDup_filter P _ Hl).

Instance: Collection A C.
Proof.
  split; [split | | ].
  * by apply not_elem_of_nil.
  * by apply elem_of_list_singleton.
  * intros [??] [??] ?. apply elem_of_list_union.
  * intros [??] [??] ?. apply elem_of_list_intersection.
  * intros [??] [??] ?. apply elem_of_list_difference.
Qed.

Global Instance listset_nodup_elems: Elements A C := listset_nodup_car.
Global Instance: FinCollection A C.
Proof. split. apply _. done. by intros [??]. Qed.
Global Instance: CollectionOps A C.
Proof.
  split.
  * apply _.
  * intros ? [??] [??] ?. unfold intersection_with, elem_of,
      listset_nodup_intersection_with, listset_nodup_elem_of; simpl.
    rewrite elem_of_remove_dups. by apply elem_of_list_intersection_with.
  * intros [??] ???. apply elem_of_list_filter.
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
