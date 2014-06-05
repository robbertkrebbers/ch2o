(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file implements finite set as unordered lists without duplicates
removed. This implementation forms a monad. *)
Require Export base decidable collections list.

Record listset A := Listset { listset_car: list A }.
Arguments listset_car {_} _.
Arguments Listset {_} _.

Section listset.
Context {A : Type}.

Instance listset_elem_of: ElemOf A (listset A) := λ x l, x ∈ listset_car l.
Instance listset_empty: Empty (listset A) := Listset [].
Instance listset_singleton: Singleton A (listset A) := λ x, Listset [x].
Instance listset_union: Union (listset A) := λ l k,
  let (l') := l in let (k') := k in Listset (l' ++ k').

Global Instance: SimpleCollection A (listset A).
Proof.
  split.
  * by apply not_elem_of_nil.
  * by apply elem_of_list_singleton.
  * intros [?] [?]. apply elem_of_app.
Qed.

Context `{∀ x y : A, Decision (x = y)}.

Instance listset_intersection: Intersection (listset A) := λ l k,
  let (l') := l in let (k') := k in Listset (list_intersection l' k').
Instance listset_difference: Difference (listset A) := λ l k,
  let (l') := l in let (k') := k in Listset (list_difference l' k').
Instance listset_intersection_with: IntersectionWith A (listset A) := λ f l k,
  let (l') := l in let (k') := k in Listset (list_intersection_with f l' k').
Instance listset_filter: Filter A (listset A) := λ P _ l,
  let (l') := l in Listset (filter P l').

Instance: Collection A (listset A).
Proof.
  split.
  * apply _.
  * intros [?] [?]. apply elem_of_list_intersection.
  * intros [?] [?]. apply elem_of_list_difference.
Qed.
Instance listset_elems: Elements A (listset A) := remove_dups ∘ listset_car.
Global Instance: FinCollection A (listset A).
Proof.
  split.
  * apply _.
  * intros. apply elem_of_remove_dups.
  * intros. apply NoDup_remove_dups.
Qed.
Global Instance: CollectionOps A (listset A).
Proof.
  split.
  * apply _.
  * intros ? [?] [?]. apply elem_of_list_intersection_with.
  * intros [?] ??. apply elem_of_list_filter.
Qed.
End listset.

(** These instances are declared using [Hint Extern] to avoid too
eager type class search. *)
Hint Extern 1 (ElemOf _ (listset _)) =>
  eapply @listset_elem_of : typeclass_instances.
Hint Extern 1 (Empty (listset _)) =>
  eapply @listset_empty : typeclass_instances.
Hint Extern 1 (Singleton _ (listset _)) =>
  eapply @listset_singleton : typeclass_instances.
Hint Extern 1 (Union (listset _)) =>
  eapply @listset_union : typeclass_instances.
Hint Extern 1 (Intersection (listset _)) =>
  eapply @listset_intersection : typeclass_instances.
Hint Extern 1 (IntersectionWith _ (listset _)) =>
  eapply @listset_intersection_with : typeclass_instances.
Hint Extern 1 (Difference (listset _)) =>
  eapply @listset_difference : typeclass_instances.
Hint Extern 1 (Elements _ (listset _)) =>
  eapply @listset_elems : typeclass_instances.
Hint Extern 1 (Filter _ (listset _)) =>
  eapply @listset_filter : typeclass_instances.

Instance listset_ret: MRet listset := λ A x, {[ x ]}.
Instance listset_fmap: FMap listset := λ A B f l,
  let (l') := l in Listset (f <$> l').
Instance listset_bind: MBind listset := λ A B f l,
  let (l') := l in Listset (mbind (listset_car ∘ f) l').
Instance listset_join: MJoin listset := λ A, mbind id.

Instance: CollectionMonad listset.
Proof.
  split.
  * intros. apply _.
  * intros ??? [?] ?. apply elem_of_list_bind.
  * intros. apply elem_of_list_ret.
  * intros ??? [?]. apply elem_of_list_fmap.
  * intros ? [?] ?. unfold mjoin, listset_join, elem_of, listset_elem_of.
    simpl. by rewrite elem_of_list_bind.
Qed.
