(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file implements finite set using hash maps. Hash sets are represented
using radix-2 search trees. Each hash bucket is thus indexed using an binary
integer of type [Z], and contains an unordered list without duplicates. *)
Require Export fin_maps.
Require Import zmap.

Record hashset {A} (hash : A → Z) := Hashset {
  hashset_car : Zmap (list A);
  hashset_prf :
    map_Forall (λ n l, Forall (λ x, hash x = n) l ∧ NoDup l) hashset_car
}.
Arguments Hashset {_ _} _ _.
Arguments hashset_car {_ _} _.

Section hashset.
Context {A : Type} {hash : A → Z} `{∀ x y : A, Decision (x = y)}.

Instance hashset_elem_of: ElemOf A (hashset hash) := λ x m, ∃ l,
  hashset_car m !! hash x = Some l ∧ x ∈ l.

Program Instance hashset_empty: Empty (hashset hash) := Hashset ∅ _.
Next Obligation. by intros n X; simpl_map. Qed.
Program Instance hashset_singleton: Singleton A (hashset hash) := λ x,
  Hashset {[ hash x, [x] ]} _.
Next Obligation.
  intros n l. rewrite lookup_singleton_Some. intros [<- <-].
  rewrite Forall_singleton; auto using NoDup_singleton.
Qed.
Program Instance hashset_union: Union (hashset hash) := λ m1 m2,
  let (m1,Hm1) := m1 in let (m2,Hm2) := m2 in
  Hashset (union_with (λ l k, Some (list_union l k)) m1 m2) _. 
Next Obligation.
  intros n l'. rewrite lookup_union_with_Some.
  intros [[??]|[[??]|(l&k&?&?&?)]]; simplify_equality'; auto.
  split; [apply Forall_list_union|apply NoDup_list_union];
    first [by eapply Hm1; eauto | by eapply Hm2; eauto].
Qed.
Program Instance hashset_intersection: Intersection (hashset hash) := λ m1 m2,
  let (m1,Hm1) := m1 in let (m2,Hm2) := m2 in
  Hashset (intersection_with (λ l k,
    let l' := list_intersection l k in guard (l' ≠ []); Some l') m1 m2) _.
Next Obligation.
  intros n l'. rewrite lookup_intersection_with_Some.
  intros (?&?&?&?&?); simplify_option_equality.
  split; [apply Forall_list_intersection|apply NoDup_list_intersection];
    first [by eapply Hm1; eauto | by eapply Hm2; eauto].
Qed.
Program Instance hashset_difference: Difference (hashset hash) := λ m1 m2,
  let (m1,Hm1) := m1 in let (m2,Hm2) := m2 in
  Hashset (difference_with (λ l k,
    let l' := list_difference l k in guard (l' ≠ []); Some l') m1 m2) _.
Next Obligation.
  intros n l'. rewrite lookup_difference_with_Some.
  intros [[??]|(?&?&?&?&?)]; simplify_option_equality; auto.
  split; [apply Forall_list_difference|apply NoDup_list_difference];
    first [by eapply Hm1; eauto | by eapply Hm2; eauto].
Qed.
Instance hashset_elems: Elements A (hashset hash) := λ m,
  map_to_list (hashset_car m) ≫= snd.

Global Instance: FinCollection A (hashset hash).
Proof.
  split; [split; [split| |]| |].
  * intros ? (?&?&?); simplify_map_equality'.
  * unfold elem_of, hashset_elem_of, singleton, hashset_singleton; simpl.
    intros x y. setoid_rewrite lookup_singleton_Some. split.
    { by intros (?&[? <-]&?); decompose_elem_of_list. }
    intros ->; eexists [y]. by rewrite elem_of_list_singleton.
  * unfold elem_of, hashset_elem_of, union, hashset_union.
    intros [m1 Hm1] [m2 Hm2] x; simpl; setoid_rewrite lookup_union_with_Some.
    split.
    { intros (?&[[]|[[]|(l&k&?&?&?)]]&Hx); simplify_equality'; eauto.
      rewrite elem_of_list_union in Hx; destruct Hx; eauto. }
    intros [(l&?&?)|(k&?&?)].
    + destruct (m2 !! hash x) as [k|]; eauto.
      exists (list_union l k). rewrite elem_of_list_union. naive_solver.
    + destruct (m1 !! hash x) as [l|]; eauto 6.
      exists (list_union l k). rewrite elem_of_list_union. naive_solver.
  * unfold elem_of, hashset_elem_of, intersection, hashset_intersection.
    intros [m1 ?] [m2 ?] x; simpl.
    setoid_rewrite lookup_intersection_with_Some. split.
    { intros (?&(l&k&?&?&?)&Hx); simplify_option_equality.
      rewrite elem_of_list_intersection in Hx; naive_solver. }
    intros [(l&?&?) (k&?&?)]. assert (x ∈ list_intersection l k)
      by (by rewrite elem_of_list_intersection).
    exists (list_intersection l k); split; [exists l k|]; split_ands; auto.
    by rewrite option_guard_True by eauto using elem_of_not_nil.
  * unfold elem_of, hashset_elem_of, intersection, hashset_intersection.
    intros [m1 ?] [m2 ?] x; simpl.
    setoid_rewrite lookup_difference_with_Some. split.
    { intros (l'&[[??]|(l&k&?&?&?)]&Hx); simplify_option_equality;
        rewrite ?elem_of_list_difference in Hx; naive_solver. }
    intros [(l&?&?) Hm2]; destruct (m2 !! hash x) as [k|] eqn:?; eauto.
    destruct (decide (x ∈ k)); [destruct Hm2; eauto|].
    assert (x ∈ list_difference l k) by (by rewrite elem_of_list_difference).
    exists (list_difference l k); split; [right; exists l k|]; split_ands; auto.
    by rewrite option_guard_True by eauto using elem_of_not_nil.
  * unfold elem_of at 2, hashset_elem_of, elements, hashset_elems.
    intros [m Hm] x; simpl. setoid_rewrite elem_of_list_bind. split.
    { intros ([n l]&Hx&Hn); simpl in *; rewrite elem_of_map_to_list in Hn.
      cut (hash x = n); [intros <-; eauto|].
      eapply (Forall_forall (λ x, hash x = n) l); eauto. eapply Hm; eauto. }
    intros (l&?&?). exists (hash x, l); simpl. by rewrite elem_of_map_to_list.
  * unfold elements, hashset_elems. intros [m Hm]; simpl.
    rewrite map_Forall_to_list in Hm. generalize (NoDup_fst_map_to_list m).
    induction Hm as [|[n l] m' [??]];
      simpl; inversion_clear 1 as [|?? Hn]; [constructor|].
    apply NoDup_app; split_ands; eauto.
    setoid_rewrite elem_of_list_bind; intros x ? ([n' l']&?&?); simpl in *.
    assert (hash x = n ∧ hash x = n') as [??]; subst.
    { split; [eapply (Forall_forall (λ x, hash x = n) l); eauto|].
      eapply (Forall_forall (λ x, hash x = n') l'); eauto.
      rewrite Forall_forall in Hm. eapply (Hm (_,_)); eauto. }
    destruct Hn; rewrite elem_of_list_fmap; exists (hash x, l'); eauto.
Qed.
End hashset.

(** These instances are declared using [Hint Extern] to avoid too
eager type class search. *)
Hint Extern 1 (ElemOf _ (hashset _)) =>
  eapply @hashset_elem_of : typeclass_instances.
Hint Extern 1 (Empty (hashset _)) =>
  eapply @hashset_empty : typeclass_instances.
Hint Extern 1 (Singleton _ (hashset _)) =>
  eapply @hashset_singleton : typeclass_instances.
Hint Extern 1 (Union (hashset _)) =>
  eapply @hashset_union : typeclass_instances.
Hint Extern 1 (Intersection (hashset _)) =>
  eapply @hashset_intersection : typeclass_instances.
Hint Extern 1 (Difference (hashset _)) =>
  eapply @hashset_difference : typeclass_instances.
Hint Extern 1 (Elements _ (hashset _)) =>
  eapply @hashset_elems : typeclass_instances.
