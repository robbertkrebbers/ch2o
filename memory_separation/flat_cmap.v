(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
From stdpp Require Import fin_maps fin_map_dom.
Require Export separation memory_basics.

Record flat_cmap (A : Type) : Type :=
  FlatCMap { flat_cmap_car : indexmap (list A) }.
Arguments FlatCMap {_} _.
Arguments flat_cmap_car {_} _.
Add Printing Constructor flat_cmap.
#[global] Instance: `{Inj (=) (=) (@FlatCMap A)}.
Proof. by injection 1. Qed.

#[refine, global] Instance flat_cmap_ops `{SeparationOps A} : SeparationOps (flat_cmap A) := {
  sep_empty := FlatCMap ∅;
  sep_union m1 m2 :=
    let (m1) := m1 in let (m2) := m2 in
    FlatCMap (union_with (λ xs1 xs2, Some (xs1 ∪* xs2)) m1 m2);
  sep_difference m1 m2 :=
    let (m1) := m1 in let (m2) := m2 in
    FlatCMap (difference_with (λ xs1 xs2,
      let xs' := xs1 ∖* xs2 in guard (¬Forall (∅ =.) xs'); Some xs'
    ) m1 m2);
  sep_half m := let (m) := m in FlatCMap (½* <$> m);
  sep_valid m :=
    let (m) := m in
    map_Forall (λ _ xs, Forall sep_valid xs ∧ ¬Forall (∅ =.) xs) m;
  sep_disjoint m1 m2 :=
    let (m1) := m1 in let (m2) := m2 in map_relation
      (λ xs1 xs2, xs1 ##* xs2 ∧ ¬Forall (∅ =.) xs1 ∧ ¬Forall (∅ =.) xs2) 
      (λ xs1, Forall sep_valid xs1 ∧ ¬Forall (∅ =.) xs1)
      (λ xs2, Forall sep_valid xs2 ∧ ¬Forall (∅ =.) xs2) m1 m2;
  sep_splittable m :=
    let (m) := m in
    map_Forall (λ _ xs,
      Forall sep_valid xs ∧ ¬Forall (∅ =.) xs ∧ Forall sep_splittable xs) m;
  sep_subseteq m1 m2 :=
    let (m1) := m1 in let (m2) := m2 in map_relation
      (λ xs1 w2, xs1 ⊆* w2 ∧ ¬Forall (∅ =.) xs1)
      (λ xs1, False)
      (λ xs2, Forall sep_valid xs2 ∧ ¬Forall (∅ =.) xs2) m1 m2;
  sep_unmapped m := flat_cmap_car m = ∅;
  sep_unshared m := False
}.
Proof.
  * intros []; apply _.
  * intros [] []; eapply map_relation_dec; apply _.
  * intros [] []; eapply map_relation_dec; apply _.
  * solve_decision.
  * intros []; apply _.
Defined.

#[global] Instance flat_cmap_sep `{Separation A} : Separation (flat_cmap A).
Proof.
  split.
  * destruct (sep_inhabited A) as (x&?&?).
    eexists (FlatCMap {[ fresh (C := indexset) ∅ := [x] ]}).
    split; [|by intro]. intros o w ?; simplify_map_eq. split.
    + by rewrite Forall_singleton.
    + inversion_clear 1; decompose_Forall_hyps; eauto using sep_unmapped_empty.
  * sep_unfold; intros [m1] [m2] Hm o w; specialize (Hm o); simpl in *.
    intros Hx. rewrite Hx in Hm. simpl in *.
    destruct (m2 !! o); intuition eauto using seps_disjoint_valid_l.
  * sep_unfold; intros [m1] [m2] Hm o w; specialize (Hm o); simpl in *.
    rewrite lookup_union_with. intros. destruct (m1 !! o), (m2 !! o);
    simplify_equality'; intuition eauto using seps_union_valid, seps_positive_l.
  * sep_unfold. intros [m] Hm o; specialize (Hm o); simplify_map_eq.
    destruct (m !! o); eauto.
  * sep_unfold; intros [m] ?; f_equal'. by rewrite (left_id_L ∅ _).
  * sep_unfold. intros [m1] [m2] Hm o; specialize (Hm o); 
    unfold option_relation in *.
    destruct (m1 !! o), (m2 !! o); intuition.
  * sep_unfold; intros [m1] [m2] Hm; f_equal'. 
    apply stdpp.fin_maps.union_with_comm. 
    intros o w1 w2 ??; specialize (Hm o); 
    unfold option_relation in Hm; simplify_option_eq.
    f_equal; intuition auto using seps_commutative.
  * sep_unfold; intros [m1] [m2] [m3] Hm Hm' o; specialize (Hm o);
      specialize (Hm' o); simpl in *; rewrite lookup_union_with in Hm'.
    destruct (m1 !! o) eqn:?, (m2 !! o), (m3 !! o); simplify_equality';
      intuition eauto using seps_disjoint_valid_l, seps_disjoint_ll.
  * sep_unfold; intros [m1] [m2] [m3] Hm Hm' o; specialize (Hm o);
      specialize (Hm' o); simpl in *; rewrite lookup_union_with in Hm' |- *.
    destruct (m1 !! o) eqn:?, (m2 !! o), (m3 !! o); simplify_equality';
      intuition eauto using seps_disjoint_valid_l, seps_disjoint_move_l,
      seps_union_valid, seps_positive_l, seps_disjoint_lr.
  * sep_unfold; intros [m1] [m2] [m3] Hm Hm'; f_equal'.
    apply map_eq; intros o; specialize (Hm o); specialize (Hm' o); simpl in *;
      rewrite !lookup_union_with; rewrite lookup_union_with in Hm'.
    destruct (m1 !! o) eqn:?, (m2 !! o), (m3 !! o); simplify_equality'; eauto.
    f_equal; intuition auto using seps_associative.
  * sep_unfold; intros [m1] [m2] _; rewrite !(inj_iff FlatCMap).
    intros Hm. apply map_eq; intros o. rewrite lookup_empty.
    apply (f_equal (.!! o)) in Hm; rewrite lookup_union_with, lookup_empty in Hm.
    by destruct (m1 !! o), (m2 !! o); simplify_equality'.
  * sep_unfold; intros [m1] [m2] [m3] Hm Hm'; rewrite !(inj_iff FlatCMap);
      intros Hm''; apply map_eq; intros o.
    specialize (Hm o); specialize (Hm' o);
      apply (f_equal (.!! o)) in Hm''; rewrite !lookup_union_with in Hm''.
    destruct (m1 !! o) eqn:?, (m2 !! o), (m3 !! o); simplify_equality';
      f_equal; naive_solver eauto using seps_cancel_l,
      seps_cancel_empty_l, seps_cancel_empty_r.
  * sep_unfold; intros [m1] [m2] Hm o; specialize (Hm o).
    rewrite lookup_union_with. destruct (m1 !! o), (m2 !! o); simpl;
      unfold option_relation in *;
      intuition auto using seps_union_subseteq_l, seps_reflexive.
  * sep_unfold; intros [m1] [m2] Hm o; specialize (Hm o).
    rewrite lookup_difference_with; destruct (m1 !! o), (m2 !! o);
      simplify_option_eq;
      intuition eauto using seps_disjoint_difference, seps_disjoint_valid_l.
  * sep_unfold; intros [m1] [m2] Hm; f_equal; apply map_eq; intros o;
      specialize (Hm o); rewrite lookup_union_with, lookup_difference_with.
    destruct (m1 !! o), (m2 !! o); simplify_option_eq; f_equal;
      intuition eauto using seps_union_difference, seps_difference_empty_rev.
  * sep_unfold; intros [m] Hm o w; specialize (Hm o).
    rewrite lookup_union_with; intros; destruct (m !! o); simplify_equality'.
    intuition eauto using seps_union_valid,
      seps_splittable_union, seps_positive_l.
  * sep_unfold; intros [m1] [m2] Hm Hm' o w ?; specialize (Hm o);
      specialize (Hm' o); unfold option_relation in *; simplify_option_eq.
    destruct (m2 !! o); naive_solver eauto using seps_disjoint_difference,
      seps_disjoint_valid_l, seps_splittable_weaken.
  * sep_unfold; intros [m] Hm o; specialize (Hm o); rewrite lookup_fmap.
    destruct (m !! o); try naive_solver
      auto using seps_half_empty_rev, seps_disjoint_half.
  * sep_unfold; intros [m] Hm; f_equal; apply map_eq; intros o;
      specialize (Hm o); rewrite lookup_union_with, lookup_fmap.
    destruct (m !! o); f_equal'; naive_solver auto using seps_union_half.
  * sep_unfold; intros [m1] [m2] Hm Hm'; f_equal; apply map_eq; intros o;
      rewrite lookup_fmap, !lookup_union_with, !lookup_fmap;
      specialize (Hm o); specialize (Hm' o); rewrite lookup_union_with in Hm'.
    destruct (m1 !! o), (m2 !! o); simplify_equality'; f_equal; auto.
    naive_solver auto using seps_union_half_distr.
  * sep_unfold; intros [m] ????; simplify_map_eq.
  * done.
  * sep_unfold; intros [m1] [m2] ? Hm; simplify_equality'. apply map_empty.
    intros o. specialize (Hm o); simplify_map_eq. by destruct (m1 !! o).
  * sep_unfold; intros [m1] [m2] ???; simpl in *; subst.
    by rewrite (left_id_L ∅ (union_with _)).
  * sep_unfold; intros [m]. split; [done|].
    intros [? Hm]. destruct (sep_inhabited A) as (x&?&?).
    specialize (Hm (FlatCMap {[fresh (dom indexset m) := [x]]}));
      feed specialize Hm; [|simplify_map_eq].
    intros o. destruct (m !! o) as [w|] eqn:Hw; simplify_map_eq.
    { rewrite lookup_singleton_ne; eauto. intros <-.
      eapply (is_fresh (dom indexset m)), fin_map_dom.elem_of_dom_2; eauto. }
    destruct ({[_ := _]} !! _) eqn:?; simplify_map_eq; split.
    + by rewrite Forall_singleton.
    + inversion_clear 1; decompose_Forall_hyps; eauto using sep_unmapped_empty.
  * done.
Qed.
