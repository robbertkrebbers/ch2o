(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export ctrees refinements.

(** We pack the memory into a record so as to avoid ambiguity with already
existing type class instances for finite maps. *)
Record cmap (Ti A : Set) : Set := CMap { cmap_car : indexmap (ctree Ti A) }.
Arguments CMap {_ _} _.
Arguments cmap_car {_ _} _.
Add Printing Constructor cmap.
Instance: Injective (=) (=) (@CMap Ti A).
Proof. by injection 1. Qed.

Instance cmap_ops {Ti A : Set} `{∀ τi1 τi2 : Ti, Decision (τi1 = τi2),
    SeparationOps A} : SeparationOps (cmap Ti A) := {
  sep_empty := CMap ∅;
  sep_union m1 m2 :=
    let (m1) := m1 in let (m2) := m2 in
    CMap (union_with (λ w1 w2, Some (w1 ∪ w2)) m1 m2);
  sep_difference m1 m2 :=
    let (m1) := m1 in let (m2) := m2 in
    CMap (difference_with (λ w1 w2,
      let w := w1 ∖ w2 in guard (¬ctree_empty w); Some w
    ) m1 m2);
  sep_half m := let (m) := m in CMap (½ <$> m);
  sep_valid m :=
    let (m) := m in map_Forall (λ _ w, ctree_valid w ∧ ¬ctree_empty w) m;
  sep_disjoint m1 m2 :=
    let (m1) := m1 in let (m2) := m2 in map_Forall2
      (λ w1 w2, w1 ⊥ w2 ∧ ¬ctree_empty w1 ∧ ¬ctree_empty w2) 
      (λ w1, ctree_valid w1 ∧ ¬ctree_empty w1)
      (λ w2, ctree_valid w2 ∧ ¬ctree_empty w2) m1 m2;
  sep_splittable m :=
    let (m) := m in
    map_Forall (λ _ w, ctree_valid w ∧ ¬ctree_empty w ∧ ctree_splittable w) m;
  sep_subseteq m1 m2 :=
    let (m1) := m1 in let (m2) := m2 in map_Forall2
      (λ w1 w2, w1 ⊆ w2 ∧ ¬ctree_empty w1)
      (λ w1, False)
      (λ w2, ctree_valid w2 ∧ ¬ctree_empty w2) m1 m2;
  sep_unmapped m := cmap_car m = ∅;
  sep_unshared m := False
}.
Proof.
  * intros []; apply _.
  * intros [] []; apply _.
  * intros [] []; apply _.
  * solve_decision.
  * intros []; apply _.
Defined.

Instance cmap_sep {Ti A : Set} `{∀ τi1 τi2 : Ti, Decision (τi1 = τi2),
  Separation A} : Separation (cmap Ti A).
Proof.
  split.
  * destruct (sep_inhabited A) as (x&?&?).
    eexists (CMap {[fresh ∅, MUnionAll (fresh ∅) [x]]}).
    split; [|by intro]. intros o w ?; simplify_map_equality'. split.
    + by constructor; rewrite Forall_singleton.
    + by inversion_clear 1; decompose_Forall_hyps'.
  * sep_unfold; intros [m1] [m2] Hm o w; specialize (Hm o); simpl in *.
    intros Hx. rewrite Hx in Hm.
    destruct (m2 !! o); intuition eauto using ctree_disjoint_valid_l.
  * sep_unfold; intros [m1] [m2] Hm o w; specialize (Hm o); simpl in *.
    rewrite lookup_union_with. intros. destruct (m1 !! o), (m2 !! o);
      simplify_equality'; intuition eauto
      using ctree_union_valid, ctree_positive_l.
  * sep_unfold. intros [m] Hm o; specialize (Hm o); simplify_map_equality'.
    destruct (m !! o); eauto.
  * sep_unfold; intros [m] ?; f_equal'. by rewrite (left_id_L ∅ _).
  * sep_unfold. intros [m1] [m2] Hm o; specialize (Hm o); simpl in *.
    destruct (m1 !! o), (m2 !! o); intuition.
  * sep_unfold; intros [m1] [m2] Hm; f_equal'. apply union_with_commutative.
    intros o w1 w2 ??; specialize (Hm o); simplify_option_equality.
    f_equal; intuition auto using ctree_commutative.
  * sep_unfold; intros [m1] [m2] [m3] Hm Hm' o; specialize (Hm o);
      specialize (Hm' o); simpl in *; rewrite lookup_union_with in Hm'.
    destruct (m1 !! o) eqn:?, (m2 !! o), (m3 !! o); simplify_equality';
      intuition eauto using ctree_disjoint_valid_l, ctree_disjoint_ll.
  * sep_unfold; intros [m1] [m2] [m3] Hm Hm' o; specialize (Hm o);
      specialize (Hm' o); simpl in *; rewrite lookup_union_with in Hm' |- *.
    destruct (m1 !! o) eqn:?, (m2 !! o), (m3 !! o); simplify_equality';
      intuition eauto using ctree_disjoint_valid_l, ctree_disjoint_move_l,
      ctree_union_valid, ctree_positive_l, ctree_disjoint_lr.
  * sep_unfold; intros [m1] [m2] [m3] Hm Hm'; f_equal'.
    apply map_eq; intros o; specialize (Hm o); specialize (Hm' o); simpl in *;
      rewrite !lookup_union_with; rewrite lookup_union_with in Hm'.
    destruct (m1 !! o) eqn:?, (m2 !! o), (m3 !! o); simplify_equality'; eauto.
    f_equal; intuition auto using ctree_associative.
  * sep_unfold; intros [m1] [m2] _; rewrite !(injective_iff CMap); intros Hm.
    apply map_eq; intros o. rewrite lookup_empty.
    apply (f_equal (!! o)) in Hm; rewrite lookup_union_with, lookup_empty in Hm.
    by destruct (m1 !! o), (m2 !! o); simplify_equality'.
  * sep_unfold; intros [m1] [m2] [m3] Hm Hm'; rewrite !(injective_iff CMap);
      intros Hm''; apply map_eq; intros o.
    specialize (Hm o); specialize (Hm' o);
      apply (f_equal (!! o)) in Hm''; rewrite !lookup_union_with in Hm''.
    destruct (m1 !! o) eqn:?, (m2 !! o), (m3 !! o); simplify_equality';
      f_equal; naive_solver eauto using ctree_cancel_l,
      ctree_cancel_empty_l, ctree_cancel_empty_r.
  * sep_unfold; intros [m1] [m2] Hm o; specialize (Hm o).
    rewrite lookup_union_with. destruct (m1 !! o), (m2 !! o); simpl;
      intuition auto using ctree_union_subseteq_l, ctree_subseteq_reflexive.
  * sep_unfold; intros [m1] [m2] Hm o; specialize (Hm o).
    rewrite lookup_difference_with; destruct (m1 !! o), (m2 !! o);
      simplify_option_equality;
      intuition eauto using ctree_disjoint_difference, ctree_disjoint_valid_l.
  * sep_unfold; intros [m1] [m2] Hm; f_equal; apply map_eq; intros o;
      specialize (Hm o); rewrite lookup_union_with, lookup_difference_with.
    destruct (m1 !! o), (m2 !! o); simplify_option_equality; f_equal;
      intuition eauto using ctree_union_difference, ctree_difference_empty_rev.
  * sep_unfold; intros [m] Hm o w; specialize (Hm o).
    rewrite lookup_union_with; intros; destruct (m !! o); simplify_equality'.
    intuition eauto using ctree_union_valid,
      ctree_splittable_union, ctree_positive_l.
  * sep_unfold; intros [m1] [m2] Hm Hm' o w ?; specialize (Hm o);
      specialize (Hm' o); simplify_option_equality.
    destruct (m2 !! o); naive_solver eauto using ctree_disjoint_difference,
      ctree_disjoint_valid_l, ctree_splittable_weaken.
  * sep_unfold; intros [m] Hm o; specialize (Hm o); rewrite lookup_fmap.
    destruct (m !! o); naive_solver
      auto using ctree_half_empty_rev, ctree_disjoint_half.
  * sep_unfold; intros [m] Hm; f_equal; apply map_eq; intros o;
      specialize (Hm o); rewrite lookup_union_with, lookup_fmap.
    destruct (m !! o); f_equal'; naive_solver auto using ctree_union_half.
  * sep_unfold; intros [m1] [m2] Hm Hm'; f_equal; apply map_eq; intros o;
      rewrite lookup_fmap, !lookup_union_with, !lookup_fmap;
      specialize (Hm o); specialize (Hm' o); rewrite lookup_union_with in Hm'.
    destruct (m1 !! o), (m2 !! o); simplify_equality'; f_equal; auto.
    naive_solver auto using ctree_union_half_distr.
  * sep_unfold; intros [m] ????; simplify_map_equality'.
  * done.
  * sep_unfold; intros [m1] [m2] ? Hm; simplify_equality'. apply map_empty.
    intros o. specialize (Hm o); simplify_map_equality. by destruct (m1 !! o).
  * sep_unfold; intros [m1] [m2] ???; simpl in *; subst.
    by rewrite (left_id_L ∅ (union_with _)).
  * sep_unfold; intros [m]. split; [done|].
    intros [? Hm]. destruct (sep_inhabited A) as (x&?&?).
    specialize (Hm (CMap {[fresh (dom _ m),MUnionAll (fresh ∅) [x]]}));
      feed specialize Hm; [|simplify_map_equality'].
    intros o. destruct (m !! o) as [w|] eqn:Hw; simplify_map_equality'.
    { rewrite lookup_singleton_ne; eauto. intros <-.
      eapply (is_fresh (dom indexset m)), fin_map_dom.elem_of_dom_2; eauto. }
    destruct ({[_]} !! _) eqn:?; simplify_map_equality; split.
    + by constructor; rewrite Forall_singleton.
    + by inversion_clear 1; decompose_Forall_hyps'.
Qed.
