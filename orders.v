(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects common properties of pre-orders and semi lattices. This
theory will mainly be used for the theory on collections and finite maps. *)
Require Export base decidable tactics list.

(** * Pre-orders *)
(** We extend a pre-order to a partial order by defining equality as
[λ X Y, X ⊆ Y ∧ Y ⊆ X]. We prove that this indeed gives rise to a setoid. *)
Section preorder.
  Context `{SubsetEq A} `{!PreOrder (⊆)}.

  Global Instance preorder_equiv: Equiv A := λ X Y, X ⊆ Y ∧ Y ⊆ X.
  Instance preorder_equivalence: @Equivalence A (≡).
  Proof.
    split.
    * done.
    * by intros ?? [??].
    * by intros x y z [??] [??]; split; transitivity y.
  Qed.

  Global Instance: Proper ((≡) ==> (≡) ==> iff) (⊆).
  Proof.
    unfold equiv, preorder_equiv.
    intros x1 y1 ? x2 y2 ?. split; intro.
    * transitivity x1. tauto. transitivity x2; tauto.
    * transitivity y1. tauto. transitivity y2; tauto.
  Qed.

  Global Instance preorder_subset: Subset A := λ X Y, X ⊆ Y ∧ Y ⊈ X.
  Lemma subset_spec X Y : X ⊂ Y ↔ X ⊆ Y ∧ Y ⊈ X.
  Proof. done. Qed.
  Lemma subset_spec_alt X Y : X ⊂ Y ↔ X ⊆ Y ∧ X ≢ Y.
  Proof.
    split.
    * intros [? HYX]. split. done. contradict HYX. by rewrite HYX.
    * intros [? HXY]. split. done. by contradict HXY.
  Qed.

  Lemma subset_subseteq X Y : X ⊂ Y → X ⊆ Y.
  Proof. by intros [? _]. Qed.
  Lemma subset_transitive_l X Y Z : X ⊂ Y → Y ⊆ Z → X ⊂ Z.
  Proof.
    intros [? HXY] ?. split.
    * by transitivity Y.
    * contradict HXY. by transitivity Z.
  Qed.
  Lemma subset_transitive_r X Y Z : X ⊆ Y → Y ⊂ Z → X ⊂ Z.
  Proof.
    intros ? [? HYZ]. split.
    * by transitivity Y.
    * contradict HYZ. by transitivity X.
  Qed.

  Global Instance: StrictOrder (⊂).
  Proof.
    split.
    * firstorder.
    * eauto using subset_transitive_r, subset_subseteq.
  Qed.
  Global Instance: Proper ((≡) ==> (≡) ==> iff) (⊂).
  Proof. unfold subset, preorder_subset. solve_proper. Qed.

  Section leibniz.
    Context `{!LeibnizEquiv A}.

    Lemma subset_spec_alt_L X Y : X ⊂ Y ↔ X ⊆ Y ∧ X ≠ Y.
    Proof. unfold_leibniz. apply subset_spec_alt. Qed.
  End leibniz.

  Section dec.
    Context `{∀ X Y : A, Decision (X ⊆ Y)}.

    Global Instance preorder_equiv_dec_slow (X Y : A) :
      Decision (X ≡ Y) | 100 := _.
    Global Instance preorder_subset_dec_slow (X Y : A) :
      Decision (X ⊂ Y) | 100 := _.

    Lemma subseteq_inv X Y : X ⊆ Y → X ⊂ Y ∨ X ≡ Y.
    Proof. rewrite subset_spec_alt. destruct (decide (X ≡ Y)); tauto. Qed.
    Lemma not_subset_inv X Y : X ⊄ Y → X ⊈ Y ∨ X ≡ Y.
    Proof. rewrite subset_spec_alt. destruct (decide (X ≡ Y)); tauto. Qed.

    Context `{!LeibnizEquiv A}.

    Lemma subseteq_inv_L X Y : X ⊆ Y → X ⊂ Y ∨ X = Y.
    Proof. unfold_leibniz. apply subseteq_inv. Qed.
    Lemma not_subset_inv_L X Y : X ⊄ Y → X ⊈ Y ∨ X = Y.
    Proof. unfold_leibniz. apply not_subset_inv. Qed.
  End dec.
End preorder.

Typeclasses Opaque preorder_equiv.
Typeclasses Opaque preorder_subset.
Hint Extern 0 (@Equivalence _ (≡)) =>
  class_apply preorder_equivalence : typeclass_instances.

(** * Partial orders *)
Section partialorder.
  Context `{SubsetEq A} `{!PartialOrder (⊆)}.

  Global Instance: LeibnizEquiv A.
  Proof.
    split.
    * intros [??]. by apply (anti_symmetric _).
    * intros. by subst.
  Qed.
End partialorder.

(** * Join semi lattices *)
(** General purpose theorems on join semi lattices. *)
Section bounded_join_sl.
  Context `{BoundedJoinSemiLattice A}.

  Hint Resolve subseteq_empty union_subseteq_l union_subseteq_r union_least.

  Lemma union_subseteq_l_alt x1 x2 y : x1 ⊆ x2 → x1 ⊆ x2 ∪ y.
  Proof. intros. transitivity x2; auto. Qed.
  Lemma union_subseteq_r_alt x1 x2 y : x1 ⊆ x2 → x1 ⊆ y ∪ x2.
  Proof. intros. transitivity x2; auto. Qed.
  Hint Resolve union_subseteq_l_alt union_subseteq_r_alt.

  Lemma union_preserving_l x y1 y2 : y1 ⊆ y2 → x ∪ y1 ⊆ x ∪ y2.
  Proof. auto. Qed.
  Lemma union_preserving_r x1 x2 y : x1 ⊆ x2 → x1 ∪ y ⊆ x2 ∪ y.
  Proof. auto. Qed.
  Lemma union_preserving x1 x2 y1 y2 : x1 ⊆ x2 → y1 ⊆ y2 → x1 ∪ y1 ⊆ x2 ∪ y2.
  Proof. auto. Qed.

  Lemma union_empty x : x ∪ ∅ ⊆ x.
  Proof. by apply union_least. Qed.
  Lemma union_commutative_1 x y : x ∪ y ⊆ y ∪ x.
  Proof. auto. Qed.
  Lemma union_associative_1 x y z : (x ∪ y) ∪ z ⊆ x ∪ (y ∪ z).
  Proof. auto. Qed.
  Lemma union_associative_2 x y z : x ∪ (y ∪ z) ⊆ (x ∪ y) ∪ z.
  Proof. auto. Qed.

  Global Instance union_proper: Proper ((≡) ==> (≡) ==> (≡)) (∪).
  Proof.
    unfold equiv, preorder_equiv.
    split; apply union_preserving; simpl in *; tauto.
  Qed.
  Global Instance: Idempotent (≡) (∪).
  Proof. split; eauto. Qed.
  Global Instance: LeftId (≡) ∅ (∪).
  Proof. split; eauto. Qed.
  Global Instance: RightId (≡) ∅ (∪).
  Proof. split; eauto. Qed.
  Global Instance: Commutative (≡) (∪).
  Proof. split; apply union_commutative_1. Qed.
  Global Instance: Associative (≡) (∪).
  Proof. split. apply union_associative_2. apply union_associative_1. Qed.

  Lemma subseteq_union X Y : X ⊆ Y ↔ X ∪ Y ≡ Y.
  Proof. repeat split; eauto. intros E. rewrite <-E. auto. Qed.
  Lemma subseteq_union_1 X Y : X ⊆ Y → X ∪ Y ≡ Y.
  Proof. apply subseteq_union. Qed.
  Lemma subseteq_union_2 X Y : X ∪ Y ≡ Y → X ⊆ Y.
  Proof. apply subseteq_union. Qed.

  Lemma equiv_empty X : X ⊆ ∅ → X ≡ ∅.
  Proof. split; eauto. Qed.

  Global Instance union_list_proper: Proper (Forall2 (≡) ==> (≡)) union_list.
  Proof.
    induction 1; simpl.
    * done.
    * by apply union_proper.
  Qed.

  Lemma union_list_nil : ⋃ @nil A = ∅.
  Proof. done. Qed.
  Lemma union_list_cons (X : A) (Xs : list A) : ⋃ (X :: Xs) = X ∪ ⋃ Xs.
  Proof. done. Qed.
  Lemma union_list_singleton (X : A) : ⋃ [X] ≡ X.
  Proof. simpl. by rewrite (right_id ∅ _). Qed.
  Lemma union_list_app (Xs1 Xs2 : list A) : ⋃ (Xs1 ++ Xs2) ≡ ⋃ Xs1 ∪ ⋃ Xs2.
  Proof.
    induction Xs1 as [|X Xs1 IH]; simpl.
    * by rewrite (left_id ∅ _).
    * by rewrite IH, (associative _).
  Qed.
  Lemma union_list_reverse (Xs : list A) : ⋃ (reverse Xs) ≡ ⋃ Xs.
  Proof.
    induction Xs as [|X Xs IH]; simpl; [done |].
    by rewrite reverse_cons, union_list_app,
      union_list_singleton, (commutative _), IH.
  Qed.
  Lemma union_list_preserving (Xs Ys : list A) : Xs ⊆* Ys → ⋃ Xs ⊆ ⋃ Ys.
  Proof. induction 1; simpl; auto using union_preserving. Qed.

  Lemma empty_union X Y : X ∪ Y ≡ ∅ ↔ X ≡ ∅ ∧ Y ≡ ∅.
  Proof.
    split.
    * intros E. split; apply equiv_empty;
        by transitivity (X ∪ Y); [auto | rewrite E].
    * intros [E1 E2]. by rewrite E1, E2, (left_id _ _).
  Qed.
  Lemma empty_union_list Xs : ⋃ Xs ≡ ∅ ↔ Forall (≡ ∅) Xs.
  Proof.
    split.
    * induction Xs; simpl; rewrite ?empty_union; intuition.
    * induction 1 as [|?? E1 ? E2]; simpl. done. by apply empty_union.
  Qed.

  Section leibniz.
    Context `{!LeibnizEquiv A}.

    Global Instance: Idempotent (=) (∪).
    Proof. intros ?. unfold_leibniz. apply (idempotent _). Qed.
    Global Instance: LeftId (=) ∅ (∪).
    Proof. intros ?. unfold_leibniz. apply (left_id _ _). Qed.
    Global Instance: RightId (=) ∅ (∪).
    Proof. intros ?. unfold_leibniz. apply (right_id _ _). Qed.
    Global Instance: Commutative (=) (∪).
    Proof. intros ??. unfold_leibniz. apply (commutative _). Qed.
    Global Instance: Associative (=) (∪).
    Proof. intros ???. unfold_leibniz. apply (associative _). Qed.

    Lemma subseteq_union_L X Y : X ⊆ Y ↔ X ∪ Y = Y.
    Proof. unfold_leibniz. apply subseteq_union. Qed.
    Lemma subseteq_union_1_L X Y : X ⊆ Y → X ∪ Y = Y.
    Proof. unfold_leibniz. apply subseteq_union_1. Qed.
    Lemma subseteq_union_2_L X Y : X ∪ Y = Y → X ⊆ Y.
    Proof. unfold_leibniz. apply subseteq_union_2. Qed.

    Lemma equiv_empty_L X : X ⊆ ∅ → X = ∅.
    Proof. unfold_leibniz. apply equiv_empty. Qed.
    Lemma union_list_singleton_L (X : A) : ⋃ [X] = X.
    Proof. unfold_leibniz. apply union_list_singleton. Qed.
    Lemma union_list_app_L (Xs1 Xs2 : list A) : ⋃ (Xs1 ++ Xs2) = ⋃ Xs1 ∪ ⋃ Xs2.
    Proof. unfold_leibniz. apply union_list_app. Qed.
    Lemma union_list_reverse_L (Xs : list A) : ⋃ (reverse Xs) = ⋃ Xs.
    Proof. unfold_leibniz. apply union_list_reverse. Qed.

    Lemma empty_union_L X Y : X ∪ Y = ∅ ↔ X = ∅ ∧ Y = ∅.
    Proof. unfold_leibniz. apply empty_union. Qed.
    Lemma empty_union_list_L Xs : ⋃ Xs = ∅ ↔ Forall (= ∅) Xs.
    Proof. unfold_leibniz. apply empty_union_list. Qed.
  End leibniz.

  Section dec.
    Context `{∀ X Y : A, Decision (X ⊆ Y)}.

    Lemma non_empty_union X Y : X ∪ Y ≢ ∅ → X ≢ ∅ ∨ Y ≢ ∅.
    Proof. rewrite empty_union. destruct (decide (X ≡ ∅)); intuition. Qed.
    Lemma non_empty_union_list Xs : ⋃ Xs ≢ ∅ → Exists (≢ ∅) Xs.
    Proof. rewrite empty_union_list. apply (not_Forall_Exists _). Qed.

    Context `{!LeibnizEquiv A}.
    Lemma non_empty_union_L X Y : X ∪ Y ≠ ∅ → X ≠ ∅ ∨ Y ≠ ∅.
    Proof. unfold_leibniz. apply non_empty_union. Qed.
    Lemma non_empty_union_list_L Xs : ⋃ Xs ≠ ∅ → Exists (≠ ∅) Xs.
    Proof. unfold_leibniz. apply non_empty_union_list. Qed.
  End dec.
End bounded_join_sl.

(** * Meet semi lattices *)
(** The dual of the above section, but now for meet semi lattices. *)
Section meet_sl.
  Context `{MeetSemiLattice A}.

  Hint Resolve intersection_subseteq_l intersection_subseteq_r
    intersection_greatest.

  Lemma intersection_subseteq_l_alt x1 x2 y : x1 ⊆ x2 → x1 ∩ y ⊆ x2.
  Proof. intros. transitivity x1; auto. Qed.
  Lemma intersection_subseteq_r_alt x1 x2 y : x1 ⊆ x2 → y ∩ x1 ⊆ x2.
  Proof. intros. transitivity x1; auto. Qed.
  Hint Resolve intersection_subseteq_l_alt intersection_subseteq_r_alt.

  Lemma intersection_preserving_l x y1 y2 : y1 ⊆ y2 → x ∩ y1 ⊆ x ∩ y2.
  Proof. auto. Qed.
  Lemma intersection_preserving_r x1 x2 y : x1 ⊆ x2 → x1 ∩ y ⊆ x2 ∩ y.
  Proof. auto. Qed.
  Lemma intersection_preserving x1 x2 y1 y2 :
    x1 ⊆ x2 → y1 ⊆ y2 → x1 ∩ y1 ⊆ x2 ∩ y2.
  Proof. auto. Qed.

  Lemma intersection_commutative_1 x y : x ∩ y ⊆ y ∩ x.
  Proof. auto. Qed.
  Lemma intersection_associative_1 x y z : (x ∩ y) ∩ z ⊆ x ∩ (y ∩ z).
  Proof. auto. Qed.
  Lemma intersection_associative_2 x y z : x ∩ (y ∩ z) ⊆ (x ∩ y) ∩ z.
  Proof. auto. Qed.

  Global Instance: Proper ((≡) ==> (≡) ==> (≡)) (∩).
  Proof.
    unfold equiv, preorder_equiv. split;
      apply intersection_preserving; simpl in *; tauto.
  Qed.
  Global Instance: Idempotent (≡) (∩).
  Proof. split; eauto. Qed.
  Global Instance: Commutative (≡) (∩).
  Proof. split; apply intersection_commutative_1. Qed.
  Global Instance: Associative (≡) (∩).
  Proof.
    split. apply intersection_associative_2. apply intersection_associative_1.
  Qed.

  Lemma subseteq_intersection X Y : X ⊆ Y ↔ X ∩ Y ≡ X.
  Proof. repeat split; eauto. intros E. rewrite <-E. auto. Qed.
  Lemma subseteq_intersection_1 X Y : X ⊆ Y → X ∩ Y ≡ X.
  Proof. apply subseteq_intersection. Qed.
  Lemma subseteq_intersection_2 X Y : X ∩ Y ≡ X → X ⊆ Y.
  Proof. apply subseteq_intersection. Qed.

  Section leibniz.
    Context `{!LeibnizEquiv A}.

    Global Instance: Idempotent (=) (∩).
    Proof. intros ?. unfold_leibniz. apply (idempotent _). Qed.
    Global Instance: Commutative (=) (∩).
    Proof. intros ??. unfold_leibniz. apply (commutative _). Qed.
    Global Instance: Associative (=) (∩).
    Proof. intros ???. unfold_leibniz. apply (associative _). Qed.

    Lemma subseteq_intersection_L X Y : X ⊆ Y ↔ X ∩ Y = X.
    Proof. unfold_leibniz. apply subseteq_intersection. Qed.
    Lemma subseteq_intersection_1_L X Y : X ⊆ Y → X ∩ Y = X.
    Proof. unfold_leibniz. apply subseteq_intersection_1. Qed.
    Lemma subseteq_intersection_2_L X Y : X ∩ Y = X → X ⊆ Y.
    Proof. unfold_leibniz. apply subseteq_intersection_2. Qed.
  End leibniz.
End meet_sl.

(** * Lower bounded lattices *)
Section lower_bounded_lattice.
  Context `{LowerBoundedLattice A}.

  Global Instance: LeftAbsorb (≡) ∅ (∩).
  Proof.
    split.
    * by apply intersection_subseteq_l.
    * by apply subseteq_empty.
  Qed.
  Global Instance: RightAbsorb (≡) ∅ (∩).
  Proof. intros ?. by rewrite (commutative _), (left_absorb _ _). Qed.

  Global Instance: LeftDistr (≡) (∪) (∩).
  Proof.
    intros x y z. split.
    * apply union_least.
      { apply intersection_greatest; auto using union_subseteq_l. }
      apply intersection_greatest.
      + apply union_subseteq_r_alt, intersection_subseteq_l.
      + apply union_subseteq_r_alt, intersection_subseteq_r.
    * apply lbl_distr.
  Qed.
  Global Instance: RightDistr (≡) (∪) (∩).
  Proof. intros x y z. by rewrite !(commutative _ _ z), (left_distr _ _). Qed.

  Global Instance: LeftDistr (≡) (∩) (∪).
  Proof.
    intros x y z. split.
    * rewrite (left_distr (∪) (∩)).
      apply intersection_greatest.
      { apply union_subseteq_r_alt, intersection_subseteq_l. }
      rewrite (right_distr (∪) (∩)). apply intersection_preserving.
      + apply union_subseteq_l.
      + done.
    * apply intersection_greatest.
      { apply union_least; auto using intersection_subseteq_l. }
      apply union_least.
      + apply intersection_subseteq_r_alt, union_subseteq_l.
      + apply intersection_subseteq_r_alt, union_subseteq_r.
  Qed.
  Global Instance: RightDistr (≡) (∩) (∪).
  Proof.
    intros x y z. by rewrite !(commutative _ _ z), (left_distr _ _).
  Qed.

  Section leibniz.
    Context `{!LeibnizEquiv A}.

    Global Instance: LeftAbsorb (=) ∅ (∩).
    Proof. intros ?. unfold_leibniz. apply (left_absorb _ _). Qed.
    Global Instance: RightAbsorb (=) ∅ (∩).
    Proof. intros ?. unfold_leibniz. apply (right_absorb _ _). Qed.

    Global Instance: LeftDistr (=) (∪) (∩).
    Proof. intros ???. unfold_leibniz. apply (left_distr _ _). Qed.
    Global Instance: RightDistr (=) (∪) (∩).
    Proof. intros ???. unfold_leibniz. apply (right_distr _ _). Qed.

    Global Instance: LeftDistr (=) (∩) (∪).
    Proof. intros ???. unfold_leibniz. apply (left_distr _ _). Qed.
    Global Instance: RightDistr (=) (∩) (∪).
    Proof. intros ???. unfold_leibniz. apply (right_distr _ _). Qed.
  End leibniz.
End lower_bounded_lattice.
