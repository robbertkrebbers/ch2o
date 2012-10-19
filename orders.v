(* Copyright (c) 2012, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects common properties of pre-orders and semi lattices. This
theory will mainly be used for the theory on collections and finite maps. *)
Require Import SetoidList.
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
    * firstorder.
    * firstorder.
    * intros x y z; split; transitivity y; firstorder.
  Qed.

  Global Instance: Proper ((≡) ==> (≡) ==> iff) (⊆).
  Proof.
    unfold equiv, preorder_equiv.
    intros x1 y1 ? x2 y2 ?. split; intro.
    * transitivity x1. tauto. transitivity x2; tauto.
    * transitivity y1. tauto. transitivity y2; tauto.
  Qed.

  Context `{∀ X Y : A, Decision (X ⊆ Y)}.
  Global Instance preorder_equiv_dec_slow (X Y : A) :
    Decision (X ≡ Y) | 100 := _.
End preorder.
Typeclasses Opaque preorder_equiv.
Hint Extern 0 (@Equivalence _ (≡)) =>
  class_apply preorder_equivalence : typeclass_instances.

(** * Join semi lattices *)
(** General purpose theorems on join semi lattices. *)
Section bounded_join_sl.
  Context `{BoundedJoinSemiLattice A}.

  Hint Resolve subseteq_empty subseteq_union_l subseteq_union_r union_least.

  Lemma union_compat_l x1 x2 y : x1 ⊆ x2 → x1 ⊆ x2 ∪ y.
  Proof. intros. transitivity x2; auto. Qed.
  Lemma union_compat_r x1 x2 y : x1 ⊆ x2 → x1 ⊆ y ∪ x2.
  Proof. intros. transitivity x2; auto. Qed.
  Hint Resolve union_compat_l union_compat_r.

  Lemma union_compat x1 x2 y1 y2 : x1 ⊆ x2 → y1 ⊆ y2 → x1 ∪ y1 ⊆ x2 ∪ y2.
  Proof. auto. Qed.
  Lemma union_empty x : x ∪ ∅ ⊆ x.
  Proof. by apply union_least. Qed.
  Lemma union_comm x y : x ∪ y ⊆ y ∪ x.
  Proof. auto. Qed.
  Lemma union_assoc_1 x y z : (x ∪ y) ∪ z ⊆ x ∪ (y ∪ z).
  Proof. auto. Qed.
  Lemma union_assoc_2 x y z : x ∪ (y ∪ z) ⊆ (x ∪ y) ∪ z.
  Proof. auto. Qed.

  Global Instance union_proper: Proper ((≡) ==> (≡) ==> (≡)) (∪).
  Proof.
    unfold equiv, preorder_equiv. split; apply union_compat; simpl in *; tauto.
  Qed.
  Global Instance: Idempotent (≡) (∪).
  Proof. split; eauto. Qed.
  Global Instance: LeftId (≡) ∅ (∪).
  Proof. split; eauto. Qed.
  Global Instance: RightId (≡) ∅ (∪).
  Proof. split; eauto. Qed.
  Global Instance: Commutative (≡) (∪).
  Proof. split; apply union_comm. Qed.
  Global Instance: Associative (≡) (∪).
  Proof. split. apply union_assoc_2. apply union_assoc_1. Qed.

  Lemma subseteq_union X Y : X ⊆ Y ↔ X ∪ Y ≡ Y.
  Proof. repeat split; eauto. intros E. rewrite <-E. auto. Qed.
  Lemma subseteq_union_1 X Y : X ⊆ Y → X ∪ Y ≡ Y.
  Proof. apply subseteq_union. Qed.
  Lemma subseteq_union_2 X Y : X ∪ Y ≡ Y → X ⊆ Y.
  Proof. apply subseteq_union. Qed.

  Lemma equiv_empty X : X ⊆ ∅ → X ≡ ∅.
  Proof. split; eauto. Qed.

  Global Instance: Proper (eqlistA (≡) ==> (≡)) union_list.
  Proof.
    induction 1; simpl.
    * done.
    * by apply union_proper.
  Qed.

  Lemma empty_union X Y : X ∪ Y ≡ ∅ ↔ X ≡ ∅ ∧ Y ≡ ∅.
  Proof.
    split.
    * intros E. split; apply equiv_empty;
        by transitivity (X ∪ Y); [auto | rewrite E].
    * intros [E1 E2]. by rewrite E1, E2, (left_id _ _).
  Qed.
  Lemma empty_list_union Xs : ⋃ Xs ≡ ∅ ↔ Forall (≡ ∅) Xs.
  Proof.
    split.
    * induction Xs; simpl; rewrite ?empty_union; intuition.
    * induction 1 as [|?? E1 ? E2]; simpl. done. by apply empty_union.
  Qed.

  Context `{∀ X Y : A, Decision (X ⊆ Y)}.
  Lemma non_empty_union X Y : X ∪ Y ≢ ∅ → X ≢ ∅ ∨ Y ≢ ∅.
  Proof. rewrite empty_union. destruct (decide (X ≡ ∅)); intuition. Qed.
  Lemma non_empty_list_union Xs : ⋃ Xs ≢ ∅ → Exists (≢ ∅) Xs.
  Proof. rewrite empty_list_union. apply (not_Forall_Exists _). Qed.
End bounded_join_sl.

(** * Meet semi lattices *)
(** The dual of the above section, but now for meet semi lattices. *)
Section meet_sl.
  Context `{MeetSemiLattice A}.

  Hint Resolve subseteq_intersection_l subseteq_intersection_r
    intersection_greatest.

  Lemma intersection_compat_l x1 x2 y : x1 ⊆ x2 → x1 ∩ y ⊆ x2.
  Proof. intros. transitivity x1; auto. Qed.
  Lemma intersection_compat_r x1 x2 y : x1 ⊆ x2 → y ∩ x1 ⊆ x2.
  Proof. intros. transitivity x1; auto. Qed.
  Hint Resolve intersection_compat_l intersection_compat_r.

  Lemma intersection_compat x1 x2 y1 y2 : x1 ⊆ x2 → y1 ⊆ y2 → x1 ∩ y1 ⊆ x2 ∩ y2.
  Proof. auto. Qed.
  Lemma intersection_comm x y : x ∩ y ⊆ y ∩ x.
  Proof. auto. Qed.
  Lemma intersection_assoc_1 x y z : (x ∩ y) ∩ z ⊆ x ∩ (y ∩ z).
  Proof. auto. Qed.
  Lemma intersection_assoc_2 x y z : x ∩ (y ∩ z) ⊆ (x ∩ y) ∩ z.
  Proof. auto. Qed.

  Global Instance: Proper ((≡) ==> (≡) ==> (≡)) (∩).
  Proof.
    unfold equiv, preorder_equiv. split;
      apply intersection_compat; simpl in *; tauto.
  Qed.
  Global Instance: Idempotent (≡) (∩).
  Proof. split; eauto. Qed.
  Global Instance: Commutative (≡) (∩).
  Proof. split; apply intersection_comm. Qed.
  Global Instance: Associative (≡) (∩).
  Proof. split. apply intersection_assoc_2. apply intersection_assoc_1. Qed.

  Lemma subseteq_intersection X Y : X ⊆ Y ↔ X ∩ Y ≡ X.
  Proof. repeat split; eauto. intros E. rewrite <-E. auto. Qed.
  Lemma subseteq_intersection_1 X Y : X ⊆ Y → X ∩ Y ≡ X.
  Proof. apply subseteq_intersection. Qed.
  Lemma subseteq_intersection_2 X Y : X ∩ Y ≡ X → X ⊆ Y.
  Proof. apply subseteq_intersection. Qed.
End meet_sl.

(** * Lower bounded lattices *)
Section lower_bounded_lattice.
  Context `{LowerBoundedLattice A}.

  Global Instance: LeftAbsorb (≡) ∅ (∩).
  Proof.
    split.
    * by apply subseteq_intersection_l.
    * by apply subseteq_empty.
  Qed.
  Global Instance: RightAbsorb (≡) ∅ (∩).
  Proof. intros ?. by rewrite (commutative _), (left_absorb _ _). Qed.
End lower_bounded_lattice.
