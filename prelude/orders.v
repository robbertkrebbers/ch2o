(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects common properties of pre-orders and semi lattices. This
theory will mainly be used for the theory on collections and finite maps. *)

From stdpp Require Export prelude.
Require Export base.

#[global] Instance preorder_equiv `{SubsetEq A} : Equiv A | 100 := λ X Y, X ⊆ Y ∧ Y ⊆ X.

(** * Partial orders *)
Section partial_order.
  Context `{SubsetEq A, !PartialOrder (@subseteq A _)}.
  Global Instance: LeibnizEquiv A.
  Proof. unfold LeibnizEquiv. intros * [? ?]. by apply (anti_symm (⊆)). Qed.
End partial_order.

Section join_semi_lattice.
  Context `{Empty A, JoinSemiLattice A, !EmptySpec A}.
  Implicit Types X Y : A.
  Implicit Types Xs Ys : list A.

  Local Instance: @Equivalence A (≡@{A}).
  Proof.
    split.
    * done.
    * by intros ?? [??].
    * by intros X Y Z [??] [??]; split; transitivity Y.
  Qed.

  Local Instance: Proper ((≡@{A}) ==> (≡@{A}) ==> (iff)) (⊆@{A}).
  Proof.
    unfold equiv, preorder_equiv. intros X1 Y1 ? X2 Y2 ?. split; intro.
    * transitivity X1. tauto. transitivity X2; tauto.
    * transitivity Y1. tauto. transitivity Y2; tauto.
  Qed.

  Local Hint Resolve subseteq_empty union_subseteq_l union_subseteq_r union_least: core.
  Lemma union_subseteq_l_transitive X1 X2 Y : X1 ⊆ X2 → X1 ⊆ X2 ∪ Y.
  Proof. intros. transitivity X2; auto. Qed.
  Lemma union_subseteq_r_transitive X1 X2 Y : X1 ⊆ X2 → X1 ⊆ Y ∪ X2.
  Proof. intros. transitivity X2; auto. Qed.
  Local Hint Resolve union_subseteq_l_transitive union_subseteq_r_transitive: core.
  Lemma union_preserving_l X Y1 Y2 : Y1 ⊆ Y2 → X ∪ Y1 ⊆ X ∪ Y2.
  Proof. auto. Qed.
  Lemma union_preserving_r X1 X2 Y : X1 ⊆ X2 → X1 ∪ Y ⊆ X2 ∪ Y.
  Proof. auto. Qed.
  Lemma union_preserving X1 X2 Y1 Y2 : X1 ⊆ X2 → Y1 ⊆ Y2 → X1 ∪ Y1 ⊆ X2 ∪ Y2.
  Proof. auto. Qed.
  Lemma union_empty X : X ∪ ∅ ⊆ X.
  Proof. by apply union_least. Qed.
  Global Instance union_proper : Proper ((≡@{A}) ==> (≡@{A}) ==> (≡@{A})) (∪).
  Proof.
    unfold equiv, preorder_equiv.
    split; apply union_preserving; simpl in *; tauto.
  Qed.
  Global Instance: IdemP (≡@{A}) (∪).
  Proof. split; eauto. Qed.
  Global Instance: LeftId (≡@{A}) ∅ (∪).
  Proof. split; eauto. Qed.
  Global Instance: RightId (≡@{A}) ∅ (∪).
  Proof. split; eauto. Qed.
  Global Instance: Comm (≡@{A}) (∪).
  Proof. split; auto. Qed.
  Global Instance: Assoc (≡@{A}) (∪).
  Proof. split; auto. Qed.
  Lemma subseteq_union X Y : X ⊆ Y ↔ X ∪ Y ≡ Y.
  Proof. repeat split; eauto. intros HXY. rewrite <-HXY. auto. Qed.
  Lemma subseteq_union_1 X Y : X ⊆ Y → X ∪ Y ≡ Y.
  Proof. apply subseteq_union. Qed.
  Lemma subseteq_union_2 X Y : X ∪ Y ≡ Y → X ⊆ Y.
  Proof. apply subseteq_union. Qed.
  Lemma equiv_empty X : X ⊆ ∅ → X ≡ ∅.
  Proof. split; eauto. Qed.
  Global Instance union_list_proper: Proper (Forall2 (≡@{A}) ==> (≡@{A})) union_list.
  Proof. induction 1; simpl. done. by apply union_proper. Qed.
  Lemma union_list_nil : ⋃ @nil A = ∅.
  Proof. done. Qed.
  Lemma union_list_cons X Xs : ⋃ (X :: Xs) = X ∪ ⋃ Xs.
  Proof. done. Qed.
  Lemma union_list_singleton X : ⋃ [X] ≡ X.
  Proof. simpl. by rewrite (right_id ∅ _). Qed.
  Lemma union_list_app Xs1 Xs2 : ⋃ (Xs1 ++ Xs2) ≡ ⋃ Xs1 ∪ ⋃ Xs2.
  Proof.
    induction Xs1 as [|X Xs1 IH]; simpl; [by rewrite (left_id ∅ _)|].
    by rewrite IH, (assoc _).
  Qed.
  Lemma union_list_reverse Xs : ⋃ (reverse Xs) ≡ ⋃ Xs.
  Proof.
    induction Xs as [|X Xs IH]; simpl; [done |].
    by rewrite reverse_cons, union_list_app,
      union_list_singleton, (comm _), IH.
  Qed.
  Lemma union_list_preserving Xs Ys : Xs ⊆* Ys → ⋃ Xs ⊆ ⋃ Ys.
  Proof. induction 1; simpl; auto using union_preserving. Qed.
  Lemma empty_union X Y : X ∪ Y ≡ ∅ ↔ X ≡ ∅ ∧ Y ≡ ∅.
  Proof.
    split.
    * intros HXY. split; apply equiv_empty;
        by transitivity (X ∪ Y); [auto | rewrite HXY].
    * intros [HX HY]. by rewrite HX, HY, (left_id _ _).
  Qed.
  Lemma empty_union_list Xs : ⋃ Xs ≡ ∅ ↔ Forall (.≡ ∅) Xs.
  Proof.
    split.
    * induction Xs; simpl; rewrite ?empty_union; intuition.
    * induction 1 as [|?? E1 ? E2]; simpl. done. by apply empty_union.
  Qed.

  Section leibniz.
    Context `{!LeibnizEquiv A}.
    Global Instance: IdemP (=@{A}) (∪).
    Proof. intros ?. unfold_leibniz. apply (idemp _). Qed.
    Global Instance: LeftId (=@{A}) ∅ (∪).
    Proof. intros ?. unfold_leibniz. apply (left_id _ _). Qed.
    Global Instance: RightId (=@{A}) ∅ (∪).
    Proof. intros ?. unfold_leibniz. apply (right_id _ _). Qed.
    Global Instance: Comm (=@{A}) (∪).
    Proof. intros ??. unfold_leibniz. apply (comm _). Qed.
    Global Instance: Assoc (=@{A}) (∪).
    Proof. intros ???. unfold_leibniz. apply (assoc _). Qed.
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
    Lemma empty_union_list_L Xs : ⋃ Xs = ∅ ↔ Forall (.= ∅) Xs.
    Proof. unfold_leibniz. by rewrite empty_union_list. Qed. 
  End leibniz.

  Section dec.
    Context `{∀ X Y : A, Decision (X ⊆ Y)}.
    Lemma non_empty_union X Y : X ∪ Y ≢ ∅ ↔ X ≢ ∅ ∨ Y ≢ ∅.
    Proof. rewrite empty_union. destruct (decide (X ≡ ∅)); intuition. Qed.
    Lemma non_empty_union_list Xs : ⋃ Xs ≢ ∅ → Exists (.≢ ∅) Xs.
    Proof. rewrite empty_union_list. apply (not_Forall_Exists _). Qed.
    Context `{!LeibnizEquiv A}.
    Lemma non_empty_union_L X Y : X ∪ Y ≠ ∅ ↔ X ≠ ∅ ∨ Y ≠ ∅.
    Proof. unfold_leibniz. apply non_empty_union. Qed.
    Lemma non_empty_union_list_L Xs : ⋃ Xs ≠ ∅ → Exists (.≠ ∅) Xs.
    Proof. unfold_leibniz. apply non_empty_union_list. Qed.
  End dec.
End join_semi_lattice.