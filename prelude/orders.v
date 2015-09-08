(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects common properties of pre-orders and semi lattices. This
theory will mainly be used for the theory on collections and finite maps. *)
Require Export Sorted.
Require Export base decidable tactics list.

(** * Arbitrary pre-, parial and total orders *)
(** Properties about arbitrary pre-, partial, and total orders. We do not use
the relation [⊆] because we often have multiple orders on the same structure *)
Section orders.
  Context {A} {R : relation A}.
  Implicit Types X Y : A.
  Infix "⊆" := R.
  Notation "X ⊈ Y" := (¬X ⊆ Y).
  Infix "⊂" := (strict R).

  Lemma reflexive_eq `{!Reflexive R} X Y : X = Y → X ⊆ Y.
  Proof. by intros <-. Qed.
  Lemma anti_symmetric_iff `{!PartialOrder R} X Y : X = Y ↔ R X Y ∧ R Y X.
  Proof. intuition (subst; auto). Qed.
  Lemma strict_spec X Y : X ⊂ Y ↔ X ⊆ Y ∧ Y ⊈ X.
  Proof. done. Qed.
  Lemma strict_include X Y : X ⊂ Y → X ⊆ Y.
  Proof. by intros [? _]. Qed.
  Lemma strict_ne X Y : X ⊂ Y → X ≠ Y.
  Proof. by intros [??] <-. Qed.
  Lemma strict_ne_sym X Y : X ⊂ Y → Y ≠ X.
  Proof. by intros [??] <-. Qed.
  Lemma strict_transitive_l `{!Transitive R} X Y Z : X ⊂ Y → Y ⊆ Z → X ⊂ Z.
  Proof.
    intros [? HXY] ?. split; [by transitivity Y|].
    contradict HXY. by transitivity Z.
  Qed.
  Lemma strict_transitive_r `{!Transitive R} X Y Z : X ⊆ Y → Y ⊂ Z → X ⊂ Z.
  Proof.
    intros ? [? HYZ]. split; [by transitivity Y|].
    contradict HYZ. by transitivity X.
  Qed.
  Global Instance: Irreflexive (strict R).
  Proof. firstorder. Qed.
  Global Instance: Transitive R → StrictOrder (strict R).
  Proof.
    split; try apply _.
    eauto using strict_transitive_r, strict_include.
  Qed.
  Global Instance preorder_subset_dec_slow `{∀ X Y, Decision (X ⊆ Y)}
    (X Y : A) : Decision (X ⊂ Y) | 100 := _.
  Lemma strict_spec_alt `{!AntiSymmetric (=) R} X Y : X ⊂ Y ↔ X ⊆ Y ∧ X ≠ Y.
  Proof.
    split.
    * intros [? HYX]. split. done. by intros <-.
    * intros [? HXY]. split. done. by contradict HXY; apply (anti_symmetric R).
  Qed.
  Lemma po_eq_dec `{!PartialOrder R, ∀ X Y, Decision (X ⊆ Y)} (X Y : A) :
    Decision (X = Y).
  Proof.
    refine (cast_if_and (decide (X ⊆ Y)) (decide (Y ⊆ X)));
     abstract (rewrite anti_symmetric_iff; tauto).
  Defined.
  Lemma total_not `{!Total R} X Y : X ⊈ Y → Y ⊆ X.
  Proof. intros. destruct (total R X Y); tauto. Qed.
  Lemma total_not_strict `{!Total R} X Y : X ⊈ Y → Y ⊂ X.
  Proof. red; auto using total_not. Qed.
  Global Instance trichotomy_total
    `{!Trichotomy (strict R), !Reflexive R} : Total R.
  Proof.
    intros X Y.
    destruct (trichotomy (strict R) X Y) as [[??]|[<-|[??]]]; intuition.
  Qed.
End orders.

Section strict_orders.
  Context {A} {R : relation A}.
  Implicit Types X Y : A.
  Infix "⊂" := R.

  Lemma irreflexive_eq `{!Irreflexive R} X Y : X = Y → ¬X ⊂ Y.
  Proof. intros ->. apply (irreflexivity R). Qed.
  Lemma strict_anti_symmetric `{!StrictOrder R} X Y :
    X ⊂ Y → Y ⊂ X → False.
  Proof. intros. apply (irreflexivity R X). by transitivity Y. Qed.
  Global Instance trichotomyT_dec `{!TrichotomyT R, !StrictOrder R} X Y :
      Decision (X ⊂ Y) :=
    match trichotomyT R X Y with
    | inleft (left H) => left H
    | inleft (right H) => right (irreflexive_eq _ _ H)
    | inright H => right (strict_anti_symmetric _ _ H)
    end.
  Global Instance trichotomyT_trichotomy `{!TrichotomyT R} : Trichotomy R.
  Proof. intros X Y. destruct (trichotomyT R X Y) as [[|]|]; tauto. Qed.
End strict_orders.

Ltac simplify_order := repeat
  match goal with
  | _ => progress simplify_equality
  | H : ?R ?x ?x |- _ => by destruct (irreflexivity _ _ H)
  | H1 : ?R ?x ?y |- _ =>
    match goal with
    | H2 : R y x |- _ =>
      assert (x = y) by (by apply (anti_symmetric R)); clear H1 H2
    | H2 : R y ?z |- _ =>
      unless (R x z) by done;
      assert (R x z) by (by transitivity y)
    end
  end.

(** * Sorting *)
(** Merge sort. Adapted from the implementation of Hugo Herbelin in the Coq
standard library, but without using the module system. *)
Section merge_sort.
  Context  {A} (R : relation A) `{∀ x y, Decision (R x y)}.

  Fixpoint list_merge (l1 : list A) : list A → list A :=
    fix list_merge_aux l2 :=
    match l1, l2 with
    | [], _ => l2
    | _, [] => l1
    | x1 :: l1, x2 :: l2 =>
       if decide_rel R x1 x2 then x1 :: list_merge l1 (x2 :: l2)
       else x2 :: list_merge_aux l2
    end.
  Global Arguments list_merge !_ !_ /.

  Local Notation stack := (list (option (list A))).
  Fixpoint merge_list_to_stack (st : stack) (l : list A) : stack :=
    match st with
    | [] => [Some l]
    | None :: st => Some l :: st
    | Some l' :: st => None :: merge_list_to_stack st (list_merge l' l)
    end.
  Fixpoint merge_stack (st : stack) : list A :=
    match st with
    | [] => []
    | None :: st => merge_stack st
    | Some l :: st => list_merge l (merge_stack st)
    end.
  Fixpoint merge_sort_aux (st : stack) (l : list A) : list A :=
    match l with
    | [] => merge_stack st
    | x :: l => merge_sort_aux (merge_list_to_stack st [x]) l
    end.
  Definition merge_sort : list A → list A := merge_sort_aux [].
End merge_sort.

(** ** Properties of the [Sorted] and [StronglySorted] predicate *)
Section sorted.
  Context {A} (R : relation A).

  Lemma Sorted_StronglySorted `{!Transitive R} l :
    Sorted R l → StronglySorted R l.
  Proof. by apply Sorted.Sorted_StronglySorted. Qed.
  Lemma StronglySorted_unique `{!AntiSymmetric (=) R} l1 l2 :
    StronglySorted R l1 → StronglySorted R l2 → l1 ≡ₚ l2 → l1 = l2.
  Proof.
    intros Hl1; revert l2. induction Hl1 as [|x1 l1 ? IH Hx1]; intros l2 Hl2 E.
    { symmetry. by apply Permutation_nil. }
    destruct Hl2 as [|x2 l2 ? Hx2].
    { by apply Permutation_nil in E. }
    assert (x1 = x2); subst.
    { rewrite Forall_forall in Hx1, Hx2.
      assert (x2 ∈ x1 :: l1) as Hx2' by (by rewrite E; left).
      assert (x1 ∈ x2 :: l2) as Hx1' by (by rewrite <-E; left).
      inversion Hx1'; inversion Hx2'; simplify_equality; auto. }
    f_equal. by apply IH, (injective (x2 ::)).
  Qed.
  Lemma Sorted_unique `{!Transitive R, !AntiSymmetric (=) R} l1 l2 :
    Sorted R l1 → Sorted R l2 → l1 ≡ₚ l2 → l1 = l2.
  Proof. auto using StronglySorted_unique, Sorted_StronglySorted. Qed.

  Global Instance HdRel_dec x `{∀ y, Decision (R x y)} l :
    Decision (HdRel R x l).
  Proof.
   refine
    match l with
    | [] => left _
    | y :: l => cast_if (decide (R x y))
    end; abstract first [by constructor | by inversion 1].
  Defined.
  Global Instance Sorted_dec `{∀ x y, Decision (R x y)} : ∀ l,
    Decision (Sorted R l).
  Proof.
   refine
    (fix go l :=
    match l return Decision (Sorted R l) with
    | [] => left _
    | x :: l => cast_if_and (decide (HdRel R x l)) (go l)
    end); clear go; abstract first [by constructor | by inversion 1].
  Defined.
  Global Instance StronglySorted_dec `{∀ x y, Decision (R x y)} : ∀ l,
    Decision (StronglySorted R l).
  Proof.
   refine
    (fix go l :=
    match l return Decision (StronglySorted R l) with
    | [] => left _
    | x :: l => cast_if_and (decide (Forall (R x) l)) (go l)
    end); clear go; abstract first [by constructor | by inversion 1].
  Defined.

  Context {B} (f : A → B).
  Lemma HdRel_fmap (R1 : relation A) (R2 : relation B) x l :
    (∀ y, R1 x y → R2 (f x) (f y)) → HdRel R1 x l → HdRel R2 (f x) (f <$> l).
  Proof. destruct 2; constructor; auto. Qed.
  Lemma Sorted_fmap (R1 : relation A) (R2 : relation B) l :
    (∀ x y, R1 x y → R2 (f x) (f y)) → Sorted R1 l → Sorted R2 (f <$> l).
  Proof. induction 2; simpl; constructor; eauto using HdRel_fmap. Qed.
  Lemma StronglySorted_fmap (R1 : relation A) (R2 : relation B) l :
    (∀ x y, R1 x y → R2 (f x) (f y)) →
    StronglySorted R1 l → StronglySorted R2 (f <$> l).
  Proof.
    induction 2; csimpl; constructor;
      rewrite ?Forall_fmap; eauto using Forall_impl.
  Qed.
End sorted.

(** ** Correctness of merge sort *)
Section merge_sort_correct.
  Context  {A} (R : relation A) `{∀ x y, Decision (R x y)} `{!Total R}.

  Lemma list_merge_cons x1 x2 l1 l2 :
    list_merge R (x1 :: l1) (x2 :: l2) =
      if decide (R x1 x2) then x1 :: list_merge R l1 (x2 :: l2)
      else x2 :: list_merge R (x1 :: l1) l2.
  Proof. done. Qed.
  Lemma HdRel_list_merge x l1 l2 :
    HdRel R x l1 → HdRel R x l2 → HdRel R x (list_merge R l1 l2).
  Proof.
    destruct 1 as [|x1 l1 IH1], 1 as [|x2 l2 IH2];
      rewrite ?list_merge_cons; simpl; repeat case_decide; auto.
  Qed.
  Lemma Sorted_list_merge l1 l2 :
    Sorted R l1 → Sorted R l2 → Sorted R (list_merge R l1 l2).
  Proof.
    intros Hl1. revert l2. induction Hl1 as [|x1 l1 IH1];
      induction 1 as [|x2 l2 IH2]; rewrite ?list_merge_cons; simpl;
      repeat case_decide;
      constructor; eauto using HdRel_list_merge, HdRel_cons, total_not.
  Qed.
  Lemma merge_Permutation l1 l2 : list_merge R l1 l2 ≡ₚ l1 ++ l2.
  Proof.
    revert l2. induction l1 as [|x1 l1 IH1]; intros l2;
      induction l2 as [|x2 l2 IH2]; rewrite ?list_merge_cons; simpl;
      repeat case_decide; auto.
    * by rewrite (right_id_L [] (++)).
    * by rewrite IH2, Permutation_middle.
  Qed.

  Local Notation stack := (list (option (list A))).
  Inductive merge_stack_Sorted : stack → Prop :=
    | merge_stack_Sorted_nil : merge_stack_Sorted []
    | merge_stack_Sorted_cons_None st :
       merge_stack_Sorted st → merge_stack_Sorted (None :: st)
    | merge_stack_Sorted_cons_Some l st :
       Sorted R l → merge_stack_Sorted st → merge_stack_Sorted (Some l :: st).
  Fixpoint merge_stack_flatten (st : stack) : list A :=
    match st with
    | [] => []
    | None :: st => merge_stack_flatten st
    | Some l :: st => l ++ merge_stack_flatten st
    end.

  Lemma Sorted_merge_list_to_stack st l :
    merge_stack_Sorted st → Sorted R l →
    merge_stack_Sorted (merge_list_to_stack R st l).
  Proof.
    intros Hst. revert l.
    induction Hst; repeat constructor; naive_solver auto using Sorted_list_merge.
  Qed.
  Lemma merge_list_to_stack_Permutation st l :
    merge_stack_flatten (merge_list_to_stack R st l) ≡ₚ
      l ++ merge_stack_flatten st.
  Proof.
    revert l. induction st as [|[l'|] st IH]; intros l; simpl; auto.
    by rewrite IH, merge_Permutation, (associative_L _), (commutative (++) l).
  Qed.
  Lemma Sorted_merge_stack st :
    merge_stack_Sorted st → Sorted R (merge_stack R st).
  Proof. induction 1; simpl; auto using Sorted_list_merge. Qed.
  Lemma merge_stack_Permutation st : merge_stack R st ≡ₚ merge_stack_flatten st.
  Proof.
    induction st as [|[] ? IH]; intros; simpl; auto.
    by rewrite merge_Permutation, IH.
  Qed.
  Lemma Sorted_merge_sort_aux st l :
    merge_stack_Sorted st → Sorted R (merge_sort_aux R st l).
  Proof.
    revert st. induction l; simpl;
      auto using Sorted_merge_stack, Sorted_merge_list_to_stack.
  Qed.
  Lemma merge_sort_aux_Permutation st l :
    merge_sort_aux R st l ≡ₚ merge_stack_flatten st ++ l.
  Proof.
    revert st. induction l as [|?? IH]; simpl; intros.
    * by rewrite (right_id_L [] (++)), merge_stack_Permutation.
    * rewrite IH, merge_list_to_stack_Permutation; simpl.
      by rewrite Permutation_middle.
  Qed.
  Lemma Sorted_merge_sort l : Sorted R (merge_sort R l).
  Proof. apply Sorted_merge_sort_aux. by constructor. Qed.
  Lemma merge_sort_Permutation l : merge_sort R l ≡ₚ l.
  Proof. unfold merge_sort. by rewrite merge_sort_aux_Permutation. Qed.
  Lemma StronglySorted_merge_sort `{!Transitive R} l :
    StronglySorted R (merge_sort R l).
  Proof. auto using Sorted_StronglySorted, Sorted_merge_sort. Qed.
End merge_sort_correct.

(** * Canonical pre and partial orders *)
(** We extend the canonical pre-order [⊆] to a partial order by defining setoid
equality as [λ X Y, X ⊆ Y ∧ Y ⊆ X]. We prove that this indeed gives rise to a
setoid. *)
Instance preorder_equiv `{SubsetEq A} : Equiv A := λ X Y, X ⊆ Y ∧ Y ⊆ X.

Section preorder.
  Context `{SubsetEq A, !PreOrder (@subseteq A _)}.

  Instance preorder_equivalence: @Equivalence A (≡).
  Proof.
    split.
    * done.
    * by intros ?? [??].
    * by intros X Y Z [??] [??]; split; transitivity Y.
  Qed.
  Global Instance: Proper ((≡) ==> (≡) ==> iff) (⊆).
  Proof.
    unfold equiv, preorder_equiv. intros X1 Y1 ? X2 Y2 ?. split; intro.
    * transitivity X1. tauto. transitivity X2; tauto.
    * transitivity Y1. tauto. transitivity Y2; tauto.
  Qed.
  Lemma subset_spec X Y : X ⊂ Y ↔ X ⊆ Y ∧ X ≢ Y.
  Proof.
    split.
    * intros [? HYX]. split. done. contradict HYX. by rewrite <-HYX.
    * intros [? HXY]. split. done. by contradict HXY.
  Qed.

  Section dec.
    Context `{∀ X Y : A, Decision (X ⊆ Y)}.
    Global Instance preorder_equiv_dec_slow (X Y : A) :
      Decision (X ≡ Y) | 100 := _.
    Lemma subseteq_inv X Y : X ⊆ Y → X ⊂ Y ∨ X ≡ Y.
    Proof. rewrite subset_spec. destruct (decide (X ≡ Y)); tauto. Qed.
    Lemma not_subset_inv X Y : X ⊄ Y → X ⊈ Y ∨ X ≡ Y.
    Proof. rewrite subset_spec. destruct (decide (X ≡ Y)); tauto. Qed.
  End dec.

  Section leibniz.
    Context `{!LeibnizEquiv A}.
    Lemma subset_spec_L X Y : X ⊂ Y ↔ X ⊆ Y ∧ X ≠ Y.
    Proof. unfold_leibniz. apply subset_spec. Qed.
    Context `{∀ X Y : A, Decision (X ⊆ Y)}.
    Lemma subseteq_inv_L X Y : X ⊆ Y → X ⊂ Y ∨ X = Y.
    Proof. unfold_leibniz. apply subseteq_inv. Qed.
    Lemma not_subset_inv_L X Y : X ⊄ Y → X ⊈ Y ∨ X = Y.
    Proof. unfold_leibniz. apply not_subset_inv. Qed.
  End leibniz.
End preorder.

Typeclasses Opaque preorder_equiv.
Hint Extern 0 (@Equivalence _ (≡)) =>
  class_apply preorder_equivalence : typeclass_instances.

(** * Partial orders *)
Section partial_order.
  Context `{SubsetEq A, !PartialOrder (@subseteq A _)}.
  Global Instance: LeibnizEquiv A.
  Proof. split. intros [??]. by apply (anti_symmetric (⊆)). by intros ->. Qed.
End partial_order.

(** * Join semi lattices *)
(** General purpose theorems on join semi lattices. *)
Section join_semi_lattice.
  Context `{Empty A, JoinSemiLattice A, !EmptySpec A}.
  Implicit Types X Y : A.
  Implicit Types Xs Ys : list A.

  Hint Resolve subseteq_empty union_subseteq_l union_subseteq_r union_least.
  Lemma union_subseteq_l_transitive X1 X2 Y : X1 ⊆ X2 → X1 ⊆ X2 ∪ Y.
  Proof. intros. transitivity X2; auto. Qed.
  Lemma union_subseteq_r_transitive X1 X2 Y : X1 ⊆ X2 → X1 ⊆ Y ∪ X2.
  Proof. intros. transitivity X2; auto. Qed.
  Hint Resolve union_subseteq_l_transitive union_subseteq_r_transitive.
  Lemma union_preserving_l X Y1 Y2 : Y1 ⊆ Y2 → X ∪ Y1 ⊆ X ∪ Y2.
  Proof. auto. Qed.
  Lemma union_preserving_r X1 X2 Y : X1 ⊆ X2 → X1 ∪ Y ⊆ X2 ∪ Y.
  Proof. auto. Qed.
  Lemma union_preserving X1 X2 Y1 Y2 : X1 ⊆ X2 → Y1 ⊆ Y2 → X1 ∪ Y1 ⊆ X2 ∪ Y2.
  Proof. auto. Qed.
  Lemma union_empty X : X ∪ ∅ ⊆ X.
  Proof. by apply union_least. Qed.
  Global Instance union_proper : Proper ((≡) ==> (≡) ==> (≡)) (∪).
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
  Proof. split; auto. Qed.
  Global Instance: Associative (≡) (∪).
  Proof. split; auto. Qed.
  Lemma subseteq_union X Y : X ⊆ Y ↔ X ∪ Y ≡ Y.
  Proof. repeat split; eauto. intros HXY. rewrite <-HXY. auto. Qed.
  Lemma subseteq_union_1 X Y : X ⊆ Y → X ∪ Y ≡ Y.
  Proof. apply subseteq_union. Qed.
  Lemma subseteq_union_2 X Y : X ∪ Y ≡ Y → X ⊆ Y.
  Proof. apply subseteq_union. Qed.
  Lemma equiv_empty X : X ⊆ ∅ → X ≡ ∅.
  Proof. split; eauto. Qed.
  Global Instance union_list_proper: Proper (Forall2 (≡) ==> (≡)) union_list.
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
    by rewrite IH, (associative _).
  Qed.
  Lemma union_list_reverse Xs : ⋃ (reverse Xs) ≡ ⋃ Xs.
  Proof.
    induction Xs as [|X Xs IH]; simpl; [done |].
    by rewrite reverse_cons, union_list_app,
      union_list_singleton, (commutative _), IH.
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
    Proof. unfold_leibniz. by rewrite empty_union_list. Qed. 
  End leibniz.

  Section dec.
    Context `{∀ X Y : A, Decision (X ⊆ Y)}.
    Lemma non_empty_union X Y : X ∪ Y ≢ ∅ ↔ X ≢ ∅ ∨ Y ≢ ∅.
    Proof. rewrite empty_union. destruct (decide (X ≡ ∅)); intuition. Qed.
    Lemma non_empty_union_list Xs : ⋃ Xs ≢ ∅ → Exists (≢ ∅) Xs.
    Proof. rewrite empty_union_list. apply (not_Forall_Exists _). Qed.
    Context `{!LeibnizEquiv A}.
    Lemma non_empty_union_L X Y : X ∪ Y ≠ ∅ ↔ X ≠ ∅ ∨ Y ≠ ∅.
    Proof. unfold_leibniz. apply non_empty_union. Qed.
    Lemma non_empty_union_list_L Xs : ⋃ Xs ≠ ∅ → Exists (≠ ∅) Xs.
    Proof. unfold_leibniz. apply non_empty_union_list. Qed.
  End dec.
End join_semi_lattice.

(** * Meet semi lattices *)
(** The dual of the above section, but now for meet semi lattices. *)
Section meet_semi_lattice.
  Context `{MeetSemiLattice A}.
  Implicit Types X Y : A.
  Implicit Types Xs Ys : list A.

  Hint Resolve intersection_subseteq_l intersection_subseteq_r
    intersection_greatest.
  Lemma intersection_subseteq_l_transitive X1 X2 Y : X1 ⊆ X2 → X1 ∩ Y ⊆ X2.
  Proof. intros. transitivity X1; auto. Qed.
  Lemma intersection_subseteq_r_transitive X1 X2 Y : X1 ⊆ X2 → Y ∩ X1 ⊆ X2.
  Proof. intros. transitivity X1; auto. Qed.
  Hint Resolve intersection_subseteq_l_transitive
    intersection_subseteq_r_transitive.
  Lemma intersection_preserving_l X Y1 Y2 : Y1 ⊆ Y2 → X ∩ Y1 ⊆ X ∩ Y2.
  Proof. auto. Qed.
  Lemma intersection_preserving_r X1 X2 Y : X1 ⊆ X2 → X1 ∩ Y ⊆ X2 ∩ Y.
  Proof. auto. Qed.
  Lemma intersection_preserving X1 X2 Y1 Y2 :
    X1 ⊆ X2 → Y1 ⊆ Y2 → X1 ∩ Y1 ⊆ X2 ∩ Y2.
  Proof. auto. Qed.
  Global Instance: Proper ((≡) ==> (≡) ==> (≡)) (∩).
  Proof.
    unfold equiv, preorder_equiv. split;
      apply intersection_preserving; simpl in *; tauto.
  Qed.
  Global Instance: Idempotent (≡) (∩).
  Proof. split; eauto. Qed.
  Global Instance: Commutative (≡) (∩).
  Proof. split; auto. Qed.
  Global Instance: Associative (≡) (∩).
  Proof. split; auto. Qed.
  Lemma subseteq_intersection X Y : X ⊆ Y ↔ X ∩ Y ≡ X.
  Proof. repeat split; eauto. intros HXY. rewrite <-HXY. auto. Qed.
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
End meet_semi_lattice.

(** * Lower bounded lattices *)
Section lattice.
  Context `{Empty A, Lattice A, !EmptySpec A}.

  Global Instance: LeftAbsorb (≡) ∅ (∩).
  Proof. split. by apply intersection_subseteq_l. by apply subseteq_empty. Qed.
  Global Instance: RightAbsorb (≡) ∅ (∩).
  Proof. intros ?. by rewrite (commutative _), (left_absorb _ _). Qed.
  Global Instance: LeftDistr (≡) (∪) (∩).
  Proof.
    intros X Y Z. split; [|apply lattice_distr].
    apply union_least.
    { apply intersection_greatest; auto using union_subseteq_l. }
    apply intersection_greatest.
    * apply union_subseteq_r_transitive, intersection_subseteq_l.
    * apply union_subseteq_r_transitive, intersection_subseteq_r.
  Qed.
  Global Instance: RightDistr (≡) (∪) (∩).
  Proof. intros X Y Z. by rewrite !(commutative _ _ Z), (left_distr _ _). Qed.
  Global Instance: LeftDistr (≡) (∩) (∪).
  Proof.
    intros X Y Z. split.
    * rewrite (left_distr (∪) (∩)).
      apply intersection_greatest.
      { apply union_subseteq_r_transitive, intersection_subseteq_l. }
      rewrite (right_distr (∪) (∩)).
      apply intersection_preserving; auto using union_subseteq_l.
    * apply intersection_greatest.
      { apply union_least; auto using intersection_subseteq_l. }
      apply union_least.
      + apply intersection_subseteq_r_transitive, union_subseteq_l.
      + apply intersection_subseteq_r_transitive, union_subseteq_r.
  Qed.
  Global Instance: RightDistr (≡) (∩) (∪).
  Proof. intros X Y Z. by rewrite !(commutative _ _ Z), (left_distr _ _). Qed.

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
End lattice.
