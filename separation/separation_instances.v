(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
From stdpp Require Export numbers.
Require Import Qcanon.
Require Export separation.
Local Open Scope Qc_scope.

#[global] Instance bool_separation_ops : SeparationOps bool := {
  sep_valid x := True;
  sep_subseteq x y := x → y;
  sep_empty := false;
  sep_disjoint x y := ¬x ∨ ¬y;
  sep_union x y := x || y;
  sep_difference x y := x && negb y;
  sep_splittable x := ¬x;
  sep_half x := x;
  sep_unmapped x := ¬x;
  sep_unshared x := x
}.
#[global] Instance bool_separation : Separation bool.
Proof.
  assert (∀ x y : bool, x ⊆ y ↔ ∃ z, y = z ∪ x ∧ z ## x).
  { intros x y. split.
    * exists (if x then false else y).
      destruct x, y; compute in *; naive_solver tauto.
    * intros ([]&->&?); destruct x; compute in *; intuition. }
  assert (∀ x, sep_unshared x ↔ sep_valid x ∧ ∀ y, x ## y → sep_unmapped y).
  { intros []; split; try by (compute; intuition).
    intros [_ Hu]; apply (Hu true); compute; intuition. }
  split; unfold Symmetric; auto 1;
    repeat match goal with |- ∀ x : bool, _ => intros [|] end;
    compute; try by intuition.
  exists true; simpl; tauto.
Qed.

#[global] Instance prod_separation_ops `{SeparationOps A, SeparationOps B} :
    SeparationOps (A * B) := {
  sep_valid x := sep_valid (x.1) ∧ sep_valid (x.2);
  sep_subseteq x y := x.1 ⊆ y.1 ∧ x.2 ⊆ y.2;
  sep_empty := (∅, ∅);
  sep_disjoint x y := x.1 ## y.1 ∧ x.2 ## y.2;
  sep_union x y := (x.1 ∪ y.1, x.2 ∪ y.2);
  sep_difference x y := (x.1 ∖ y.1, x.2 ∖ y.2);
  sep_splittable x := sep_splittable (x.1) ∧ sep_splittable (x.2);
  sep_half x := (½ (x.1), ½ (x.2));
  sep_unmapped x := sep_unmapped (x.1) ∧ sep_unmapped (x.2);
  sep_unshared x := sep_unshared (x.1) ∧ sep_unshared (x.2)
}.
#[global] Instance prod_separation `{Separation A, Separation B} : Separation (A * B).
Proof.
  split; sep_unfold.
  * destruct (sep_inhabited A) as (x&?&?), (sep_inhabited B) as (y&?&?).
    exists (x,y). naive_solver.
  * naive_solver eauto using @sep_disjoint_valid_l.
  * naive_solver eauto using @sep_union_valid.
  * naive_solver eauto using @sep_disjoint_empty_l.
  * intros [] ?; f_equal; naive_solver eauto using @sep_left_id.
  * intros ??; naive_solver.
  * intros; f_equal; naive_solver eauto using @sep_commutative'.
  * naive_solver eauto using @sep_disjoint_ll.
  * naive_solver eauto using @sep_disjoint_move_l.
  * intros; f_equal; naive_solver eauto using @sep_associative'.
  * intros [][] ??; f_equal; naive_solver eauto using @sep_positive_l'.
  * intros [][][] ???; f_equal; naive_solver eauto using @sep_cancel_l'.
  * naive_solver eauto using @sep_union_subseteq_l'.
  * naive_solver eauto using @sep_disjoint_difference'.
  * intros [][] ?; f_equal; naive_solver eauto using @sep_union_difference.
  * naive_solver eauto using @sep_splittable_union'.
  * naive_solver eauto using @sep_splittable_weaken.
  * naive_solver eauto using @sep_disjoint_half'.
  * intros [??] ?; f_equal; naive_solver eauto using @sep_union_half.
  * intros; f_equal; naive_solver eauto using @sep_union_half_distr'.
  * naive_solver auto using @sep_unmapped_valid.
  * split; by apply sep_unmapped_empty.
  * naive_solver eauto using @sep_unmapped_weaken.
  * naive_solver eauto using @sep_unmapped_union_2'.
  * intros [x y]; simpl. rewrite !sep_unshared_spec'. split.
    { intros [[??] [??]]; split_and ?; auto. intros [??] [??]; naive_solver. }
    intros [[??] Hxy]; split_and ?; auto.
    + intros z ?. apply (Hxy (z,∅)); simpl; eauto using @sep_disjoint_empty_r.
    + intros z ?. apply (Hxy (∅,z)); simpl; eauto using @sep_disjoint_empty_r.
  * naive_solver eauto using @sep_unshared_unmapped.
Qed.

#[refine, global] Instance sum_separation_ops `{SeparationOps A, SeparationOps B} :
    SeparationOps (A + B) := {
  sep_valid x :=
    match x with inl x => sep_valid x | inr x => sep_valid x ∧ x ≠ ∅ end;
  sep_subseteq x y :=
    match x, y with
    | inl x, inl y => x ⊆ y
    | inr x, inr y => x ⊆ y ∧ x ≠ ∅
    | inl x, inr y => x = ∅ ∧ sep_valid y ∧ y ≠ ∅
    | _, _ => False
    end;
  sep_empty := inl ∅;
  sep_disjoint x y :=
    match x, y with
    | inl x, inl y => x ## y
    | inr x, inr y => x ## y ∧ x ≠ ∅ ∧ y ≠ ∅
    | inl x, inr y => x = ∅ ∧ sep_valid y ∧ y ≠ ∅
    | inr x, inl y => sep_valid x ∧ x ≠ ∅ ∧ y = ∅
    end;
  sep_union x y :=
    match x, y with
    | inl x, inl y => inl (x ∪ y)
    | inr x, inr y => inr (x ∪ y)
    | inl x, inr y => inr y
    | inr x, inl y => inr x
    end;
  sep_difference x y :=
    match x, y with
    | inl x, inl y => inl (x ∖ y)
    | inr x, inr y => if decide (x = y) then inl ∅ else inr (x ∖ y)
    | inl x, inr y => inr y
    | inr x, inl y => inr x
    end;
  sep_splittable x :=
    match x with
    | inl x => sep_splittable x | inr x => sep_splittable x ∧ x ≠ ∅
    end;
  sep_half x :=
    match x with inl x => inl (½ x) | inr x => inr (½ x) end;
  sep_unmapped x :=
    match x with
    | inl x => sep_unmapped x | inr x => sep_unmapped x ∧ x ≠ ∅
    end;
  sep_unshared x :=
    match x with inl x => sep_unshared x | inr x => sep_unshared x end
}.
Proof.
  * intros []; apply _.
  * intros [] []; apply _.
  * intros [] []; apply _.
  * intros []; apply _.
  * intros []; apply _.
  * intros []; apply _.
Defined.

#[global] Instance sum_separation `{Separation A, Separation B} : Separation (A + B).
Proof.
  split; sep_unfold.
  * destruct (sep_inhabited A) as (x&?&?). eexists (inl x). naive_solver.
  * intros [] []; naive_solver
      eauto using @sep_disjoint_valid_l, @sep_empty_valid.
  * intros [] []; naive_solver eauto using @sep_union_valid, @sep_positive_l'.
  * intros []; naive_solver eauto using @sep_disjoint_empty_l.
  * intros [] ?; f_equal; naive_solver eauto using @sep_left_id.
  * intros [] []; naive_solver.
  * intros [] [] ?; f_equal; naive_solver eauto using @sep_commutative'.
  * intros [] [] []; naive_solver
      eauto using @sep_disjoint_ll, @sep_positive_l',
      @sep_disjoint_empty_l, @sep_empty_valid, @sep_disjoint_valid_l.
  * intros [] [] []; naive_solver
      eauto using @sep_disjoint_move_l, @sep_positive_l', @sep_disjoint_lr,
      @sep_left_id, @sep_empty_valid, @sep_union_valid.
  * intros [] [] [] ??; f_equal; naive_solver eauto using @sep_associative'.
  * intros [][] ??; f_equal; naive_solver eauto using @sep_positive_l'.
  * intros [][][] ???; f_equal;
      naive_solver eauto using @sep_cancel_l', @sep_cancel_empty_r.
  * intros [] []; naive_solver
      eauto using @sep_union_subseteq_l', @sep_reflexive.
  * intros [] [] ?; repeat case_decide; naive_solver
      eauto using @sep_disjoint_difference', @sep_subseteq_valid_l,
      @sep_difference_empty_rev, eq_sym.
  * intros [] [] ?; repeat case_decide; f_equal;
      naive_solver eauto using @sep_union_difference.
  * intros []; naive_solver
      eauto using @sep_splittable_union', @sep_positive_l'.
  * intros [] []; naive_solver
      eauto using @sep_splittable_weaken, @sep_splittable_empty.
  * intros []; naive_solver
      eauto using @sep_disjoint_half', @sep_half_empty_rev.
  * intros [] ?; f_equal; naive_solver eauto using @sep_union_half.
  * intros [] [] ??; f_equal; naive_solver eauto using @sep_union_half_distr'.
  * intros []; naive_solver auto using @sep_unmapped_valid.
  * by apply sep_unmapped_empty.
  * intros [] []; naive_solver
      eauto using @sep_unmapped_weaken, @sep_unmapped_empty.
  * intros [] []; naive_solver
      eauto using @sep_unmapped_union_2', @sep_positive_l'.
  * intros [x|x].
    { split.
      + intros ?; split; auto using @sep_unshared_valid.
        intros [y|y]; eauto using @sep_disjoint_unshared_unmapped.
        by intros [-> ?]; destruct (@sep_unshared_empty A _ _).
      + rewrite !sep_unshared_spec'; intros [? Hx]; split; intros; auto.
        by apply (Hx (inl y)). }
    split.
    + intros ?; split; auto using @sep_unshared_valid, @sep_unshared_ne_empty.
      intros []; naive_solver
        eauto using @sep_unmapped_empty, @sep_disjoint_unshared_unmapped.
    + rewrite !sep_unshared_spec'; intros [[] Hx]; split_and ?; auto; intros y ?.
      destruct (decide (y = ∅)) as [->|?]; auto using sep_unmapped_empty.
      by apply (Hx (inr y)).
  * intros []; naive_solver eauto using (@sep_unshared_unmapped A _),
      (@sep_unshared_unmapped B _).
Qed.

#[global] Instance Qc_ops: SeparationOps Qc := {
  sep_valid x := 0 ≤ x ≤ 1;
  sep_empty := 0;
  sep_disjoint x y := 0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ 1;
  sep_union x y := x + y;
  sep_subseteq x y := 0 ≤ x ≤ y ≤ 1;
  sep_difference x y := x + -y;
  sep_splittable x := 0 ≤ x ≤ 1;
  sep_half x := x * /2;
  sep_unmapped x := x = 0;
  sep_unshared x := x = 1
}.

#[global] Instance Qc_separation: Separation Qc.
Proof.
  split; sep_unfold.
  * by exists 1.
  * intros x y (?&?&?). split; [done|]. rewrite <-(Qcplus_0_r x).
    transitivity (x + y). by apply Qcplus_le_mono_l. done.
  * intros ?? (?&?&?). auto using Qcplus_nonneg_nonneg.
  * intros ? [??]. by rewrite ?Qcplus_0_l.
  * intros. by rewrite Qcplus_0_l.
  * intros x y (?&?&?). by rewrite ?(Qcplus_comm y).
  * intros ???. by rewrite Qcplus_comm.
  * intros x y z (?&?&?) (?&?&?). split_and ?; auto. rewrite <-(Qcplus_0_r x).
    transitivity (x + y + z); auto. by apply Qcplus_le_mono_r, Qcplus_le_mono_l.
  * intros x y z (?&?&?) (?&?&?). rewrite Qcplus_assoc.
    auto using Qcplus_nonneg_nonneg.
  * intros. by rewrite Qcplus_assoc.
  * intros x y (?&?&?) Hxy.  apply (anti_symm (≤)); [|done].
    apply (Qcplus_le_mono_r _ _ y). by rewrite Hxy, Qcplus_0_l.
  * intros ??? _ _. by apply (inj (Qcplus z)).
  * intros x y (?&?&?). split_and ?; auto.
    transitivity (x + 0); [by rewrite Qcplus_0_r|]. by apply Qcplus_le_mono_l.
  * intros x y (?&?&?). split_and ?; auto; [by rewrite <-Qcle_minus_iff|].
    by ring_simplify.
  * intros. ring.
  * intros x (?&?&?). split. by apply Qcplus_nonneg_nonneg. done.
  * intros x y [??] (?&?&?). split; [done|]. by transitivity y.
  * intros x [??]. assert (0 ≤ x * /2).
    { rewrite <-(Qcmult_0_l (/2)). by apply Qcmult_le_mono_nonneg_r. }
    split_and ?; auto. replace (x * /2 + x * /2) with (x * (2 * /2)) by ring.
    by rewrite Qcmult_inv_r, Qcmult_1_r by done.
  * intros x _. replace (x * /2 + x * /2) with (x * (2 * /2)) by ring.
    by rewrite Qcmult_inv_r, Qcmult_1_r by done.
  * intros x y _ _. ring.
  * by intros ? ->.
  * done.
  * intros ?? -> (?&?&?). by apply (anti_symm (≤) x 0).
  * by intros ?? _ -> ->.
  * intros x; split.
    { intros ->. split_and ?; auto. intros y (?&?&?).
      apply (anti_symm (≤)); auto. by apply (Qcplus_le_mono_l _ _ 1). }
    intros [[??] Hx]. apply (inj Qcopp), (inj (Qcplus 1)), Hx.
    split_and ?; auto; [|by ring_simplify].
    by apply (Qcplus_le_mono_l (-1) (-x) 1), Qcopp_le_compat.
  * by intros x ->.
Qed.

Record counter (A : sType) : sType :=
  Counter { counter_count : Qc ; counter_perm : A }.
Add Printing Constructor counter.
Arguments Counter {_} _ _.
Arguments counter_perm {_} _.
Arguments counter_count {_} _.
Set Warnings "-notation-overridden".
Local Notation "p .1" := (counter_count p).
Local Notation "p .2" := (counter_perm p).
Set Warnings "default".
#[global] Instance: `{Inj2 (=) (=) (=) (@Counter A)}.
Proof. by injection 1. Qed.
Lemma counter_injective_projections {A} (x y : counter A) :
  x.1 = y.1 → x.2 = y.2 → x = y.
Proof. by destruct x, y; simpl; intros -> ->. Qed.

#[refine, global] Instance counter_ops `{SeparationOps A}: SeparationOps (counter A) := {
  sep_valid x :=
    sep_valid (x.2)
    ∧ (sep_unmapped (x.2) → x.1 ≤ 0) ∧ (sep_unshared (x.2) → 0 ≤ x.1);
  sep_empty := Counter 0 ∅;
  sep_disjoint x y :=
    x.2 ## y.2
    ∧ (sep_unmapped (x.2) → x.1 ≤ 0) ∧ (sep_unmapped (y.2) → y.1 ≤ 0)
    ∧ (sep_unshared (x.2 ∪ y.2) → 0 ≤ x.1 + y.1);
  sep_union x y := Counter (x.1 + y.1) (x.2 ∪ y.2);
  sep_subseteq x y :=
    x.2 ⊆ y.2
    ∧ (sep_unmapped (y.2 ∖ x.2) → y.1 ≤ x.1)
    ∧ (sep_unmapped (x.2) → x.1 ≤ 0) ∧ (sep_unshared (y.2) → 0 ≤ y.1);
  sep_difference x y := Counter (x.1 - y.1) (x.2 ∖ y.2);
  sep_splittable x :=
    sep_splittable (x.2)
    ∧ (sep_unmapped (x.2) → x.1 ≤ 0) ∧ (sep_unshared (x.2) → 0 ≤ x.1);
  sep_half x := Counter (x.1 * /2) (½ (x.2));
  sep_unmapped x := sep_unmapped (x.2) ∧ x.1 ≤ 0;
  sep_unshared x := sep_unshared (x.2) ∧ 0 ≤ x.1
}.
Proof. solve_decision. Defined.

#[global] Instance counter_separation `{Separation A} : Separation (counter A).
Proof.
  split.
  * destruct (sep_inhabited A) as (x&?&?). exists (Counter 0 x).
    sep_unfold; naive_solver.
  * intros x y (Hxy&Hx&Hy&Hxy').
    repeat split; eauto using sep_disjoint_valid_l. intros Hx'.
    rewrite <-(Qcplus_0_r (x.1)). transitivity (x.1 + y.1).
    + eauto using sep_unshared_union_l'.
    + apply Qcplus_le_mono_l, Hy; eauto using sep_disjoint_unshared_unmapped.
  * sep_unfold; intros x y (?&?&?&?); split_and ?; eauto using sep_union_valid.
    intros. apply Qcplus_nonpos_nonpos;
      naive_solver eauto using sep_unmapped_union_l', sep_unmapped_union_r'.
  * sep_unfold; intros x (?&?&?); split_and ?; eauto using sep_disjoint_empty_l.
    by rewrite sep_left_id, Qcplus_0_l by done.
  * sep_unfold; intros [??] [??]. by rewrite sep_left_id, Qcplus_0_l by done.
  * sep_unfold; intros x y (?&?&?&?); split_and ?; auto.
    by rewrite sep_commutative', Qcplus_comm by done.
  * sep_unfold; intros [??] [??] [? _].
    by rewrite sep_commutative', Qcplus_comm by done.
  * sep_unfold; intros ??? (?&?&?&?) (?&?&?&Hxyz).
    split_and ?; eauto using sep_disjoint_ll; intros.
    assert (sep_unmapped (y.2)).
    { apply sep_disjoint_unshared_unmapped with (x.2 ∪ z.2); auto.
      rewrite sep_commutative' by eauto using sep_disjoint_ll.
      by apply sep_disjoint_move_r. }
    rewrite <-(Qcplus_0_r (x.1)). transitivity (x.1 + y.1 + z.1); auto.
    { apply Hxyz. assert (x.2 ∪ z.2 ## y.2).
      { rewrite sep_commutative' by eauto using sep_disjoint_ll.
        by apply sep_disjoint_move_r. }
      rewrite sep_permute by done; eauto using sep_unshared_union_l'. }
    apply Qcplus_le_mono_r, Qcplus_le_mono_l; auto.
  * sep_unfold; intros ??? (?&?&?&?) (?&?&?&?).
    split_and ?; eauto using sep_disjoint_move_l.
    { intros. apply Qcplus_nonpos_nonpos; eauto using sep_unmapped_union_l',
        sep_unmapped_union_r', sep_disjoint_lr. }
    by rewrite sep_associative', Qcplus_assoc by
      eauto using sep_disjoint_lr, sep_disjoint_move_l.
  * sep_unfold; intros [??] [??] [??] [? _] [? _].
    by rewrite sep_associative', Qcplus_assoc by done.
  * sep_unfold; intros x y (?&?&?&?) Hxy.
    apply (inj2 _) in Hxy; destruct Hxy as [Hxy Hxy'].
    apply counter_injective_projections; simpl; [|eauto using sep_positive_l'].
    apply (anti_symm (≤)).
    { eauto using sep_unmapped_union_l',sep_unmapped_empty_alt. }
    apply (Qcplus_le_mono_r _ _ (y.1)). rewrite Qcplus_0_l, Hxy.
    eauto using sep_positive_r', sep_unmapped_empty_alt.
  * sep_unfold; intros ??? (?&?&?&?) (?&?&?&?) ?; simplify_equality.
    apply counter_injective_projections; eauto using sep_cancel_l'.
  * sep_unfold; intros x y (?&Hx&Hy&?).
    split_and ?; auto using sep_union_subseteq_l'.
    rewrite sep_union_difference_alt by done; intros.
    rewrite <-(Qcplus_0_r (x.1)) at 2; apply Qcplus_le_mono_l; auto.
  * sep_unfold; intros x y (Hxy&?&?&?). rewrite sep_union_difference by done.
    split_and ?; auto using sep_disjoint_difference'; intros.
    + replace (y.1 - x.1) with (-(x.1 - y.1)) by ring.
      apply (Qcopp_le_compat 0), (proj1 (Qcle_minus_iff _ _)); auto.
    + replace (x.1 + (y.1 - x.1)) with (y.1) by ring.
      auto.
  * sep_unfold; intros x y (?&?&?&?). apply counter_injective_projections;
      simpl; auto using sep_union_difference; ring.
  * sep_unfold; intros x (?&?&?&?); split_and ?; auto using sep_splittable_union'.
    intros. apply Qcplus_nonpos_nonpos; eauto using sep_unmapped_union_l'.
  * sep_unfold; intros x y (?&?&?) (Hxy&?&?&?).
    split_and ?; eauto using sep_splittable_weaken; intros.
    transitivity (y.1); eauto using sep_unshared_weaken,
      sep_disjoint_unshared_unmapped, sep_disjoint_difference'.
  * sep_unfold; intros x (?&?&?).
    assert (sep_unmapped (½ (x.2)) → x.1 * /2 ≤ 0).
    { intros. rewrite <-(Qcmult_0_l (/2)).
      apply Qcmult_le_mono_nonneg_r; auto using sep_unmapped_half_1. }
    split_and ?; auto using sep_disjoint_half'.
    rewrite sep_union_half by done. intros. rewrite <-Qcmult_plus_distr_l.
    apply Qcmult_nonneg_nonneg; auto using Qcplus_nonneg_nonneg.
  * sep_unfold; intros x [? _]. apply counter_injective_projections; simpl.
    + transitivity (x.1 * (2 * /2)); [ring|].
      by rewrite Qcmult_inv_r, Qcmult_1_r.
    + by apply sep_union_half.
  * sep_unfold;  intros x y [? _] [? _].
    apply counter_injective_projections; simpl; [ring|].
    by apply sep_union_half_distr'.
  * sep_unfold; intros ? (?&?); split_and ?; auto using sep_unmapped_valid.
    intros; exfalso; eauto using sep_unshared_unmapped.
  * sep_unfold. auto using sep_unmapped_empty.
  * sep_unfold; intros ?? (?&?) (?&?&?&?); eauto using sep_unmapped_weaken.
  * sep_unfold; intros ?? (?&?&?&?) (?&?) (?&?).
    split_and ?; eauto using sep_unmapped_union_2'; intros.
    apply Qcplus_nonpos_nonpos;
      eauto using sep_unmapped_union_l', sep_unmapped_union_r'.
  * sep_unfold; intros x; split.
    { intros (?&?); split_and ?; auto using sep_unshared_valid.
      { intros; exfalso; eauto using sep_unshared_unmapped. }
      intros y (?&?&?&?); eauto using sep_disjoint_unshared_unmapped. }
    intros [(?&?&?) Hx]. cut (sep_unshared (x.2)); eauto.
    rewrite sep_unshared_spec'; split; auto; intros y ?.
    apply dec_stable; intros Hy; apply Hy.
    destruct (Hx (Counter (-x.1) y)); simpl in *; [|done].
    by split_and ?; rewrite ?Qcplus_opp_r; eauto using sep_unshared_union_l'.
  * sep_unfold; intros ? [??] [??]; eauto using sep_unshared_unmapped.
Qed.

Inductive lockable (A : sType) : sType :=
  | LLocked : A → lockable A | LUnlocked : A → lockable A.
Arguments LLocked {_} _.
Arguments LUnlocked {_} _.

#[refine, global] Instance lockable_separation_ops
    `{SeparationOps A} : SeparationOps (lockable A) := {
  sep_valid x :=
    match x with
    | LLocked x => sep_unshared x | LUnlocked x => sep_valid x
    end;
  sep_empty := LUnlocked ∅;
  sep_disjoint x y :=
    match x, y with
    | LUnlocked x, LUnlocked y => x ## y
    | LLocked x, LUnlocked y => x ## y ∧ sep_unshared x ∧ sep_unmapped y
    | LUnlocked x, LLocked y => x ## y ∧ sep_unmapped x ∧ sep_unshared y
    | LLocked _, LLocked _ => False
    end;
  sep_union x y :=
    match x, y with
    | LUnlocked x, LUnlocked y => LUnlocked (x ∪ y)
    | LLocked x, LUnlocked y | LUnlocked x, LLocked y => LLocked (x ∪ y)
    | LLocked x, LLocked y => LLocked (x ∪ y)
    end;
  sep_subseteq x y :=
    match x, y with
    | LUnlocked x, LUnlocked y => x ⊆ y
    | LLocked x, LLocked y => x ⊆ y ∧ sep_unshared x
    | LUnlocked x, LLocked y => x ⊆ y ∧ sep_unmapped x ∧ sep_unshared (y ∖ x)
    | LLocked _, LUnlocked _ => False
    end;
  sep_difference x y :=
    match x, y with
    | LUnlocked x, LUnlocked y => LUnlocked (x ∖ y)
    | LLocked x, LUnlocked y => LLocked (x ∖ y)
    | (LUnlocked x | LLocked x), LLocked y => LUnlocked (x ∖ y)
    end;
  sep_splittable x :=
    match x with
    | LLocked x => False | LUnlocked x => sep_splittable x
    end;
  sep_half x :=
    match x with
    | LLocked x => LLocked x | LUnlocked x => LUnlocked (½ x)
    end;
  sep_unmapped x :=
    match x with
    | LLocked x => False | LUnlocked x => sep_unmapped x
    end;
  sep_unshared x :=
    match x with
    | LLocked x | LUnlocked x => sep_unshared x
    end
}.
Proof.
  * intros [?|?]; apply _.
  * intros [?|?] [?|?]; apply _.
  * intros [?|?] [?|?]; apply _.
  * solve_decision.
  * intros [?|?]; apply _.
  * intros [?|?]; apply _.
  * intros [?|?]; apply _.
Defined.
#[global] Instance lockable_separation `{Separation A} : Separation (lockable A).
Proof.
  split.
  * destruct (sep_inhabited A) as (x&?&?). exists (LUnlocked x).
    sep_unfold; naive_solver.
  * sep_unfold; intros [][]; naive_solver
      eauto using sep_unmapped_valid, sep_disjoint_valid_l.
  * sep_unfold; intros [][]; naive_solver eauto using
      sep_union_valid, sep_unshared_union_l', sep_unshared_union_r'.
  * sep_unfold; intros []; naive_solver auto using sep_disjoint_empty_l,
      sep_unmapped_empty, sep_unshared_valid.
  * sep_unfold; intros [] ?; f_equal;
      naive_solver auto using sep_left_id, sep_unshared_valid.
  * sep_unfold; intros [][]; naive_solver.
  * sep_unfold; intros [][] ?; f_equal;
      naive_solver eauto using sep_commutative'.
  * sep_unfold; intros [][][]; naive_solver
      eauto using sep_disjoint_ll, sep_unmapped_union_l'.
  * sep_unfold; intros [][][]; naive_solver eauto using sep_disjoint_move_l,
      sep_disjoint_lr, sep_unmapped_union_2', sep_unmapped_union_l',
      sep_unshared_union_l', sep_unshared_union_r'.
  * sep_unfold; intros [][][] ??; f_equal;
      naive_solver eauto using sep_associative'.
  * sep_unfold; intros [][] ??; f_equal;
      naive_solver eauto using sep_positive_l'.
  * sep_unfold; intros [][][] ???; f_equal;
      naive_solver eauto using sep_cancel_l'.
  * assert (∀ x y, x ## y → sep_unshared y → sep_unshared ((x ∪ y) ∖ x)).
    { intros ???. by rewrite sep_union_difference_alt. }
    sep_unfold; intros [][];
      naive_solver eauto using sep_union_subseteq_l', sep_unshared_union_r'.
  * sep_unfold; intros [][]; naive_solver eauto using
      sep_disjoint_difference', sep_disjoint_unshared_unmapped.
  * sep_unfold; intros [][] ?; f_equal;
      naive_solver eauto using sep_union_difference.
  * sep_unfold; intros []; try naive_solver auto using sep_splittable_union'.
  * sep_unfold; intros [][]; naive_solver eauto using sep_splittable_weaken.
  * sep_unfold; intros []; naive_solver auto using sep_disjoint_half'.
  * sep_unfold; intros []; naive_solver eauto using sep_union_half with f_equal.
  * sep_unfold; intros [][] ??; f_equal; by eauto using sep_union_half_distr'.
  * sep_unfold; intros []; naive_solver auto using sep_unmapped_valid.
  * sep_unfold; auto using sep_unmapped_empty.
  * sep_unfold; intros [][]; naive_solver eauto using sep_unmapped_empty,
      sep_unmapped_weaken, sep_unshared_weaken, sep_subseteq_valid_l.
  * sep_unfold; intros [][]; naive_solver eauto using
      sep_unmapped_union_2', sep_unshared_union_l', sep_unshared_union_r'.
  * sep_unfold; intros [x|x].
    { split; [intros|intros [??]; naive_solver].
      split_and ?; auto using sep_unshared_valid. intros [?|?]; naive_solver. }
    split.
    + intros ?; split_and ?; auto using sep_unshared_valid.
      intros [?|?]; naive_solver eauto using
        sep_disjoint_unshared_unmapped, sep_unshared_unmapped.
    + intros [? Hx]. rewrite sep_unshared_spec'; split; auto.
      intros y ?. by apply (Hx (LUnlocked y)).
  * sep_unfold; intros [x|x]; eauto using sep_unshared_unmapped.
Qed.

Record tagged (A : sType) {L : Type} (d : L) : sType :=
  Tagged { tagged_perm : A; tagged_tag : L }.
Add Printing Constructor tagged.
Arguments Tagged {_ _ _} _ _.
Arguments tagged_tag {_ _ _} _.
Arguments tagged_perm {_ _ _} _.
Set Warnings "-notation-overridden".
Local Notation "x .1" := (tagged_perm x).
Local Notation "x .2" := (tagged_tag x).
Set Warnings "default".
#[global] Instance: `{Inj2 (=) (=) (=) (@Tagged A L d)}.
Proof. by injection 1. Qed.

#[refine, global] Instance tagged_separation_ops {A : sType} `{d : L}
    `{∀ x y : L, Decision (x = y),
    SeparationOps A} : SeparationOps (tagged A d) := {
  sep_valid x := sep_valid (x.1) ∧ (sep_unmapped (x.1) → x.2 = d);
  sep_empty := Tagged ∅ d;
  sep_disjoint x y :=
    x.1 ## y.1 ∧ (sep_unmapped (x.1) ∨ x.2 = y.2 ∨ sep_unmapped (y.1))
    ∧ (sep_unmapped (x.1) → x.2 = d) ∧ (sep_unmapped (y.1) → y.2 = d);
  sep_union x y := Tagged (x.1 ∪ y.1) (if decide (x.2 = d) then y.2 else x.2);
  sep_subseteq x y :=
    x.1 ⊆ y.1 ∧ (x.2 = d ∧ sep_unmapped (x.1) ∨ x.2 = y.2)
    ∧ (sep_unmapped (x.1) → x.2 = d) ∧ (sep_unmapped (y.1) → y.2 = d);
  sep_difference x y :=
    let z := x.1 ∖ y.1 in Tagged z (if decide (sep_unmapped z) then d else x.2);
  sep_splittable x := sep_splittable (x.1) ∧ (sep_unmapped (x.1) → x.2 = d);
  sep_half x := Tagged (½ (x.1)) (x.2);
  sep_unmapped x := sep_unmapped (x.1) ∧ x.2 = d;
  sep_unshared x := sep_unshared (x.1)
}.
Proof. solve_decision. Defined.

#[global] Instance tagged_separation {A : sType} `{d : L}
  `{∀ x y : L, Decision (x = y), Separation A} : Separation (tagged A d).
Proof.
  split.
  * sep_unfold; destruct (sep_inhabited A) as (x&?&?).
    eexists (Tagged x d). naive_solver.
  * sep_unfold; intros [x1 c1] [x2 c2] (?&?&?&?); simpl in *.
    naive_solver eauto using sep_disjoint_valid_l.
  * sep_unfold; intros [x1 c1] [x2 c2] (?&?&?&?); simpl in *.
    rewrite sep_unmapped_union' by done.
    case_decide; naive_solver eauto using sep_union_valid.
  * sep_unfold; intros [x c] (?&?); simpl in *.
    naive_solver eauto using sep_disjoint_empty_l, sep_unmapped_empty.
  * by sep_unfold; intros [x c] (?&?); case_decide; rewrite sep_left_id.
  * sep_unfold; intros [x1 c1] [x2 c2] (?&?&?&?); naive_solver.
  * sep_unfold; intros [x1 c1] [x2 c2] (?&?&?&?); simpl in *.
    rewrite sep_commutative' by done. repeat case_decide; naive_solver.
  * sep_unfold; intros [x1 c1] [x2 c2] [x3 c3] (?&?&?&?) (?&Hx&?&?); simpl in *.
    rewrite sep_unmapped_union' in Hx by done.
    assert (x1 ## x3) by eauto using sep_disjoint_ll; case_decide; naive_solver.
  * sep_unfold; intros [x1 c1] [x2 c2] [x3 c3] (?&?&?&?) (?&Hx&_&?); simpl in *.
    assert (x1 ## x2 ∪ x3) by eauto using sep_disjoint_move_l.
    assert (x2 ## x3) by eauto using sep_disjoint_lr.
    rewrite !sep_unmapped_union' in Hx |- * by done.
    repeat case_decide; naive_solver.
  * sep_unfold; intros [x1 c1] [x2 c2] [x3 c3] (?&?&?&?) (?&?&?&?).
    rewrite sep_associative' by done. by repeat case_decide.
  * sep_unfold; intros [x1 c1] [x2 c2] (?&?&?&?) ?; simpl in *.
    case_decide; simplify_equality. by rewrite (sep_positive_l' x1 x2).
  * sep_unfold; intros [x1 c1] [x2 c2] [x3 c3] (?&?&?&?) (?&?&?&?) ?.
    simplify_equality'. assert (x1 = x2) by eauto using sep_cancel_l'.
    case_decide; naive_solver.
  * sep_unfold; intros [x1 c1] [x2 c2] (?&?&?&?); simpl in *.
    rewrite sep_unmapped_union' by done.
    repeat case_decide; naive_solver eauto using sep_union_subseteq_l'.
  * sep_unfold; intros [x1 c1] [x2 c2] (?&?&?&?); simpl in *.
    case_decide; naive_solver eauto using sep_disjoint_difference'.
  * sep_unfold; intros [x1 c1] [x2 c2] (?&?&?&?); simpl in *.
    rewrite sep_union_difference by done.
    repeat case_decide; naive_solver eauto using sep_unmapped_difference_1.
  * sep_unfold; intros [x c] (?&?&?&?); simpl in *.
    rewrite sep_unmapped_union' by done.
    repeat case_decide; naive_solver eauto using sep_splittable_union'.
  * sep_unfold; intros [x1 c1] [x2 c2] (?&?) (?&?&?&?); simpl in *.
    naive_solver eauto using sep_splittable_weaken.
  * sep_unfold; intros [x c] (?&?); simpl in *.
    rewrite !sep_unmapped_half by done.
    naive_solver eauto using sep_disjoint_half'.
  * sep_unfold; intros [x c] (?&?); simpl in *.
    rewrite sep_union_half by done. by case_decide.
  * sep_unfold; intros [x1 c1] [x2 c2] (?&?&?&?) (?&?); simpl in *.
    rewrite sep_union_half_distr' by done. by case_decide.
  * intros ? [??]; split; auto using sep_unmapped_valid.
  * split. by apply sep_unmapped_empty. done.
  * intros ?? [??] (?&?&?&?); split; eauto using sep_unmapped_weaken.
  * sep_unfold; intros ?? (?&?&?&?) [??] [??]; simpl in *;
      repeat case_decide; auto using sep_unmapped_union_2'.
  * sep_unfold; intros [x1 c1]; simpl; split.
    + intros Hx; split_and ?; eauto using sep_unshared_valid.
      { intros; exfalso; eauto using sep_unshared_unmapped. }
      intros [x2 c2]; naive_solver eauto using sep_disjoint_unshared_unmapped.
    + intros [[??] Hx]; rewrite sep_unshared_spec'; split_and ?; auto.
      intros x2 ?.
      destruct (Hx (Tagged x2 (if decide (sep_unmapped x2) then d else c1)));
        case_decide; naive_solver.
  * sep_unfold; naive_solver eauto using sep_unshared_unmapped.
Qed.
