(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file gives an implementation of fractional permissions and shows that
they are an instance of our abstract interface for permissions. A fractional
permission is a rational number [x] with [0 < x ≤ 1], where [1] means full
access, and any other value means read only access. *)

(** We implement fractional permissions using the type [Qc] of rational numbers
in canonical representation. We equip these rational numbers with a boolean
proof of being in the required interval to ensure canonicity. *)

Require Import Field Qcanon.
Require Export abstract_permissions numbers.
Local Open Scope Qc_scope.

Definition frac : Set := dsigS (λ x : Qc, 0 < x ≤ 1).

Definition frac_bounds (f : frac) : 0 < `f ≤ 1 := proj2_dsig f.
Lemma frac_lower (f : frac) : 0 < `f.
Proof. apply frac_bounds. Qed.
Lemma frac_upper (f : frac) : `f ≤ 1.
Proof. apply frac_bounds. Qed.

Program Definition frac1 : frac := dexist 1%Qc _.
Next Obligation. done. Qed.

Definition frac_gen_kind (k : pkind) (f : frac) : pkind :=
  if decide (f = frac1) then k else Read.

Program Instance frac_ops: PermissionsOps frac := {
  perm_kind := frac_gen_kind Write;
  perm_lock_ := λ _ f, f;
  perm_subseteq := λ f1 f2, `f1 ≤ `f2;
  perm_disjoint := λ f1 f2, `f1 + `f2 ≤ 1;
  perm_union := λ f1 f2,
    if decide (`f1 + `f2 ≤ 1)
    then dexist (`f1 + `f2) _
    else frac1;
  perm_difference := λ f1 f2,
    if decide (`f2 < `f1)
    then dexist (`f1 - `f2) _
    else frac1 (**i dummy *)
}.
Next Obligation.
  split; [|done]. apply Qclt_le_trans with (`f1 + 0).
  * ring_simplify. auto using frac_lower.
  * rewrite <-Qcplus_le_mono_l. auto using Qclt_le_weak, frac_lower.
Qed.
Next Obligation.
  unfold Qcminus. split.
  { by rewrite <-Qclt_minus_iff. }
  transitivity (`f1 + 0).
  * rewrite <-Qcplus_le_mono_l.
    apply (Qcopp_le_compat 0 (`f2)), Qclt_le_weak, frac_lower.
  * rewrite Qcplus_0_r. apply frac_upper.
Qed.

Lemma frac_subset_spec f1 f2 : f1 ⊂ f2 ↔ `f1 < `f2.
Proof.
  unfold subset, orders.preorder_subset, subseteq, perm_subseteq; simpl.
  rewrite <-Qclt_nge. intuition auto using Qclt_le_weak.
Qed.

Local Instance: PartialOrder (@subseteq frac _).
Proof.
  repeat split.
  * intros ?. apply Qcle_refl.
  * intros ???. apply Qcle_trans.
  * intros ????. by apply dsig_eq, Qcle_antisym.
Qed.
Local Instance: Symmetric (@disjoint frac _).
Proof.
  intros ??. unfold disjoint, perm_disjoint; simpl.
  by rewrite Qcplus_comm.
Qed.

Lemma frac_disjoint_weaken_l (f1 f1' f2 : frac) : f1 ⊥ f2 → f1' ⊆ f1 → f1' ⊥ f2.
Proof.
  unfold disjoint, perm_disjoint, subseteq, perm_subseteq; simpl.
  intros ??. transitivity (`f1 + `f2); [|done].
  by apply Qcplus_le_mono_r.
Qed.

Lemma frac_union_not_disjoint (f1 f2 : frac) : ¬f1 ⊥ f2 → f1 ∪ f2 = frac1.
Proof. intros. unfold union, perm_union; simpl. by case_decide. Qed.
Lemma frac_union_disjoint (f1 f2 : frac) :
  f1 ⊥ f2 → @proj1_sig Qc _ (f1 ∪ f2) = `f1 + `f2.
Proof. intros. unfold union, perm_union; simpl. by case_decide. Qed.

Local Instance: Commutative (=) (@union frac _).
Proof.
  intros f1 f2. apply dsig_eq.
  destruct (decide (f1 ⊥ f2)).
  * by rewrite !frac_union_disjoint, Qcplus_comm.
  * by rewrite !frac_union_not_disjoint.
Qed.

Lemma frac_disjoint_union_ll (f1 f2 f3 : frac) : f1 ∪ f2 ⊥ f3 → f1 ⊥ f3.
Proof.
  unfold union, perm_union, disjoint, perm_disjoint; simpl.
  case_decide; simpl.
  * intros. transitivity (`f1 + `f2 + `f3); [|done].
    replace (`f1 + `f3) with (0 + (`f1 + `f3)) by ring.
    replace (`f1 + `f2 + `f3) with (`f2 + (`f1 + `f3)) by ring.
    apply Qcplus_le_mono_r. auto using Qclt_le_weak, frac_lower.
  * rewrite Qcle_ngt. intros [].
    apply (Qcplus_lt_mono_l 0 (`f3) 1), frac_lower.
Qed.
Lemma frac_disjoint_union_lr (f1 f2 f3 : frac) : f1 ∪ f2 ⊥ f3 → f2 ⊥ f3.
Proof. rewrite (commutative_L (∪)). apply frac_disjoint_union_ll. Qed.
Lemma frac_disjoint_union_rl (f1 f2 f3 : frac) : f1 ⊥ f2 ∪ f3 → f1 ⊥ f2.
Proof. rewrite !(symmetry_iff (⊥) f1). apply frac_disjoint_union_ll. Qed.
Lemma frac_disjoint_union_rr (f1 f2 f3 : frac) : f1 ⊥ f2 ∪ f3 → f1 ⊥ f3.
Proof. rewrite (commutative_L (∪)). apply frac_disjoint_union_rl. Qed.

Lemma frac_disjoint_union_l (f1 f2 f3 : frac) : f1 ∪ f2 ⊥ f3 → f1 ⊥ f2.
Proof.
  intros H1. apply dec_stable.
  unfold disjoint, perm_disjoint in H1; simpl in H1.
  rewrite Qcle_ngt in H1. contradict H1.
  rewrite frac_union_not_disjoint by done.
  apply (Qcplus_lt_mono_l 0 (`f3) 1), frac_lower.
Qed.

Lemma frac_disjoint_union_move_l (f1 f2 f3 : frac) :
  f1 ∪ f2 ⊥ f3 → f1 ⊥ f2 ∪ f3.
Proof.
  intros H1. pose proof (frac_disjoint_union_l _ _ _ H1).
  unfold disjoint, perm_disjoint; simpl.
  rewrite frac_union_disjoint, Qcplus_assoc by
    (by apply frac_disjoint_union_lr with f1).
  unfold disjoint, perm_disjoint in H1; simpl in H1.
  by rewrite frac_union_disjoint in H1.
Qed.
Lemma frac_disjoint_union_move_r (f1 f2 f3 : frac) :
  f1 ⊥ f2 ∪ f3 → f1 ∪ f2 ⊥ f3.
Proof.
  intros. symmetry. rewrite (commutative_L (∪)).
  apply frac_disjoint_union_move_l. by rewrite (commutative_L (∪)).
Qed.

Lemma frac_1_max f : f ⊆ frac1.
Proof. apply frac_upper. Qed.
Lemma frac_1_max_alt f : frac1 ⊆ f → f = frac1.
Proof. intros. apply (anti_symmetric _); auto using frac_1_max. Qed.

Lemma frac_disjoint_1_l f : ¬frac1 ⊥ f.
Proof.
  unfold disjoint, perm_disjoint; simpl. intros H.
  apply (Qcle_not_lt (`f) 0); auto using frac_lower.
  by rewrite (Qcplus_le_mono_l _ _ 1).
Qed.
Lemma frac_disjoint_1_r f : ¬f ⊥ frac1.
Proof. rewrite (symmetry_iff _). by apply frac_disjoint_1_l. Qed.

Lemma frac_gen_kind_preserving k f1 f2 :
  Read ⊆ k → f1 ⊆ f2 → frac_gen_kind k f1 ⊆ frac_gen_kind k f2.
Proof.
  intro. unfold frac_gen_kind.
  pose proof frac_1_max_alt.
  repeat case_decide; try constructor; naive_solver.
Qed.
Lemma frac_fragment_gen_kind k f :
  perm_fragment f → frac_gen_kind k f = Read.
Proof.
  intros [f' ?]. unfold frac_gen_kind. case_decide; subst; [|done].
  by destruct (frac_disjoint_1_l f').
Qed.
Lemma frac_unlock_kind k f :
  k ≠ Locked → frac_gen_kind k (perm_unlock f) ≠ Locked.
Proof. unfold frac_gen_kind. by case_decide. Qed.

Local Instance: Permissions frac.
Proof.
  split.
  * apply _.
  * apply _.
  * intros. apply frac_gen_kind_preserving. constructor. done.
  * apply frac_fragment_gen_kind.
  * apply frac_disjoint_weaken_l.
  * done.
  * done.
  * intros. by apply frac_unlock_kind.
  * intros f1 f2 f3. apply dsig_eq.
    destruct (decide (f1 ⊥ f2 ∪ f3)) as [Hf|Hf].
    + rewrite !frac_union_disjoint, Qcplus_assoc; auto.
      - eapply frac_disjoint_union_rl; eauto.
      - by apply frac_disjoint_union_move_r.
      - apply frac_disjoint_union_lr with f1.
        by apply frac_disjoint_union_move_r.
    + rewrite !frac_union_not_disjoint; auto.
      contradict Hf. by apply frac_disjoint_union_move_l.
  * apply _.
  * apply frac_disjoint_union_ll.
  * apply frac_disjoint_union_move_l.
  * intros f1 f2 H1. rewrite frac_subset_spec.
    rewrite frac_union_disjoint by done.
    rewrite <-(Qcplus_0_r (`f1)) at 1.
    apply Qcplus_lt_mono_l, frac_lower.
  * intros f1 f2 f3 H1. unfold subseteq, perm_subseteq; simpl.
    destruct (decide (f3 ⊥ f2)).
    + assert (f3 ⊥ f1).
      { symmetry. by apply frac_disjoint_weaken_l with f2. }
      rewrite !frac_union_disjoint by done.
      by apply Qcplus_le_mono_l.
    + rewrite !(frac_union_not_disjoint _ f2) by done.
      destruct (decide (f3 ⊥ f1)).
      { by rewrite frac_union_disjoint. }
      by rewrite frac_union_not_disjoint.
  * intros f1 f2 f3 H1 H2 H3. unfold subseteq, perm_subseteq in *; simpl in *.
    rewrite !frac_union_disjoint in H3 by done.
    by rewrite (Qcplus_le_mono_l _ _ (`f3)).
  * intros f1 f2 H1. do 2 red. rewrite frac_subset_spec in H1.
    unfold difference, perm_difference; simpl. case_decide; simpl; [|done].
    transitivity (`f1 + (`f2 - `f1)).
    { by rewrite <-Qcplus_le_mono_r. }
    replace (`f1 + (`f2 - `f1)) with (`f2) by ring. apply frac_upper.
  * intros f1 f2 H1. rewrite frac_subset_spec in H1. apply dsig_eq.
    unfold difference, perm_difference; simpl. case_decide; simpl; [|done].
    unfold union, perm_union; simpl. case_decide; simpl. ring.
    assert (`f1 + (`f2 - `f1) ≤ 1); [|done].
    ring_simplify. apply frac_upper.
Qed.

Instance: LeftAbsorb (=) frac1 (∪).
Proof.
  intros ?. apply dsig_eq.
  rewrite frac_union_not_disjoint; eauto using frac_disjoint_1_l.
Qed.
Instance: RightAbsorb (=) frac1 (∪).
Proof. intro. rewrite (commutative_L (∪)). apply (left_absorb_L _ (∪)). Qed.

Program Instance frac_half: Half frac := λ f, dexist (`f / 2) _.
Next Obligation.
  split.
  * by apply (Qcmult_lt_compat_r 0 (`f) (/2)); auto using frac_lower.
  * apply (Qcmult_le_compat_r (`f) 2 (/2)); [|done].
    by transitivity 1; auto using frac_upper.
Qed.

Lemma frac_disjoint_half (f : frac) : f.½ ⊥ f.½.
Proof.
  change (`f * /2 + `f * /2 ≤ 1). rewrite <-Qcmult_plus_distr_r.
  replace (/2 + /2) with 1 by (by apply Qc_is_canon).
  rewrite Qcmult_1_r. apply frac_upper.
Qed.

Instance: FracPermissions frac.
Proof.
  split.
  * apply _.
  * intros. apply frac_disjoint_half.
  * intros f. apply dsig_eq.
    rewrite frac_union_disjoint by auto using frac_disjoint_half.
    simpl. unfold Qcdiv. rewrite <-Qcmult_plus_distr_r.
    replace (/2 + /2) with 1 by (by apply Qc_is_canon). ring.
Qed.
