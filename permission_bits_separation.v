(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export permission_bits_refine.

Section permission_bits.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types Δ : memenv K.
Implicit Types b : bit K.
Implicit Types bs : list (bit K).
Implicit Types x : perm.
Implicit Types xs : list perm.
Implicit Types xb : pbit K.
Implicit Types xbs : list (pbit K).

Hint Extern 0 (Separation _) => apply (_ : Separation perm).

Lemma pbit_disjoint_valid Γ Δ xb1 xb2 :
  xb1 ⊥ xb2 → ✓{Γ,Δ} xb1 → sep_unmapped xb2 → ✓{Γ,Δ} xb2.
Proof.
  destruct xb1, xb2; intros (?&?&?&?) (?&?&?) [??]; repeat split;
    naive_solver eauto using sep_unmapped_valid, BIndet_valid.
Qed.
Lemma pbits_disjoint_valid Γ Δ xbs1 xbs2 :
  xbs1 ⊥* xbs2 → ✓{Γ,Δ}* xbs1 → Forall sep_unmapped xbs2 → ✓{Γ,Δ}* xbs2.
Proof.
  induction 1; intros; decompose_Forall_hyps; eauto using pbit_disjoint_valid.
Qed.
Lemma pbit_subseteq_valid Γ Δ xb1 xb2 : xb1 ⊆ xb2 → ✓{Γ,Δ} xb2 → ✓{Γ,Δ} xb1.
Proof.
  destruct xb1, xb2; intros (?&?&?) (?&?&?);  repeat split;
    naive_solver eauto using BIndet_valid, sep_subseteq_valid_l.
Qed.
Lemma pbits_subseteq_valid Γ Δ xbs1 xbs2 :
  xbs1 ⊆* xbs2 → ✓{Γ,Δ}* xbs2 → ✓{Γ,Δ}* xbs1.
Proof.
  induction 1; intros; decompose_Forall_hyps; eauto using pbit_subseteq_valid.
Qed.
Lemma PBit_perm_disjoint xb1 xb2 b :
  sep_unshared xb1 → ¬sep_unmapped xb1 →
  xb1 ⊥ xb2 → PBit (tagged_perm xb1) b ⊥ xb2.
Proof.
  sep_unfold. destruct xb1, xb2; naive_solver eauto using sep_unshared_unmapped.
Qed.
Lemma PBits_perm_disjoint xbs1 xbs2 bs :
  Forall sep_unshared xbs1 → Forall (not ∘ sep_unmapped) xbs1 →
  length bs = length xbs1 →
  xbs1 ⊥* xbs2 → zip_with PBit (tagged_perm <$> xbs1) bs ⊥* xbs2.
Proof.
  rewrite <-Forall2_same_length. intros ?? Hbs. revert xbs2.
  induction Hbs; intros; decompose_Forall_hyps; eauto using PBit_perm_disjoint.
Qed.
Lemma pbit_indetify_disjoint xb1 xb2 :
  xb1 ⊥ xb2 → pbit_indetify xb1 ⊥ pbit_indetify xb2.
Proof. intros (?&?&?&?); split; eauto. Qed.
Lemma pbits_indetify_disjoint xbs1 xbs2 :
  xbs1 ⊥* xbs2 → pbit_indetify <$> xbs1 ⊥* pbit_indetify <$> xbs2.
Proof. induction 1; csimpl; auto using pbit_indetify_disjoint. Qed.
Lemma pbits_indetify_union xbs1 xbs2 :
  pbit_indetify <$> xbs1 ∪* xbs2
  = (pbit_indetify <$> xbs1) ∪* (pbit_indetify <$> xbs2).
Proof. revert xbs2. by induction xbs1; intros [|??]; f_equal'. Qed.
Lemma pbit_disjoint_indetified xb1 xb2 :
  xb1 ⊥ xb2 → pbit_indetify xb1 = xb1 → sep_unmapped xb2 →
  pbit_indetify xb2 = xb2.
Proof. destruct xb1, xb2; intros (?&?&?&?) ? [??]; naive_solver. Qed.
Lemma pbits_disjoint_indetified xbs1 xbs2 :
  xbs1 ⊥* xbs2 → pbit_indetify <$> xbs1 = xbs1 → Forall sep_unmapped xbs2 →
  pbit_indetify <$> xbs2 = xbs2.
Proof.
  induction 1; intros; decompose_Forall_hyps; f_equal;
    eauto using pbit_disjoint_indetified.
Qed.
Lemma pbits_perm_union xbs1 xbs2 :
  tagged_perm <$> xbs1 ∪* xbs2
  = (tagged_perm <$> xbs1) ∪* (tagged_perm <$> xbs2).
Proof. revert xbs2. induction xbs1; intros [|??]; f_equal'; auto. Qed.
Lemma PBits_disjoint xs1 xs2 bs :
  xs1 ⊥* xs2 →
  Forall (not ∘ sep_unmapped) xs1 → Forall (not ∘ sep_unmapped) xs2 →
  zip_with PBit xs1 bs ⊥* zip_with PBit xs2 bs.
Proof.
  intros Hxs. revert bs. induction Hxs; intros [|??] ??;
    decompose_Forall_hyps; constructor; sep_unfold; naive_solver.
Qed.
Lemma PBits_union xs1 xs2 (bs : list (bit K)) :
  zip_with PBit (xs1 ∪* xs2) bs = zip_with PBit xs1 bs ∪* zip_with PBit xs2 bs.
Proof.
  revert xs2 bs. unfold union at 2, sep_union at 2; simpl.
  induction xs1; intros [|??] [|??]; f_equal'; simplify_option_equality; auto.
Qed.
Lemma PBits_BIndet_union_r xs1 xs2 bs :
  zip_with PBit (xs1 ∪* xs2) bs
  = zip_with PBit xs1 bs ∪* (flip PBit BIndet <$> xs2).
Proof.
  revert xs2 bs. induction xs1; intros [|??] [|??]; f_equal'; auto.
  by unfold union at 2, sep_union at 2; simplify_option_equality.
Qed.
Lemma PBits_BIndet_disjoint xs1 xs2 :
  xs1 ⊥* xs2 → (flip PBit (@BIndet K) <$> xs1) ⊥* (flip PBit BIndet <$> xs2).
Proof. induction 1; constructor; sep_unfold; auto. Qed.
Lemma PBits_BIndet_union xs1 xs2 :
  flip PBit (@BIndet K) <$> xs1 ∪* xs2
  = (flip PBit BIndet <$> xs1) ∪* (flip PBit BIndet <$> xs2).
Proof. revert xs2. induction xs1; intros [|??]; f_equal'; eauto. Qed.
Lemma pbits_locked_union xbs1 xbs2 :
  xbs1 ⊥* xbs2 → pbit_locked <$> xbs1 ∪* xbs2
  = (pbit_locked <$> xbs1) ||* (pbit_locked <$> xbs2).
Proof.
  assert (∀ x1 x2, x1 ⊥ x2 →
    perm_locked (x1 ∪ x2) = perm_locked x1 || perm_locked x2).
  { intros [[]|] [[]|]; repeat sep_unfold; naive_solver. }
  unfold pbit_locked. induction 1 as [|???? (?&?&?&?)]; f_equal'; auto.
Qed.
Lemma pbits_unlock_union_1 βs1 βs2 xbs :
  zip_with pbit_unlock_if xbs (βs1 ∪* βs2)
  = zip_with pbit_unlock_if (zip_with pbit_unlock_if xbs βs2) βs1.
Proof.
  assert (∀ x, perm_unlock x = perm_unlock (perm_unlock x)).
  { by intros [[]|]. }
  revert βs1 βs2. unfold pbit_unlock_if, pbit_unlock.
  induction xbs as [|[]]; intros [|[] ?] [|[] ?]; f_equal'; auto with f_equal.
Qed.
Lemma pbit_lock_disjoint xb1 xb2 :
  Some Writable ⊆ pbit_kind xb1 → xb1 ⊥ xb2 → pbit_lock xb1 ⊥ xb2.
Proof.
  destruct xb1 as [x1 b1], xb2 as [x2 b2]; intros ? (?&?&?&?);
    split_ands'; simplify_equality'; intuition auto using
    perm_lock_disjoint, perm_lock_mapped.
  destruct (perm_mapped x1); auto. by transitivity (Some Writable).
Qed.
Lemma pbits_lock_disjoint xbs1 xbs2 :
  Forall (λ xb, Some Writable ⊆ pbit_kind xb) xbs1 →
  xbs1 ⊥* xbs2 → pbit_lock <$> xbs1 ⊥* xbs2.
Proof. induction 2; decompose_Forall_hyps; auto using pbit_lock_disjoint. Qed.
Lemma pbit_lock_union xb1 xb2 : pbit_lock (xb1 ∪ xb2) = pbit_lock xb1 ∪ xb2.
Proof. sep_unfold. destruct xb1, xb2; f_equal'; auto using perm_lock_union. Qed.
Lemma pbit_unlock_disjoint xb1 xb2 : xb1 ⊥ xb2 → pbit_unlock xb1 ⊥ xb2.
Proof.
  sep_unfold; destruct xb1 as [x1 b1], xb2 as [x2 b2];
    naive_solver eauto using perm_unlock_disjoint, perm_unlock_unmapped,
    perm_unlock_mapped, @sep_disjoint_valid_r.
Qed.
Lemma pbit_unlock_union xb1 xb2 :
  xb1 ⊥ xb2 → pbit_locked xb1 → pbit_unlock (xb1 ∪ xb2) = pbit_unlock xb1 ∪ xb2.
Proof.
  sep_unfold; intros.
  destruct xb1, xb2; f_equal'; naive_solver auto using perm_unlock_union.
Qed.
Lemma pbits_unlock_disjoint xbs1 xbs2 βs :
  xbs1 ⊥* xbs2 → βs =.>* pbit_locked <$> xbs1 →
  zip_with pbit_unlock_if xbs1 βs ⊥* xbs2.
Proof.
  rewrite Forall2_fmap_r; intros Hxbs; revert βs; induction Hxbs;
    intros [|[] ?] ?; decompose_Forall_hyps; auto using pbit_unlock_disjoint.
Qed.
Lemma pbits_unlock_union xbs1 xbs2 βs :
  xbs1 ⊥* xbs2 → βs =.>* pbit_locked <$> xbs1 →
  zip_with pbit_unlock_if (xbs1 ∪* xbs2) βs
  = zip_with pbit_unlock_if xbs1 βs ∪* xbs2.
Proof.
  rewrite Forall2_fmap_r; intros Hxbs; revert βs; induction Hxbs;
    intros [|[] ?] ?; decompose_Forall_hyps; f_equal; auto.
  by apply pbit_unlock_union.
Qed.
Lemma pbit_disjoint_full xb1 xb2 :
  xb1 ⊥ xb2 → tagged_perm xb1 = perm_full → xb2 = ∅.
Proof.
  assert (¬sep_unmapped perm_full) by (by intros []).
  assert (sep_unshared perm_full) by done.
  destruct xb1, xb2; intros (?&?&?&?) ?; sep_unfold; naive_solver
    eauto using perm_disjoint_full, sep_unshared_unmapped with f_equal.
Qed.
Lemma pbits_disjoint_full xbs1 xbs2 :
  xbs1 ⊥* xbs2 → Forall (λ xb, tagged_perm xb = perm_full) xbs1 →
  Forall (∅ =) xbs2.
Proof.
  induction 1; constructor; decompose_Forall_hyps;
    eauto using pbit_disjoint_full, eq_sym.
Qed.
Lemma pbit_tag_subseteq xb1 xb2 :
  xb1 ⊆ xb2 → ¬sep_unmapped xb1 → tagged_tag xb1 = tagged_tag xb2.
Proof. intros (?&[[??]|]&?&?); auto; by destruct 1. Qed.
Lemma pbits_tag_subseteq xbs1 xbs2 :
  xbs1 ⊆* xbs2 → Forall (not ∘ sep_unmapped) xbs1 →
  tagged_tag <$> xbs1 = tagged_tag <$> xbs2.
Proof.
  induction 1; intros; decompose_Forall_hyps;
    f_equal'; auto using pbit_tag_subseteq.
Qed.
Lemma pbit_kind_subseteq xb1 xb2 : xb1 ⊆ xb2 → pbit_kind xb1 ⊆ pbit_kind xb2.
Proof. intros [??]; eauto using perm_kind_subseteq. Qed.
Lemma pbits_kind_subseteq xbs1 xbs2 k :
  Forall (λ xb, k ⊆ pbit_kind xb) xbs1 → xbs1 ⊆* xbs2 →
  Forall (λ xb, k ⊆ pbit_kind xb) xbs2.
Proof.
  induction 2; decompose_Forall_hyps; constructor; auto.
  etransitivity; eauto using pbit_kind_subseteq.
Qed.
Lemma pbit_indetified_subseteq xb1 xb2 :
  pbit_indetify xb2 = xb2 → xb1 ⊆ xb2 → pbit_indetify xb1 = xb1.
Proof. destruct xb1, xb2; intros ? (?&?&?&?); naive_solver. Qed.
Lemma pbits_indetified_subseteq xbs1 xbs2 :
  pbit_indetify <$> xbs2 = xbs2 → xbs1 ⊆* xbs2 → pbit_indetify <$> xbs1 = xbs1.
Proof.
  induction 2; simplify_equality';
    f_equal'; eauto using pbit_indetified_subseteq.
Qed.
Lemma pbit_union_typed Γ Δ xb1 xb2 :
  ✓{Γ,Δ} xb1 → ✓{Γ,Δ} xb2 → xb1 ⊥ xb2 → ✓{Γ,Δ} (xb1 ∪ xb2).
Proof.
  destruct xb1 as [x1 b1], xb2 as [x2 b2].
  intros (?&?&?) (?&?&?) (?&?&?&?); simplify_equality'.
  split; split_ands; sep_unfold; simpl; [case_decide; auto|].
  split; intros; auto using sep_union_valid.
  rewrite decide_True by eauto using sep_unmapped_union_l'.
  eauto using sep_unmapped_union_r'.
Qed.
Lemma pbits_union_typed Γ Δ xbs1 xbs2 :
  ✓{Γ,Δ}* xbs1 → ✓{Γ,Δ}* xbs2 → xbs1 ⊥* xbs2 → ✓{Γ,Δ}* (xbs1 ∪* xbs2).
Proof. induction 3; decompose_Forall_hyps; auto using pbit_union_typed. Qed.
Lemma pbit_union_refine Γ α f Δ1 Δ2 xb1 xb2 xb1' xb2' :
  ✓ Γ → xb1 ⊑{Γ,α,f@Δ1↦Δ2} xb2 → xb1' ⊑{Γ,α,f@Δ1↦Δ2} xb2' →
  xb2 ⊥ xb2' → xb1 ∪ xb1' ⊑{Γ,α,f@Δ1↦Δ2} xb2 ∪ xb2'.
Proof.
  destruct xb1 as [x1 b1], xb2 as [x2 b2], xb1' as [x1' b1'], xb2' as [x2' b2'].
  intros ? (?&?&[??]&_) (?&?&[??]&_) (?&?&?&?); simplify_equality'.
  split; split_ands; sep_unfold; simpl; auto.
  * repeat case_decide;
      naive_solver eauto 2 using BIndet_refine, bit_refine_valid_r.
  * split; intros; auto using sep_union_valid.
    rewrite decide_True by eauto using sep_unmapped_union_l'.
    eauto using sep_unmapped_union_r'.
  * split; intros; auto using sep_union_valid.
    rewrite decide_True by eauto using sep_unmapped_union_l'.
    eauto using sep_unmapped_union_r'.
Qed.
Lemma pbits_union_refine Γ α f Δ1 Δ2 xbs1 xbs2 xbs1' xbs2' :
  ✓ Γ → xbs1 ⊑{Γ,α,f@Δ1↦Δ2}* xbs2 → xbs1' ⊑{Γ,α,f@Δ1↦Δ2}* xbs2' →
  xbs2 ⊥* xbs2' → xbs1 ∪* xbs1' ⊑{Γ,α,f@Δ1↦Δ2}* xbs2 ∪* xbs2'.
Proof.
  intros ? Hxbs. revert xbs1' xbs2'. induction Hxbs; destruct 1; intros;
    decompose_Forall_hyps; constructor; auto using pbit_union_refine.
Qed.
End permission_bits.
