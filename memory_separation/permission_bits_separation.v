(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export permission_bits_refine.

Section permission_bits.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types Δ : memenv K.
Implicit Types b : bit K.
Implicit Types bs : list (bit K).
Implicit Types γ : perm.
Implicit Types γs : list perm.
Implicit Types γb : pbit K.
Implicit Types γbs : list (pbit K).

Lemma pbit_disjoint_valid Γ Δ γb1 γb2 :
  γb1 ## γb2 → ✓{Γ,Δ} γb1 → sep_unmapped γb2 → ✓{Γ,Δ} γb2.
Proof.
  destruct γb1, γb2; intros (?&?&?&?) (?&?&?) [??]; repeat split;
    naive_solver eauto using sep_unmapped_valid, BIndet_valid.
Qed.
Lemma pbits_disjoint_valid Γ Δ γbs1 γbs2 :
  γbs1 ##* γbs2 → ✓{Γ,Δ}* γbs1 → Forall sep_unmapped γbs2 → ✓{Γ,Δ}* γbs2.
Proof.
  induction 1; intros; decompose_Forall_hyps; eauto using pbit_disjoint_valid.
Qed.
Lemma pbit_subseteq_valid Γ Δ γb1 γb2 : γb1 ⊆ γb2 → ✓{Γ,Δ} γb2 → ✓{Γ,Δ} γb1.
Proof.
  destruct γb1, γb2; intros (?&?&?) (?&?&?);  repeat split;
    naive_solver eauto using BIndet_valid, sep_subseteq_valid_l.
Qed.
Lemma pbits_subseteq_valid Γ Δ γbs1 γbs2 :
  γbs1 ⊆* γbs2 → ✓{Γ,Δ}* γbs2 → ✓{Γ,Δ}* γbs1.
Proof.
  induction 1; intros; decompose_Forall_hyps; eauto using pbit_subseteq_valid.
Qed.
Lemma PBit_perm_disjoint γb1 γb2 b :
  sep_unshared γb1 → γb1 ## γb2 → PBit (tagged_perm γb1) b ## γb2.
Proof.
  sep_unfold. destruct γb1, γb2; intuition; simplify_equality';
    first [ by exfalso; eauto using @sep_unshared_unmapped
          | naive_solver eauto using sep_disjoint_unshared_unmapped ].
Qed.
Lemma PBits_perm_disjoint γbs1 γbs2 bs :
  Forall sep_unshared γbs1 → length bs = length γbs1 →
  γbs1 ##* γbs2 → zip_with PBit (tagged_perm <$> γbs1) bs ##* γbs2.
Proof.
  rewrite <-Forall2_same_length. intros ? Hbs; revert γbs2.
  induction Hbs; intros; decompose_Forall_hyps; eauto using PBit_perm_disjoint.
Qed.
Lemma pbit_indetify_disjoint γb1 γb2 :
  γb1 ## γb2 → pbit_indetify γb1 ## pbit_indetify γb2.
Proof. intros (?&?&?&?); split; eauto. Qed.
Lemma pbits_indetify_disjoint γbs1 γbs2 :
  γbs1 ##* γbs2 → pbit_indetify <$> γbs1 ##* pbit_indetify <$> γbs2.
Proof. induction 1; csimpl; auto using pbit_indetify_disjoint. Qed.
Lemma pbits_indetify_union γbs1 γbs2 :
  pbit_indetify <$> γbs1 ∪* γbs2
  = (pbit_indetify <$> γbs1) ∪* (pbit_indetify <$> γbs2).
Proof. revert γbs2. by induction γbs1; intros [|??]; f_equal'. Qed.
Lemma pbit_disjoint_indetified γb1 γb2 :
  γb1 ## γb2 → pbit_indetify γb1 = γb1 → sep_unmapped γb2 →
  pbit_indetify γb2 = γb2.
Proof. destruct γb1, γb2; intros (?&?&?&?) ? [??]; naive_solver. Qed.
Lemma pbits_disjoint_indetified γbs1 γbs2 :
  γbs1 ##* γbs2 → pbit_indetify <$> γbs1 = γbs1 → Forall sep_unmapped γbs2 →
  pbit_indetify <$> γbs2 = γbs2.
Proof.
  induction 1; intros; decompose_Forall_hyps; f_equal;
    eauto using pbit_disjoint_indetified.
Qed.
Lemma pbits_perm_union γbs1 γbs2 :
  tagged_perm <$> γbs1 ∪* γbs2
  = (tagged_perm <$> γbs1) ∪* (tagged_perm <$> γbs2).
Proof. revert γbs2. induction γbs1; intros [|??]; f_equal'; auto. Qed.
Lemma PBits_disjoint γs1 γs2 bs :
  γs1 ##* γs2 →
  Forall (not ∘ sep_unmapped) γs1 → Forall (not ∘ sep_unmapped) γs2 →
  zip_with PBit γs1 bs ##* zip_with PBit γs2 bs.
Proof.
  intros Hγs. revert bs. induction Hγs; intros [|??] ??;
    decompose_Forall_hyps; constructor; sep_unfold; naive_solver.
Qed.
Lemma PBits_union γs1 γs2 (bs : list (bit K)) :
  zip_with PBit (γs1 ∪* γs2) bs = zip_with PBit γs1 bs ∪* zip_with PBit γs2 bs.
Proof.
  revert γs2 bs. unfold union at 2, sep_union at 2; simpl.
  induction γs1; intros [|??] [|??]; f_equal'; simplify_option_eq; auto.
Qed.
Lemma PBits_BIndet_union_r γs1 γs2 bs :
  zip_with PBit (γs1 ∪* γs2) bs
  = zip_with PBit γs1 bs ∪* (flip PBit BIndet <$> γs2).
Proof.
  revert γs2 bs. induction γs1; intros [|??] [|??]; f_equal'; auto.
  by unfold union at 2, sep_union at 2; simplify_option_eq.
Qed.
Lemma PBits_BIndet_disjoint γs1 γs2 :
  γs1 ##* γs2 → (flip PBit (@BIndet K) <$> γs1) ##* (flip PBit BIndet <$> γs2).
Proof. induction 1; constructor; sep_unfold; auto. Qed.
Lemma PBits_BIndet_union γs1 γs2 :
  flip PBit (@BIndet K) <$> γs1 ∪* γs2
  = (flip PBit BIndet <$> γs1) ∪* (flip PBit BIndet <$> γs2).
Proof. revert γs2. induction γs1; intros [|??]; f_equal'; eauto. Qed.
Lemma pbits_locked_union γbs1 γbs2 :
  γbs1 ##* γbs2 → pbit_locked <$> γbs1 ∪* γbs2
  = (pbit_locked <$> γbs1) ||* (pbit_locked <$> γbs2).
Proof.
  assert (∀ γ1 γ2, γ1 ## γ2 →
    perm_locked (γ1 ∪ γ2) = perm_locked γ1 || perm_locked γ2).
  { intros [[?|?]|?] [[?|?]|?]; repeat sep_unfold; naive_solver. }
  unfold pbit_locked. induction 1 as [|???? (?&?&?&?)]; f_equal'; auto.
Qed.
Lemma pbits_unlock_union_1 βs1 βs2 γbs :
  zip_with pbit_unlock_if γbs (βs1 ∪* βs2)
  = zip_with pbit_unlock_if (zip_with pbit_unlock_if γbs βs2) βs1.
Proof.
  assert (∀ γ, perm_unlock γ = perm_unlock (perm_unlock γ)).
  { by intros [[]|]. }
  revert βs1 βs2. unfold pbit_unlock_if, pbit_unlock.
  induction γbs as [|[]]; intros [|[] ?] [|[] ?]; f_equal'; auto with f_equal.
Qed.
Lemma pbit_lock_disjoint γb1 γb2 :
  Some Writable ⊆ pbit_kind γb1 → γb1 ## γb2 → pbit_lock γb1 ## γb2.
Proof.
  destruct γb1 as [γ1 b1], γb2 as [γ2 b2]; intros ? (?&?&?&?);
    split_and !; simplify_equality'; intuition auto using
    perm_lock_disjoint, perm_lock_mapped.
  destruct (perm_mapped γ1); auto. by transitivity (Some Writable).
Qed.
Lemma pbits_lock_disjoint γbs1 γbs2 :
  Forall (λ γb, Some Writable ⊆ pbit_kind γb) γbs1 →
  γbs1 ##* γbs2 → pbit_lock <$> γbs1 ##* γbs2.
Proof. induction 2; decompose_Forall_hyps; auto using pbit_lock_disjoint. Qed.
Lemma pbit_lock_union γb1 γb2 : pbit_lock (γb1 ∪ γb2) = pbit_lock γb1 ∪ γb2.
Proof. sep_unfold. destruct γb1, γb2; f_equal'; auto using perm_lock_union. Qed.
Lemma pbit_unlock_disjoint γb1 γb2 : γb1 ## γb2 → pbit_unlock γb1 ## γb2.
Proof.
  sep_unfold; destruct γb1 as [x1 b1], γb2 as [x2 b2];
    naive_solver eauto using perm_unlock_disjoint, perm_unlock_unmapped,
    perm_unlock_mapped, @sep_disjoint_valid_r.
Qed.
Lemma pbit_unlock_union γb1 γb2 :
  γb1 ## γb2 → pbit_locked γb1 → pbit_unlock (γb1 ∪ γb2) = pbit_unlock γb1 ∪ γb2.
Proof.
  sep_unfold; intros.
  destruct γb1, γb2; f_equal'; naive_solver auto using perm_unlock_union.
Qed.
Lemma pbits_unlock_disjoint γbs1 γbs2 βs :
  γbs1 ##* γbs2 → βs =.>* pbit_locked <$> γbs1 →
  zip_with pbit_unlock_if γbs1 βs ##* γbs2.
Proof.
  rewrite Forall2_fmap_r; intros Hγbs; revert βs; induction Hγbs;
    intros [|[] ?] ?; decompose_Forall_hyps; auto using pbit_unlock_disjoint.
Qed.
Lemma pbits_unlock_union γbs1 γbs2 βs :
  γbs1 ##* γbs2 → βs =.>* pbit_locked <$> γbs1 →
  zip_with pbit_unlock_if (γbs1 ∪* γbs2) βs
  = zip_with pbit_unlock_if γbs1 βs ∪* γbs2.
Proof.
  rewrite Forall2_fmap_r; intros Hγbs; revert βs; induction Hγbs;
    intros [|[] ?] ?; decompose_Forall_hyps; f_equal; auto.
  by apply pbit_unlock_union.
Qed.
Lemma pbit_disjoint_full γb1 γb2 :
  γb1 ## γb2 → tagged_perm γb1 = perm_full → γb2 = ∅.
Proof.
  assert (¬sep_unmapped perm_full) by (by intros []).
  assert (sep_unshared perm_full) by done.
  destruct γb1, γb2; intros (?&?&?&?) ?; sep_unfold; naive_solver
    eauto using perm_disjoint_full, sep_disjoint_unshared_unmapped with f_equal.
Qed.
Lemma pbits_disjoint_full γbs1 γbs2 :
  γbs1 ##* γbs2 → Forall (λ γb, tagged_perm γb = perm_full) γbs1 →
  Forall (∅ =.) γbs2.
Proof.
  induction 1; constructor; decompose_Forall_hyps;
    eauto using pbit_disjoint_full, eq_sym.
Qed.
Lemma pbits_subseteq_full γbs1 γbs2 :
  Forall (λ γb, tagged_perm γb = perm_full) γbs1 → γbs1 ⊆* γbs2 →
  Forall (λ γb, tagged_perm γb = perm_full) γbs2.
Proof.
  induction 2 as [|???? [??]]; decompose_Forall_hyps;
    constructor; eauto using perm_subseteq_full.
Qed.
Lemma pbit_tag_subseteq γb1 γb2 :
  γb1 ⊆ γb2 → ¬sep_unmapped γb1 → tagged_tag γb1 = tagged_tag γb2.
Proof. intros (?&[[??]|]&?&?); auto; by destruct 1. Qed.
Lemma pbits_tag_subseteq γbs1 γbs2 :
  γbs1 ⊆* γbs2 → Forall (not ∘ sep_unmapped) γbs1 →
  tagged_tag <$> γbs1 = tagged_tag <$> γbs2.
Proof.
  induction 1; intros; decompose_Forall_hyps;
    f_equal'; auto using pbit_tag_subseteq.
Qed.
Lemma pbit_kind_subseteq γb1 γb2 : γb1 ⊆ γb2 → pbit_kind γb1 ⊆ pbit_kind γb2.
Proof. intros [??]; eauto using perm_kind_subseteq. Qed.
Lemma pbits_kind_subseteq γbs1 γbs2 k :
  Forall (λ γb, k ⊆ pbit_kind γb) γbs1 → γbs1 ⊆* γbs2 →
  Forall (λ γb, k ⊆ pbit_kind γb) γbs2.
Proof.
  induction 2; decompose_Forall_hyps; constructor; auto.
  etransitivity; eauto using pbit_kind_subseteq.
Qed.
Lemma pbit_indetified_subseteq γb1 γb2 :
  pbit_indetify γb2 = γb2 → γb1 ⊆ γb2 → pbit_indetify γb1 = γb1.
Proof. destruct γb1, γb2; intros ? (?&?&?&?); naive_solver. Qed.
Lemma pbits_indetified_subseteq γbs1 γbs2 :
  pbit_indetify <$> γbs2 = γbs2 → γbs1 ⊆* γbs2 → pbit_indetify <$> γbs1 = γbs1.
Proof.
  induction 2; simplify_equality';
    f_equal'; eauto using pbit_indetified_subseteq.
Qed.
Lemma pbit_union_typed Γ Δ γb1 γb2 :
  ✓{Γ,Δ} γb1 → ✓{Γ,Δ} γb2 → γb1 ## γb2 → ✓{Γ,Δ} (γb1 ∪ γb2).
Proof.
  destruct γb1 as [x1 b1], γb2 as [x2 b2].
  intros (?&?&?) (?&?&?) (?&?&?&?); simplify_equality'.
  split; split_and ?; sep_unfold; simpl; [case_decide; auto|].
  split; intros; auto using sep_union_valid.
  rewrite decide_True by eauto using sep_unmapped_union_l'.
  eauto using sep_unmapped_union_r'.
Qed.
Lemma pbits_union_typed Γ Δ γbs1 γbs2 :
  ✓{Γ,Δ}* γbs1 → ✓{Γ,Δ}* γbs2 → γbs1 ##* γbs2 → ✓{Γ,Δ}* (γbs1 ∪* γbs2).
Proof. induction 3; decompose_Forall_hyps; auto using pbit_union_typed. Qed.
Lemma pbit_union_refine Γ α f Δ1 Δ2 γb1 γb2 γb1' γb2' :
  ✓ Γ → γb1 ⊑{Γ,α,f@Δ1↦Δ2} γb2 → γb1' ⊑{Γ,α,f@Δ1↦Δ2} γb2' →
  γb2 ## γb2' → γb1 ∪ γb1' ⊑{Γ,α,f@Δ1↦Δ2} γb2 ∪ γb2'.
Proof.
  destruct γb1 as [x1 b1], γb2 as [x2 b2], γb1' as [x1' b1'], γb2' as [x2' b2'].
  intros ? (?&?&[??]&_) (?&?&[??]&_) (?&?&?&?); simplify_equality'.
  split; split_and ?; sep_unfold; simpl; auto.
  * repeat case_decide;
      naive_solver eauto 2 using BIndet_refine, bit_refine_valid_r.
  * split; intros; auto using sep_union_valid.
    rewrite decide_True by eauto using sep_unmapped_union_l'.
    eauto using sep_unmapped_union_r'.
  * split; intros; auto using sep_union_valid.
    rewrite decide_True by eauto using sep_unmapped_union_l'.
    eauto using sep_unmapped_union_r'.
Qed.
Lemma pbits_union_refine Γ α f Δ1 Δ2 γbs1 γbs2 γbs1' γbs2' :
  ✓ Γ → γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 → γbs1' ⊑{Γ,α,f@Δ1↦Δ2}* γbs2' →
  γbs2 ##* γbs2' → γbs1 ∪* γbs1' ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 ∪* γbs2'.
Proof.
  intros ? Hγbs. revert γbs1' γbs2'. induction Hγbs; destruct 1; intros;
    decompose_Forall_hyps; constructor; auto using pbit_union_refine.
Qed.
End permission_bits.
