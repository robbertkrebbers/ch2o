(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export permission_bits bits_refine.

#[global] Instance pbit_refine `{Env K} :
    Refine K (env K) (pbit K) := λ Γ α f Δ1 Δ2 γb1 γb2,
  tagged_tag γb1 ⊑{Γ,α,f@Δ1↦Δ2} tagged_tag γb2 ∧
  tagged_perm γb1 = tagged_perm γb2 ∧
  sep_valid γb1 ∧ sep_valid γb2.

Section permission_bits.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types Δ : memenv K.
Implicit Types α : bool.
Implicit Types b : bit K.
Implicit Types bs : list (bit K).
Implicit Types γ : perm.
Implicit Types γs : list perm.
Implicit Types γb : pbit K.
Implicit Types γbs : list (pbit K).

Lemma pbit_refine_valid_l Γ α f Δ1 Δ2 γb1 γb2 :
  ✓ Γ → γb1 ⊑{Γ,α,f@Δ1↦Δ2} γb2 → ✓{Γ,Δ1} γb1.
Proof.
  destruct γb1, γb2; intros ? (?&?&?&?); split;
    naive_solver eauto using bit_refine_valid_l.
Qed.
Lemma pbits_refine_valid_l Γ α f Δ1 Δ2 γbs1 γbs2 :
  ✓ Γ → γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 → ✓{Γ,Δ1}* γbs1.
Proof. induction 2; eauto using pbit_refine_valid_l. Qed.
Lemma pbit_refine_valid_r Γ α f Δ1 Δ2 γb1 γb2 :
  ✓ Γ → γb1 ⊑{Γ,α,f@Δ1↦Δ2} γb2 → ✓{Γ,Δ2} γb2.
Proof.
  destruct γb1, γb2; intros ? (?&?&?&?); split;
    naive_solver eauto using bit_refine_valid_r.
Qed.
Lemma pbits_refine_valid_r Γ α f Δ1 Δ2 γbs1 γbs2 :
  ✓ Γ → γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 → ✓{Γ,Δ2}* γbs2.
Proof. induction 2; eauto using pbit_refine_valid_r. Qed.
Lemma pbit_refine_id Γ α Δ γb : ✓{Γ,Δ} γb → γb ⊑{Γ,α@Δ} γb.
Proof. intros (?&?&?); repeat split; eauto using bit_refine_id. Qed.
Lemma pbits_refine_id Γ α Δ γbs : ✓{Γ,Δ}* γbs → γbs ⊑{Γ,α@Δ}* γbs.
Proof. induction 1; eauto using pbit_refine_id. Qed.
Lemma pbit_refine_compose Γ α1 α2 f1 f2 Δ1 Δ2 Δ3 γb1 γb2 γb3 :
  ✓ Γ → γb1 ⊑{Γ,α1,f1@Δ1↦Δ2} γb2 → γb2 ⊑{Γ,α2,f2@Δ2↦Δ3} γb3 →
  γb1 ⊑{Γ,α1||α2,f2 ◎ f1@Δ1↦Δ3} γb3.
Proof.
  destruct γb1, γb2, γb3; intros ? (?&?&?) (?&?&?); split;
    naive_solver eauto using bit_refine_compose.
Qed.
Lemma pbits_refine_compose Γ α1 α2 f1 f2 Δ1 Δ2 Δ3 γbs1 γbs2 γbs3 :
  ✓ Γ → γbs1 ⊑{Γ,α1,f1@Δ1↦Δ2}* γbs2 → γbs2 ⊑{Γ,α2,f2@Δ2↦Δ3}* γbs3 →
  γbs1 ⊑{Γ,α1||α2,f2 ◎ f1@Δ1↦Δ3}* γbs3.
Proof.
  intros ? Hγbs. revert γbs3. induction Hγbs; intros;
    decompose_Forall_hyps; eauto using pbit_refine_compose.
Qed.
Lemma pbit_refine_inverse Γ f Δ1 Δ2 γb1 γb2 :
  γb1 ⊑{Γ,false,f@Δ1↦Δ2} γb2 → γb2 ⊑{Γ,false,meminj_inverse f@Δ2↦Δ1} γb1.
Proof. intros (?&?&?&?); split; eauto using bit_refine_inverse. Qed.
Lemma pbits_refine_inverse Γ f Δ1 Δ2 γbs1 γbs2 :
  γbs1 ⊑{Γ,false,f@Δ1↦Δ2}* γbs2 →
  γbs2 ⊑{Γ,false,meminj_inverse f@Δ2↦Δ1}* γbs1.
Proof. induction 1; eauto using pbit_refine_inverse. Qed.
Lemma pbit_refine_weaken Γ Γ' α α' f f' Δ1 Δ2 Δ1' Δ2' γb1 γb2 :
  ✓ Γ → γb1 ⊑{Γ,α,f@Δ1↦Δ2} γb2 → Γ ⊆ Γ' → (α → α') →
  Δ1' ⊑{Γ',α',f'} Δ2' → Δ1 ⇒ₘ Δ1' →
  Δ2 ⇒ₘ Δ2' → meminj_extend f f' Δ1 Δ2 → γb1 ⊑{Γ',α',f'@Δ1'↦Δ2'} γb2.
Proof. intros ? (?&?&[]&[]); repeat split; eauto using bit_refine_weaken. Qed.
Lemma pbits_refine_perm Γ α f Δ1 Δ2 γbs1 γbs2 :
  γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 → tagged_perm <$> γbs1 = tagged_perm <$> γbs2.
Proof. induction 1 as [|???? (?&?&?&?)]; f_equal'; auto. Qed.
Lemma pbits_refine_perm_1 Γ α f Δ1 Δ2 γ γbs1 γbs2 :
  γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 → Forall (λ γb, tagged_perm γb = γ) γbs1 →
  Forall (λ γb, tagged_perm γb = γ) γbs2.
Proof.
  induction 1 as [|[??] [??] ?? (?&?&?&?)]; intros;
    decompose_Forall_hyps; constructor; auto.
Qed.
Lemma pbit_refine_unmapped Γ α f Δ1 Δ2 γb1 γb2 :
  sep_unmapped γb1 → γb1 ⊑{Γ,α,f@Δ1↦Δ2} γb2 → sep_unmapped γb2.
Proof. destruct γb1, γb2; intros [??] (?&?&[??]&[??]); split; naive_solver. Qed.
Lemma pbits_refine_unmapped Γ α f Δ1 Δ2 γbs1 γbs2 :
  Forall sep_unmapped γbs1 → γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 →
  Forall sep_unmapped γbs2.
Proof.
  induction 2; decompose_Forall_hyps; eauto using pbit_refine_unmapped.
Qed.
Lemma pbit_refine_mapped Γ α f Δ1 Δ2 γb1 γb2 :
  sep_unmapped γb2 → γb1 ⊑{Γ,α,f@Δ1↦Δ2} γb2 → sep_unmapped γb1.
Proof. intros [??] (?&?&[??]&[??]); split; eauto with congruence. Qed.
Lemma pbits_refine_mapped Γ α f Δ1 Δ2 γbs1 γbs2 :
  Forall sep_unmapped γbs2 → γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 →
  Forall sep_unmapped γbs1.
Proof.
  induction 2; decompose_Forall_hyps;
    eauto using pbit_refine_mapped.
Qed.
Lemma pbit_refine_unshared Γ α f Δ1 Δ2 γb1 γb2 :
  sep_unshared γb1 → γb1 ⊑{Γ,α,f@Δ1↦Δ2} γb2 → sep_unshared γb2.
Proof. destruct γb1, γb2; intros ? (?&?&[??]&[??]); naive_solver. Qed.
Lemma pbits_refine_unshared Γ α f Δ1 Δ2 γbs1 γbs2 :
  Forall sep_unshared γbs1 →
  γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 → Forall sep_unshared γbs2.
Proof. induction 2;decompose_Forall_hyps; eauto using pbit_refine_unshared. Qed.
Lemma pbit_refine_shared Γ α f Δ1 Δ2 γb1 γb2 :
  sep_unshared γb2 → γb1 ⊑{Γ,α,f@Δ1↦Δ2} γb2 → sep_unshared γb1.
Proof. destruct γb1, γb2; intros ? (?&?&[??]&[??]); naive_solver. Qed.
Lemma pbits_refine_shared Γ α f Δ1 Δ2 γbs1 γbs2 :
  Forall sep_unshared γbs2 → γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 →
  Forall sep_unshared γbs1.
Proof. induction 2; decompose_Forall_hyps; eauto using pbit_refine_shared. Qed.
Lemma pbit_empty_refine Γ α f Δ1 Δ2 : (∅ : pbit K) ⊑{Γ,α,f@Δ1↦Δ2} ∅.
Proof.
  repeat split; simpl; auto using BIndet_BIndet_refine, sep_empty_valid.
Qed.
Lemma PBit_refine Γ α f Δ1 Δ2 γ b1 b2 :
  sep_valid γ → ¬sep_unmapped γ →
  b1 ⊑{Γ,α,f@Δ1↦Δ2} b2 → PBit γ b1 ⊑{Γ,α,f@Δ1↦Δ2} PBit γ b2.
Proof. repeat split; naive_solver eauto using BBit_refine. Qed.
Lemma PBits_refine Γ α f Δ1 Δ2 γs bs1 bs2 :
  Forall sep_valid γs → Forall (not ∘ sep_unmapped) γs →
  bs1 ⊑{Γ,α,f@Δ1↦Δ2}* bs2 →
  zip_with PBit γs bs1 ⊑{Γ,α,f@Δ1↦Δ2}* zip_with PBit γs bs2.
Proof.
  intros Hγs Hγs' Hbs. revert γs Hγs Hγs'. induction Hbs; intros ? [|????] ?;
    decompose_Forall_hyps; eauto using PBit_refine.
Qed.
Lemma PBit_BIndet_refine Γ α f Δ1 Δ2 γ :
  sep_valid γ → PBit γ BIndet ⊑{Γ,α,f@Δ1↦Δ2} PBit γ BIndet.
Proof. repeat split; auto using BIndet_BIndet_refine. Qed.
Lemma PBits_BIndet_refine Γ α f Δ1 Δ2 γs :
  Forall sep_valid γs →
  flip PBit BIndet <$> γs ⊑{Γ,α,f@Δ1↦Δ2}* flip PBit BIndet <$> γs.
Proof. induction 1; csimpl; auto using PBit_BIndet_refine. Qed.
Lemma PBit_BIndet_refine_l Γ Δ γb :
  ✓{Γ,Δ} γb → PBit (tagged_perm γb) BIndet ⊑{Γ,true@Δ} γb.
Proof.
  intros (?&?&?); repeat split; naive_solver eauto using BIndet_refine.
Qed.
Lemma PBits_BIndet_refine_l Γ Δ γbs :
  ✓{Γ,Δ}* γbs → flip PBit BIndet <$> (tagged_perm <$> γbs) ⊑{Γ,true@Δ}* γbs.
Proof. induction 1; csimpl; eauto using PBit_BIndet_refine_l. Qed.
Lemma pbit_tag_refine Γ α f Δ1 Δ2 γb1 γb2 :
  γb1 ⊑{Γ,α,f@Δ1↦Δ2} γb2 → tagged_tag γb1 ⊑{Γ,α,f@Δ1↦Δ2} tagged_tag γb2.
Proof. by intros []. Qed.
Lemma pbits_tag_refine Γ α f Δ1 Δ2 γbs1 γbs2 :
  γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 →
  tagged_tag <$> γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* tagged_tag <$> γbs2.
Proof. induction 1; constructor; auto using pbit_tag_refine. Qed.
Lemma pbit_unlock_refine Γ α f Δ1 Δ2 γb1 γb2 :
  γb1 ⊑{Γ,α,f@Δ1↦Δ2} γb2 → pbit_unlock γb1 ⊑{Γ,α,f@Δ1↦Δ2} pbit_unlock γb2.
Proof.
  destruct γb1, γb2; intros (?&?&[??]&[??]); repeat split;
    try naive_solver eauto using perm_unlock_valid, perm_unlock_mapped.
Qed.
Lemma pbit_lock_refine Γ α f Δ1 Δ2 γb1 γb2 :
  Some Writable ⊆ pbit_kind γb1 →
  γb1 ⊑{Γ,α,f@Δ1↦Δ2} γb2 → pbit_lock γb1 ⊑{Γ,α,f@Δ1↦Δ2} pbit_lock γb2.
Proof.
  destruct γb1, γb2; intros ? (?&?&[??]&[??]); repeat split;
    try naive_solver eauto using perm_lock_mapped, perm_lock_valid.
Qed.
Lemma pbits_lock_refine Γ α f Δ1 Δ2 γbs1 γbs2 :
  Forall (λ γb, Some Writable ⊆ pbit_kind γb) γbs1 →
  γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 →
  pbit_lock <$> γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* pbit_lock <$> γbs2.
Proof. induction 2; decompose_Forall_hyps; auto using pbit_lock_refine. Qed.
Lemma pbit_indetify_refine Γ α f Δ1 Δ2 γb1 γb2 :
  γb1 ⊑{Γ,α,f@Δ1↦Δ2} γb2 →
  pbit_indetify γb1 ⊑{Γ,α,f@Δ1↦Δ2} pbit_indetify γb2.
Proof.
  destruct γb1, γb2; intros (?&?&[??]&[??]);
    repeat split; eauto using BIndet_BIndet_refine.
Qed.
Lemma pbits_indetify_refine Γ α f Δ1 Δ2 γbs1 γbs2 :
  γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 →
  pbit_indetify <$> γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* pbit_indetify <$> γbs2.
Proof. induction 1; csimpl; auto using pbit_indetify_refine. Qed.
Lemma pbit_refine_kind_rev Γ α f Δ1 Δ2 γb1 γb2 k :
  γb1 ⊑{Γ,α,f@Δ1↦Δ2} γb2 → pbit_kind γb2 = k → pbit_kind γb1 = k.
Proof. unfold pbit_kind; intros (?&?&?&?); simpl; congruence. Qed.
Lemma pbits_refine_locked Γ α f Δ1 Δ2 γbs1 γbs2 :
  γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 → pbit_locked <$> γbs1 = pbit_locked <$> γbs2.
Proof.
  unfold pbit_locked.
  induction 1 as [|???? (?&?&?)]; f_equal'; auto with f_equal.
Qed.
Lemma pbits_refine_kind_subseteq Γ α f Δ1 Δ2 k γbs1 γbs2 :
  γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 → Forall (λ γb, k ⊆ pbit_kind γb) γbs1 →
  Forall (λ γb, k ⊆ pbit_kind γb) γbs2.
Proof.
  induction 1 as [|[??] [??] ?? (?&?&?&?)]; intros;
    decompose_Forall_hyps; constructor; auto; by destruct k.
Qed.
Lemma pbits_refine_kind_subseteq_inv Γ α f Δ1 Δ2 k γbs1 γbs2 :
  γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 → Forall (λ γb, k ⊆ pbit_kind γb) γbs2 →
  Forall (λ γb, k ⊆ pbit_kind γb) γbs1.
Proof.
  induction 1 as [|[??] [??] ?? (?&?&?&?)]; intros;
    decompose_Forall_hyps; constructor; auto; by destruct k.
Qed.
Lemma pbits_unlock_refine Γ α f Δ1 Δ2 γbs1 γbs2 βs :
  γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 → zip_with pbit_unlock_if γbs1 βs
  ⊑{Γ,α,f@Δ1↦Δ2}* zip_with pbit_unlock_if γbs2 βs.
Proof.
  intros Hγbs; revert βs. induction Hγbs; intros [|[]?];
    constructor; simpl; auto using pbit_unlock_refine.
Qed.
Lemma pbit_indetify_refine_l Γ Δ γb :
  ✓{Γ,Δ} γb → pbit_indetify γb ⊑{Γ,true@Δ} γb.
Proof. intros (?&?&?); split_and !; auto; by destruct γb; constructor. Qed.
Lemma pbits_indetify_refine_l Γ Δ γbs :
  ✓{Γ,Δ}* γbs → pbit_indetify <$> γbs ⊑{Γ,true@Δ}* γbs.
Proof. induction 1; constructor; eauto using pbit_indetify_refine_l. Qed.
Lemma pbits_mask_indetify_refine_l Γ Δ γbs βs :
  ✓{Γ,Δ}* γbs → mask pbit_indetify βs γbs ⊑{Γ,true@Δ}* γbs.
Proof.
  intros Hγbs. revert βs.
  induction Hγbs; intros [|[] ?]; simpl; constructor;
    auto using pbit_refine_id, pbits_refine_id, pbit_indetify_refine_l.
Qed.
End permission_bits.
