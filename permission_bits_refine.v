(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export permission_bits bits_refine.

Instance pbit_refine `{Env K} :
    Refine K (env K) (pbit K) := λ Γ α f Δ1 Δ2 xb1 xb2,
  tagged_tag xb1 ⊑{Γ,α,f@Δ1↦Δ2} tagged_tag xb2 ∧
  tagged_perm xb1 = tagged_perm xb2 ∧
  sep_valid xb1 ∧ sep_valid xb2.

Section permission_bits.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types Δ : memenv K.
Implicit Types α : bool.
Implicit Types b : bit K.
Implicit Types bs : list (bit K).
Implicit Types x : perm.
Implicit Types xs : list perm.
Implicit Types xb : pbit K.
Implicit Types xbs : list (pbit K).

Lemma pbit_refine_valid_l Γ α f Δ1 Δ2 xb1 xb2 :
  ✓ Γ → xb1 ⊑{Γ,α,f@Δ1↦Δ2} xb2 → ✓{Γ,Δ1} xb1.
Proof.
  destruct xb1, xb2; intros ? (?&?&?&?); split;
    naive_solver eauto using bit_refine_valid_l.
Qed.
Lemma pbits_refine_valid_l Γ α f Δ1 Δ2 xbs1 xbs2 :
  ✓ Γ → xbs1 ⊑{Γ,α,f@Δ1↦Δ2}* xbs2 → ✓{Γ,Δ1}* xbs1.
Proof. induction 2; eauto using pbit_refine_valid_l. Qed.
Lemma pbit_refine_valid_r Γ α f Δ1 Δ2 xb1 xb2 :
  ✓ Γ → xb1 ⊑{Γ,α,f@Δ1↦Δ2} xb2 → ✓{Γ,Δ2} xb2.
Proof.
  destruct xb1, xb2; intros ? (?&?&?&?); split;
    naive_solver eauto using bit_refine_valid_r.
Qed.
Lemma pbits_refine_valid_r Γ α f Δ1 Δ2 xbs1 xbs2 :
  ✓ Γ → xbs1 ⊑{Γ,α,f@Δ1↦Δ2}* xbs2 → ✓{Γ,Δ2}* xbs2.
Proof. induction 2; eauto using pbit_refine_valid_r. Qed.
Lemma pbit_refine_id Γ α Δ xb : ✓{Γ,Δ} xb → xb ⊑{Γ,α@Δ} xb.
Proof. intros (?&?&?); repeat split; eauto using bit_refine_id. Qed.
Lemma pbits_refine_id Γ α Δ xbs : ✓{Γ,Δ}* xbs → xbs ⊑{Γ,α@Δ}* xbs.
Proof. induction 1; eauto using pbit_refine_id. Qed.
Lemma pbit_refine_compose Γ α1 α2 f1 f2 Δ1 Δ2 Δ3 xb1 xb2 xb3 :
  ✓ Γ → xb1 ⊑{Γ,α1,f1@Δ1↦Δ2} xb2 → xb2 ⊑{Γ,α2,f2@Δ2↦Δ3} xb3 →
  xb1 ⊑{Γ,α1||α2,f2 ◎ f1@Δ1↦Δ3} xb3.
Proof.
  destruct xb1, xb2, xb3; intros ? (?&?&?) (?&?&?); split;
    naive_solver eauto using bit_refine_compose.
Qed.
Lemma pbits_refine_compose Γ α1 α2 f1 f2 Δ1 Δ2 Δ3 xbs1 xbs2 xbs3 :
  ✓ Γ → xbs1 ⊑{Γ,α1,f1@Δ1↦Δ2}* xbs2 → xbs2 ⊑{Γ,α2,f2@Δ2↦Δ3}* xbs3 →
  xbs1 ⊑{Γ,α1||α2,f2 ◎ f1@Δ1↦Δ3}* xbs3.
Proof.
  intros ? Hxbs. revert xbs3. induction Hxbs; intros;
    decompose_Forall_hyps; eauto using pbit_refine_compose.
Qed.
Lemma pbit_refine_inverse Γ f Δ1 Δ2 xb1 xb2 :
  xb1 ⊑{Γ,false,f@Δ1↦Δ2} xb2 → xb2 ⊑{Γ,false,meminj_inverse f@Δ2↦Δ1} xb1.
Proof. intros (?&?&?&?); split; eauto using bit_refine_inverse. Qed.
Lemma pbits_refine_inverse Γ f Δ1 Δ2 xbs1 xbs2 :
  xbs1 ⊑{Γ,false,f@Δ1↦Δ2}* xbs2 →
  xbs2 ⊑{Γ,false,meminj_inverse f@Δ2↦Δ1}* xbs1.
Proof. induction 1; eauto using pbit_refine_inverse. Qed.
Lemma pbit_refine_weaken Γ Γ' α α' f f' Δ1 Δ2 Δ1' Δ2' xb1 xb2 :
  ✓ Γ → xb1 ⊑{Γ,α,f@Δ1↦Δ2} xb2 → Γ ⊆ Γ' → (α → α') →
  Δ1' ⊑{Γ',α',f'} Δ2' → Δ1 ⇒ₘ Δ1' →
  Δ2 ⇒ₘ Δ2' → meminj_extend f f' Δ1 Δ2 → xb1 ⊑{Γ',α',f'@Δ1'↦Δ2'} xb2.
Proof. intros ? (?&?&[]&[]); repeat split; eauto using bit_refine_weaken. Qed.
Lemma pbits_refine_perm Γ α f Δ1 Δ2 xbs1 xbs2 :
  xbs1 ⊑{Γ,α,f@Δ1↦Δ2}* xbs2 → tagged_perm <$> xbs1 = tagged_perm <$> xbs2.
Proof. induction 1 as [|???? (?&?&?&?)]; f_equal'; auto. Qed.
Lemma pbits_refine_perm_1 Γ α f Δ1 Δ2 x xbs1 xbs2 :
  xbs1 ⊑{Γ,α,f@Δ1↦Δ2}* xbs2 → Forall (λ xb, tagged_perm xb = x) xbs1 →
  Forall (λ xb, tagged_perm xb = x) xbs2.
Proof.
  induction 1 as [|[??] [??] ?? (?&?&?&?)]; intros;
    decompose_Forall_hyps; constructor; auto.
Qed.
Lemma pbit_refine_unmapped Γ α f Δ1 Δ2 xb1 xb2 :
  sep_unmapped xb1 → xb1 ⊑{Γ,α,f@Δ1↦Δ2} xb2 → sep_unmapped xb2.
Proof. destruct xb1, xb2; intros [??] (?&?&[??]&[??]); split; naive_solver. Qed.
Lemma pbits_refine_unmapped Γ α f Δ1 Δ2 xbs1 xbs2 :
  Forall sep_unmapped xbs1 → xbs1 ⊑{Γ,α,f@Δ1↦Δ2}* xbs2 →
  Forall sep_unmapped xbs2.
Proof.
  induction 2; decompose_Forall_hyps; eauto using pbit_refine_unmapped.
Qed.
Lemma pbit_refine_mapped Γ α f Δ1 Δ2 xb1 xb2 :
  sep_unmapped xb2 → xb1 ⊑{Γ,α,f@Δ1↦Δ2} xb2 → sep_unmapped xb1.
Proof. intros [??] (?&?&[??]&[??]); split; eauto with congruence. Qed.
Lemma pbits_refine_mapped Γ α f Δ1 Δ2 xbs1 xbs2 :
  Forall sep_unmapped xbs2 → xbs1 ⊑{Γ,α,f@Δ1↦Δ2}* xbs2 →
  Forall sep_unmapped xbs1.
Proof.
  induction 2; decompose_Forall_hyps;
    eauto using pbit_refine_mapped.
Qed.
Lemma pbit_refine_unshared Γ α f Δ1 Δ2 xb1 xb2 :
  sep_unshared xb1 → xb1 ⊑{Γ,α,f@Δ1↦Δ2} xb2 → sep_unshared xb2.
Proof.
  destruct xb1, xb2. intros [??] (?&?&[??]&[??]); split;
    naive_solver eauto using sep_unshared_valid.
Qed.
Lemma pbits_refine_unshared Γ α f Δ1 Δ2 xbs1 xbs2 :
  Forall sep_unshared xbs1 →
  xbs1 ⊑{Γ,α,f@Δ1↦Δ2}* xbs2 → Forall sep_unshared xbs2.
Proof. induction 2;decompose_Forall_hyps; eauto using pbit_refine_unshared. Qed.
Lemma pbit_refine_shared Γ α f Δ1 Δ2 xb1 xb2 :
  sep_unshared xb2 → xb1 ⊑{Γ,α,f@Δ1↦Δ2} xb2 → sep_unshared xb1.
Proof.
  destruct xb1, xb2; intros [??] (?&?&[??]&[??]); split;
    naive_solver eauto using BIndet_refine_r_inv.
Qed.
Lemma pbits_refine_shared Γ α f Δ1 Δ2 xbs1 xbs2 :
  Forall sep_unshared xbs2 → xbs1 ⊑{Γ,α,f@Δ1↦Δ2}* xbs2 →
  Forall sep_unshared xbs1.
Proof. induction 2; decompose_Forall_hyps; eauto using pbit_refine_shared. Qed.
Lemma pbit_empty_refine Γ α f Δ1 Δ2 : (∅ : pbit K) ⊑{Γ,α,f@Δ1↦Δ2} ∅.
Proof.
  repeat split; simpl; auto using BIndet_BIndet_refine, sep_empty_valid.
Qed.
Lemma PBit_refine Γ α f Δ1 Δ2 x b1 b2 :
  sep_valid x → ¬sep_unmapped x →
  b1 ⊑{Γ,α,f@Δ1↦Δ2} b2 → PBit x b1 ⊑{Γ,α,f@Δ1↦Δ2} PBit x b2.
Proof. repeat split; naive_solver eauto using BBit_refine. Qed.
Lemma PBits_refine Γ α f Δ1 Δ2 xs bs1 bs2 :
  Forall sep_valid xs → Forall (not ∘ sep_unmapped) xs →
  bs1 ⊑{Γ,α,f@Δ1↦Δ2}* bs2 →
  zip_with PBit xs bs1 ⊑{Γ,α,f@Δ1↦Δ2}* zip_with PBit xs bs2.
Proof.
  intros Hxs Hxs' Hbs. revert xs Hxs Hxs'. induction Hbs; intros ? [|????] ?;
    decompose_Forall_hyps; eauto using PBit_refine.
Qed.
Lemma PBit_BIndet_refine Γ α f Δ1 Δ2 x :
  sep_valid x → PBit x BIndet ⊑{Γ,α,f@Δ1↦Δ2} PBit x BIndet.
Proof. repeat split; auto using BIndet_BIndet_refine. Qed.
Lemma PBits_BIndet_refine Γ α f Δ1 Δ2 xs :
  Forall sep_valid xs →
  flip PBit BIndet <$> xs ⊑{Γ,α,f@Δ1↦Δ2}* flip PBit BIndet <$> xs.
Proof. induction 1; csimpl; auto using PBit_BIndet_refine. Qed.
Lemma PBit_BIndet_refine_l Γ Δ xb :
  ✓{Γ,Δ} xb → PBit (tagged_perm xb) BIndet ⊑{Γ,true@Δ} xb.
Proof.
  intros (?&?&?); repeat split; naive_solver eauto using BIndet_refine.
Qed.
Lemma PBits_BIndet_refine_l Γ Δ xbs :
  ✓{Γ,Δ}* xbs → flip PBit BIndet <$> tagged_perm <$> xbs ⊑{Γ,true@Δ}* xbs.
Proof. induction 1; csimpl; eauto using PBit_BIndet_refine_l. Qed.
Lemma pbit_tag_refine Γ α f Δ1 Δ2 xb1 xb2 :
  xb1 ⊑{Γ,α,f@Δ1↦Δ2} xb2 → tagged_tag xb1 ⊑{Γ,α,f@Δ1↦Δ2} tagged_tag xb2.
Proof. by intros []. Qed.
Lemma pbits_tag_refine Γ α f Δ1 Δ2 xbs1 xbs2 :
  xbs1 ⊑{Γ,α,f@Δ1↦Δ2}* xbs2 →
  tagged_tag <$> xbs1 ⊑{Γ,α,f@Δ1↦Δ2}* tagged_tag <$> xbs2.
Proof. induction 1; constructor; auto using pbit_tag_refine. Qed.
Lemma pbit_unlock_refine Γ α f Δ1 Δ2 xb1 xb2 :
  xb1 ⊑{Γ,α,f@Δ1↦Δ2} xb2 → pbit_unlock xb1 ⊑{Γ,α,f@Δ1↦Δ2} pbit_unlock xb2.
Proof.
  destruct xb1, xb2; intros (?&?&[??]&[??]); repeat split;
    try naive_solver eauto using perm_unlock_valid, perm_unlock_mapped.
Qed.
Lemma pbit_lock_refine Γ α f Δ1 Δ2 xb1 xb2 :
  Some Writable ⊆ pbit_kind xb1 →
  xb1 ⊑{Γ,α,f@Δ1↦Δ2} xb2 → pbit_lock xb1 ⊑{Γ,α,f@Δ1↦Δ2} pbit_lock xb2.
Proof.
  destruct xb1, xb2; intros ? (?&?&[??]&[??]); repeat split;
    try naive_solver eauto using perm_lock_mapped, perm_lock_valid.
Qed.
Lemma pbits_lock_refine Γ α f Δ1 Δ2 xbs1 xbs2 :
  Forall (λ xb, Some Writable ⊆ pbit_kind xb) xbs1 →
  xbs1 ⊑{Γ,α,f@Δ1↦Δ2}* xbs2 →
  pbit_lock <$> xbs1 ⊑{Γ,α,f@Δ1↦Δ2}* pbit_lock <$> xbs2.
Proof. induction 2; decompose_Forall_hyps; auto using pbit_lock_refine. Qed.
Lemma pbit_indetify_refine Γ α f Δ1 Δ2 xb1 xb2 :
  xb1 ⊑{Γ,α,f@Δ1↦Δ2} xb2 →
  pbit_indetify xb1 ⊑{Γ,α,f@Δ1↦Δ2} pbit_indetify xb2.
Proof.
  destruct xb1, xb2; intros (?&?&[??]&[??]);
    repeat split; eauto using BIndet_BIndet_refine.
Qed.
Lemma pbits_indetify_refine Γ α f Δ1 Δ2 xbs1 xbs2 :
  xbs1 ⊑{Γ,α,f@Δ1↦Δ2}* xbs2 →
  pbit_indetify <$> xbs1 ⊑{Γ,α,f@Δ1↦Δ2}* pbit_indetify <$> xbs2.
Proof. induction 1; csimpl; auto using pbit_indetify_refine. Qed.
Lemma pbit_refine_kind_rev Γ α f Δ1 Δ2 xb1 xb2 k :
  xb1 ⊑{Γ,α,f@Δ1↦Δ2} xb2 → pbit_kind xb2 = k → pbit_kind xb1 = k.
Proof. unfold pbit_kind; intros (?&?&?&?); simpl; congruence. Qed.
Lemma pbits_refine_locked Γ α f Δ1 Δ2 xbs1 xbs2 :
  xbs1 ⊑{Γ,α,f@Δ1↦Δ2}* xbs2 → pbit_locked <$> xbs1 = pbit_locked <$> xbs2.
Proof.
  unfold pbit_locked.
  induction 1 as [|???? (?&?&?)]; f_equal'; auto with f_equal.
Qed.
Lemma pbits_refine_kind_subseteq Γ α f Δ1 Δ2 k xbs1 xbs2 :
  xbs1 ⊑{Γ,α,f@Δ1↦Δ2}* xbs2 → Forall (λ xb, k ⊆ pbit_kind xb) xbs1 →
  Forall (λ xb, k ⊆ pbit_kind xb) xbs2.
Proof.
  induction 1 as [|[??] [??] ?? (?&?&?&?)]; intros;
    decompose_Forall_hyps; constructor; auto; by destruct k.
Qed.
Lemma pbits_refine_kind_subseteq_inv Γ α f Δ1 Δ2 k xbs1 xbs2 :
  xbs1 ⊑{Γ,α,f@Δ1↦Δ2}* xbs2 → Forall (λ xb, k ⊆ pbit_kind xb) xbs2 →
  Forall (λ xb, k ⊆ pbit_kind xb) xbs1.
Proof.
  induction 1 as [|[??] [??] ?? (?&?&?&?)]; intros;
    decompose_Forall_hyps; constructor; auto; by destruct k.
Qed.
Lemma pbits_unlock_refine Γ α f Δ1 Δ2 xbs1 xbs2 βs :
  xbs1 ⊑{Γ,α,f@Δ1↦Δ2}* xbs2 → zip_with pbit_unlock_if xbs1 βs
  ⊑{Γ,α,f@Δ1↦Δ2}* zip_with pbit_unlock_if xbs2 βs.
Proof.
  intros Hxbs; revert βs. induction Hxbs; intros [|[]?];
    constructor; simpl; auto using pbit_unlock_refine.
Qed.
Lemma pbit_indetify_refine_l Γ Δ xb :
  ✓{Γ,Δ} xb → pbit_indetify xb ⊑{Γ,true@Δ} xb.
Proof. intros (?&?&?); split_ands'; auto. by destruct xb; constructor. Qed.
Lemma pbits_indetify_refine_l Γ Δ xbs :
  ✓{Γ,Δ}* xbs → pbit_indetify <$> xbs ⊑{Γ,true@Δ}* xbs.
Proof. induction 1; constructor; eauto using pbit_indetify_refine_l. Qed.
Lemma pbits_mask_indetify_refine_l Γ Δ xbs βs :
  ✓{Γ,Δ}* xbs → mask pbit_indetify βs xbs ⊑{Γ,true@Δ}* xbs.
Proof.
  intros Hxbs. revert βs.
  induction Hxbs; intros [|[] ?]; simpl; constructor;
    auto using pbit_refine_id, pbits_refine_id, pbit_indetify_refine_l.
Qed.
End permission_bits.
