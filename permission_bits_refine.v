(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export permission_bits bits_refine.

Instance pbit_refine `{Env Ti} :
    Refine Ti (env Ti) (pbit Ti) := λ Γ α f Γm1 Γm2 xb1 xb2,
  tagged_tag xb1 ⊑{Γ,α,f@Γm1↦Γm2} tagged_tag xb2 ∧
  tagged_perm xb1 = tagged_perm xb2 ∧
  sep_valid xb1 ∧ sep_valid xb2.

Section permission_bits.
Context `{EnvSpec Ti}.
Implicit Types Γ : env Ti.
Implicit Types Γm : memenv Ti.
Implicit Types α : bool.
Implicit Types b : bit Ti.
Implicit Types bs : list (bit Ti).
Implicit Types x : perm.
Implicit Types xs : list perm.
Implicit Types xb : pbit Ti.
Implicit Types xbs : list (pbit Ti).

Lemma pbit_refine_valid_l Γ α f Γm1 Γm2 xb1 xb2 :
  ✓ Γ → xb1 ⊑{Γ,α,f@Γm1↦Γm2} xb2 → ✓{Γ,Γm1} xb1.
Proof.
  destruct xb1, xb2; intros ? (?&?&?&?); split;
    naive_solver eauto using bit_refine_valid_l.
Qed.
Lemma pbits_refine_valid_l Γ α f Γm1 Γm2 xbs1 xbs2 :
  ✓ Γ → xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 → ✓{Γ,Γm1}* xbs1.
Proof. induction 2; eauto using pbit_refine_valid_l. Qed.
Lemma pbit_refine_valid_r Γ α f Γm1 Γm2 xb1 xb2 :
  ✓ Γ → xb1 ⊑{Γ,α,f@Γm1↦Γm2} xb2 → ✓{Γ,Γm2} xb2.
Proof.
  destruct xb1, xb2; intros ? (?&?&?&?); split;
    naive_solver eauto using bit_refine_valid_r.
Qed.
Lemma pbits_refine_valid_r Γ α f Γm1 Γm2 xbs1 xbs2 :
  ✓ Γ → xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 → ✓{Γ,Γm2}* xbs2.
Proof. induction 2; eauto using pbit_refine_valid_r. Qed.
Lemma pbit_refine_id Γ α Γm xb : ✓{Γ,Γm} xb → xb ⊑{Γ,α@Γm} xb.
Proof. intros (?&?&?); repeat split; eauto using bit_refine_id. Qed.
Lemma pbits_refine_id Γ α Γm xbs : ✓{Γ,Γm}* xbs → xbs ⊑{Γ,α@Γm}* xbs.
Proof. induction 1; eauto using pbit_refine_id. Qed.
Lemma pbit_refine_compose Γ α1 α2 f1 f2 Γm1 Γm2 Γm3 xb1 xb2 xb3 :
  ✓ Γ → xb1 ⊑{Γ,α1,f1@Γm1↦Γm2} xb2 → xb2 ⊑{Γ,α2,f2@Γm2↦Γm3} xb3 →
  xb1 ⊑{Γ,α1||α2,f2 ◎ f1@Γm1↦Γm3} xb3.
Proof.
  destruct xb1, xb2, xb3; intros ? (?&?&?) (?&?&?); split;
    naive_solver eauto using bit_refine_compose.
Qed.
Lemma pbits_refine_compose Γ α1 α2 f1 f2 Γm1 Γm2 Γm3 xbs1 xbs2 xbs3 :
  ✓ Γ → xbs1 ⊑{Γ,α1,f1@Γm1↦Γm2}* xbs2 → xbs2 ⊑{Γ,α2,f2@Γm2↦Γm3}* xbs3 →
  xbs1 ⊑{Γ,α1||α2,f2 ◎ f1@Γm1↦Γm3}* xbs3.
Proof.
  intros ? Hxbs. revert xbs3. induction Hxbs; intros;
    decompose_Forall_hyps; eauto using pbit_refine_compose.
Qed.
Lemma pbit_refine_inverse Γ f Γm1 Γm2 xb1 xb2 :
  xb1 ⊑{Γ,false,f@Γm1↦Γm2} xb2 → xb2 ⊑{Γ,false,meminj_inverse f@Γm2↦Γm1} xb1.
Proof. intros (?&?&?&?); split; eauto using bit_refine_inverse. Qed.
Lemma pbits_refine_inverse Γ f Γm1 Γm2 xbs1 xbs2 :
  xbs1 ⊑{Γ,false,f@Γm1↦Γm2}* xbs2 →
  xbs2 ⊑{Γ,false,meminj_inverse f@Γm2↦Γm1}* xbs1.
Proof. induction 1; eauto using pbit_refine_inverse. Qed.
Lemma pbit_refine_weaken Γ Γ' α α' f f' Γm1 Γm2 Γm1' Γm2' xb1 xb2 :
  ✓ Γ → xb1 ⊑{Γ,α,f@Γm1↦Γm2} xb2 → Γ ⊆ Γ' → (α → α') →
  Γm1' ⊑{Γ',α',f'} Γm2' → Γm1 ⇒ₘ Γm1' →
  Γm2 ⇒ₘ Γm2' → meminj_extend f f' Γm1 Γm2 → xb1 ⊑{Γ',α',f'@Γm1'↦Γm2'} xb2.
Proof. intros ? (?&?&[]&[]); repeat split; eauto using bit_refine_weaken. Qed.
Lemma pbits_refine_perm Γ α f Γm1 Γm2 xbs1 xbs2 :
  xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 → tagged_perm <$> xbs1 = tagged_perm <$> xbs2.
Proof. induction 1 as [|???? (?&?&?&?)]; f_equal'; auto. Qed.
Lemma pbit_refine_unmapped Γ α f Γm1 Γm2 xb1 xb2 :
  sep_unmapped xb1 → xb1 ⊑{Γ,α,f@Γm1↦Γm2} xb2 → sep_unmapped xb2.
Proof. destruct xb1, xb2; intros [??] (?&?&[??]&[??]); split; naive_solver. Qed.
Lemma pbits_refine_unmapped Γ α f Γm1 Γm2 xbs1 xbs2 :
  Forall sep_unmapped xbs1 → xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 →
  Forall sep_unmapped xbs2.
Proof.
  induction 2; decompose_Forall_hyps; eauto using pbit_refine_unmapped.
Qed.
Lemma pbit_refine_mapped Γ α f Γm1 Γm2 xb1 xb2 :
  sep_unmapped xb2 → xb1 ⊑{Γ,α,f@Γm1↦Γm2} xb2 → sep_unmapped xb1.
Proof. intros [??] (?&?&[??]&[??]); split; eauto with congruence. Qed.
Lemma pbits_refine_mapped Γ α f Γm1 Γm2 xbs1 xbs2 :
  Forall sep_unmapped xbs2 → xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 →
  Forall sep_unmapped xbs1.
Proof.
  induction 2; decompose_Forall_hyps;
    eauto using pbit_refine_mapped.
Qed.
Lemma pbit_refine_unshared Γ α f Γm1 Γm2 xb1 xb2 :
  sep_unshared xb1 → xb1 ⊑{Γ,α,f@Γm1↦Γm2} xb2 → sep_unshared xb2.
Proof.
  destruct xb1, xb2. intros [??] (?&?&[??]&[??]); split;
    naive_solver eauto using sep_unshared_valid.
Qed.
Lemma pbits_refine_unshared Γ α f Γm1 Γm2 xbs1 xbs2 :
  Forall sep_unshared xbs1 →
  xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 → Forall sep_unshared xbs2.
Proof. induction 2;decompose_Forall_hyps; eauto using pbit_refine_unshared. Qed.
Lemma pbit_refine_shared Γ α f Γm1 Γm2 xb1 xb2 :
  sep_unshared xb2 → xb1 ⊑{Γ,α,f@Γm1↦Γm2} xb2 → sep_unshared xb1.
Proof.
  destruct xb1, xb2; intros [??] (?&?&[??]&[??]); split;
    naive_solver eauto using BIndet_refine_r_inv.
Qed.
Lemma pbits_refine_shared Γ α f Γm1 Γm2 xbs1 xbs2 :
  Forall sep_unshared xbs2 → xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 →
  Forall sep_unshared xbs1.
Proof. induction 2; decompose_Forall_hyps; eauto using pbit_refine_shared. Qed.
Lemma pbit_empty_refine Γ α f Γm1 Γm2 : (∅ : pbit Ti) ⊑{Γ,α,f@Γm1↦Γm2} ∅.
Proof.
  repeat split; simpl; auto using BIndet_BIndet_refine, sep_empty_valid.
Qed.
Lemma PBit_refine Γ α f Γm1 Γm2 x b1 b2 :
  sep_valid x → ¬sep_unmapped x →
  b1 ⊑{Γ,α,f@Γm1↦Γm2} b2 → PBit x b1 ⊑{Γ,α,f@Γm1↦Γm2} PBit x b2.
Proof. repeat split; naive_solver eauto using BBit_refine. Qed.
Lemma PBits_refine Γ α f Γm1 Γm2 xs bs1 bs2 :
  Forall sep_valid xs → Forall (not ∘ sep_unmapped) xs →
  bs1 ⊑{Γ,α,f@Γm1↦Γm2}* bs2 →
  zip_with PBit xs bs1 ⊑{Γ,α,f@Γm1↦Γm2}* zip_with PBit xs bs2.
Proof.
  intros Hxs Hxs' Hbs. revert xs Hxs Hxs'. induction Hbs; intros ? [|????] ?;
    decompose_Forall_hyps; eauto using PBit_refine.
Qed.
Lemma PBit_BIndet_refine Γ α f Γm1 Γm2 x :
  sep_valid x → PBit x BIndet ⊑{Γ,α,f@Γm1↦Γm2} PBit x BIndet.
Proof. repeat split; auto using BIndet_BIndet_refine. Qed.
Lemma PBits_BIndet_refine Γ α f Γm1 Γm2 xs :
  Forall sep_valid xs →
  flip PBit BIndet <$> xs ⊑{Γ,α,f@Γm1↦Γm2}* flip PBit BIndet <$> xs.
Proof. induction 1; csimpl; auto using PBit_BIndet_refine. Qed.
Lemma PBit_BIndet_refine_l Γ Γm xb :
  ✓{Γ,Γm} xb → PBit (tagged_perm xb) BIndet ⊑{Γ,true@Γm} xb.
Proof.
  intros (?&?&?); repeat split; naive_solver eauto using BIndet_refine.
Qed.
Lemma PBits_BIndet_refine_l Γ Γm xbs :
  ✓{Γ,Γm}* xbs → flip PBit BIndet <$> tagged_perm <$> xbs ⊑{Γ,true@Γm}* xbs.
Proof. induction 1; csimpl; eauto using PBit_BIndet_refine_l. Qed.
Lemma pbit_tag_refine Γ α f Γm1 Γm2 xb1 xb2 :
  xb1 ⊑{Γ,α,f@Γm1↦Γm2} xb2 → tagged_tag xb1 ⊑{Γ,α,f@Γm1↦Γm2} tagged_tag xb2.
Proof. by intros []. Qed.
Lemma pbits_tag_refine Γ α f Γm1 Γm2 xbs1 xbs2 :
  xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 →
  tagged_tag <$> xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* tagged_tag <$> xbs2.
Proof. induction 1; constructor; auto using pbit_tag_refine. Qed.
Lemma pbit_unlock_refine Γ α f Γm1 Γm2 xb1 xb2 :
  xb1 ⊑{Γ,α,f@Γm1↦Γm2} xb2 → pbit_unlock xb1 ⊑{Γ,α,f@Γm1↦Γm2} pbit_unlock xb2.
Proof.
  destruct xb1, xb2; intros (?&?&[??]&[??]); repeat split;
    try naive_solver eauto using perm_unlock_valid, perm_unlock_mapped.
Qed.
Lemma pbit_lock_refine Γ α f Γm1 Γm2 xb1 xb2 :
  Some Writable ⊆ pbit_kind xb1 →
  xb1 ⊑{Γ,α,f@Γm1↦Γm2} xb2 → pbit_lock xb1 ⊑{Γ,α,f@Γm1↦Γm2} pbit_lock xb2.
Proof.
  destruct xb1, xb2; intros ? (?&?&[??]&[??]); repeat split;
    try naive_solver eauto using perm_lock_mapped, perm_lock_valid.
Qed.
Lemma pbits_lock_refine Γ α f Γm1 Γm2 xbs1 xbs2 :
  Forall (λ xb, Some Writable ⊆ pbit_kind xb) xbs1 →
  xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 →
  pbit_lock <$> xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* pbit_lock <$> xbs2.
Proof. induction 2; decompose_Forall_hyps; auto using pbit_lock_refine. Qed.
Lemma pbit_indetify_refine Γ α f Γm1 Γm2 xb1 xb2 :
  xb1 ⊑{Γ,α,f@Γm1↦Γm2} xb2 →
  pbit_indetify xb1 ⊑{Γ,α,f@Γm1↦Γm2} pbit_indetify xb2.
Proof.
  destruct xb1, xb2; intros (?&?&[??]&[??]);
    repeat split; eauto using BIndet_BIndet_refine.
Qed.
Lemma pbits_indetify_refine Γ α f Γm1 Γm2 xbs1 xbs2 :
  xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 →
  pbit_indetify <$> xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* pbit_indetify <$> xbs2.
Proof. induction 1; csimpl; auto using pbit_indetify_refine. Qed.
Lemma pbit_refine_kind_rev Γ α f Γm1 Γm2 xb1 xb2 k :
  xb1 ⊑{Γ,α,f@Γm1↦Γm2} xb2 → pbit_kind xb2 = k → pbit_kind xb1 = k.
Proof. unfold pbit_kind; intros (?&?&?&?); simpl; congruence. Qed.
Lemma pbits_refine_locked Γ α f Γm1 Γm2 xbs1 xbs2 :
  xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 → pbit_locked <$> xbs1 = pbit_locked <$> xbs2.
Proof.
  unfold pbit_locked.
  induction 1 as [|???? (?&?&?)]; f_equal'; auto with f_equal.
Qed.
Lemma pbits_refine_kind_subseteq Γ α f Γm1 Γm2 k xbs1 xbs2 :
  xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 → Forall (λ xb, k ⊆ pbit_kind xb) xbs1 →
  Forall (λ xb, k ⊆ pbit_kind xb) xbs2.
Proof.
  induction 1 as [|[??] [??] ?? (?&?&?&?)]; intros;
    decompose_Forall_hyps; constructor; auto; by destruct k.
Qed.
Lemma pbits_unlock_refine Γ α f Γm1 Γm2 xbs1 xbs2 βs :
  xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 → zip_with pbit_unlock_if xbs1 βs
  ⊑{Γ,α,f@Γm1↦Γm2}* zip_with pbit_unlock_if xbs2 βs.
Proof.
  intros Hxbs; revert βs. induction Hxbs; intros [|[]?];
    constructor; simpl; auto using pbit_unlock_refine.
Qed.
End permission_bits.
