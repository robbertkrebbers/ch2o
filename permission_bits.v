(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export permissions bits.

Notation pbit Ti := (tagged perm (@BIndet Ti)).
Notation PBit := (Tagged (d:=BIndet)).

Section operations.
  Context `{TypeOfIndex Ti M, Refine Ti M, IndexAlive M, IntEnv Ti, PtrEnv Ti,
    ∀ m x, Decision (index_alive m x)}.

  Global Instance pbit_valid :
      Valid (env Ti * option M) (pbit Ti) := λ Γmm xb,
    sep_valid (tagged_perm xb) ∧
    ✓{Γmm} (tagged_tag xb) ∧
    (sep_unmapped (tagged_perm xb) → tagged_tag xb = BIndet).

  Definition pbit_indetify (xb : pbit Ti) : pbit Ti :=
    PBit (tagged_perm xb) BIndet.
  Definition pbit_kind (xb : pbit Ti) : option pkind :=
    perm_kind (tagged_perm xb).
  Definition pbit_freed : pbit Ti := PBit perm_freed BIndet.
  Definition pbit_full (alloc : bool) : pbit Ti :=
    PBit (perm_full alloc) BIndet.
  Definition pbit_token : pbit Ti := PBit perm_token BIndet.
  Definition pbit_locked (xb : pbit Ti) : bool :=
    perm_locked (tagged_perm xb).
  Definition pbit_lock (xb : pbit Ti) : pbit Ti :=
    PBit (perm_lock (tagged_perm xb)) (tagged_tag xb).
  Definition pbit_unlock (xb : pbit Ti) : pbit Ti :=
    PBit (perm_unlock (tagged_perm xb)) (tagged_tag xb).

  Global Instance pbit_refine `{PtrEnv Ti, IntEnv Ti} :
      Refine Ti (pbit Ti) := λ Γ f xb1 xb2,
    tagged_tag xb1 ⊑{Γ,f} tagged_tag xb2 ∧
    tagged_perm xb1 = tagged_perm xb2 ∧
    sep_valid (tagged_perm xb1) ∧
    (sep_unmapped (tagged_perm xb2) → tagged_tag xb2 = BIndet).
End operations.

Section properties.
Context `{MemSpec Ti M}.
Implicit Types Γ : env Ti.
Implicit Types m : M.
Implicit Types mm : option M.
Implicit Types b : bit Ti.
Implicit Types bs : list (bit Ti).
Implicit Types x : perm.
Implicit Types xs : list perm.
Implicit Types xb : pbit Ti.
Implicit Types xbs : list (pbit Ti).

Lemma pbits_label x bs : tagged_tag <$> PBit x <$> bs = bs.
Proof. induction bs; f_equal'; auto. Qed.
Lemma PBits_perm_label xbs :
  zip_with PBit (tagged_perm <$> xbs) (tagged_tag <$> xbs) = xbs.
Proof. by induction xbs as [|[]]; f_equal'. Qed.
Lemma pbit_empty_valid Γ mm : ✓{Γ,mm} (∅ : pbit Ti).
Proof. repeat split; auto using BIndet_valid, sep_empty_valid. Qed.
Lemma PBit_valid Γ mm x b :
  sep_valid x → ¬sep_unmapped x → ✓{Γ,mm} b → ✓{Γ,mm} (PBit x b).
Proof. by repeat split. Qed.
Lemma PBits_valid Γ mm xs bs :
  Forall sep_valid xs → Forall (not ∘ sep_unmapped) xs →
  ✓{Γ,mm}* bs → ✓{Γ,mm}* (zip_with PBit xs bs).
Proof.
  intros Hxs. revert bs. induction Hxs; intros ?? [|????];
    decompose_Forall_hyps'; auto using PBit_valid.
Qed.
Lemma pbit_perm_mapped xb :
  sep_valid xb → sep_unmapped (tagged_perm xb) → sep_unmapped xb.
Proof. intros [??]; split; auto. Qed.
Lemma pbits_perm_mapped xbs :
  Forall sep_valid xbs → Forall (not ∘ sep_unmapped) xbs →
  Forall (not ∘ sep_unmapped) (tagged_perm <$> xbs).
Proof.
  induction 1; inversion_clear 1; constructor; auto using pbit_perm_mapped.
Qed.
Lemma PBits_mapped xs bs :
  Forall (not ∘ sep_unmapped) xs →
  Forall (not ∘ sep_unmapped) (zip_with PBit xs bs).
Proof.
  intros Hxs. revert bs. induction Hxs; intros [|??]; constructor; auto.
  by intros [??].
Qed.
Lemma pbit_label_valid Γ mm xb : ✓{Γ,mm} xb → ✓{Γ,mm} (tagged_tag xb).
Proof. by intros (?&?&?). Qed.
Lemma pbits_label_valid Γ mm xbs :
  ✓{Γ,mm}* xbs → ✓{Γ,mm}* (tagged_tag <$> xbs).
Proof. induction 1; constructor; auto using pbit_label_valid. Qed.
Lemma pbit_valid_weaken Γ1 Γ2 m1 m2 xb :
  ✓ Γ1 → ✓{Γ1,Some m1} xb → Γ1 ⊆ Γ2 →
  (∀ z σ, type_of_index m1 z = Some σ → type_of_index m2 z = Some σ) →
  ✓{Γ2,Some m2} xb.
Proof. intros ? (?&?&?); repeat split; eauto using bit_valid_weaken. Qed.
Lemma pbit_valid_weakly_valid Γ m xb : ✓{Γ,Some m} xb → ✓{Γ,None} xb.
Proof. intros (?&?&?); repeat split; eauto using bit_valid_weakly_valid. Qed.
Lemma pbit_valid_sep_valid Γ mm xb  : ✓{Γ,mm} xb → sep_valid xb.
Proof. by intros (?&?&?); repeat split. Qed.
Lemma pbit_unlock_valid Γ mm xb : ✓{Γ,mm} xb → ✓{Γ,mm} (pbit_unlock xb).
Proof.
  unfold pbit_unlock; intros (?&?&?); split; naive_solver
    auto using perm_unlock_valid, perm_unlock_unmapped_inv.
Qed.
Lemma pbit_unlock_unshared xb :
  sep_unshared xb → sep_unshared (pbit_unlock xb).
Proof.
  unfold pbit_unlock; intros (?&?); split; naive_solver auto using
    perm_unlock_unshared, perm_unlock_unmapped_inv, sep_unshared_valid.
Qed.
Lemma PBits_indetify xs :
  pbit_indetify <$> flip PBit (@BIndet Ti) <$> xs = flip PBit BIndet <$> xs.
Proof. induction xs; f_equal'; auto. Qed.
Lemma pbit_indetify_valid Γ mm xb : ✓{Γ,mm} xb → ✓{Γ,mm} (pbit_indetify xb).
Proof. destruct xb; intros (?&?&?); split; eauto using BIndet_valid. Qed.
Lemma pbits_indetify_valid Γ mm xbs :
  ✓{Γ,mm}* xbs → ✓{Γ,mm}* (pbit_indetify <$> xbs).
Proof. induction 1; simpl; auto using pbit_indetify_valid. Qed.
Lemma pbits_indetify_idempotent xbs :
  pbit_indetify <$> pbit_indetify <$> xbs = pbit_indetify <$> xbs.
Proof. by induction xbs; f_equal'. Qed.
Lemma pbit_indetified_subseteq xb1 xb2 :
  pbit_indetify xb2 = xb2 → xb1 ⊆ xb2 → pbit_indetify xb1 = xb1.
Proof. destruct xb1, xb2; intros ? (?&?&?&?); naive_solver. Qed.
Lemma pbits_indetified_subseteq xbs1 xbs2 :
  pbit_indetify <$> xbs2 = xbs2 → xbs1 ⊆* xbs2 → pbit_indetify <$> xbs1 = xbs1.
Proof.
  induction 2; simplify_equality';
    f_equal'; eauto using pbit_indetified_subseteq.
Qed.
Lemma pbit_indetify_unmapped xb : sep_unmapped xb → pbit_indetify xb = xb.
Proof. destruct xb; intros [??]; naive_solver. Qed.
Lemma pbit_unmapped_indetify xb :
  sep_unmapped xb → sep_unmapped (pbit_indetify xb).
Proof. destruct xb; intros [??]; split; naive_solver. Qed.
Lemma pbits_indetify_unmapped xbs :
  Forall sep_unmapped xbs → pbit_indetify <$> xbs = xbs.
Proof. induction 1; f_equal'; auto using pbit_indetify_unmapped. Qed.
Lemma pbits_indetify_mask_unmapped βs xbs :
  Forall sep_unmapped xbs → mask pbit_indetify βs xbs = xbs.
Proof.
  intros Hxbs. revert βs. induction Hxbs;
    intros [|[] ?]; f_equal'; auto using pbit_indetify_unmapped.
Qed.
Lemma pbit_indetify_disjoint xb1 xb2 :
  xb1 ⊥ xb2 → pbit_indetify xb1 ⊥ pbit_indetify xb2.
Proof. intros (?&?&?&?); split; eauto. Qed.
Lemma pbits_indetify_disjoint xbs1 xbs2 :
  xbs1 ⊥* xbs2 → pbit_indetify <$> xbs1 ⊥* pbit_indetify <$> xbs2.
Proof. induction 1; simpl; auto using pbit_indetify_disjoint. Qed.
Lemma pbits_indetify_union xbs1 xbs2 :
  pbit_indetify <$> xbs1 ∪* xbs2
  = (pbit_indetify <$> xbs1) ∪* (pbit_indetify <$> xbs2).
Proof. revert xbs2. by induction xbs1; intros [|??]; f_equal'. Qed.
Lemma pbit_indetify_unshared xb :
  sep_unshared xb → sep_unshared (pbit_indetify xb).
Proof. by intros [??]. Qed.

(** ** Refinements *)
Lemma pbit_refine_valid_l Γ f xb1 xb2 : ✓ Γ → xb1 ⊑{Γ,f} xb2 → ✓{Γ,None} xb1.
Proof.
  destruct xb1, xb2; intros ? (?&?&?&?); split;
    naive_solver eauto using BIndet_refine_r_inv, bit_refine_valid_l.
Qed.
Lemma pbits_refine_valid_l Γ f xbs1 xbs2 :
  ✓ Γ → xbs1 ⊑{Γ,f}* xbs2 → ✓{Γ,None}* xbs1.
Proof. induction 2; eauto using pbit_refine_valid_l. Qed.
Lemma pbit_refine_valid_r Γ f xb1 xb2 : ✓ Γ → xb1 ⊑{Γ,f} xb2 → ✓{Γ,None} xb2.
Proof.
  destruct xb1, xb2; intros ? (?&?&?&?); split;
      naive_solver eauto using BIndet_refine_r_inv, bit_refine_valid_r.
Qed.
Lemma pbits_refine_valid_r Γ f xbs1 xbs2 :
  ✓ Γ → xbs1 ⊑{Γ,f}* xbs2 → ✓{Γ,None}* xbs2.
Proof. induction 2; eauto using pbit_refine_valid_r. Qed.
Lemma pbit_refine_id Γ mm xb : ✓{Γ,mm} xb → xb ⊑{Γ} xb.
Proof. intros (?&?&?); split; eauto using bit_refine_id. Qed.
Lemma pbits_refine_id Γ mm xbs : ✓{Γ,mm}* xbs → xbs ⊑{Γ}* xbs.
Proof. induction 1; eauto using pbit_refine_id. Qed.
Lemma pbit_refine_compose Γ f1 f2 xb1 xb2 xb3 :
  ✓ Γ → xb1 ⊑{Γ,f1} xb2 → xb2 ⊑{Γ,f2} xb3 → xb1 ⊑{Γ,f1 ◎ f2} xb3.
Proof.
  destruct xb1, xb2, xb3; intros ? (?&?&?) (?&?&?); split;
    naive_solver eauto using bit_refine_compose.
Qed.
Lemma pbits_refine_compose Γ f1 f2 xbs1 xbs2 xbs3 :
  ✓ Γ → xbs1 ⊑{Γ,f1}* xbs2 → xbs2 ⊑{Γ,f2}* xbs3 → xbs1 ⊑{Γ,f1 ◎ f2}* xbs3.
Proof.
  intros ? Hxbs. revert xbs3. induction Hxbs; intros;
    decompose_Forall_hyps; eauto using pbit_refine_compose.
Qed.
Global Instance:
  PropHolds (✓ Γ) → Transitive (refine Γ mem_inj_id : relation (pbit Ti)).
Proof. intros Γ ????. eapply @pbit_refine_compose; eauto; apply _. Qed.
Global Instance: AntiSymmetric (=) (refine Γ mem_inj_id : relation (pbit Ti)).
Proof.
  intros Γ [??] [??] (?&?&?) (?&?&?); simplify_equality'; f_equal; auto.
  by apply (anti_symmetric (refine Γ mem_inj_id)).
Qed.
Lemma pbit_refine_unmapped Γ f xb1 xb2 :
  sep_unmapped xb1 → xb1 ⊑{Γ,f} xb2 → sep_unmapped xb2.
Proof. destruct xb1, xb2; intros [??] (?&?&?); split; naive_solver. Qed.
Lemma pbits_refine_unmapped Γ f xbs1 xbs2 :
  Forall sep_unmapped xbs1 → xbs1 ⊑{Γ,f}* xbs2 → Forall sep_unmapped xbs2.
Proof.
  induction 2; decompose_Forall_hyps; eauto using pbit_refine_unmapped.
Qed.
Lemma pbit_refine_unmapped_inv Γ f xb1 xb2 :
  sep_unmapped xb2 → xb1 ⊑{Γ,f} xb2 → sep_unmapped xb1.
Proof.
  intros [??] (?&?&?);
    split; eauto using (BIndet_refine_r_inv Γ f) with congruence.
Qed.
Lemma pbits_refine_unmapped_inv Γ f xbs1 xbs2 :
  Forall sep_unmapped xbs2 → xbs1 ⊑{Γ,f}* xbs2 → Forall sep_unmapped xbs1.
Proof.
  induction 2; decompose_Forall_hyps;
    eauto using pbit_refine_unmapped_inv.
Qed.
Lemma pbit_refine_unshared Γ f xb1 xb2 :
  sep_unshared xb1 → xb1 ⊑{Γ,f} xb2 → sep_unshared xb2.
Proof.
  destruct xb1, xb2. intros [??] (?&?&?); split;
    naive_solver eauto using sep_unshared_valid.
Qed.
Lemma pbits_refine_unshared Γ f xbs1 xbs2 :
  Forall sep_unshared xbs1 → xbs1 ⊑{Γ,f}* xbs2 → Forall sep_unshared xbs2.
Proof.
  induction 2; decompose_Forall_hyps; eauto using pbit_refine_unshared.
Qed.
Lemma pbit_refine_unshared_inv Γ f xb1 xb2 :
  sep_unshared xb2 → xb1 ⊑{Γ,f} xb2 → sep_unshared xb1.
Proof.
  destruct xb1, xb2; intros [??] (?&?&?&?); split;
    naive_solver eauto using BIndet_refine_r_inv.
Qed.
Lemma pbits_refine_unshared_inv Γ f xbs1 xbs2 :
  Forall sep_unshared xbs2 → xbs1 ⊑{Γ,f}* xbs2 → Forall sep_unshared xbs1.
Proof.
  induction 2; decompose_Forall_hyps;
    eauto using pbit_refine_unshared_inv.
Qed.
Lemma pbit_empty_refine Γ f : (∅ : pbit Ti) ⊑{Γ,f} ∅.
Proof. split; simpl; auto using BIndet_BIndet_refine, sep_empty_valid. Qed.
Lemma PBit_refine Γ f x b1 b2 :
  sep_valid x → ¬sep_unmapped x → b1 ⊑{Γ,f} b2 → PBit x b1 ⊑{Γ,f} PBit x b2.
Proof. split; naive_solver eauto using BBit_refine. Qed.
Lemma PBits_refine Γ f xs bs1 bs2 :
  Forall sep_valid xs → Forall (not ∘ sep_unmapped) xs →
  bs1 ⊑{Γ,f}* bs2 → zip_with PBit xs bs1 ⊑{Γ,f}* zip_with PBit xs bs2.
Proof.
  intros Hxs Hxs' Hbs. revert xs Hxs Hxs'. induction Hbs; intros ? [|????] ?;
    decompose_Forall_hyps'; eauto using PBit_refine.
Qed.
Lemma PBit_BIndet_refine Γ f x :
  sep_valid x → PBit x BIndet ⊑{Γ,f} PBit x BIndet.
Proof. repeat split; auto using BIndet_BIndet_refine. Qed.
Lemma PBits_BIndet_refine Γ f xs :
  Forall sep_valid xs → flip PBit BIndet <$> xs ⊑{Γ,f}* flip PBit BIndet <$> xs.
Proof. induction 1; simpl; auto using PBit_BIndet_refine. Qed.
Lemma PBit_BIndet_refine_l Γ mm xb :
  ✓{Γ,mm} xb → PBit (tagged_perm xb) BIndet ⊑{Γ} xb.
Proof. intros (?&?&?); split; naive_solver eauto using BIndet_refine. Qed.
Lemma PBits_BIndet_refine_l Γ mm xbs :
  ✓{Γ,mm}* xbs → flip PBit BIndet <$> tagged_perm <$> xbs ⊑{Γ}* xbs.
Proof. induction 1; simpl; eauto using PBit_BIndet_refine_l. Qed.
Lemma pbit_unshared x b :
  sep_unshared x → ¬sep_unmapped x → sep_unshared (PBit x b).
Proof. by repeat split. Qed.
Lemma pbits_unshared xs bs :
  Forall sep_unshared xs → Forall (not ∘ sep_unmapped) xs →
  Forall sep_unshared (zip_with PBit xs bs).
Proof.
  revert xs. induction bs; intros ? [|????] ?;
    decompose_Forall_hyps'; auto using pbit_unshared.
Qed.
Lemma pbit_label_refine Γ f xb1 xb2 :
  xb1 ⊑{Γ,f} xb2 → tagged_tag xb1 ⊑{Γ,f} tagged_tag xb2.
Proof. by intros []. Qed.
Lemma pbits_label_refine Γ f xbs1 xbs2 :
  xbs1 ⊑{Γ,f}* xbs2 → tagged_tag <$> xbs1 ⊑{Γ,f}* tagged_tag <$> xbs2.
Proof. induction 1; constructor; auto using pbit_label_refine. Qed.
Lemma pbit_unlock_refine Γ f xb1 xb2 :
  xb1 ⊑{Γ,f} xb2 → pbit_unlock xb1 ⊑{Γ,f} pbit_unlock xb2.
Proof.
  destruct xb1, xb2; intros (?&?&?&?); split;
    try naive_solver eauto using perm_unlock_valid, perm_unlock_unmapped_inv.
Qed.
Lemma pbit_lock_refine Γ f xb1 xb2 :
  Some Writable ⊆ pbit_kind xb1 →
  xb1 ⊑{Γ,f} xb2 → pbit_lock xb1 ⊑{Γ,f} pbit_lock xb2.
Proof.
  destruct xb1, xb2; intros ? (?&?&?&?); split;
    try naive_solver eauto using perm_lock_unmapped_inv, perm_lock_valid.
Qed.
Lemma pbit_indetify_refine Γ f xb1 xb2 :
  xb1 ⊑{Γ,f} xb2 → pbit_indetify xb1 ⊑{Γ,f} pbit_indetify xb2.
Proof.
  destruct xb1, xb2; intros (?&?&?&?); split; eauto using BIndet_BIndet_refine.
Qed.
Lemma pbits_indetify_refine Γ f xbs1 xbs2 :
  xbs1 ⊑{Γ,f}* xbs2 → pbit_indetify <$> xbs1 ⊑{Γ,f}* pbit_indetify <$> xbs2.
Proof. induction 1; simpl; auto using pbit_indetify_refine. Qed.
Lemma pbit_indetified_refine Γ f xb1 xb2 :
  pbit_indetify xb2 = xb2 → xb1 ⊑{Γ,f} xb2 → pbit_indetify xb1 = xb1.
Proof.
  unfold pbit_indetify. destruct xb1, xb2; intros ? (?&?&?&?);
    simplify_equality'; f_equal; eauto using BIndet_refine_r_inv, eq_sym.
Qed.
Lemma pbits_indetified_refine Γ f xbs1 xbs2 :
  pbit_indetify <$> xbs2 = xbs2 →
  xbs1 ⊑{Γ,f}* xbs2 → pbit_indetify <$> xbs1 = xbs1.
Proof.
  induction 2; simplify_equality'; f_equal; eauto using pbit_indetified_refine.
Qed.
End properties.
