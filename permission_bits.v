(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export permissions bits.

Notation pbit K := (tagged perm (@BIndet K)).
Notation PBit := (Tagged (d:=BIndet)).
Hint Extern 0 (Separation _) => apply (_ : Separation (pbit _)).

Section operations.
  Context `{Env K}.

  Global Instance pbit_valid: Valid (env K * memenv K) (pbit K) := λ ΓΔ xb,
    ✓{ΓΔ} (tagged_tag xb) ∧ sep_valid xb.

  Definition pbit_indetify (xb : pbit K) : pbit K :=
    PBit (tagged_perm xb) BIndet.
  Definition pbit_kind : pbit K → option pkind := perm_kind ∘ tagged_perm.
  Definition pbit_full : pbit K := PBit perm_full BIndet.
  Definition pbit_token : pbit K := PBit perm_token BIndet.
  Definition pbit_locked : pbit K → bool := perm_locked ∘ tagged_perm.
  Definition pbit_lock (xb : pbit K) : pbit K :=
    PBit (perm_lock (tagged_perm xb)) (tagged_tag xb).
  Definition pbit_unlock (xb : pbit K) : pbit K :=
    PBit (perm_unlock (tagged_perm xb)) (tagged_tag xb).
  Definition pbit_unlock_if (xb : pbit K) (β : bool) : pbit K :=
    if β then pbit_unlock xb else xb.
End operations.

Arguments pbit_kind _ !_ /.
Arguments pbit_indetify _ !_ /.
Arguments pbit_locked _ !_ /.
Arguments pbit_lock _ !_ /.
Arguments pbit_unlock _ !_ /.

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

Lemma pbits_tag x bs : tagged_tag <$> PBit x <$> bs = bs.
Proof. induction bs; f_equal'; auto. Qed.
Lemma PBits_perm_tag xbs :
  zip_with PBit (tagged_perm <$> xbs) (tagged_tag <$> xbs) = xbs.
Proof. by induction xbs as [|[]]; f_equal'. Qed.
Lemma pbit_empty_valid Γ Δ : ✓{Γ,Δ} (∅ : pbit K).
Proof. repeat split; auto using BIndet_valid, sep_empty_valid. Qed.
Lemma PBit_valid Γ Δ x b :
  sep_valid x → ¬sep_unmapped x → ✓{Γ,Δ} b → ✓{Γ,Δ} (PBit x b).
Proof. by repeat split. Qed.
Lemma PBits_valid Γ Δ xs bs :
  Forall sep_valid xs → Forall (not ∘ sep_unmapped) xs →
  ✓{Γ,Δ}* bs → ✓{Γ,Δ}* (zip_with PBit xs bs).
Proof.
  intros Hxs. revert bs. induction Hxs; intros ?? [|????];
    decompose_Forall_hyps; auto using PBit_valid.
Qed.
Lemma pbit_mapped xb : Some Readable ⊆ pbit_kind xb → ¬sep_unmapped xb.
Proof. intros ? [? _]. by apply (perm_mapped (tagged_perm xb)). Qed.
Lemma pbit_perm_mapped xb :
  sep_valid xb → sep_unmapped (tagged_perm xb) → sep_unmapped xb.
Proof. intros [??]; split; auto. Qed.
Lemma pbits_perm_mapped xbs :
  Forall sep_valid xbs → Forall (not ∘ sep_unmapped) xbs →
  Forall (not ∘ sep_unmapped) (tagged_perm <$> xbs).
Proof.
  induction 1; inversion_clear 1; constructor; auto using pbit_perm_mapped.
Qed.
Lemma pbits_perm_mapped' xbs :
  Forall sep_valid xbs → Forall sep_unmapped (tagged_perm <$> xbs) →
  Forall sep_unmapped xbs.
Proof.
  induction 1; inversion_clear 1; constructor; auto using pbit_perm_mapped.
Qed.
Lemma pbits_perm_unshared xbs :
  Forall sep_unshared xbs → Forall sep_unshared (tagged_perm <$> xbs).
Proof. by induction 1; constructor. Qed.
Lemma PBits_mapped xs bs :
  Forall (not ∘ sep_unmapped) xs →
  Forall (not ∘ sep_unmapped) (zip_with PBit xs bs).
Proof.
  intros Hxs. revert bs. induction Hxs; intros [|??]; constructor; auto.
  by intros [??].
Qed.
Lemma pbits_tag_valid Γ Δ xbs :
  ✓{Γ,Δ}* xbs → ✓{Γ,Δ}* (tagged_tag <$> xbs).
Proof. induction 1 as [|?? (?&?&?)]; csimpl; eauto. Qed.
Lemma pbits_valid_perm_valid Γ Δ xbs :
  ✓{Γ,Δ}* xbs → Forall sep_valid (tagged_perm <$> xbs).
Proof. induction 1 as [|?? (?&?&?)]; csimpl; eauto. Qed.
Lemma pbit_valid_weaken Γ1 Γ2 Δ1 Δ2 xb :
  ✓ Γ1 → ✓{Γ1,Δ1} xb → Γ1 ⊆ Γ2 → Δ1 ⇒ₘ Δ2 → ✓{Γ2,Δ2} xb.
Proof. intros ? (?&?&?); repeat split; eauto using bit_valid_weaken. Qed.
Lemma pbit_valid_sep_valid Γ Δ xb  : ✓{Γ,Δ} xb → sep_valid xb.
Proof. by intros (?&?&?); repeat split. Qed.
Lemma pbits_valid_sep_valid Γ Δ xbs  : ✓{Γ,Δ}* xbs → Forall sep_valid xbs.
Proof. induction 1; eauto using pbit_valid_sep_valid. Qed.
Lemma pbit_unlock_valid Γ Δ xb : ✓{Γ,Δ} xb → ✓{Γ,Δ} (pbit_unlock xb).
Proof.
  unfold pbit_unlock; intros (?&?&?); repeat split; naive_solver
    auto using perm_unlock_valid, perm_unlock_mapped.
Qed.
Lemma pbit_unlock_if_empty β : pbit_unlock_if (∅ : pbit K) β = ∅.
Proof. by destruct β. Qed.
Lemma pbit_unlock_unshared xb :
  sep_unshared xb → sep_unshared (pbit_unlock xb).
Proof. apply perm_unlock_unshared. Qed.
Lemma pbits_unlock_unshared xbs βs :
  Forall sep_unshared xbs →
  Forall sep_unshared (zip_with pbit_unlock_if xbs βs).
Proof.
  intros Hxbs. revert βs. induction Hxbs; intros [|[] ?];
    simpl; constructor; auto using pbit_unlock_unshared.
Qed.
Lemma pbit_unlock_unmapped xb : sep_unmapped xb → sep_unmapped (pbit_unlock xb).
Proof.
  destruct xb; sep_unfold; naive_solver auto using perm_unlock_unmapped.
Qed.
Lemma pbit_unlock_mapped xb :
  sep_valid xb → sep_unmapped (pbit_unlock xb) → sep_unmapped xb.
Proof. destruct xb; sep_unfold; naive_solver auto using perm_unlock_mapped. Qed.
Lemma pbits_kind_weaken xbs k1 k2 :
  Forall (λ xb, k2 ⊆ pbit_kind xb) xbs → k1 ⊆ k2 →
  Forall (λ xb, k1 ⊆ pbit_kind xb) xbs.
Proof. intros. eapply Forall_impl; eauto. intros xb ?. by transitivity k2. Qed.
Lemma pbits_mapped xbs :
  Forall (λ xb, Some Readable ⊆ pbit_kind xb) xbs →
  Forall (not ∘ sep_unmapped) xbs.
Proof.
  induction 1 as [|[x b]]; constructor; auto.
  intros [??]; simplify_equality'; eapply perm_mapped; eauto.
Qed.
Lemma PBits_unshared xs bs :
  Forall sep_unshared xs → Forall sep_unshared (zip_with PBit xs bs).
Proof.
  intros Hxs. revert bs. induction Hxs; intros [|??]; constructor; eauto.
Qed.
Lemma pbits_unshared xbs :
  Forall sep_valid xbs → Forall (λ xb, Some Locked ⊆ pbit_kind xb) xbs →
  Forall sep_unshared xbs.
Proof.
  induction 1 as [|[x b] ? [??]]; intros; decompose_Forall_hyps;
    repeat constructor; sep_unfold; auto using perm_unshared.
Qed.
Lemma PBits_indetify xs :
  pbit_indetify <$> flip PBit (@BIndet K) <$> xs = flip PBit BIndet <$> xs.
Proof. induction xs; f_equal'; auto. Qed.
Lemma pbit_indetify_valid Γ Δ xb : ✓{Γ,Δ} xb → ✓{Γ,Δ} (pbit_indetify xb).
Proof. destruct xb; intros (?&?&?); repeat split; eauto using BIndet_valid. Qed.
Lemma pbits_indetify_valid Γ Δ xbs :
  ✓{Γ,Δ}* xbs → ✓{Γ,Δ}* (pbit_indetify <$> xbs).
Proof. induction 1; csimpl; auto using pbit_indetify_valid. Qed.
Lemma pbits_indetify_idempotent xbs :
  pbit_indetify <$> pbit_indetify <$> xbs = pbit_indetify <$> xbs.
Proof. by induction xbs; f_equal'. Qed.
Lemma pbit_indetify_unmapped xb : sep_unmapped xb → pbit_indetify xb = xb.
Proof. destruct xb; intros [??]; naive_solver. Qed.
Lemma pbit_unmapped_indetify xb :
  sep_unmapped xb → sep_unmapped (pbit_indetify xb).
Proof. destruct xb; intros [??]; split; naive_solver. Qed.
Lemma pbits_unmapped_tag xbs :
  Forall sep_unmapped xbs → tagged_tag <$> xbs = replicate (length xbs) BIndet.
Proof. by induction 1 as [|?? []]; f_equal'. Qed.
Lemma pbit_unmapped_indetify_inv xb :
  sep_valid xb → sep_unmapped (pbit_indetify xb) → sep_unmapped xb.
Proof. destruct xb; intros [??] [??]; split; naive_solver. Qed.
Lemma pbits_unmapped_indetify_inv βs xbs :
  Forall sep_valid xbs →
  Forall sep_unmapped (mask pbit_indetify βs xbs) → Forall sep_unmapped xbs.
Proof.
  intros Hxbs. revert βs. induction Hxbs; intros [|[] ?] ?;
    decompose_Forall_hyps; eauto using pbit_unmapped_indetify_inv.
Qed.
Lemma pbits_indetify_unmapped xbs :
  Forall sep_unmapped xbs → pbit_indetify <$> xbs = xbs.
Proof. induction 1; f_equal'; auto using pbit_indetify_unmapped. Qed.
Lemma pbits_indetify_mask_unmapped βs xbs :
  Forall sep_unmapped xbs → mask pbit_indetify βs xbs = xbs.
Proof.
  intros Hxbs. revert βs. induction Hxbs;
    intros [|[] ?]; f_equal'; auto using pbit_indetify_unmapped.
Qed.
Lemma pbit_indetify_unshared xb :
  sep_unshared xb → sep_unshared (pbit_indetify xb).
Proof. done. Qed.
Lemma pbit_full_valid Γ Δ : ✓{Γ,Δ} pbit_full.
Proof. by apply (bool_decide_unpack _). Qed.
Lemma pbit_full_unshared : sep_unshared (@pbit_full K).
Proof. done. Qed.
Lemma PBits_BIndet_tag xbs :
  Forall sep_unmapped xbs →
  flip PBit BIndet <$> tagged_perm <$> xbs = xbs.
Proof. induction 1 as [|[] ? [??]]; simplify_equality'; f_equal; auto. Qed.

Lemma pbit_Readable_locked xb :
  Some Readable ⊆ pbit_kind xb → pbit_locked xb = false.
Proof. by destruct xb; f_equal'; auto using perm_Readable_locked. Qed.
Lemma pbits_Readable_locked xbs i :
  Forall (λ xb, Some Readable ⊆ pbit_kind xb) xbs →
  i < length xbs → pbit_locked <$> xbs !! i = Some false.
Proof.
  intros Hxbs. revert i. induction Hxbs; intros [|?] ?;
    f_equal'; auto using pbit_Readable_locked with lia.
Qed.
Lemma pbits_unlock_sep_valid xbs βs :
  Forall sep_valid xbs → Forall sep_valid (zip_with pbit_unlock_if xbs βs).
Proof.
  sep_unfold; intros Hxbs; revert βs.
  induction Hxbs as [|[]]; intros [|[] ?]; constructor;
    naive_solver eauto using perm_unlock_valid, perm_unlock_mapped.
Qed.
Lemma pbits_locks_unlock βs xbs :
  βs =.>* pbit_locked <$> xbs →
  pbit_locked <$> zip_with pbit_unlock_if xbs βs = (pbit_locked <$> xbs) ∖* βs.
Proof.
  revert βs. induction xbs as [|[[[]|]] ?]; intros [|[] ?] ?;
    decompose_Forall_hyps; f_equal; auto.
Qed.
Lemma pbits_unlock_empty_inv xbs βs :
  Forall (∅ =) (zip_with pbit_unlock_if xbs βs) → Forall sep_valid xbs →
  length xbs = length βs → Forall (∅ =) xbs.
Proof.
  assert (∀ x, sep_valid x → perm_unlock x = ∅ → x = ∅).
  { intros [[]|]; repeat sep_unfold; naive_solver. }
  intros Hxbs Hxbs'. revert βs Hxbs.
  induction Hxbs' as [|[] ? []]; intros [|[] ?]; sep_unfold;
    intros; decompose_Forall_hyps; constructor; eauto.
  f_equal; eauto using eq_sym.
Qed.
Lemma pbits_unlock_mapped xbs βs :
  Forall sep_unmapped (zip_with pbit_unlock_if xbs βs) → Forall sep_valid xbs →
  length xbs = length βs → Forall sep_unmapped xbs.
Proof.
  intros Hxbs Hxbs'. revert βs Hxbs. induction Hxbs' as [|[] ? []]; sep_unfold;
    intros [|[] ?] ??; decompose_Forall_hyps; constructor;
    intuition eauto using perm_unlock_mapped.
Qed.
Lemma pbits_unlock_valid Γ Δ xbs βs :
  ✓{Γ,Δ}* xbs → ✓{Γ,Δ}* (zip_with pbit_unlock_if xbs βs).
Proof.
  intros Hxs. revert βs.
  induction Hxs; intros [|[] ?]; simpl; auto using pbit_unlock_valid.
Qed.
Lemma pbit_indetify_unlock xbs βs :
  pbit_indetify <$> zip_with pbit_unlock_if xbs βs
  = zip_with pbit_unlock_if (pbit_indetify <$> xbs) βs.
Proof. revert βs. induction xbs; intros [|[] ?]; f_equal'; auto. Qed.
Lemma pbits_unlock_orb xbs βs1 βs2 :
  zip_with pbit_unlock_if xbs (βs1 ||* βs2)
  = zip_with pbit_unlock_if (zip_with pbit_unlock_if xbs βs1) βs2.
Proof.
  revert βs1 βs2. induction xbs as [|[]]; intros [|[] ?] [|[] ?];
    f_equal'; auto using perm_unlock_unlock with f_equal.
Qed.
Lemma pbits_lock_mapped xbs :
  Forall (not ∘ sep_unmapped) xbs →
  Forall (not ∘ sep_unmapped) (pbit_lock <$> xbs).
Proof.
  sep_unfold. induction 1; constructor; simpl in *;
    intuition eauto using perm_lock_mapped.
Qed.
Lemma pbit_lock_indetified xb :
  pbit_indetify xb = xb → pbit_indetify (pbit_lock xb) = pbit_lock xb.
Proof. by intros <-. Qed.
Lemma pbits_lock_valid Γ Δ xbs :
  ✓{Γ,Δ}* xbs → Forall (λ xb, Some Writable ⊆ pbit_kind xb) xbs →
  ✓{Γ,Δ}* (pbit_lock <$> xbs).
Proof.
  induction 1 as [|[??] ? (?&?&?)]; repeat constructor; decompose_Forall_hyps;
    eauto using perm_lock_valid, perm_lock_mapped.
Qed.
Lemma pbit_lock_unmapped xb :
  Some Writable ⊆ pbit_kind xb → sep_unmapped xb → sep_unmapped (pbit_lock xb).
Proof. intros ? [??]; split; auto. by apply perm_lock_unmapped. Qed.
Lemma pbit_lock_mapped xb :
  sep_unmapped (pbit_lock xb) → sep_unmapped xb.
Proof. intros [??]; split; auto using perm_lock_mapped. Qed.
Lemma pbit_lock_unshared xb :
  sep_unshared xb → sep_unshared (pbit_lock xb).
Proof. apply perm_lock_unshared. Qed.
Lemma pbits_perm_mask βs xbs :
  tagged_perm <$> mask pbit_indetify βs xbs = tagged_perm <$> xbs.
Proof. revert βs. induction xbs; intros [|[] ?]; f_equal'; auto. Qed.
Lemma pbits_locked_mask βs xbs :
  pbit_locked <$> mask pbit_indetify βs xbs = pbit_locked <$> xbs.
Proof. revert βs. induction xbs; intros [|[] ?]; f_equal'; auto. Qed.
End permission_bits.
