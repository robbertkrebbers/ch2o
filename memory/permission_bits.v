(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export permissions bits.

Notation pbit K := (tagged perm (@BIndet K)).
Notation PBit := (Tagged (d:=BIndet)).
Global Hint Extern 0 (Separation _) => apply (_ : Separation (pbit _)): core.

Section operations.
  Context `{Env K}.

  Global Instance pbit_valid: Valid (env K * memenv K) (pbit K) := λ ΓΔ γb,
    ✓{ΓΔ} (tagged_tag γb) ∧ sep_valid γb.

  Definition pbit_indetify (γb : pbit K) : pbit K :=
    PBit (tagged_perm γb) BIndet.
  Definition pbit_kind : pbit K → option pkind := perm_kind ∘ tagged_perm.
  Definition pbit_full : pbit K := PBit perm_full BIndet.
  Definition pbit_token : pbit K := PBit perm_token BIndet.
  Definition pbit_locked : pbit K → bool := perm_locked ∘ tagged_perm.
  Definition pbit_lock (γb : pbit K) : pbit K :=
    PBit (perm_lock (tagged_perm γb)) (tagged_tag γb).
  Definition pbit_unlock (γb : pbit K) : pbit K :=
    PBit (perm_unlock (tagged_perm γb)) (tagged_tag γb).
  Definition pbit_unlock_if (γb : pbit K) (β : bool) : pbit K :=
    if β then pbit_unlock γb else γb.
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
Implicit Types γ : perm.
Implicit Types γs : list perm.
Implicit Types γb : pbit K.
Implicit Types γbs : list (pbit K).

Lemma pbits_tag γ bs : tagged_tag <$> (PBit γ <$> bs) = bs.
Proof. induction bs; f_equal'; auto. Qed.
Lemma PBits_perm_tag γbs :
  zip_with PBit (tagged_perm <$> γbs) (tagged_tag <$> γbs) = γbs.
Proof. by induction γbs as [|[]]; f_equal'. Qed.
Lemma pbit_empty_valid Γ Δ : ✓{Γ,Δ} (∅ : pbit K).
Proof. repeat split; auto using BIndet_valid, sep_empty_valid. Qed.
Lemma PBit_valid Γ Δ γ b :
  sep_valid γ → ¬sep_unmapped γ → ✓{Γ,Δ} b → ✓{Γ,Δ} (PBit γ b).
Proof. by repeat split. Qed.
Lemma PBits_valid Γ Δ γs bs :
  Forall sep_valid γs → Forall (not ∘ sep_unmapped) γs →
  ✓{Γ,Δ}* bs → ✓{Γ,Δ}* (zip_with PBit γs bs).
Proof.
  intros Hγs. revert bs. induction Hγs; intros ?? [|????];
    decompose_Forall_hyps; auto using PBit_valid.
Qed.
Lemma pbit_mapped γb : Some Readable ⊆ pbit_kind γb → ¬sep_unmapped γb.
Proof. intros ? [? _]. by apply (perm_mapped (tagged_perm γb)). Qed.
Lemma pbit_perm_mapped γb :
  sep_valid γb → sep_unmapped (tagged_perm γb) → sep_unmapped γb.
Proof. intros [??]; split; auto. Qed.
Lemma pbits_perm_mapped γbs :
  Forall sep_valid γbs → Forall (not ∘ sep_unmapped) γbs →
  Forall (not ∘ sep_unmapped) (tagged_perm <$> γbs).
Proof.
  induction 1; inversion_clear 1; constructor; auto using pbit_perm_mapped.
Qed.
Lemma pbits_perm_mapped' γbs :
  Forall sep_valid γbs → Forall sep_unmapped (tagged_perm <$> γbs) →
  Forall sep_unmapped γbs.
Proof.
  induction 1; inversion_clear 1; constructor; auto using pbit_perm_mapped.
Qed.
Lemma pbits_perm_unshared γbs :
  Forall sep_unshared γbs → Forall sep_unshared (tagged_perm <$> γbs).
Proof. by induction 1; constructor. Qed.
Lemma PBits_mapped γs bs :
  Forall (not ∘ sep_unmapped) γs →
  Forall (not ∘ sep_unmapped) (zip_with PBit γs bs).
Proof.
  intros Hγs. revert bs. induction Hγs; intros [|??]; constructor; auto.
  by intros [??].
Qed.
Lemma pbits_tag_valid Γ Δ γbs :
  ✓{Γ,Δ}* γbs → ✓{Γ,Δ}* (tagged_tag <$> γbs).
Proof. induction 1 as [|?? (?&?&?)]; csimpl; eauto. Qed.
Lemma pbits_valid_perm_valid Γ Δ γbs :
  ✓{Γ,Δ}* γbs → Forall sep_valid (tagged_perm <$> γbs).
Proof. induction 1 as [|?? (?&?&?)]; csimpl; eauto. Qed.
Lemma pbit_valid_weaken Γ1 Γ2 Δ1 Δ2 γb :
  ✓ Γ1 → ✓{Γ1,Δ1} γb → Γ1 ⊆ Γ2 → Δ1 ⇒ₘ Δ2 → ✓{Γ2,Δ2} γb.
Proof. intros ? (?&?&?); repeat split; eauto using bit_valid_weaken. Qed.
Lemma pbit_valid_sep_valid Γ Δ γb  : ✓{Γ,Δ} γb → sep_valid γb.
Proof. by intros (?&?&?); repeat split. Qed.
Lemma pbits_valid_sep_valid Γ Δ γbs  : ✓{Γ,Δ}* γbs → Forall sep_valid γbs.
Proof. induction 1; eauto using pbit_valid_sep_valid. Qed.
Lemma pbit_unlock_valid Γ Δ γb : ✓{Γ,Δ} γb → ✓{Γ,Δ} (pbit_unlock γb).
Proof.
  unfold pbit_unlock; intros (?&?&?); repeat split; naive_solver
    auto using perm_unlock_valid, perm_unlock_mapped.
Qed.
Lemma pbit_unlock_if_empty β : pbit_unlock_if (∅ : pbit K) β = ∅.
Proof. by destruct β. Qed.
Lemma pbit_unlock_unshared γb :
  sep_unshared γb → sep_unshared (pbit_unlock γb).
Proof. apply perm_unlock_unshared. Qed.
Lemma pbits_unlock_unshared γbs βs :
  Forall sep_unshared γbs →
  Forall sep_unshared (zip_with pbit_unlock_if γbs βs).
Proof.
  intros Hγbs. revert βs. induction Hγbs; intros [|[] ?];
    simpl; constructor; auto using pbit_unlock_unshared.
Qed.
Lemma pbit_unlock_unmapped γb : sep_unmapped γb → sep_unmapped (pbit_unlock γb).
Proof.
  destruct γb; sep_unfold; naive_solver auto using perm_unlock_unmapped.
Qed.
Lemma pbit_unlock_mapped γb :
  sep_valid γb → sep_unmapped (pbit_unlock γb) → sep_unmapped γb.
Proof. destruct γb; sep_unfold; naive_solver auto using perm_unlock_mapped. Qed.
Lemma pbits_kind_weaken γbs k1 k2 :
  Forall (λ γb, k2 ⊆ pbit_kind γb) γbs → k1 ⊆ k2 →
  Forall (λ γb, k1 ⊆ pbit_kind γb) γbs.
Proof. intros. eapply Forall_impl; eauto. intros γb ?. by transitivity k2. Qed.
Lemma pbits_mapped γbs :
  Forall (λ γb, Some Readable ⊆ pbit_kind γb) γbs →
  Forall (not ∘ sep_unmapped) γbs.
Proof.
  induction 1 as [|[x b]]; constructor; auto.
  intros [??]; simplify_equality'; eapply perm_mapped; eauto.
Qed.
Lemma PBits_unshared γs bs :
  Forall sep_unshared γs → Forall sep_unshared (zip_with PBit γs bs).
Proof.
  intros Hγs. revert bs. induction Hγs; intros [|??]; constructor; eauto.
Qed.
Lemma pbits_unshared γbs :
  Forall sep_valid γbs → Forall (λ γb, Some Locked ⊆ pbit_kind γb) γbs →
  Forall sep_unshared γbs.
Proof.
  induction 1 as [|[x b] ? [??]]; intros; decompose_Forall_hyps;
    repeat constructor; sep_unfold; auto using perm_unshared.
Qed.
Lemma PBits_indetify γs :
  pbit_indetify <$> (flip PBit (@BIndet K) <$> γs) = flip PBit BIndet <$> γs.
Proof. induction γs; f_equal'; auto. Qed.
Lemma pbit_indetify_valid Γ Δ γb : ✓{Γ,Δ} γb → ✓{Γ,Δ} (pbit_indetify γb).
Proof. destruct γb; intros (?&?&?); repeat split; eauto using BIndet_valid. Qed.
Lemma pbits_indetify_valid Γ Δ γbs :
  ✓{Γ,Δ}* γbs → ✓{Γ,Δ}* (pbit_indetify <$> γbs).
Proof. induction 1; csimpl; auto using pbit_indetify_valid. Qed.
Lemma pbits_indetify_idempotent γbs :
  pbit_indetify <$> (pbit_indetify <$> γbs) = pbit_indetify <$> γbs.
Proof. by induction γbs; f_equal'. Qed.
Lemma pbit_indetify_unmapped γb : sep_unmapped γb → pbit_indetify γb = γb.
Proof. destruct γb; intros [??]; naive_solver. Qed.
Lemma pbit_unmapped_indetify γb :
  sep_unmapped γb → sep_unmapped (pbit_indetify γb).
Proof. destruct γb; intros [??]; split; naive_solver. Qed.
Lemma pbits_unmapped_tag γbs :
  Forall sep_unmapped γbs → tagged_tag <$> γbs = replicate (length γbs) BIndet.
Proof. by induction 1 as [|?? []]; f_equal'. Qed.
Lemma pbit_unmapped_indetify_inv γb :
  sep_valid γb → sep_unmapped (pbit_indetify γb) → sep_unmapped γb.
Proof. destruct γb; intros [??] [??]; split; naive_solver. Qed.
Lemma pbits_unmapped_indetify_inv βs γbs :
  Forall sep_valid γbs →
  Forall sep_unmapped (mask pbit_indetify βs γbs) → Forall sep_unmapped γbs.
Proof.
  intros Hγbs. revert βs. induction Hγbs; intros [|[] ?] ?;
    decompose_Forall_hyps; eauto using pbit_unmapped_indetify_inv.
Qed.
Lemma pbits_indetify_unmapped γbs :
  Forall sep_unmapped γbs → pbit_indetify <$> γbs = γbs.
Proof. induction 1; f_equal'; auto using pbit_indetify_unmapped. Qed.
Lemma pbits_indetify_mask_unmapped βs γbs :
  Forall sep_unmapped γbs → mask pbit_indetify βs γbs = γbs.
Proof.
  intros Hγbs. revert βs. induction Hγbs;
    intros [|[] ?]; f_equal'; auto using pbit_indetify_unmapped.
Qed.
Lemma pbit_indetify_unshared γb :
  sep_unshared γb → sep_unshared (pbit_indetify γb).
Proof. done. Qed.
Lemma pbit_full_valid Γ Δ : ✓{Γ,Δ} pbit_full.
Proof. by apply (bool_decide_unpack _). Qed.
Lemma pbit_full_unshared : sep_unshared (@pbit_full K).
Proof. done. Qed.
Lemma PBits_BIndet_tag γbs :
  Forall sep_unmapped γbs →
  flip PBit BIndet <$> (tagged_perm <$> γbs) = γbs.
Proof. induction 1 as [|[] ? [??]]; simplify_equality'; f_equal; auto. Qed.

Lemma pbit_Readable_locked γb :
  Some Readable ⊆ pbit_kind γb → pbit_locked γb = false.
Proof. by destruct γb; f_equal'; auto using perm_Readable_locked. Qed.
Lemma pbits_Readable_locked γbs i :
  Forall (λ γb, Some Readable ⊆ pbit_kind γb) γbs →
  i < length γbs → pbit_locked <$> γbs !! i = Some false.
Proof.
  intros Hγbs. revert i. induction Hγbs; intros [|?] ?;
    f_equal'; auto using pbit_Readable_locked with lia.
Qed.
Lemma pbits_unlock_sep_valid γbs βs :
  Forall sep_valid γbs → Forall sep_valid (zip_with pbit_unlock_if γbs βs).
Proof.
  sep_unfold; intros Hγbs; revert βs.
  induction Hγbs as [|[]]; intros [|[] ?]; constructor;
    naive_solver eauto using perm_unlock_valid, perm_unlock_mapped.
Qed.
Lemma pbits_locks_unlock βs γbs :
  βs =.>* pbit_locked <$> γbs →
  pbit_locked <$> zip_with pbit_unlock_if γbs βs = (pbit_locked <$> γbs) ∖* βs.
Proof.
  revert βs. induction γbs as [|[[[]|]] ?]; intros [|[] ?] ?;
    decompose_Forall_hyps; f_equal; auto.
Qed.
Lemma pbits_unlock_empty_inv γbs βs :
  Forall (∅ =.) (zip_with pbit_unlock_if γbs βs) → Forall sep_valid γbs →
  length γbs = length βs → Forall (∅ =.) γbs.
Proof.
  assert (∀ γ, sep_valid γ → perm_unlock γ = ∅ → γ = ∅).
  { intros [[]|]; repeat sep_unfold; naive_solver. }
  intros Hγbs Hγbs'. revert βs Hγbs.
  induction Hγbs' as [|[] ? []]; intros [|[] ?]; sep_unfold;
    intros; decompose_Forall_hyps; constructor; eauto.
  f_equal; eauto using eq_sym.
Qed.
Lemma pbits_unlock_mapped γbs βs :
  Forall sep_unmapped (zip_with pbit_unlock_if γbs βs) → Forall sep_valid γbs →
  length γbs = length βs → Forall sep_unmapped γbs.
Proof.
  intros Hγbs Hγbs'. revert βs Hγbs. induction Hγbs' as [|[] ? []]; sep_unfold;
    intros [|[] ?] ??; decompose_Forall_hyps; constructor;
    intuition eauto using perm_unlock_mapped.
Qed.
Lemma pbits_unlock_valid Γ Δ γbs βs :
  ✓{Γ,Δ}* γbs → ✓{Γ,Δ}* (zip_with pbit_unlock_if γbs βs).
Proof.
  intros Hγs. revert βs.
  induction Hγs; intros [|[] ?]; simpl; auto using pbit_unlock_valid.
Qed.
Lemma pbit_indetify_unlock γbs βs :
  pbit_indetify <$> zip_with pbit_unlock_if γbs βs
  = zip_with pbit_unlock_if (pbit_indetify <$> γbs) βs.
Proof. revert βs. induction γbs; intros [|[] ?]; f_equal'; auto. Qed.
Lemma pbits_unlock_orb γbs βs1 βs2 :
  zip_with pbit_unlock_if γbs (βs1 ||* βs2)
  = zip_with pbit_unlock_if (zip_with pbit_unlock_if γbs βs1) βs2.
Proof.
  revert βs1 βs2. induction γbs as [|[]]; intros [|[] ?] [|[] ?];
    f_equal'; auto using perm_unlock_unlock with f_equal.
Qed.
Lemma pbits_lock_mapped γbs :
  Forall (not ∘ sep_unmapped) γbs →
  Forall (not ∘ sep_unmapped) (pbit_lock <$> γbs).
Proof.
  sep_unfold. induction 1; constructor; simpl in *;
    intuition eauto using perm_lock_mapped.
Qed.
Lemma pbit_lock_indetified γb :
  pbit_indetify γb = γb → pbit_indetify (pbit_lock γb) = pbit_lock γb.
Proof. by intros <-. Qed.
Lemma pbits_lock_valid Γ Δ γbs :
  ✓{Γ,Δ}* γbs → Forall (λ γb, Some Writable ⊆ pbit_kind γb) γbs →
  ✓{Γ,Δ}* (pbit_lock <$> γbs).
Proof.
  induction 1 as [|[??] ? (?&?&?)]; repeat constructor; decompose_Forall_hyps;
    eauto using perm_lock_valid, perm_lock_mapped.
Qed.
Lemma pbit_lock_unmapped γb :
  Some Writable ⊆ pbit_kind γb → sep_unmapped γb → sep_unmapped (pbit_lock γb).
Proof. intros ? [??]; split; auto. by apply perm_lock_unmapped. Qed.
Lemma pbit_lock_mapped γb :
  sep_unmapped (pbit_lock γb) → sep_unmapped γb.
Proof. intros [??]; split; auto using perm_lock_mapped. Qed.
Lemma pbit_lock_unshared γb :
  sep_unshared γb → sep_unshared (pbit_lock γb).
Proof. apply perm_lock_unshared. Qed.
Lemma pbits_perm_mask βs γbs :
  tagged_perm <$> mask pbit_indetify βs γbs = tagged_perm <$> γbs.
Proof. revert βs. induction γbs; intros [|[] ?]; f_equal'; auto. Qed.
Lemma pbits_locked_mask βs γbs :
  pbit_locked <$> mask pbit_indetify βs γbs = pbit_locked <$> γbs.
Proof. revert βs. induction γbs; intros [|[] ?]; f_equal'; auto. Qed.
End permission_bits.
