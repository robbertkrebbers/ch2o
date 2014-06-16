(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export permissions bits.

Notation pbit Ti := (tagged perm (@BIndet Ti)).
Notation PBit := (Tagged (d:=BIndet)).

Section operations.
  Context `{TypeCheck M (type Ti) index, Refine Ti M, IndexAlive M,
    IntEnv Ti, PtrEnv Ti, ∀ m x, Decision (index_alive m x)}.

  Global Instance pbit_valid: Valid (env Ti * M) (pbit Ti) := λ Γm xb,
    sep_valid (tagged_perm xb) ∧
    ✓{Γm} (tagged_tag xb) ∧
    (sep_unmapped (tagged_perm xb) → tagged_tag xb = BIndet).

  Definition pbit_indetify (xb : pbit Ti) : pbit Ti :=
    PBit (tagged_perm xb) BIndet.
  Definition pbit_kind : pbit Ti → option pkind := perm_kind ∘ tagged_perm.
  Definition pbit_freed : pbit Ti := PBit perm_freed BIndet.
  Definition pbit_full (alloc : bool) : pbit Ti :=
    PBit (perm_full alloc) BIndet.
  Definition pbit_token : pbit Ti := PBit perm_token BIndet.
  Definition pbit_locked : pbit Ti → bool := perm_locked ∘ tagged_perm.
  Definition pbit_lock (xb : pbit Ti) : pbit Ti :=
    PBit (perm_lock (tagged_perm xb)) (tagged_tag xb).
  Definition pbit_unlock (xb : pbit Ti) : pbit Ti :=
    PBit (perm_unlock (tagged_perm xb)) (tagged_tag xb).
  Definition pbit_unlock_if (xb : pbit Ti) (β : bool) : pbit Ti :=
    if β then pbit_unlock xb else xb.

  Global Instance pbit_refine: Refine Ti M (pbit Ti) := λ Γ f m1 m2 xb1 xb2,
    tagged_tag xb1 ⊑{Γ,f@m1↦m2} tagged_tag xb2 ∧
    tagged_perm xb1 = tagged_perm xb2 ∧
    sep_valid (tagged_perm xb1) ∧
    (sep_unmapped (tagged_perm xb2) → tagged_tag xb2 = BIndet).
End operations.

Section properties.
Context `{MemSpec Ti M}.
Implicit Types Γ : env Ti.
Implicit Types m : M.
Implicit Types b : bit Ti.
Implicit Types bs : list (bit Ti).
Implicit Types x : perm.
Implicit Types xs : list perm.
Implicit Types xb : pbit Ti.
Implicit Types xbs : list (pbit Ti).

Lemma pbits_tag x bs : tagged_tag <$> PBit x <$> bs = bs.
Proof. induction bs; f_equal'; auto. Qed.
Lemma PBits_perm_tag xbs :
  zip_with PBit (tagged_perm <$> xbs) (tagged_tag <$> xbs) = xbs.
Proof. by induction xbs as [|[]]; f_equal'. Qed.
Lemma pbit_empty_valid Γ m : ✓{Γ,m} (∅ : pbit Ti).
Proof. repeat split; auto using BIndet_valid, sep_empty_valid. Qed.
Lemma PBit_valid Γ m x b :
  sep_valid x → ¬sep_unmapped x → ✓{Γ,m} b → ✓{Γ,m} (PBit x b).
Proof. by repeat split. Qed.
Lemma PBits_valid Γ m xs bs :
  Forall sep_valid xs → Forall (not ∘ sep_unmapped) xs →
  ✓{Γ,m}* bs → ✓{Γ,m}* (zip_with PBit xs bs).
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
Lemma pbits_perm_unshared xbs :
  Forall sep_unshared xbs → Forall sep_unshared (tagged_perm <$> xbs).
Proof. by induction 1 as [|?? [??]]; constructor. Qed.
Lemma PBits_mapped xs bs :
  Forall (not ∘ sep_unmapped) xs →
  Forall (not ∘ sep_unmapped) (zip_with PBit xs bs).
Proof.
  intros Hxs. revert bs. induction Hxs; intros [|??]; constructor; auto.
  by intros [??].
Qed.
Lemma pbits_tag_valid Γ m xbs :
  ✓{Γ,m}* xbs → ✓{Γ,m}* (tagged_tag <$> xbs).
Proof. induction 1 as [|?? (?&?&?)]; csimpl; eauto. Qed.
Lemma pbits_valid_perm_valid Γ m xbs :
  ✓{Γ,m}* xbs → Forall sep_valid (tagged_perm <$> xbs).
Proof. induction 1 as [|?? (?&?&?)]; csimpl; eauto. Qed.
Lemma pbit_valid_weaken Γ1 Γ2 m1 m2 xb :
  ✓ Γ1 → ✓{Γ1,m1} xb → Γ1 ⊆ Γ2 → (∀ o τ, m1 ⊢ o : τ → m2 ⊢ o : τ) → ✓{Γ2,m2} xb.
Proof. intros ? (?&?&?); repeat split; eauto using bit_valid_weaken. Qed.
Lemma pbit_valid_sep_valid Γ m xb  : ✓{Γ,m} xb → sep_valid xb.
Proof. by intros (?&?&?); repeat split. Qed.
Lemma pbits_valid_sep_valid Γ m xbs  : ✓{Γ,m}* xbs → Forall sep_valid xbs.
Proof. induction 1; eauto using pbit_valid_sep_valid. Qed.
Lemma pbit_unlock_valid Γ m xb : ✓{Γ,m} xb → ✓{Γ,m} (pbit_unlock xb).
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
Lemma pbits_kind_perm xbs k :
  Forall (λ xb, k ⊆ pbit_kind xb) xbs →
  Forall (λ x, k ⊆ perm_kind x) (tagged_perm <$> xbs).
Proof. intros. by apply Forall_fmap. Qed.
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
Lemma pbits_unshared xbs :
  Forall sep_valid xbs → Forall (λ xb, Some Locked ⊆ pbit_kind xb) xbs →
  Forall sep_unshared xbs.
Proof.
  induction 1 as [|[x b] ? [??]]; intros; decompose_Forall_hyps';
    repeat constructor; auto using perm_unshared.
Qed.
Lemma PBits_indetify xs :
  pbit_indetify <$> flip PBit (@BIndet Ti) <$> xs = flip PBit BIndet <$> xs.
Proof. induction xs; f_equal'; auto. Qed.
Lemma pbit_indetify_valid Γ m xb : ✓{Γ,m} xb → ✓{Γ,m} (pbit_indetify xb).
Proof. destruct xb; intros (?&?&?); split; eauto using BIndet_valid. Qed.
Lemma pbits_indetify_valid Γ m xbs :
  ✓{Γ,m}* xbs → ✓{Γ,m}* (pbit_indetify <$> xbs).
Proof. induction 1; csimpl; auto using pbit_indetify_valid. Qed.
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
Lemma pbit_unmapped_indetify_inv xb :
  sep_valid xb → sep_unmapped (pbit_indetify xb) → sep_unmapped xb.
Proof. destruct xb; intros [??] [??]; split; naive_solver. Qed.
Lemma pbits_unmapped_indetify_inv βs xbs :
  Forall sep_valid xbs →
  Forall sep_unmapped (mask pbit_indetify βs xbs) → Forall sep_unmapped xbs.
Proof.
  intros Hxbs. revert βs. induction Hxbs; intros [|[] ?] ?;
    decompose_Forall_hyps'; eauto using pbit_unmapped_indetify_inv.
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
Lemma pbit_indetify_unshared xb :
  sep_unshared xb → sep_unshared (pbit_indetify xb).
Proof. by intros [??]. Qed.
Lemma pbit_disjoint_typed Γ m xb1 xb2 :
  xb1 ⊥ xb2 → ✓{Γ,m} xb1 → sep_unmapped xb2 → ✓{Γ,m} xb2.
Proof.
  destruct xb1, xb2; intros (?&?&?&?) (?&?&?) [??]; split;
    naive_solver eauto using sep_unmapped_valid, BIndet_valid.
Qed.
Lemma pbits_disjoint_typed Γ m xbs1 xbs2 :
  xbs1 ⊥* xbs2 → ✓{Γ,m}* xbs1 → Forall sep_unmapped xbs2 → ✓{Γ,m}* xbs2.
Proof.
  induction 1; intros; decompose_Forall_hyps; eauto using pbit_disjoint_typed.
Qed.
Lemma pbit_disjoint_indetified xb1 xb2 :
  xb1 ⊥ xb2 → pbit_indetify xb1 = xb1 → sep_unmapped xb2 →
  pbit_indetify xb2 = xb2.
Proof. destruct xb1, xb2; intros (?&?&?&?) ? [??]; naive_solver. Qed.
Lemma pbits_disjoint_indetified xbs1 xbs2 :
  xbs1 ⊥* xbs2 → pbit_indetify <$> xbs1 = xbs1 → Forall sep_unmapped xbs2 →
  pbit_indetify <$> xbs2 = xbs2.
Proof.
  induction 1; intros; decompose_Forall_hyps'; f_equal;
    eauto using pbit_disjoint_indetified.
Qed.
Lemma pbit_full_valid Γ m alloc : ✓{Γ,m} (pbit_full alloc).
Proof. by destruct alloc; apply (bool_decide_unpack _). Qed.
Lemma pbit_full_unshared alloc : sep_unshared (pbit_full alloc).
Proof. by destruct alloc; apply (bool_decide_unpack _). Qed.
Lemma pbit_freed_valid Γ m : ✓{Γ,m} pbit_freed.
Proof. by apply (bool_decide_unpack _). Qed.
Lemma pbit_freed_unshared : sep_unshared pbit_freed.
Proof. by apply (bool_decide_unpack _). Qed.
Lemma pbits_perm_union xbs1 xbs2 :
  tagged_perm <$> xbs1 ∪* xbs2
  = (tagged_perm <$> xbs1) ∪* (tagged_perm <$> xbs2).
Proof. revert xbs2. induction xbs1; intros [|??]; f_equal'; auto. Qed.
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
  induction Hbs; intros; decompose_Forall_hyps'; eauto using PBit_perm_disjoint.
Qed.
Lemma PBits_union xs1 xs2 bs :
  zip_with PBit (xs1 ∪* xs2) bs
  = zip_with PBit xs1 bs ∪* (flip PBit BIndet <$> xs2).
Proof.
  revert xs2 bs. induction xs1; intros [|??] [|??]; f_equal'; auto.
  by unfold union at 2,  sep_union at 2; simplify_option_equality.
Qed.
Lemma PBits_BIndet_union xs1 xs2 :
  flip PBit (@BIndet Ti) <$> xs1 ∪* xs2
  = (flip PBit BIndet <$> xs1) ∪* (flip PBit BIndet <$> xs2).
Proof. revert xs2. induction xs1; intros [|??]; f_equal'; eauto. Qed.
Lemma PBits_BIndet_tag xbs :
  Forall sep_unmapped xbs →
  flip PBit BIndet <$> tagged_perm <$> xbs = xbs.
Proof. induction 1 as [|[] ? [??]]; simplify_equality'; f_equal; auto. Qed.

Lemma pbits_locked_union xbs1 xbs2 :
  xbs1 ⊥* xbs2 → pbit_locked <$> xbs1 ∪* xbs2
  = (pbit_locked <$> xbs1) ||* (pbit_locked <$> xbs2).
Proof.
  assert (∀ x1 x2, x1 ⊥ x2 →
    perm_locked (x1 ∪ x2) = perm_locked x1 || perm_locked x2).
  { intros [[]|] [[]|]; repeat sep_unfold; naive_solver. }
  unfold pbit_locked. induction 1 as [|???? (?&?&?&?)]; f_equal'; auto.
Qed.
Lemma pbits_locked_unmapped xbs :
  Forall sep_unmapped xbs → Forall sep_unmapped (pbit_locked <$> xbs).
Proof.
  assert (∀ x, sep_unmapped x → sep_unmapped (perm_locked x)).
  { intros [[[[]]|]|]; repeat sep_unfold; naive_solver. }
  unfold pbit_locked. induction 1 as [|?? []]; csimpl; auto.
Qed.
Lemma pbits_locks_unlock βs xbs :
  βs =.>* pbit_locked <$> xbs →
  pbit_locked <$> zip_with pbit_unlock_if xbs βs = (pbit_locked <$> xbs) ∖* βs.
Proof.
  revert βs. induction xbs as [|[[[]|]] ?]; intros [|[] ?] ?;
    decompose_Forall_hyps'; f_equal; auto.
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
Lemma pbits_unlock_empty_inv xbs βs :
  Forall (∅ =) (zip_with pbit_unlock_if xbs βs) → Forall sep_valid xbs →
  length xbs = length βs → Forall (∅ =) xbs.
Proof.
  assert (∀ x, sep_valid x → perm_unlock x = ∅ → x = ∅).
  { intros [[]|]; repeat sep_unfold; naive_solver. }
  intros Hxbs Hxbs'. revert βs Hxbs. induction Hxbs' as [|[] ? []];
    intros [|[] ?] ??; decompose_Forall_hyps'; constructor; eauto.
  sep_unfold; f_equal; eauto using eq_sym.
Qed.
Lemma pbits_unmapped_inv xbs βs :
  Forall sep_unmapped (zip_with pbit_unlock_if xbs βs) → Forall sep_valid xbs →
  length xbs = length βs → Forall sep_unmapped xbs.
Proof.
  intros Hxbs Hxbs'. revert βs Hxbs. induction Hxbs' as [|[] ? []]; sep_unfold;
    intros [|[] ?] ??; decompose_Forall_hyps'; constructor;
    intuition eauto using perm_unlock_unmapped_inv.
Qed.
Lemma pbits_unlock_if_valid Γ m xbs βs :
  ✓{Γ,m}* xbs → ✓{Γ,m}* (zip_with pbit_unlock_if xbs βs).
Proof.
  intros Hxs. revert βs.
  induction Hxs; intros [|[] ?]; simpl; auto using pbit_unlock_valid.
Qed.
Lemma pbit_indetify_unlock_if xbs βs :
  pbit_indetify <$> zip_with pbit_unlock_if xbs βs
  = zip_with pbit_unlock_if (pbit_indetify <$> xbs) βs.
Proof. revert βs. induction xbs; intros [|[] ?]; f_equal'; auto. Qed.
Lemma pbits_mapped_lock xbs :
  Forall (not ∘ sep_unmapped) xbs →
  Forall (not ∘ sep_unmapped) (pbit_lock <$> xbs).
Proof.
  sep_unfold. induction 1; constructor; simpl in *;
    intuition eauto using perm_lock_unmapped_inv.
Qed.
Lemma pbits_lock_valid Γ m xbs :
  ✓{Γ,m}* xbs → Forall (λ xb, Some Writable ⊆ pbit_kind xb) xbs →
  ✓{Γ,m}* (pbit_lock <$> xbs).
Proof.
  induction 1 as [|[??] ? (?&?&?)]; repeat constructor; decompose_Forall_hyps';
    eauto using perm_lock_valid, perm_lock_unmapped_inv.
Qed.

(** ** Refinements *)
Lemma pbit_refine_valid_l Γ f m1 m2 xb1 xb2 :
  ✓ Γ → xb1 ⊑{Γ,f@m1↦m2} xb2 → ✓{Γ,m1} xb1.
Proof.
  destruct xb1, xb2; intros ? (?&?&?&?); split;
    naive_solver eauto using BIndet_refine_r_inv, bit_refine_valid_l.
Qed.
Lemma pbits_refine_valid_l Γ f m1 m2 xbs1 xbs2 :
  ✓ Γ → xbs1 ⊑{Γ,f@m1↦m2}* xbs2 → ✓{Γ,m1}* xbs1.
Proof. induction 2; eauto using pbit_refine_valid_l. Qed.
Lemma pbit_refine_valid_r Γ f m1 m2 xb1 xb2 :
  ✓ Γ → xb1 ⊑{Γ,f@m1↦m2} xb2 → ✓{Γ,m2} xb2.
Proof.
  destruct xb1, xb2; intros ? (?&?&?&?); split;
      naive_solver eauto using BIndet_refine_r_inv, bit_refine_valid_r.
Qed.
Lemma pbits_refine_valid_r Γ f m1 m2 xbs1 xbs2 :
  ✓ Γ → xbs1 ⊑{Γ,f@m1↦m2}* xbs2 → ✓{Γ,m2}* xbs2.
Proof. induction 2; eauto using pbit_refine_valid_r. Qed.
Lemma pbit_refine_id Γ m xb : ✓{Γ,m} xb → xb ⊑{Γ@m} xb.
Proof. intros (?&?&?); split; eauto using bit_refine_id. Qed.
Lemma pbits_refine_id Γ m xbs : ✓{Γ,m}* xbs → xbs ⊑{Γ@m}* xbs.
Proof. induction 1; eauto using pbit_refine_id. Qed.
Lemma pbit_refine_compose Γ f1 f2 m1 m2 m3 xb1 xb2 xb3 :
  ✓ Γ → xb1 ⊑{Γ,f1@m1↦m2} xb2 → xb2 ⊑{Γ,f2@m2↦m3} xb3 →
  xb1 ⊑{Γ,f1 ◎ f2@m1↦m3} xb3.
Proof.
  destruct xb1, xb2, xb3; intros ? (?&?&?) (?&?&?); split;
    naive_solver eauto using bit_refine_compose.
Qed.
Lemma pbits_refine_compose Γ f1 f2 m1 m2 m3 xbs1 xbs2 xbs3 :
  ✓ Γ → xbs1 ⊑{Γ,f1@m1↦m2}* xbs2 → xbs2 ⊑{Γ,f2@m2↦m3}* xbs3 →
  xbs1 ⊑{Γ,f1 ◎ f2@m1↦m3}* xbs3.
Proof.
  intros ? Hxbs. revert xbs3. induction Hxbs; intros;
    decompose_Forall_hyps; eauto using pbit_refine_compose.
Qed.
Global Instance:
  PropHolds (✓ Γ) → Transitive (refine Γ mem_inj_id m m : relation (pbit Ti)).
Proof. intros Γ ?????. eapply @pbit_refine_compose; eauto; apply _. Qed.
Lemma pbit_refine_weaken Γ Γ' f f' m1 m2 m1' m2' pb1 pb2 :
  ✓ Γ → pb1 ⊑{Γ,f@m1↦m2} pb2 → Γ ⊆ Γ' → f ⊆ f' →
  (∀ o τ, m1 ⊢ o : τ → m1' ⊢ o : τ) → (∀ o τ, m2 ⊢ o : τ → m2' ⊢ o : τ) →
  pb1 ⊑{Γ',f'@m1'↦m2'} pb2.
Proof. intros ? (?&?&?&?); repeat split; eauto using bit_refine_weaken. Qed.
Lemma pbits_refine_perm Γ f m1 m2 xbs1 xbs2 :
  xbs1 ⊑{Γ,f@m1↦m2}* xbs2 → tagged_perm <$> xbs1 = tagged_perm <$> xbs2.
Proof. induction 1 as [|???? (?&?&?&?)]; f_equal'; auto. Qed.
Lemma pbit_refine_unmapped Γ f m1 m2 xb1 xb2 :
  sep_unmapped xb1 → xb1 ⊑{Γ,f@m1↦m2} xb2 → sep_unmapped xb2.
Proof. destruct xb1, xb2; intros [??] (?&?&?); split; naive_solver. Qed.
Lemma pbits_refine_unmapped Γ f m1 m2 xbs1 xbs2 :
  Forall sep_unmapped xbs1 → xbs1 ⊑{Γ,f@m1↦m2}* xbs2 → Forall sep_unmapped xbs2.
Proof.
  induction 2; decompose_Forall_hyps; eauto using pbit_refine_unmapped.
Qed.
Lemma pbit_refine_unmapped_inv Γ f m1 m2 xb1 xb2 :
  sep_unmapped xb2 → xb1 ⊑{Γ,f@m1↦m2} xb2 → sep_unmapped xb1.
Proof.
  intros [??] (?&?&?);
    split; eauto using (BIndet_refine_r_inv Γ f m1 m2) with congruence.
Qed.
Lemma pbits_refine_unmapped_inv Γ f m1 m2 xbs1 xbs2 :
  Forall sep_unmapped xbs2 → xbs1 ⊑{Γ,f@m1↦m2}* xbs2 → Forall sep_unmapped xbs1.
Proof.
  induction 2; decompose_Forall_hyps;
    eauto using pbit_refine_unmapped_inv.
Qed.
Lemma pbit_refine_unshared Γ f m1 m2 xb1 xb2 :
  sep_unshared xb1 → xb1 ⊑{Γ,f@m1↦m2} xb2 → sep_unshared xb2.
Proof.
  destruct xb1, xb2. intros [??] (?&?&?); split;
    naive_solver eauto using sep_unshared_valid.
Qed.
Lemma pbits_refine_unshared Γ f m1 m2 xbs1 xbs2 :
  Forall sep_unshared xbs1 → xbs1 ⊑{Γ,f@m1↦m2}* xbs2 → Forall sep_unshared xbs2.
Proof.
  induction 2; decompose_Forall_hyps; eauto using pbit_refine_unshared.
Qed.
Lemma pbit_refine_unshared_inv Γ f m1 m2 xb1 xb2 :
  sep_unshared xb2 → xb1 ⊑{Γ,f@m1↦m2} xb2 → sep_unshared xb1.
Proof.
  destruct xb1, xb2; intros [??] (?&?&?&?); split;
    naive_solver eauto using BIndet_refine_r_inv.
Qed.
Lemma pbits_refine_unshared_inv Γ f m1 m2 xbs1 xbs2 :
  Forall sep_unshared xbs2 → xbs1 ⊑{Γ,f@m1↦m2}* xbs2 → Forall sep_unshared xbs1.
Proof.
  induction 2; decompose_Forall_hyps;
    eauto using pbit_refine_unshared_inv.
Qed.
Lemma pbit_empty_refine Γ f m1 m2 : (∅ : pbit Ti) ⊑{Γ,f@m1↦m2} ∅.
Proof. split; simpl; auto using BIndet_BIndet_refine, sep_empty_valid. Qed.
Lemma PBit_refine Γ f m1 m2 x b1 b2 :
  sep_valid x → ¬sep_unmapped x →
  b1 ⊑{Γ,f@m1↦m2} b2 → PBit x b1 ⊑{Γ,f@m1↦m2} PBit x b2.
Proof. split; naive_solver eauto using BBit_refine. Qed.
Lemma PBits_refine Γ f m1 m2 xs bs1 bs2 :
  Forall sep_valid xs → Forall (not ∘ sep_unmapped) xs →
  bs1 ⊑{Γ,f@m1↦m2}* bs2 →
  zip_with PBit xs bs1 ⊑{Γ,f@m1↦m2}* zip_with PBit xs bs2.
Proof.
  intros Hxs Hxs' Hbs. revert xs Hxs Hxs'. induction Hbs; intros ? [|????] ?;
    decompose_Forall_hyps'; eauto using PBit_refine.
Qed.
Lemma PBit_BIndet_refine Γ f m1 m2 x :
  sep_valid x → PBit x BIndet ⊑{Γ,f@m1↦m2} PBit x BIndet.
Proof. repeat split; auto using BIndet_BIndet_refine. Qed.
Lemma PBits_BIndet_refine Γ f m1 m2 xs :
  Forall sep_valid xs →
  flip PBit BIndet <$> xs ⊑{Γ,f@m1↦m2}* flip PBit BIndet <$> xs.
Proof. induction 1; csimpl; auto using PBit_BIndet_refine. Qed.
Lemma PBit_BIndet_refine_l Γ m xb :
  ✓{Γ,m} xb → PBit (tagged_perm xb) BIndet ⊑{Γ@m} xb.
Proof. intros (?&?&?); split; naive_solver eauto using BIndet_refine. Qed.
Lemma PBits_BIndet_refine_l Γ m xbs :
  ✓{Γ,m}* xbs → flip PBit BIndet <$> tagged_perm <$> xbs ⊑{Γ@m}* xbs.
Proof. induction 1; csimpl; eauto using PBit_BIndet_refine_l. Qed.
Lemma PBit_unshared x b :
  sep_unshared x → ¬sep_unmapped x → sep_unshared (PBit x b).
Proof. by repeat split. Qed.
Lemma PBits_unshared xs bs :
  Forall sep_unshared xs → Forall (not ∘ sep_unmapped) xs →
  Forall sep_unshared (zip_with PBit xs bs).
Proof.
  revert xs. induction bs; intros ? [|????] ?;
    decompose_Forall_hyps'; auto using PBit_unshared.
Qed.
Lemma pbit_tag_refine Γ f m1 m2 xb1 xb2 :
  xb1 ⊑{Γ,f@m1↦m2} xb2 → tagged_tag xb1 ⊑{Γ,f@m1↦m2} tagged_tag xb2.
Proof. by intros []. Qed.
Lemma pbits_tag_refine Γ f m1 m2 xbs1 xbs2 :
  xbs1 ⊑{Γ,f@m1↦m2}* xbs2 →
  tagged_tag <$> xbs1 ⊑{Γ,f@m1↦m2}* tagged_tag <$> xbs2.
Proof. induction 1; constructor; auto using pbit_tag_refine. Qed.
Lemma pbit_unlock_refine Γ f m1 m2 xb1 xb2 :
  xb1 ⊑{Γ,f@m1↦m2} xb2 → pbit_unlock xb1 ⊑{Γ,f@m1↦m2} pbit_unlock xb2.
Proof.
  destruct xb1, xb2; intros (?&?&?&?); split;
    try naive_solver eauto using perm_unlock_valid, perm_unlock_unmapped_inv.
Qed.
Lemma pbit_lock_refine Γ f m1 m2 xb1 xb2 :
  Some Writable ⊆ pbit_kind xb1 →
  xb1 ⊑{Γ,f@m1↦m2} xb2 → pbit_lock xb1 ⊑{Γ,f@m1↦m2} pbit_lock xb2.
Proof.
  destruct xb1, xb2; intros ? (?&?&?&?); split;
    try naive_solver eauto using perm_lock_unmapped_inv, perm_lock_valid.
Qed.
Lemma pbit_indetify_refine Γ f m1 m2 xb1 xb2 :
  xb1 ⊑{Γ,f@m1↦m2} xb2 → pbit_indetify xb1 ⊑{Γ,f@m1↦m2} pbit_indetify xb2.
Proof.
  destruct xb1, xb2; intros (?&?&?&?); split; eauto using BIndet_BIndet_refine.
Qed.
Lemma pbits_indetify_refine Γ f m1 m2 xbs1 xbs2 :
  xbs1 ⊑{Γ,f@m1↦m2}* xbs2 →
  pbit_indetify <$> xbs1 ⊑{Γ,f@m1↦m2}* pbit_indetify <$> xbs2.
Proof. induction 1; csimpl; auto using pbit_indetify_refine. Qed.
Lemma pbit_indetified_refine Γ f m1 m2 xb1 xb2 :
  pbit_indetify xb2 = xb2 → xb1 ⊑{Γ,f@m1↦m2} xb2 → pbit_indetify xb1 = xb1.
Proof.
  unfold pbit_indetify. destruct xb1, xb2; intros ? (?&?&?&?);
    simplify_equality'; f_equal; eauto using BIndet_refine_r_inv, eq_sym.
Qed.
Lemma pbits_indetified_refine Γ f m1 m2 xbs1 xbs2 :
  pbit_indetify <$> xbs2 = xbs2 →
  xbs1 ⊑{Γ,f@m1↦m2}* xbs2 → pbit_indetify <$> xbs1 = xbs1.
Proof.
  induction 2; simplify_equality'; f_equal; eauto using pbit_indetified_refine.
Qed.
Lemma pbit_refine_kind Γ f m1 m2 xb1 xb2 k :
  xb1 ⊑{Γ,f@m1↦m2} xb2 → k ⊆ pbit_kind xb1 → k ⊆ pbit_kind xb2.
Proof. unfold pbit_kind; intros (?&?&?&?); simpl; congruence. Qed.
End properties.
