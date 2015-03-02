(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export memory memory_map_separation values_separation.
Require Import natmap.

Section memory.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types Δ : memenv K.
Implicit Types τ : type K.
Implicit Types a : addr K.
Implicit Types w : mtree K.
Implicit Types v : val K.
Implicit  Types m : mem K.
Implicit Types Ω : lockset.
Local Arguments union _ _ !_ !_ /.
Hint Immediate cmap_lookup_typed val_typed_type_valid.
Hint Extern 0 (Separation _) => apply (_ : Separation (pbit K)).

Ltac solve_length := repeat first 
  [ rewrite take_length | rewrite drop_length | rewrite app_length
  | rewrite zip_with_length | rewrite replicate_length | rewrite resize_length
  | rewrite fmap_length | erewrite ctree_flatten_length by eauto
  | erewrite val_flatten_length by eauto | rewrite to_bools_length
  | rewrite bit_size_of_char ]; lia.
Hint Extern 0 (length _ = _) => solve_length.
Hint Extern 0 (length _ ≤ _) => solve_length.
Hint Extern 0 (length _ ≠ _) => solve_length.

Lemma mem_lookup_subseteq Γ Δ m1 m2 a v1 :
  ✓ Γ → ✓{Γ,Δ} m1 → m1 ⊆ m2 → m1 !!{Γ} a = Some v1 → m2 !!{Γ} a = Some v1.
Proof.
  unfold lookupE, mem_lookup; intros.
  destruct (m1 !!{Γ} a) as [w1|] eqn:?; simplify_option_equality.
  destruct (cmap_lookup_subseteq Γ m1 m2 a w1) as (w2&->&?); simpl; auto.
  { eapply ctree_Forall_not; eauto using cmap_lookup_Some, pbits_mapped. }
  by erewrite option_guard_True, (to_val_subseteq _ _ w1 w2)
    by eauto using cmap_lookup_Some, pbits_mapped,
    pbits_kind_subseteq, @ctree_flatten_subseteq.
Qed.
Lemma mem_alloc_disjoint Γ Δ m1 m2 o1 malloc x v τ :
  ✓ Γ → sep_valid x → ¬sep_unmapped x → (Γ,Δ) ⊢ v : τ → 
  m1 ⊥ m2 → o1 ∉ dom indexset m2 → mem_alloc Γ o1 malloc x v m1 ⊥ m2.
Proof.
  rewrite mem_allocable_alt.
  destruct m1 as [m1], m2 as [m2]; simpl; intros ???? Hm ? o; specialize (Hm o).
  destruct (decide (o = o1)); simplify_map_equality';
    simplify_type_equality; [|by destruct (m1 !! o), (m2 !! o)].
  split; eauto 12 using ctree_typed_sep_valid, of_val_typed, Forall_replicate,
    ctree_Forall_not, Forall_impl, of_val_mapped, Forall_replicate,
    @sep_unmapped_empty_alt.
Qed.
Lemma mem_alloc_union Γ m1 m2 o1 malloc x v :
  o1 ∉ dom indexset m2 →
  mem_alloc Γ o1 malloc x v (m1 ∪ m2) = mem_alloc Γ o1 malloc x v m1 ∪ m2.
Proof.
  rewrite mem_allocable_alt; destruct m1 as [m1], m2 as [m2];
    intros; sep_unfold; f_equal'; by apply insert_union_with_l.
Qed.
Lemma mem_free_disjoint Γ m1 m2 o1 :
  m1 ⊥ m2 → mem_freeable_perm o1 m1 → mem_free o1 m1 ⊥ m2.
Proof.
  destruct m1 as [m1], m2 as [m2]; intros Hm (w1&?&?) o; specialize (Hm o).
  destruct (decide (o = o1));
    simplify_map_equality'; [|by destruct (m1 !! o), (m2 !! o)].
  destruct (m2 !! o1) as [[|w2]|];
    intuition; eauto using pbits_disjoint_full, @ctree_flatten_disjoint.
Qed.
Lemma mem_free_union m1 m2 o1 :
  m1 ⊥ m2 → mem_freeable_perm o1 m1 →
  mem_free o1 (m1 ∪ m2) = mem_free o1 m1 ∪ m2.
Proof.
  destruct m1 as [m1], m2 as [m2]; intros Hm (w1&?&?); sep_unfold; f_equal'.
  apply alter_union_with_l; [|intros [] ??; naive_solver].
  intros [] [|w2 ?] ??; do 2 f_equal';
    specialize (Hm o1); simplify_map_equality';
    naive_solver eauto using pbits_disjoint_full, @ctree_flatten_disjoint.
Qed.
Lemma mem_force_disjoint Γ Δ1 m1 m2 a1 τ1 :
  ✓ Γ → ✓{Γ,Δ1} m1 → m1 ⊥ m2 → is_Some (m1 !!{Γ} a1) → mem_force Γ a1 m1 ⊥ m2.
Proof.
  unfold lookupE, mem_lookup, mem_force, lookupE, cmap_lookup; intros ??? [??].
  destruct (m1 !!{Γ} _) as [w1|] eqn:?; case_option_guard; simplify_equality'.
  destruct (cmap_lookup_ref_Some Γ Δ1 m1 (addr_index a1) (addr_ref Γ a1) w1)
    as (τ&σ&?&?&?); auto.
  eapply cmap_alter_ref_disjoint; eauto.
  case_decide; simplify_equality'; case_option_guard; simplify_equality'.
  { eapply ctree_Forall_not; eauto using pbits_mapped. }
  destruct (w1 !!{Γ} _) as [w1'|] eqn:?; simplify_option_equality.
  intros ?; eapply (ctree_Forall_not _ _ _ w1');
    eauto using ctree_lookup_byte_Forall, pbit_unmapped_indetify,
    pbits_mapped, ctree_lookup_byte_typed.
Qed.
Lemma mem_force_disjoint_le Γ Δ m ms a v τ :
  ✓ Γ → ✓{Γ,Δ} m → (Γ,Δ) ⊢ a : TType τ → is_Some (m !!{Γ} a) →
  m :: ms ⊆⊥ mem_force Γ a m :: ms.
Proof.
  intros. apply sep_disjoint_cons_le_inj; intros m'.
  rewrite !sep_disjoint_list_double, !(symmetry_iff _ m').
  eauto using mem_force_disjoint.
Qed.
Lemma mem_force_union Γ Δ1 m1 m2 a1 :
  ✓ Γ → ✓{Γ,Δ1} m1 → m1 ⊥ m2 → is_Some (m1 !!{Γ} a1) →
  mem_force Γ a1 (m1 ∪ m2) = mem_force Γ a1 m1 ∪ m2.
Proof.
  unfold lookupE, mem_lookup, mem_force, lookupE, cmap_lookup; intros ??? [??].
  destruct (m1 !!{Γ} _) as [w1|] eqn:?; case_option_guard; simplify_equality'.
  destruct (cmap_lookup_ref_Some Γ Δ1 m1 (addr_index a1) (addr_ref Γ a1) w1)
    as (τ&σ&?&?&?); auto.
  eapply cmap_alter_ref_union; eauto.
  case_decide; simplify_equality'; case_option_guard; simplify_equality'.
  { eapply ctree_Forall_not; eauto using pbits_mapped. }
  destruct (w1 !!{Γ} _) as [w1'|] eqn:?; simplify_option_equality.
  intros ?; eapply (ctree_Forall_not _ _ _ w1');
    eauto using ctree_lookup_byte_Forall, pbit_unmapped_indetify,
    pbits_mapped, ctree_lookup_byte_typed.
Qed.
Lemma mem_forced_subseteq Γ Δ m1 m2 a :
  ✓ Γ → ✓{Γ,Δ} m1 → m1 ⊆ m2 → mem_forced Γ a m1 →
  is_Some (m1 !!{Γ} a) → mem_forced Γ a m2.
Proof.
  unfold mem_forced; rewrite sep_subseteq_spec'; intros ?? (m3&->&?) Hforced ?.
  by erewrite mem_force_union, Hforced by eauto.
Qed.
Lemma mem_writable_subseteq Γ Δ m1 m2 a v1 :
  ✓ Γ → ✓{Γ,Δ} m1 → m1 ⊆ m2 → mem_writable Γ a m1 → mem_writable Γ a m2.
Proof.
  intros ??? (w1&?&?).
  destruct (cmap_lookup_subseteq Γ m1 m2 a w1) as (w2&?&?); auto.
  { eauto using ctree_Forall_not,
      cmap_lookup_Some, pbits_mapped, pbits_kind_weaken. }
  exists w2; eauto using pbits_kind_subseteq, @ctree_flatten_subseteq.
Qed.
Lemma mem_insert_disjoint Γ Δ1 m1 m2 a1 v1 τ1 :
  ✓ Γ → ✓{Γ,Δ1} m1 → m1 ⊥ m2 →
  (Γ,Δ1) ⊢ a1 : TType τ1 → mem_writable Γ a1 m1 → (Γ,Δ1) ⊢ v1 : τ1 →
  <[a1:=v1]{Γ}>m1 ⊥ m2.
Proof.
  intros ???? (w1&?&?) ?. assert (ctree_unshared w1).
  { eapply pbits_unshared; eauto using pbits_kind_weaken,
      pbits_valid_sep_valid, ctree_flatten_valid. }
  assert (ctree_Forall (not ∘ sep_unmapped) w1).
  { eapply pbits_mapped; eauto using pbits_kind_weaken. }
  eapply cmap_alter_disjoint; eauto using of_val_flatten_typed,
    of_val_flatten_mapped, of_val_flatten_disjoint, ctree_Forall_not.
Qed.
Lemma mem_insert_disjoint_le Γ Δ m ms a v τ :
  ✓ Γ → ✓{Γ,Δ} m → (Γ,Δ) ⊢ a : TType τ → mem_writable Γ a m → (Γ,Δ) ⊢ v : τ →
  m :: ms ⊆⊥ <[a:=v]{Γ}>m :: ms.
Proof.
  intros. apply sep_disjoint_cons_le_inj; intros m'.
  rewrite !sep_disjoint_list_double, !(symmetry_iff _ m').
  eauto using mem_insert_disjoint.
Qed.
Lemma mem_insert_union Γ Δ1 m1 m2 a1 v1 τ1 :
  ✓ Γ → ✓{Γ,Δ1} m1 → m1 ⊥ m2 →
  (Γ,Δ1) ⊢ a1 : TType τ1 → mem_writable Γ a1 m1 → (Γ,Δ1) ⊢ v1 : τ1 →
  <[a1:=v1]{Γ}>(m1 ∪ m2) = <[a1:=v1]{Γ}>m1 ∪ m2.
Proof.
  intros ???? (w1&?&?) ?. assert (ctree_unshared w1).
  { eapply pbits_unshared; eauto using pbits_kind_weaken,
      pbits_valid_sep_valid, ctree_flatten_valid. }
  assert (ctree_Forall (not ∘ sep_unmapped) w1).
  { eapply pbits_mapped; eauto using pbits_kind_weaken. }
  eapply cmap_alter_union; eauto using of_val_flatten_typed, ctree_Forall_not,
    of_val_flatten_mapped, of_val_flatten_disjoint, of_val_flatten_union.
Qed.
Lemma mem_lock_disjoint Γ Δ1 m1 m2 a1 τ1 :
  ✓ Γ → ✓{Γ,Δ1} m1 → m1 ⊥ m2 →
  (Γ,Δ1) ⊢ a1 : TType τ1 → mem_writable Γ a1 m1 → mem_lock Γ a1 m1 ⊥ m2.
Proof.
  intros ???? (w1&?&Hw1).
  assert ((Γ,Δ1) ⊢ ctree_map pbit_lock w1 : τ1).
  { eapply ctree_map_typed; eauto using cmap_lookup_Some, pbits_lock_valid,
      pbit_lock_indetified, ctree_flatten_valid, pbit_lock_mapped. }
  eapply cmap_alter_disjoint; eauto.
  { eapply ctree_Forall_not; eauto; rewrite ctree_flatten_map.
    apply Forall_fmap; apply (Forall_impl (not ∘ sep_unmapped));
      eauto using pbits_mapped, pbits_kind_weaken, pbit_lock_mapped. }
  eauto 8 using @ctree_map_disjoint, @ctree_flatten_disjoint, Forall_true,
    pbit_lock_mapped, Forall_impl, pbit_lock_unmapped, pbits_lock_disjoint.
Qed.
Lemma mem_lock_disjoint_le Γ Δ m ms a τ :
  ✓ Γ → ✓{Γ,Δ} m → (Γ,Δ) ⊢ a : TType τ → mem_writable Γ a m →
  m :: ms ⊆⊥ mem_lock Γ a m :: ms.
Proof.
  intros. apply sep_disjoint_cons_le_inj; intros m'.
  rewrite !sep_disjoint_list_double, !(symmetry_iff _ m').
  eauto using mem_lock_disjoint.
Qed.
Lemma mem_lock_union Γ Δ1 m1 m2 a1 τ1 :
  ✓ Γ → ✓{Γ,Δ1} m1 → m1 ⊥ m2 →
  (Γ,Δ1) ⊢ a1 : TType τ1 → mem_writable Γ a1 m1 →
  mem_lock Γ a1 (m1 ∪ m2) = mem_lock Γ a1 m1 ∪ m2.
Proof.
  intros ???? (w1&?&Hw1).
  assert ((Γ,Δ1) ⊢ ctree_map pbit_lock w1 : τ1).
  { eapply ctree_map_typed; eauto using cmap_lookup_Some, pbits_lock_valid,
      pbit_lock_indetified, ctree_flatten_valid, pbit_lock_mapped. }
  eapply cmap_alter_union; eauto.
  * eapply ctree_Forall_not; eauto; rewrite ctree_flatten_map.
    apply Forall_fmap; apply (Forall_impl (not ∘ sep_unmapped));
      eauto using pbits_mapped, pbits_kind_weaken, pbit_lock_mapped.
  * eauto 8 using @ctree_map_disjoint, @ctree_flatten_disjoint, Forall_true,
      pbit_lock_mapped, Forall_impl, pbit_lock_unmapped, pbits_lock_disjoint.
  * intros w2 Hw; apply ctree_map_union;
      eauto using pbits_lock_disjoint, @ctree_flatten_disjoint.
    apply ctree_flatten_disjoint in Hw.
    elim Hw; intros; f_equal'; auto; apply pbit_lock_union.
Qed.
Lemma mem_locks_union m1 m2 :
  m1 ⊥ m2 → mem_locks (m1 ∪ m2) = mem_locks m1 ∪ mem_locks m2.
Proof.
  intros Hm. apply elem_of_equiv_L; intros [o i]; rewrite elem_of_union,
    !elem_of_mem_locks; destruct m1 as [m1], m2 as [m2]; simpl.
  rewrite lookup_union_with. specialize (Hm o). assert (∀ w1 w2,
    w1 ⊥ w2 → pbit_locked <$> ctree_flatten (w1 ∪ w2) !! i = Some true ↔
      pbit_locked <$> ctree_flatten w1 !! i = Some true
      ∨ pbit_locked <$> ctree_flatten w2 !! i = Some true).
  { intros w1 w2 ?. rewrite ctree_flatten_union, <-!list_lookup_fmap by done.
    assert (ctree_flatten w1 ⊥* ctree_flatten w2)
      by auto using @ctree_flatten_disjoint.
    rewrite pbits_locked_union, lookup_zip_with by done.
    set (βs1 := pbit_locked <$> ctree_flatten w1).
    set (βs2 := pbit_locked <$> ctree_flatten w2).
    assert (Forall2 (λ _ _, True) βs1 βs2).
    { eapply Forall2_fmap, Forall2_impl; eauto. }
    destruct (βs1 !! i) as [[]|] eqn:?, (βs2 !! i) as [[]|] eqn:?;
      decompose_Forall_hyps; intuition congruence. }
  destruct (m1 !! o) as [[]|], (m2 !! o) as [[]|]; naive_solver eauto 0.
Qed.
Lemma mem_locks_subseteq m1 m2 : m1 ⊆ m2 → mem_locks m1 ⊆ mem_locks m2.
Proof.
  rewrite !sep_subseteq_spec'; intros (m3&->&?).
  rewrite mem_locks_union by done. esolve_elem_of.
Qed.
Lemma ctree_unlock_disjoint w1 w2 βs :
  w1 ⊥ w2 → βs =.>* pbit_locked <$> ctree_flatten w1 →
  ctree_merge true pbit_unlock_if w1 βs ⊥ w2.
Proof.
  intros Hw Hβs. apply ctree_merge_disjoint; auto.
  * list.solve_length.
  * rewrite Forall2_fmap_r in Hβs.
    cut (Forall sep_valid (ctree_flatten w1));
      eauto using @ctree_valid_Forall, @ctree_disjoint_valid_l.
    induction Hβs as [|[] ?]; intros;
      decompose_Forall_hyps; auto using pbit_unlock_mapped.
  * rewrite Forall2_fmap_r in Hβs.
    induction Hβs as [|[] ?];
      constructor; csimpl; auto using pbit_unlock_unmapped.
  * eauto using pbits_unlock_disjoint, @ctree_flatten_disjoint.
Qed.
Lemma mem_unlock_disjoint m1 m2 Ω :
  m1 ⊥ m2 → Ω ⊆ mem_locks m1 → mem_unlock Ω m1 ⊥ m2.
Proof.
  intros Hm HΩm'.
  pose proof (λ o, mem_locks_subseteq_inv _ _ o HΩm') as HΩm; clear HΩm'.
  destruct m1 as [m1], m2 as [m2], Ω as [Ω ?]; intros o; simpl in *.
  specialize (Hm o); specialize (HΩm o). rewrite !lookup_merge by done.
  destruct (m1 !! o) as [[|w1 β1]|], (m2 !! o) as [[|w2 β2]|],
   (Ω !! o) as [ω|]; simplify_equality'; rewrite ?ctree_flatten_merge; try done.
  { intuition eauto using ctree_unlock_disjoint, pbits_unlock_empty_inv,
      to_bools_length, @ctree_disjoint_valid_l, @ctree_valid_Forall. }
  assert (Forall sep_valid (ctree_flatten w1))
    by intuition eauto using @ctree_disjoint_valid_l, @ctree_valid_Forall.
  intuition eauto using ctree_unlock_disjoint,
    pbits_unlock_empty_inv, to_bools_length.
  apply ctree_merge_valid; auto using to_bools_length, pbits_unlock_sep_valid.
  apply Forall2_lookup_2; auto using to_bools_length.
  intros ?? [] ??; decompose_Forall_hyps; eauto using pbit_unlock_mapped.
Qed.
Lemma mem_unlock_disjoint_le m ms Ω :
  Ω ⊆ mem_locks m → m :: ms ⊆⊥ mem_unlock Ω m :: ms.
Proof.
  intros. apply sep_disjoint_cons_le_inj; intros m'.
  rewrite !sep_disjoint_list_double, !(symmetry_iff _ m').
  eauto using mem_unlock_disjoint.
Qed.
Lemma ctree_unlock_union w1 w2 βs :
  w1 ⊥ w2 → βs =.>* pbit_locked <$> ctree_flatten w1 →
  ctree_merge true pbit_unlock_if (w1 ∪ w2) βs =
    ctree_merge true pbit_unlock_if w1 βs ∪ w2.
Proof.
  intros. apply ctree_merge_union; eauto using pbits_unlock_disjoint,
    pbits_unlock_union, @ctree_flatten_disjoint; list.solve_length.
Qed.
Lemma mem_unlock_union m1 m2 Ω :
  m1 ⊥ m2 → Ω ⊆ mem_locks m1 →
  mem_unlock Ω (m1 ∪ m2) = mem_unlock Ω m1 ∪ m2.
Proof.
  intros Hm HΩm'.
  pose proof (λ o, mem_locks_subseteq_inv _ _ o HΩm') as HΩm; clear HΩm'.
  destruct m1 as [m1], m2 as [m2], Ω as [Ω ?]; sep_unfold; f_equal'.
  apply map_eq; intros o; simpl in *; specialize (Hm o); specialize (HΩm o).
  rewrite lookup_merge, !lookup_union_with, lookup_merge by done.
  destruct (m1 !! o) as [[|w1 β1]|], (m2 !! o) as [[|w2 β2]|],
    (Ω !! o) as [ω|]; do 2 f_equal'; try done.
  rewrite ctree_flatten_union, zip_with_length_l_eq
    by naive_solver eauto using Forall2_length, @ctree_flatten_disjoint.
  intuition auto using ctree_unlock_union.
Qed.
Lemma mem_unlock_all_disjoint_le m ms : m :: ms ⊆⊥ mem_unlock_all m :: ms.
Proof. by apply mem_unlock_disjoint_le. Qed.
Lemma mem_unlock_all_disjoint m1 m2 :
  m1 ⊥ m2 → mem_unlock_all m1 ⊥ mem_unlock_all m2.
Proof.
  rewrite <-!sep_disjoint_list_double.
  intros. by rewrite <-!mem_unlock_all_disjoint_le.
Qed.
Lemma mem_unlock_all_union m1 m2 :
  m1 ⊥ m2 → mem_unlock_all (m1 ∪ m2) = mem_unlock_all m1 ∪ mem_unlock_all m2.
Proof.
  unfold mem_unlock_all; intros. assert (m1 ⊥ mem_unlock_all m2).
  { symmetry. by apply mem_unlock_disjoint. }
  by rewrite mem_locks_union, mem_unlock_union_locks, sep_commutative',
    mem_unlock_union, sep_commutative', mem_unlock_union
    by auto using mem_unlock_disjoint.
Qed.
Lemma mem_singleton_disjoint Γ Δ a malloc x1 x2 v τ :
  ✓ Γ → (Γ,Δ) ⊢ a : TType τ → addr_strict Γ a → (Γ,Δ) ⊢ v : τ →
  x1 ⊥ x2 → ¬sep_unmapped x1 → ¬sep_unmapped x2 →
  mem_singleton Γ a malloc x1 v ⊥ mem_singleton Γ a malloc x2 v.
Proof.
  intros. assert (bit_size_of Γ τ ≠ 0) by eauto using bit_size_of_ne_0.
  eapply cmap_singleton_disjoint; simplify_type_equality; eauto.
  * eapply of_val_disjoint; eauto using Forall2_replicate, Forall_replicate.
  * erewrite ctree_flatten_of_val, zip_with_replicate_l, Forall_fmap by eauto.
    apply Forall_not, Forall_true; auto; by destruct 1.
  * erewrite ctree_flatten_of_val, zip_with_replicate_l, Forall_fmap by eauto.
    apply Forall_not, Forall_true; auto; by destruct 1.
Qed.
Lemma mem_singleton_union Γ Δ a malloc x1 x2 v τ :
  ✓ Γ → (Γ,Δ) ⊢ a : TType τ → addr_strict Γ a →
  mem_singleton Γ a malloc (x1 ∪ x2) v
  = mem_singleton Γ a malloc x1 v ∪ mem_singleton Γ a malloc x2 v.
Proof.
  intros. unfold mem_singleton. by erewrite <-zip_with_replicate,
    of_val_union, cmap_singleton_union by eauto.
Qed.
Lemma mem_singleton_imap f Γ a malloc x vs :
  imap (λ i, mem_singleton Γ (f i a) malloc x) vs
  = imap (λ i, cmap_singleton Γ (f i a) malloc)
      ((λ v, of_val Γ (replicate (bit_size_of Γ (type_of v)) x) v) <$> vs).
Proof. unfold imap. generalize 0. induction vs; intros; f_equal'; auto. Qed.
Lemma mem_singleton_array_disjoint Γ Δ a malloc x vs n τ :
  ✓ Γ → (Γ,Δ) ⊢ a : TType (τ.[n]) → addr_strict Γ a → (Γ,Δ) ⊢* vs : τ → 
  length vs = n → sep_valid x → ¬sep_unmapped x →
  ⊥ imap (λ i, mem_singleton Γ (addr_elt Γ (RArray i τ n) a) malloc x) vs.
Proof.
  intros ??? Hvs Hn ??. rewrite (mem_singleton_imap (λ _, _)).
  eapply cmap_singleton_array_disjoint; eauto.
  * clear Hn. induction Hvs; simplify_type_equality';
      constructor; auto using of_val_typed, Forall_replicate.
  * clear Hn. induction Hvs; simplify_type_equality'; constructor; eauto 10
      using ctree_Forall_not, of_val_typed, Forall_replicate, of_val_mapped.
Qed.
Lemma mem_singleton_array_union Γ Δ a malloc x vs τ n :
  ✓ Γ → (Γ,Δ) ⊢ a : TType (τ.[n]) → addr_strict Γ a → (Γ,Δ) ⊢* vs : τ →
  length vs = n → sep_valid x → ¬sep_unmapped x →
  mem_singleton Γ a malloc x (VArray τ vs)
  = ⋃ imap (λ i, mem_singleton Γ (addr_elt Γ (RArray i τ n) a) malloc x) vs.
Proof.
  intros ??? Hvs Hn ??. rewrite (mem_singleton_imap (λ _, _)).
  assert ((Γ,Δ) ⊢* (λ v,
    of_val Γ (replicate (bit_size_of Γ (type_of v)) x) v) <$> vs : τ) as Hvs'.
  { clear Hn. induction Hvs; simplify_type_equality';
      constructor; auto using of_val_typed, Forall_replicate. }
  erewrite <-cmap_singleton_array_union by eauto.
  unfold mem_singleton; do 2 f_equal'. rewrite bit_size_of_array.
  clear Hvs' Hn; induction Hvs; simplify_type_equality'; f_equal';
    rewrite ?replicate_plus, ?take_app_alt, ?drop_app_alt by auto; eauto.
Qed.
Lemma mem_alloc_empty_singleton Γ o malloc x v τ :
  mem_alloc Γ o malloc x v ∅ = mem_singleton Γ (addr_top o τ) malloc x v.
Proof. done. Qed.
Lemma mem_alloc_singleton Γ m o malloc x v τ :
  o ∉ dom indexset m → sep_valid m →
  mem_alloc Γ o malloc x v m
  = mem_singleton Γ (addr_top o τ) malloc x v ∪ m.
Proof.
  intros. by rewrite <-mem_alloc_empty_singleton,
    <-mem_alloc_union, sep_left_id by done.
Qed.
Lemma mem_free_singleton Γ o a malloc x v :
  addr_index a = o → cmap_erase (mem_free o (mem_singleton Γ a malloc x v)) = ∅.
Proof.
  intros <-; sep_unfold; f_equal'; apply map_empty; intros o.
  by destruct (decide (o = addr_index a)); simplify_map_equality'.
Qed.
Lemma mem_free_singleton_union Γ o a malloc x v m :
  addr_index a = o →
  cmap_erase (mem_free o (mem_singleton Γ a malloc x v) ∪ m) = cmap_erase m.
Proof.
  destruct m as [m]; intros <-; sep_unfold; f_equal'; apply map_eq; intros o.
  destruct (decide (o = addr_index a)) as [->|].
  * rewrite !lookup_omap, lookup_union_with, lookup_alter, lookup_singleton.
    by destruct (m !! addr_index a) as [[]|].
  * rewrite !lookup_omap, lookup_union_with,
      lookup_alter_ne, lookup_singleton_ne by done.
    by destruct (m !! o) as [[]|].
Qed.
End memory.
