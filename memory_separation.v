(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export memory memory_map_separation values_separation.

Section memory.
Context `{EnvSpec Ti}.
Implicit Types Γ : env Ti.
Implicit Types Γm : memenv Ti.
Implicit Types τ : type Ti.
Implicit Types a : addr Ti.
Implicit Types w : mtree Ti.
Implicit Types v : val Ti.
Implicit Types m : mem Ti.
Implicit Types Ω : lockset.

Local Arguments union _ _ !_ !_ /.
Hint Immediate cmap_lookup_typed val_typed_type_valid.
Hint Extern 0 (Separation _) => apply (_ : Separation (pbit Ti)).

Lemma mem_lookup_subseteq Γ Γm m1 m2 a v1 :
  ✓ Γ → ✓{Γ,Γm} m1 → m1 ⊆ m2 → m1 !!{Γ} a = Some v1 → m2 !!{Γ} a = Some v1.
Proof.
  unfold lookupE, mem_lookup; intros.
  destruct (m1 !!{Γ} a) as [w1|] eqn:?; simplify_option_equality.
  destruct (cmap_lookup_subseteq Γ m1 m2 a w1) as (w2&->&?); simpl; auto.
  { eapply ctree_Forall_not; eauto using cmap_lookup_Some, pbits_mapped. }
  by erewrite option_guard_True, (to_val_subseteq _ _ w1 w2)
    by eauto using cmap_lookup_Some, pbits_mapped,
    pbits_kind_subseteq, @ctree_flatten_subseteq.
Qed.
Lemma mem_alloc_disjoint Γ m1 m2 o1 malloc τ1 :
  ✓ Γ → ✓{Γ} τ1 → m1 ⊥ m2 → mem_allocable o1 m2 →
  mem_alloc Γ o1 malloc τ1 m1 ⊥ m2.
Proof.
  destruct m1 as [m1], m2 as [m2]; simpl; intros ?? Hm ? o; specialize (Hm o).
  destruct (decide (o = o1));
    simplify_map_equality'; [|by destruct (m1 !! o), (m2 !! o)].
  eauto 10 using (ctree_Forall_not _ _ ('{CMap m1})), ctree_typed_sep_valid,
    (ctree_new_typed _ ('{CMap m1})), pbit_full_valid, ctree_new_Forall.
Qed.
Lemma mem_alloc_union Γ m1 m2 o1 malloc τ1 :
  mem_allocable o1 m2 →
  mem_alloc Γ o1 malloc τ1 (m1 ∪ m2) = mem_alloc Γ o1 malloc τ1 m1 ∪ m2.
Proof.
  destruct m1 as [m1], m2 as [m2]; intros; sep_unfold; f_equal'.
  by apply insert_union_with_l.
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
  m1 ⊥ m2 → mem_freeable_perm o1 m1 → mem_free o1 (m1 ∪ m2) = mem_free o1 m1 ∪ m2.
Proof.
  destruct m1 as [m1], m2 as [m2]; intros Hm (w1&?&?); sep_unfold; f_equal'.
  apply alter_union_with_l.
  * intros [] [] ??; do 2 f_equal'. specialize (Hm o1); simplify_map_equality'.
    intuition eauto using ctree_union_type_of.
  * intros [] ??; naive_solver.
Qed.
Lemma mem_force_disjoint Γ Γm1 m1 m2 a1 τ1 :
  ✓ Γ → ✓{Γ,Γm1} m1 → m1 ⊥ m2 →
  (Γ,Γm1) ⊢ a1 : Some τ1 → is_Some (m1 !!{Γ} a1) → mem_force Γ a1 m1 ⊥ m2.
Proof.
  unfold lookupE, mem_lookup, mem_force. intros ???? [??].
  destruct (m1 !!{Γ} a1) as [w1|] eqn:?; simplify_option_equality.
  eapply cmap_alter_disjoint; eauto using ctree_Forall_not, pbits_mapped.
Qed.
Lemma mem_force_disjoint_le Γ Γm m ms a v τ :
  ✓ Γ → ✓{Γ,Γm} m → (Γ,Γm) ⊢ a : Some τ → is_Some (m !!{Γ} a) →
  m :: ms ⊆⊥ mem_force Γ a m :: ms.
Proof.
  intros. apply sep_disjoint_cons_le_inj; intros m'.
  rewrite !sep_disjoint_list_double, !(symmetry_iff _ m').
  eauto using mem_force_disjoint.
Qed.
Lemma mem_force_union Γ Γm1 m1 m2 a1 v1 τ1 :
  ✓ Γ → ✓{Γ,Γm1} m1 → m1 ⊥ m2 →
  (Γ,Γm1) ⊢ a1 : Some τ1 → is_Some (m1 !!{Γ} a1) →
  mem_force Γ a1 (m1 ∪ m2) = mem_force Γ a1 m1 ∪ m2.
Proof.
  unfold lookupE, mem_lookup, mem_force. intros ???? [??].
  destruct (m1 !!{Γ} a1) as [w1|] eqn:?; simplify_option_equality.
  eapply cmap_alter_union; eauto using ctree_Forall_not, pbits_mapped.
Qed.
Lemma mem_writable_subseteq Γ Γm m1 m2 a v1 :
  ✓ Γ → ✓{Γ,Γm} m1 → m1 ⊆ m2 → mem_writable Γ a m1 → mem_writable Γ a m2.
Proof.
  intros ??? (w1&?&?).
  destruct (cmap_lookup_subseteq Γ m1 m2 a w1) as (w2&?&?); auto.
  { eauto using ctree_Forall_not,
      cmap_lookup_Some, pbits_mapped, pbits_kind_weaken. }
  exists w2; eauto using pbits_kind_subseteq, @ctree_flatten_subseteq.
Qed.
Lemma mem_insert_disjoint Γ Γm1 m1 m2 a1 v1 τ1 :
  ✓ Γ → ✓{Γ,Γm1} m1 → m1 ⊥ m2 →
  (Γ,Γm1) ⊢ a1 : Some τ1 → mem_writable Γ a1 m1 → (Γ,Γm1) ⊢ v1 : τ1 →
  <[a1:=v1]{Γ}>m1 ⊥ m2.
Proof.
  intros ???? (w1&?&?) ?. assert (ctree_unshared w1).
  { eapply pbits_unshared; eauto using pbits_kind_weaken,
      pbits_valid_sep_valid, ctree_flatten_valid. }
  assert (ctree_Forall (not ∘ sep_unmapped) w1).
  { eapply pbits_mapped; eauto using pbits_kind_weaken. }
  eapply cmap_alter_disjoint; eauto using of_val_flatten_typed,
    of_val_flatten_mapped, of_val_disjoint, ctree_Forall_not.
Qed.
Lemma mem_insert_disjoint_le Γ Γm m ms a v τ :
  ✓ Γ → ✓{Γ,Γm} m → (Γ,Γm) ⊢ a : Some τ → mem_writable Γ a m → (Γ,Γm) ⊢ v : τ →
  m :: ms ⊆⊥ <[a:=v]{Γ}>m :: ms.
Proof.
  intros. apply sep_disjoint_cons_le_inj; intros m'.
  rewrite !sep_disjoint_list_double, !(symmetry_iff _ m').
  eauto using mem_insert_disjoint.
Qed.
Lemma mem_insert_union Γ Γm1 m1 m2 a1 v1 τ1 :
  ✓ Γ → ✓{Γ,Γm1} m1 → m1 ⊥ m2 →
  (Γ,Γm1) ⊢ a1 : Some τ1 → mem_writable Γ a1 m1 → (Γ,Γm1) ⊢ v1 : τ1 →
  <[a1:=v1]{Γ}>(m1 ∪ m2) = <[a1:=v1]{Γ}>m1 ∪ m2.
Proof.
  intros ???? (w1&?&?) ?. assert (ctree_unshared w1).
  { eapply pbits_unshared; eauto using pbits_kind_weaken,
      pbits_valid_sep_valid, ctree_flatten_valid. }
  assert (ctree_Forall (not ∘ sep_unmapped) w1).
  { eapply pbits_mapped; eauto using pbits_kind_weaken. }
  eapply cmap_alter_union; eauto using of_val_flatten_typed,
    of_val_flatten_mapped, of_val_disjoint, of_val_union, ctree_Forall_not.
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
End memory.
