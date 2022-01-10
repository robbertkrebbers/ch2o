(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
From stdpp Require Import fin_maps natmap.
Require Export memory_separation.

Definition mem_singleton `{Env K} (Γ : env K) (Δ : memenv K) (a : addr K)
    (μ : bool) (γ : perm) (v : val K) (τ : type K) (m : mem K) : Prop := ∃ w,
  v = to_val Γ w ∧ m = cmap_singleton Γ a μ w ∧
  (Γ,Δ) ⊢ w : τ ∧ ctree_Forall (λ γb, tagged_perm γb = γ) w ∧
  (Γ,Δ) ⊢ a : TType τ ∧ addr_is_obj a ∧ addr_strict Γ a ∧ γ ≠ ∅.

Section mem_singleton.
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

Ltac solve_length := repeat first 
  [ rewrite take_length | rewrite drop_length | rewrite app_length
  | rewrite zip_with_length | rewrite replicate_length | rewrite resize_length
  | rewrite fmap_length | erewrite ctree_flatten_length by eauto ]; lia.
Hint Extern 0 (length _ = _) => solve_length: core.
Hint Extern 0 (_ ≤ length _) => solve_length: core.
Hint Extern 0 (length _ ≤ _) => solve_length: core.

Lemma mem_singleton_valid Γ Δ m a μ γ v τ :
  ✓ Γ → ✓{Γ} Δ → γ ≠ ∅ →
  mem_singleton Γ Δ a μ γ v τ m → index_alive Δ (addr_index a) → ✓{Γ,Δ} m.
Proof.
  intros ??? (w&->&->&?&?&?&?&?&?) ?; eapply cmap_singleton_valid; eauto.
  eapply ctree_Forall_not, Forall_impl; eauto; by intros ? <- <-.
Qed.
Lemma mem_singleton_typed_addr_typed Γ Δ m a μ γ v τ :
  mem_singleton Γ Δ a μ γ v τ m → (Γ,Δ) ⊢ a : TType τ.
Proof. by intros (?&?&?&?&?&?&?). Qed.
Lemma mem_erase_singleton Γ Δ m a μ γ v τ :
  mem_singleton Γ Δ a μ γ v τ m → cmap_erase m = m.
Proof. intros (w&->&->&_). apply cmap_erase_singleton. Qed.
Lemma mem_singleton_weaken Γ1 Γ2 Δ1 Δ2 m a μ γ v τ :
  ✓ Γ1 → Γ1 ⊆ Γ2 → Δ1 ⇒ₘ Δ2 →
  mem_singleton Γ1 Δ1 a μ γ v τ m → mem_singleton Γ2 Δ2 a μ γ v τ m.
Proof.
  intros ??? (w&->&->&?&?&?&?&?&?).
  exists w; eauto 15 using cmap_singleton_weaken,
    addr_strict_weaken, to_val_weaken, ctree_typed_weaken, addr_typed_weaken.
Qed.
Lemma mem_lookup_singleton Γ Δ m a μ γ v τ :
  ✓ Γ → Some Readable ⊆ perm_kind γ →
  mem_singleton Γ Δ a μ γ v τ m → m !!{Γ} a = Some v.
Proof.
  intros ?? (w&->&->&?&?&?&?&?&?); unfold lookupE, mem_lookup; simpl.
  assert (¬ctree_unmapped w).
  { eapply ctree_Forall_not, Forall_impl; eauto.
    intros ? <-; eauto using pbit_mapped. }
  erewrite cmap_lookup_singleton by eauto; simpl.
  by rewrite option_guard_True by (eapply Forall_impl; naive_solver).
Qed.
Lemma mem_writable_singleton Γ Δ m a μ γ v τ :
  ✓ Γ → Some Writable ⊆ perm_kind γ →
  mem_singleton Γ Δ a μ γ v τ m → mem_writable Γ a m.
Proof.
  intros ?? (w&_&->&?&?&?&?&?&?); eexists w; split.
  { assert (¬ctree_unmapped w).
    { eapply ctree_Forall_not, Forall_impl; eauto.
      by intros ? <-; apply pbit_mapped; transitivity (Some Writable). }
    by erewrite cmap_lookup_singleton by eauto. }
  eapply Forall_impl; naive_solver.
Qed.
Lemma mem_singleton_forced Γ Δ m a μ γ v τ :
  ✓ Γ → Some Readable ⊆ perm_kind γ →
  mem_singleton Γ Δ a μ γ v τ m → mem_forced Γ a m.
Proof.
  intros ?? (w&_&->&?&?&?&?&?&?); assert (¬ctree_unmapped w).
  { eapply ctree_Forall_not, Forall_impl; eauto.
    intros ? <-; eauto using pbit_mapped. }
  by apply (cmap_alter_ref_singleton _ Δ id _ _ _ τ).
Qed.
Lemma mem_insert_singleton Γ Δ m a μ γ v1 v2 τ :
  ✓ Γ → Some Writable ⊆ perm_kind γ →
  mem_singleton Γ Δ a μ γ v1 τ m → (Γ,Δ) ⊢ v2 : τ →
  mem_singleton Γ Δ a μ γ (freeze true v2) τ (<[a:=v2]{Γ}>m).
Proof.
  intros ?? (w&_&->&?&Hperm&?&?&?&?) ?.
  assert (¬ctree_unmapped w).
  { eapply ctree_Forall_not, Forall_impl; eauto.
    by intros ? <-; apply pbit_mapped; transitivity (Some Writable). }
  assert ((Γ, Δ) ⊢ of_val Γ (tagged_perm <$> ctree_flatten w) v2 : τ).
  { eapply of_val_typed; eauto using pbits_valid_perm_valid, ctree_flatten_valid.
    eapply pbits_perm_mapped, Forall_impl;
      eauto using @ctree_valid_Forall, ctree_typed_sep_valid.
    by intros ? <-; apply pbit_mapped; transitivity (Some Writable). }
  assert (ctree_Forall (λ γb, Some Writable ⊆ pbit_kind γb) w).
  { eapply Forall_impl; naive_solver. }
  exists (of_val Γ (tagged_perm <$> ctree_flatten w) v2); split_and ?; auto.
  * symmetry; eapply to_of_val; eauto.
  * by unfold insertE, mem_insert; erewrite cmap_alter_singleton
      by eauto using ctree_Forall_not, of_val_flatten_mapped.
  * erewrite ctree_flatten_of_val by eauto. generalize (val_flatten Γ v2).
    elim Hperm; [|intros ?????]; intros [|??]; constructor; auto.
Qed.
Lemma mem_freeable_perm_singleton Γ Δ m o μ v τ :
  mem_singleton Γ Δ (addr_top o τ) μ perm_full v τ m →
  mem_freeable_perm o μ m.
Proof. by intros (w&_&->&?&?&?&?&?); exists w; simplify_map_eq. Qed.
Lemma mem_locks_singleton_empty Γ Δ m a μ γ v τ :
  ✓ Γ → perm_locked γ = false →
  mem_singleton Γ Δ a μ γ v τ m → mem_locks m = ∅.
Proof.
  intros ?? (w&_&->&?&?&?&?&?&?); apply elem_of_equiv_empty_L; intros [o i].
  assert (τ = addr_type_base a) by eauto using addr_is_obj_type; subst.
  rewrite elem_of_mem_locks;
    destruct (decide (o = addr_index a)); simplify_map_eq; [|tauto].
  erewrite ctree_singleton_flatten by eauto using addr_typed_ref_typed.
  rewrite <-list_lookup_fmap, !fmap_app, !fmap_replicate, !lookup_app_Some,
    !lookup_replicate, list_lookup_fmap, fmap_Some; unfold pbit_locked.
  intros [[??]|[_ [(?&?&?)|(?&?&?)]]]; decompose_Forall_hyps; congruence.
Qed.
Lemma mem_locks_singleton Γ Δ m a μ γ v τ :
  ✓ Γ → perm_locked γ = true →
  mem_singleton Γ Δ a μ γ v τ m → mem_locks m = lock_singleton Γ a.
Proof.
  intros ?? (w&_&->&?&?&?&?&?&?); apply set_eq; intros [o i].
  assert (τ = addr_type_base a) by eauto using addr_is_obj_type; subst.
  rewrite elem_of_lock_singleton, elem_of_mem_locks;
    destruct (decide (o = addr_index a)); simplify_map_eq; [|tauto].
  erewrite ctree_singleton_flatten by eauto using addr_typed_ref_typed.
  erewrite addr_object_offset_alt, addr_is_obj_ref_byte,
    Nat.mul_0_l, Nat.add_0_r by eauto.
  erewrite <-list_lookup_fmap, !fmap_app, !fmap_replicate, !lookup_app_Some,
    !lookup_replicate, replicate_length, fmap_length, list_lookup_fmap,
    fmap_Some by done; simplify_type_equality.
  split.
  * intros [[??]|[? [(?&Hi&_)|(?&?&?)]]]; simplify_equality'.
    apply lookup_lt_Some in Hi; erewrite !ctree_flatten_length in Hi by eauto.
    auto with lia.
  * intros (_&?&?); right; split; [done|left].
    destruct (lookup_lt_is_Some_2 (ctree_flatten w)
      (i - ref_object_offset Γ (addr_ref Γ a))) as [x' Hx']; eauto.
    { erewrite !ctree_flatten_length by eauto; simplify_equality'; lia. }
    decompose_Forall_hyps; rewrite Hx'; eauto.
Qed.
Lemma mem_lock_singleton Γ Δ m a μ γ v τ :
  ✓ Γ → Some Writable ⊆ perm_kind γ →
  mem_singleton Γ Δ a μ γ v τ m →
  mem_singleton Γ Δ a μ (perm_lock γ) v τ (mem_lock Γ a m).
Proof.
  intros ?? (w&->&->&?&?&?&?&?&?); exists (ctree_map pbit_lock w).
  assert (¬ctree_unmapped w) as Hunmap.
  { eapply ctree_Forall_not, Forall_impl; eauto.
    by intros ? <-; apply pbit_mapped; transitivity (Some Writable). }
  split_and ?; auto using perm_lock_empty.
  * by rewrite to_val_ctree_map by done.
  * eapply cmap_alter_singleton; eauto.
    rewrite ctree_flatten_map, Forall_fmap; contradict Hunmap.
    eauto using Forall_impl, pbit_lock_mapped.
  * eapply ctree_map_typed; eauto using pbit_lock_mapped, pbit_lock_indetified.
    eapply pbits_lock_valid, Forall_impl;
      naive_solver eauto using ctree_flatten_valid.
  * rewrite ctree_flatten_map, Forall_fmap; eapply Forall_impl; naive_solver.
Qed.
Lemma mem_unlock_singleton Γ Δ m a μ γ v τ :
  ✓ Γ → perm_locked γ = true → mem_singleton Γ Δ a μ γ v τ m →
  mem_singleton Γ Δ a μ (perm_unlock γ) v τ (mem_unlock (lock_singleton Γ a) m).
Proof.
  intros ?? (w&->&->&?&?&?&?&?&?).
  assert (¬ctree_unmapped w) as Hunmap.
  { eapply ctree_Forall_not, Forall_impl; eauto.
    intros ? <- [??]; eapply perm_locked_mapped; eauto. }
  assert (τ = addr_type_base a) by eauto using addr_is_obj_type; subst.
  unfold mem_unlock, cmap_singleton, lock_singleton.
  destruct (decide _) as [|[]]; simplify_type_equality'; f_equal'.
  * exists (ctree_map pbit_unlock w); split_and ?; eauto.
    + by rewrite to_val_ctree_map by done.
    + assert (ref_object_offset Γ (addr_ref Γ a) +
        bit_size_of Γ (addr_type_base a) ≤ bit_size_of Γ (addr_type_object a)).
      { eauto using ref_object_offset_size', addr_typed_ref_typed. }
      erewrite merge_singleton by done.
      erewrite ctree_flatten_length, natset_to_bools_to_natset
        by eauto using ctree_singleton_typed, addr_typed_ref_typed.
      assert (∀ (γb : pbit K) β,
        sep_valid γb → sep_unmapped (pbit_unlock_if γb β) → sep_unmapped γb).
      { intros ? []; eauto using pbit_unlock_mapped. }
      erewrite ctree_merge_singleton, addr_object_offset_alt,
        addr_is_obj_ref_byte, ?resize_ge, <-?(assoc_L (++)),
        ?drop_app_alt, ?take_app_alt by eauto using addr_typed_ref_typed,
        pbit_unlock_if_empty, replicate_length.
      by erewrite (ctree_merge_map _ pbit_unlock) by (rewrite
        ?zip_with_replicate_r by auto; eauto using pbit_unlock_if_empty).
    + eapply ctree_map_typed; eauto using pbit_unlock_mapped, pbit_valid_sep_valid.
      { eapply Forall_fmap, Forall_impl,
          pbit_unlock_valid; eauto using ctree_flatten_valid. }
      by intros [] ?; simplify_equality'.
    + rewrite ctree_flatten_map, Forall_fmap; eapply Forall_impl; naive_solver.
    + cut (sep_valid γ); auto using perm_unlock_empty.
      assert (length (ctree_flatten w) ≠ 0).
      { erewrite ctree_flatten_length by eauto;
        eauto using bit_size_of_ne_0, addr_typed_type_valid. }
      assert (✓{Γ,Δ}* (ctree_flatten w)) as Hw' by eauto using ctree_flatten_valid.
      destruct Hw'; decompose_Forall_hyps; eapply pbit_valid_sep_valid; eauto.
  * rewrite elem_of_equiv_empty_L;
      intros Htrue; apply (Htrue (addr_object_offset Γ a)).
    rewrite elem_of_bools_to_natset, lookup_app_r,
      replicate_length, Nat.sub_diag, lookup_replicate by auto.
    eauto using bit_size_of_pos, addr_typed_type_valid.
Qed.
Lemma mem_unlock_all_singleton Γ Δ m a μ γ v τ :
  ✓ Γ → perm_locked γ = true → mem_singleton Γ Δ a μ γ v τ m →
  mem_singleton Γ Δ a μ (perm_unlock γ) v τ (mem_unlock_all m).
Proof.
  intros. erewrite mem_unlock_all_spec, mem_locks_singleton by eauto.
  eauto using mem_unlock_singleton.
Qed.
Lemma mem_unlock_all_singleton_unlocked Γ Δ m a μ γ v τ :
  ✓ Γ → perm_locked γ = false → mem_singleton Γ Δ a μ γ v τ m →
  mem_singleton Γ Δ a μ γ v τ (mem_unlock_all m).
Proof.
  intros. by erewrite mem_unlock_all_spec,
    mem_locks_singleton_empty, mem_unlock_empty by eauto.
Qed.
Lemma mem_alloc_singleton Γ Δ m o μ γ v τ :
  ✓ Γ → ✓{Γ,Δ} m → Δ ⊢ o : τ → index_alive Δ o → o ∉ dom indexset m →
  sep_valid γ → ¬sep_unmapped γ → (Γ,Δ) ⊢ v : τ → ∃ m',
  mem_alloc Γ o μ γ v m = m' ∪ m ∧ m' ## m ∧
  mem_singleton Γ Δ (addr_top o τ) μ γ (freeze true v) τ m'.
Proof.
  intros. exists (cmap_singleton Γ (addr_top o τ) μ
    (of_val Γ (replicate (bit_size_of Γ (type_of v)) γ) v)); split_and ?.
  * rewrite <-(sep_left_id m) at 1 by eauto using cmap_valid_sep_valid.
    by rewrite mem_alloc_union by done.
  * simplify_type_equality; assert ((Γ,Δ) ⊢
      of_val Γ (replicate (bit_size_of Γ τ) γ) v : τ).
    { apply of_val_typed; eauto using Forall_replicate, replicate_length. }
    eapply cmap_singleton_disjoint_l;
      eauto using addr_top_typed, addr_top_is_obj, addr_top_strict,
      val_typed_type_valid, mem_alloc_index_typed, cmap_valid_sep_valid,
      ctree_Forall_not, of_val_mapped, Forall_replicate.
    eauto using mem_alloc_memenv_valid,
      val_typed_type_valid, cmap_valid_memenv_valid.
  * simplify_type_equality.
    exists (of_val Γ (replicate (bit_size_of Γ τ) γ) v);
      split_and ?; eauto using of_val_typed, addr_top_typed, addr_top_is_obj,
      addr_top_strict, val_typed_type_valid, mem_alloc_index_typed,
      Forall_replicate, @sep_unmapped_empty_alt, to_of_val, eq_sym.
    erewrite ctree_flatten_of_val, zip_with_replicate_l
       by (by erewrite ?val_flatten_length by eauto; eauto).
    by apply Forall_fmap, Forall_true.
Qed.
Lemma mem_alloc_singleton_alt Γ Δ m o μ γ v τ :
  ✓ Γ → ✓{Γ,Δ} m → Δ !! o = None →
  sep_valid γ → ¬sep_unmapped γ → (Γ,Δ) ⊢ v : τ → frozen v → ∃ m',
  mem_alloc Γ o μ γ v m = m' ∪ m ∧ m' ## m ∧
  mem_singleton Γ (<[o:=(τ,false)]>Δ) (addr_top o τ) μ γ v τ m'.
Proof.
  intros ?????? Hfrozen; setoid_rewrite <-Hfrozen at 2.
  assert (Δ ⊆ <[o:=(τ, false)]> Δ) by (by apply insert_subseteq).
  apply mem_alloc_singleton; eauto using mem_alloc_index_typed, cmap_dom_None,
    mem_alloc_index_alive, val_typed_weaken, memenv_subseteq_forward,
    cmap_valid_weaken, mem_alloc_memenv_valid, val_typed_type_valid,
    cmap_valid_memenv_valid.
Qed.
Lemma mem_free_singleton Γ Δ m o a μ γ v τ :
  mem_singleton Γ Δ a μ γ v τ m →
  addr_index a = o → cmap_erase (mem_free o m) = ∅.
Proof.
  intros (w&_&->&?&?&?&?&?) <-. sep_unfold; f_equal'; apply map_empty; intros o.
  by destruct (decide (o = addr_index a)); simplify_map_eq.
Qed.
Lemma mem_singleton_union Γ Δ m1 m2 a μ γ1 γ2 v1 v2 v3 τ :
  ✓ Γ → m1 ## m2 → γ1 ## γ2 →
  (sep_unmapped γ1 → v3 = v2) →
  (¬sep_unmapped γ1 → v3 = v1) →
  mem_singleton Γ Δ a μ γ1 v1 τ m1 → mem_singleton Γ Δ a μ γ2 v2 τ m2 →
  mem_singleton Γ Δ a μ (γ1 ∪ γ2) v3 τ (m1 ∪ m2).
Proof.
  intros ??? Hv3 Hv3' (w1&Hv1&->&?&Hw1&?&?&?&?) (w2&Hv2&->&?&Hw2&_).
  assert (w1 ## w2) by eauto using cmap_singleton_disjoint_rev.
  assert (ctree_Forall (λ γb, tagged_perm γb = γ1 ∪ γ2) (w1 ∪ w2)).
  { rewrite ctree_flatten_union by done.
    revert Hw2; generalize (ctree_flatten w2).
    induction Hw1 as [|[]]; destruct 1 as [|[]]; simplify_equality'; eauto. }
  exists (w1 ∪ w2); split_and ?;
    eauto using ctree_union_typed, cmap_singleton_union, eq_sym.
  destruct (decide (sep_unmapped γ1)); rewrite ?Hv3, ?Hv3' by done; subst.
  * destruct (decide (sep_unmapped γ2)).
    + assert (sep_unmapped (γ1 ∪ γ2)) by eauto using @sep_unmapped_union_2'.
      assert (ctree_unmapped w1).
      { eapply pbits_perm_mapped', Forall_fmap, Forall_impl;
          naive_solver eauto using pbits_valid_sep_valid, ctree_flatten_valid. }
      assert (ctree_unmapped w2).
      { eapply pbits_perm_mapped', Forall_fmap, Forall_impl;
          naive_solver eauto using pbits_valid_sep_valid, ctree_flatten_valid. }
      by erewrite !to_val_unmapped
        by eauto using ctree_union_typed, @ctree_unmapped_union.
    + rewrite ctree_commutative by done.
      eapply to_val_subseteq; eauto using @ctree_union_subseteq_l.
      eapply Forall_impl; eauto; by intros ? <- [??].
  * eapply to_val_subseteq; eauto using @ctree_union_subseteq_l.
    eapply Forall_impl; eauto; by intros ? <- [??].
  * eauto using @sep_positive_l'.
Qed.
Lemma mem_singleton_union_rev Γ Δ m a μ γ1 γ2 v τ :
  ✓ Γ → γ1 ## γ2 → ¬sep_unmapped γ1 → ¬sep_unmapped γ2 →
  mem_singleton Γ Δ a μ (γ1 ∪ γ2) v τ m → ∃ m1 m2,
  m = m1 ∪ m2 ∧ m1 ## m2 ∧
  mem_singleton Γ Δ a μ γ1 v τ m1 ∧ mem_singleton Γ Δ a μ γ2 v τ m2.
Proof.
  intros ???? (w&->&->&?&?&?&?&?&?).
  assert (∀ γ, sep_valid γ → ¬sep_unmapped γ →
    (Γ,Δ) ⊢ ctree_map (λ γb, PBit γ (tagged_tag γb)) w : τ).
  { intros γ ??. apply ctree_map_typed; auto.
    + apply Forall_fmap; apply (Forall_impl (✓{Γ,Δ})); eauto using ctree_flatten_valid.
      by intros ? (?&?&?); split_and !.
    + by intros ?? [??].
    + by intros []; naive_solver. }
  set (w1 := ctree_map (λ γb, PBit γ1 (tagged_tag γb)) w).
  set (w2 := ctree_map (λ γb, PBit γ2 (tagged_tag γb)) w).
  assert ((Γ,Δ) ⊢ w1 : τ) by eauto using @sep_disjoint_valid_l.
  assert ((Γ,Δ) ⊢ w2 : τ) by eauto using @sep_disjoint_valid_r.
  assert (w1 ## w2).
  { eapply (ctree_disjoint_map (λ _, True)); sep_unfold;
      naive_solver eauto using Forall_true, ctree_typed_sep_valid. }
  assert (w = w1 ∪ w2) as Hw.
  { unfold w1, w2. erewrite ctree_union_map; symmetry.
    apply (ctree_map_id (λ γb, tagged_perm γb = γ1 ∪ γ2)); auto.
    by intros [] ?; sep_unfold; case_decide; naive_solver. }
  assert (bit_size_of Γ τ ≠ 0)
    by eauto using bit_size_of_ne_0, ctree_typed_type_valid.
  exists (cmap_singleton Γ a μ w1), (cmap_singleton Γ a μ w2); split_and ?.
  * by erewrite Hw, cmap_singleton_union by eauto.
  * eapply cmap_singleton_disjoint; eauto.
    + eapply ctree_Forall_not; eauto.
      unfold w1; rewrite ctree_flatten_map; apply Forall_fmap, Forall_true.
      sep_unfold; intros [] ?; naive_solver eauto using sep_unmapped_empty_alt.
    + eapply ctree_Forall_not; eauto.
      unfold w2; rewrite ctree_flatten_map; apply Forall_fmap, Forall_true.
      sep_unfold; intros [] ?; naive_solver eauto using sep_unmapped_empty_alt.
  * exists w1; rewrite Hw; split_and ?; eauto using @sep_unmapped_empty_alt.
    + symmetry; eapply to_val_subseteq; eauto using @ctree_union_subseteq_l.
      unfold w1; rewrite ctree_flatten_map; apply Forall_fmap, Forall_true.
      by intros ? [].
    + by unfold w1; rewrite ctree_flatten_map; apply Forall_fmap, Forall_true.
  * exists w2; rewrite Hw; split_and ?; eauto using @sep_unmapped_empty_alt.
    + symmetry; rewrite ctree_commutative by done.
      eapply to_val_subseteq; eauto using @ctree_union_subseteq_l.
      unfold w2; rewrite ctree_flatten_map; apply Forall_fmap, Forall_true.
      by intros ? [].
    + by unfold w2; rewrite ctree_flatten_map; apply Forall_fmap, Forall_true.
Qed.
Lemma mem_singleton_union_rev_unmapped Γ Δ m a μ γ1 γ2 v τ :
  ✓ Γ → γ1 ## γ2 → γ1 ≠ ∅ → γ2 ≠ ∅ → sep_unmapped γ2 →
  mem_singleton Γ Δ a μ (γ1 ∪ γ2) v τ m → ∃ m1 m2,
  m = m1 ∪ m2 ∧ m1 ## m2 ∧
  mem_singleton Γ Δ a μ γ1 v τ m1 ∧ mem_singleton Γ Δ a μ γ2 (val_new Γ τ) τ m2.
Proof.
  intros ????? (w&->&->&Hw&Hx&?&?&?&_).
  assert (✓{Γ,Δ}* (ctree_flatten w)) as Hw' by eauto using ctree_flatten_valid.
  set (w1 := ctree_map (PBit γ1 ∘ tagged_tag) w).
  set (w2 := ctree_new Γ (PBit γ2 BIndet) τ).
  assert ((Γ,Δ) ⊢ w1 : τ).
  { apply ctree_map_typed_alt; auto.
    + induction Hw' as [|[] ? (?&?&?)]; decompose_Forall_hyps; constructor;
        try split_and !; try constructor;
        eauto using sep_disjoint_valid_l, sep_unmapped_union_2'.
    + induction Hw' as [|[] ? (?&?&?)]; decompose_Forall_hyps; constructor; auto.
      intros [??]; split_and !; eauto using sep_unmapped_union_2'.
    + by intros []; naive_solver. }
  assert ((Γ,Δ) ⊢ w2 : τ).
  { eapply ctree_new_typed; eauto using ctree_typed_type_valid.
    split_and !; try constructor; eauto using sep_disjoint_valid_l, BIndet_valid. }
  assert (bit_size_of Γ τ ≠ 0 ∧ ✓{Γ} τ) as []
    by eauto using bit_size_of_ne_0, ctree_typed_type_valid.
  assert (ctree_unmapped w2).
  { unfold w2; rewrite ctree_flatten_new by eauto; by apply Forall_replicate. }
  assert (w1 ## w2).
  { symmetry; eapply ctree_flatten_unflatten_disjoint; eauto.
    + unfold w1; rewrite ctree_flatten_map.
      eapply Forall2_replicate_l, Forall_fmap; auto.
      induction Hw' as [|[] ? (?&?&?)]; decompose_Forall_hyps;
        constructor; try split_and !; eauto using sep_unmapped_union_2'.
    + by apply Forall_replicate; split_and !. }
  assert (w = w1 ∪ w2) as Hw12.
  { unfold w1, w2; rewrite <-ctree_merge_flatten, ctree_flatten_new by auto.
    erewrite (ctree_merge_map _ (flip union (PBit γ2 BIndet)))
      by (rewrite ?zip_with_replicate_r_eq by auto; auto).
    rewrite <-ctree_map_compose; symmetry.
    apply (ctree_map_id (λ γb, tagged_perm γb = γ1 ∪ γ2)); auto.
    by intros [] ?; sep_unfold; case_decide; simplify_equality'. }
  exists (cmap_singleton Γ a μ w1), (cmap_singleton Γ a μ w2); split_and ?.
  * by erewrite Hw12, cmap_singleton_union by eauto.
  * eapply cmap_singleton_disjoint; eauto.
    + eapply ctree_Forall_not; eauto.
      unfold w1; rewrite ctree_flatten_map; apply Forall_fmap, Forall_true.
      sep_unfold; intros [] ?; naive_solver eauto using sep_unmapped_empty_alt.
    + eapply ctree_Forall_not; eauto.
      unfold w2; rewrite ctree_flatten_new by eauto.
      apply Forall_replicate; sep_unfold; naive_solver.
  * exists w1; rewrite Hw12; split_and ?; eauto using @sep_unmapped_empty_alt.
    + destruct (decide (sep_unmapped γ1)).
      - assert (ctree_unmapped w1).
        { unfold w1; rewrite ctree_flatten_map; apply Forall_fmap.
        induction Hw' as [|[] ? (?&?&?)]; decompose_Forall_hyps;
          constructor; try split_and !; eauto using sep_unmapped_union_2'. }
        by erewrite !to_val_unmapped
          by eauto using @ctree_unmapped_union, ctree_union_typed.
      - symmetry; eapply to_val_subseteq; eauto using @ctree_union_subseteq_l.
        unfold w1; rewrite ctree_flatten_map; apply Forall_fmap, Forall_true.
        by intros ? [].
    + by unfold w1; rewrite ctree_flatten_map; apply Forall_fmap, Forall_true.
  * exists w2; split_and ?; eauto.
    + symmetry; eapply to_val_unmapped; eauto.
    + unfold w2; rewrite ctree_flatten_new by eauto; by apply Forall_replicate.
Qed.
End mem_singleton.
