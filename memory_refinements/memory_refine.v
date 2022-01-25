(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
From stdpp Require Import fin_map_dom natmap.
Require Export memory memory_map_refine values_refine.
Local Open Scope ctype_scope.

Section map_of_collection.
  Context `{A, FinSet K C, FinMap K M}.
  
  Definition map_of_collection (f : K → option A) (X : C) : (M A) :=
    list_to_map (omap (λ i, (pair i) <$> f i) (elements X)).

  Lemma lookup_map_of_collection
    (f : K → option A) X i x :
    map_of_collection f X !! i = Some x ↔ i ∈ X ∧ f i = Some x.
  Proof.
    assert (NoDup (fst <$> omap (λ i, (pair i) <$> f i) (elements X))).
    { induction (NoDup_elements X) as [|i' l]; csimpl; [constructor|].
      destruct (f i') as [x'|]; csimpl; auto; constructor; auto.
      rewrite elem_of_list_fmap. setoid_rewrite elem_of_list_omap.
      by intros (?&?&?&?&?); simplify_option_eq. }
    unfold map_of_collection. rewrite <-elem_of_list_to_map by done.
    rewrite elem_of_list_omap. setoid_rewrite elem_of_elements; split.
    * intros (?&?&?); simplify_option_eq; eauto.
    * intros [??]; exists i; simplify_option_eq; eauto.
  Qed.
End map_of_collection.

#[global] Instance locks_refine `{Env K} :
    Refine K (env K) lockset := λ Γ α f Δ1 Δ2 Ω1 Ω2,
  (**i 1.) *) ✓{Γ,Δ1} Ω1 ∧ ✓{Γ,Δ2} Ω2 ∧
  (**i 2.) *) Δ1 ⊑{Γ,α,f} Δ2 ∧
  (**i 3.) *) (∀ o1 o2 r τ1 i,
    f !! o1 = Some (o2,r) → Δ1 ⊢ o1 : τ1 → index_alive Δ1 o1 →
    i < bit_size_of Γ τ1 →
    (o1,i) ∈ Ω1 ↔ (o2,ref_object_offset Γ r + i) ∈ Ω2).

Section memory.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types Δ : memenv K.
Implicit Types τ : type K.
Implicit Types a : addr K.
Implicit Types p : ptr K.
Implicit Types w : mtree K.
Implicit Types v : val K.
Implicit Types m : mem K.
Implicit Types α β : bool.
Implicit Types βs : list bool.
Implicit Types γb : pbit K.
Implicit Types γbs : list (pbit K).
Implicit Types Ω : lockset.

Hint Immediate ctree_refine_typed_l ctree_refine_typed_r: core.
Hint Immediate vals_refine_typed_l vals_refine_typed_r: core.
Hint Resolve Forall_app_2 Forall2_app: core.
Hint Immediate cmap_lookup_typed val_typed_type_valid: core.

Ltac solve_length := repeat first 
  [ rewrite take_length | rewrite drop_length | rewrite app_length
  | rewrite zip_with_length | rewrite replicate_length | rewrite resize_length
  | rewrite fmap_length | erewrite ctree_flatten_length by eauto
  | rewrite natset_to_bools_length 
  | match goal with H : Forall2 _ _ _ |- _ => apply Forall2_length in H end ];
  lia.
Hint Extern 0 (length _ = _) => solve_length: core.
Hint Extern 0 (_ ≤ length _) => solve_length: core.
Hint Extern 0 (length _ ≤ _) => solve_length: core.

Lemma mem_lookup_refine Γ α f Δ1 Δ2 m1 m2 a1 a2 v1 τ :
  ✓ Γ → m1 ⊑{Γ,α,f@Δ1↦Δ2} m2 → a1 ⊑{Γ,α,f@Δ1↦Δ2} a2 : TType τ →
  m1 !!{Γ} a1 = Some v1 →
  ∃ v2, m2 !!{Γ} a2 = Some v2 ∧ v1 ⊑{Γ,α,f@Δ1↦Δ2} v2 : τ.
Proof.
  unfold lookupE, mem_lookup. intros.
  destruct (m1 !!{Γ} a1) as [w1|] eqn:?; simplify_option_eq.
  destruct (cmap_lookup_refine Γ α f Δ1 Δ2
    m1 m2 a1 a2 w1 τ) as (w2&->&?); auto.
  exists (to_val Γ w2); simplify_option_eq by eauto using
    pbits_refine_kind_subseteq, ctree_flatten_refine; eauto using to_val_refine.
Qed.
Lemma mem_force_refine Γ α f Δ1 Δ2 m1 m2 a1 a2 τ :
  ✓ Γ → m1 ⊑{Γ,α,f@Δ1↦Δ2} m2 → a1 ⊑{Γ,α,f@Δ1↦Δ2} a2 : TType τ →
  is_Some (m1 !!{Γ} a1) → mem_force Γ a1 m1 ⊑{Γ,α,f@Δ1↦Δ2} mem_force Γ a2 m2.
Proof.
  unfold lookupE, mem_lookup, mem_force, lookupE, cmap_lookup.
  intros ??? [v1 ?]; case_option_guard; simplify_equality'.
  destruct (m1 !!{Γ} _) as [w1|] eqn:?; simplify_equality'.
  destruct (addr_ref_refine Γ α f Δ1 Δ2 a1 a2 (TType τ)) as (r&?&_&?); auto.
  destruct (cmap_lookup_ref_refine Γ α f Δ1 Δ2 m1 m2 (addr_index a1)
    (addr_ref Γ a1) (addr_index a2) r w1) as (w2&?&?); auto.
  erewrite <-(cmap_alter_ref_le _ _ _ _ (addr_ref Γ a2)) by eauto.
  eapply cmap_alter_ref_refine; eauto.
  case_decide; simplify_equality'; case_option_guard; simplify_equality'.
  { eapply ctree_Forall_not; eauto using pbits_mapped. }
  destruct (w1 !!{Γ} _) as [w1'|] eqn:?; simplify_option_eq.
  intros ?; eapply (ctree_Forall_not _ _ _ w1');
    eauto using ctree_lookup_byte_Forall, pbit_unmapped_indetify,
    pbits_mapped, ctree_lookup_byte_typed.
Qed.
Lemma mem_force_refine' Γ α f m1 m2 a1 a2 τ :
  ✓ Γ → m1 ⊑{Γ,α,f} m2 → a1 ⊑{Γ,α,f@'{m1}↦'{m2}} a2 : TType τ →
  is_Some (m1 !!{Γ} a1) → mem_force Γ a1 m1 ⊑{Γ,α,f} mem_force Γ a2 m2.
Proof.
  unfold refineM, cmap_refine'; intros ??? [v1 ?].
  destruct (mem_lookup_refine Γ α f '{m1} '{m2}
    m1 m2 a1 a2 v1 τ) as (v2&?&?); eauto.
  erewrite !mem_force_memenv_of by eauto using cmap_refine_valid_l',
    cmap_refine_valid_r'; eauto using mem_force_refine.
Qed.
Lemma mem_force_refine_l Γ Δ m a :
  ✓ Γ → ✓{Γ,Δ} m → is_Some (m !!{Γ} a) → frozen a →
  mem_force Γ a m ⊑{Γ,true@Δ} m.
Proof.
  intros ?? [v ?] ?.
  split; split_and ?; eauto using mem_force_valid, memenv_refine_id.
  intros ? o r w' μ'; rewrite lookup_meminj_id.
  destruct m as [m]; unfold lookupE, mem_lookup, lookupE, cmap_lookup in *;
    intros; simplify_equality'; case_option_guard; simplify_equality'.
  destruct (m !! addr_index a) as [[|w μ]|] eqn:?; simplify_equality'.
  destruct (w !!{Γ} addr_ref Γ a) as [w''|] eqn:?; simplify_equality'.
  destruct (decide (o = addr_index a)); simplify_map_eq.
  { destruct (cmap_valid_Obj Γ Δ (CMap m) (addr_index a) w μ')
      as (τ&?&_&?&_); eauto.
    assert (¬ctree_unmapped w'').
    { case_decide; simplify_equality'; case_option_guard; simplify_equality'.
      { eapply ctree_Forall_not;
          eauto using pbits_mapped, ctree_lookup_Some_type_of. }
      destruct (w'' !!{Γ} addr_ref_byte Γ a)
        as [w'''|] eqn:?; simplify_option_eq.
      intros ?; eapply (ctree_Forall_not _ _ _ w''');
        eauto using ctree_lookup_byte_Forall, pbit_unmapped_indetify,
        pbits_mapped, ctree_lookup_byte_typed, ctree_lookup_Some_type_of. }
    assert (freeze true <$> addr_ref Γ a = addr_ref Γ a).
    { rewrite <-addr_ref_freeze. by f_equal. }
    eauto 10 using ctree_alter_id_refine. }
  destruct (cmap_valid_Obj Γ Δ (CMap m) o w' μ')
    as (τ&?&_&?&_); eauto 10 using ctree_refine_id.
Qed.
Lemma mem_writable_refine Γ α f Δ1 Δ2 m1 m2 a1 a2 τ :
  ✓ Γ → m1 ⊑{Γ,α,f@Δ1↦Δ2} m2 → a1 ⊑{Γ,α,f@Δ1↦Δ2} a2 : TType τ →
  mem_writable Γ a1 m1 → mem_writable Γ a2 m2.
Proof.
  intros ??? (w1&?&?). destruct (cmap_lookup_refine Γ α f Δ1 Δ2
    m1 m2 a1 a2 w1 τ) as (w2&?&?); auto.
  exists w2; eauto using pbits_refine_kind_subseteq, ctree_flatten_refine.
Qed.
Lemma mem_insert_refine Γ α f Δ1 Δ2 m1 m2 a1 a2 v1 v2 τ :
  ✓ Γ → m1 ⊑{Γ,α,f@Δ1↦Δ2} m2 → a1 ⊑{Γ,α,f@Δ1↦Δ2} a2 : TType τ →
  mem_writable Γ a1 m1 → v1 ⊑{Γ,α,f@Δ1↦Δ2} v2 : τ →
  <[a1:=v1]{Γ}>m1 ⊑{Γ,α,f@Δ1↦Δ2} <[a2:=v2]{Γ}>m2.
Proof.
  intros ??? (w1&?&?) ?. destruct (cmap_lookup_refine Γ α f Δ1 Δ2
    m1 m2 a1 a2 w1 τ) as (w2&?&?); auto.
  eapply cmap_alter_refine; eauto 1.
  * eapply ctree_Forall_not, pbits_mapped; eauto using pbits_kind_weaken.
  * erewrite <-(pbits_refine_perm _ _ _ _ _ (ctree_flatten w1)
      (ctree_flatten w2)) by eauto using ctree_flatten_refine.
    eapply of_val_refine; eauto.
    eapply pbits_perm_unshared, pbits_unshared; eauto using
      pbits_kind_weaken, pbits_valid_sep_valid, ctree_flatten_valid.
  * eapply ctree_Forall_not, of_val_flatten_mapped; eauto using
      val_refine_typed_l, of_val_flatten_typed, cmap_lookup_Some.
Qed.
Lemma mem_insert_refine' Γ α f m1 m2 a1 a2 v1 v2 τ :
  ✓ Γ → m1 ⊑{Γ,α,f} m2 →
  a1 ⊑{Γ,α,f@'{m1}↦'{m2}} a2 : TType τ → mem_writable Γ a1 m1 →
  v1 ⊑{Γ,α,f@'{m1}↦'{m2}} v2 : τ → <[a1:=v1]{Γ}>m1 ⊑{Γ,α,f} <[a2:=v2]{Γ}>m2.
Proof.
  unfold refineM, cmap_refine'; intros.
  erewrite !mem_insert_memenv_of by eauto using cmap_refine_valid_l',
    cmap_refine_valid_r', addr_refine_typed_l, addr_refine_typed_r,
    val_refine_typed_l, val_refine_typed_r, mem_writable_refine.
  eauto using mem_insert_refine.
Qed.

(* todo: prove a stronger version that allows to allocate multiple objects
on the left and all map to the same object on the right. *)
Lemma mem_refine_extend Γ α f Δ1 Δ2 o1 o2 :
  ✓ Γ → Δ1 ⊑{Γ,α,f} Δ2 → Δ1 !! o1 = None → Δ2 !! o2 = None → ∃ f',
  (**i 1.) *) Δ1 ⊑{Γ,α,f'} Δ2 ∧
  (**i 2.) *) f' !! o1 = Some (o2,[]) ∧
  (**i 3.) *) meminj_extend f f' Δ1 Δ2.
Proof.
  intros ? HΔ ??. set (f' := meminj_map $
    (<[o1:=(o2,[])]> (map_of_collection (f !!.) (dom indexset Δ1)))).
  assert (f' !! o1 = Some (o2,[])) as help1.
  { by unfold f', lookup; intros; simplify_map_eq. }
  assert (∀ o' τ, Δ1 ⊢ o' : τ → f' !! o' = f !! o') as help2.
  { intros o' τ [β ?]; unfold lookup at 1, f'; simpl.
    rewrite lookup_insert_ne by naive_solver.
    apply option_eq; intros [o2' r]; simpl.
    rewrite lookup_map_of_collection, elem_of_dom; naive_solver. }
  exists f'; repeat split; auto.
  * intros o3 o3' o4 r1 r2. destruct HΔ as [? _ ?? _ _ _ _].
    unfold typed, index_typed in *; unfold lookup, f'; simpl.
    rewrite !lookup_insert_Some, !lookup_map_of_collection, !elem_of_dom.
    intros [[??]|(?&[[??]?]&?)] [[??]|(?&[[??]?]&?)]; naive_solver.
  * intros o3 o4 r. destruct HΔ as [_ ? _ _ _ _ _ _]. unfold lookup, f'; simpl.
    rewrite lookup_insert_Some, lookup_map_of_collection, elem_of_dom.
    intros [[??]|(?&[[??]?]&?)]; simplify_map_eq; naive_solver. 
  * intros o3 o4 r τ Hf' ?; erewrite help2 in Hf' by eauto.
    eauto using memenv_refine_typed_l.
  * intros o3 o4 r τ. destruct HΔ as [_ _ _ ? _ _ _ _].
    unfold lookup, f'; simpl; unfold typed, index_typed in *.
    rewrite lookup_insert_Some, lookup_map_of_collection, elem_of_dom.
    intros [[??]|(?&[[??]?]&?)]; simplify_map_eq; naive_solver.
  * intros o3 o4 r Hf' Ho3.
    assert (∃ τ, Δ1 ⊢ o3 : τ) as [τ ?] by (destruct Ho3; do 2 eexists; eauto).
    erewrite help2 in Hf' by eauto; eauto using memenv_refine_alive_l.
  * intros o3 o4 r ?. destruct HΔ as [_ _ _ _ _ ? _ _].
    unfold lookup, f'; simpl; unfold index_alive in *.
    rewrite lookup_insert_Some, lookup_map_of_collection, elem_of_dom.
    intros [[??]|(?&[[??]?]&?)]; simplify_map_eq; naive_solver. 
  * intros o3 τ. destruct α; [by intros []|intros].
    destruct (memenv_refine_perm_l Γ f Δ1 Δ2 o3 τ) as (o4&?&?); auto.
    exists o4. by erewrite help2 by eauto.
  * intros o4 τ. destruct α; [by intros []|intros].
    destruct (decide (o4 = o2)) as [->|]; eauto.
    destruct (memenv_refine_perm_r Γ f Δ1 Δ2 o4 τ) as (o3&?&?); auto.
    exists o3. by erewrite help2 by eauto.
  * intros o3 o4 r τ [??].
    unfold lookup at 1, f'; simpl; unfold typed, index_typed in *.
    rewrite lookup_insert_Some, lookup_map_of_collection, elem_of_dom.
    intros [[??]|(?&[[??]?]&?)]; simplify_map_eq; naive_solver.
Qed.
Lemma mem_alloc_refine_env Γ α f Δ1 Δ2 τ o1 o2 :
  Δ1 ⊑{Γ,α,f} Δ2 → Δ1 !! o1 = None → Δ2 !! o2 = None →
  f !! o1 = Some (o2,[]) →
  <[o1:=(τ,false)]> Δ1 ⊑{Γ,α,f} <[o2:=(τ,false)]> Δ2.
Proof.
  intros HΔ; split; eauto using memenv_refine_injective.
  * eauto using memenv_refine_frozen.
  * intros o3 o4 r τ3 ? Ho3. destruct (decide (o1 = o3)) as [->|?].
    + destruct Ho3; simplify_map_eq/=.
      setoid_rewrite ref_typed_nil; eauto using mem_alloc_index_typed.
    + destruct (memenv_refine_typed_l HΔ o3 o4 r τ3)
        as (τ4&?&?); eauto using mem_alloc_forward,
        memenv_forward_typed, mem_alloc_index_typed_inv.
  * intros o3 o4 r τ4 ? Ho4. destruct (decide (o1 = o3)) as [->|?].
    { destruct Ho4; simplify_map_eq.
      setoid_rewrite ref_typed_nil; eauto using mem_alloc_index_typed. }
    destruct (meminj_injective_ne f o1 o2 o3 o4 [] r)
      as [|[??]]; simplify_map_eq; eauto using memenv_refine_injective.
    + destruct (memenv_refine_typed_r HΔ o3 o4 r τ4)
        as (τ3&?&?); eauto using mem_alloc_forward,
        memenv_forward_typed, mem_alloc_index_typed_inv.
    + by destruct (ref_disjoint_nil_inv_l r).
  * intros o3 o4 r ??; destruct (decide (o1 = o3)) as [->|?].
    { simplify_equality; eauto using mem_alloc_index_alive. }
    destruct (meminj_injective_ne f o1 o2 o3 o4 [] r) as [?|[??]];
      eauto using memenv_refine_injective, mem_alloc_index_alive_ne,
      mem_alloc_index_alive_inv, memenv_refine_alive_l.
    by destruct (ref_disjoint_nil_inv_l r).
  * intros o3 o4 r ??; destruct (decide (o2 = o4)) as [->|?].
    { destruct (memenv_refine_injective Γ α f Δ1 Δ2 HΔ o1 o3 o4 [] r);
        simplify_equality; eauto using mem_alloc_index_alive.
      by destruct (ref_disjoint_nil_inv_l r). }
    eauto using mem_alloc_index_alive_ne,
      mem_alloc_index_alive_inv, memenv_refine_alive_r with congruence.
  * intros o3 ???. destruct (decide (o1 = o3)) as [->|]; eauto.
    eauto using memenv_refine_perm_l', mem_alloc_index_typed_inv.
  * intros o4 ???. destruct (decide (o2 = o4)) as [->|]; eauto.
    eauto using memenv_refine_perm_r', mem_alloc_index_typed_inv.
Qed.
Lemma mem_alloc_refine Γ α f Δ1 Δ2 m1 m2 o1 o2 mallc x v1 v2 τ :
  let Δ1' := <[o1:=(τ,false)]>Δ1 in let Δ2' := <[o2:=(τ,false)]>Δ2 in
  ✓ Γ → m1 ⊑{Γ,α,f@Δ1↦Δ2} m2 →
  Δ1 !! o1 = None → Δ2 !! o2 = None → f !! o1 = Some (o2,[]) →
  sep_unshared x → v1 ⊑{Γ,α,f@Δ1'↦Δ2'} v2 : τ →
  mem_alloc Γ o1 mallc x v1 m1 ⊑{Γ,α,f@Δ1'↦Δ2'} mem_alloc Γ o2 mallc x v2 m2.
Proof.
  simpl; intros ? (?&?&HΔ&Hm) ?????.
  assert (sep_valid x) by (by apply sep_unshared_valid).
  split; split_and ?; eauto 5 using mem_alloc_valid, mem_alloc_refine_env,
    val_refine_typed_l, val_refine_typed_r, sep_unshared_unmapped.
  destruct m1 as [m1], m2 as [m2]; intros o3 o4 r w3 μ' ?; simpl in *.
  rewrite lookup_insert_Some; intros [[??]|[??]]; simplify_map_eq.
  { exists (of_val Γ (replicate (bit_size_of Γ τ) x) v2),
      (of_val Γ (replicate (bit_size_of Γ τ) x) v2), τ.
    erewrite val_refine_type_of_r, val_refine_type_of_l by eauto.
    auto 7 using of_val_refine, Forall_replicate. }
  destruct (meminj_injective_ne f o1 o2 o3 o4 [] r)
    as [|[??]]; simplify_map_eq; eauto using memenv_refine_injective.
  * destruct (Hm o3 o4 r w3 μ') as (w2&w2'&τ2&?&?&?&?); auto.
    exists w2, w2', τ2; eauto 10 using ctree_refine_weaken,
      mem_alloc_forward, mem_alloc_refine_env, meminj_extend_reflexive.
  * by destruct (ref_disjoint_nil_inv_l r).
Qed.
Lemma mem_alloc_refine' Γ α f m1 m2 o1 o2 μ x v1 v2 τ :
  ✓ Γ → m1 ⊑{Γ,α,f} m2 → o1 ∉ dom indexset m1 → o2 ∉ dom indexset m2 →
  sep_unshared x → v1 ⊑{Γ,α,f@'{m1}↦'{m2}} v2 : τ → ∃ f',
  (**i 1.) *) f' !! o1 = Some (o2,[]) ∧
  (**i 2.) *)
    mem_alloc Γ o1 μ x v1 m1 ⊑{Γ,α,f'} mem_alloc Γ o2 μ x v2 m2 ∧
  (**i 3.) *) meminj_extend f f' '{m1} '{m2}.
Proof.
  intros ????? Hv. destruct (mem_refine_extend Γ α f '{m1} '{m2} o1 o2) as
    (f'&?&?&?); eauto using mem_allocable_memenv_of,cmap_refine_memenv_refine.
  exists f'; split_and ?; auto. unfold refineM, cmap_refine'.
  erewrite !mem_alloc_memenv_of
    by eauto using val_refine_typed_l, val_refine_typed_r.
  eapply mem_alloc_refine;
    eauto 10 using mem_allocable_memenv_of, cmap_refine_weaken,
    val_refine_weaken, mem_alloc_forward, mem_alloc_refine_env.
Qed.
Lemma mem_alloc_new_refine' Γ α f m1 m2 o1 o2 μ x τ :
  ✓ Γ → m1 ⊑{Γ,α,f} m2 → o1 ∉ dom indexset m1 → o2 ∉ dom indexset m2 →
  sep_unshared x → ✓{Γ} τ → ∃ f',
  (**i 1.) *) f' !! o1 = Some (o2,[]) ∧
  (**i 2.) *)
    mem_alloc Γ o1 μ x (val_new Γ τ) m1
    ⊑{Γ,α,f'} mem_alloc Γ o2 μ x (val_new Γ τ) m2 ∧
  (**i 3.) *) meminj_extend f f' '{m1} '{m2}.
Proof. eauto using mem_alloc_refine', (val_new_refine _ _ ∅). Qed.
Hint Immediate cmap_refine_valid_l' cmap_refine_valid_r': core.
Hint Immediate cmap_refine_memenv_refine: core.
Lemma mem_alloc_list_refine' Γ α f m1 m2 os1 os2 vs1 vs2 τs :
  ✓ Γ → m1 ⊑{Γ,α,f} m2 → vs1 ⊑{Γ,α,f@'{m1}↦'{m2}}* vs2 :* τs →
  length os1 = length vs1 → length os2 = length vs2 →
  Forall_fresh (dom indexset m1) os1 → Forall_fresh (dom indexset m2) os2 → ∃ f',
  (**i 1.) *) Forall2 (λ o1 o2, f' !! o1 = Some (o2,[])) os1 os2 ∧
  (**i 2.) *) mem_alloc_list Γ os1 vs1 m1
      ⊑{Γ,α,f'} mem_alloc_list Γ os2 vs2 m2 ∧
  (**i 3.) *) meminj_extend f f' '{m1} '{m2}.
Proof.
  rewrite <-!Forall2_same_length. intros ? Hm Hvs Hovs1 Hovs2 Hos1 Hos2.
  revert τs os2 vs2 Hos1 Hos2 Hvs Hovs2.
  induction Hovs1 as [|o1 v1 os1 vs1 ?? IH];
    intros [|τ τs] [|o2 os2] [|v2 vs2]; inversion_clear 1;
    inversion_clear 1; inversion_clear 1; intros; decompose_Forall_hyps.
  { eauto using meminj_extend_reflexive. }
  assert ((Γ,'{m1}) ⊢ v1 : τ) by eauto using val_refine_typed_l.
  assert ((Γ,'{m2}) ⊢ v2 : τ) by eauto using val_refine_typed_r.
  assert (✓{Γ} τ) by eauto using val_typed_type_valid.
  destruct (IH τs os2 vs2) as (f'&?&?&?); auto.
  assert (o1 ∉ dom indexset (mem_alloc_list Γ os1 vs1 m1)).
  { rewrite mem_dom_alloc_list, elem_of_union, elem_of_list_to_set
       by eauto using Forall2_length; tauto. }
  assert (o2 ∉ dom indexset (mem_alloc_list Γ os2 vs2 m2)).
  { rewrite mem_dom_alloc_list, elem_of_union, elem_of_list_to_set
       by eauto using Forall2_length; tauto. }
  destruct (mem_alloc_refine' Γ α f' (mem_alloc_list Γ os1 vs1 m1)
    (mem_alloc_list Γ os2 vs2 m2) o1 o2 false perm_full v1 v2 τ)
    as (f''&?&?&?); eauto 6 using perm_full_mapped, perm_full_unshared,
    val_refine_weaken, mem_alloc_list_forward.
  exists f''; split_and ?; eauto using meminj_extend_transitive.
  * assert ('{mem_alloc_list Γ os1 vs1 m1} ⊢* os1 :* τs)
      by eauto using mem_alloc_list_index_typed.
    constructor; auto.
    decompose_Forall. eapply (@transitivity _ _ _ ) with (f' !! _);
      eauto using eq_sym, meminj_extend_left.
  * eapply meminj_extend_transitive; eauto using mem_alloc_list_forward.
Qed.
Lemma mem_freeable_refine Γ α f Δ1 Δ2 m1 m2 a1 a2 τp :
  ✓ Γ → m1 ⊑{Γ,α,f@Δ1↦Δ2} m2 →
  a1 ⊑{Γ,α,f@Δ1↦Δ2} a2 : τp → mem_freeable a1 m1 → mem_freeable a2 m2.
Proof.
  intros ? (_&_&_&Hm) ? (Ha&w1&?&?).
  rewrite addr_is_top_array_alt in Ha by eauto using addr_refine_typed_l.
  destruct Ha as (τ'&n&?&Ha1&?).
  destruct (addr_ref_refine Γ α f Δ1 Δ2 a1 a2 τp) as (r&?&_&Ha2); eauto.
  destruct (Hm (addr_index a1) (addr_index a2) r w1 true)
    as (?&w2&τ''&?&?&?&Hr); auto; specialize (Hr I); simplify_type_equality'.
  split; [|exists w2; eauto using pbits_refine_perm_1, ctree_flatten_refine].
  rewrite addr_is_top_array_alt by eauto using addr_refine_typed_r.
  assert (addr_ref Γ a2 = [RArray 0 τ' n]) as ->.
  { by rewrite Ha1 in Ha2;
      inversion Ha2 as [|???? Harr]; inversion Harr; decompose_Forall_hyps. }
  erewrite <-addr_ref_byte_refine by eauto.
  exists τ', n; split_and ?; eauto using addr_strict_refine.
Qed.
Lemma mem_freeable_index_refine Γ α f Δ1 Δ2 m1 m2 a1 a2 τp :
  ✓ Γ → m1 ⊑{Γ,α,f@Δ1↦Δ2} m2 → a1 ⊑{Γ,α,f@Δ1↦Δ2} a2 : τp →
  mem_freeable a1 m1 → f !! addr_index a1 = Some (addr_index a2, []).
Proof.
  intros ? (_&_&_&Hm) ? (Ha&w1&?&?).
  rewrite addr_is_top_array_alt in Ha by eauto using addr_refine_typed_l.
  destruct Ha as (τ'&n&?&Ha1&?), (addr_ref_refine Γ α f Δ1 Δ2 a1 a2 τp)
    as (r&?&Ha2); naive_solver.
Qed.
Lemma mem_free_refine_env Γ α f Δ1 Δ2 o1 o2 :
  Δ1 ⊑{Γ,α,f} Δ2 → f !! o1 = Some (o2,[]) →
  alter (prod_map id (λ _, true)) o1 Δ1
    ⊑{Γ,α,f} alter (prod_map id (λ _, true)) o2 Δ2.
Proof.
  intros HΔ ?; split; eauto using memenv_refine_injective.
  * eauto using memenv_refine_frozen.
  * intros o3 o4 r τ3 ??.
    destruct (memenv_refine_typed_l HΔ o3 o4 r τ3) as (τ4&?&?); eauto
      using mem_free_index_typed_inv, mem_free_forward, memenv_forward_typed.
  * intros o3 o4 r τ4 ??.
    destruct (memenv_refine_typed_r HΔ o3 o4 r τ4) as (τ3&?&?); eauto
      using mem_free_index_typed_inv, mem_free_forward, memenv_forward_typed.
  * intros o3 o4 r ??. destruct (decide (o2 = o4)) as [->|?].
    { destruct (memenv_refine_injective Γ α f Δ1 Δ2 HΔ o1 o3 o4 [] r);
        simplify_equality; eauto.
      + by destruct (mem_free_index_alive Δ1 o3).
      + by destruct (ref_disjoint_nil_inv_l r). }
    eauto using mem_free_index_alive_ne,
      mem_free_index_alive_inv, memenv_refine_alive_l.
  * intros o3 o4 r ???. destruct (decide (o1 = o3)); simplify_equality.
    + by destruct (mem_free_index_alive Δ2 o2).
    + eauto using mem_free_index_alive_ne,
        mem_free_index_alive_inv, memenv_refine_alive_r.
  * intros o3 τ ??. destruct (decide (o1 = o3)) as [->|]; eauto.
    eauto using memenv_refine_perm_l', mem_free_index_typed_inv.
  * intros o4 τ ??. destruct (decide (o2 = o4)) as [->|]; eauto.
    eauto using memenv_refine_perm_r', mem_free_index_typed_inv.
Qed.
Lemma mem_free_refine_env_l Γ f Δ1 Δ2 o :
  Δ1 ⊑{Γ,true,f} Δ2 → alter (prod_map id (λ _, true)) o Δ1 ⊑{Γ,true,f} Δ2.
Proof.
  destruct 1; split; simpl; try by auto.
  * eauto using mem_free_index_typed_inv.
  * naive_solver eauto using mem_free_forward, memenv_forward_typed.
  * eauto using mem_free_index_alive_inv.
Qed.
Lemma mem_free_refine_env_r Γ f Δ1 Δ2 o :
  Δ1 ⊑{Γ,true,f} Δ2 → (∀ o' r, f !! o' = Some (o,r) → ¬index_alive Δ1 o') →
  Δ1 ⊑{Γ,true,f} alter (prod_map id (λ _, true)) o Δ2.
Proof.
  intros [] Hf; split; simpl; try by auto.
  * naive_solver eauto using mem_free_forward, memenv_forward_typed.
  * eauto using mem_free_index_typed_inv.
  * intros o1 o2 r ??.
    destruct (decide (o2 = o)) as [->|?]; [by destruct (Hf o1 r)|].
    eauto using mem_free_index_alive_ne.
Qed.
Lemma mem_free_refine Γ α f Δ1 Δ2 m1 m2 o1 o2 :
  let Δ1' := alter (prod_map id (λ _, true)) o1 Δ1 in
  let Δ2' := alter (prod_map id (λ _, true)) o2 Δ2 in
  ✓ Γ → m1 ⊑{Γ,α,f@Δ1↦Δ2} m2 → f !! o1 = Some (o2,[]) →
  mem_free o1 m1 ⊑{Γ,α,f@Δ1'↦Δ2'} mem_free o2 m2.
Proof.
  simpl; intros ?(?&?&?&Hm).
  split; split_and ?; auto using mem_free_valid, mem_free_refine_env.
  destruct m1 as [m1], m2 as [m2]; simpl in *.
  intros o1' o2' r w1 μ ?; rewrite lookup_alter_Some;
    intros [(?&[?|??]&?&?)|[??]]; simplify_equality'; eauto.
  destruct (Hm o1' o2' r w1 μ) as (w2&w2'&τ2&?&?&?&?); auto.
  destruct (decide (o2 = o2')) as [->|?]; simplify_map_eq.
  * destruct (meminj_injective_alt f o1 o1' o2' [] r) as [->|[??]];
      simplify_map_eq; eauto using memenv_refine_injective.
    by destruct (ref_disjoint_nil_inv_l r).
  * exists w2, w2', τ2; split_and ?; eauto using ctree_refine_weaken,
      mem_free_forward, mem_free_refine_env, meminj_extend_reflexive.
Qed.
Lemma mem_free_refine_l Γ f Δ1 Δ2 m1 m2 o :
  let Δ1' := alter (prod_map id (λ _, true)) o Δ1 in
  ✓ Γ → m1 ⊑{Γ,true,f@Δ1↦Δ2} m2 → mem_free o m1 ⊑{Γ,true,f@Δ1'↦Δ2} m2.
Proof.
  simpl; intros ?(?&?&?&Hm).
  split; split_and ?; auto using mem_free_valid, mem_free_refine_env_l.
  destruct m1 as [m1], m2 as [m2]; simpl in *.
  intros o1 o2 r w1 μ ?; rewrite lookup_alter_Some;
    intros [(?&[?|??]&?&?)|[??]]; simplify_equality'; eauto.
  destruct (Hm o1 o2 r w1 μ) as (w2&w2'&τ2&?&?&?&?); auto.
  exists w2, w2', τ2; eauto 10 using ctree_refine_weaken,
    mem_free_forward, mem_free_refine_env_l, meminj_extend_reflexive.
Qed.
Lemma mem_free_refine_r Γ f Δ1 Δ2 m1 m2 o :
  let Δ2' := alter (prod_map id (λ _, true)) o Δ2 in ✓ Γ →
  (∀ o' r, f !! o' = Some (o,r) → ¬index_alive Δ1 o') →
  m1 ⊑{Γ,true,f@Δ1↦Δ2} m2 → m1 ⊑{Γ,true,f@Δ1↦Δ2'} mem_free o m2.
Proof.
  simpl; intros ? Hf (Hm1&?&?&Hm).
  split; split_and ?; auto using mem_free_valid, mem_free_refine_env_r.
  destruct m1 as [m1], m2 as [m2]; simpl in *; intros o1 o2 r w1 μ ??.
  destruct (cmap_valid_Obj Γ Δ1 (CMap m1) o1 w1 μ) as (τ1&?&?&_); auto.
  destruct (decide (o2 = o)) as [->|?]; [by destruct (Hf o1 r)|].
  destruct (Hm o1 o2 r w1 μ) as (w2&w2'&τ2&?&?&?&?); auto.
  exists w2, w2', τ2; simplify_map_eq; eauto 7 using ctree_refine_weaken,
    mem_free_forward, mem_free_refine_env_r, meminj_extend_reflexive.
Qed.
Lemma mem_free_refine' Γ α f m1 m2 o1 o2 :
  ✓ Γ → m1 ⊑{Γ,α,f} m2 → f !! o1 = Some (o2,[]) →
  mem_free o1 m1 ⊑{Γ,α,f} mem_free o2 m2.
Proof.
  unfold refineM, cmap_refine'.
  rewrite !mem_free_memenv_of; eauto using mem_free_refine.
Qed.
Lemma mem_foldr_free_refine Γ α f m1 m2 os1 os2 :
  ✓ Γ → m1 ⊑{Γ,α,f} m2 →
  Forall2 (λ o1 o2, f !! o1 = Some (o2, [])) os1 os2 →
  foldr mem_free m1 os1 ⊑{Γ,α,f} foldr mem_free m2 os2.
Proof. induction 3; simpl; auto using mem_free_refine'. Qed.

Lemma locks_refine_id Γ α Δ Ω : ✓{Γ,Δ} Ω → Ω ⊑{Γ,α@Δ} Ω.
Proof.
  split; split_and ?; intros *; rewrite ?lookup_meminj_id; intros;
    simplify_type_equality'; eauto using memenv_refine_id.
Qed.
Lemma locks_refine_compose Γ α1 α2 f1 f2 Δ1 Δ2 Δ3 Ω1 Ω2 Ω3 :
  ✓ Γ → Ω1 ⊑{Γ,α1,f1@Δ1↦Δ2} Ω2 → Ω2 ⊑{Γ,α2,f2@Δ2↦Δ3} Ω3 →
  Ω1 ⊑{Γ,α1||α2,f2 ◎ f1@Δ1↦Δ3} Ω3.
Proof.
  intros ? (?&?&HΔ12&HΩ12) (?&?&HΔ23&HΩ23);
    split; split_and ?; eauto using memenv_refine_compose.
  intros o1 o3 r τ1 i.
  rewrite lookup_meminj_compose_Some; intros (o2&r2&r3&?&?&->) ???.
  destruct (memenv_refine_typed_l HΔ12 o1 o2 r2 τ1) as (τ2&?&?); auto.
  destruct (memenv_refine_typed_l HΔ23 o2 o3 r3 τ2) as (τ3&?&?); auto.
  assert (ref_object_offset Γ r2 + i < bit_size_of Γ τ2).
  { apply Nat.lt_le_trans with
      (ref_object_offset Γ r2 + bit_size_of Γ τ1); [lia|].
    eauto using ref_object_offset_size'. }
  rewrite HΩ12, HΩ23 by eauto using memenv_refine_alive_l.
  by rewrite ref_object_offset_app, Nat.add_assoc,
    (Nat.add_comm (ref_object_offset Γ r2)).
Qed.
Lemma locks_refine_inverse Γ f Δ1 Δ2 Ω1 Ω2 :
  Ω1 ⊑{Γ,false,f@Δ1↦Δ2} Ω2 → Ω2 ⊑{Γ,false,meminj_inverse f@Δ2↦Δ1} Ω1.
Proof.
  intros (?&?&?&Hf); split; split_and ?; eauto using memenv_refine_inverse.
  intros o2 o1 r τ i Ho2 ???. destruct (lookup_meminj_inverse_1 Γ f
    Δ1 Δ2 o1 o2 r τ) as (?&?&->); simpl; auto.
  symmetry; apply (Hf _ _ [] τ); eauto using memenv_refine_alive_r.
Qed.
Lemma locks_refine_valid_l Γ α f Δ1 Δ2 Ω1 Ω2 :
  Ω1 ⊑{Γ,α,f@Δ1↦Δ2} Ω2 → ✓{Γ,Δ1} Ω1.
Proof. by intros (?&?&?&?). Qed.
Lemma locks_list_refine_valid_l Γ α f Δ1 Δ2 Ωs1 Ωs2 :
  Ωs1 ⊑{Γ,α,f@Δ1↦Δ2}* Ωs2 → ✓{Γ,Δ1}* Ωs1.
Proof. induction 1; eauto using locks_refine_valid_l. Qed.
Lemma locks_refine_valid_r Γ α f Δ1 Δ2 Ω1 Ω2 :
  Ω1 ⊑{Γ,α,f@Δ1↦Δ2} Ω2 → ✓{Γ,Δ2} Ω2.
Proof. by intros (?&?&?&?). Qed.
Lemma locks_list_refine_valid_r Γ α f Δ1 Δ2 Ωs1 Ωs2 :
  Ωs1 ⊑{Γ,α,f@Δ1↦Δ2}* Ωs2 → ✓{Γ,Δ2}* Ωs2.
Proof. induction 1; eauto using locks_refine_valid_r. Qed.
Lemma locks_refine_weaken Γ α α' f f' Δ1 Δ2 Δ1' Δ2' Ω1 Ω2 :
  ✓ Γ → Ω1 ⊑{Γ,α,f@Δ1↦Δ2} Ω2 →
  Δ1' ⊑{Γ,α',f'} Δ2' → Δ1 ⇒ₘ Δ1' → Δ2 ⇒ₘ Δ2' →
  meminj_extend f f' Δ1 Δ2 → Ω1 ⊑{Γ,α',f'@Δ1'↦Δ2'} Ω2.
Proof.
  intros ? (HΩ1&HΩ2&HΔ12&HΩ) ? HΔ ? [??];
    split; split_and ?; eauto 2 using lockset_valid_weaken.
  intros o1 o2 r τ1 i ????; split.
  * intros ?. destruct (HΩ1 o1 i) as (τ1'&?&?); auto.
    assert (τ1 = τ1') by eauto using typed_unique, memenv_forward_typed.
    simplify_type_equality.
    by erewrite <-HΩ by eauto using memenv_forward_alive, option_eq_1.
  * intros ?. destruct (HΩ2 o2 (ref_object_offset Γ r + i)) as (τ2'&?&?); auto.
    destruct (memenv_refine_typed_r HΔ12 o1 o2 r τ2') as (τ1'&?&?); eauto.
    assert (τ1 = τ1') by eauto using typed_unique, memenv_forward_typed.
    simplify_type_equality. by erewrite HΩ by eauto using memenv_forward_alive.
Qed.
Lemma locks_empty_refine Γ α f Δ1 Δ2 :
  Δ1 ⊑{Γ,α,f} Δ2 → (∅ : lockset) ⊑{Γ,α,f@Δ1↦Δ2} ∅.
Proof. split; split_and ?; eauto using lockset_empty_valid; set_solver. Qed.
Lemma mem_locks_refine Γ α f m1 m2 :
  ✓ Γ → m1 ⊑{Γ,α,f} m2 → mem_locks m1 ⊑{Γ,α,f@'{m1}↦'{m2}} mem_locks m2.
Proof.
  intros ? (Hm1&Hm2&?&Hm); split; split_and ?; auto using mem_locks_valid.
  intros o1 o2 r σ1 i ?? [σ1' ?] ?. assert (∃ w1 μ,
    cmap_car m1 !! o1 = Some (Obj w1 μ)) as (w1&μ&?).
  { destruct m1 as [m1]; simplify_map_eq.
    destruct (m1 !! o1) as [[]|]; naive_solver. }
  destruct (Hm o1 o2 r w1 μ) as (w2'&w2&τ2&?&?&?&?); auto; clear Hm.
  assert ((Γ,'{m1}) ⊢ w1 : τ2) by eauto.
  destruct (cmap_valid_Obj Γ '{m1} m1 o1 w1 μ) as (?&?&?&?&_),
    (cmap_valid_Obj Γ '{m2} m2 o2 w2' μ) as (τ'&?&?&?&_);
    simplify_type_equality'; auto.
  rewrite !elem_of_mem_locks; simplify_option_eq.
  rewrite <-!list_lookup_fmap.
  erewrite pbits_refine_locked; eauto using ctree_flatten_refine.
  rewrite <-(ctree_lookup_flatten Γ '{m2} w2' τ' r w2 σ1)
    by eauto using ctree_refine_typed_r, ctree_lookup_le, ref_freeze_le_l.
  by rewrite pbits_locked_mask, fmap_take, fmap_drop, lookup_take, lookup_drop.
Qed.
Lemma mem_lock_refine Γ α f Δ1 Δ2 m1 m2 a1 a2 τ : 
  ✓ Γ → m1 ⊑{Γ,α,f@Δ1↦Δ2} m2 → a1 ⊑{Γ,α,f@Δ1↦Δ2} a2 : TType τ →
  mem_writable Γ a1 m1 → mem_lock Γ a1 m1 ⊑{Γ,α,f@Δ1↦Δ2} mem_lock Γ a2 m2.
Proof.
  intros ??? (w1&?&?).
  destruct (cmap_lookup_refine Γ α f Δ1 Δ2 m1 m2 a1 a2 w1 τ) as (w2&?&?); auto.
  eapply cmap_alter_refine; eauto 1.
  * eapply ctree_Forall_not, pbits_mapped; eauto using pbits_kind_weaken.
  * apply ctree_map_refine; eauto using pbit_lock_unshared, pbit_lock_indetified,
      pbits_lock_refine, ctree_flatten_refine, pbit_lock_mapped.
  * eapply ctree_Forall_not; eauto 8 using ctree_map_typed, pbit_lock_indetified,
      pbits_lock_valid, ctree_flatten_valid, pbit_lock_mapped.
    rewrite ctree_flatten_map.
    eauto using pbits_lock_mapped, pbits_mapped, pbits_kind_weaken.
Qed.
Lemma mem_lock_refine' Γ α f m1 m2 a1 a2 τ : 
  ✓ Γ → m1 ⊑{Γ,α,f} m2 → a1 ⊑{Γ,α,f@'{m1}↦'{m2}} a2 : TType τ →
  mem_writable Γ a1 m1 → mem_lock Γ a1 m1 ⊑{Γ,α,f} mem_lock Γ a2 m2.
Proof.
  intros. unfold refineM, cmap_refine'. erewrite !mem_lock_memenv_of by eauto
    using cmap_refine_valid_l, cmap_refine_valid_r, mem_writable_refine.
  eauto using mem_lock_refine.
Qed.
Lemma ctree_unlock_refine Γ α f Δ1 Δ2 w1 w2 τ βs :
  ✓ Γ → w1 ⊑{Γ,α,f@Δ1↦Δ2} w2 : τ → length βs = bit_size_of Γ τ →
  ctree_merge pbit_unlock_if w1 βs
    ⊑{Γ,α,f@Δ1↦Δ2} ctree_merge pbit_unlock_if w2 βs : τ.
Proof.
  intros HΓ Hw Hlen.
  apply ctree_leaf_refine_refine; eauto using ctree_unlock_typed.
  revert w1 w2 τ Hw βs Hlen.
  refine (ctree_refine_ind _ _ _ _ _ _ _ _ _ _ _ _); simpl.
  * constructor; auto using pbits_unlock_refine.
  * intros τ n ws1 ws2 -> ? IH _ βs. rewrite bit_size_of_array. intros Hlen.
    constructor. revert βs Hlen. induction IH; intros; decompose_Forall_hyps;
      erewrite ?Forall2_length by eauto using ctree_flatten_refine; auto.
  * intros t τs wγbss1 wγbss2 Ht Hws IH Hγbss _ _ Hpad βs.
    erewrite bit_size_of_struct by eauto; clear Ht. constructor.
    + revert wγbss1 wγbss2 βs Hws IH Hγbss Hlen Hpad. unfold field_bit_padding.
      induction (bit_size_of_fields _ τs HΓ);
        intros [|[w1 γbs1] ?] [|[w2 γbs2] ?];
        do 2 inversion_clear 1; intros; decompose_Forall_hyps; [done|].
      erewrite ?ctree_flatten_length, <-(Forall2_length _ γbs1 γbs2) by eauto.
      constructor; eauto.
    + clear Hlen IH Hpad. revert βs. induction Hws as [|[w1 γbs1] [w2 γbs2]];
        intros; decompose_Forall_hyps; auto.
      erewrite ?ctree_flatten_length, <-(Forall2_length _ γbs1 γbs2) by eauto.
      constructor; eauto using pbits_unlock_refine.
  * intros. erewrite Forall2_length by eauto using ctree_flatten_refine.
    constructor; auto using pbits_unlock_refine.
  * constructor; auto using pbits_unlock_refine.
  * intros t i τs w1 γbs1 γbs2 τ ???????? βs ?.
    erewrite ctree_flatten_length by eauto.
    constructor; auto using pbits_unlock_unshared.
    rewrite ctree_flatten_merge, <-zip_with_app, take_drop by auto.
    auto using pbits_unlock_refine.
Qed.
Lemma mem_unlock_refine Γ α f Δ1 Δ2 m1 m2 Ω1 Ω2 :
  ✓ Γ → m1 ⊑{Γ,α,f@Δ1↦Δ2} m2 → Ω1 ⊑{Γ,α,f@Δ1↦Δ2} Ω2 →
  mem_unlock Ω1 m1 ⊑{Γ,α,f@Δ1↦Δ2} mem_unlock Ω2 m2.
Proof.
  assert (∀ γb β,
    pbit_unlock_if (pbit_indetify γb) β = pbit_indetify (pbit_unlock_if γb β)).
  { by intros ? []. }
  assert (∀ γb β, sep_unshared γb → sep_unshared (pbit_unlock_if γb β)).
  { intros ? []; eauto using pbit_unlock_unshared. }
  assert (∀ n γbs,
    length γbs = n → zip_with pbit_unlock_if γbs (replicate n false) = γbs).
  { intros n γbs <-. rewrite zip_with_replicate_r by auto.
    by elim γbs; intros; f_equal'. }
  intros ? (Hm1&Hm2&?&Hm) (_&_&_&HΩ);
    split; split_and ?; auto using mem_unlock_valid; intros o1 o2 r w1 μ ? Hw1.
  destruct m1 as [m1], m2 as [m2], Ω1 as [Ω1 HΩ1], Ω2 as [Ω2 HΩ2]; simpl in *.
  unfold elem_of, lockset_elem_of in HΩ; simpl in HΩ; clear HΩ1 HΩ2.
  rewrite lookup_merge in Hw1 |- *. unfold diag_None in Hw1 |- *.
  destruct (m1 !! o1) as [[|w1' μ']|] eqn:?; try by destruct (Ω1 !! o1).
  destruct (Hm o1 o2 r w1' μ') as (w2&w2'&τ1&Ho2&?&?&?); auto; clear Hm.
  assert ((Γ,Δ1) ⊢ w1' : τ1) by eauto using ctree_refine_typed_l.
  assert ((Γ,Δ2) ⊢ w2' : τ1) by eauto using ctree_refine_typed_r.
  destruct (cmap_valid_Obj Γ Δ1 (CMap m1) o1 w1' μ')as (?&?&?&?&_),
    (cmap_valid_Obj Γ Δ2 (CMap m2) o2 w2 μ') as (τ2&?&?&?&_);
    simplify_type_equality; auto.
  destruct (ctree_lookup_Some Γ Δ2 w2 τ2 r w2')
    as (τ1'&?&?); auto; simplify_type_equality.
  assert (ref_object_offset Γ r + bit_size_of Γ τ1
    ≤ bit_size_of Γ τ2) by eauto using ref_object_offset_size'.
  erewrite Ho2, ctree_flatten_length by eauto.
  destruct (Ω1 !! o1) as [ω1|] eqn:?; simplify_equality'.
  { erewrite ctree_flatten_length by eauto. destruct (Ω2 !! o2) as [ω2|] eqn:?.
    * assert (take (bit_size_of Γ τ1) (drop (ref_object_offset Γ r) (natset_to_bools
        (bit_size_of Γ τ2) ω2)) = natset_to_bools (bit_size_of Γ τ1) ω1) as Hω2.
      { apply list_eq_same_length with (bit_size_of Γ τ1); try done.
        intros i β1 β2 ?.
        specialize (HΩ o1 o2 r τ1 i); feed specialize HΩ; auto.
        assert (i ∈ ω1 ↔ ref_object_offset Γ r + i ∈ ω2) as Hi by naive_solver.
        rewrite lookup_take, lookup_drop, !lookup_natset_to_bools, Hi by lia.
        destruct β1, β2; intuition. }
      do 3 eexists; split_and ?; eauto using ctree_lookup_merge.
      rewrite Hω2; eauto using ctree_unlock_refine.
    * assert (natset_to_bools (bit_size_of Γ τ1) ω1
        = replicate (bit_size_of Γ τ1) false) as Hω.
      { apply list_eq_same_length with (bit_size_of Γ τ1); try done.
        intros i β1 β2 ?. rewrite lookup_replicate_2 by done.
        intros Hβ1 ?; destruct β1; simplify_equality'; try done.
        rewrite lookup_natset_to_bools_true in Hβ1 by lia.
        specialize (HΩ o1 o2 r τ1 i); feed specialize HΩ; auto.
        destruct (proj1 HΩ) as (?&?&?); simplify_equality; eauto. }
      do 3 eexists; split_and ?; eauto.
      rewrite Hω, ctree_merge_id by auto; eauto. }
  destruct (Ω2 !! o2) as [ω2|] eqn:?; [|by eauto 7].
  assert (take (bit_size_of Γ τ1) (drop (ref_object_offset Γ r) (natset_to_bools
    (bit_size_of Γ τ2) ω2)) = replicate (bit_size_of Γ τ1) false) as Hω2.
  { apply list_eq_same_length with (bit_size_of Γ τ1); try done.
    intros i β1 β2 ?.
    rewrite lookup_take, lookup_drop, lookup_replicate_2 by done.
    intros Hβ1 ?; destruct β1; simplify_equality'; try done.
    rewrite lookup_natset_to_bools_true in Hβ1 by lia.
    specialize (HΩ o1 o2 r τ1 i); feed specialize HΩ; auto.
    destruct (proj2 HΩ) as (?&?&?); simplify_equality; eauto. }
  do 3 eexists; split_and ?; eauto using ctree_lookup_merge.
  rewrite Hω2, ctree_merge_id by auto; eauto.
Qed.
Lemma mem_unlock_refine' Γ α f m1 m2 Ω1 Ω2 :
  ✓ Γ → m1 ⊑{Γ,α,f} m2 → Ω1 ⊑{Γ,α,f@'{m1}↦'{m2}} Ω2 →
  mem_unlock Ω1 m1 ⊑{Γ,α,f} mem_unlock Ω2 m2.
Proof.
  unfold refineM, cmap_refine'. rewrite !mem_unlock_memenv_of.
  eauto using mem_unlock_refine.
Qed.
Lemma lock_singleton_refine Γ α f Δ1 Δ2 a1 a2 σ :
  ✓ Γ → a1 ⊑{Γ,α,f@Δ1↦Δ2} a2 : TType σ → addr_strict Γ a1 →
  lock_singleton Γ a1 ⊑{Γ,α,f@Δ1↦Δ2} lock_singleton Γ a2.
Proof.
  intros ? Ha ?.
  assert (Δ1 ⊑{Γ,α,f} Δ2) as HΔ by eauto using addr_refine_memenv_refine.
  assert ((Γ,Δ1) ⊢ a1 : TType σ) by eauto using addr_refine_typed_l.
  assert ((Γ,Δ2) ⊢ a2 : TType σ) by eauto using addr_refine_typed_r.
  split; split_and ?; eauto using lock_singleton_valid, addr_strict_refine.
  intros o1 o2 r τ i ????. rewrite !elem_of_lock_singleton_typed by eauto.
  destruct (addr_object_offset_refine Γ α f
    Δ1 Δ2 a1 a2 (TType σ)) as (r'&?&?&->); auto.
  split; [intros (->&?&?); simplify_equality'; intuition lia|intros (->&?&?)].
  destruct (meminj_injective_alt f o1 (addr_index a1) (addr_index a2) r r')
    as [|[??]]; simplify_equality'; eauto using memenv_refine_injective.
  { intuition lia. }
  destruct (memenv_refine_typed_r HΔ o1 (addr_index a2) r
    (addr_type_object a2)) as (?&?&?); eauto using addr_typed_index;
    simplify_type_equality'.
  assert (addr_object_offset Γ a1 + bit_size_of Γ σ
    ≤ bit_size_of Γ (addr_type_object a1)).
  { erewrite addr_object_offset_alt by eauto. transitivity
      (ref_object_offset Γ (addr_ref Γ a1) + bit_size_of Γ (addr_type_base a1));
    eauto using ref_object_offset_size', addr_typed_ref_typed.
    rewrite <-Nat.add_assoc, <-Nat.add_le_mono_l; eauto using addr_bit_range. }
  destruct (ref_disjoint_object_offset Γ (addr_type_object a2) r r'
    τ (addr_type_object a1)); auto; lia.
Qed.
Lemma locks_union_refine Γ α f Δ1 Δ2 Ω1 Ω2 Ω1' Ω2' :
  Ω1 ⊑{Γ,α,f@Δ1↦Δ2} Ω2 → Ω1' ⊑{Γ,α,f@Δ1↦Δ2} Ω2' →
  Ω1 ∪ Ω1' ⊑{Γ,α,f@Δ1↦Δ2} Ω2 ∪ Ω2'.
Proof.
  intros (?&?&?&HΩ) (?&?&_&HΩ');
    split; split_and ?; auto using lockset_union_valid.
  intros o1 o2 r τ1 i ????. by rewrite !elem_of_union, HΩ, HΩ' by eauto.
Qed.
Lemma locks_union_list_refine Γ α f Δ1 Δ2 Ωs1 Ωs2 :
  Δ1 ⊑{Γ,α,f} Δ2 → Ωs1 ⊑{Γ,α,f@Δ1↦Δ2}* Ωs2 → ⋃ Ωs1 ⊑{Γ,α,f@Δ1↦Δ2} ⋃ Ωs2.
Proof.
  induction 2; simpl; eauto using locks_union_refine, locks_empty_refine.
Qed.
End memory.
