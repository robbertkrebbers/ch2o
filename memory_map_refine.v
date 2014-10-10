(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export memory_map memory_trees_refine.
Local Open Scope ctype_scope.

Instance cmap_refine `{Env Ti} :
    Refine Ti (env Ti) (mem Ti) := λ Γ α f Γm1 Γm2 m1 m2,
  (**i 1.) *) ✓{Γ,Γm1} m1 ∧
  (**i 2.) *) ✓{Γ,Γm2} m2 ∧
  (**i 3.) *) Γm1 ⊑{Γ,α,f} Γm2 ∧
  (**i 4.) *) (∀ o1 o2 r w1 malloc,
    f !! o1 = Some (o2,r) → cmap_car m1 !! o1 = Some (Obj w1 malloc) →
    ∃ w2 w2' τ,
      cmap_car m2 !! o2 = Some (Obj w2 malloc) ∧
      w2 !!{Γ} (freeze true <$> r) = Some w2' ∧
      w1 ⊑{Γ,α,f@Γm1↦Γm2} w2' : τ ∧ (malloc → r = [])).
Instance cmap_refine' `{Env Ti} : RefineM Ti (env Ti) (mem Ti) := λ Γ α f m1 m2,
  m1 ⊑{Γ,α,f@memenv_of m1↦memenv_of m2} m2.

Section memory_map.
Context `{EnvSpec Ti}.
Implicit Types Γ : env Ti.
Implicit Types m : mem Ti.
Implicit Types Γm : memenv Ti.
Implicit Types τ σ : type Ti.
Implicit Types o : index.
Implicit Types w : mtree Ti.
Implicit Types rs : ref_seg Ti.
Implicit Types r : ref Ti.
Implicit Types a : addr Ti.
Implicit Types f : meminj Ti.
Implicit Types g : mtree Ti → mtree Ti.
Implicit Types α β : bool.

Arguments lookupE _ _ _ _ _ _ _ !_ /.
Arguments cmap_lookup _ _ _ _ !_ /.

Lemma cmap_refine_memenv_refine Γ α f Γm1 Γm2 m1 m2 :
  m1 ⊑{Γ,α,f@Γm1↦Γm2} m2 → Γm1 ⊑{Γ,α,f} Γm2.
Proof. by intros (?&?&?&?). Qed.
Lemma cmap_refine_memenv_refine' Γ α f m1 m2 :
  m1 ⊑{Γ,α,f} m2 → '{m1} ⊑{Γ,α,f} '{m2}.
Proof. by apply cmap_refine_memenv_refine. Qed.
Lemma cmap_refine_injective Γ α f Γm1 Γm2 m1 m2 :
  m1 ⊑{Γ,α,f@Γm1↦Γm2} m2 → meminj_injective f.
Proof. eauto using cmap_refine_memenv_refine, memenv_refine_injective. Qed.
Lemma cmap_refine_valid_l Γ α f Γm1 Γm2 m1 m2 :
  m1 ⊑{Γ,α,f@Γm1↦Γm2} m2 → ✓{Γ,Γm1} m1.
Proof. by intros (?&?&?&?). Qed.
Lemma cmap_refine_valid_l' Γ α f m1 m2: m1 ⊑{Γ,α,f} m2 → ✓{Γ} m1.
Proof. by apply cmap_refine_valid_l. Qed.
Lemma cmap_refine_valid_r Γ α f Γm1 Γm2 m1 m2 :
  m1 ⊑{Γ,α,f@Γm1↦Γm2} m2 → ✓{Γ,Γm2} m2.
Proof. by intros (?&?&?&?). Qed.
Lemma cmap_refine_valid_r' Γ α f m1 m2: m1 ⊑{Γ,α,f} m2 → ✓{Γ} m2.
Proof. by apply cmap_refine_valid_r. Qed.
Hint Immediate cmap_refine_valid_l cmap_refine_valid_r.
Lemma cmap_refine_id Γ α Γm m : ✓ Γ → ✓{Γ,Γm} m → m ⊑{Γ,α@Γm} m.
Proof.
  destruct m as [m]; intros ? Hm.
  do 2 red; split_ands; simpl; auto using memenv_refine_id.
  intros ? o r w malloc; rewrite lookup_meminj_id; intros; simplify_equality'.
  destruct (proj2 Hm o w malloc) as (τ&?&_&?&_); auto.
  exists w w; eauto 6 using ctree_refine_id, type_of_typed.
Qed.
Lemma cmap_refine_id' Γ α m : ✓ Γ → ✓{Γ} m → m ⊑{Γ,α} m.
Proof. by apply cmap_refine_id. Qed.
Lemma cmap_refine_compose Γ α1 α2 f1 f2 Γm1 Γm2 Γm3 m1 m2 m3 :
  ✓ Γ → m1 ⊑{Γ,α1,f1@Γm1↦Γm2} m2 → m2 ⊑{Γ,α2,f2@Γm2↦Γm3} m3 →
  m1 ⊑{Γ,α1||α2,f2 ◎ f1@Γm1↦Γm3} m3.
Proof.
  intros ? (?&?&?&Hm12) (?&Hm3&?&Hm23);
    split; split_ands; eauto 2 using memenv_refine_compose.
  intros o1 o3 r w1 malloc.
  rewrite lookup_meminj_compose_Some; intros (o2&r2&r3&?&?&->) Hw1.
  destruct (Hm12 o1 o2 r2 w1 malloc) as (w2&w2'&τ2&?&?&?&?); auto.
  destruct (Hm23 o2 o3 r3 w2 malloc) as (w3&w3'&τ3&->&?&?&?); auto.
  destruct (ctree_lookup_refine Γ α2 f2 Γm2 Γm3 w2 w3' τ3
    (freeze true <$> r2) w2') as (w3''&?&Hw23); auto.
  erewrite ctree_refine_type_of_r in Hw23 by eauto. exists w3 w3'' τ2.
  rewrite fmap_app, ctree_lookup_app; simplify_option_equality.
  naive_solver eauto using ctree_refine_compose.
Qed.
Lemma cmap_refine_compose' Γ α1 α2 f1 f2 m1 m2 m3 :
  ✓ Γ → m1 ⊑{Γ,α1,f1} m2 → m2 ⊑{Γ,α2,f2} m3 → m1 ⊑{Γ,α1||α2,f2 ◎ f1} m3.
Proof. by apply cmap_refine_compose. Qed.
Lemma cmap_refine_inverse' Γ f m1 m2 :
  m1 ⊑{Γ,false,f} m2 → m2 ⊑{Γ,false,meminj_inverse f} m1.
Proof.
  intros (?&Hm2&?&Hm); split; split_ands; eauto using memenv_refine_inverse.
  intros o2 o1 r w2 malloc ??.
  destruct (proj2 Hm2 o2 w2 malloc) as (τ&?&?&?&_); auto.
  destruct (lookup_meminj_inverse_1 Γ f ('{m1}) ('{m2}) o1 o2 r τ)
    as (?&?&->); auto.
  assert (index_alive' m1 o1) as help; [|unfold index_alive' in help].
  { apply index_alive_spec'; eauto using memenv_refine_alive_r. }
  destruct (index_typed_lookup_cmap m1 o1 τ) as ([|w1 malloc']&?&?);
    simplify_map_equality; try done.
  destruct (Hm o1 o2 [] w1 malloc') as (?&w1'&τ'&?&?&?&?);
    simplify_type_equality'; auto.
  exists w1 w1 τ'; split_ands; auto using ctree_refine_inverse.
Qed.
Lemma cmap_lookup_refine Γ α f Γm1 Γm2 m1 m2 a1 a2 w1 τ :
  ✓ Γ → m1 ⊑{Γ,α,f@Γm1↦Γm2} m2 →
  a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : τ → m1 !!{Γ} a1 = Some w1 →
  ∃ w2, m2 !!{Γ} a2 = Some w2 ∧ w1 ⊑{Γ,α,f@Γm1↦Γm2} w2 : τ.
Proof.
  destruct m1 as [m1], m2 as [m2]; simpl; intros ? (Hm1&_&_&Hm) Ha Hw1.
  assert ((Γ,Γm1) ⊢ a1 : τ) by eauto using addr_refine_typed_l.
  assert ((Γ,Γm2) ⊢ a2 : τ) by eauto using addr_refine_typed_r.
  case_option_guard; simplify_type_equality'.
  rewrite option_guard_True by eauto using addr_strict_refine.
  destruct (m1 !! addr_index a1) as [[|w1' β]|] eqn:?; simplify_equality'.
  destruct (w1' !!{Γ} addr_ref Γ a1) as [w1''|] eqn:?; simplify_equality'.
  destruct (addr_ref_refine Γ α f Γm1 Γm2 a1 a2 τ) as (r&?&->); auto.
  destruct (Hm (addr_index a1) (addr_index a2) r w1' β)
    as (w2&w2'&τ2&->&Hr&?&_); auto; csimpl.
  destruct (ctree_lookup_Some Γ Γm1 w1' τ2
    (addr_ref Γ a1) w1'') as (σ'&?&?); eauto using ctree_refine_typed_l.
  rewrite ctree_lookup_app, Hr; csimpl.
  destruct (ctree_lookup_refine Γ α f Γm1 Γm2 w1' w2' τ2
    (addr_ref Γ a1) w1'') as (w2''&->&?); auto; csimpl.
  rewrite <-(decide_iff _ _ _ _ (addr_is_obj_refine _ _ _ _ _ _ _ _ Ha));
    case_decide; simplify_equality'.
  { cut (τ = σ'); [intros; simplify_type_equality; eauto|].
    erewrite <-(addr_is_obj_type_base _ _ a1 τ) by eauto.
    assert ((Γ,Γm1) ⊢ w1' : τ2) by eauto using ctree_refine_typed_l.
    assert (Γm1 ⊢ addr_index a1 : addr_type_object a1)
      by eauto using addr_typed_index, addr_refine_typed_l.
    destruct (proj2 Hm1 (addr_index a1) w1' β)
      as (?&?&_&?&_); auto; simplify_type_equality'.
    eauto using ref_set_offset_typed_unique, addr_typed_ref_base_typed. }
  case_option_guard; simplify_equality'; rewrite option_guard_True
    by intuition eauto using pbits_refine_unshared, ctree_flatten_refine.
  assert (τ = ucharT) by (intuition eauto using
    addr_not_obj_type, addr_refine_typed_l); subst.
  erewrite <-addr_ref_byte_refine by eauto.
  eauto using ctree_lookup_byte_refine.
Qed.
Lemma cmap_refine_weaken Γ Γ' α α' f f' Γm1 Γm2 m1 m2 :
  ✓ Γ → m1 ⊑{Γ,α,f@Γm1↦Γm2} m2 → Γ ⊆ Γ' → (α → α') →
  Γm1 ⊑{Γ',α',f'} Γm2 → meminj_extend f f' Γm1 Γm2 →
  m1 ⊑{Γ',α',f'@Γm1↦Γm2} m2.
Proof.
  intros ? (Hm1&?&HΓm&Hm) ?? Hf.
  split; split_ands; eauto using cmap_valid_weaken.
  intros o1 o2 r w1 malloc ??.
  destruct (proj2 Hm1 o1 w1 malloc) as (τ&?&_); auto.
  destruct (Hm o1 o2 r w1 malloc)
    as (w2&w2'&τ'&?&?&?&?); eauto using option_eq_1, meminj_extend_left.
  exists w2 w2' τ'; split_ands;
    eauto using ctree_refine_weaken, ctree_lookup_weaken, option_eq_1_alt.
Qed.
Lemma cmap_alter_refine Γ α f Γm1 Γm2 g1 g2 m1 m2 a1 a2 w1 w2 τ :
  ✓ Γ → m1 ⊑{Γ,α,f@Γm1↦Γm2} m2 → a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : τ →
  m1 !!{Γ} a1 = Some w1 → m2 !!{Γ} a2 = Some w2 → ¬ctree_unmapped w1 →
  g1 w1 ⊑{Γ,α,f@Γm1↦Γm2} g2 w2 : τ → ¬ctree_unmapped (g1 w1) →
  cmap_alter Γ g1 a1 m1 ⊑{Γ,α,f@Γm1↦Γm2} cmap_alter Γ g2 a2 m2.
Proof.
  intros ? (Hm1&Hm2&?&Hm) Ha Hw1 Hw2 Hw1' ? Hgw1.
  assert ((Γ,Γm1) ⊢ a1 : τ) by eauto using addr_refine_typed_l.
  assert ((Γ,Γm2) ⊢ a2 : τ) by eauto using addr_refine_typed_r.
  assert ((Γ,Γm1) ⊢ w1 : τ) by eauto using cmap_lookup_typed.
  assert ((Γ,Γm2) ⊢ w2 : τ) by eauto using cmap_lookup_typed.
  assert (¬ctree_unmapped (g2 w2)) as Hgw2
    by eauto using pbits_refine_mapped, ctree_flatten_refine. 
  split; split_ands; auto.
  { eapply cmap_alter_valid; eauto.
    simplify_type_equality; eauto using ctree_refine_typed_l. }
  { eapply cmap_alter_valid; eauto.
    simplify_type_equality; eauto using ctree_refine_typed_r. }
  intros o3 o4 r4 w3 malloc ? Hw3. destruct m1 as [m1], m2 as [m2]; simpl in *.
  repeat case_option_guard; simplify_type_equality'.
  destruct (addr_ref_refine Γ α f Γm1 Γm2 a1 a2 τ) as (r2&?&Hr2); auto.
  rewrite Hr2 in Hw2 |- *; clear Hr2.
  destruct (m1 !! addr_index a1) as [[|w1' ?]|] eqn:?; simplify_equality'.
  destruct (m2 !! addr_index a2) as [[|w2' ?]|] eqn:?; simplify_equality'.
  rewrite ctree_lookup_app in Hw2.
  destruct (w1' !!{Γ} addr_ref Γ a1) as [w1''|] eqn:?; simplify_equality'.
  destruct (decide (o3 = addr_index a1)); simplify_map_equality'.
  * destruct (Hm (addr_index a1) (addr_index a2) r2 w1' malloc)
      as (?&w2''&τ2&?&?&?&?); auto.
    destruct (ctree_lookup_refine Γ α f Γm1 Γm2 w1' w2'' τ2
      (addr_ref Γ a1) w1'') as (w2'''&?&?); auto; simplify_map_equality'.
    eexists _, (ctree_alter Γ _ (addr_ref Γ a1) w2''), τ2; split_ands; eauto.
    { by erewrite ctree_alter_app, ctree_lookup_alter
        by eauto using ctree_lookup_unfreeze. }
    assert (addr_is_obj a1 ↔ addr_is_obj a2) by eauto using addr_is_obj_refine.
    simplify_option_equality; try tauto.
    { eapply ctree_alter_refine; eauto; simplify_type_equality; eauto using
        ctree_Forall_not, ctree_refine_typed_l, ctree_refine_typed_r. }
    assert (τ = ucharT) by (intuition eauto using addr_not_obj_type); subst.
    erewrite addr_ref_byte_refine in Hw1 |- * by eauto.
    eapply ctree_alter_refine; eauto using ctree_alter_byte_refine.
    contradict Hgw1. eapply (ctree_alter_byte_unmapped _ _ _ w1'');
      eauto using ctree_alter_lookup_Forall, ctree_refine_typed_l.
  * destruct (meminj_injective_ne f (addr_index a1)
      (addr_index a2) o3 o4 r2 r4) as [?|[??]];
      eauto using memenv_refine_injective; simplify_map_equality'; [eauto|].
    destruct (Hm o3 (addr_index a2) r4 w3 malloc)
      as (w4''&w4'&τ4&?&?&?&?); auto; simplify_map_equality'.
    eexists _, w4', τ4; split_ands; eauto.
    by erewrite ctree_alter_app, ctree_lookup_alter_disjoint by
      (eauto; by apply ref_disjoint_freeze_l, ref_disjoint_freeze_r).
Qed.
End memory_map.
