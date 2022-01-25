(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
From stdpp Require Import fin_maps.
Require Export memory_map memory_trees_refine.
Local Open Scope ctype_scope.

#[global] Instance cmap_refine `{Env K} :
    Refine K (env K) (mem K) := λ Γ α f Δ1 Δ2 m1 m2,
  (**i 1.) *) ✓{Γ,Δ1} m1 ∧
  (**i 2.) *) ✓{Γ,Δ2} m2 ∧
  (**i 3.) *) Δ1 ⊑{Γ,α,f} Δ2 ∧
  (**i 4.) *) (∀ o1 o2 r w1 μ,
    f !! o1 = Some (o2,r) → cmap_car m1 !! o1 = Some (Obj w1 μ) →
    ∃ w2 w2' τ,
      cmap_car m2 !! o2 = Some (Obj w2 μ) ∧ w2 !!{Γ} r = Some w2' ∧
      w1 ⊑{Γ,α,f@Δ1↦Δ2} w2' : τ ∧ (μ → r = [])).
#[global] Instance cmap_refine' `{Env K} : RefineM K (env K) (mem K) := λ Γ α f m1 m2,
  m1 ⊑{Γ,α,f@memenv_of m1↦memenv_of m2} m2.

Section memory_map.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types m : mem K.
Implicit Types Δ : memenv K.
Implicit Types τ σ : type K.
Implicit Types o : index.
Implicit Types w : mtree K.
Implicit Types rs : ref_seg K.
Implicit Types r : ref K.
Implicit Types a : addr K.
Implicit Types f : meminj K.
Implicit Types g : mtree K → mtree K.
Implicit Types α μ : bool.

Lemma cmap_refine_memenv_refine Γ α f Δ1 Δ2 m1 m2 :
  m1 ⊑{Γ,α,f@Δ1↦Δ2} m2 → Δ1 ⊑{Γ,α,f} Δ2.
Proof. by intros (?&?&?&?). Qed.
Lemma cmap_refine_memenv_refine' Γ α f m1 m2 :
  m1 ⊑{Γ,α,f} m2 → '{m1} ⊑{Γ,α,f} '{m2}.
Proof. by apply cmap_refine_memenv_refine. Qed.
Lemma cmap_refine_injective Γ α f Δ1 Δ2 m1 m2 :
  m1 ⊑{Γ,α,f@Δ1↦Δ2} m2 → meminj_injective f.
Proof. eauto using cmap_refine_memenv_refine, memenv_refine_injective. Qed.
Lemma cmap_refine_valid_l Γ α f Δ1 Δ2 m1 m2 :
  m1 ⊑{Γ,α,f@Δ1↦Δ2} m2 → ✓{Γ,Δ1} m1.
Proof. by intros (?&?&?&?). Qed.
Lemma cmap_refine_valid_l' Γ α f m1 m2: m1 ⊑{Γ,α,f} m2 → ✓{Γ} m1.
Proof. by apply cmap_refine_valid_l. Qed.
Lemma cmap_refine_valid_r Γ α f Δ1 Δ2 m1 m2 :
  m1 ⊑{Γ,α,f@Δ1↦Δ2} m2 → ✓{Γ,Δ2} m2.
Proof. by intros (?&?&?&?). Qed.
Lemma cmap_refine_valid_r' Γ α f m1 m2: m1 ⊑{Γ,α,f} m2 → ✓{Γ} m2.
Proof. by apply cmap_refine_valid_r. Qed.
Hint Immediate cmap_refine_valid_l cmap_refine_valid_r: core.
Lemma cmap_refine_id Γ α Δ m : ✓ Γ → ✓{Γ,Δ} m → m ⊑{Γ,α@Δ} m.
Proof.
  destruct m as [m]; intros ? Hm.
  do 2 red; split_and ?; simpl; auto using memenv_refine_id.
  intros ? o r w μ; rewrite lookup_meminj_id; intros; simplify_equality'.
  destruct (cmap_valid_Obj Γ Δ (CMap m) o w μ) as (τ&?&_&?&_); auto.
  exists w, w; eauto 6 using ctree_refine_id, type_of_typed.
Qed.
Lemma cmap_refine_id' Γ α m : ✓ Γ → ✓{Γ} m → m ⊑{Γ,α} m.
Proof. by apply cmap_refine_id. Qed.
Lemma cmap_refine_compose Γ α1 α2 f1 f2 Δ1 Δ2 Δ3 m1 m2 m3 :
  ✓ Γ → m1 ⊑{Γ,α1,f1@Δ1↦Δ2} m2 → m2 ⊑{Γ,α2,f2@Δ2↦Δ3} m3 →
  m1 ⊑{Γ,α1||α2,f2 ◎ f1@Δ1↦Δ3} m3.
Proof.
  intros ? (?&?&?&Hm12) (?&Hm3&?&Hm23);
    split; split_and ?; eauto 2 using memenv_refine_compose.
  intros o1 o3 r w1 μ.
  rewrite lookup_meminj_compose_Some; intros (o2&r2&r3&?&?&->) Hw1.
  destruct (Hm12 o1 o2 r2 w1 μ) as (w2&w2'&τ2&?&?&?&?); auto.
  destruct (Hm23 o2 o3 r3 w2 μ) as (w3&w3'&τ3&->&?&?&?); auto.
  destruct (ctree_lookup_refine Γ α2 f2 Δ2 Δ3 w2 w3' τ3 r2 w2')
    as (w3''&?&Hw23); auto.
  erewrite ctree_refine_type_of_r in Hw23 by eauto. exists w3, w3'', τ2.
  rewrite ctree_lookup_app; simplify_option_eq.
  naive_solver eauto using ctree_refine_compose.
Qed.
Lemma cmap_refine_compose' Γ α1 α2 f1 f2 m1 m2 m3 :
  ✓ Γ → m1 ⊑{Γ,α1,f1} m2 → m2 ⊑{Γ,α2,f2} m3 → m1 ⊑{Γ,α1||α2,f2 ◎ f1} m3.
Proof. by apply cmap_refine_compose. Qed.
Lemma cmap_refine_inverse' Γ f m1 m2 :
  m1 ⊑{Γ,false,f} m2 → m2 ⊑{Γ,false,meminj_inverse f} m1.
Proof.
  intros (?&Hm2&?&Hm); split; split_and ?; eauto using memenv_refine_inverse.
  intros o2 o1 r w2 μ ??.
  destruct (cmap_valid_Obj Γ '{m2} m2 o2 w2 μ) as (τ&?&?&?&_); auto.
  destruct (lookup_meminj_inverse_1 Γ f '{m1} '{m2} o1 o2 r τ)
    as (?&?&->); auto.
  assert (index_alive' m1 o1) as help; [|unfold index_alive' in help].
  { apply index_alive_spec'; eauto using memenv_refine_alive_r. }
  destruct (index_typed_lookup_cmap m1 o1 τ) as ([|w1 μ']&?&?);
    simplify_map_eq; try done.
  destruct (Hm o1 o2 [] w1 μ') as (?&w1'&τ'&?&?&?&?);
    simplify_type_equality'; auto.
  exists w1, w1, τ'; split_and ?; auto using ctree_refine_inverse.
Qed.
Lemma cmap_refine_weaken Γ Γ' α α' f f' Δ1 Δ2 m1 m2 :
  ✓ Γ → m1 ⊑{Γ,α,f@Δ1↦Δ2} m2 → Γ ⊆ Γ' → (α → α') →
  Δ1 ⊑{Γ',α',f'} Δ2 → meminj_extend f f' Δ1 Δ2 →
  m1 ⊑{Γ',α',f'@Δ1↦Δ2} m2.
Proof.
  intros ? (Hm1&?&HΔ&Hm) ?? Hf.
  split; split_and ?; eauto using cmap_valid_weaken,
    memenv_valid_weaken, cmap_valid_memenv_valid.
  intros o1 o2 r w1 μ ??.
  destruct (cmap_valid_Obj Γ Δ1 m1 o1 w1 μ) as (τ&?&_); auto.
  destruct (Hm o1 o2 r w1 μ)
    as (w2&w2'&τ'&?&?&?&?); eauto using option_eq_1, meminj_extend_left.
  exists w2, w2', τ'; split_and ?;
    eauto using ctree_refine_weaken, ctree_lookup_weaken, option_eq_1_alt.
Qed.
Lemma cmap_lookup_alter_refine Γ Δ g m a w τ :
  ✓ Γ → ✓{Γ,Δ} m → (Γ,Δ) ⊢ a : TType τ →
  m !!{Γ} a = Some w → (Γ,Δ) ⊢ g w : τ → ctree_unshared (g w) →
  ∃ w', cmap_alter Γ g a m !!{Γ} a = Some w' ∧ w' ⊑{Γ,true@Δ} g w : τ.
Proof.
  intros. destruct (decide (addr_is_obj a)).
  { exists (g w). erewrite cmap_lookup_alter by eauto.
    eauto using ctree_refine_id. }
  exists (ctree_lookup_byte_after Γ (addr_type_base a)
    (addr_ref_byte Γ a) (g w)); split; eauto using cmap_lookup_alter_not_obj.
  assert (τ = ucharT) by eauto using addr_not_is_obj_type; subst.
  eauto using ctree_lookup_byte_alter_refine.
Qed.
Lemma cmap_lookup_ref_refine Γ α f Δ1 Δ2 m1 m2 o1 r1 o2 r2 w1 :
  ✓ Γ → m1 ⊑{Γ,α,f@Δ1↦Δ2} m2 → f !! o1 = Some (o2,r2) →
  m1 !!{Γ} (o1,r1) = Some w1 →
  ∃ w2, m2 !!{Γ} (o2,r1 ++ r2) = Some w2 ∧ w1 ⊑{Γ,α,f@Δ1↦Δ2} w2 : type_of w1.
Proof.
  destruct m1 as [m1], m2 as [m2]; simpl; intros ? (Hm1&_&_&Hm) Ha Hw1.
  destruct (m1 !! o1) as [[|w1' μ]|] eqn:?; simplify_equality'.
  destruct (Hm o1 o2 r2 w1' μ) as (w2&w2'&τ2&->&Hr&?&_); auto; csimpl.
  rewrite ctree_lookup_app, Hr; csimpl; eauto using ctree_lookup_refine.
Qed.
Lemma cmap_lookup_refine Γ α f Δ1 Δ2 m1 m2 a1 a2 w1 τ :
  ✓ Γ → m1 ⊑{Γ,α,f@Δ1↦Δ2} m2 →
  a1 ⊑{Γ,α,f@Δ1↦Δ2} a2 : TType τ → m1 !!{Γ} a1 = Some w1 →
  ∃ w2, m2 !!{Γ} a2 = Some w2 ∧ w1 ⊑{Γ,α,f@Δ1↦Δ2} w2 : τ.
Proof.
  intros. assert (type_of w1 = τ) by
    eauto using type_of_correct, cmap_lookup_typed, addr_refine_typed_l.
  unfold lookupE, cmap_lookup in *; case_option_guard; simplify_equality'.
  rewrite option_guard_True by eauto using addr_strict_refine.
  destruct (m1 !!{_} _) as [w1'|] eqn:?; simplify_equality'.
  destruct (addr_ref_refine Γ α f Δ1 Δ2 a1 a2 (TType (type_of w1)))
    as (r&?&_&?); auto.
  destruct (cmap_lookup_ref_refine Γ α f Δ1 Δ2 m1 m2 (addr_index a1)
    (addr_ref Γ a1) (addr_index a2) r w1') as (w2&?&?); auto.
  erewrite cmap_lookup_ref_le by eauto; simpl.
  destruct (decide (addr_is_obj a1)); simplify_equality'.
  { rewrite decide_True by (by erewrite <-addr_is_obj_refine by eauto).
    eauto. }
  case_option_guard; simplify_equality'.
  rewrite decide_False by (by erewrite <-addr_is_obj_refine by eauto).
  rewrite option_guard_True
    by eauto using pbits_refine_unshared, ctree_flatten_refine.
  erewrite <-addr_ref_byte_refine by eauto.
  assert (type_of w1 = ucharT) as ->
    by eauto using addr_not_is_obj_type, addr_refine_typed_l.
  eauto using ctree_lookup_byte_refine.
Qed.
Lemma cmap_alter_ref_refine Γ α f Δ1 Δ2 g1 g2 m1 m2 o1 r1 o2 r2 w1 w2 :
  ✓ Γ → m1 ⊑{Γ,α,f@Δ1↦Δ2} m2 → f !! o1 = Some (o2,r2) →
  m1 !!{Γ} (o1,r1) = Some w1 → m2 !!{Γ} (o2,r1 ++ r2) = Some w2 →
  g1 w1 ⊑{Γ,α,f@Δ1↦Δ2} g2 w2 : type_of w1 → ¬ctree_unmapped (g1 w1) →
  cmap_alter_ref Γ g1 o1 r1 m1
  ⊑{Γ,α,f@Δ1↦Δ2} cmap_alter_ref Γ g2 o2 (r1 ++ r2) m2.
Proof.
  intros ? Hm Hf Hw1 Hw2 Hg ?; split; split_and ?; eauto using
    cmap_refine_memenv_refine, cmap_alter_ref_valid, ctree_refine_typed_l.
  { eapply cmap_alter_ref_valid;
      eauto using pbits_refine_mapped, ctree_flatten_refine.
    destruct (cmap_lookup_ref_refine Γ α f Δ1 Δ2 m1 m2 o1 r1 o2 r2 w1)
      as (?&?&?); auto; simplify_equality'.
    erewrite ctree_refine_type_of_r by eauto.
    eauto using ctree_refine_typed_r. }
  destruct m1 as [m1], m2 as [m2]; destruct Hm as (Hm1&_&?&Hm); simpl in *.
  destruct (m1 !! o1) as [[|w1' μ1]|] eqn:?; simplify_equality'.
  destruct (Hm o1 o2 r2 w1' μ1)
    as (w2''&w2'&τ2&?&Hr&?&?); auto; simplify_option_eq.
  rewrite ctree_lookup_app in Hw2; simplify_option_eq.
  intros o3 o4 r4 w3 μ3 ? Hw3.
  destruct (decide (o3 = o1)); simplify_map_eq.
  { rewrite ctree_alter_app; eauto 10 using ctree_lookup_alter,
      ctree_lookup_le, ref_freeze_le_r, ctree_alter_refine; eauto. }
  destruct (meminj_injective_ne f o1 o2 o3 o4 r2 r4) as [?|[??]];
    eauto using memenv_refine_injective; simplify_map_eq; [eauto|].
  destruct (Hm o3 o4 r4 w3 μ3)
    as (w4''&w4'&τ4&?&?&?&?); auto; simplify_map_eq.
  rewrite ctree_alter_app; eauto 10 using ctree_lookup_alter_disjoint.
Qed.
Lemma cmap_alter_refine Γ α f Δ1 Δ2 g1 g2 m1 m2 a1 a2 w1 w2 τ :
  ✓ Γ → m1 ⊑{Γ,α,f@Δ1↦Δ2} m2 → a1 ⊑{Γ,α,f@Δ1↦Δ2} a2 : TType τ →
  m1 !!{Γ} a1 = Some w1 → m2 !!{Γ} a2 = Some w2 → ¬ctree_unmapped w1 →
  g1 w1 ⊑{Γ,α,f@Δ1↦Δ2} g2 w2 : τ → ¬ctree_unmapped (g1 w1) →
  cmap_alter Γ g1 a1 m1 ⊑{Γ,α,f@Δ1↦Δ2} cmap_alter Γ g2 a2 m2.
Proof.
  intros. assert (type_of w1 = τ) by
    eauto using type_of_correct, cmap_lookup_typed, addr_refine_typed_l.
  unfold lookupE, cmap_lookup, cmap_alter in *;
    do 2 case_option_guard; simplify_equality'.
  destruct (m1 !!{_} _) as [w1'|] eqn:?,
    (m2 !!{_} _) as [w2'|] eqn:?; simplify_equality'.
  destruct (addr_ref_refine Γ α f Δ1 Δ2 a1 a2 (TType (type_of w1)))
    as (r&?&_&?); auto.
  erewrite <-(cmap_alter_ref_le _ _ _ _ (addr_ref Γ a2)) by eauto.
  destruct (cmap_lookup_ref_refine Γ α f Δ1 Δ2 m1 m2 (addr_index a1)
    (addr_ref Γ a1) (addr_index a2) r w1') as (w2''&?&?); auto.
  assert (w2'' = w2'); subst.
  { eapply cmap_lookup_ref_freeze_proper; eauto using (ref_freeze_le true). }
  assert (addr_is_obj a1 ↔ addr_is_obj a2) by eauto using addr_is_obj_refine.
  simplify_option_eq; try tauto; eauto using cmap_alter_ref_refine.
  assert (w1' !!{Γ} addr_ref_byte Γ a2 = Some w1)
    by (by erewrite <-(addr_ref_byte_refine _ _ _ _ _ _ a2) by eauto).
  assert (type_of w1 = ucharT) as Hw1_type
    by eauto using addr_not_is_obj_type, addr_refine_typed_l.
  rewrite Hw1_type in *.
  erewrite addr_ref_byte_refine by eauto.
  eapply cmap_alter_ref_refine; eauto 9 using ctree_alter_byte_refine,
    ctree_alter_byte_unmapped, ctree_refine_typed_l.
Qed.
End memory_map.
