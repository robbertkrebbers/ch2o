(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export memory_trees_separation memory_map.

Section memory_map.
Context `{EnvSpec Ti}.
Implicit Types Γ : env Ti.
Implicit Types m : mem Ti.
Implicit Types Γm : memenv Ti.
Implicit Types τ σ : type Ti.
Implicit Types w : mtree Ti.
Implicit Types a : addr Ti.
Implicit Types g : mtree Ti → mtree Ti.
Hint Extern 0 (Separation _) => apply (_ : Separation (pbit Ti)).

Lemma cmap_valid_subseteq Γ Γm m1 m2 : ✓ Γ → ✓{Γ,Γm} m2 → m1 ⊆ m2 → ✓{Γ,Γm} m1.
Proof.
  destruct m1 as [m1], m2 as [m2]; intros ? (?&Hm2&Hm2') Hm; split_ands'.
  * done.
  * intros o τ ?; specialize (Hm o); simplify_option_equality.
    destruct (m2 !! o) as [[]|] eqn:?; destruct Hm; subst; eauto.
  * intros o w malloc ?; specialize (Hm o); simplify_option_equality.
    destruct (m2 !! o) as [[|w' malloc']|] eqn:?; try done.
    destruct Hm as [[??]?], (Hm2' o w' malloc') as (τ'&?&?&?&?);
      eauto 10 using ctree_typed_subseteq.
Qed.
Lemma cmap_lookup_ref_disjoint Γ Γm m1 m2 o r w1 w2 :
  ✓ Γ → ✓{Γ,Γm} m1 → ✓{Γ,Γm} m2 → m1 ⊥ m2 →
  m1 !!{Γ} (o,r) = Some w1 → m2 !!{Γ} (o,r) = Some w2 → w1 ⊥ w2.
Proof.
  destruct m1 as [m1], m2 as [m2]; intros ??? Hm ??; simplify_equality'.
  specialize (Hm o).
  destruct (m1 !! o) as [[|w1' β]|] eqn:Hw1,
    (m2 !! o) as [[|w2' β']|] eqn:Hw2; simplify_equality'.
  destruct (cmap_valid_Obj Γ Γm (CMap m1) o w1' β) as (τ&?&?&?&_),
    (cmap_valid_Obj Γ Γm (CMap m2) o w2' β') as (?&?&?&?&_);
    simplify_type_equality'; intuition eauto 3 using ctree_lookup_disjoint.
Qed.
Lemma cmap_lookup_disjoint Γ Γm m1 m2 a w1 w2 :
  ✓ Γ → ✓{Γ,Γm} m1 → ✓{Γ,Γm} m2 → m1 ⊥ m2 →
  m1 !!{Γ} a = Some w1 → m2 !!{Γ} a = Some w2 → w1 ⊥ w2.
Proof.
  unfold lookupE, cmap_lookup; intros; case_option_guard; simplify_equality'.
  destruct (m1 !!{_} _) as [w1'|] eqn:Hw1,
    (m2 !!{_} _) as [w2'|] eqn:Hw2; simplify_option_equality;
    eauto 3 using ctree_lookup_byte_disjoint, cmap_lookup_ref_disjoint.
Qed.
Lemma cmap_lookup_ref_subseteq Γ m1 m2 o r w1 :
  ✓ Γ → m1 ⊆ m2 → m1 !!{Γ} (o,r) = Some w1 → ¬ctree_Forall sep_unmapped w1 →
  ∃ w2, m2 !!{Γ} (o,r) = Some w2 ∧ w1 ⊆ w2.
Proof.
  destruct m1 as [m1], m2 as [m2]; simpl; intros ? Hm ??; specialize (Hm o).
  destruct (m1 !! o) as [[|w1' β]|] eqn:?,
    (m2 !! o) as [[|w2' β']|] eqn:?; simplify_equality'; try done.
  destruct (ctree_lookup_subseteq Γ w1' w2' r w1)
    as (w2''&?&?); simplify_option_equality; intuition eauto.
Qed.
Lemma cmap_lookup_subseteq Γ m1 m2 a w1 :
  ✓ Γ → m1 ⊆ m2 → m1 !!{Γ} a = Some w1 → ¬ctree_Forall sep_unmapped w1 →
  ∃ w2, m2 !!{Γ} a = Some w2 ∧ w1 ⊆ w2.
Proof.
  unfold lookupE, cmap_lookup; intros; case_option_guard; simplify_equality'.
  destruct (m1 !!{_} _) as [w1'|] eqn:Hw1; simplify_equality'.
  assert (¬ctree_unmapped w1').
  { simplify_option_equality; eauto using
      ctree_lookup_byte_Forall, pbit_unmapped_indetify. }
  destruct (cmap_lookup_ref_subseteq Γ m1 m2 (addr_index a)
    (addr_ref Γ a) w1') as (w2'&->&?); simpl; auto.
  simplify_option_equality by eauto using @ctree_unshared_weaken;
    eauto using ctree_lookup_byte_subseteq.
Qed.
Lemma cmap_alter_ref_disjoint Γ Γm1 m1 m2 g o r w1 :
  ✓ Γ → ✓{Γ,Γm1} m1 → m1 ⊥ m2 →
  m1 !!{Γ} (o,r) = Some w1 → ¬ctree_unmapped (g w1) →
  (∀ w2, w1 ⊥ w2 → g w1 ⊥ w2) → cmap_alter_ref Γ g o r m1 ⊥ m2.
Proof.
  assert (∀ w', ctree_empty w' → ctree_unmapped w').
  { eauto using Forall_impl, @sep_unmapped_empty_alt. }
  destruct m1 as [m1], m2 as [m2]; simpl; intros ? Hm1 Hm ??? o'.
  specialize (Hm o'); destruct (decide (o' = o)); simplify_map_equality'; auto.
  destruct (m1 !! o) as [[|w1' β]|] eqn:?; simplify_equality'; auto.
  destruct (cmap_valid_Obj Γ Γm1 (CMap m1) o w1' β)
    as (τ&?&_&?&_); auto; simplify_equality'.
  destruct (m2 !! o) as [[|w2' β']|]; simplify_equality; auto.
  { intuition eauto using ctree_alter_disjoint, ctree_alter_lookup_Forall. }
  assert (∃ w2', w1' ⊥ w2') as (w2'&?).
  { exists (ctree_new Γ ∅ τ); symmetry. eauto using ctree_new_disjoint. }
  split.
  { eapply ctree_disjoint_valid_l, ctree_alter_disjoint; intuition eauto. }
  intuition eauto using ctree_alter_lookup_Forall.
Qed.
Lemma cmap_alter_disjoint Γ Γm1 m1 m2 g a w1 τ1 :
  ✓ Γ → ✓{Γ,Γm1} m1 → m1 ⊥ m2 →
  (Γ,Γm1) ⊢ a : Some τ1 → m1 !!{Γ} a = Some w1 → (Γ,Γm1) ⊢ g w1 : τ1 →
  ¬ctree_unmapped (g w1) →
  (∀ w2, w1 ⊥ w2 → g w1 ⊥ w2) → cmap_alter Γ g a m1 ⊥ m2.
Proof.
  assert (∀ w', ctree_empty w' → ctree_unmapped w').
  { eauto using Forall_impl, @sep_unmapped_empty_alt. }
  unfold lookupE, cmap_lookup; intros; case_option_guard; simplify_equality'.
  destruct (m1 !!{_} _) as [w1'|] eqn:Hw1; simplify_equality'.
  destruct (cmap_lookup_ref_Some Γ Γm1 m1 (addr_index a) (addr_ref Γ a) w1')
    as (τ&σ&?&?&?); auto.
  eapply cmap_alter_ref_disjoint; eauto.
  { simplify_option_equality; eauto.
    assert (τ1 = ucharT%T) by eauto using addr_not_is_obj_type; subst.
    intuition eauto 3 using ctree_alter_byte_unmapped. }
  intros; simplify_option_equality; eauto using ctree_alter_byte_disjoint.
Qed.
Lemma cmap_alter_ref_union Γ Γm1 m1 m2 g o r w1 τ1 :
  ✓ Γ → ✓{Γ,Γm1} m1 → m1 ⊥ m2 →
  m1 !!{Γ} (o,r) = Some w1 → ¬ctree_unmapped (g w1) →
  (∀ w2, w1 ⊥ w2 → g w1 ⊥ w2) → (∀ w2, w1 ⊥ w2 → g (w1 ∪ w2) = g w1 ∪ w2) →
  cmap_alter_ref Γ g o r (m1 ∪ m2) = cmap_alter_ref Γ g o r m1 ∪ m2.
Proof.
  destruct m1 as [m1], m2 as [m2]; simpl; intros ? Hm1 Hm ????.
  unfold union at 2, sep_union; f_equal'; apply map_eq; intros o'.
  specialize (Hm o'); destruct (decide (o' = o)); simplify_map_equality';
    rewrite !lookup_union_with, ?lookup_alter,
    ?lookup_alter_ne, ?lookup_union_with by done; auto.
  destruct (m1 !! o) as [[|w1' β]|] eqn:?; simplify_equality'; auto.
  destruct (cmap_valid_Obj Γ Γm1 (CMap m1) o w1' β)
    as (τ&?&_&?&_); auto; simplify_equality'.
  destruct (m2 !! o) as [[|w2' β']|]; simplify_equality'; do 2 f_equal'.
  intuition eauto using ctree_alter_union.
Qed.
Lemma cmap_alter_union Γ Γm1 m1 m2 g a w1 τ1 :
  ✓ Γ → ✓{Γ,Γm1} m1 → m1 ⊥ m2 → (Γ,Γm1) ⊢ a : Some τ1 →
  m1 !!{Γ} a = Some w1 → (Γ,Γm1) ⊢ g w1 : τ1 → ¬ctree_unmapped (g w1) →
  (∀ w2, w1 ⊥ w2 → g w1 ⊥ w2) → (∀ w2, w1 ⊥ w2 → g (w1 ∪ w2) = g w1 ∪ w2) →
  cmap_alter Γ g a (m1 ∪ m2) = cmap_alter Γ g a m1 ∪ m2.
Proof.
  unfold lookupE, cmap_lookup, cmap_alter;
    intros; case_option_guard; simplify_equality'.
  destruct (m1 !!{_} _) as [w1'|] eqn:Hw1; simplify_equality'.
  destruct (cmap_lookup_ref_Some Γ Γm1 m1 (addr_index a) (addr_ref Γ a) w1')
    as (τ&σ&?&?&?); auto.
  eapply cmap_alter_ref_union; eauto.
  * simplify_option_equality; eauto.
    assert (τ1 = ucharT%T) by eauto using addr_not_is_obj_type; subst.
    intuition eauto 3 using ctree_alter_byte_unmapped.
  * intros; simplify_option_equality; eauto using ctree_alter_byte_disjoint.
  * intros; simplify_option_equality; eauto using ctree_alter_byte_union.
Qed.
Lemma cmap_singleton_disjoint Γ Γm a malloc w1 w2 τ :
  ✓ Γ → (Γ,Γm) ⊢ a : Some τ → addr_strict Γ a →
  w1 ⊥ w2 → ¬ctree_unmapped w1 → ¬ctree_unmapped w2 →
  cmap_singleton Γ a malloc w1 ⊥ cmap_singleton Γ a malloc w2.
Proof.
  intros ???? Hperm1 Hperm2 o.
  destruct (decide (o = addr_index a)); simplify_map_equality'; auto.
  split_ands; eauto 10 using ctree_singleton_disjoint, addr_typed_ref_typed,
    addr_typed_type_object_valid, Forall_impl,
    @sep_unmapped_empty_alt, ctree_singleton_Forall_inv.
Qed.
Lemma cmap_singleton_union Γ Γm a malloc w1 w2 τ :
  ✓ Γ → (Γ,Γm) ⊢ a : Some τ → addr_strict Γ a →
  cmap_singleton Γ a malloc (w1 ∪ w2)
  = cmap_singleton Γ a malloc w1 ∪ cmap_singleton Γ a malloc w2.
Proof.
  intros. unfold union at 2; unfold sep_union,
    cmap_singleton, singleton, map_singleton; f_equal'.
  erewrite <-insert_union_with, (left_id_L ∅ _) by done.
  by erewrite ctree_singleton_union
    by eauto using addr_typed_ref_typed, addr_typed_type_object_valid.
Qed.
End memory_map.
