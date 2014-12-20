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

Arguments lookupE _ _ _ _ _ _ _ !_ /.
Arguments cmap_lookup _ _ _ _ !_ /.
Hint Extern 0 (Separation _) => apply (_ : Separation (pbit Ti)).

Lemma cmap_lookup_disjoint Γ Γm m1 m2 a w1 w2 :
  ✓ Γ → ✓{Γ,Γm} m1 → ✓{Γ,Γm} m2 → m1 ⊥ m2 →
  m1 !!{Γ} a = Some w1 → m2 !!{Γ} a = Some w2 → w1 ⊥ w2.
Proof.
  destruct m1 as [m1], m2 as [m2]; simpl.
  intros ? Hm1 Hm2 Hm ??. case_option_guard; simplify_equality'.
  specialize (Hm (addr_index a)).
  destruct (m1 !! addr_index a) as [[|w1' β]|] eqn:Hw1; simplify_equality'.
  destruct (m2 !! addr_index a) as [[|w2' β']|] eqn:Hw2; simplify_equality'.
  destruct (w1' !!{Γ} addr_ref Γ a) as [w1''|] eqn:?; simplify_equality'.
  destruct (w2' !!{Γ} addr_ref Γ a) as [w2''|] eqn:?; simplify_equality'.
  destruct (proj2 Hm1 (addr_index a) w1' β) as (τ&?&?&?&_),
    (proj2 Hm2 (addr_index a) w2' β') as (?&?&?&?&_);
    auto; simplify_type_equality'.
  simplify_option_equality; naive_solver
    eauto 3 using ctree_lookup_byte_disjoint, ctree_lookup_disjoint.
Qed.
Lemma cmap_lookup_subseteq Γ m1 m2 a w1 :
  ✓ Γ → m1 ⊆ m2 → m1 !!{Γ} a = Some w1 → ¬ctree_Forall sep_unmapped w1 →
  ∃ w2, m2 !!{Γ} a = Some w2 ∧ w1 ⊆ w2.
Proof.
  destruct m1 as [m1], m2 as [m2]; simpl.
  intros ? Hm ??. case_option_guard; simplify_equality'.
  specialize (Hm (addr_index a)).
  destruct (m1 !! (addr_index a)) as [[|w1' β]|] eqn:?,
    (m2 !! (addr_index a)) as [[|w2' β']|] eqn:?; simplify_equality'; try done.
  destruct (w1' !!{Γ} addr_ref Γ a) as [w1''|] eqn:?; simplify_equality'.
  destruct (ctree_lookup_subseteq Γ w1' w2' (addr_ref Γ a) w1'')
    as (w2''&?&?); simplify_option_equality; intuition eauto using
    ctree_lookup_byte_Forall, pbit_unmapped_indetify,ctree_lookup_byte_subseteq.
  exfalso; eauto using @ctree_unshared_weaken.
Qed.
Lemma cmap_alter_disjoint Γ Γm1 m1 m2 g a w1 τ1 :
  ✓ Γ → ✓{Γ,Γm1} m1 → m1 ⊥ m2 →
  (Γ,Γm1) ⊢ a : Some τ1 → m1 !!{Γ} a = Some w1 → (Γ,Γm1) ⊢ g w1 : τ1 →
  ¬ctree_unmapped (g w1) →
  (∀ w2, w1 ⊥ w2 → g w1 ⊥ w2) → cmap_alter Γ g a m1 ⊥ m2.
Proof.
  assert (∀ w', ctree_empty w' → ctree_unmapped w').
  { eauto using Forall_impl, @sep_unmapped_empty_alt. }
  destruct m1 as [m1], m2 as [m2]; simpl. intros ? Hm1 Hm ????? o.
  specialize (Hm o). case_option_guard; simplify_type_equality'.
  destruct (decide (o = addr_index a)); simplify_map_equality'; [|apply Hm].
  destruct (m1 !! addr_index a) as [[|w1' β]|] eqn:?; simplify_equality'.
  destruct (w1' !!{Γ} addr_ref Γ a) as [w1''|] eqn:?; simplify_equality'.
  destruct (proj2 Hm1 (addr_index a) w1' β)
    as (τ&?&_&?&_); auto; simplify_equality'.
  destruct (ctree_lookup_Some Γ Γm1 w1' τ (addr_ref Γ a) w1'')
    as (τ'&_&?); auto.
  destruct (m2 !! addr_index a) as [[|w2' ?]|] eqn:?; try done.
  * destruct Hm as [(?&?&?)?]; case_decide; simplify_option_equality.
    { split_ands; eauto using ctree_alter_disjoint, ctree_alter_lookup_Forall. }
    assert (τ1 = ucharT%T) by eauto using addr_not_is_obj_type.
    simplify_equality; split_ands; auto.
    { eapply ctree_alter_disjoint; intuition eauto 3
        using ctree_alter_byte_unmapped, ctree_alter_byte_disjoint. }
    intuition eauto using ctree_alter_byte_unmapped, ctree_alter_lookup_Forall.
  * assert (∃ w2', w1' ⊥ w2') as (w2'&?).
    { exists (ctree_new Γ ∅ τ); symmetry. eauto using ctree_new_disjoint. }
    destruct Hm. case_decide; simplify_option_equality.
    { intuition eauto using ctree_alter_disjoint, ctree_alter_lookup_Forall,
        @ctree_disjoint_valid_l, ctree_alter_disjoint. }
    assert (τ1 = ucharT%T) by eauto using addr_not_is_obj_type.
    simplify_equality. split.
    { eapply ctree_disjoint_valid_l, ctree_alter_disjoint; intuition eauto 3
        using ctree_alter_byte_disjoint, ctree_alter_byte_unmapped. }
    intuition eauto using ctree_alter_byte_unmapped, ctree_alter_lookup_Forall.
Qed.
Lemma cmap_alter_union Γ Γm1 m1 m2 g a w1 τ1 :
  ✓ Γ → ✓{Γ,Γm1} m1 → m1 ⊥ m2 →
  (Γ,Γm1) ⊢ a : Some τ1 → m1 !!{Γ} a = Some w1 → (Γ,Γm1) ⊢ g w1 : τ1 →
  ¬ctree_unmapped (g w1) →
  (∀ w2, w1 ⊥ w2 → g w1 ⊥ w2) → (∀ w2, w1 ⊥ w2 → g (w1 ∪ w2) = g w1 ∪ w2) →
  cmap_alter Γ g a (m1 ∪ m2) = cmap_alter Γ g a m1 ∪ m2.
Proof.
  destruct m1 as [m1], m2 as [m2]; unfold union, sep_union; simpl.
  intros ? Hm1 Hm ??????; f_equal; apply map_eq; intros o.
  case_option_guard; simplify_type_equality'.
  destruct (decide (addr_index a = o)) as [<-|?]; rewrite !lookup_union_with,
    ?lookup_alter, ?lookup_alter_ne, ?lookup_union_with by done; auto.
  specialize (Hm (addr_index a)).
  destruct (m1 !! addr_index a) as [[|w1' β]|] eqn:?,
    (m2 !! addr_index a) as [[|w2' ?]|]; simplify_equality'; do 2 f_equal.
  destruct (w1' !!{Γ} addr_ref Γ a) as [w1''|] eqn:?; simplify_equality'.
  destruct (proj2 Hm1 (addr_index a) w1' β)
    as (τ&?&_&?&_); auto; simplify_equality'.
  destruct (ctree_lookup_Some Γ Γm1 w1' τ (addr_ref Γ a) w1'') as (τ'&_&?); auto.
  destruct Hm as [(?&?&?)?]; case_decide; simplify_option_equality.
  { eauto using ctree_alter_union. }
  assert (τ1 = ucharT%T) by eauto using addr_not_is_obj_type.
  simplify_equality. eapply ctree_alter_union; intuition eauto 3 using
   ctree_alter_byte_disjoint, ctree_alter_byte_union, ctree_alter_byte_unmapped.
Qed.
End memory_map.
