(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export memory_trees_separation memory_map.
Local Open Scope ctype_scope.

Section memory_map.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types m : mem K.
Implicit Types Δ : memenv K.
Implicit Types τ σ : type K.
Implicit Types w : mtree K.
Implicit Types a : addr K.
Implicit Types g : mtree K → mtree K.
Hint Extern 0 (Separation _) => apply (_ : Separation (pbit K)).

Lemma cmap_subseteq_index_alive m1 m2 o :
  index_alive ('{m1}) o → m1 ⊆ m2 → index_alive ('{m2}) o.
Proof.
  rewrite <-!index_alive_spec'; unfold index_alive'; intros ? Hm.
  destruct m1 as [m1], m2 as [m2]; specialize (Hm o); simpl in *.
  by destruct (m1 !! _) as [[]|], (m2 !! _) as [[]|].
Qed.
Lemma cmap_valid_subseteq Γ Δ m1 m2 : ✓ Γ → ✓{Γ,Δ} m2 → m1 ⊆ m2 → ✓{Γ,Δ} m1.
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
Lemma cmap_lookup_ref_disjoint Γ Δ m1 m2 o r w1 w2 :
  ✓ Γ → ✓{Γ,Δ} m1 → ✓{Γ,Δ} m2 → m1 ⊥ m2 →
  m1 !!{Γ} (o,r) = Some w1 → m2 !!{Γ} (o,r) = Some w2 → w1 ⊥ w2.
Proof.
  destruct m1 as [m1], m2 as [m2]; intros ??? Hm ??; simplify_equality'.
  specialize (Hm o).
  destruct (m1 !! o) as [[|w1' β]|] eqn:Hw1,
    (m2 !! o) as [[|w2' β']|] eqn:Hw2; simplify_equality'.
  destruct (cmap_valid_Obj Γ Δ (CMap m1) o w1' β) as (τ&?&?&?&_),
    (cmap_valid_Obj Γ Δ (CMap m2) o w2' β') as (?&?&?&?&_);
    simplify_type_equality'; intuition eauto 3 using ctree_lookup_disjoint.
Qed.
Lemma cmap_lookup_disjoint Γ Δ m1 m2 a w1 w2 :
  ✓ Γ → ✓{Γ,Δ} m1 → ✓{Γ,Δ} m2 → m1 ⊥ m2 →
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
Lemma cmap_alter_ref_disjoint Γ Δ1 m1 m2 g o r w1 :
  ✓ Γ → ✓{Γ,Δ1} m1 → m1 ⊥ m2 →
  m1 !!{Γ} (o,r) = Some w1 → ¬ctree_unmapped (g w1) →
  (∀ w2, w1 ⊥ w2 → g w1 ⊥ w2) → cmap_alter_ref Γ g o r m1 ⊥ m2.
Proof.
  assert (∀ w', ctree_empty w' → ctree_unmapped w').
  { eauto using Forall_impl, @sep_unmapped_empty_alt. }
  destruct m1 as [m1], m2 as [m2]; simpl; intros ? Hm1 Hm ??? o'.
  specialize (Hm o'); destruct (decide (o' = o)); simplify_map_equality'; auto.
  destruct (m1 !! o) as [[|w1' β]|] eqn:?; simplify_equality'; auto.
  destruct (cmap_valid_Obj Γ Δ1 (CMap m1) o w1' β)
    as (τ&?&_&?&_); auto; simplify_equality'.
  destruct (m2 !! o) as [[|w2' β']|]; simplify_equality; auto.
  { intuition eauto using ctree_alter_disjoint, ctree_alter_lookup_Forall. }
  assert (∃ w2', w1' ⊥ w2') as (w2'&?).
  { exists (ctree_new Γ ∅ τ); symmetry. eauto using ctree_new_disjoint_l. }
  split.
  { eapply ctree_disjoint_valid_l, ctree_alter_disjoint; intuition eauto. }
  intuition eauto using ctree_alter_lookup_Forall.
Qed.
Lemma cmap_alter_disjoint Γ Δ1 m1 m2 g a w1 τ1 :
  ✓ Γ → ✓{Γ,Δ1} m1 → m1 ⊥ m2 →
  (Γ,Δ1) ⊢ a : TType τ1 → m1 !!{Γ} a = Some w1 → (Γ,Δ1) ⊢ g w1 : τ1 →
  ¬ctree_unmapped (g w1) →
  (∀ w2, w1 ⊥ w2 → g w1 ⊥ w2) → cmap_alter Γ g a m1 ⊥ m2.
Proof.
  assert (∀ w', ctree_empty w' → ctree_unmapped w').
  { eauto using Forall_impl, @sep_unmapped_empty_alt. }
  unfold lookupE, cmap_lookup; intros; case_option_guard; simplify_equality'.
  destruct (m1 !!{_} _) as [w1'|] eqn:Hw1; simplify_equality'.
  destruct (cmap_lookup_ref_Some Γ Δ1 m1 (addr_index a) (addr_ref Γ a) w1')
    as (τ&σ&?&?&?); auto.
  eapply cmap_alter_ref_disjoint; eauto.
  { simplify_option_equality; eauto.
    assert (τ1 = ucharT%T) by eauto using addr_not_is_obj_type; subst.
    intuition eauto 3 using ctree_alter_byte_unmapped. }
  intros; simplify_option_equality; eauto using ctree_alter_byte_disjoint.
Qed.
Lemma cmap_alter_ref_union Γ Δ1 m1 m2 g o r w1 τ1 :
  ✓ Γ → ✓{Γ,Δ1} m1 → m1 ⊥ m2 →
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
  destruct (cmap_valid_Obj Γ Δ1 (CMap m1) o w1' β)
    as (τ&?&_&?&_); auto; simplify_equality'.
  destruct (m2 !! o) as [[|w2' β']|]; simplify_equality'; do 2 f_equal'.
  intuition eauto using ctree_alter_union.
Qed.
Lemma cmap_alter_union Γ Δ1 m1 m2 g a w1 τ1 :
  ✓ Γ → ✓{Γ,Δ1} m1 → m1 ⊥ m2 → (Γ,Δ1) ⊢ a : TType τ1 →
  m1 !!{Γ} a = Some w1 → (Γ,Δ1) ⊢ g w1 : τ1 → ¬ctree_unmapped (g w1) →
  (∀ w2, w1 ⊥ w2 → g w1 ⊥ w2) → (∀ w2, w1 ⊥ w2 → g (w1 ∪ w2) = g w1 ∪ w2) →
  cmap_alter Γ g a (m1 ∪ m2) = cmap_alter Γ g a m1 ∪ m2.
Proof.
  unfold lookupE, cmap_lookup, cmap_alter;
    intros; case_option_guard; simplify_equality'.
  destruct (m1 !!{_} _) as [w1'|] eqn:Hw1; simplify_equality'.
  destruct (cmap_lookup_ref_Some Γ Δ1 m1 (addr_index a) (addr_ref Γ a) w1')
    as (τ&σ&?&?&?); auto.
  eapply cmap_alter_ref_union; eauto.
  * simplify_option_equality; eauto.
    assert (τ1 = ucharT%T) by eauto using addr_not_is_obj_type; subst.
    intuition eauto 3 using ctree_alter_byte_unmapped.
  * intros; simplify_option_equality; eauto using ctree_alter_byte_disjoint.
  * intros; simplify_option_equality; eauto using ctree_alter_byte_union.
Qed.
Lemma cmap_singleton_disjoint Γ Δ a malloc w1 w2 τ :
  ✓ Γ → (Γ,Δ) ⊢ a : TType τ → addr_strict Γ a →
  w1 ⊥ w2 → ¬ctree_unmapped w1 → ¬ctree_unmapped w2 →
  cmap_singleton Γ a malloc w1 ⊥ cmap_singleton Γ a malloc w2.
Proof.
  intros ???? Hperm1 Hperm2 o.
  destruct (decide (o = addr_index a)); simplify_map_equality'; auto.
  split_ands; eauto 10 using ctree_singleton_disjoint, addr_typed_ref_typed,
    addr_typed_type_object_valid, Forall_impl,
    @sep_unmapped_empty_alt, ctree_singleton_Forall_inv.
Qed.
Lemma cmap_singleton_union Γ Δ a malloc w1 w2 τ :
  ✓ Γ → (Γ,Δ) ⊢ a : TType τ → addr_strict Γ a →
  cmap_singleton Γ a malloc (w1 ∪ w2)
  = cmap_singleton Γ a malloc w1 ∪ cmap_singleton Γ a malloc w2.
Proof.
  intros. unfold union at 2; unfold sep_union,
    cmap_singleton, singleton, map_singleton; f_equal'.
  erewrite <-insert_union_with, (left_id_L ∅ _) by done.
  by erewrite ctree_singleton_union
    by eauto using addr_typed_ref_typed, addr_typed_type_object_valid.
Qed.
Lemma cmap_singleton_elt_array Γ Δ a malloc w τ n j :
  ✓ Γ → (Γ,Δ) ⊢ a : TType (τ.[n]) → j < n →
  cmap_singleton Γ (addr_elt Γ (RArray j τ n) a) malloc w
  = cmap_singleton Γ a malloc (ctree_singleton_seg Γ (RArray j τ n) w).
Proof.
  intros; unfold cmap_singleton; simpl.
  by erewrite addr_ref_elt, addr_index_elt by (eauto; by constructor).
Qed.
Lemma cmap_singleton_array_go Γ Δ a malloc ws n τ j :
  ✓ Γ → (Γ,Δ) ⊢ a : TType (τ.[n]) → addr_strict Γ a → (Γ,Δ) ⊢* ws : τ →
  j + length ws ≤ n → ws ≠ [] →
  cmap_singleton Γ a malloc (foldr (∪) (ctree_new Γ ∅ (τ.[n]))
    (imap_go (λ i, ctree_singleton_seg Γ (RArray i τ n)) j ws))
  = ⋃ imap_go (λ i, cmap_singleton Γ (addr_elt Γ (RArray i τ n) a) malloc) j ws.
Proof.
  intros ??? Hws; revert j.
  induction Hws as [|w1 ws ?? IH]; intros j ??; simplify_equality'.
  destruct (decide (ws = [])); simplify_equality'.
  { assert (
      (Γ,Δ) ⊢ MArray τ (<[j:=w1]> (replicate n (ctree_new Γ ∅ τ))) : τ.[n]).
    { typed_constructor.
      * by rewrite insert_length, replicate_length.
      * rewrite list_insert_alter.
        eauto 8 using Forall_alter, Forall_replicate, ctree_new_typed,
          pbit_empty_valid, TArray_valid_inv_type, addr_typed_type_valid.
      * lia. }
    erewrite (ctree_new_union_r _ Δ),
      cmap_singleton_elt_array by eauto with lia.
    unfold cmap_singleton, union, sep_union; simpl.
    by rewrite (right_id_L ∅ _). }
  erewrite cmap_singleton_union, <-IH by eauto with lia.
  by erewrite cmap_singleton_elt_array by eauto with lia.
Qed.
Lemma cmap_singleton_array_disjoint Γ Δ a malloc ws n τ :
  ✓ Γ → (Γ,Δ) ⊢ a : TType (τ.[n]) → addr_strict Γ a → (Γ,Δ) ⊢* ws : τ → 
  Forall (not ∘ Forall sep_unmapped ∘ ctree_flatten) ws → length ws = n →
  ⊥ imap (λ i, cmap_singleton Γ (addr_elt Γ (RArray i τ n) a) malloc) ws.
Proof.
  intros ??? Hws ?. cut (∀ j, j + length ws ≤ n →
   ⊥ imap_go (λ i, cmap_singleton Γ (addr_elt Γ (RArray i τ n) a) malloc) j ws).
  { intros help ?; apply help; lia. }
  induction Hws as [|w1 ws ?? IH]; intros j ?; decompose_Forall_hyps.
  { constructor. }
  assert (Γ ⊢ RArray j τ n : τ.[n] ↣ τ) by (constructor; lia).
  constructor; [|auto with lia].
  destruct (decide (ws = [])); simplify_equality'.
  { eapply sep_disjoint_empty_r, cmap_singleton_sep_valid;
      eauto using addr_elt_typed, addr_elt_is_obj, addr_elt_strict. }
  erewrite <-cmap_singleton_array_go, cmap_singleton_elt_array,
    ctree_singleton_seg_array by eauto with lia.
  eapply cmap_singleton_disjoint; eauto.
  * constructor; apply Forall2_lookup_2.
    { by rewrite inserts_length, insert_length. }
    intros i w2 w3.
    rewrite list_lookup_insert_Some,list_lookup_inserts_Some, !lookup_replicate.
    intros [(?&?&?)|(?&?&?)] [(?&?&?)|(?&?&?)]; decompose_Forall_hyps;
      eauto using ctree_new_disjoint_r, ctree_new_disjoint_l,
        (ctree_new_typed _ Δ), pbit_empty_valid, ctree_typed_type_valid; lia.
  * eauto using ctree_singleton_seg_Forall_inv.
  * clear IH; destruct ws as [|w2 ws]; decompose_Forall_hyps.
    rewrite Forall_bind, Forall_lookup; intros Hmapped.
    cut (ctree_unmapped w2); [done|apply (Hmapped (S j) w2)].
    by rewrite list_lookup_insert
      by (rewrite inserts_length, replicate_length; lia).
Qed.
Lemma cmap_singleton_array_union Γ Δ a malloc ws n τ :
  ✓ Γ → (Γ,Δ) ⊢ a : TType (τ.[n]) → addr_strict Γ a → (Γ,Δ) ⊢* ws : τ →
  length ws = n →
  cmap_singleton Γ a malloc (MArray τ ws)
  = ⋃ imap (λ i, cmap_singleton Γ (addr_elt Γ (RArray i τ n) a) malloc) ws.
Proof.
  intros ? Ha ? Hws ?. assert (ws ≠ []).
  { intros ->.
    apply (TArray_valid_inv_size Γ τ n); eauto using addr_typed_type_valid. }
  unfold imap; erewrite <-cmap_singleton_array_go,
    ctree_singleton_seg_array by eauto with lia.
  do 2 f_equal; apply list_eq_same_length with n;
    rewrite ?inserts_length, ?replicate_length; auto; intros i w1 w2 ??.
  rewrite list_lookup_inserts, Nat.sub_0_r by
    by (rewrite ?replicate_length; auto with lia). congruence.
Qed.
End memory_map.
