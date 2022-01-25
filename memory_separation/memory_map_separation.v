(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
From stdpp Require Import fin_map_dom.
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

Lemma cmap_erase_subseteq m1 m2 : m1 ⊆ m2 → cmap_erase m1 ⊆ cmap_erase m2.
Proof.
  destruct m1 as [m1], m2 as [m2]; intros Hm o; specialize (Hm o).
  rewrite !lookup_omap. by destruct (m1 !! o) as [[]|], (m2 !! o) as [[]|].
Qed.
Lemma cmap_erase_subseteq_l m : sep_valid m → cmap_erase m ⊆ m.
Proof.
  sep_unfold; destruct m as [m]; intros Hm; intros o; specialize (Hm o).
  rewrite lookup_omap. destruct (m !! o) as [[]|];
    naive_solver eauto using @ctree_subseteq_reflexive.
Qed.
Lemma cmap_erased_subseteq m1 m2 : cmap_erased m2 → m1 ⊆ m2 → cmap_erased m1.
Proof.
  unfold cmap_erased; destruct m1 as [m1], m2 as [m2]; intros Hm2 Hm;
    simplify_equality'; f_equal; apply map_eq; intros o;
    apply (f_equal (.!! o)) in Hm2; specialize (Hm o); simplify_map_eq.
  destruct (m1 !! o) as [[]|], (m2 !! o) as [[]|]; naive_solver.
Qed.
Lemma cmap_erase_disjoint_l m1 m2 : m1 ## m2 → cmap_erase m1 ## m2.
Proof.
  destruct m1 as [m1], m2 as [m2]; intros Hm o; specialize (Hm o).
  rewrite !lookup_omap. by destruct (m1 !! o) as [[]|], (m2 !! o) as [[]|].
Qed.
Lemma cmap_erase_disjoint_le m ms : m :: ms ⊆## cmap_erase m :: ms.
Proof.
  apply sep_disjoint_cons_le_inj; intros m'; rewrite !sep_disjoint_list_double.
  intros; symmetry; auto using cmap_erase_disjoint_l.
Qed.
Lemma cmap_erase_disjoint_list_le ms : ms ⊆## cmap_erase <$> ms.
Proof.
  induction ms as [|m ms IH]; csimpl; [done|].
  by rewrite <-cmap_erase_disjoint_le, <-IH.
Qed.
Lemma cmap_erase_union m1 m2 :
  cmap_erase (m1 ∪ m2) = cmap_erase m1 ∪ cmap_erase m2.
Proof.
  sep_unfold; destruct m1 as [m1], m2 as [m2]; f_equal'; apply map_eq; intros o.
  rewrite lookup_omap, !lookup_union_with, !lookup_omap.
  destruct (m1 !! o) as [[]|], (m2 !! o) as [[]|]; naive_solver.
Qed.
Lemma cmap_erase_union_list ms : cmap_erase (⋃ ms) = ⋃ (cmap_erase <$> ms).
Proof.
  induction ms; simpl;
    rewrite ?cmap_erase_union; auto using cmap_erase_empty with f_equal.
Qed.

Lemma cmap_erased_union m1 m2 :
  cmap_erased m1 → cmap_erased m2 → cmap_erased (m1 ∪ m2).
Proof. unfold cmap_erased; rewrite cmap_erase_union; congruence. Qed.
Lemma cmap_erase_difference m1 m2 :
  m2 ⊆ m1 → cmap_erase (m1 ∖ m2) = cmap_erase m1 ∖ cmap_erase m2.
Proof.
  sep_unfold; destruct m1 as [m1], m2 as [m2]; intros Hm; f_equal'.
  apply map_eq; intros o; specialize (Hm o).
  rewrite lookup_omap, !lookup_difference_with, !lookup_omap.
  destruct (m1 !! o) as [[]|], (m2 !! o) as [[]|];
    simplify_option_eq; naive_solver.
Qed.
Lemma cmap_erase_union_inv_l m m1 m2 :
  cmap_erase m = m1 ∪ m2 → sep_valid m → m1 ## m2 →
  ∃ m2', m = m1 ∪ m2' ∧ m1 ## m2' ∧ cmap_erased m1 ∧ m2 = cmap_erase m2'.
Proof.
  intros Hm ??; assert (m1 ⊆ m).
  { transitivity (cmap_erase m); eauto using cmap_erase_subseteq_l.
    rewrite Hm; eauto using @sep_union_subseteq_l'. }
  assert (cmap_erased m1) as Hm1 by eauto using cmap_erased_subseteq,
    @sep_union_subseteq_l', cmap_erase_erased.
  exists (m ∖ m1); split_and ?; eauto using
    @sep_union_difference, @sep_disjoint_difference', eq_sym.
  apply sep_cancel_l' with (cmap_erase m1).
  * by rewrite Hm1.
  * do 2 (apply cmap_erase_disjoint_l; symmetry).
    eauto using @sep_disjoint_difference'.
  * by rewrite <-cmap_erase_union, Hm1, sep_union_difference by done.
Qed.
Lemma cmap_erase_union_inv_r m m1 m2 :
  cmap_erase m = m1 ∪ m2 → sep_valid m → m1 ## m2 →
  ∃ m1', m = m1' ∪ m2 ∧ m1' ## m2 ∧ m1 = cmap_erase m1' ∧ cmap_erased m2.
Proof.
  intros. destruct (cmap_erase_union_inv_l m m2 m1) as (m1'&->&?&?&->); auto.
  { by rewrite sep_commutative by solve_sep_disjoint. }
  exists m1'. by rewrite sep_commutative by solve_sep_disjoint.
Qed.
Lemma cmap_erase_union_inv m m1 m2 :
  cmap_erase m = m1 ∪ m2 → sep_valid m → m1 ## m2 →
  ∃ m1' m2',
    m = m1' ∪ m2' ∧ m1' ## m2' ∧ m1 = cmap_erase m1' ∧ m2 = cmap_erase m2'.
Proof.
  intros. destruct (cmap_erase_union_inv_l m m1 m2) as (m2'&->&?&?&->); auto.
  by exists m1, m2'.
Qed.

Lemma cmap_subseteq_index_alive' m1 m2 o :
  index_alive' m1 o → m1 ⊆ m2 → index_alive' m2 o.
Proof.
  unfold index_alive'; intros ? Hm.
  destruct m1 as [m1], m2 as [m2]; specialize (Hm o); simpl in *.
  by destruct (m1 !! _) as [[]|], (m2 !! _) as [[]|].
Qed.
Lemma cmap_subseteq_index_alive m1 m2 o :
  index_alive '{m1} o → m1 ⊆ m2 → index_alive '{m2} o.
Proof. rewrite <-!index_alive_spec'; apply cmap_subseteq_index_alive'. Qed.
Lemma cmap_valid_subseteq Γ Δ m1 m2 : ✓ Γ → ✓{Γ,Δ} m2 → m1 ⊆ m2 → ✓{Γ,Δ} m1.
Proof.
  destruct m1 as [m1], m2 as [m2]; intros ? (?&Hm2&Hm2') Hm; split_and !.
  * done.
  * intros o τ ?; specialize (Hm o); unfold option_relation in *; simplify_option_eq.
    destruct (m2 !! o) as [[]|] eqn:?; destruct Hm; subst; eauto.
  * intros o w μ ?; specialize (Hm o); unfold option_relation in *; simplify_option_eq.
    destruct (m2 !! o) as [[|w' μ']|] eqn:?; try done.
    destruct Hm as [[??]?], (Hm2' o w' μ') as (τ'&?&?&?&?);
      eauto 10 using ctree_typed_subseteq.
Qed.
Lemma cmap_union_valid_2 Γ Δ m1 m2 :
  m1 ## m2 → ✓{Γ,Δ} m1 → ✓{Γ,Δ} m2 → ✓{Γ,Δ} (m1 ∪ m2).
Proof.
  destruct m1 as [m1], m2 as [m2].
  intros Hm (HΔ&Hm1&Hm1') (_&Hm2&Hm2'); split_and !; simpl in *; auto.
  * intros o τ; specialize (Hm o); rewrite lookup_union_with; intros.
    destruct (m1 !! o) as [[]|] eqn:?, (m2 !! o) as [[]|] eqn:?;
      simplify_equality'; eauto.
  * intros o w μ; specialize (Hm o); rewrite lookup_union_with; intros.
    destruct (m1 !! o) as [[|w1 ?]|] eqn:?,
      (m2 !! o) as [[|w2 μ']|] eqn:?; simplify_equality'; eauto.
    destruct (Hm1' o w1 μ) as (τ&?&?&?&?),
      (Hm2' o w2 μ') as (τ'&?&?&?&?); simplify_type_equality'; auto.
    exists τ; intuition eauto using ctree_union_typed, @ctree_positive_l.
Qed.
Lemma cmap_union_valid Γ Δ m1 m2 :
  ✓ Γ → m1 ## m2 → ✓{Γ,Δ} (m1 ∪ m2) ↔ ✓{Γ,Δ} m1 ∧ ✓{Γ,Δ} m2.
Proof.
  split; intuition eauto using cmap_union_valid_2,
    cmap_valid_subseteq, @sep_union_subseteq_r', @sep_union_subseteq_l'.
Qed.
Lemma cmap_dom_union m1 m2 : dom indexset (m1 ∪ m2) = dom _ m1 ∪ dom _ m2.
Proof.
  destruct m1 as [m1], m2 as [m2]; simpl; apply set_eq; intros o.
  rewrite elem_of_union, !elem_of_dom, lookup_union_with, <-!not_eq_None_Some.
  destruct (m1 !! o) as [[]|], (m2 !! o) as [[]|]; naive_solver.
Qed.
Lemma cmap_union_list_valid Γ Δ (ms : list (mem K)) :
  ✓ Γ → ✓{Γ} Δ → ## ms → Forall ✓{Γ,Δ} ms ↔ ✓{Γ,Δ} (⋃ ms).
Proof.
  induction 3; csimpl; rewrite ?Forall_cons, ?cmap_union_valid by auto;
    intuition eauto using cmap_empty_valid.
Qed.
Lemma cmap_union_list_lookup_valid Γ Δ {n} (ms : vec (mem K) n) i :
  ✓ Γ → ✓{Γ} Δ → ## ms → ✓{Γ,Δ} (⋃ ms) → ✓{Γ,Δ} (ms !!! i).
Proof.
  intros ???. rewrite <-cmap_union_list_valid, Forall_vlookup by done; auto.
Qed.
Lemma cmap_union_list_delete_lookup_valid Γ Δ {n} (ms : vec (mem K) n) i j :
  ✓ Γ → ✓{Γ} Δ → ## ms → ✓{Γ,Δ} (⋃ delete (fin_to_nat i) (vec_to_list ms)) →
  i ≠ j → ✓{Γ,Δ} (ms !!! j).
Proof.
  intros ?? Hms. rewrite <-cmap_union_list_valid
    by eauto using @sep_disjoint_contains, @submseteq_delete.
  assert (∀ n (ms : vec _ n) i, ✓{Γ,Δ}* ms → ✓{Γ,Δ} (ms !!! i)).
  { intros ???. by rewrite Forall_vlookup. }
  revert i j Hms; induction ms; inversion_clear 1; intros;
    inv_all_vec_fin; decompose_Forall_hyps; eauto with congruence.
Qed.

Lemma cmap_lookup_ref_disjoint Γ Δ m1 m2 o r w1 w2 :
  ✓ Γ → ✓{Γ,Δ} m1 → ✓{Γ,Δ} m2 → m1 ## m2 →
  m1 !!{Γ} (o,r) = Some w1 → m2 !!{Γ} (o,r) = Some w2 → w1 ## w2.
Proof.
  destruct m1 as [m1], m2 as [m2]; intros ??? Hm ??; simplify_equality'.
  specialize (Hm o).
  destruct (m1 !! o) as [[|w1' μ]|] eqn:Hw1,
    (m2 !! o) as [[|w2' μ']|] eqn:Hw2; simplify_equality'.
  destruct (cmap_valid_Obj Γ Δ (CMap m1) o w1' μ) as (τ&?&?&?&_),
    (cmap_valid_Obj Γ Δ (CMap m2) o w2' μ') as (?&?&?&?&_);
    simplify_type_equality'; intuition eauto 3 using ctree_lookup_disjoint.
Qed.
Lemma cmap_lookup_disjoint Γ Δ m1 m2 a w1 w2 :
  ✓ Γ → ✓{Γ,Δ} m1 → ✓{Γ,Δ} m2 → m1 ## m2 →
  m1 !!{Γ} a = Some w1 → m2 !!{Γ} a = Some w2 → w1 ## w2.
Proof.
  unfold lookupE, cmap_lookup; intros; case_option_guard; simplify_equality'.
  destruct (m1 !!{_} _) as [w1'|] eqn:Hw1,
    (m2 !!{_} _) as [w2'|] eqn:Hw2; simplify_option_eq;
    eauto 3 using ctree_lookup_byte_disjoint, cmap_lookup_ref_disjoint.
Qed.
Lemma cmap_lookup_ref_subseteq Γ m1 m2 o r w1 :
  ✓ Γ → m1 ⊆ m2 → m1 !!{Γ} (o,r) = Some w1 → ¬ctree_Forall sep_unmapped w1 →
  ∃ w2, m2 !!{Γ} (o,r) = Some w2 ∧ w1 ⊆ w2.
Proof.
  destruct m1 as [m1], m2 as [m2]; simpl; intros ? Hm ??; specialize (Hm o).
  destruct (m1 !! o) as [[|w1' μ]|] eqn:?,
    (m2 !! o) as [[|w2' μ']|] eqn:?; simplify_equality'; try done.
  destruct (ctree_lookup_subseteq Γ w1' w2' r w1)
    as (w2''&?&?); simplify_option_eq; intuition eauto.
Qed.
Lemma cmap_lookup_subseteq Γ m1 m2 a w1 :
  ✓ Γ → m1 ⊆ m2 → m1 !!{Γ} a = Some w1 → ¬ctree_Forall sep_unmapped w1 →
  ∃ w2, m2 !!{Γ} a = Some w2 ∧ w1 ⊆ w2.
Proof.
  unfold lookupE, cmap_lookup; intros; case_option_guard; simplify_equality'.
  destruct (m1 !!{_} _) as [w1'|] eqn:Hw1; simplify_equality'.
  assert (¬ctree_unmapped w1').
  { simplify_option_eq; eauto using
      ctree_lookup_byte_Forall, pbit_unmapped_indetify. }
  destruct (cmap_lookup_ref_subseteq Γ m1 m2 (addr_index a)
    (addr_ref Γ a) w1') as (w2'&->&?); simpl; auto.
  simplify_option_eq by eauto using @ctree_unshared_weaken;
    eauto using ctree_lookup_byte_subseteq.
Qed.
Lemma cmap_alter_ref_disjoint Γ Δ1 m1 m2 g o r w1 :
  ✓ Γ → ✓{Γ,Δ1} m1 → m1 ## m2 →
  m1 !!{Γ} (o,r) = Some w1 → ¬ctree_unmapped (g w1) →
  (∀ w2, w1 ## w2 → g w1 ## w2) → cmap_alter_ref Γ g o r m1 ## m2.
Proof.
  assert (∀ w', ctree_empty w' → ctree_unmapped w').
  { eauto using Forall_impl, @sep_unmapped_empty_alt. }
  destruct m1 as [m1], m2 as [m2]; simpl; intros ? Hm1 Hm ??? o'.
  specialize (Hm o'); destruct (decide (o' = o)); simplify_map_eq; auto.
  destruct (m1 !! o) as [[|w1' μ]|] eqn:?; simplify_equality'; auto.
  destruct (cmap_valid_Obj Γ Δ1 (CMap m1) o w1' μ)
    as (τ&?&_&?&_); auto; simplify_equality'.
  destruct (m2 !! o) as [[|w2' μ']|]; simplify_equality; auto.
  { intuition eauto using ctree_alter_disjoint, ctree_alter_lookup_Forall. }
  assert (∃ w2', w1' ## w2') as (w2'&?).
  { exists (ctree_new Γ ∅ τ); symmetry. eauto using ctree_new_disjoint_l. }
  split.
  { eapply ctree_disjoint_valid_l, ctree_alter_disjoint; intuition eauto. }
  intuition eauto using ctree_alter_lookup_Forall.
Qed.
Lemma cmap_alter_disjoint Γ Δ1 m1 m2 g a w1 τ1 :
  ✓ Γ → ✓{Γ,Δ1} m1 → m1 ## m2 →
  (Γ,Δ1) ⊢ a : TType τ1 → m1 !!{Γ} a = Some w1 → (Γ,Δ1) ⊢ g w1 : τ1 →
  ¬ctree_unmapped (g w1) →
  (∀ w2, w1 ## w2 → g w1 ## w2) → cmap_alter Γ g a m1 ## m2.
Proof.
  assert (∀ w', ctree_empty w' → ctree_unmapped w').
  { eauto using Forall_impl, @sep_unmapped_empty_alt. }
  unfold lookupE, cmap_lookup; intros; case_option_guard; simplify_equality'.
  destruct (m1 !!{_} _) as [w1'|] eqn:Hw1; simplify_equality'.
  destruct (cmap_lookup_ref_Some Γ Δ1 m1 (addr_index a) (addr_ref Γ a) w1')
    as (τ&σ&?&?&?); auto.
  eapply cmap_alter_ref_disjoint; eauto.
  { simplify_option_eq; eauto.
    assert (τ1 = ucharT%T) by eauto using addr_not_is_obj_type; subst.
    intuition eauto 3 using ctree_alter_byte_unmapped. }
  intros; simplify_option_eq; eauto using ctree_alter_byte_disjoint.
Qed.
Lemma cmap_alter_ref_union Γ Δ1 m1 m2 g o r w1 τ1 :
  ✓ Γ → ✓{Γ,Δ1} m1 → m1 ## m2 →
  m1 !!{Γ} (o,r) = Some w1 → ¬ctree_unmapped (g w1) →
  (∀ w2, w1 ## w2 → g w1 ## w2) → (∀ w2, w1 ## w2 → g (w1 ∪ w2) = g w1 ∪ w2) →
  cmap_alter_ref Γ g o r (m1 ∪ m2) = cmap_alter_ref Γ g o r m1 ∪ m2.
Proof.
  destruct m1 as [m1], m2 as [m2]; simpl; intros ? Hm1 Hm ????.
  unfold union at 2, sep_union; f_equal'; apply map_eq; intros o'.
  specialize (Hm o'); destruct (decide (o' = o)); simplify_map_eq;
    rewrite !lookup_union_with, ?lookup_alter,
    ?lookup_alter_ne, ?lookup_union_with by done; auto.
  destruct (m1 !! o) as [[|w1' μ]|] eqn:?; simplify_equality'; auto.
  destruct (cmap_valid_Obj Γ Δ1 (CMap m1) o w1' μ)
    as (τ&?&_&?&_); auto; simplify_equality'.
  destruct (m2 !! o) as [[|w2' μ']|]; simplify_equality'; do 2 f_equal'.
  intuition eauto using ctree_alter_union.
Qed.
Lemma cmap_alter_union Γ Δ1 m1 m2 g a w1 τ1 :
  ✓ Γ → ✓{Γ,Δ1} m1 → m1 ## m2 → (Γ,Δ1) ⊢ a : TType τ1 →
  m1 !!{Γ} a = Some w1 → (Γ,Δ1) ⊢ g w1 : τ1 → ¬ctree_unmapped (g w1) →
  (∀ w2, w1 ## w2 → g w1 ## w2) → (∀ w2, w1 ## w2 → g (w1 ∪ w2) = g w1 ∪ w2) →
  cmap_alter Γ g a (m1 ∪ m2) = cmap_alter Γ g a m1 ∪ m2.
Proof.
  unfold lookupE, cmap_lookup, cmap_alter;
    intros; case_option_guard; simplify_equality'.
  destruct (m1 !!{_} _) as [w1'|] eqn:Hw1; simplify_equality'.
  destruct (cmap_lookup_ref_Some Γ Δ1 m1 (addr_index a) (addr_ref Γ a) w1')
    as (τ&σ&?&?&?); auto.
  eapply cmap_alter_ref_union; eauto.
  * simplify_option_eq; eauto.
    assert (τ1 = ucharT%T) by eauto using addr_not_is_obj_type; subst.
    intuition eauto 3 using ctree_alter_byte_unmapped.
  * intros; simplify_option_eq; eauto using ctree_alter_byte_disjoint.
  * intros; simplify_option_eq; eauto using ctree_alter_byte_union.
Qed.
Lemma cmap_singleton_disjoint_l Γ Δ m a μ w τ :
  ✓ Γ → ✓{Γ} Δ → (Γ,Δ) ⊢ a : TType τ → addr_is_obj a → addr_strict Γ a →
  (Γ,Δ) ⊢ w : τ → ¬ctree_unmapped w →
  addr_index a ∉ dom indexset m → sep_valid m → cmap_singleton Γ a μ w ## m.
Proof.
  rewrite cmap_dom_alt; destruct m as [m]; intros ????????? o.
  destruct (decide (o = addr_index a)); simplify_map_eq;
    [|by destruct (m !! o) eqn:?; eauto].
  assert (τ = addr_type_base a) by eauto using addr_is_obj_type; subst.
  split_and ?; eauto 10 using addr_typed_ref_typed, Forall_impl,
    @sep_unmapped_empty_alt, ctree_singleton_Forall_inv,
    ctree_typed_sep_valid, ctree_singleton_typed.
Qed.
Lemma cmap_singleton_disjoint Γ Δ a μ w1 w2 τ :
  ✓ Γ → (Γ,Δ) ⊢ a : TType τ → addr_is_obj a → addr_strict Γ a → w1 ## w2 →
  (Γ,Δ) ⊢ w1 : τ → ¬ctree_empty w1 → (Γ,Δ) ⊢ w2 : τ → ¬ctree_empty w2 →
  cmap_singleton Γ a μ w1 ## cmap_singleton Γ a μ w2.
Proof.
  intros; intros o.
  assert (τ = addr_type_base a) by eauto using addr_is_obj_type; subst.
  destruct (decide (o = addr_index a)); simplify_map_eq;
    eauto 15 using ctree_singleton_disjoint,
    addr_typed_ref_typed, ctree_singleton_Forall_inv.
Qed.
Lemma cmap_singleton_disjoint_rev Γ Δ a μ w1 w2 τ :
  ✓ Γ → (Γ,Δ) ⊢ a : TType τ → addr_is_obj a → addr_strict Γ a → 
  (Γ,Δ) ⊢ w1 : τ → (Γ,Δ) ⊢ w2 : τ →
  cmap_singleton Γ a μ w1 ## cmap_singleton Γ a μ w2 → w1 ## w2.
Proof.
  intros ?????? Hm; specialize (Hm (addr_index a)); simplify_map_eq.
  assert (τ = addr_type_base a) by eauto using addr_is_obj_type; subst.
  intuition eauto using ctree_singleton_disjoint_rev, addr_typed_ref_typed.
Qed.
Lemma cmap_singleton_union Γ Δ a μ w1 w2 τ :
  ✓ Γ → (Γ,Δ) ⊢ a : TType τ → addr_is_obj a → addr_strict Γ a → w1 ## w2 →
  (Γ,Δ) ⊢ w1 : τ → (Γ,Δ) ⊢ w2 : τ →
  cmap_singleton Γ a μ (w1 ∪ w2)
  = cmap_singleton Γ a μ w1 ∪ cmap_singleton Γ a μ w2.
Proof.
  intros. unfold union at 2; unfold sep_union,
    cmap_singleton, singletonM, map_singleton; f_equal'.
  assert (τ = addr_type_base a) by eauto using addr_is_obj_type; subst.
  by erewrite <-insert_union_with, (left_id_L ∅ _), ctree_singleton_union
    by eauto using addr_typed_ref_typed, addr_typed_type_object_valid.
Qed.
Lemma cmap_singleton_elt_array Γ Δ a μ w τ n j :
  ✓ Γ → (Γ,Δ) ⊢ a : TType (τ.[n]) → j < n →
  cmap_singleton Γ (addr_elt Γ (RArray j τ n) a) μ w
  = cmap_singleton Γ a μ (ctree_singleton_seg Γ (RArray j τ n) w).
Proof.
  intros; unfold cmap_singleton; simpl.
  by erewrite addr_ref_elt, addr_index_elt by (eauto; by constructor).
Qed.
Lemma cmap_singleton_array_go Γ Δ a μ ws n τ j :
  ✓ Γ → (Γ,Δ) ⊢ a : TType (τ.[n]) → addr_strict Γ a → (Γ,Δ) ⊢* ws : τ →
  Forall (not ∘ Forall (∅ =.) ∘ ctree_flatten) ws →
  j + length ws ≤ n → ws ≠ [] →
  cmap_singleton Γ a μ (foldr (∪) (ctree_new Γ ∅ (τ.[n]))
    (imap_go (λ i, ctree_singleton_seg Γ (RArray i τ n)) j ws))
  = ⋃ imap_go (λ i, cmap_singleton Γ (addr_elt Γ (RArray i τ n) a) μ) j ws ∧
  ## imap_go (λ i, cmap_singleton Γ (addr_elt Γ (RArray i τ n) a) μ) j ws.
Proof.
  intros ??? Hws; revert j.
  induction Hws as [|w1 ws ?? IH]; intros j ???; decompose_Forall_hyps.
  assert (Γ ⊢ RArray j τ n : τ.[n] ↣ τ) by (constructor; lia).
  assert (
    (Γ,Δ) ⊢ MArray τ (<[j:=w1]> (replicate n (ctree_new Γ ∅ τ))) : τ.[n]).
  { typed_constructor; rewrite ?insert_length, ?replicate_length; auto with lia.
    eauto using Forall_insert, Forall_replicate,
      ctree_new_typed, ctree_typed_type_valid, pbit_empty_valid. }
  destruct (decide (ws = [])); simplify_equality'.
  { assert (sep_valid
      (cmap_singleton Γ a μ (ctree_singleton_seg Γ (RArray j τ n) w1))).
    { eauto 8 using cmap_singleton_sep_valid,
        addr_ref_byte_is_obj_parent, ctree_singleton_seg_Forall_inv. }
    by erewrite (ctree_new_union_r _ Δ), cmap_singleton_elt_array ,
      sep_right_id, sep_disjoint_list_singleton by eauto with lia. }
  assert (<[j:=w1]> (replicate n (ctree_new Γ ∅ τ))
    ##* list_inserts (S j) ws (replicate n (ctree_new Γ ∅ τ))).
  { apply Forall2_same_length_lookup_2; [|intros i w2 w3].
    { by rewrite inserts_length, insert_length. }
    rewrite list_lookup_insert_Some,
      list_lookup_inserts_Some, !lookup_replicate.
    intros [(?&?&?)|(?&?&?)] [(?&?&?)|(?&?&?)]; decompose_Forall_hyps;
      eauto using ctree_new_disjoint_r, ctree_new_disjoint_l,
        (ctree_new_typed _ Δ), pbit_empty_valid, ctree_typed_type_valid; lia. }
  assert ((Γ,Δ) ⊢ MArray τ
    (list_inserts (S j) ws (replicate n (ctree_new Γ ∅ τ))) : τ.[n]).
  { typed_constructor; auto with lia.
    { by rewrite inserts_length, replicate_length. }
    eauto using Forall_inserts, Forall_replicate,
      ctree_new_typed, ctree_typed_type_valid, pbit_empty_valid. }
  destruct (IH (S j)) as [IH1 IH2]; auto with lia; clear IH.
  erewrite cmap_singleton_elt_array,ctree_singleton_seg_array by eauto with lia.
  split.
  * erewrite <-IH1, ctree_singleton_seg_array by eauto with lia.
    by erewrite cmap_singleton_union by
      eauto using addr_ref_byte_is_obj_parent, @MArray_disjoint with lia.
  * constructor; auto.
    erewrite <-IH1, ctree_singleton_seg_array by eauto with lia.
    eapply cmap_singleton_disjoint; simpl; eauto using @MArray_disjoint,
      addr_ref_byte_is_obj_parent, ctree_singleton_seg_Forall_inv.
    clear IH1 IH2; destruct ws as [|w2 ws]; decompose_Forall_hyps.
    rewrite Forall_bind, Forall_lookup; intros Hemp.
    cut (ctree_empty w2); [done|].
    apply (Hemp (S j) w2); by rewrite list_lookup_insert
      by (rewrite inserts_length, replicate_length; lia).
Qed.
Lemma cmap_singleton_array_disjoint Γ Δ a μ ws n τ :
  ✓ Γ → (Γ,Δ) ⊢ a : TType (τ.[n]) → addr_strict Γ a → (Γ,Δ) ⊢* ws : τ → 
  Forall (not ∘ Forall (eq ∅) ∘ ctree_flatten) ws → length ws = n →
  ## imap_go (λ i, cmap_singleton Γ (addr_elt Γ (RArray i τ n) a) μ) 0 ws.
Proof.
  intros. destruct (decide (ws = [])) as [->|]; [constructor|].
  eapply cmap_singleton_array_go; eauto with lia.
Qed.
Lemma cmap_singleton_array_union Γ Δ a μ ws n τ :
  ✓ Γ → (Γ,Δ) ⊢ a : TType (τ.[n]) → addr_strict Γ a → (Γ,Δ) ⊢* ws : τ →
  Forall (not ∘ Forall (eq ∅) ∘ ctree_flatten) ws → length ws = n →
  cmap_singleton Γ a μ (MArray τ ws)
  = ⋃ imap_go (λ i, cmap_singleton Γ (addr_elt Γ (RArray i τ n) a) μ) 0 ws.
Proof.
  intros. destruct (decide (ws = [])) as [->|].
  { destruct (TArray_valid_inv_size Γ τ n); eauto using addr_typed_type_valid. }
  unfold imap.
  destruct (cmap_singleton_array_go Γ Δ a μ ws n τ 0) as [<- _]; eauto with lia.
  erewrite ctree_singleton_seg_array by eauto with lia.
  do 2 f_equal; apply list_eq_same_length with n;
    rewrite ?inserts_length, ?replicate_length; auto; intros i w1 w2 ??.
  rewrite list_lookup_inserts, Nat.sub_0_r by
    (by rewrite ?replicate_length; auto with lia); congruence.
Qed.
End memory_map.
