(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export memory_trees cmap.
Local Open Scope ctype_scope.

Notation mem Ti := (cmap Ti (pbit Ti)).

Section operations.
  Context `{Env Ti}.

  Global Instance cmap_dom: Dom (mem Ti) indexset := λ m,
    let (m) := m in dom _ m.
  Global Instance cmap_valid: Valid (env Ti * memenv Ti) (mem Ti) := λ ΓΓm m,
    let (Γ,Γm) := ΓΓm in 
    (**i 1). *) (∀ o τ,
      cmap_car m !! o = Some (Freed τ) →
      Γm ⊢ o : τ ∧ ¬index_alive Γm o ∧ ✓{Γ} τ ∧ int_typed (size_of Γ τ) sptrT) ∧
    (**i 2). *) (∀ o w malloc,
      cmap_car m !! o = Some (Obj w malloc) →
      ∃ τ, Γm ⊢ o : τ ∧ index_alive Γm o ∧ (Γ,Γm) ⊢ w : τ ∧
        ¬ctree_empty w ∧ int_typed (size_of Γ τ) sptrT).
  Definition memenv_of (m : mem Ti) : memenv Ti :=
    let (m) := m in
    let f x : type Ti * bool :=
      match x with Freed τ => (τ,true) | Obj w _ => (type_of w,false) end in
    f <$> m.
  Global Instance cmap_valid': Valid (env Ti) (mem Ti) := λ Γ m,
    ✓{Γ,memenv_of m} m.

  Global Instance cmap_lookup:
      LookupE (env Ti) (addr Ti) (mtree Ti) (mem Ti) := λ Γ a m,
    guard (addr_strict Γ a);
    '(w',_) ← cmap_car m !! addr_index a ≫= maybe_Obj;
    w ← lookupE Γ (addr_ref Γ a) w';
    if decide (addr_is_obj a) then Some w else
      guard (ctree_unshared w ∧ type_of a ≠ voidT); w !!{Γ} (addr_ref_byte Γ a).
  Definition cmap_alter (Γ : env Ti) (g : mtree Ti → mtree Ti)
      (a : addr Ti) (m : mem Ti) : mem Ti :=
    let (m) := m in
    let G := if decide (addr_is_obj a) then g
             else ctree_alter_byte Γ g (addr_ref_byte Γ a) in
    CMap $
      alter (cmap_elem_map (ctree_alter Γ G (addr_ref Γ a))) (addr_index a) m.
  Global Instance cmap_refine: Refine Ti (mem Ti) := λ Γ f Γm1 Γm2 m1 m2,
    (**i 1.) *) ✓{Γ,Γm1} m1 ∧
    (**i 2.) *) ✓{Γ,Γm2} m2 ∧
    (**i 3.) *) Γm1 ⊑{Γ,f} Γm2 ∧
    (**i 4.) *) (∀ o1 o2 r w1 malloc,
      f !! o1 = Some (o2,r) → cmap_car m1 !! o1 = Some (Obj w1 malloc) →
      ∃ w2 w2' τ,
        cmap_car m2 !! o2 = Some (Obj w2 malloc) ∧
        w2 !!{Γ} (freeze true <$> r) = Some w2' ∧
        w1 ⊑{Γ,f@Γm1↦Γm2} w2' : τ ∧ (malloc → r = [])).
  Global Instance cmap_refine': RefineM Ti (mem Ti) := λ Γ f m1 m2,
    m1 ⊑{Γ,f@memenv_of m1↦memenv_of m2} m2.
End operations.

Notation "'{ m }" := (memenv_of m) (at level 20, format "''{' m }").

Section cmap_typed.
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
Implicit Types f : mem_inj Ti.
Implicit Types g : mtree Ti → mtree Ti.
Implicit Types β : bool.
Local Opaque nmap.Nempty.

Arguments lookupE _ _ _ _ _ _ _ !_ /.
Arguments cmap_lookup _ _ _ _ !_ /.
Hint Extern 0 (Separation _) => apply (_ : Separation (pbit Ti)).

Lemma cmap_empty_valid Γ Γm : ✓{Γ,Γm} (∅ : mem Ti).
Proof. by split; intros until 0; simplify_map_equality'. Qed.
Lemma cmap_empty_valid' Γ Γm : ✓{Γ} (∅ : mem Ti).
Proof. by apply cmap_empty_valid. Qed.
Lemma cmap_valid_weaken Γ1 Γ2 Γm m : ✓ Γ1 → ✓{Γ1,Γm} m → Γ1 ⊆ Γ2 → ✓{Γ2,Γm} m.
Proof.
  intros ? [Hm1 Hm2] ?; split.
  * intros o τ ?. destruct (Hm1 o τ) as (?&?&?&?); auto.
    erewrite <-size_of_weaken by eauto using ctree_typed_type_valid.
    eauto using type_valid_weaken.
  * intros o w malloc ?. destruct (Hm2 o w malloc) as (τ&?&?&?&?); auto.
    exists τ. erewrite <-size_of_weaken by eauto using ctree_typed_type_valid.
    eauto using ctree_typed_weaken. 
Qed.
Lemma cmap_valid'_weaken Γ1 Γ2 m : ✓ Γ1 → ✓{Γ1} m → Γ1 ⊆ Γ2 → ✓{Γ2} m.
Proof. by apply cmap_valid_weaken. Qed.
Lemma cmap_valid_sep_valid Γ Γm m : ✓{Γ,Γm} m → sep_valid m.
Proof.
  destruct m as [m]; intros Hm o [τ|w malloc] ?; [done|].
  destruct (proj2 Hm o w malloc) as (?&?&?&?&?&?); simpl;
    eauto using ctree_typed_sep_valid.
Qed.
Lemma index_typed_valid_representable Γ Γm m o τ :
  ✓ Γ → ✓{Γ,Γm} m → '{m} ⊢ o : τ → ✓{Γ} τ ∧ int_typed (size_of Γ τ) sptrT.
Proof.
  intros ? [Hm1 Hm2] [β Hβ]. destruct m as [m]; simplify_map_equality'.
  destruct (m !! o) as [[τ'|w malloc]|] eqn:?; simplify_equality'.
  * destruct (Hm1 o τ) as (?&?&?&?); eauto.
  * destruct (Hm2 o w malloc) as (?&?&?&?&?&?);
      simplify_type_equality; eauto using ctree_typed_type_valid.
Qed.
Lemma index_typed_valid Γ Γm m o τ : ✓ Γ → ✓{Γ,Γm} m → '{m} ⊢ o : τ → ✓{Γ} τ.
Proof. intros; eapply index_typed_valid_representable; eauto. Qed.
Lemma index_typed_representable Γ Γm m o τ :
  ✓ Γ → ✓{Γ,Γm} m → '{m} ⊢ o : τ → int_typed (size_of Γ τ) sptrT.
Proof. intros; eapply index_typed_valid_representable; eauto. Qed.
Lemma cmap_lookup_unfreeze Γ m a w :
  m !!{Γ} a = Some w → m !!{Γ} (freeze false a) = Some w.
Proof.
  destruct m as [m]; simpl; intros.
  rewrite addr_index_freeze, addr_ref_freeze, addr_ref_byte_freeze.
  case_option_guard; simplify_equality'.
  rewrite option_guard_True by auto using addr_strict_freeze_2.
  destruct (m !! addr_index a) as [[|w' β]|]; simplify_equality'.
  destruct (w' !!{Γ} addr_ref Γ a) as [w''|] eqn:?; simplify_equality'.
  erewrite ctree_lookup_unfreeze by eauto; csimpl.
  by rewrite (decide_iff _ _ _ _ (addr_is_obj_freeze _ _)), addr_type_of_freeze.
Qed.
Lemma cmap_lookup_typed Γ Γm m a w σ :
  ✓ Γ → ✓{Γ,Γm} m → (Γ,Γm) ⊢ a : σ → m !!{Γ} a = Some w → (Γ,Γm) ⊢ w : σ.
Proof.
  destruct m as [m]; simpl; intros ? Hm Ha ?.
  case_option_guard; simplify_equality'.
  destruct (m !! addr_index a) as [[|w' β]|] eqn:Hw; simplify_equality'.
  destruct (w' !!{Γ} addr_ref Γ a) as [w''|] eqn:?; simplify_equality'.
  destruct (proj2 Hm (addr_index a) w' β)
    as (τ&?&?&?&_); auto; simplify_equality'.
  destruct (ctree_lookup_Some Γ Γm w' τ (addr_ref Γ a) w'')
    as (σ'&?&?); auto; simplify_option_equality; simplify_type_equality.
  * cut (σ = σ'); [by intros ->|].
    erewrite <-(addr_is_obj_type_base _ _ _ σ) by eauto.
    assert (Γm ⊢ addr_index a : addr_type_object a)
      by eauto using addr_typed_index; simplify_type_equality.
    eauto using ref_set_offset_typed_unique, addr_typed_ref_base_typed.
  * erewrite addr_not_obj_type by intuition eauto.
    eauto using ctree_lookup_byte_typed.
Qed.
Lemma cmap_lookup_strict Γ m a w : m !!{Γ} a = Some w → addr_strict Γ a.
Proof. by destruct m as [m]; intros; simplify_option_equality. Qed.
Lemma cmap_lookup_Some Γ Γm m w a :
  ✓ Γ → ✓{Γ,Γm} m → m !!{Γ} a = Some w → (Γ,Γm) ⊢ w : type_of w.
Proof.
  destruct m as [m]; simpl; intros ? Hm Ha.
  case_option_guard; simplify_equality'.
  destruct (m !! addr_index a) as [[|w' β]|] eqn:Hw; simplify_equality'.
  destruct (w' !!{Γ} addr_ref Γ a) as [w''|] eqn:?; simplify_equality'.
  destruct (proj2 Hm (addr_index a) w' β)
    as (τ&?&?&?&_); auto; simplify_equality'.
  destruct (ctree_lookup_Some Γ Γm w' τ (addr_ref Γ a) w'')
    as (σ'&?&?); auto; simplify_option_equality;
    eauto using ctree_lookup_byte_typed, type_of_typed.
Qed.
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
Lemma cmap_lookup_subseteq Γ m1 m2 a w1 w2 :
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
Lemma cmap_alter_memenv_of Γ Γm m g a w :
  ✓ Γ → ✓{Γ,Γm} m → m !!{Γ} a = Some w → type_of (g w) = type_of w →
  '{cmap_alter Γ g a m} = '{m}.
Proof.
  destruct m as [m]; simpl; intros ? Hm ??.
  apply map_eq; intros o; case_option_guard; simplify_map_equality'.
  destruct (decide (o = addr_index a)); simplify_map_equality'; auto.
  destruct (m !! addr_index a) as [[|w' β]|] eqn:?; simplify_equality'; f_equal.
  destruct (w' !!{Γ} addr_ref Γ a) as [w''|] eqn:?; simplify_equality'.
  destruct (proj2 Hm (addr_index a) w' β)
    as (τ&?&?&?&_); auto; simplify_equality'.
  destruct (ctree_lookup_Some Γ Γm w' τ (addr_ref Γ a) w'')
    as (σ'&?&?); auto; simplify_type_equality'; f_equal.
  eapply ctree_alter_type_of_weak; eauto using type_of_typed.
  simplify_option_equality; [done|apply ctree_alter_byte_type_of;
    simplify_type_equality; eauto using ctree_typed_type_valid].
Qed.
Lemma cmap_alter_valid Γ Γm m g a w :
  ✓ Γ → ✓{Γ,Γm} m → m !!{Γ} a = Some w → (Γ,Γm) ⊢ g w : type_of w →
  ¬ctree_unmapped (g w) → ✓{Γ,Γm} (cmap_alter Γ g a m).
Proof.
  destruct m as [m]; intros ? [Hm1 Hm2] Hw ? Hgw; split; simpl in *.
  { intros o τ; rewrite lookup_alter_Some;
      intros [(?&[]&?&?)|[??]]; eauto; simplify_option_equality. }
  intros o ? β; rewrite lookup_alter_Some;
    intros [(?&[|w' β']&?&?)|[??]]; simplify_map_equality'; eauto.
  case_option_guard; simplify_equality'.
  destruct (w' !!{Γ} addr_ref Γ a) as [w''|] eqn:?; simplify_equality'.
  destruct (Hm2 (addr_index a) w' β') as (τ&?&?&?&?&?); auto.
  exists τ; simplify_option_equality.
  { intuition eauto using ctree_alter_lookup_Forall,
      ctree_alter_typed, @ctree_empty_unmapped. }
  destruct (ctree_lookup_Some Γ Γm w' τ (addr_ref Γ a) w'') as (τ'&?&?); auto.
  assert ((Γ,Γm) ⊢ w : ucharT)
    by eauto using ctree_lookup_byte_typed; simplify_type_equality'.
  split_ands; auto.
  { eapply ctree_alter_typed; eauto using ctree_alter_byte_typed,
      type_of_typed, ctree_alter_byte_unmapped. }
  contradict Hgw; eapply (ctree_alter_byte_unmapped _ _ _ w'');
    eauto using ctree_alter_lookup_Forall, @ctree_empty_unmapped.
Qed.
Lemma cmap_alter_freeze Γ q g m a :
  cmap_alter Γ g (freeze q a) m = cmap_alter Γ g a m.
Proof.
  destruct m as [m]; f_equal'. rewrite addr_index_freeze,
    addr_ref_freeze, addr_ref_byte_freeze, ctree_alter_freeze.
  apply alter_ext; intros [|??] ?; f_equal'; apply ctree_alter_ext; intros.
  by rewrite (decide_iff _ _ _ _ (addr_is_obj_freeze q a)).
Qed.
Lemma cmap_alter_commute Γ Γm g1 g2 m a1 a2 w1 w2 τ1 τ2 :
  ✓ Γ → ✓{Γ,Γm} m → a1 ⊥{Γ} a2 → 
  (Γ,Γm) ⊢ a1 : τ1 → m !!{Γ} a1 = Some w1 → (Γ,Γm) ⊢ g1 w1 : τ1 →
  (Γ,Γm) ⊢ a2 : τ2 → m !!{Γ} a2 = Some w2 → (Γ,Γm) ⊢ g2 w2 : τ2 →
  cmap_alter Γ g1 a1 (cmap_alter Γ g2 a2 m)
  = cmap_alter Γ g2 a2 (cmap_alter Γ g1 a1 m).
Proof.
  destruct m as [m]; simpl;
    intros ? Hm [?|[[-> ?]|(->&Ha&?&?&?)]] ? Hw1 ?? Hw2?; f_equal.
  { by rewrite alter_commute. }
  { rewrite <-!alter_compose.
    apply alter_ext; intros [|??] ?; f_equal'; auto using ctree_alter_commute. }
  rewrite <-!alter_compose.
  apply alter_ext; intros [|w β] Hw; f_equal'; simplify_type_equality'.
  repeat case_option_guard; simplify_equality'.
  rewrite Hw in Hw1, Hw2; simplify_equality'.
  rewrite <-!(ctree_alter_freeze _ true _ (addr_ref Γ a1)), !Ha,
    !ctree_alter_freeze, <-!ctree_alter_compose.
  destruct (w !!{Γ} addr_ref Γ a1) as [w1'|] eqn:Hw1',
    (w !!{Γ} addr_ref Γ a2) as [w2'|] eqn:Hw2'; simplify_option_equality.
  assert (τ1 = ucharT) by intuition eauto using addr_not_obj_type.
  assert (τ2 = ucharT) by intuition eauto using addr_not_obj_type.
  destruct (proj2 Hm (addr_index a2) w β)
    as (τ&?&_&?&_); auto; simplify_equality'.
  assert (w1' = w2') by eauto using ctree_lookup_freeze_proper; subst.
  destruct (ctree_lookup_Some Γ Γm w τ
    (addr_ref Γ a2) w2') as (τ'&_&?); auto.
  eapply ctree_alter_ext_lookup; simpl; eauto using ctree_alter_byte_commute.
Qed.
(** We need [addr_is_obj a] because padding bytes are ignored *)
Lemma cmap_lookup_alter Γ Γm g m a w :
  ✓ Γ → ✓{Γ,Γm} m → addr_is_obj a → m !!{Γ} a = Some w →
  cmap_alter Γ g a m !!{Γ} a = Some (g w).
Proof.
  destruct m as [m]; simpl; intros. case_option_guard; simplify_map_equality'.
  destruct (m !! addr_index a) as [[|w' β]|] eqn:?; simplify_equality'.
  destruct (w' !!{Γ} addr_ref Γ a) as [w''|] eqn:?; simplify_equality'.
  erewrite ctree_lookup_alter by eauto using ctree_lookup_unfreeze; simpl.
  by case_decide; simplify_equality'.
Qed.
Lemma cmap_lookup_alter_not_obj Γ Γm g m a w τ :
  ✓ Γ → ✓{Γ,Γm} m → ¬addr_is_obj a →
  (Γ,Γm) ⊢ a : τ → m !!{Γ} a = Some w → (Γ,Γm) ⊢ g w : τ → ctree_unshared (g w) →
  cmap_alter Γ g a m !!{Γ} a =
  Some (ctree_lookup_byte_after Γ (addr_type_base a) (addr_ref_byte Γ a) (g w)).
Proof.
  destruct m as [m]; simpl; intros ? Hm ?????.
  case_option_guard; simplify_map_equality'.
  assert (Γm ⊢ addr_index a : addr_type_object a)
    by eauto using addr_typed_index.
  destruct (m !! addr_index a) as [[|w' β]|] eqn:?; simplify_equality'.
  destruct (proj2 Hm (addr_index a) w' β)
    as (?&?&_&?&?&_); auto; simplify_type_equality'.
  assert (Γ ⊢ addr_ref Γ a : addr_type_object a ↣ addr_type_base a).
  { eapply addr_typed_ref_typed; eauto. }
  destruct (w' !!{Γ} addr_ref Γ a) as [w''|] eqn:?; simplify_equality'.
  destruct (ctree_lookup_Some Γ Γm w' (addr_type_object a)
    (addr_ref Γ a) w'') as (τ''&?&?); auto; simplify_type_equality.
  erewrite ctree_lookup_alter by eauto using ctree_lookup_unfreeze; simpl.
  case_decide; [done|]; case_option_guard; simplify_equality'.
  assert (τ = ucharT) by (intuition eauto using addr_not_obj_type); subst.
  erewrite option_guard_True, ctree_lookup_alter_byte
    by intuition eauto using ctree_alter_byte_Forall, pbit_indetify_unshared.
  by simplify_option_equality.
Qed.
Lemma cmap_lookup_alter_disjoint Γ Γm g m a1 a2 w1 w2 τ2 :
  ✓ Γ → ✓{Γ,Γm} m → a1 ⊥{Γ} a2 → m !!{Γ} a1 = Some w1 →
  (Γ,Γm) ⊢ a2 : τ2 → m !!{Γ} a2 = Some w2 → (Γ,Γm) ⊢ g w2 : τ2 →
  (ctree_unshared w2 → ctree_unshared (g w2)) →
  cmap_alter Γ g a2 m !!{Γ} a1 = Some w1.
Proof.
  destruct m as [m]; simpl; intros ? Hm [?|[[-> ?]|(->&Ha&?&?&?)]] ?? Hw2 ??;
    simplify_map_equality; auto.
  { repeat case_option_guard; simplify_equality'; try contradiction.
    destruct (m !! _) as [[|w2' β]|]; simplify_equality'.
    destruct (w2' !!{Γ} addr_ref Γ a1) as [w1''|] eqn:?,
      (w2' !!{Γ} addr_ref Γ a2) as [w2''|] eqn:?; simplify_equality'.
    by erewrite ctree_lookup_alter_disjoint by eauto. }
  repeat case_option_guard; simplify_type_equality'; try contradiction.
  destruct (m !! _) as [[|w β]|]eqn:?; simplify_equality'.
  destruct (proj2 Hm (addr_index a2) w β)
    as (τ&_&?&?&_); auto; simplify_equality'.
  destruct (w !!{Γ} addr_ref Γ a1) as [w1'|] eqn:?,
    (w !!{Γ} addr_ref Γ a2) as [w2'|] eqn:?; simplify_equality'.
  assert (w1' = w2') by eauto using ctree_lookup_freeze_proper; subst.
  destruct (ctree_lookup_Some Γ Γm w τ (addr_ref Γ a2) w2') as (τ'&_&?); auto.
  simplify_option_equality.
  assert (τ2 = ucharT) by (intuition eauto using addr_not_obj_type); subst.
  erewrite ctree_lookup_alter by eauto using ctree_lookup_unfreeze; csimpl.
  assert (ctree_unshared (g w2))
    by intuition eauto using ctree_lookup_byte_Forall, pbit_indetify_unshared.
  by erewrite option_guard_True, ctree_lookup_alter_byte_ne
    by intuition eauto using ctree_alter_byte_Forall, pbit_indetify_unshared.
Qed.
Lemma cmap_alter_disjoint Γ Γm1 m1 m2 g a w1 τ1 :
  ✓ Γ → ✓{Γ,Γm1} m1 → m1 ⊥ m2 →
  (Γ,Γm1) ⊢ a : τ1 → m1 !!{Γ} a = Some w1 → (Γ,Γm1) ⊢ g w1 : τ1 →
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
    assert (τ1 = ucharT) by intuition eauto using addr_not_obj_type.
    simplify_equality; split_ands; auto.
    { eapply ctree_alter_disjoint; intuition eauto 3
        using ctree_alter_byte_unmapped, ctree_alter_byte_disjoint. }
    intuition eauto using ctree_alter_byte_unmapped, ctree_alter_lookup_Forall.
  * assert (∃ w2', w1' ⊥ w2') as (w2'&?).
    { exists (ctree_new Γ ∅ τ); symmetry. eauto using ctree_new_disjoint. }
    destruct Hm. case_decide; simplify_option_equality.
    { intuition eauto using ctree_alter_disjoint, ctree_alter_lookup_Forall,
        @ctree_disjoint_valid_l, ctree_alter_disjoint. }
    assert (τ1 = ucharT) by intuition eauto using addr_not_obj_type.
    simplify_equality. split.
    { eapply ctree_disjoint_valid_l, ctree_alter_disjoint; intuition eauto 3
        using ctree_alter_byte_disjoint, ctree_alter_byte_unmapped. }
    intuition eauto using ctree_alter_byte_unmapped, ctree_alter_lookup_Forall.
Qed.
Lemma cmap_alter_union Γ Γm1 m1 m2 g a w1 τ1 :
  ✓ Γ → ✓{Γ,Γm1} m1 → m1 ⊥ m2 →
  (Γ,Γm1) ⊢ a : τ1 → m1 !!{Γ} a = Some w1 → (Γ,Γm1) ⊢ g w1 : τ1 →
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
  assert (τ1 = ucharT) by intuition eauto using addr_not_obj_type.
  simplify_equality. eapply ctree_alter_union; intuition eauto 3 using
   ctree_alter_byte_disjoint, ctree_alter_byte_union, ctree_alter_byte_unmapped.
Qed.
Lemma cmap_non_aliasing Γ Γm m a1 a2 σ1 σ2 :
  ✓ Γ → ✓{Γ,Γm} m → (Γ,Γm) ⊢ a1 : σ1 → frozen a1 → addr_is_obj a1 →
  (Γ,Γm) ⊢ a2 : σ2 → frozen a2 → addr_is_obj a2 →
  (**i 1.) *) (∀ j1 j2, addr_plus Γ j1 a1 ⊥{Γ} addr_plus Γ j2 a2) ∨
  (**i 2.) *) σ1 ⊆{Γ} σ2 ∨
  (**i 3.) *) σ2 ⊆{Γ} σ1 ∨
  (**i 4.) *) ∀ g j1 j2,
    cmap_alter Γ g (addr_plus Γ j1 a1) m !!{Γ} addr_plus Γ j2 a2 = None ∧
    cmap_alter Γ g (addr_plus Γ j2 a2) m !!{Γ} addr_plus Γ j1 a1 = None.
Proof.
  intros ? Hm ??????. destruct (addr_disjoint_cases Γ Γm a1 a2 σ1 σ2)
    as [Ha12|[?|[?|(Hidx&s&r1'&i1&r2'&i2&r'&Ha1&Ha2&?)]]]; auto.
  do 3 right. intros g j1 j2.
  assert (Γm ⊢ addr_index a1 : addr_type_object a1)
    by eauto using addr_typed_index.
  assert (Γm ⊢ addr_index a1 : addr_type_object a2)
    by (rewrite Hidx; eauto using addr_typed_index).
  destruct m as [m]; unfold insertE, cmap_alter, lookupE, cmap_lookup;
    simpl in *; rewrite !addr_index_plus, <-!Hidx; simplify_map_equality'.
  destruct (m !! addr_index a1) as [[|w β]|] eqn:?;
    [by simplify_option_equality| |by simplify_option_equality].
  destruct (proj2 Hm (addr_index a1) w β)
    as (τ&?&_&?&_); auto; simplify_type_equality'.
  assert (Γ ⊢ r1' ++ RUnion i1 s true :: r' :
    addr_type_object a2 ↣ addr_type_base a1).
  { erewrite <-Ha1, <-(typed_unique _ (addr_index a1)
      (addr_type_object a1) (addr_type_object a2)) by eauto.
    eauto using addr_typed_ref_base_typed. }
  assert (Γ ⊢ r2' ++ RUnion i2 s true :: r' :
    addr_type_object a2 ↣ addr_type_base a2).
  { rewrite <-Ha2. eauto using addr_typed_ref_base_typed. }
  unfold addr_ref; rewrite !addr_ref_base_plus, Ha1, Ha2.
  by split; case_option_guard; simplify_equality;
    erewrite ?ctree_lookup_non_aliasing by eauto.
Qed.

(** ** Refinements *)
Lemma cmap_refine_memenv_refine Γ f Γm1 Γm2 m1 m2 :
  m1 ⊑{Γ,f@Γm1↦Γm2} m2 → Γm1 ⊑{Γ,f} Γm2.
Proof. by intros (?&?&?&?). Qed.
Lemma cmap_refine_injective Γ f Γm1 Γm2 m1 m2 :
  m1 ⊑{Γ,f@Γm1↦Γm2} m2 → mem_inj_injective f.
Proof. eauto using cmap_refine_memenv_refine, memenv_refine_injective. Qed.
Lemma cmap_refine_valid_l Γ f Γm1 Γm2 m1 m2: m1 ⊑{Γ,f@Γm1↦Γm2} m2 → ✓{Γ,Γm1} m1.
Proof. by intros (?&?&?&?). Qed.
Lemma cmap_refine_valid_l' Γ f m1 m2: m1 ⊑{Γ,f} m2 → ✓{Γ} m1.
Proof. by apply cmap_refine_valid_l. Qed.
Lemma cmap_refine_valid_r Γ f Γm1 Γm2 m1 m2: m1 ⊑{Γ,f@Γm1↦Γm2} m2 → ✓{Γ,Γm2} m2.
Proof. by intros (?&?&?&?). Qed.
Lemma cmap_refine_valid_r' Γ f m1 m2: m1 ⊑{Γ,f} m2 → ✓{Γ} m2.
Proof. by apply cmap_refine_valid_r. Qed.
Hint Immediate cmap_refine_valid_l cmap_refine_valid_r.
Lemma cmap_refine_id Γ Γm m : ✓ Γ → ✓{Γ,Γm} m → m ⊑{Γ@Γm} m.
Proof.
  destruct m as [m]; intros ? Hm.
  do 2 red; split_ands; simpl; auto using memenv_refine_id.
  intros ? o r w malloc ??; simplify_equality'.
  destruct (proj2 Hm o w malloc) as (τ&?&_&?&_); auto.
  exists w w; eauto 6 using ctree_refine_id, type_of_typed.
Qed.
Lemma cmap_refine_id' Γ m : ✓ Γ → ✓{Γ} m → m ⊑{Γ} m.
Proof. by apply cmap_refine_id. Qed.
Lemma cmap_refine_compose Γ f1 f2 Γm1 Γm2 Γm3 m1 m2 m3 :
  ✓ Γ → m1 ⊑{Γ,f1@Γm1↦Γm2} m2 → m2 ⊑{Γ,f2@Γm2↦Γm3} m3 →
  m1 ⊑{Γ,f1 ◎ f2@Γm1↦Γm3} m3.
Proof.
  intros ? (?&?&?&Hm12) (?&Hm3&?&Hm23);
    split; split_ands; eauto 2 using memenv_refine_compose.
  intros o1 o3 r w1 malloc.
  rewrite lookup_mem_inj_compose_Some; intros (o2&r2&r3&?&?&->) Hw1.
  destruct (Hm12 o1 o2 r2 w1 malloc) as (w2&w2'&τ2&?&?&?&?); auto.
  destruct (Hm23 o2 o3 r3 w2 malloc) as (w3&w3'&τ3&->&?&?&?); auto.
  destruct (ctree_lookup_refine Γ f2 Γm2 Γm3 w2 w3' τ3
    (freeze true <$> r2) w2') as (w3''&?&Hw23); auto.
  erewrite ctree_refine_type_of_r in Hw23 by eauto. exists w3 w3'' τ2.
  rewrite fmap_app, ctree_lookup_app; simplify_option_equality.
  naive_solver eauto using ctree_refine_compose.
Qed.
Lemma cmap_refine_compose' Γ f1 f2 m1 m2 m3 :
  ✓ Γ → m1 ⊑{Γ,f1} m2 → m2 ⊑{Γ,f2} m3 → m1 ⊑{Γ,f1 ◎ f2} m3.
Proof. by apply cmap_refine_compose. Qed.
Lemma cmap_lookup_refine Γ f Γm1 Γm2 m1 m2 a1 a2 w1 τ :
  ✓ Γ → m1 ⊑{Γ,f@Γm1↦Γm2} m2 →
  a1 ⊑{Γ,f@Γm1↦Γm2} a2 : τ → m1 !!{Γ} a1 = Some w1 →
  ∃ w2, m2 !!{Γ} a2 = Some w2 ∧ w1 ⊑{Γ,f@Γm1↦Γm2} w2 : τ.
Proof.
  destruct m1 as [m1], m2 as [m2]; simpl; intros ? (Hm1&_&_&Hm) Ha Hw1.
  assert ((Γ,Γm1) ⊢ a1 : τ) by eauto using addr_refine_typed_l.
  assert ((Γ,Γm2) ⊢ a2 : τ) by eauto using addr_refine_typed_r.
  case_option_guard; simplify_type_equality'.
  rewrite option_guard_True by eauto using addr_strict_refine.
  destruct (m1 !! addr_index a1) as [[|w1' β]|] eqn:?; simplify_equality'.
  destruct (w1' !!{Γ} addr_ref Γ a1) as [w1''|] eqn:?; simplify_equality'.
  destruct (addr_ref_refine Γ f Γm1 Γm2 a1 a2 τ) as (r&?&->); auto.
  destruct (Hm (addr_index a1) (addr_index a2) r w1' β)
    as (w2&w2'&τ2&->&Hr&?&_); auto; csimpl.
  destruct (ctree_lookup_Some Γ Γm1 w1' τ2
    (addr_ref Γ a1) w1'') as (σ'&?&?); eauto using ctree_refine_typed_l.
  rewrite ctree_lookup_app, Hr; csimpl.
  destruct (ctree_lookup_refine Γ f Γm1 Γm2 w1' w2' τ2
    (addr_ref Γ a1) w1'') as (w2''&->&?); auto; csimpl.
  rewrite <-(decide_iff _ _ _ _ (addr_is_obj_refine _ _ _ _ _ _ _ Ha));
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
Lemma cmap_refine_weaken Γ Γ' f f' Γm1 Γm2 m1 m2 :
  ✓ Γ → m1 ⊑{Γ,f@Γm1↦Γm2} m2 → Γ ⊆ Γ' → (∀ o τ, Γm1 ⊢ o : τ → f!!o = f'!!o) →
  mem_inj_injective f' → m1 ⊑{Γ',f'@Γm1↦Γm2} m2.
Proof.
  intros ? (Hm1&?&HΓm&Hm) ? Hf ?; split; split_ands;
    eauto using cmap_valid_weaken, memenv_refine_weaken.
  assert (∀ o o2 r τ, Γm1 ⊢ o : τ → f !! o = Some (o2,r) →
    f' !! o = Some (o2,r)) by (by intros; erewrite <-Hf by eauto).
  assert (∀ o o2 r τ, Γm1 ⊢ o : τ → f' !! o = Some (o2,r) →
    f !! o = Some (o2,r)) by (by intros; erewrite Hf by eauto).
  intros o1 o2 r w1 malloc ??.
  destruct HΓm as (?&?&?), (proj2 Hm1 o1 w1 malloc) as (τ&?&_); auto.
  destruct (Hm o1 o2 r w1 malloc) as (w2&w2'&τ'&?&?&?&?); eauto.
  exists w2 w2' τ'; eauto 7 using ctree_refine_weaken, ctree_lookup_weaken.
Qed.
Lemma cmap_alter_refine Γ f Γm1 Γm2 g1 g2 m1 m2 a1 a2 w1 w2 τ :
  ✓ Γ → m1 ⊑{Γ,f@Γm1↦Γm2} m2 → a1 ⊑{Γ,f@Γm1↦Γm2} a2 : τ →
  m1 !!{Γ} a1 = Some w1 → m2 !!{Γ} a2 = Some w2 → ¬ctree_unmapped w1 →
  g1 w1 ⊑{Γ,f@Γm1↦Γm2} g2 w2 : τ → ¬ctree_unmapped (g1 w1) →
  cmap_alter Γ g1 a1 m1 ⊑{Γ,f@Γm1↦Γm2} cmap_alter Γ g2 a2 m2.
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
  destruct (addr_ref_refine Γ f Γm1 Γm2 a1 a2 τ) as (r2&?&Hr2); auto.
  rewrite Hr2 in Hw2 |- *; clear Hr2.
  destruct (m1 !! addr_index a1) as [[|w1' ?]|] eqn:?; simplify_equality'.
  destruct (m2 !! addr_index a2) as [[|w2' ?]|] eqn:?; simplify_equality'.
  rewrite ctree_lookup_app in Hw2.
  destruct (w1' !!{Γ} addr_ref Γ a1) as [w1''|] eqn:?; simplify_equality'.
  destruct (decide (o3 = addr_index a1)); simplify_map_equality'.
  * destruct (Hm (addr_index a1) (addr_index a2) r2 w1' malloc)
      as (?&w2''&τ2&?&?&?&?); auto.
    destruct (ctree_lookup_refine Γ f Γm1 Γm2 w1' w2'' τ2
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
  * destruct (mem_inj_injective_ne f (addr_index a1)
      (addr_index a2) o3 o4 r2 r4) as [?|[??]];
      eauto using memenv_refine_injective; simplify_map_equality'; [eauto|].
    destruct (Hm o3 (addr_index a2) r4 w3 malloc)
      as (w4''&w4'&τ4&?&?&?&?); auto; simplify_map_equality'.
    eexists _, w4', τ4; split_ands; eauto.
    by erewrite ctree_alter_app, ctree_lookup_alter_disjoint by
      (eauto; by apply ref_disjoint_freeze_l, ref_disjoint_freeze_r).
Qed.
End cmap_typed.
