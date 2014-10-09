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
  Definition index_alive' (m : mem Ti) (o : index) : Prop :=
    match cmap_car m !! o with Some (Obj _ _) => True | _ => False end.

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
End operations.

Notation "'{ m }" := (memenv_of m) (at level 20, format "''{' m }").

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
Implicit Types g : mtree Ti → mtree Ti.
Implicit Types α β : bool.
Local Opaque nmap.Nempty.

Arguments lookupE _ _ _ _ _ _ _ !_ /.
Arguments cmap_lookup _ _ _ _ !_ /.
Hint Extern 0 (Separation _) => apply (_ : Separation (pbit Ti)).

Lemma index_alive_spec' m o : index_alive' m o ↔ index_alive ('{m}) o.
Proof.
  unfold index_alive'; destruct m as [m]; simpl; split.
  * intros. destruct (m !! o) as [[|w]|] eqn:?; try done.
    by exists (type_of w); simplify_map_equality'.
  * intros [τ ?]; simplify_map_equality'.
    by destruct (m !! o) as [[|w []]|] eqn:?.
Qed.
Lemma index_alive_1' m o : index_alive' m o → index_alive ('{m}) o.
Proof. by rewrite index_alive_spec'. Qed.
Lemma index_alive_2' m o : index_alive ('{m}) o → index_alive' m o.
Proof. by rewrite index_alive_spec'. Qed.
Global Instance index_alive_dec' m o : Decision (index_alive' m o).
Proof.
  refine
    match cmap_car m !! o as mw' return Decision (match mw' with
       Some (Obj _ _) => True | _ => False end) with
    | Some (Obj _ _) => left _ | _ => right _
    end; tauto.
Defined.

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
Lemma cmap_lookup_weaken Γ1 Γ2 Γm m a w σ :
  ✓ Γ1 → (Γ1,Γm) ⊢ a : σ → m !!{Γ1} a = Some w → Γ1 ⊆ Γ2 → m !!{Γ2} a = Some w.
Proof.
  destruct m as [m]; simpl; intros. case_option_guard; simplify_equality'.
  rewrite option_guard_True by eauto using addr_strict_weaken.
  destruct (m !! addr_index a) as [[|w' β]|]; simplify_equality'.
  destruct (w' !!{Γ1} addr_ref Γ1 a) as [w''|] eqn:?; simplify_equality'.
  by erewrite <-addr_ref_weaken, <-addr_ref_byte_weaken,
    ctree_lookup_weaken by eauto.
Qed.
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
End memory_map.
