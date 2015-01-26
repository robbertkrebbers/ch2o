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
    (**i 1). *) ✓{Γ} Γm ∧
    (**i 2). *) (∀ o τ,
      cmap_car m !! o = Some (Freed τ) → Γm ⊢ o : τ ∧ ¬index_alive Γm o) ∧
    (**i 3). *) (∀ o w malloc,
      cmap_car m !! o = Some (Obj w malloc) →
      ∃ τ, Γm ⊢ o : τ ∧ index_alive Γm o ∧ (Γ,Γm) ⊢ w : τ ∧ ¬ctree_empty w).
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
    '(w',_) ← cmap_car m !! addr_index a ≫= maybe2 Obj;
    w ← lookupE Γ (addr_ref Γ a) w';
    if decide (addr_is_obj a) then Some w
    else guard (ctree_unshared w); w !!{Γ} (addr_ref_byte Γ a).
  Definition cmap_alter (Γ : env Ti) (g : mtree Ti → mtree Ti)
      (a : addr Ti) (m : mem Ti) : mem Ti :=
    let (m) := m in
    let G := if decide (addr_is_obj a) then g
             else ctree_alter_byte Γ g (addr_ref_byte Γ a) in
    CMap $
      alter (cmap_elem_map (ctree_alter Γ G (addr_ref Γ a))) (addr_index a) m.
  Definition cmap_singleton (Γ : env Ti) (a : addr Ti)
      (malloc : bool) (w : mtree Ti) : mem Ti :=
    CMap {[ addr_index a, Obj (ctree_singleton Γ (addr_ref Γ a) w) malloc ]}.
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
Lemma index_alive_erase' m o :
  index_alive' (cmap_erase m) o = index_alive' m o.
Proof.
  unfold index_alive'; destruct m as [m]; simpl.
  rewrite lookup_omap. by destruct (m !! o) as [[]|].
Qed.

Lemma cmap_valid_Freed Γ Γm m o τ :
  ✓{Γ,Γm} m → cmap_car m !! o = Some (Freed τ) →
  Γm ⊢ o : τ ∧ ¬index_alive Γm o ∧ ✓{Γ} τ ∧ int_typed (size_of Γ τ) sptrT.
Proof. intros (HΓm&Hm&_) ?. destruct (HΓm o τ), (Hm o τ); auto. Qed.
Lemma cmap_valid_Obj Γ Γm m o w malloc :
  ✓{Γ,Γm} m → cmap_car m !! o = Some (Obj w malloc) →
  ∃ τ, Γm ⊢ o : τ ∧ index_alive Γm o ∧ (Γ,Γm) ⊢ w : τ
    ∧ ¬ctree_empty w ∧ int_typed (size_of Γ τ) sptrT.
Proof.
  intros (HΓm&_&Hm) ?; destruct (Hm o w malloc) as (τ&?&?&?&?); auto.
  destruct (HΓm o τ); eauto 10.
Qed.
Lemma cmap_valid_memenv_valid Γ Γm m : ✓{Γ,Γm} m → ✓{Γ} Γm.
Proof. by intros []. Qed.
Lemma cmap_index_typed_valid Γ Γm m o τ : ✓{Γ,Γm} m → Γm ⊢ o : τ → ✓{Γ} τ.
Proof. eauto using cmap_valid_memenv_valid, index_typed_valid. Qed.
Lemma cmap_index_typed_representable Γ Γm m o τ :
  ✓{Γ,Γm} m → Γm ⊢ o : τ → int_typed (size_of Γ τ) sptrT.
Proof. eauto using cmap_valid_memenv_valid, index_typed_representable. Qed.
Lemma cmap_empty_valid Γ : ✓{Γ} (∅ : mem Ti).
Proof.
  split; [apply memenv_empty_valid|].
  by split; intros until 0; simplify_map_equality'.
Qed.
Lemma cmap_valid_weaken Γ1 Γ2 Γm m : ✓ Γ1 → ✓{Γ1,Γm} m → Γ1 ⊆ Γ2 → ✓{Γ2,Γm} m.
Proof.
  intros ? (HΓm&Hm1&Hm2) ?; split_ands'; eauto using memenv_valid_weaken.
  intros o w malloc ?; destruct (Hm2 o w malloc)
    as (τ&?&?&?&?); eauto 10 using ctree_typed_weaken.
Qed.
Lemma cmap_valid'_weaken Γ1 Γ2 m : ✓ Γ1 → ✓{Γ1} m → Γ1 ⊆ Γ2 → ✓{Γ2} m.
Proof. by apply cmap_valid_weaken. Qed.
Lemma cmap_valid_sep_valid Γ Γm m : ✓{Γ,Γm} m → sep_valid m.
Proof.
  destruct m as [m]; intros Hm o [τ|w malloc] ?; [done|].
  destruct (cmap_valid_Obj Γ Γm (CMap m) o w malloc)
    as (?&?&?&?&?&?); simpl; eauto using ctree_typed_sep_valid.
Qed.
Lemma index_typed_lookup_cmap m o τ :
  '{m} ⊢ o : τ → ∃ x, cmap_car m !! o = Some x ∧
  match x with Freed τ' => τ' = τ | Obj w _ => type_of w = τ end.
Proof.
  intros [β Hβ]. destruct m as [m]; simplify_map_equality'.
  by destruct (m !! o) as [[]|]; simplify_equality'; do 2 eexists; eauto.
Qed.
Lemma cmap_index_typed Γ Γm m o τ : ✓{Γ,Γm} m → '{m} ⊢ o : τ → Γm ⊢ o : τ.
Proof.
  intros.
  destruct (index_typed_lookup_cmap m o τ) as ([|w malloc]&?&?); auto; subst.
  * by destruct (cmap_valid_Freed Γ Γm m o τ).
  * by destruct (cmap_valid_Obj Γ Γm m o w malloc)
      as (τ&?&?&?&?&_); simplify_type_equality.
Qed.
Lemma cmap_erase_typed Γ Γm m : ✓{Γ,Γm} m →  ✓{Γ,Γm} (cmap_erase m).
Proof.
  destruct m as [m]; unfold lookupE; intros (?&?&?); split_ands'; simpl in *.
  * done.
  * intros o τ. rewrite lookup_omap. by destruct (m !! o) as [[]|].
  * intros o w maloc. rewrite lookup_omap.
    destruct (m !! o) as [[]|] eqn:?; intros; simplify_equality'; eauto.
Qed.
Lemma cmap_lookup_erase Γ m a : cmap_erase m !!{Γ} a = m !!{Γ} a.
Proof.
  unfold lookupE, cmap_lookup; destruct m as [m]; simpl.
  rewrite lookup_omap. by destruct (m !! addr_index a) as [[]|].
Qed.
Lemma cmap_lookup_weaken Γ1 Γ2 Γm m a w σ :
  ✓ Γ1 → (Γ1,Γm) ⊢ a : Some σ → m !!{Γ1} a = Some w → Γ1 ⊆ Γ2 →
  m !!{Γ2} a = Some w.
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
  erewrite ctree_lookup_le by eauto using ref_freeze_le_r; csimpl.
  by rewrite (decide_iff _ _ _ _ (addr_is_obj_freeze _ _)).
Qed.
Lemma cmap_lookup_typed Γ Γm m a w σ :
  ✓ Γ → ✓{Γ,Γm} m → (Γ,Γm) ⊢ a : Some σ → m !!{Γ} a = Some w → (Γ,Γm) ⊢ w : σ.
Proof.
  destruct m as [m]; simpl; intros ? Hm Ha ?.
  case_option_guard; simplify_equality'.
  destruct (m !! addr_index a) as [[|w' β]|] eqn:Hw; simplify_equality'.
  destruct (w' !!{Γ} addr_ref Γ a) as [w''|] eqn:?; simplify_equality'.
  destruct (cmap_valid_Obj Γ Γm (CMap m) (addr_index a) w' β)
    as (τ&?&?&?&_); auto; simplify_equality'.
  destruct (ctree_lookup_Some Γ Γm w' τ (addr_ref Γ a) w'')
    as (σ'&?&?); auto; simplify_option_equality; simplify_type_equality.
  * cut (σ = σ'); [by intros ->|].
    erewrite (addr_is_obj_type _ _ _ σ) by eauto.
    assert (Γm ⊢ addr_index a : addr_type_object a)
      by eauto using addr_typed_index; simplify_type_equality.
    eauto using ref_set_offset_typed_unique, addr_typed_ref_base_typed.
  * erewrite addr_not_is_obj_type by eauto. eauto using ctree_lookup_byte_typed.
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
  destruct (cmap_valid_Obj Γ Γm (CMap m) (addr_index a) w' β)
    as (τ&?&?&?&_); auto; simplify_equality'.
  destruct (ctree_lookup_Some Γ Γm w' τ (addr_ref Γ a) w'')
    as (σ'&?&?); auto; simplify_option_equality;
    eauto using ctree_lookup_byte_typed, type_of_typed.
Qed.
Lemma cmap_erase_alter Γ g m a :
  cmap_erase (cmap_alter Γ g a m) = cmap_alter Γ g a (cmap_erase m).
Proof.
  unfold lookupE, cmap_lookup; destruct m as [m]; f_equal'; apply map_eq.
  intros o; destruct (decide (o = addr_index a)); simplify_map_equality; auto.
  by destruct (m !! addr_index a) as [[]|].
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
  destruct (cmap_valid_Obj Γ Γm (CMap m) (addr_index a) w' β)
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
  destruct m as [m]; intros ? (HΓm&Hm1&Hm2) Hw ? Hgw; split_ands'; simpl in *.
  { done. }
  { intros o τ; rewrite lookup_alter_Some;
      intros [(?&[]&?&?)|[??]]; eauto; simplify_option_equality. }
  intros o ? β; rewrite lookup_alter_Some;
    intros [(?&[|w' β']&?&?)|[??]]; simplify_map_equality'; eauto.
  case_option_guard; simplify_equality'.
  destruct (w' !!{Γ} addr_ref Γ a) as [w''|] eqn:?; simplify_equality'.
  destruct (Hm2 (addr_index a) w' β') as (τ&?&?&?&?); auto.
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
Lemma cmap_alter_commute Γ Γm g1 g2 m a1 a2 w1 w2 τ1 τ2 :
  ✓ Γ → ✓{Γ,Γm} m → a1 ⊥{Γ} a2 → 
  (Γ,Γm) ⊢ a1 : Some τ1 → m !!{Γ} a1 = Some w1 → (Γ,Γm) ⊢ g1 w1 : τ1 →
  (Γ,Γm) ⊢ a2 : Some τ2 → m !!{Γ} a2 = Some w2 → (Γ,Γm) ⊢ g2 w2 : τ2 →
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
  rewrite <-!(ctree_alter_le _ _ (freeze true <$> addr_ref Γ a1)), !Ha,
    !(ctree_alter_le _ _ (freeze true <$> addr_ref Γ a2) (addr_ref Γ a2)),
    <-!ctree_alter_compose by eauto using ref_freeze_le_l.
  destruct (w !!{Γ} addr_ref Γ a1) as [w1'|] eqn:Hw1',
    (w !!{Γ} addr_ref Γ a2) as [w2'|] eqn:Hw2'; simplify_option_equality.
  assert (τ1 = ucharT) by eauto using addr_not_is_obj_type.
  assert (τ2 = ucharT) by eauto using addr_not_is_obj_type.
  destruct (cmap_valid_Obj Γ Γm (CMap m) (addr_index a2) w β)
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
  erewrite ctree_lookup_alter
    by eauto using ctree_lookup_le, ref_freeze_le_r; simpl.
  by case_decide; simplify_equality'.
Qed.
Lemma cmap_lookup_alter_not_obj Γ Γm g m a w τ :
  ✓ Γ → ✓{Γ,Γm} m → ¬addr_is_obj a →
  (Γ,Γm) ⊢ a : Some τ → m !!{Γ} a = Some w → (Γ,Γm) ⊢ g w : τ →
  ctree_unshared (g w) → cmap_alter Γ g a m !!{Γ} a =
  Some (ctree_lookup_byte_after Γ (addr_type_base a) (addr_ref_byte Γ a) (g w)).
Proof.
  destruct m as [m]; simpl; intros ? Hm ?????.
  case_option_guard; simplify_map_equality'.
  assert (Γm ⊢ addr_index a : addr_type_object a)
    by eauto using addr_typed_index.
  destruct (m !! addr_index a) as [[|w' β]|] eqn:?; simplify_equality'.
  destruct (cmap_valid_Obj Γ Γm (CMap m) (addr_index a) w' β)
    as (?&?&_&?&?&_); auto; simplify_type_equality'.
  assert (Γ ⊢ addr_ref Γ a : addr_type_object a ↣ addr_type_base a).
  { eapply addr_typed_ref_typed; eauto. }
  destruct (w' !!{Γ} addr_ref Γ a) as [w''|] eqn:?; simplify_equality'.
  destruct (ctree_lookup_Some Γ Γm w' (addr_type_object a)
    (addr_ref Γ a) w'') as (τ''&?&?); auto; simplify_type_equality.
  erewrite ctree_lookup_alter
    by eauto using ctree_lookup_le, ref_freeze_le_r; simpl.
  case_decide; [done|]; case_option_guard; simplify_equality'.
  assert (τ = ucharT) by eauto using addr_not_is_obj_type; subst.
  erewrite option_guard_True, ctree_lookup_alter_byte
    by intuition eauto using ctree_alter_byte_Forall, pbit_indetify_unshared.
  by simplify_option_equality.
Qed.
Lemma cmap_lookup_alter_disjoint Γ Γm g m a1 a2 w1 w2 τ2 :
  ✓ Γ → ✓{Γ,Γm} m → a1 ⊥{Γ} a2 → m !!{Γ} a1 = Some w1 →
  (Γ,Γm) ⊢ a2 : Some τ2 → m !!{Γ} a2 = Some w2 → (Γ,Γm) ⊢ g w2 : τ2 →
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
  destruct (cmap_valid_Obj Γ Γm (CMap m) (addr_index a2) w β)
    as (τ&_&?&?&_); auto; simplify_equality'.
  destruct (w !!{Γ} addr_ref Γ a1) as [w1'|] eqn:?,
    (w !!{Γ} addr_ref Γ a2) as [w2'|] eqn:?; simplify_equality'.
  assert (w1' = w2') by eauto using ctree_lookup_freeze_proper; subst.
  destruct (ctree_lookup_Some Γ Γm w τ (addr_ref Γ a2) w2') as (τ'&_&?); auto.
  assert (τ2 = ucharT%T)
    by eauto using addr_not_is_obj_type; simplify_option_equality.
  erewrite ctree_lookup_alter
    by eauto using ctree_lookup_le, ref_freeze_le_r; csimpl.
  assert (ctree_unshared (g w2))
    by eauto using ctree_lookup_byte_Forall, pbit_indetify_unshared.
  by erewrite option_guard_True, ctree_lookup_alter_byte_ne
    by eauto using ctree_alter_byte_Forall, pbit_indetify_unshared.
Qed.
Lemma cmap_singleton_freeze Γ β a malloc w :
  cmap_singleton Γ (freeze β a) malloc w = cmap_singleton Γ a malloc w.
Proof.
  unfold cmap_singleton. rewrite addr_index_freeze, addr_ref_freeze.
  destruct β.
  * by erewrite ctree_singleton_le by eauto using ref_freeze_le_l.
  * by erewrite <-ctree_singleton_le by eauto using ref_freeze_le_r.
Qed.
Lemma cmap_singleton_valid Γ Γm a malloc w τ :
  ✓ Γ → ✓{Γ} Γm → (Γ,Γm) ⊢ a : Some τ →
  index_alive Γm (addr_index a) → addr_is_obj a → addr_strict Γ a →
  (Γ,Γm) ⊢ w : τ → ¬ctree_unmapped w → ✓{Γ,Γm} (cmap_singleton Γ a malloc w).
Proof.
  intros ??????? Hperm; split_ands'; intros; simplify_map_equality'; auto.
  assert (τ = addr_type_base a) by eauto using addr_is_obj_type; subst.
  exists (addr_type_object a); split_ands; eauto using addr_typed_index,
    addr_typed_representable, ctree_singleton_typed, addr_typed_ref_typed.
  contradict Hperm; eapply Forall_impl with (∅ =); eauto using
    @sep_unmapped_empty_alt, ctree_singleton_Forall_inv, addr_typed_ref_typed.
Qed.
Lemma cmap_lookup_singleton Γ Γm a malloc w τ :
  ✓ Γ → (Γ,Γm) ⊢ a : Some τ → addr_is_obj a → addr_strict Γ a →
  cmap_singleton Γ a malloc w !!{Γ} a = Some w.
Proof.
  intros. unfold lookupE, cmap_lookup.
  rewrite option_guard_True by done; simplify_map_equality'.
  erewrite ctree_lookup_singleton by eauto using addr_typed_ref_typed; simpl.
  by rewrite decide_True by done.
Qed.
Lemma cmap_alter_singleton Γ Γm g a malloc w τ :
  ✓ Γ → (Γ,Γm) ⊢ a : Some τ → addr_is_obj a → addr_strict Γ a →
  cmap_alter Γ g a (cmap_singleton Γ a malloc w)
  = cmap_singleton Γ a malloc (g w).
Proof.
  intros; unfold cmap_singleton; f_equal'; rewrite alter_singleton; simpl.
  by erewrite decide_True, ctree_alter_singleton
    by eauto using addr_typed_ref_typed.
Qed.
End memory_map.
