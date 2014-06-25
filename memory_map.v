(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export memory_trees cmap.
Local Open Scope ctype_scope.

Section operations.
  Context `{IntEnv Ti, PtrEnv Ti}.

  Global Instance cmap_dom: Dom (mem Ti) indexset := λ m,
    let (m) := m in dom _ m.
  Global Instance cmap_valid: Valid (env Ti) (mem Ti) := λ Γ m,
    map_Forall (λ _ w, ∃ τ,
      (Γ,m) ⊢ w : τ ∧ ¬ctree_empty w ∧ int_typed (size_of Γ τ) sptrT
    ) (cmap_car m).
  Global Instance cmap_lookup:
      LookupE (env Ti) (addr Ti) (mtree Ti) (mem Ti) := λ Γ a m,
    guard (addr_strict Γ a);
    w ← cmap_car m !! addr_index a ≫= lookupE Γ (addr_ref Γ a);
    if decide (addr_is_obj a) then Some w else
      guard (ctree_unshared w ∧ type_of a ≠ voidT); w !!{Γ} (addr_ref_byte Γ a).
  Definition cmap_alter (Γ : env Ti) (g : mtree Ti → mtree Ti)
      (a : addr Ti) (m : mem Ti) : mem Ti :=
    let (m) := m in CMap $ alter (ctree_alter Γ (λ w,
      if decide (addr_is_obj a) then g w
      else ctree_alter_byte Γ g (addr_ref_byte Γ a) w
    ) (addr_ref Γ a)) (addr_index a) m.
  Global Instance cmap_refine: RefineM Ti (mem Ti) := λ Γ f m1 m2,
    (**i 1.) *) mem_inj_injective f ∧
    (**i 2.) *) ✓{Γ} m1 ∧
    (**i 3.) *) ✓{Γ} m2 ∧
    (**i 4.) *) ∀ o1 o2 r w1,
      f !! o1 = Some (o2,r) → cmap_car m1 !! o1 = Some w1 →
      ∃ w2 w2', cmap_car m2 !! o2 = Some w2 ∧
        w2 !!{Γ} (freeze true <$> r) = Some w2' ∧
        w1 ⊑{Γ,f@m1↦m2} w2' : type_of w1.
End operations.

Section cmap_typed.
Context `{EnvSpec Ti}.
Implicit Types Γ : env Ti.
Implicit Types m : mem Ti.
Implicit Types τ σ : type Ti.
Implicit Types o : index.
Implicit Types w : mtree Ti.
Implicit Types rs : ref_seg Ti.
Implicit Types r : ref Ti.
Implicit Types a : addr Ti.
Implicit Types f : mem_inj Ti.
Implicit Types g : mtree Ti → mtree Ti.

Arguments lookupE _ _ _ _ _ _ _ !_ /.
Arguments cmap_lookup _ _ _ _ _ !_ /.
Hint Extern 0 (Separation _) => apply (_ : Separation (pbit Ti)).

Global Instance mem_index_alive_dec m o : Decision (index_alive m o).
Proof.
 refine
  match cmap_car m !! o as mo return Decision (∃ w, mo = Some w ∧ _) with
  | Some w => cast_if_not (decide (ctree_Forall (λ xb, pbit_kind xb = None) w))
  | _ => right _
  end; abstract naive_solver.
Defined.
Lemma index_typed_alt m o τ :
  m ⊢ o : τ ↔ ∃ w, cmap_car m !! o = Some w ∧ τ = type_of w.
Proof.
  change (m ⊢ o : τ) with (type_of <$> cmap_car m !! o = Some τ).
  destruct (cmap_car m !! o); naive_solver.
Qed.
Lemma cmap_empty_valid Γ : ✓{Γ} (∅ : mem Ti).
Proof. by intros x o; simplify_map_equality'. Qed.
Lemma cmap_valid_weaken Γ1 Γ2 m : ✓ Γ1 → ✓{Γ1} m → Γ1 ⊆ Γ2 → ✓{Γ2} m.
Proof.
  intros ? Hm ? o w Hw. destruct (Hm o w) as (τ&?&?); auto. exists τ.
  erewrite <-size_of_weaken by eauto using ctree_typed_type_valid.
  eauto using ctree_typed_weaken.
Qed.
Lemma cmap_valid_sep_valid Γ m : ✓{Γ} m → sep_valid m.
Proof.
  intros Hm; destruct m as [m]; simpl in *. intros o w ?.
  destruct (Hm o w) as (?&?&?&?); eauto using ctree_typed_sep_valid.
Qed.
Lemma index_typed_valid Γ m o τ : ✓{Γ} m → m ⊢ o : τ → ✓{Γ} τ.
Proof.
  rewrite index_typed_alt. destruct m as [m]; simpl; intros Hm (w&?&->).
  destruct (Hm o w) as (τ&?&_); auto; simplify_type_equality.
  eauto using ctree_typed_type_valid.
Qed.
Lemma index_typed_representable Γ m o τ :
  ✓{Γ} m → m ⊢ o : τ → int_typed (size_of Γ τ) sptrT.
Proof.
  rewrite index_typed_alt. destruct m as [m]; simpl; intros Hm (w&?&->).
  by destruct (Hm o w) as (τ&?&_&?); auto; simplify_type_equality.
Qed.
Lemma cmap_lookup_unfreeze Γ m a w :
  m !!{Γ} a = Some w → m !!{Γ} (freeze false a) = Some w.
Proof.
  destruct m as [m]; simpl; intros.
  rewrite addr_index_freeze, addr_ref_freeze, addr_ref_byte_freeze.
  case_option_guard; simplify_equality'.
  rewrite option_guard_True by auto using addr_strict_freeze_2.
  destruct (m !! addr_index a) as [w'|]; simplify_equality'.
  destruct (w' !!{Γ} addr_ref Γ a) as [w''|] eqn:?; simplify_equality'.
  erewrite ctree_lookup_unfreeze by eauto; csimpl.
  by rewrite (decide_iff _ _ _ _ (addr_is_obj_freeze _ _)), addr_type_of_freeze.
Qed.
Lemma cmap_lookup_typed Γ m a w σ :
  ✓ Γ → ✓{Γ} m → (Γ,m) ⊢ a : σ → m !!{Γ} a = Some w → (Γ,m) ⊢ w : σ.
Proof.
  destruct m as [m]; simpl; intros ? Hm Ha ?.
  case_option_guard; simplify_equality'.
  destruct (m !! addr_index a) as [w'|] eqn:Hw; simplify_equality'.
  destruct (w' !!{Γ} addr_ref Γ a) as [w''|] eqn:?; simplify_equality'.
  destruct (Hm (addr_index a) w' Hw) as (τ&Hoτ&_); simplify_equality'.
  destruct (ctree_lookup_Some Γ (CMap m) w' τ (addr_ref Γ a) w'')
    as (σ'&?&?); auto; simplify_option_equality; simplify_type_equality.
  * cut (σ = σ'); [by intros ->|].
    erewrite <-(addr_is_obj_type_base _ _ _ σ) by eauto.
    assert (∃ w, m !! addr_index a = Some w ∧ addr_type_object a = type_of w) 
     as (?&?&?) by (eapply (index_typed_alt (CMap m)), addr_typed_index; eauto).
    simplify_type_equality'.
    eauto using ref_set_offset_typed_unique, addr_typed_ref_base_typed.
  * erewrite addr_not_obj_type by intuition eauto.
    eauto using ctree_lookup_byte_typed.
Qed.
Lemma cmap_lookup_Some Γ m w a :
  ✓ Γ → ✓{Γ} m → m !!{Γ} a = Some w → (Γ,m) ⊢ w : type_of w.
Proof.
  destruct m as [m]; simpl; intros ? Hm Ha.
  case_option_guard; simplify_equality'.
  destruct (m !! addr_index a) as [w'|] eqn:Hw; simplify_equality'.
  destruct (w' !!{Γ} addr_ref Γ a) as [w''|] eqn:?; simplify_equality'.
  destruct (Hm (addr_index a) w' Hw) as (τ&Hoτ&_); simplify_equality'.
  destruct (ctree_lookup_Some Γ (CMap m) w' τ (addr_ref Γ a) w'')
    as (σ'&?&?); auto; simplify_option_equality;
    eauto using ctree_lookup_byte_typed, type_of_typed.
Qed.
Lemma cmap_lookup_disjoint Γ m1 m2 a w1 w2 :
  ✓ Γ → ✓{Γ} m1 → ✓{Γ} m2 → m1 ⊥ m2 →
  m1 !!{Γ} a = Some w1 → m2 !!{Γ} a = Some w2 → w1 ⊥ w2.
Proof.
  destruct m1 as [m1], m2 as [m2]; simpl.
  intros ? Hm1 Hm2 Hm ??. case_option_guard; simplify_equality'.
  specialize (Hm (addr_index a)).
  destruct (m1 !! addr_index a) as [w1'|] eqn:Hw1; simplify_equality'.
  destruct (m2 !! addr_index a) as [w2'|] eqn:Hw2; simplify_equality'.
  destruct (w1' !!{Γ} addr_ref Γ a) as [w1''|] eqn:?; simplify_equality'.
  destruct (w2' !!{Γ} addr_ref Γ a) as [w2''|] eqn:?; simplify_equality'.
  destruct (Hm1 (addr_index a) w1') as (τ1&?&_),
    (Hm2 (addr_index a) w2') as (τ2&?&_), Hm as [? _]; auto.
  assert (τ1 = τ2) by eauto using ctree_disjoint_typed_unique.
  simplify_option_equality;
    eauto using ctree_lookup_byte_disjoint, ctree_lookup_disjoint.
Qed.
Lemma cmap_lookup_subseteq Γ m1 m2 a w1 w2 :
  ✓ Γ → m1 ⊆ m2 → m1 !!{Γ} a = Some w1 → ¬ctree_Forall sep_unmapped w1 →
  ∃ w2, m2 !!{Γ} a = Some w2 ∧ w1 ⊆ w2.
Proof.
  destruct m1 as [m1], m2 as [m2]; simpl.
  intros ? Hm ??. case_option_guard; simplify_equality'.
  specialize (Hm (addr_index a)).
  destruct (m1 !! (addr_index a)) as [w1'|] eqn:?; simplify_equality'.
  destruct (m2 !! (addr_index a)) as [w2'|] eqn:?; simplify_equality'; [|done].
  destruct (w1' !!{Γ} addr_ref Γ a) as [w1''|] eqn:?; simplify_equality'.
  destruct (ctree_lookup_subseteq Γ w1' w2' (addr_ref Γ a) w1'')
    as (w2''&?&?); simplify_option_equality; intuition eauto using
    ctree_lookup_byte_Forall, pbit_unmapped_indetify, ctree_lookup_byte_subseteq.
  exfalso; eauto using @ctree_unshared_weaken.
Qed.
Lemma cmap_alter_index_type_check Γ m g a w o :
  ✓ Γ → ✓{Γ} m → m !!{Γ} a = Some w → type_of (g w) = type_of w →
  type_check (cmap_alter Γ g a m) o = type_check m o.
Proof.
  unfold type_check, index_type_check. destruct m as [m]; simpl. intros ? Hm ??.
  case_option_guard; simplify_equality'.
  destruct (decide (o = addr_index a)); simplify_map_equality'; auto.
  destruct (m !! addr_index a) as [w'|] eqn:?; simplify_equality'; f_equal.
  destruct (w' !!{Γ} addr_ref Γ a) as [w''|] eqn:?; simplify_equality'.
  destruct (Hm (addr_index a) w') as (τ&?&?&_); auto.
  destruct (ctree_lookup_Some Γ (CMap m) w' τ (addr_ref Γ a) w'')
    as (σ'&?&?); auto; simplify_type_equality'.
  eapply ctree_alter_type_of_weak; eauto using type_of_typed.
  simplify_option_equality; auto. apply ctree_alter_byte_type_of;
    simplify_type_equality; eauto using ctree_typed_type_valid.
Qed.
Lemma cmap_alter_index_typed Γ m g a w o σ :
  ✓ Γ → ✓{Γ} m → m !!{Γ} a = Some w → type_of (g w) = type_of w →
  m ⊢ o : σ → cmap_alter Γ g a m ⊢ o : σ.
Proof.
  intros. unfold typed, index_typed.
  by erewrite cmap_alter_index_type_check by eauto.
Qed.
Lemma cmap_alter_index_alive Γ m g a w o :
  ✓ Γ → ✓{Γ} m → m !!{Γ} a = Some w → ¬ctree_unmapped w →
  index_alive (cmap_alter Γ g a m) o → index_alive m o.
Proof.
  destruct m as [m]. intros ? Hm Hw Hunmap (w''&Hw'&Hw''); do 2 red; simpl in *.
  rewrite lookup_alter_Some in Hw'; destruct Hw' as [(<-&w'&?&->)|[??]]; eauto.
  exists w'; split; auto; clear Hw''; intros Hw'; destruct Hunmap.
  case_option_guard; simplify_map_equality'.
  destruct (w' !!{Γ} addr_ref Γ a) as [w''|] eqn:?; simplify_equality'.
  assert (ctree_unmapped w'').
  { destruct (Hm (addr_index a) w') as (τ&?&_); auto.
    destruct (ctree_lookup_Some Γ (CMap m) w' τ
      (addr_ref Γ a) w'') as (τ'&?&?); auto.
    eauto using ctree_lookup_Forall, pbit_unmapped_indetify,
      pbits_kind_None_unmapped, pbits_valid_sep_valid, ctree_flatten_valid. }
  simplify_option_equality;
    eauto using ctree_lookup_byte_Forall, pbit_unmapped_indetify.
Qed.
Lemma cmap_typed_alter_weaken Γ m g a w τ w' :
  ✓ Γ → ✓{Γ} m → m !!{Γ} a = Some w' → type_of (g w') = type_of w' →
  (Γ,m) ⊢ w : τ → (Γ,cmap_alter Γ g a m) ⊢ w : τ.
Proof. eauto using ctree_typed_weaken, cmap_alter_index_typed. Qed.
Lemma cmap_alter_valid Γ m g a w :
  ✓ Γ → ✓{Γ} m → m !!{Γ} a = Some w → (Γ,m) ⊢ g w : type_of w →
  ¬ctree_unmapped (g w) → ✓{Γ} (cmap_alter Γ g a m).
Proof.
  intros ? Hm Hw ? Hgw o w''' ?. cut (∃ τ, (Γ,m) ⊢ w''' : τ
    ∧ ¬ctree_empty w''' ∧ int_typed (size_of Γ τ) sptrT).
  { intros (τ&?&?&?); eauto 6 using cmap_typed_alter_weaken, type_of_correct. }
  destruct m as [m]; simpl in *; case_option_guard; simplify_equality'.
  destruct (m !! addr_index a) as [w'|] eqn:?; simplify_equality'.
  destruct (w' !!{Γ} addr_ref Γ a) as [w''|] eqn:?; simplify_equality'.
  destruct (decide (addr_index a = o));
    simplify_map_equality'; [|destruct (Hm o w''') as (τ&?&?&?); eauto].
  destruct (Hm (addr_index a) w') as (τ&?&Hemp&?); auto.
  exists τ; simplify_option_equality.
  { intuition eauto using ctree_alter_lookup_Forall,
      ctree_alter_typed, @ctree_empty_unmapped. }
  destruct (ctree_lookup_Some Γ (CMap m) w' τ
    (addr_ref Γ a) w'') as (τ'&?&?); auto.
  assert ((Γ,CMap m) ⊢ w : ucharT)
    by eauto using ctree_lookup_byte_typed; simplify_type_equality.
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
  apply alter_ext; intros; apply ctree_alter_ext; intros.
  by rewrite (decide_iff _ _ _ _ (addr_is_obj_freeze q a)).
Qed.
Lemma cmap_alter_commute Γ g1 g2 m a1 a2 w1 w2 τ1 τ2 :
  ✓ Γ → ✓{Γ} m → a1 ⊥{Γ} a2 → 
  (Γ,m) ⊢ a1 : τ1 → m !!{Γ} a1 = Some w1 → (Γ,m) ⊢ g1 w1 : τ1 →
  (Γ,m) ⊢ a2 : τ2 → m !!{Γ} a2 = Some w2 → (Γ,m) ⊢ g2 w2 : τ2 →
  cmap_alter Γ g1 a1 (cmap_alter Γ g2 a2 m)
  = cmap_alter Γ g2 a2 (cmap_alter Γ g1 a1 m).
Proof.
  destruct m as [m]; simpl;
    intros ? Hm [?|[[-> ?]|(->&Ha&?&?&?)]] ? Hw1 ?? Hw2?; f_equal.
  { by rewrite alter_commute. }
  { rewrite <-!alter_compose.
    apply alter_ext; simpl; auto using ctree_alter_commute. }
  rewrite <-!alter_compose. apply alter_ext; intros w Hw; simplify_type_equality'.
  repeat case_option_guard; simplify_equality'.
  rewrite Hw in Hw1, Hw2; simplify_equality'.
  rewrite <-!(ctree_alter_freeze _ true _ (addr_ref Γ a1)), !Ha,
    !ctree_alter_freeze, <-!ctree_alter_compose.
  destruct (w !!{Γ} addr_ref Γ a1) as [w1'|] eqn:Hw1',
    (w !!{Γ} addr_ref Γ a2) as [w2'|] eqn:Hw2'; simplify_option_equality.
  assert (τ1 = ucharT) by intuition eauto using addr_not_obj_type.
  assert (τ2 = ucharT) by intuition eauto using addr_not_obj_type.
  destruct (Hm (addr_index a2) w) as (τ&?&_); auto.
  assert (w1' = w2') by eauto using ctree_lookup_freeze_proper; subst.
  destruct (ctree_lookup_Some Γ (CMap m) w τ
    (addr_ref Γ a2) w2') as (τ'&_&?); auto.
  eapply ctree_alter_ext_lookup; simpl; eauto using ctree_alter_byte_commute.
Qed.
(** We need [addr_is_obj a] because padding bytes are ignored *)
Lemma cmap_lookup_alter Γ g m a w :
  ✓ Γ → ✓{Γ} m → addr_is_obj a → m !!{Γ} a = Some w →
  cmap_alter Γ g a m !!{Γ} a = Some (g w).
Proof.
  destruct m as [m]; simpl; intros. case_option_guard; simplify_map_equality'.
  destruct (m !! addr_index a) as [w'|] eqn:?; simplify_equality'.
  destruct (w' !!{Γ} addr_ref Γ a) as [w''|] eqn:?; simplify_equality'.
  erewrite ctree_lookup_alter by eauto using ctree_lookup_unfreeze; simpl.
  by case_decide; simplify_equality'.
Qed.
Lemma cmap_lookup_alter_not_obj Γ g m a w τ :
  ✓ Γ → ✓{Γ} m → ¬addr_is_obj a →
  (Γ,m) ⊢ a : τ → m !!{Γ} a = Some w → (Γ,m) ⊢ g w : τ → ctree_unshared (g w) →
  cmap_alter Γ g a m !!{Γ} a =
  Some (ctree_lookup_byte_after Γ (addr_type_base a) (addr_ref_byte Γ a) (g w)).
Proof.
  destruct m as [m]; simpl; intros ? Hm ?????.
  case_option_guard; simplify_map_equality'.
  assert (type_of <$> m !! addr_index a = Some (addr_type_object a)).
  { by refine (addr_typed_index Γ (CMap m) a τ _). }
  assert (Γ ⊢ addr_ref Γ a : addr_type_object a ↣ addr_type_base a).
  { eapply addr_typed_ref_typed; eauto. }
  destruct (m !! addr_index a) as [w'|] eqn:?; simplify_equality'.
  destruct (Hm (addr_index a) w') as (τ'&?&_); auto.
  destruct (w' !!{Γ} addr_ref Γ a) as [w''|] eqn:?; simplify_equality'.
  destruct (ctree_lookup_Some Γ (CMap m)
    w' τ' (addr_ref Γ a) w'') as (τ''&?&?); auto; simplify_type_equality.
  erewrite ctree_lookup_alter by eauto using ctree_lookup_unfreeze; simpl.
  case_decide; [done|]; case_option_guard; simplify_equality'.
  assert (τ = ucharT) by (intuition eauto using addr_not_obj_type); subst.
  erewrite option_guard_True, ctree_lookup_alter_byte
    by intuition eauto using ctree_alter_byte_Forall, pbit_indetify_unshared.
  by simplify_option_equality.
Qed.
Lemma cmap_lookup_alter_disjoint Γ g m a1 a2 w1 w2 τ2 :
  ✓ Γ → ✓{Γ} m → a1 ⊥{Γ} a2 → m !!{Γ} a1 = Some w1 →
  (Γ,m) ⊢ a2 : τ2 → m !!{Γ} a2 = Some w2 → (Γ,m) ⊢ g w2 : τ2 →
  (ctree_unshared w2 → ctree_unshared (g w2)) →
  cmap_alter Γ g a2 m !!{Γ} a1 = Some w1.
Proof.
  destruct m as [m]; simpl; intros ? Hm [?|[[-> ?]|(->&Ha&?&?&?)]] ?? Hw2 ??;
    simplify_map_equality; auto.
  { repeat case_option_guard; simplify_equality'; try contradiction.
    destruct (m !! _) as [w2'|]; simplify_equality'.
    destruct (w2' !!{Γ} addr_ref Γ a1) as [w1''|] eqn:?,
      (w2' !!{Γ} addr_ref Γ a2) as [w2''|] eqn:?; simplify_equality'.
    by erewrite ctree_lookup_alter_disjoint by eauto. }
  repeat case_option_guard; simplify_type_equality'; try contradiction.
  destruct (m !! _) as [w|]eqn:?; simplify_equality'.
  destruct (Hm (addr_index a2) w) as (τ&?&_); auto.
  destruct (w !!{Γ} addr_ref Γ a1) as [w1'|] eqn:?,
    (w !!{Γ} addr_ref Γ a2) as [w2'|] eqn:?; simplify_equality'.
  assert (w1' = w2') by eauto using ctree_lookup_freeze_proper; subst.
  destruct (ctree_lookup_Some Γ (CMap m)
    w τ (addr_ref Γ a2) w2') as (τ'&_&?); auto.
  simplify_option_equality.
  assert (τ2 = ucharT) by (intuition eauto using addr_not_obj_type); subst.
  erewrite ctree_lookup_alter by eauto using ctree_lookup_unfreeze; csimpl.
  assert (ctree_unshared (g w2))
    by intuition eauto using ctree_lookup_byte_Forall, pbit_indetify_unshared.
  by erewrite option_guard_True, ctree_lookup_alter_byte_ne
    by intuition eauto using ctree_alter_byte_Forall, pbit_indetify_unshared.
Qed.
Lemma cmap_alter_disjoint Γ m1 m2 g a w1 τ1 :
  ✓ Γ → ✓{Γ} m1 → m1 ⊥ m2 →
  (Γ,m1) ⊢ a : τ1 → m1 !!{Γ} a = Some w1 → (Γ,m1) ⊢ g w1 : τ1 →
  ¬ctree_unmapped (g w1) →
  (∀ w2, w1 ⊥ w2 → g w1 ⊥ w2) → cmap_alter Γ g a m1 ⊥ m2.
Proof.
  assert (∀ w', ctree_empty w' → ctree_unmapped w').
  { eauto using Forall_impl, @sep_unmapped_empty_alt. }
  destruct m1 as [m1], m2 as [m2]; simpl. intros ? Hm1 Hm ????? o.
  specialize (Hm o). case_option_guard; simplify_type_equality'.
  destruct (decide (o = addr_index a)); simplify_map_equality'; [|apply Hm].
  destruct (m1 !! addr_index a) as [w1'|] eqn:?; simplify_equality'.
  destruct (w1' !!{Γ} addr_ref Γ a) as [w1''|] eqn:?; simplify_equality'.
  destruct (Hm1 (addr_index a) w1') as (τ&?&_); auto.
  destruct (ctree_lookup_Some Γ (CMap m1) w1' τ (addr_ref Γ a) w1'')
    as (τ'&_&?); auto.
  destruct (m2 !! addr_index a) as [w2'|] eqn:?.
  * destruct Hm as (?&?&?). case_decide; simplify_option_equality.
    { split_ands; eauto using ctree_alter_disjoint, ctree_alter_lookup_Forall. }
    assert (τ1 = ucharT) by intuition eauto using addr_not_obj_type.
    simplify_equality; split_ands; auto.
    { eapply ctree_alter_disjoint; intuition eauto
        using ctree_alter_byte_unmapped, ctree_alter_byte_disjoint. }
    intuition eauto using ctree_alter_byte_unmapped, ctree_alter_lookup_Forall.
  * assert (∃ w2', w1' ⊥ w2') as (w2'&?).
    { exists (ctree_new Γ ∅ τ); symmetry. eauto using ctree_new_disjoint. }
    destruct Hm. case_decide; simplify_option_equality.
    { intuition eauto using ctree_alter_disjoint, ctree_alter_lookup_Forall,
        @ctree_disjoint_valid_l, ctree_alter_disjoint. }
    assert (τ1 = ucharT) by intuition eauto using addr_not_obj_type.
    simplify_equality. split.
    { eapply ctree_disjoint_valid_l, ctree_alter_disjoint; intuition eauto
        using ctree_alter_byte_disjoint, ctree_alter_byte_unmapped. }
    intuition eauto using ctree_alter_byte_unmapped, ctree_alter_lookup_Forall.
Qed.
Lemma cmap_alter_union Γ m1 m2 g a w1 τ1 :
  ✓ Γ → ✓{Γ} m1 → m1 ⊥ m2 →
  (Γ,m1) ⊢ a : τ1 → m1 !!{Γ} a = Some w1 → (Γ,m1) ⊢ g w1 : τ1 →
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
  destruct (m1 !! addr_index a) as [w1'|] eqn:?,
    (m2 !! addr_index a); simplify_equality'; f_equal.
  destruct (w1' !!{Γ} addr_ref Γ a) as [w1''|] eqn:?; simplify_equality'.
  destruct (Hm1 (addr_index a) w1') as (τ&?&_); auto.
  destruct (ctree_lookup_Some Γ (CMap m1)
    w1' τ (addr_ref Γ a) w1'') as (τ'&_&?); auto.
  destruct Hm as (?&?&?). case_decide; simplify_option_equality.
  { eauto using ctree_alter_union. }
  assert (τ1 = ucharT) by intuition eauto using addr_not_obj_type.
  simplify_equality. eapply ctree_alter_union; intuition eauto using
   ctree_alter_byte_disjoint, ctree_alter_byte_union, ctree_alter_byte_unmapped.
Qed.
Lemma cmap_non_aliasing Γ m a1 a2 σ1 σ2 :
  ✓ Γ → ✓{Γ} m → (Γ,m) ⊢ a1 : σ1 → frozen a1 → addr_is_obj a1 →
  (Γ,m) ⊢ a2 : σ2 → frozen a2 → addr_is_obj a2 →
  (**i 1.) *) (∀ j1 j2, addr_plus Γ j1 a1 ⊥{Γ} addr_plus Γ j2 a2) ∨
  (**i 2.) *) σ1 ⊆{Γ} σ2 ∨
  (**i 3.) *) σ2 ⊆{Γ} σ1 ∨
  (**i 4.) *) ∀ g j1 j2,
    cmap_alter Γ g (addr_plus Γ j1 a1) m !!{Γ} addr_plus Γ j2 a2 = None ∧
    cmap_alter Γ g (addr_plus Γ j2 a2) m !!{Γ} addr_plus Γ j1 a1 = None.
Proof.
  intros ? Hm ??????. destruct (addr_disjoint_cases Γ m a1 a2 σ1 σ2)
    as [Ha12|[?|[?|(Hidx&s&r1'&i1&r2'&i2&r'&Ha1&Ha2&?)]]]; auto.
  do 3 right. intros g j1 j2.
  assert (∃ w, cmap_car m !! addr_index a1 = Some w
    ∧ addr_type_object a1 = type_of w) as (w&?&Hidx1).
  { eapply index_typed_alt, addr_typed_index; eauto. }
  assert (∃ w, cmap_car m !! addr_index a1 = Some w
    ∧ addr_type_object a2 = type_of w) as (?&?&?); simplify_equality'.
  { rewrite Hidx. eapply index_typed_alt, addr_typed_index; eauto. }
  destruct m as [m]; unfold insertE, cmap_alter, lookupE, cmap_lookup;
    simpl in *; rewrite !addr_index_plus, <-!Hidx; simplify_map_equality'.
  destruct (Hm (addr_index a1) w) as (?&?&_&_); auto; simplify_type_equality'.
  assert (Γ ⊢ r1' ++ RUnion i1 s true :: r' :
    addr_type_object a2 ↣ addr_type_base a1).
  { rewrite <-Ha1, <-Hidx1. eauto using addr_typed_ref_base_typed. }
  assert (Γ ⊢ r2' ++ RUnion i2 s true :: r' :
    addr_type_object a2 ↣ addr_type_base a2).
  { rewrite <-Ha2. eauto using addr_typed_ref_base_typed. }
  unfold addr_ref; rewrite !addr_ref_base_plus, Ha1, Ha2.
  by split; case_option_guard; simplify_equality;
    erewrite ?ctree_lookup_non_aliasing by eauto.
Qed.

(** ** Refinements *)
Lemma cmap_refine_index_typed Γ m1 m2 f o1 o2 r τ :
  ✓ Γ → m1 ⊑{Γ,f} m2 → f !! o1 = Some (o2,r) →
  m1 ⊢ o1 : τ → ∃ τ', m2 ⊢ o2 : τ' ∧ Γ ⊢ r : τ' ↣ τ.
Proof.
  unfold typed, index_typed, type_check, index_type_check.
  intros ? (_&_&Hm2&Hm) ??; simplify_equality'.
  destruct (cmap_car m1 !! o1) as [w1|] eqn:?; simplify_equality'.
  destruct (Hm o1 o2 r w1) as (w2&w2'&Ho2&?&?); auto; rewrite Ho2; simpl.
  destruct (Hm2 o2 w2) as (τ2&?&_); auto.
  erewrite <-(ctree_refine_type_of_r _ _ _ _ w1 w2' (type_of w1)) by eauto.
  destruct (ctree_lookup_Some Γ m2 w2 τ2
    (freeze true <$> r) w2') as (τ2'&?&?); auto; simplify_type_equality'.
  eauto using ref_typed_freeze_1.
Qed.
Lemma cmap_refine_alive Γ m1 m2 f o1 o2 r :
  ✓ Γ → m1 ⊑{Γ,f} m2 → f !! o1 = Some (o2,r) →
  index_alive m1 o1 → index_alive m2 o2.
Proof.
  intros ? (_&_&_&Hm) ? (w1&?&Hw1).
  destruct (Hm o1 o2 r w1) as (w2&w2'&?&?&?); auto.
  exists w2; split; auto. contradict Hw1.
  apply (ctree_refine_Forall_inv _ Γ f m1 m2 w1 w2'
    (type_of w1)); eauto using @ctree_lookup_Forall, pbit_refine_kind_rev.
Qed.
Lemma cmap_refine_injective Γ f m1 m2 : m1 ⊑{Γ,f} m2 → mem_inj_injective f.
Proof. by intros [??]. Qed.
Lemma cmap_refine_valid_l Γ f m1 m2 : m1 ⊑{Γ,f} m2 → ✓{Γ} m1.
Proof. by intros (?&?&?&?). Qed.
Lemma cmap_refine_valid_r Γ f m1 m2 : m1 ⊑{Γ,f} m2 → ✓{Γ} m2.
Proof. by intros (?&?&?&?). Qed.
Hint Immediate cmap_refine_valid_l cmap_refine_valid_r.
Lemma cmap_refine_id Γ m : ✓ Γ → ✓{Γ} m → m ⊑{Γ} m.
Proof.
  destruct m as [m]; intros ? Hm.
  split; split_ands; auto using mem_inj_id_injective.
  intros ? o r w ??; simplify_equality'. destruct (Hm o w) as (τ&?&_); auto.
  exists w w; simplify_type_equality; eauto using ctree_refine_id, type_of_typed.
Qed.
Lemma cmap_refine_compose Γ f1 f2 m1 m2 m3 :
  ✓ Γ → m1 ⊑{Γ,f1} m2 → m2 ⊑{Γ,f2} m3 → m1 ⊑{Γ,f1 ◎ f2} m3.
Proof.
  intros ? (?&?&?&Hm12) (?&_&?&Hm23); split; split_ands;
    eauto 2 using mem_inj_compose_injective, cmap_refine_injective.
  intros o1 o3 r w1.
  rewrite lookup_mem_inj_compose_Some; intros (o2&r2&r3&?&?&->) ?.
  destruct (Hm12 o1 o2 r2 w1) as (w2&w2'&?&?&?); auto.
  destruct (Hm23 o2 o3 r3 w2) as (w3&w3'&->&?&?); auto.
  destruct (ctree_lookup_refine Γ f2 m2 m3 w2 w3' (type_of w2)
    (freeze true <$> r2) w2') as (w3''&?&Hw23); auto.
  erewrite ctree_refine_type_of_r in Hw23 by eauto. exists w3 w3''.
  rewrite fmap_app, ctree_lookup_app; simplify_option_equality.
  split_ands; eauto using ctree_refine_compose.
Qed.
Lemma cmap_lookup_refine Γ f m1 m2 a1 a2 w1 τ :
  ✓ Γ → m1 ⊑{Γ,f} m2 → a1 ⊑{Γ,f@m1↦m2} a2 : τ → m1 !!{Γ} a1 = Some w1 →
  ∃ w2, m2 !!{Γ} a2 = Some w2 ∧ w1 ⊑{Γ,f@m1↦m2} w2 : τ.
Proof.
  destruct m1 as [m1], m2 as [m2]; simpl; intros ? (_&_&_&Hm) Ha ?.
  assert ((Γ,CMap m1) ⊢ a1 : τ) by eauto using addr_refine_typed_l.
  assert ((Γ,CMap m2) ⊢ a2 : τ) by eauto using addr_refine_typed_r.
  case_option_guard; simplify_type_equality'.
  rewrite option_guard_True by eauto using addr_strict_refine.
  destruct (m1 !! addr_index a1) as [w1'|] eqn:?; simplify_equality'.
  destruct (w1' !!{Γ} addr_ref Γ a1) as [w1''|] eqn:?; simplify_equality'.
  destruct (addr_ref_refine Γ f (CMap m1) (CMap m2) a1 a2 τ) as (r&?&->); auto.
  destruct (Hm (addr_index a1) (addr_index a2) r w1')
    as (w2&w2'&->&Hr&?); auto; csimpl.
  destruct (ctree_lookup_Some Γ (CMap m1) w1' (type_of w1')
    (addr_ref Γ a1) w1'') as (σ'&?&?); eauto using ctree_refine_typed_l.
  rewrite ctree_lookup_app, Hr; csimpl.
  destruct (ctree_lookup_refine Γ f (CMap m1) (CMap m2) w1' w2' (type_of w1')
    (addr_ref Γ a1) w1'') as (w2''&->&?); auto; csimpl.
  rewrite <-(decide_iff _ _ _ _ (addr_is_obj_refine _ _ _ _ _ _ _ Ha));
    case_decide; simplify_equality'.
  { cut (τ = type_of w1); [intros ->; eauto|].
    erewrite <-(addr_is_obj_type_base _ _ a1 τ) by eauto.
    assert (∃ w, m1 !! addr_index a1 = Some w ∧ addr_type_object a1 = type_of w) 
      as (?&?&Hidx) by (eapply (index_typed_alt (CMap m1)),
      addr_typed_index, addr_refine_typed_l; eauto); simplify_type_equality'.
    eapply ref_set_offset_typed_unique; eauto.
    rewrite <-Hidx; eauto using addr_typed_ref_base_typed, addr_refine_typed_l. }
  case_option_guard; simplify_equality'; rewrite option_guard_True
    by intuition eauto using ctree_refine_Forall, pbit_refine_unshared.
  assert (τ = ucharT) by (intuition eauto using
    addr_not_obj_type, addr_refine_typed_l); subst.
  erewrite <-addr_ref_byte_refine by eauto. eauto using ctree_lookup_byte_refine.
Qed.
Lemma cmap_alter_refine Γ f g1 g2 m1 m2 a1 a2 w1 w2 τ :
  ✓ Γ → m1 ⊑{Γ,f} m2 → a1 ⊑{Γ,f@m1↦m2} a2 : τ →
  m1 !!{Γ} a1 = Some w1 → m2 !!{Γ} a2 = Some w2 → ¬ctree_unmapped w1 →
  g1 w1 ⊑{Γ,f@m1↦m2} g2 w2 : τ → ¬ctree_unmapped (g1 w1) →
  cmap_alter Γ g1 a1 m1 ⊑{Γ,f} cmap_alter Γ g2 a2 m2.
Proof.
  intros ? (?&Hm1&Hm2&Hm) Ha Hw1 Hw2 ?? Hgw.
  assert ((Γ,m1) ⊢ a1 : τ) by eauto using addr_refine_typed_l.
  assert ((Γ,m2) ⊢ a2 : τ) by eauto using addr_refine_typed_r.
  assert ((Γ,m1) ⊢ w1 : τ) by eauto using cmap_lookup_typed.
  assert ((Γ,m2) ⊢ w2 : τ) by eauto using cmap_lookup_typed.
  split; split_ands.
  { eauto 2 using cmap_refine_injective. }
  { eapply cmap_alter_valid; eauto; simplify_type_equality;
      eauto using ctree_refine_typed_l. }
  { eapply cmap_alter_valid; eauto; simplify_type_equality; eauto using
      ctree_refine_typed_r, ctree_refine_Forall_inv, pbit_refine_unmapped_inv. }
  cut (∀ o3 o4 r4 w3, f !! o3 = Some (o4, r4) →
    cmap_car (cmap_alter Γ g1 a1 m1) !! o3 = Some w3 → ∃ τ' w4 w4',
    cmap_car (cmap_alter Γ g2 a2 m2) !! o4 = Some w4 ∧
    w4 !!{Γ} (freeze true<$>r4) = Some w4' ∧ w3 ⊑{Γ,f@m1↦m2} w4' : τ').
  { intros help o3 o4 r4 w3 ? Hw3.
    destruct (help o3 o4 r4 w3) as (τ'&w4&w4'&?&?&?); auto.
    exists w4 w4'; split_ands; auto. erewrite ctree_refine_type_of_l by eauto.
    eapply (ctree_refine_weaken _ _ _ _ m1 m2); eauto 1.
    * intros. eapply cmap_alter_index_typed; eauto.
      by erewrite ctree_refine_type_of_l, type_of_correct by eauto.
    * intros. eapply cmap_alter_index_typed; eauto.
      by erewrite ctree_refine_type_of_r, type_of_correct by eauto.
    * eauto using cmap_alter_index_alive.
    * clear dependent o3 o4 r4 w3 τ' w4 w4'. intros o3 o4 r4 ? (w3&?&Hw3).
      destruct (help o3 o4 r4 w3) as (τ'&w4&w4'&?&?&?); auto.
      exists w4; split; auto; contradict Hw3.
      eapply (ctree_refine_Forall_inv _ _ _ m1 m2 _ w4');
        eauto 2 using ctree_lookup_Forall, pbit_refine_kind_rev. }
  intros o3 o4 r4 w3 ? Hw3. destruct m1 as [m1], m2 as [m2]; simpl in *.
  repeat case_option_guard; simplify_type_equality'.
  destruct (addr_ref_refine Γ f (CMap m1) (CMap m2) a1 a2 τ) as (r2&?&Hr2); auto.
  rewrite Hr2 in Hw2 |- *; clear Hr2.
  destruct (m1 !! addr_index a1) as [w1'|] eqn:?; simplify_equality'.
  destruct (m2 !! addr_index a2) as [w2'|] eqn:?; simplify_equality'.
  rewrite ctree_lookup_app in Hw2.
  destruct (w1' !!{Γ} addr_ref Γ a1) as [w1''|] eqn:?; simplify_equality'.
  destruct (decide (o3 = addr_index a1)); simplify_map_equality'.
  * destruct (Hm (addr_index a1) (addr_index a2) r2 w1') as (?&w2''&?&?&?); auto.
    destruct (ctree_lookup_refine Γ f (CMap m1) (CMap m2) w1' w2'' (type_of w1')
      (addr_ref Γ a1) w1'') as (w2'''&?&?); auto; simplify_map_equality'.
    eexists (type_of w1'), _,
      (ctree_alter Γ _ (addr_ref Γ a1) w2''); split_ands; eauto.
    { by erewrite ctree_alter_app, ctree_lookup_alter
        by eauto using ctree_lookup_unfreeze. }
    assert (addr_is_obj a1 ↔ addr_is_obj a2) by eauto using addr_is_obj_refine.
    simplify_option_equality; try tauto.
    { eapply ctree_alter_refine; eauto; simplify_type_equality; eauto. }
    assert (τ = ucharT) by (intuition eauto using addr_not_obj_type); subst.
    erewrite addr_ref_byte_refine in Hw1 |- * by eauto.
    eapply ctree_alter_refine; eauto using ctree_alter_byte_refine.
    contradict Hgw; eapply (ctree_alter_byte_unmapped _ _ _ w1'');
      eauto using ctree_alter_lookup_Forall, ctree_refine_typed_l.
  * destruct (mem_inj_injective_ne f (addr_index a1) (addr_index a2) o3 o4 r2
      r4) as [?|[??]]; eauto using cmap_refine_injective; simplify_map_equality'.
    { exists (type_of w3). by apply (Hm o3). }
    destruct (Hm o3 (addr_index a2) r4 w3)
      as (w4''&w4'&?&?&?); auto; simplify_map_equality'.
    eexists (type_of w3), _, w4'; split_ands; eauto.
    by erewrite ctree_alter_app, ctree_lookup_alter_disjoint by
      (eauto; by apply ref_disjoint_freeze_l, ref_disjoint_freeze_r).
Qed.
End cmap_typed.
