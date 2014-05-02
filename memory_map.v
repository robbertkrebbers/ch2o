(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export memory_trees cmap.
Local Open Scope ctype_scope.

Section operations.
  Context `{IntEnv Ti, PtrEnv Ti}.

  Global Instance cmap_valid: Valid (env Ti) (mem Ti) := λ Γ m,
    map_Forall (λ _ w, ∃ τ,
      (Γ,Some m) ⊢ w : τ ∧ ¬ctree_empty w ∧ int_typed (size_of Γ τ) sptrT
    ) (cmap_car m).
  Global Instance cmap_lookup: LookupE (env Ti) (index * ref Ti) (mtree Ti)
    (mem Ti) := λ Γ or m, cmap_car m !! or.1 ≫= lookupE Γ (or.2).
  Definition cmap_alter (Γ : env Ti) (g : mtree Ti → mtree Ti)
      (o : index) (r : ref Ti) (m : mem Ti) : mem Ti :=
    let (m) := m in CMap $ alter (ctree_alter Γ g r) o m.

  Global Instance cmap_refine: Refine Ti (mem Ti) := λ Γ f m1 m2,
    (**i 1.) *) mem_inj_injective f ∧
    (**i 2.) *) ∀ o1 o2 r w1,
      f !! o1 = Some (o2,r) → cmap_car m1 !! o1 = Some w1 →
      ∃ w2 w2', cmap_car m2 !! o2 = Some w2 ∧ (Γ,None) ⊢ w2 : type_of w2 ∧
        w2 !!{Γ} (freeze true <$> r) = Some w2' ∧ w1 ⊑{Γ,f} w2' : type_of w1.
End operations.

Section cmap_typed.
Context `{EnvSpec Ti}.
Implicit Types Γ : env Ti.
Implicit Types m : mem Ti.
Implicit Types mm : option (mem Ti).
Implicit Types τ σ : type Ti.
Implicit Types o : index.
Implicit Types w : mtree Ti.
Implicit Types rs : ref_seg Ti.
Implicit Types r : ref Ti.
Implicit Types f : mem_inj Ti.
Implicit Types g : mtree Ti → mtree Ti.

Arguments cmap_lookup _ _ _ _ !_ !_ /.
Arguments type_of_index _ _ _ !_ _ /.
Arguments cmap_type_of_index _ !_ _ /.
Arguments type_of_object _ _ _ _ _ !_ _ _ /.
Hint Extern 0 (Separation _) => apply (_ : Separation (pbit Ti)).

Global Instance mem_index_alive_dec m o : Decision (index_alive m o).
Proof.
 refine
  match cmap_car m !! o as mo return Decision (∃ w, mo = Some w ∧ _) with
  | Some w => cast_if_not (decide (ctree_Forall (λ xb, pbit_kind xb = None) w))
  | _ => right _
  end; abstract naive_solver.
Defined.
Global Instance: MemSpec Ti (mem Ti).
Proof.
  split. intros Γ m1 m2 f o1 o2 r ? Hm ? (w1&?&Hw1).
  destruct (proj2 Hm o1 o2 r w1) as (w2&w2'&?&?&?&?); auto.
  exists w2; split; auto. contradict Hw1.
  apply (ctree_refine_Forall_inv _ Γ f w1 w2' (type_of w1));
    eauto using @ctree_lookup_Forall.
  unfold pbit_kind; by intros ??? (?&->&_).
Qed.

Lemma cmap_empty_valid Γ : ✓{Γ} (∅ : mem Ti).
Proof. by intros x o; simplify_map_equality'. Qed.
Lemma cmap_valid_weaken Γ1 Γ2 m :
  ✓ Γ1 → ✓{Γ1} m → Γ1 ⊆ Γ2 → (∀ x, ✓{Γ1,Some m} x → ✓{Γ2,Some m} x) → ✓{Γ2} m.
Proof.
  intros ? Hm ?? o w Hw. destruct (Hm o w) as (τ&?&?); auto. exists τ.
  erewrite <-size_of_weaken by eauto using ctree_typed_type_valid.
  eauto using ctree_typed_weaken.
Qed.
Lemma cmap_valid_sep_valid Γ m :
  (∀ x, ✓{Γ,Some m} x → sep_valid x) → ✓{Γ} m → sep_valid m.
Proof.
  intros ? Hm; destruct m as [m]; simpl in *. intros o w ?.
  destruct (Hm o w) as (?&?&?&?); eauto using ctree_typed_sep_valid.
Qed.
Lemma type_of_index_valid Γ m o τ : ✓{Γ} m → type_of_index m o = Some τ → ✓{Γ} τ.
Proof.
  destruct m as [m]; simpl; intros Hm Hτ.
  destruct (m !! o) as [w|] eqn:Hw; simplify_equality.
  destruct (Hm o w) as (τ&?&_); auto. erewrite type_of_correct by eauto.
  eauto using ctree_typed_type_valid.
Qed.
Lemma type_of_index_representable Γ m o τ :
  ✓{Γ} m → type_of_index m o = Some τ → int_typed (size_of Γ τ) sptrT.
Proof.
  destruct m as [m]; unfold type_of_index; simpl; intros Hm Hτ.
  destruct (m !! o) as [w|] eqn:Hw; simplify_equality.
  destruct (Hm o w) as (τ&?&_&?); auto. by erewrite type_of_correct by eauto.
Qed.
Lemma type_of_object_representable Γ m o r σ :
  ✓Γ → ✓{Γ} m → type_of_object Γ m o r = Some σ →
  int_typed (size_of Γ σ * ref_size r) sptrT.
Proof.
  unfold type_of_object. intros. split.
  { transitivity 0; auto using int_lower_nonpos with zpos. }
  destruct (type_of_index m o) as [τ|] eqn:Hτ; simplify_equality'.
  destruct (type_of_index_representable Γ m o τ); auto.
  apply Z.le_lt_trans with (size_of Γ τ); auto.
  rewrite <-Nat2Z.inj_mul, <-Nat2Z.inj_le.
  apply size_of_ref; auto. by apply path_type_check_sound.
Qed.

Lemma cmap_lookup_nil Γ m o : m !!{Γ} (o,[]) = cmap_car m !! o.
Proof. unfold lookupE, cmap_lookup; simpl. by destruct (_ !! _). Qed.
Lemma cmap_lookup_app Γ m o r1 r2 :
  m !!{Γ} (o,r1 ++ r2) = m !!{Γ} (o,r2) ≫= lookupE Γ r1.
Proof.
  unfold lookupE, cmap_lookup; simpl.
  destruct (cmap_car m !! o); simpl; by rewrite ?list_path_lookup_app.
Qed.
Lemma cmap_lookup_unfreeze Γ m o r w :
  m !!{Γ} (o,r) = Some w → m !!{Γ} (o,freeze false <$> r) = Some w.
Proof.
  unfold lookupE, cmap_lookup; intros; simplify_option_equality.
  eauto using ctree_lookup_unfreeze.
Qed.
Lemma cmap_lookup_typed Γ m o r w :
  ✓ Γ → ✓{Γ} m → m !!{Γ} (o,r) = Some w → ∃ σ,
  type_of_object Γ m o r = Some σ ∧ (Γ,Some m) ⊢ w : σ.
Proof.
  destruct m as [m]; simpl; intros ? Hm ?.
  destruct (m !! o) as [w'|] eqn:Hw; simplify_equality'.
  destruct (Hm o w' Hw) as (τ&Hoτ&_); simplify_equality'.
  destruct (ctree_lookup_Some Γ (Some (CMap m)) w' τ r w) as (σ&?&?); auto.
  exists σ; split; eauto; simplify_type_equality.
  by apply path_type_check_complete.
Qed.
Lemma cmap_lookup_disjoint Γ m1 m2 o r w1 w2 :
  ✓ Γ → ✓{Γ} m1 → ✓{Γ} m2 → m1 ⊥ m2 →
  m1 !!{Γ} (o,r) = Some w1 → m2 !!{Γ} (o,r) = Some w2 → w1 ⊥ w2.
Proof.
  destruct m1 as [m1], m2 as [m2].
  intros ? Hm1 Hm2 Hm ??; simpl in *. specialize (Hm o).
  destruct (m1 !! o) as [w1'|] eqn:Hw1; simplify_equality'.
  destruct (m2 !! o) as [w2'|] eqn:Hw2; simplify_equality'.
  destruct (Hm1 o w1') as (τ1&?&_), (Hm2 o w2') as (τ2&?&_), Hm as [? _]; auto.
  assert (τ1 = τ2) by eauto using ctree_disjoint_typed; subst.
  eauto using ctree_lookup_disjoint.
Qed.
Lemma cmap_lookup_subseteq Γ m1 m2 o r w1 w2 :
  ✓ Γ → m1 ⊆ m2 → m1 !!{Γ} (o,r) = Some w1 → ¬ctree_Forall sep_unmapped w1 →
  ∃ w2, m2 !!{Γ} (o,r) = Some w2 → w1 ⊆ w2.
Proof.
  destruct m1 as [m1], m2 as [m2].
  intros ? Hm ??; simpl in *. specialize (Hm o).
  destruct (m1 !! o) as [w1'|] eqn:Hw1; simplify_equality'.
  destruct (m2 !! o) as [w2'|] eqn:Hw2; simplify_equality'; [|done].
  destruct (ctree_lookup_subseteq Γ w1' w2' r w1); naive_solver.
Qed.

Lemma cmap_alter_type_of_index Γ m g o1 o2 r :
  (∀ w', type_of (g w') = type_of w') →
  type_of_index (cmap_alter Γ g o1 r m) o2 = type_of_index m o2.
Proof.
  destruct m as [m]; simpl. intros Hg.
  destruct (decide (o1 = o2)); simplify_map_equality'; auto.
  destruct (m !! o2); f_equal'; auto using ctree_alter_type_of.
Qed.
Lemma cmap_alter_type_of_index_weak Γ m g o r w o' :
  ✓ Γ → ✓{Γ} m → m !!{Γ} (o,r) = Some w → type_of (g w) = type_of w →
  type_of_index (cmap_alter Γ g o r m) o' = type_of_index m o'.
Proof.
  destruct m as [m]; simpl. intros HΓ Hm ? Hg.
  destruct (decide (o = o')); simplify_map_equality'; auto.
  destruct (m !! o') as [w'|] eqn:?; simplify_equality'; f_equal.
  destruct (Hm o' w') as (?&?&?&?); simplify_type_equality';
    eauto using ctree_alter_type_of_weak.
Qed.
Lemma cmap_alter_valid Γ m g o r w :
  ✓ Γ → (∀ m1 m2 x,
    (∀ o' τ', type_of_index m1 o' = Some τ' → type_of_index m2 o' = Some τ') →
    ✓{Γ,Some m1} x → ✓{Γ,Some m2} x) →
  ✓{Γ} m → m !!{Γ} (o,r) = Some w →
  (Γ, Some m) ⊢ g w : type_of w → ¬ctree_unmapped (g w) →
  ✓{Γ} (cmap_alter Γ g o r m).
Proof.
  intros ? Hx Hm Hw ??. assert (∀ w', ctree_empty w' → ctree_unmapped w').
  { intros w'. rewrite <-!ctree_flatten_Forall.
    eauto using Forall_impl, @sep_unmapped_empty_alt. }
  assert (∀ x, ✓{Γ,Some m} x → ✓{Γ,Some (cmap_alter Γ g o r m)} x).
  { intros x. apply Hx; clear x. intros o' τ' ?.
    by erewrite cmap_alter_type_of_index_weak by eauto using type_of_correct. }
  destruct m as [m]; simpl in *; intros o' w' Hw'.
  destruct (m !! o) as [w''|]eqn:Hw''; simplify_equality'.
  destruct (decide (o = o')); simplify_map_equality'; simplify_option_equality.
  * destruct (Hm o' w'' Hw'') as (τ&?&Hemp&?); exists τ.
    split_ands; eauto using ctree_alter_lookup_Forall.
    apply (ctree_typed_weaken_aux Γ _ (Some (CMap m)));
      eauto using ctree_alter_typed.
  * destruct (Hm o' w' Hw') as (τ&?&?&?); exists τ.
    split_ands; auto. apply (ctree_typed_weaken_aux Γ _ (Some (CMap m))); eauto.
Qed.
Lemma cmap_alter_freeze Γ q g m o r :
  cmap_alter Γ g o (freeze q <$> r) m = cmap_alter Γ g o r m.
Proof. destruct m as [m]; f_equal'. by rewrite ctree_alter_freeze. Qed.
Lemma cmap_alter_compose Γ g1 g2 m o r :
  cmap_alter Γ (g1 ∘ g2) o r m = cmap_alter Γ g1 o r (cmap_alter Γ g2 o r m).
Proof.
  destruct m as [m]; f_equal'. rewrite <-alter_compose.
  apply alter_ext; intros; by apply ctree_alter_compose.
Qed.
Lemma cmap_alter_commute Γ g1 g2 m o1 o2 r1 r2 :
  o1 ≠ o2 → cmap_alter Γ g1 o1 r1 (cmap_alter Γ g2 o2 r2 m)
  = cmap_alter Γ g2 o2 r2 (cmap_alter Γ g1 o1 r1 m).
Proof. destruct m as [m]; intros ?; simpl. by rewrite alter_commute. Qed.
Lemma cmap_alter_commute_disjoint Γ g1 g2 m o r1 r2 :
  r1 ⊥ r2 → cmap_alter Γ g1 o r1 (cmap_alter Γ g2 o r2 m)
  = cmap_alter Γ g2 o r2 (cmap_alter Γ g1 o r1 m).
Proof.
  intros. destruct m as [m]; f_equal'. rewrite <-!alter_compose.
  apply alter_ext; simpl; auto using ctree_alter_commute.
Qed.
Lemma cmap_alter_ext_typed Γ m g1 g2 o i r σ :
  ✓ Γ → ✓{Γ} m → type_of_object Γ m o r = Some σ →
  (∀ w, (Γ, Some m) ⊢ w : σ → g1 w = g2 w) →
  cmap_alter Γ g1 o (ref_set_offset i r) m
  = cmap_alter Γ g2 o (ref_set_offset i r) m.
Proof.
  intros ? Hm ??. destruct m as [m]; f_equal'. apply alter_ext; intros w Hw.
  destruct (Hm o w Hw) as (τ&?&?&?);
    simplify_option_equality; simplify_type_equality.
  eapply ctree_alter_ext_typed; eauto. by apply path_type_check_sound.
Qed.
Lemma cmap_lookup_alter_ne Γ g m o1 o2 r1 r2 :
  o1 ≠ o2 → cmap_alter Γ g o1 r1 m !!{Γ} (o2,r2) = m !!{Γ} (o2,r2).
Proof. by destruct m as [m]; intros ?; simplify_map_equality'. Qed.
Lemma cmap_lookup_alter_disjoint Γ g m o r1 r2 w :
  ✓ Γ → r1 ⊥ r2 →
  m !!{Γ} (o,r2) = Some w → cmap_alter Γ g o r1 m !!{Γ} (o,r2) = Some w.
Proof.
  destruct m as [m]; intros; simplify_map_equality'; simplify_option_equality.
  eauto using ctree_lookup_alter_disjoint.
Qed.
Lemma cmap_lookup_alter Γ g m o r1 r2 r3 w :
  ✓ Γ → m !!{Γ} (o,freeze false <$> r2) = Some w →
  freeze true <$> r1 = freeze true <$> r2 →
  cmap_alter Γ g o (r3 ++ r1) m !!{Γ} (o,r2) = Some (ctree_alter Γ g r3 w).
Proof.
  destruct m as [m]; intros; simplify_map_equality'; simplify_option_equality.
  by erewrite ctree_alter_app, ctree_lookup_alter by eauto.
Qed.
Lemma cmap_lookup_alter_nil Γ g m o r :
  cmap_alter Γ g o r m !!{Γ} (o,[]) = ctree_alter Γ g r <$> m !!{Γ} (o,[]).
Proof.
  destruct m as [m]; intros; simplify_map_equality'. by destruct (m !! _).
Qed.
Lemma cmap_alter_disjoint Γ m1 m2 g o r w1 :
  ✓ Γ → ✓{Γ} m1 → m1 ⊥ m2 → m1 !!{Γ} (o,r) = Some w1 → ¬ctree_unmapped (g w1) →
  (∀ w2, w1 ⊥ w2 → g w1 ⊥ w2) → cmap_alter Γ g o r m1 ⊥ m2.
Proof.
  assert (∀ w', ctree_empty w' → ctree_unmapped w').
  { intros w'. rewrite <-!ctree_flatten_Forall.
    eauto using Forall_impl, @sep_unmapped_empty_alt. }
  destruct m1 as [m1], m2 as [m2]; simpl. intros ? Hm1 Hm ??? o'.
  destruct (m1 !! o) as [w1'|] eqn:Hw1; simplify_equality'.
  destruct (decide (o' = o)); simplify_map_equality'; [|apply Hm].
  specialize (Hm o). destruct (Hm1 o w1') as (τ&?&_); auto.
  destruct (m2 !! o); simplify_option_equality.
  * intuition eauto using ctree_alter_disjoint, ctree_alter_lookup_Forall.
  * assert (∃ w2', w1' ⊥ w2') as (w2'&?).
    { exists (ctree_new Γ ∅ τ); symmetry. eauto using ctree_new_disjoint. }
    intuition eauto using ctree_alter_disjoint, ctree_alter_lookup_Forall,
      @ctree_disjoint_valid_l, ctree_alter_disjoint.
Qed.
Lemma cmap_alter_union Γ m1 m2 g o r w1 :
  ✓ Γ → ✓{Γ} m1 → m1 ⊥ m2 → m1 !!{Γ} (o,r) = Some w1 → ¬ctree_unmapped (g w1) →
  (∀ w2, w1 ⊥ w2 → g w1 ⊥ w2) → (∀ w2, w1 ⊥ w2 → g (w1 ∪ w2) = g w1 ∪ w2) →
  cmap_alter Γ g o r (m1 ∪ m2) = cmap_alter Γ g o r m1 ∪ m2.
Proof.
  destruct m1 as [m1], m2 as [m2]; unfold union, sep_union; simpl.
  intros ? Hm1 Hm ????; f_equal; apply map_eq; intros o'.
  destruct (decide (o' = o)) as [->|?].
  * rewrite !lookup_union_with, !lookup_alter, lookup_union_with.
    specialize (Hm o).
    destruct (m1 !! o) as [w1'|] eqn:?, (m2 !! o); simplify_equality'; f_equal.
    destruct (Hm1 o w1') as (?&?&_); intuition eauto using ctree_alter_union.
  * by rewrite !lookup_union_with, !lookup_alter_ne, lookup_union_with by done.
Qed.
Lemma cmap_lookup_non_aliasing Γ m g s o r r1 j1 σ1 i1 r2 j2 σ2 i2 :
  let r1' := r1 ++ RUnion i1 s true :: r in
  let r2' := r2 ++ RUnion i2 s true :: r in
  ✓ Γ → ✓{Γ} m → type_of_object Γ m o r1' = Some σ1 →
  type_of_object Γ m o r2' = Some σ2 → i1 ≠ i2 →
  cmap_alter Γ g o (ref_set_offset j1 r1') m
    !!{Γ} (o,ref_set_offset j2 r2') = None.
Proof.
  simpl; intros ? Hm ???. destruct m as [m]; simplify_map_equality'.
  destruct (m !! o) as [w|] eqn:Hw; simplify_equality'.
  destruct (Hm o w Hw) as (τ&?&?&_); simplify_type_equality';
    eauto using ctree_lookup_non_aliasing, (path_type_check_sound (R:=list _)).
Qed.

(** ** Refinements *)
Lemma cmap_refine_injective Γ f m1 m2 : m1 ⊑{Γ,f} m2 → mem_inj_injective f.
Proof. by intros [??]. Qed.
Lemma cmap_lookup_refine Γ f m1 m2 o1 o2 r1 r2 w1 :
  ✓ Γ → m1 ⊑{Γ,f} m2 → f !! o1 = Some (o2,r2) → m1 !!{Γ} (o1,r1) = Some w1 →
  ∃ w2, m2 !!{Γ} (o2,r1 ++ freeze true <$> r2) = Some w2
    ∧ w1 ⊑{Γ,f} w2 : type_of w1.
Proof.
  unfold lookupE, cmap_lookup; simpl. intros ? [_ Hm] ??.
  destruct (cmap_car m1 !! o1) as [w1'|] eqn:?; simplify_equality'.
  destruct (Hm o1 o2 r2 w1') as (w2&w2'&->&?&?&?); auto; simpl.
  erewrite list_path_lookup_app by eauto; simplify_option_equality.
  eauto using ctree_lookup_refine.
Qed.
Lemma cmap_alter_refine Γ f g1 g2 m1 m2 o1 o2 r1 r2 w1 w2 :
  ✓ Γ → f !! o1 = Some (o2,r2) → m1 ⊑{Γ,f} m2 →
  m1 !!{Γ} (o1,r1) = Some w1 →
  m2 !!{Γ} (o2,r1 ++ freeze true <$> r2) = Some w2 →
  g1 w1 ⊑{Γ,f} g2 w2 : type_of w1 → ¬ctree_unmapped (g1 w1) →
  cmap_alter Γ g1 o1 r1 m1
    ⊑{Γ,f} cmap_alter Γ g2 o2 (r1 ++ freeze true <$> r2) m2.
Proof.
  destruct m1 as [m1], m2 as [m2]; simpl.
  intros ?? Hm Hw1 Hw2; split; [eauto using cmap_refine_injective|].
  intros o3 o4 r4 w3 ? Hw3; simplify_equality'.
  destruct (decide (o3 = o1)); simplify_map_equality'.
  * destruct (m1 !! o1) as [w1'|] eqn:Hw1'; simplify_equality'.
    destruct (proj2 Hm o1 o2 r2 w1')
      as (w2'&w2''&Ho2&?&?&?); auto; simplify_option_equality.
    eexists _, (ctree_alter Γ g2 r1 w2''); split_ands; eauto.
    + eapply type_of_typed with (type_of w2'), ctree_alter_typed;
        eauto using ctree_refine_Forall_inv, pbit_refine_unmapped_inv.
      rewrite list_path_lookup_app in Hw2; simplify_option_equality.
      erewrite ctree_refine_type_of_r by eauto using ctree_lookup_refine_both.
      eauto using ctree_refine_typed_r.
    + by erewrite ctree_alter_app, ctree_lookup_alter
        by eauto using ctree_lookup_unfreeze.
    + rewrite list_path_lookup_app in Hw2; simplify_option_equality.
      erewrite type_of_correct
        by eauto using ctree_alter_typed, ctree_refine_typed_l.
      eauto using ctree_alter_refine.
  * destruct (mem_inj_injective_ne f o1 o2 o3 o4 r2 r4) as [?|[??]];
      eauto using cmap_refine_injective; simplify_map_equality.
    { by apply (proj2 Hm o3). }
    destruct (m1 !! o1) as [w1'|] eqn:Hw1'; simplify_equality'.
    destruct (proj2 Hm o1 o4 r2 w1')
      as (w2''&w2'&?&?&?&?); auto; simplify_option_map_equality.
    destruct (proj2 Hm o3 o4 r4 w3)
      as (w4''&w4'&?&?&?&?); auto; simplify_option_map_equality.
    eexists _, w4'; split_ands; eauto.
    + eapply type_of_typed with (type_of w2''), ctree_alter_typed;
        eauto using ctree_refine_Forall_inv, pbit_refine_unmapped_inv.
      rewrite list_path_lookup_app in Hw2; simplify_option_equality.
      erewrite ctree_refine_type_of_r by eauto using ctree_lookup_refine_both.
      eauto using ctree_refine_typed_r.
    + by erewrite ctree_alter_app, ctree_lookup_alter_disjoint by
        (eauto; by apply ref_disjoint_freeze_l, ref_disjoint_freeze_r).
Qed.
Lemma cmap_refine_id Γ m : ✓ Γ → ✓{Γ} m → m ⊑{Γ} m.
Proof.
  intros ? Hm. split; auto using mem_inj_id_injective.
  intros ? o r w ??; simplify_equality'. destruct (Hm o w) as (τ&?&_); auto.
  exists w w; simplify_type_equality; split_ands;
    eauto using ctree_refine_id, type_of_typed, ctree_typed_weakly_typed.
Qed.
Lemma cmap_refine_compose Γ m1 m2 m3 f1 f2 :
  ✓ Γ → m1 ⊑{Γ,f1} m2 → m2 ⊑{Γ,f2} m3 → m1 ⊑{Γ,f1 ◎ f2} m3.
Proof.
  intros ? Hm12 Hm23; split; [eauto using mem_inj_compose_injective,
    cmap_refine_injective|intros o1 o3 r w1].
  rewrite lookup_mem_inj_compose_Some; intros (o2&r2&r3&?&?&->) ?.
  destruct (proj2 Hm12 o1 o2 r2 w1) as (w2&w2'&?&?&?&?); auto.
  destruct (proj2 Hm23 o2 o3 r3 w2) as (w3&w3'&->&?&?&?); auto.
  destruct (ctree_lookup_refine Γ f2 w2 w3' (type_of w2)
    (freeze true <$> r2) w2') as (w3''&?&Hw23); auto.
  erewrite ctree_refine_type_of_r in Hw23 by eauto. exists w3 w3''. 
  rewrite fmap_app, list_path_lookup_app; simplify_option_equality.
  split_ands; eauto using ctree_refine_compose.
Qed.
End cmap_typed.
