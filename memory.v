(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export values.
Local Open Scope ctype_scope.

Section memory_operations.
  Context `{IntEnv Ti, PtrEnv Ti}.

  Global Instance mem_lookup:
      LookupE (env Ti) (addr Ti) (val Ti) (mem Ti) := λ Γ a m,
    w ← m !!{Γ} a;
    guard (ctree_Forall (λ xb, Some Readable ⊆ pbit_kind xb) w);
    Some (to_val Γ w).
  Definition mem_force (Γ : env Ti) (a : addr Ti) : mem Ti → mem Ti :=
    cmap_alter Γ id a.

  Definition mem_writable (Γ : env Ti) (a : addr Ti) (m : mem Ti) : Prop :=
    ∃ w, m !!{Γ} a = Some w
         ∧ ctree_Forall (λ xb, Some Writable ⊆ pbit_kind xb) w.
  Global Instance mem_insert:
      InsertE (env Ti) (addr Ti) (val Ti) (mem Ti) := λ Γ a v,
    cmap_alter Γ (λ w, of_val Γ (tagged_perm <$> ctree_flatten w) v) a.

  Fixpoint mem_insert_array (Γ : env Ti) (a : addr Ti)
      (vs : list (val Ti)) (m : mem Ti) : mem Ti :=
    match vs with
    | [] => m
    | v :: vs => <[a:=v]{Γ}>(mem_insert_array Γ (addr_plus Γ 1 a) vs m)
    end.

  Definition is_free (o : index) (m : mem Ti) : Prop := cmap_car m !! o = None.
  Definition mem_alloc (Γ : env Ti) (o : index)
      (alloc : bool) (τ : type Ti) (m : mem Ti) : mem Ti :=
    let (m) := m in CMap (<[o:=ctree_new Γ (pbit_full alloc) τ]>m).

  Definition mem_freeable (o : index) (m : mem Ti) : Prop :=
    ∃ w, cmap_car m !! o = Some w
       ∧ ctree_Forall (λ xb, Some Freeable ⊆ pbit_kind xb) w.
  Definition mem_free (o : index) (m : mem Ti) : mem Ti :=
    let (m) := m in CMap (alter (ctree_map (λ _ : pbit Ti, pbit_freed)) o m).
End memory_operations.

Section memory.
Context `{EnvSpec Ti}.
Implicit Types Γ : env Ti.
Implicit Types τ : type Ti.
Implicit Types a : addr Ti.
Implicit Types p : ptr Ti.
Implicit Types w : mtree Ti.
Implicit Types v : val Ti.
Implicit Types m : mem Ti.

Arguments cmap_lookup _ _ _ _ !_ !_ /.
Arguments type_of_index _ _ _ !_ _ /.
Arguments cmap_type_of_index _ !_ _ /.
Arguments type_of_object _ _ _ _ _ !_ _ _ /.
Hint Extern 0 (Separation _) => apply (_ : Separation (pbit Ti)).

Ltac solve_length := repeat first
  [ rewrite take_length | rewrite drop_length | rewrite app_length
  | rewrite fmap_length | rewrite replicate_length
  | erewrite ctree_flatten_length by eauto]; lia.
Hint Extern 0 (length _ = _) => solve_length.
Hint Extern 0 (_ ≤ length _) => solve_length.
Hint Extern 0 (length _ ≤ _) => solve_length.

Hint Immediate cmap_lookup_typed.
Hint Immediate ctree_refine_typed_l.

(** ** Properties of the [alloc] function *)
Lemma mem_alloc_type_of Γ m o alloc τ :
  ✓ Γ → ✓{Γ} τ → type_of_index (mem_alloc Γ o alloc τ m) o = Some τ.
Proof.
  intros. unfold mem_alloc, type_of_index.
  destruct m as [m]; simplify_map_equality'; f_equal.
  apply (type_of_correct (Γ,∅) _), ctree_new_typed; auto using pbit_full_valid.
Qed.
Lemma mem_alloc_type_of_free Γ m o alloc τ o' τ' :
  is_free o m → type_of_index m o' = Some τ' →
  type_of_index (mem_alloc Γ o alloc τ m) o' = Some τ'.
Proof.
  unfold mem_alloc, type_of_index; destruct m as [m]; simpl; intros.
  by destruct (decide (o = o')); simplify_map_equality'.
Qed.
Lemma addr_typed_alloc Γ m o alloc τ a' τ' :
  ✓ Γ → is_free o m → (Γ,m) ⊢ a' : τ' → (Γ,mem_alloc Γ o alloc τ m) ⊢ a' : τ'.
Proof. eauto using addr_typed_weaken, mem_alloc_type_of_free. Qed.
Lemma val_typed_alloc Γ m o alloc τ v' τ' :
  ✓ Γ → is_free o m → (Γ,m) ⊢ v' : τ' → (Γ,mem_alloc Γ o alloc τ m) ⊢ v' : τ'.
Proof. eauto using val_typed_weaken, mem_alloc_type_of_free. Qed.
Lemma addr_new_typed_alloc Γ m o alloc τ a :
  ✓ Γ → ✓{Γ} τ → int_typed (size_of Γ τ) sptrT →
  (Γ,mem_alloc Γ o alloc τ m) ⊢ addr_new o τ : τ.
Proof.
  constructor; simpl; split_ands; auto using mem_alloc_type_of.
  * by apply list_typed_nil.
  * lia.
  * by apply Nat.mod_0_l, size_of_ne_0.
Qed.
Lemma mem_alloc_valid Γ o alloc m τ :
  ✓ Γ → ✓{Γ} m → is_free o m → ✓{Γ} τ → int_typed (size_of Γ τ) sptrT →
  ✓{Γ} (mem_alloc Γ o alloc τ m).
Proof.
  destruct m as [m]; intros HΓ Hm Hx Hτ Hsz o' w; simpl.
  rewrite lookup_insert_Some; intros [[-> <-]|[??]].
  { exists τ. split_ands; eauto 7 using (ctree_Forall_not _ _ (CMap m)),
     ctree_new_typed, pbit_full_valid, ctree_new_Forall. }
  destruct (Hm o' w) as (σ&?&?); eauto.
  eauto using ctree_typed_weaken, (mem_alloc_type_of_free _ (CMap m)).
Qed.

(** ** Properties of the [mem_free] fucntion *)
Lemma mem_free_type_of_index m o o' :
  type_of_index (mem_free o m) o' = type_of_index m o'.
Proof.
  unfold type_of_index; destruct m as [m]; simpl; intros.
  destruct (decide (o' = o)); simplify_map_equality; auto.
  destruct (m !! o); f_equal'; auto using ctree_map_type_of.
Qed.
Lemma addr_typed_free Γ m o a τ :
  ✓ Γ → (Γ,m) ⊢ a : τ → (Γ,mem_free o m) ⊢ a : τ.
Proof.
  intros. eapply addr_typed_weaken; eauto.
  intros. by rewrite mem_free_type_of_index.
Qed.
Lemma val_typed_free Γ m o v τ :
  ✓ Γ → (Γ,m) ⊢ v : τ → (Γ,mem_free o m) ⊢ v : τ.
Proof.
  intros. eapply val_typed_weaken; eauto.
  intros. by rewrite mem_free_type_of_index.
Qed.
Lemma mem_free_valid Γ o m : ✓ Γ → ✓{Γ} m → ✓{Γ} (mem_free o m).
Proof.
  intros HΓ Hm o' w Hw.
  cut (∃ τ, (Γ,m) ⊢ w : τ ∧ ¬ctree_empty w ∧ int_typed (size_of Γ τ) sptrT).
  { intros (τ&?&?&?); exists τ; split_ands; auto.
    eapply ctree_typed_weaken; eauto.
    intros. by rewrite mem_free_type_of_index. }
  revert Hw; destruct m as [m]; simpl.
  rewrite lookup_alter_Some; intros [(?&w'&?&->)|[??]]; [|by apply (Hm o' w)].
  destruct (Hm o' w') as (τ&?&?&?); auto.
  exists τ; split_ands; auto using ctree_map_typed, pbit_freed_valid.
  eapply ctree_Forall_not; eauto using ctree_map_typed, pbit_freed_valid.
  rewrite <-ctree_flatten_Forall, ctree_flatten_map.
  by apply Forall_fmap, Forall_true.
Qed.

(** ** Properties of the [lookup] function *)
Lemma mem_lookup_typed Γ m a v τ :
  ✓ Γ → ✓{Γ} m → m !!{Γ} a = Some v → (Γ,m) ⊢ a : τ → (Γ,m) ⊢ v : τ.
Proof.
  unfold lookupE, mem_lookup. intros ? Hm Hv Ha. destruct (m !!{Γ} a)
    as [w|] eqn:?; simplify_option_equality; eauto using to_val_typed.
Qed.
Lemma mem_lookup_frozen Γ m a v :
  ✓ Γ → ✓{Γ} m → m !!{Γ} a = Some v → val_map (freeze true) v = v.
Proof.
  unfold lookupE, mem_lookup. intros ? Hm Hv.
  destruct (m !!{Γ} a) as [w|] eqn:?; simplify_option_equality.
  destruct (cmap_lookup_Some Γ m w a); eauto using to_val_frozen.
Qed.

(** Properties of the [force] function *)
Lemma addr_typed_force Γ m a a' τ' :
  ✓ Γ → ✓{Γ} m → is_Some (m !!{Γ} a) →
  (Γ,m) ⊢ a' : τ' → (Γ,mem_force Γ a m) ⊢ a' : τ'.
Proof.
  unfold mem_force, lookupE, mem_lookup. intros ?? [v ?] ?.
  destruct (m !!{Γ} a) as [w|] eqn:?; simplify_equality'.
  eapply addr_typed_weaken; eauto.
  intros. by erewrite cmap_alter_type_of_index by eauto.
Qed.
Lemma val_typed_force Γ m a τ v' τ' :
  ✓ Γ → ✓{Γ} m → is_Some (m !!{Γ} a) →
  (Γ,m) ⊢ v' : τ' → (Γ,mem_force Γ a m) ⊢ v' : τ'.
Proof.
  unfold mem_force, lookupE, mem_lookup. intros ?? [v ?] ?.
  destruct (m !!{Γ} a) as [w|] eqn:?; simplify_equality'.
  eapply val_typed_weaken; eauto.
  intros. by erewrite cmap_alter_type_of_index by eauto.
Qed.
Lemma mem_force_valid Γ m a :
  ✓ Γ → ✓{Γ} m → is_Some (m !!{Γ} a) → ✓{Γ} (mem_force Γ a m).
Proof.
  unfold mem_force, lookupE, mem_lookup. intros ?? [v ?].
  destruct (m !!{Γ} a) as [w|] eqn:?; simplify_option_equality.
  destruct (cmap_lookup_Some Γ m w a) as [τ ?]; auto.
  eapply cmap_alter_valid; eauto; [eapply type_of_typed; eauto|].
  eapply ctree_Forall_not, ctree_flatten_Forall_1, pbits_mapped;
    eauto using ctree_flatten_Forall_2.
Qed.
Lemma mem_lookup_force Γ m a v τ :
  ✓ Γ → ✓{Γ} m → (Γ,m) ⊢ a : τ → m !!{Γ} a = Some v → addr_is_obj a →
  mem_force Γ a m !!{Γ} a = Some v.
Proof.
  unfold lookupE, mem_lookup, mem_force. intros.
  destruct (m !!{Γ} a) as [w'|] eqn:?; simplify_equality'.
  by erewrite cmap_lookup_alter by eauto; simplify_option_equality.
Qed.
Lemma mem_lookup_force_disjoint Γ m a1 a2 τ2 v1 :
  ✓ Γ → ✓{Γ} m → a1 ⊥{Γ} a2 → m !!{Γ} a1 = Some v1 →
  (Γ,m) ⊢ a2 : τ2 → is_Some (m !!{Γ} a2) → mem_force Γ a2 m !!{Γ} a1 = Some v1.
Proof.
  unfold lookupE, mem_force, mem_lookup. intros ????? [??].
  destruct (m !!{Γ} a1) as [w1|] eqn:?,
    (m !!{Γ} a2) as [w2|] eqn:?; simplify_equality'.
  by erewrite cmap_lookup_alter_disjoint by eauto.
Qed.
Lemma mem_force_commute Γ m a1 a2 τ1 τ2 :
  ✓ Γ → ✓{Γ} m → a1 ⊥{Γ} a2 →
  (Γ,m) ⊢ a1 : τ1 → is_Some (m !!{Γ} a1) →
  (Γ,m) ⊢ a2 : τ2 → is_Some (m !!{Γ} a2) →
  mem_force Γ a1 (mem_force Γ a2 m) = mem_force Γ a2 (mem_force Γ a1 m).
Proof.
  unfold lookupE, mem_lookup, mem_force. intros ???? [??] ? [??].
  destruct (m !!{Γ} a1) as [w1|] eqn:?, (m !!{Γ} a2) as [w2|] eqn:?;
    simplify_equality'; eauto using cmap_alter_commute.
Qed.
Lemma ctree_force_disjoint Γ m1 m2 a1 τ1 :
  ✓ Γ → ✓{Γ} m1 → m1 ⊥ m2 →
  (Γ,m1) ⊢ a1 : τ1 → is_Some (m1 !!{Γ} a1) → mem_force Γ a1 m1 ⊥ m2.
Proof.
  unfold lookupE, mem_lookup, mem_force. intros ???? [??].
  destruct (m1 !!{Γ} a1) as [w1|] eqn:?; simplify_option_equality.
  eapply cmap_alter_disjoint; eauto.
  eapply ctree_Forall_not, ctree_flatten_Forall_1, pbits_mapped;
    eauto using ctree_flatten_Forall_2.
Qed.
Lemma ctree_force_union Γ m1 m2 a1 v1 τ1 :
  ✓ Γ → ✓{Γ} m1 → m1 ⊥ m2 →
  (Γ,m1) ⊢ a1 : τ1 → is_Some (m1 !!{Γ} a1) →
  mem_force Γ a1 (m1 ∪ m2) =  mem_force Γ a1 m1 ∪ m2.
Proof.
  unfold lookupE, mem_lookup, mem_force. intros ???? [??].
  destruct (m1 !!{Γ} a1) as [w1|] eqn:?; simplify_option_equality.
  eapply cmap_alter_union; eauto.
  eapply ctree_Forall_not, ctree_flatten_Forall_1, pbits_mapped;
    eauto using ctree_flatten_Forall_2.
Qed.

(** Properties of the [insert] function *)
Lemma of_val_flatten_typed Γ m w v τ :
  ✓ Γ → (Γ,m) ⊢ w : τ → (Γ,m) ⊢ v : τ →
  ctree_Forall (λ xb, Some Writable ⊆ pbit_kind xb) w →
  (Γ,m) ⊢ of_val Γ (tagged_perm <$> ctree_flatten w) v : τ.
Proof.
  intros. eapply of_val_typed; eauto.
  * eauto using pbits_valid_perm_valid, ctree_flatten_valid.
  * eapply pbits_perm_mapped, pbits_mapped; eauto using pbits_kind_weaken,
      ctree_flatten_Forall_2, pbits_valid_sep_valid, ctree_flatten_valid.
Qed.
Lemma of_val_flatten_unmapped Γ m w v τ :
  ✓ Γ → (Γ,m) ⊢ w : τ → (Γ,m) ⊢ v : τ →
  ctree_Forall (λ xb, Some Writable ⊆ pbit_kind xb) w →
  ¬ctree_unmapped (of_val Γ (tagged_perm <$> ctree_flatten w) v).
Proof.
  intros. eapply ctree_Forall_not; eauto using of_val_flatten_typed.
  eapply of_val_mapped; eauto using ctree_flatten_Forall_2.
  eapply pbits_perm_mapped, pbits_mapped; eauto using pbits_kind_weaken,
    ctree_flatten_Forall_2, pbits_valid_sep_valid, ctree_flatten_valid.
Qed.
Lemma addr_typed_insert Γ m a v τ a' τ' :
  ✓ Γ → ✓{Γ} m → (Γ,m) ⊢ a : τ → mem_writable Γ a m → (Γ,m) ⊢ v : τ →
  (Γ,m) ⊢ a' : τ' → (Γ,<[a:=v]{Γ}>m) ⊢ a' : τ'.
Proof.
  unfold insertE, mem_insert, lookupE, mem_lookup. intros ??? (w&?&?) ??.
  assert ((Γ,m) ⊢ w : τ) by eauto. eapply addr_typed_weaken; eauto. intros.
  by erewrite cmap_alter_type_of_index
    by (rewrite ?of_val_type_of; simplify_type_equality; eauto).
Qed.
Lemma val_typed_insert Γ m a v τ v' τ' :
  ✓ Γ → ✓{Γ} m → (Γ,m) ⊢ a : τ → mem_writable Γ a m → (Γ,m) ⊢ v : τ →
  (Γ,m) ⊢ v' : τ' → (Γ,<[a:=v]{Γ}>m) ⊢ v' : τ'.
Proof.
  unfold insertE, mem_insert, lookupE, mem_lookup. intros ??? (w&?&?) ??.
  assert ((Γ,m) ⊢ w : τ) by eauto. eapply val_typed_weaken; eauto. intros.
  by erewrite cmap_alter_type_of_index
    by (rewrite ?of_val_type_of; simplify_type_equality; eauto).
Qed.
Lemma mem_insert_valid Γ m a v τ :
  ✓ Γ → ✓{Γ} m → (Γ,m) ⊢ a : τ → mem_writable Γ a m → (Γ,m) ⊢ v : τ →
  ✓{Γ} (<[a:=v]{Γ}>m).
Proof.
  intros ??? (w&?&?) ?. assert ((Γ,m) ⊢ w : τ) by eauto.
  eapply cmap_alter_valid; eauto; simplify_type_equality;
    eauto using of_val_flatten_typed, of_val_flatten_unmapped.
Qed.
(** We need [addr_is_obj a] because writes at padding bytes are ignored *)
Lemma mem_lookup_insert Γ m a v τ :
  ✓ Γ → ✓{Γ} m → (Γ,m) ⊢ a : τ → mem_writable Γ a m → addr_is_obj a →
  (Γ,m) ⊢ v : τ → <[a:=v]{Γ}>m !!{Γ} a = Some (val_map (freeze true) v).
Proof.
  unfold insertE, lookupE, mem_insert, mem_lookup. intros ??? (w&?&Hw) ??.
  erewrite cmap_lookup_alter by eauto using of_val_flatten_typed; simpl.
  assert (ctree_Forall (λ xb, Some Readable ⊆ pbit_kind xb)
    (of_val Γ (tagged_perm <$> ctree_flatten w) v)).
  { revert Hw. erewrite <-!ctree_flatten_Forall, ctree_flatten_of_val by eauto.
    intros Hw. generalize (val_flatten Γ v).
    induction Hw; intros [|??]; simpl; constructor; auto.
    by transitivity (Some Writable). }
  by erewrite option_guard_True, to_of_val by eauto.
Qed.
Lemma mem_lookup_insert_disjoint Γ m a1 a2 v1 v2 τ2 :
  ✓ Γ → ✓{Γ} m → a1 ⊥{Γ} a2 → m !!{Γ} a1 = Some v1 →
  (Γ,m) ⊢ a2 : τ2 → mem_writable Γ a2 m → (Γ,m) ⊢ v2 : τ2 →
  <[a2:=v2]{Γ}>m !!{Γ} a1 = Some v1.
Proof.
  unfold insertE, lookupE, mem_insert, mem_lookup. intros ????? (w2&?&Hw2) ?.
  destruct (m !!{Γ} a1) as [w1|] eqn:?; simplify_equality'.
  assert (ctree_unshared (of_val Γ (tagged_perm <$> ctree_flatten w2) v2)).
  { eapply of_val_unshared; eauto.
    * eapply pbits_perm_unshared, pbits_unshared; eauto using pbits_kind_weaken,
        ctree_flatten_Forall_2, pbits_valid_sep_valid, ctree_flatten_valid.
    * eapply pbits_perm_mapped, pbits_mapped; eauto using pbits_kind_weaken,
        ctree_flatten_Forall_2, pbits_valid_sep_valid, ctree_flatten_valid. }
  by erewrite cmap_lookup_alter_disjoint by eauto using of_val_flatten_typed.
Qed.
Lemma mem_insert_commute Γ m a1 a2 v1 v2 τ1 τ2 :
  ✓ Γ → ✓{Γ} m → a1 ⊥{Γ} a2 →
  (Γ,m) ⊢ a1 : τ1 → mem_writable Γ a1 m → (Γ,m) ⊢ v1 : τ1 →
  (Γ,m) ⊢ a2 : τ2 → mem_writable Γ a2 m → (Γ,m) ⊢ v2 : τ2 →
  <[a1:=v1]{Γ}>(<[a2:=v2]{Γ}>m) = <[a2:=v2]{Γ}>(<[a1:=v1]{Γ}>m).
Proof.
  intros ???? (?&?&?) ?? (?&?&?) ?.
  eapply cmap_alter_commute; eauto using of_val_flatten_typed.
Qed.
Lemma mem_insert_force_commute Γ m a1 a2 v1 τ1 τ2 :
  ✓ Γ → ✓{Γ} m → a1 ⊥{Γ} a2 →
  (Γ,m) ⊢ a1 : τ1 → mem_writable Γ a1 m → (Γ,m) ⊢ v1 : τ1 →
  (Γ,m) ⊢ a2 : τ2 → is_Some (m !!{Γ} a2) →
  <[a1:=v1]{Γ}>(mem_force Γ a2 m) = mem_force Γ a2 (<[a1:=v1]{Γ}>m).
Proof.
  unfold lookupE, mem_lookup, mem_force. intros ???? (?&?&?) ?? [??].
  destruct (m !!{Γ} a2) as [w2|] eqn:?; simplify_equality'.
  eapply cmap_alter_commute; eauto using of_val_flatten_typed.
Qed.
Lemma ctree_insert_disjoint Γ m1 m2 a1 v1 τ1 :
  ✓ Γ → ✓{Γ} m1 → m1 ⊥ m2 →
  (Γ,m1) ⊢ a1 : τ1 → mem_writable Γ a1 m1 → (Γ,m1) ⊢ v1 : τ1 →
  <[a1:=v1]{Γ}>m1 ⊥ m2.
Proof.
  intros ???? (w1&?&?) ?. assert (ctree_unshared w1).
  { eapply ctree_flatten_Forall, pbits_unshared; eauto using pbits_kind_weaken,
      ctree_flatten_Forall_2, pbits_valid_sep_valid, ctree_flatten_valid. }
  assert (ctree_Forall (not ∘ sep_unmapped) w1).
  { eapply ctree_flatten_Forall, pbits_mapped;
      eauto using pbits_kind_weaken, ctree_flatten_Forall_2. }
  eapply cmap_alter_disjoint; eauto using of_val_flatten_typed,
    of_val_flatten_unmapped, of_val_disjoint.
Qed.
Lemma ctree_insert_union Γ m1 m2 a1 v1 τ1 :
  ✓ Γ → ✓{Γ} m1 → m1 ⊥ m2 →
  (Γ,m1) ⊢ a1 : τ1 → mem_writable Γ a1 m1 → (Γ,m1) ⊢ v1 : τ1 →
  <[a1:=v1]{Γ}>(m1 ∪ m2) = <[a1:=v1]{Γ}>m1 ∪ m2.
Proof.
  intros ???? (w1&?&?) ?. assert (ctree_unshared w1).
  { eapply ctree_flatten_Forall, pbits_unshared; eauto using pbits_kind_weaken,
      ctree_flatten_Forall_2, pbits_valid_sep_valid, ctree_flatten_valid. }
  assert (ctree_Forall (not ∘ sep_unmapped) w1).
  { eapply ctree_flatten_Forall, pbits_mapped;
      eauto using pbits_kind_weaken, ctree_flatten_Forall_2. }
  eapply cmap_alter_union; eauto using of_val_flatten_typed,
    of_val_flatten_unmapped, of_val_disjoint, of_val_union.
Qed.

(** ** Non-aliassing results *)
Lemma mem_non_aliasing Γ m a1 a2 τ1 τ2 :
  ✓ Γ → ✓{Γ} m → (Γ,m) ⊢ a1 : τ1 → frozen a1 → addr_is_obj a1 →
  (Γ,m) ⊢ a2 : τ2 → frozen a2 → addr_is_obj a2 →
  (**i 1.) *) (∀ j1 j2, addr_plus Γ j1 a1 ⊥{Γ} addr_plus Γ j2 a2) ∨
  (**i 2.) *) τ1 ⊆{Γ} τ2 ∨
  (**i 3.) *) τ2 ⊆{Γ} τ1 ∨
  (**i 4.) *) ∀ j1 j2,
    (∀ v1, <[addr_plus Γ j1 a1:=v1]{Γ}>m !!{Γ} addr_plus Γ j2 a2 = None) ∧
    mem_force Γ (addr_plus Γ j1 a1) m !!{Γ} addr_plus Γ j2 a2 = None ∧
    (∀ v2, <[addr_plus Γ j2 a2:=v2]{Γ}>m !!{Γ} addr_plus Γ j1 a1 = None) ∧
    mem_force Γ (addr_plus Γ j2 a2) m !!{Γ} addr_plus Γ j1 a1 = None.
Proof.
  intros. destruct (cmap_non_aliasing Γ m a1 a2 τ1 τ2) as [?|[?|[?|Ha]]]; auto.
  unfold lookupE, mem_lookup, insertE, mem_insert, mem_force.
  by do 3 right; repeat split; intros;
    rewrite ?(proj1 (Ha _ _ _)), ?(proj2 (Ha _ _ _)).
Qed.

(** ** Refinements *)
Lemma mem_lookup_refine Γ f m1 m2 a1 a2 v1 τ :
  ✓ Γ → m1 ⊑{Γ,f} m2 → a1 ⊑{Γ,f@m1↦m2} a2 : τ → m1 !!{Γ} a1 = Some v1 →
  ∃ v2, m2 !!{Γ} a2 = Some v2 ∧ v1 ⊑{Γ,f@m1↦m2} v2 : τ.
Proof.
  unfold lookupE, mem_lookup. intros.
  destruct (m1 !!{Γ} a1) as [w1|] eqn:?; simplify_equality'.
  destruct (cmap_lookup_refine Γ f m1 m2 a1 a2 w1 τ) as (w2&->&?); auto.
  exists (to_val Γ w2); simplify_option_equality by eauto using
    ctree_refine_Forall, pbit_refine_kind; eauto using to_val_refine.
Qed.
Lemma mem_force_refine Γ f m1 m2 a1 a2 v1 τ :
  ✓ Γ → m1 ⊑{Γ,f} m2 → a1 ⊑{Γ,f@m1↦m2} a2 : τ → m1 !!{Γ} a1 = Some v1 →
  mem_force Γ a1 m1 ⊑{Γ,f} mem_force Γ a2 m2.
Proof.
  unfold lookupE, mem_lookup, mem_force. intros.
  destruct (m1 !!{Γ} a1) as [w1|] eqn:?; simplify_option_equality.
  destruct (cmap_lookup_refine Γ f m1 m2 a1 a2 w1 τ) as (w2&?&?); auto.
  eapply cmap_alter_refine; eauto.
  eapply ctree_Forall_not, ctree_flatten_Forall_1, pbits_mapped;
    eauto using ctree_flatten_Forall_2.
Qed.
Lemma mem_writable_refine Γ f m1 m2 a1 a2 τ :
  ✓ Γ → m1 ⊑{Γ,f} m2 → a1 ⊑{Γ,f@m1↦m2} a2 : τ →
  mem_writable Γ a1 m1 → mem_writable Γ a2 m2.
Proof.
  intros ??? (w1&?&?).
  destruct (cmap_lookup_refine Γ f m1 m2 a1 a2 w1 τ) as (w2&?&?); auto.
  exists w2; eauto using ctree_refine_Forall, pbit_refine_kind.
Qed.
Lemma mem_insert_refine Γ f m1 m2 a1 a2 v1 v2 τ :
  ✓ Γ → m1 ⊑{Γ,f} m2 → a1 ⊑{Γ,f@m1↦m2} a2 : τ → mem_writable Γ a1 m1 →
  v1 ⊑{Γ,f@m1↦m2} v2 : τ → <[a1:=v1]{Γ}>m1 ⊑{Γ,f} <[a2:=v2]{Γ}>m2.
Proof.
  intros ??? (w1&?&?) ?.
  destruct (cmap_lookup_refine Γ f m1 m2 a1 a2 w1 τ) as (w2&?&?); auto.
  eapply cmap_alter_refine;
    eauto using of_val_flatten_unmapped, val_refine_typed_l.
  erewrite <-(pbits_refine_perm _ _ _ _ (ctree_flatten w1) (ctree_flatten w2))
    by eauto using ctree_flatten_refine.
  eapply of_val_refine; eauto.
  * eapply pbits_perm_unshared, pbits_unshared; eauto using pbits_kind_weaken,
      ctree_flatten_Forall_2, pbits_valid_sep_valid, ctree_flatten_valid.
  * eapply pbits_perm_mapped, pbits_mapped; eauto using pbits_kind_weaken,
      ctree_flatten_Forall_2, pbits_valid_sep_valid, ctree_flatten_valid.
Qed.
End memory.
