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

  Definition mem_allocable (o : index) (m : mem Ti) : Prop :=
    cmap_car m !! o = None.
  Definition mem_alloc (Γ : env Ti) (o : index)
      (alloc : bool) (τ : type Ti) (m : mem Ti) : mem Ti :=
    let (m) := m in CMap (<[o:=ctree_new Γ (pbit_full alloc) τ]>m).

  Definition mem_free (o : index) (m : mem Ti) : mem Ti :=
    let (m) := m in CMap (alter (ctree_map (λ _ : pbit Ti, pbit_freed)) o m).
  Definition mem_freeable (a : addr Ti) (m : mem Ti) : Prop :=
    (**i 1.) *) addr_ref_base a = [] ∧ addr_byte a = 0 ∧
    (**i 2.) *) ∃ w, cmap_car m !! addr_index a = Some w
       ∧ ctree_Forall (λ xb, Some Freeable ⊆ pbit_kind xb) w.

  Inductive mem_allocable_list (m : mem Ti) : list index → Prop :=
    | mem_allocable_nil : mem_allocable_list m []
    | mem_allocable_cons o os :
       o ∉ os → mem_allocable o m →
       mem_allocable_list m os → mem_allocable_list m (o :: os).
  Fixpoint mem_alloc_val_list (Γ : env Ti)
      (ovs : list (index * val Ti)) (m : mem Ti) : mem Ti :=
    match ovs with
    | [] => m
    | (o,v) :: ovs =>
       let τ := type_of v in let a := addr_top o τ in
       mem_alloc_val_list Γ ovs (<[a:=v]{Γ}>(mem_alloc Γ o false τ m))
    end.

  Program Definition mem_locks (m : mem Ti) : lockset :=
    let (m) := m in
    dexist (omap (λ w,
      let βs := natmap.of_bools (pbit_locked <$> ctree_flatten w) in
      guard (βs ≠ ∅); Some βs
    ) m) _.
  Next Obligation.
    intros o ω; rewrite lookup_omap, bind_Some; intros (?&?&?).
    by case_option_guard; simplify_equality.
  Qed.
  Definition mem_lock (Γ : env Ti) : addr Ti → mem Ti → mem Ti :=
    cmap_alter Γ (ctree_map pbit_lock).
  Definition mem_unlock (Ω : lockset) (m : mem Ti) : mem Ti :=
    let (Ω,_) := Ω in let (m) := m in
    CMap $ merge (λ mω mw,
      match mω, mw with
      | Some ω, Some w =>
         let sz := length (ctree_flatten w) in
         Some (ctree_merge true pbit_unlock_if w
           (resize sz false (natmap.to_bools ω)))
      | _,_ => mw
      end
    ) Ω m.
  Program Definition lock_singleton (Γ : env Ti) (a : addr Ti) : lockset :=
    let i := addr_object_offset Γ a in
    let n := bit_size_of' Γ a in
    let ω := natmap.of_bools (replicate i false ++ replicate n true) in
    (**i does not happen for typed addresses, then [n] is always positive *)
    if decide (ω ≠ ∅) then dexist {[ addr_index a, ω ]} _ else ∅.
  Next Obligation. by intros o ω ?; simplify_map_equality'. Qed.

  Global Instance locks_refine: Refine Ti (mem Ti) lockset := λ Γ f m1 m2 Ω1 Ω2,
    (**i 1.) *) Ω1 ⊆ mem_locks m1 ∧
    (**i 2.) *) Ω2 ⊆ mem_locks m2 ∧
    (**i 3.) *) m1 ⊑{Γ,f} m2 ∧
    (**i 4.) *) ∀ o1 o2 r w i,
      f !! o1 = Some (o2,r) → cmap_car m1 !! o1 = Some w →
      i < length (ctree_flatten w) →
      (o1,i) ∈ Ω1 ↔ (o2,ref_object_offset Γ r + i) ∈ Ω2.
End memory_operations.

Notation mem_unlock_all m := (mem_unlock (mem_locks m) m).

Section memory.
Context `{EnvSpec Ti}.
Implicit Types Γ : env Ti.
Implicit Types τ : type Ti.
Implicit Types a : addr Ti.
Implicit Types p : ptr Ti.
Implicit Types w : mtree Ti.
Implicit Types v : val Ti.
Implicit Types m : mem Ti.
Implicit Types β : bool.
Implicit Types βs : list bool.
Implicit Types xb : pbit Ti.
Implicit Types xbs : list (pbit Ti).
Implicit Types Ω : lockset.

Local Opaque nmap.Nempty.
Arguments union _ _ !_ !_ /.
Arguments difference _ _ !_ !_ /.
Arguments cmap_lookup _ _ _ _ !_ !_ /.

Hint Resolve Forall_app_2 Forall2_app.
Hint Immediate cmap_lookup_typed.
Hint Immediate ctree_refine_typed_l.
Hint Immediate val_typed_type_valid.
Hint Extern 0 (Separation _) => apply (_ : Separation (pbit Ti)).
Hint Extern 0 (Separation _) => apply (_ : Separation bool).
Hint Extern 0 (Separation _) => apply (_ : Separation (map bool)).

Ltac solve_length := repeat first 
  [ rewrite take_length | rewrite drop_length | rewrite app_length
  | rewrite zip_with_length | rewrite replicate_length | rewrite resize_length
  | rewrite fmap_length | erewrite ctree_flatten_length by eauto
  | match goal with
    | |- context [ bit_size_of ?Γ ?τ ] =>
      match goal with
        | H : Γ !! ?s = Some ?τs, H2 : ?τs !! _ = Some τ |- _ =>
          unless (bit_size_of Γ τ ≤ bit_size_of Γ (unionT s)) by done;
          assert (bit_size_of Γ τ ≤ bit_size_of Γ (unionT s))
            by eauto using bit_size_of_union_lookup
        end
      end ]; lia.
Hint Extern 0 (length _ = _) => solve_length.
Hint Extern 0 (_ ≤ length _) => solve_length.
Hint Extern 0 (length _ ≤ _) => solve_length.

(** ** Properties of the [alloc] function *)
Lemma mem_allocable_alt m o : mem_allocable o m ↔ o ∉ dom indexset m.
Proof. destruct m as [m]; simpl. by rewrite not_elem_of_dom. Qed.
Lemma NoDup_mem_allocable_list m os : mem_allocable_list m os → NoDup os.
Proof. induction 1; by constructor. Qed.
Lemma Forall_mem_allocable_list m os :
  mem_allocable_list m os → Forall (flip mem_allocable m) os.
Proof. by induction 1; constructor. Qed.
Lemma mem_allocable_list_alt m os :
  mem_allocable_list m os ↔ NoDup os ∧ Forall (flip mem_allocable m) os.
Proof.
  split; eauto using Forall_mem_allocable_list, NoDup_mem_allocable_list.
  intros [Hos Hmos]. induction Hos; decompose_Forall_hyps; constructor; auto.
Qed.
Lemma mem_empty_allocable o : mem_allocable o (∅ : mem Ti).
Proof. by unfold mem_allocable; simplify_map_equality'. Qed.
Lemma index_typed_alloc Γ m o alloc τ :
  ✓ Γ → ✓{Γ} τ → mem_alloc Γ o alloc τ m ⊢ o : τ.
Proof.
  intros. unfold typed, index_typed, type_check, index_type_check.
  destruct m as [m]; simplify_map_equality'; f_equal.
  apply (type_of_correct (Γ,∅) _), ctree_new_typed; auto using pbit_full_valid.
Qed.
Lemma index_typed_alloc_free Γ m o alloc τ o' τ' :
  mem_allocable o m → m ⊢ o' : τ' → mem_alloc Γ o alloc τ m ⊢ o' : τ'.
Proof.
  unfold mem_alloc, typed, index_typed, type_check, index_type_check.
  destruct m as [m]; simpl; intros.
  by destruct (decide (o = o')); simplify_map_equality'.
Qed.
Lemma mem_alloc_valid Γ m o alloc τ :
  ✓ Γ → ✓{Γ} m → ✓{Γ} τ → mem_allocable o m → int_typed (size_of Γ τ) sptrT →
  ✓{Γ} (mem_alloc Γ o alloc τ m).
Proof.
  destruct m as [m]; intros HΓ Hm Hx Hτ Hsz o' w; simpl.
  rewrite lookup_insert_Some; intros [[-> <-]|[??]].
  { exists τ. split_ands; eauto 7 using (ctree_Forall_not _ _ (CMap m)),
     ctree_new_typed, pbit_full_valid, ctree_new_Forall. }
  destruct (Hm o' w) as (σ&?&?); eauto.
  eauto using ctree_typed_weaken, (index_typed_alloc_free _ (CMap m)).
Qed.
Lemma mem_alloc_writable_top Γ m o alloc τ :
  ✓ Γ → ✓{Γ} τ → 
  mem_allocable o m → mem_writable Γ (addr_top o τ) (mem_alloc Γ o alloc τ m).
Proof.
  unfold mem_allocable. intros. exists (ctree_new Γ (pbit_full alloc) τ); split.
  * unfold lookupE, cmap_lookup. 
    rewrite option_guard_True by eauto using addr_top_strict.
    by destruct m as [m]; simplify_map_equality'.
  * apply ctree_new_Forall; auto; by destruct alloc.
Qed.
Lemma mem_alloc_writable Γ m o alloc a τ :
  ✓ Γ → ✓{Γ} τ →  mem_allocable o m →
  mem_writable Γ a m → mem_writable Γ a (mem_alloc Γ o alloc τ m).
Proof.
  intros ??? (w&?&?); exists w; split; auto.
  unfold mem_allocable, lookupE, cmap_lookup in *; destruct m as [m].
  case_option_guard; simplify_equality'.
  destruct (m !! addr_index a) as [w'|] eqn:?; simplify_equality'.
  by destruct (decide (o = addr_index a)); simplify_map_equality.
Qed.
Lemma mem_alloc_allocable Γ m o alloc o' τ :
  mem_allocable o' m → o ≠ o' → mem_allocable o' (mem_alloc Γ o alloc τ m).
Proof.
  by destruct m as [m]; unfold mem_allocable; intros; simplify_map_equality'.
Qed.
Lemma mem_alloc_allocable_list Γ m o alloc os τ :
  mem_allocable_list m os → o ∉ os →
  mem_allocable_list (mem_alloc Γ o alloc τ m) os.
Proof.
  induction 1; rewrite ?elem_of_cons; constructor;
    naive_solver auto using mem_alloc_allocable.
Qed.

(** ** Properties of the [mem_free] fucntion *)
Global Instance mem_freeable_dec o m : Decision (mem_freeable o m).
Proof.
  refine
   match Some_dec (cmap_car m !! addr_index o) with
   | inleft (w ↾ _) => cast_if_and3
      (decide (addr_ref_base o = [])) (decide (addr_byte o = 0))
      (decide (ctree_Forall (λ xb, Some Freeable ⊆ pbit_kind xb) w))
   | inright _ => right _
   end; abstract (unfold mem_freeable; naive_solver).
Defined.
Lemma mem_free_index_type_check m o o' :
  type_check (mem_free o m) o' = type_check m o'.
Proof.
  unfold type_check, index_type_check; destruct m as [m]; simpl; intros.
  destruct (decide (o' = o)); simplify_map_equality; auto.
  destruct (m !! o); f_equal'; auto using ctree_map_type_of.
Qed.
Lemma index_typed_free m o o' σ : m ⊢ o' : σ → mem_free o m ⊢ o' : σ.
Proof.
  intros. unfold typed, index_typed. by rewrite mem_free_index_type_check.
Qed.
Lemma addr_typed_free Γ m o a τ :
  ✓ Γ → (Γ,m) ⊢ a : τ → (Γ,mem_free o m) ⊢ a : τ.
Proof. eauto using addr_typed_weaken, index_typed_free. Qed.
Lemma val_typed_free Γ m o v τ :
  ✓ Γ → (Γ,m) ⊢ v : τ → (Γ,mem_free o m) ⊢ v : τ.
Proof. eauto using val_typed_weaken, index_typed_free. Qed.
Lemma mem_free_valid Γ m o : ✓ Γ → ✓{Γ} m → ✓{Γ} (mem_free o m).
Proof.
  intros HΓ Hm o' w Hw.
  cut (∃ τ, (Γ,m) ⊢ w : τ ∧ ¬ctree_empty w ∧ int_typed (size_of Γ τ) sptrT).
  { intros (τ&?&?&?); eauto 6 using ctree_typed_weaken, index_typed_free. } 
  revert Hw; destruct m as [m]; simpl.
  rewrite lookup_alter_Some; intros [(?&w'&?&->)|[??]]; [|by apply (Hm o' w)].
  destruct (Hm o' w') as (τ&?&?&?); auto.
  assert ((Γ, CMap m) ⊢ ctree_map (λ _, pbit_freed) w' : τ).
  { apply ctree_map_typed; auto.
    apply Forall_fmap, Forall_true; auto using pbit_freed_valid. }
  exists τ; split_ands; auto.
  eapply ctree_Forall_not; eauto. rewrite ctree_flatten_map.
  by apply Forall_fmap, Forall_true.
Qed.
Lemma index_typed_foldr_free m os o' σ :
  m ⊢ o' : σ → foldr mem_free m os ⊢ o' : σ.
Proof. induction os; simpl; eauto using index_typed_free. Qed.
Lemma mem_foldr_free_valid Γ m os : ✓ Γ → ✓{Γ} m → ✓{Γ} (foldr mem_free m os).
Proof. induction os; simpl; auto using mem_free_valid. Qed.

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
  eapply to_val_frozen, cmap_lookup_Some; eauto.
Qed.

(** Properties of the [force] function *)
Lemma index_typed_force Γ m a o σ :
  ✓ Γ → ✓{Γ} m → is_Some (m !!{Γ} a) →
  m ⊢ o : σ → mem_force Γ a m ⊢ o : σ.
Proof.
  unfold mem_force, lookupE, mem_lookup. intros ?? [v ?] ?.
  destruct (m !!{Γ} a) as [w|] eqn:?; simplify_equality'.
  eauto using cmap_alter_index_typed.
Qed.
Lemma addr_typed_force Γ m a a' τ' :
  ✓ Γ → ✓{Γ} m → is_Some (m !!{Γ} a) →
  (Γ,m) ⊢ a' : τ' → (Γ,mem_force Γ a m) ⊢ a' : τ'.
Proof. eauto using addr_typed_weaken, index_typed_force. Qed.
Lemma val_typed_force Γ m a v' τ' :
  ✓ Γ → ✓{Γ} m → is_Some (m !!{Γ} a) →
  (Γ,m) ⊢ v' : τ' → (Γ,mem_force Γ a m) ⊢ v' : τ'.
Proof. eauto using val_typed_weaken, index_typed_force. Qed.
Lemma mem_force_valid Γ m a :
  ✓ Γ → ✓{Γ} m → is_Some (m !!{Γ} a) → ✓{Γ} (mem_force Γ a m).
Proof.
  unfold mem_force, lookupE, mem_lookup. intros ?? [v ?].
  destruct (m !!{Γ} a) as [w|] eqn:?; simplify_option_equality.
  eapply cmap_alter_valid; eauto using cmap_lookup_Some.
  eauto using ctree_Forall_not, pbits_mapped, cmap_lookup_Some.
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
  eapply cmap_alter_disjoint; eauto using ctree_Forall_not, pbits_mapped.
Qed.
Lemma ctree_force_union Γ m1 m2 a1 v1 τ1 :
  ✓ Γ → ✓{Γ} m1 → m1 ⊥ m2 →
  (Γ,m1) ⊢ a1 : τ1 → is_Some (m1 !!{Γ} a1) →
  mem_force Γ a1 (m1 ∪ m2) =  mem_force Γ a1 m1 ∪ m2.
Proof.
  unfold lookupE, mem_lookup, mem_force. intros ???? [??].
  destruct (m1 !!{Γ} a1) as [w1|] eqn:?; simplify_option_equality.
  eapply cmap_alter_union; eauto using ctree_Forall_not, pbits_mapped.
Qed.

(** Properties of the [insert] function *)
Global Instance mem_writable_dec Γ a m : Decision (mem_writable Γ a m).
Proof.
  refine
   match Some_dec (m !!{Γ} a) with
   | inleft (w ↾ _) => cast_if
      (decide (ctree_Forall (λ xb, Some Writable ⊆ pbit_kind xb) w))
   | inright _ => right _
   end; abstract (unfold mem_writable; naive_solver).
Defined.
Lemma of_val_flatten_typed Γ m w v τ :
  ✓ Γ → (Γ,m) ⊢ w : τ → (Γ,m) ⊢ v : τ →
  ctree_Forall (λ xb, Some Writable ⊆ pbit_kind xb) w →
  (Γ,m) ⊢ of_val Γ (tagged_perm <$> ctree_flatten w) v : τ.
Proof.
  intros. eapply of_val_typed; eauto.
  * eauto using pbits_valid_perm_valid, ctree_flatten_valid.
  * eapply pbits_perm_mapped, pbits_mapped; eauto using pbits_kind_weaken,
      pbits_valid_sep_valid, ctree_flatten_valid.
Qed.
Lemma of_val_flatten_mapped Γ m w v τ :
  ✓ Γ → (Γ,m) ⊢ w : τ → (Γ,m) ⊢ v : τ →
  ctree_Forall (λ xb, Some Writable ⊆ pbit_kind xb) w →
  ¬ctree_unmapped (of_val Γ (tagged_perm <$> ctree_flatten w) v).
Proof.
  intros. eapply ctree_Forall_not; eauto using of_val_flatten_typed.
  eapply of_val_mapped; eauto.
  eapply pbits_perm_mapped, pbits_mapped; eauto using pbits_kind_weaken,
    pbits_valid_sep_valid, ctree_flatten_valid.
Qed.
Lemma of_val_flatten_unshared Γ m w v τ :
  ✓ Γ → (Γ,m) ⊢ w : τ → (Γ,m) ⊢ v : τ →
  ctree_Forall (λ xb, Some Writable ⊆ pbit_kind xb) w →
  ctree_unshared (of_val Γ (tagged_perm <$> ctree_flatten w) v).
Proof.
  intros. eapply of_val_unshared; eauto.
  * eapply pbits_perm_unshared, pbits_unshared; eauto using
      pbits_kind_weaken, pbits_valid_sep_valid, ctree_flatten_valid.
  * eapply pbits_perm_mapped, pbits_mapped; eauto using
      pbits_kind_weaken, pbits_valid_sep_valid, ctree_flatten_valid.
Qed.
Lemma index_typed_insert Γ m a v τ o σ :
  ✓ Γ → ✓{Γ} m → (Γ,m) ⊢ a : τ → mem_writable Γ a m → (Γ,m) ⊢ v : τ →
  m ⊢ o : σ → <[a:=v]{Γ}>m ⊢ o : σ.
Proof.
  unfold insertE, mem_insert, lookupE, mem_lookup. intros ??? (w&?&?) ??.
  assert ((Γ,m) ⊢ w : τ) by eauto. eapply cmap_alter_index_typed; eauto.
  rewrite of_val_type_of; simplify_type_equality; eauto.
Qed.
Lemma addr_typed_insert Γ m a v τ a' τ' :
  ✓ Γ → ✓{Γ} m → (Γ,m) ⊢ a : τ → mem_writable Γ a m → (Γ,m) ⊢ v : τ →
  (Γ,m) ⊢ a' : τ' → (Γ,<[a:=v]{Γ}>m) ⊢ a' : τ'.
Proof. eauto using addr_typed_weaken, index_typed_insert. Qed.
Lemma val_typed_insert Γ m a v τ v' τ' :
  ✓ Γ → ✓{Γ} m → (Γ,m) ⊢ a : τ → mem_writable Γ a m → (Γ,m) ⊢ v : τ →
  (Γ,m) ⊢ v' : τ' → (Γ,<[a:=v]{Γ}>m) ⊢ v' : τ'.
Proof. eauto using val_typed_weaken, index_typed_insert. Qed.
Lemma mem_insert_valid Γ m a v τ :
  ✓ Γ → ✓{Γ} m → (Γ,m) ⊢ a : τ → mem_writable Γ a m → (Γ,m) ⊢ v : τ →
  ✓{Γ} (<[a:=v]{Γ}>m).
Proof.
  intros ??? (w&?&?) ?. assert ((Γ,m) ⊢ w : τ) by eauto.
  eapply cmap_alter_valid; eauto; simplify_type_equality;
    eauto using of_val_flatten_typed, of_val_flatten_mapped.
Qed.
(** We need [addr_is_obj a] because writes at padding bytes are ignored *)
Lemma mem_lookup_insert Γ m a v τ :
  ✓ Γ → ✓{Γ} m → (Γ,m) ⊢ a : τ → mem_writable Γ a m → addr_is_obj a →
  (Γ,m) ⊢ v : τ → <[a:=v]{Γ}>m !!{Γ} a = Some (val_map (freeze true) v).
Proof.
  unfold insertE, lookupE, mem_insert, mem_lookup. intros ??? (w&?&Hw) ??.
  erewrite cmap_lookup_alter by eauto using of_val_flatten_typed; csimpl.
  assert (ctree_Forall (λ xb, Some Readable ⊆ pbit_kind xb)
    (of_val Γ (tagged_perm <$> ctree_flatten w) v)).
  { erewrite ctree_flatten_of_val by eauto. generalize (val_flatten Γ v).
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
  by erewrite cmap_lookup_alter_disjoint
    by eauto using of_val_flatten_typed, of_val_flatten_unshared.
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
(** Horrible premises, should be able to prove this without some. *)
Lemma mem_insert_writable Γ m a1 a2 v2 τ2 :
  ✓ Γ → ✓{Γ} m → a1 = a2 ∨ a1 ⊥{Γ} a2 →
  (Γ,m) ⊢ a2 : τ2 → mem_writable Γ a2 m → (Γ,m) ⊢ v2 : τ2 →
  mem_writable Γ a1 m → mem_writable Γ a1 (<[a2:=v2]{Γ}>m).
Proof.
  intros ?? Ha ? (w2&?&Hw2) ? (w1&?&Hw1). red. unfold insertE, mem_insert.
  destruct Ha as [<-|?]; [|erewrite cmap_lookup_alter_disjoint
    by eauto using of_val_flatten_unshared, of_val_flatten_typed; eauto].
  assert (ctree_Forall (λ xb, Some Writable ⊆ pbit_kind xb)
    (of_val Γ (tagged_perm <$> ctree_flatten w2) v2)).
  { erewrite ctree_flatten_of_val by eauto. generalize (val_flatten Γ v2).
    induction Hw2; intros [|??]; simpl; constructor; auto. }
  destruct (decide (addr_is_obj a1)).
  { erewrite cmap_lookup_alter by eauto; eauto. }
  erewrite cmap_lookup_alter_not_obj
    by eauto using of_val_flatten_unshared, of_val_flatten_typed.
  eauto using ctree_lookup_byte_after_Forall.
Qed.
Lemma mem_insert_allocable Γ m a v o :
  mem_allocable o (<[a:=v]{Γ}>m) ↔ mem_allocable o m.
Proof. destruct m as [m]; apply lookup_alter_None. Qed.
Lemma mem_insert_allocable_list Γ m a v os :
  mem_allocable_list (<[a:=v]{Γ}>m) os ↔ mem_allocable_list m os.
Proof.
  rewrite !mem_allocable_list_alt; unfold flip.
  by setoid_rewrite mem_insert_allocable.
Qed.
Lemma ctree_insert_disjoint Γ m1 m2 a1 v1 τ1 :
  ✓ Γ → ✓{Γ} m1 → m1 ⊥ m2 →
  (Γ,m1) ⊢ a1 : τ1 → mem_writable Γ a1 m1 → (Γ,m1) ⊢ v1 : τ1 →
  <[a1:=v1]{Γ}>m1 ⊥ m2.
Proof.
  intros ???? (w1&?&?) ?. assert (ctree_unshared w1).
  { eapply pbits_unshared; eauto using pbits_kind_weaken,
      pbits_valid_sep_valid, ctree_flatten_valid. }
  assert (ctree_Forall (not ∘ sep_unmapped) w1).
  { eapply pbits_mapped; eauto using pbits_kind_weaken. }
  eapply cmap_alter_disjoint; eauto using of_val_flatten_typed,
    of_val_flatten_mapped, of_val_disjoint.
Qed.
Lemma ctree_insert_union Γ m1 m2 a1 v1 τ1 :
  ✓ Γ → ✓{Γ} m1 → m1 ⊥ m2 →
  (Γ,m1) ⊢ a1 : τ1 → mem_writable Γ a1 m1 → (Γ,m1) ⊢ v1 : τ1 →
  <[a1:=v1]{Γ}>(m1 ∪ m2) = <[a1:=v1]{Γ}>m1 ∪ m2.
Proof.
  intros ???? (w1&?&?) ?. assert (ctree_unshared w1).
  { eapply pbits_unshared; eauto using pbits_kind_weaken,
      pbits_valid_sep_valid, ctree_flatten_valid. }
  assert (ctree_Forall (not ∘ sep_unmapped) w1).
  { eapply pbits_mapped; eauto using pbits_kind_weaken. }
  eapply cmap_alter_union; eauto using of_val_flatten_typed,
    of_val_flatten_mapped, of_val_disjoint, of_val_union.
Qed.
Lemma mem_alloc_val_valid Γ m alloc o v τ :
  ✓ Γ → ✓{Γ} m → mem_allocable o m →
  (Γ,m) ⊢ v : τ → int_typed (size_of Γ τ) sptrT →
  ✓{Γ} (<[addr_top o τ:=v]{Γ}>(mem_alloc Γ o alloc τ m)).
Proof.
  intros. eapply mem_insert_valid; eauto using mem_alloc_valid,
    addr_top_typed, index_typed_alloc, mem_alloc_writable_top,
    val_typed_weaken, index_typed_alloc_free.
Qed.
Lemma index_typed_alloc_val_free Γ m alloc o v τ :
  ✓ Γ → ✓{Γ} m → mem_allocable o m →
  (Γ,m) ⊢ v : τ → int_typed (size_of Γ τ) sptrT →
  <[addr_top o τ:=v]{Γ}>(mem_alloc Γ o alloc τ m) ⊢ o : τ.
Proof.
  intros; eapply index_typed_insert; eauto using mem_alloc_valid,
    addr_top_typed, index_typed_alloc, mem_alloc_writable_top,
    val_typed_weaken, index_typed_alloc_free.
Qed.
Lemma index_typed_alloc_val Γ m alloc o v τ o' σ' :
  ✓ Γ → ✓{Γ} m → mem_allocable o m →
  (Γ,m) ⊢ v : τ → int_typed (size_of Γ τ) sptrT →
  m ⊢ o' : σ' → <[addr_top o τ:=v]{Γ}>(mem_alloc Γ o alloc τ m) ⊢ o' : σ'.
Proof.
  intros. eapply index_typed_insert; eauto using mem_alloc_valid,
    addr_top_typed, index_typed_alloc, mem_alloc_writable_top,
    val_typed_weaken, index_typed_alloc_free.
Qed.
Lemma mem_alloc_val_allocable Γ m o alloc v τ o' :
  mem_allocable o' m → o ≠ o' →
  mem_allocable o' (<[addr_top o τ:=v]{Γ}>(mem_alloc Γ o alloc τ m)).
Proof. intros. by apply mem_insert_allocable, mem_alloc_allocable. Qed.
Lemma mem_alloc_val_list_valid Γ m os vs τs :
  ✓ Γ → ✓{Γ} m → mem_allocable_list m os → length os = length vs →
  (Γ,m) ⊢* vs :* τs → Forall (λ τ, int_typed (size_of Γ τ) sptrT) τs →
  ✓{Γ} (mem_alloc_val_list Γ (zip os vs) m)
  ∧ mem_alloc_val_list Γ (zip os vs) m ⊢* os :* τs
  ∧ ∀ o σ, m ⊢ o : σ → mem_alloc_val_list Γ (zip os vs) m ⊢ o : σ.
Proof.
  rewrite <-Forall2_same_length. intros ? Hm Hfree Hovs Hvs Hτs.
  revert os vs m Hovs Hm Hvs Hfree.
  induction Hτs as [|τ τs ?? IH];
    intros ?? m [|o v os vs ??]; inversion_clear 3;
    decompose_Forall_hyps'; simplify_type_equality; auto.
  destruct (IH os vs (<[addr_top o τ:=v]{Γ}> (mem_alloc Γ o false τ m))) as
    (IH1&IH2&IH3); eauto using mem_alloc_val_valid.
  { eauto using Forall2_impl, val_typed_weaken, index_typed_alloc_val. }
  { by apply mem_insert_allocable_list, mem_alloc_allocable_list. }
  repeat constructor;
    eauto using index_typed_alloc_val_free, index_typed_alloc_val.
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
  eapply cmap_alter_refine; eauto using ctree_Forall_not, pbits_mapped.
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
    eauto using of_val_flatten_mapped, val_refine_typed_l.
  erewrite <-(pbits_refine_perm _ _ _ _ (ctree_flatten w1) (ctree_flatten w2))
    by eauto using ctree_flatten_refine.
  eapply of_val_refine; eauto.
  * eapply pbits_perm_unshared, pbits_unshared; eauto using
      pbits_kind_weaken, pbits_valid_sep_valid, ctree_flatten_valid.
  * eapply pbits_perm_mapped, pbits_mapped; eauto using
      pbits_kind_weaken, pbits_valid_sep_valid, ctree_flatten_valid.
Qed.

(** ** Locks *)
Lemma mem_locks_empty : mem_locks ∅ = ∅.
Proof. apply dsig_eq; unfold mem_locks; simpl. by rewrite omap_empty. Qed.
Lemma mem_locks_union m1 m2 :
  m1 ⊥ m2 → mem_locks (m1 ∪ m2) = mem_locks m1 ∪ mem_locks m2.
Proof.
  intros Hm. apply dsig_eq. destruct m1 as [m1], m2 as [m2]; simpl.
  apply map_eq; intros o; specialize (Hm o);
    rewrite lookup_omap, !lookup_union_with, !lookup_omap.
  destruct (m1 !! o) as [w1|], (m2 !! o) as [w2|]; csimpl.
  * destruct Hm as (?&?&?). assert (length (pbit_locked <$> ctree_flatten w1)
      = length (pbit_locked <$> ctree_flatten w2)).
    { rewrite !fmap_length. by eapply Forall2_length, @ctree_flatten_disjoint. }
    rewrite ctree_flatten_union, pbits_locked_union, natmap.of_bools_union
      by eauto using @ctree_flatten_disjoint.
    simplify_option_equality; f_equal; esolve_elem_of.
  * by simplify_option_equality.
  * by simplify_option_equality.
  * by simplify_option_equality.
Qed.
Lemma mem_unlock_empty m : mem_unlock ∅ m = m.
Proof.
  destruct m as [m]; unfold mem_unlock; sep_unfold; f_equal.
  apply map_eq; intros i. by rewrite lookup_merge, lookup_empty by done.
Qed.
Lemma mem_locks_subseteq m1 m2 : m1 ⊆ m2 → mem_locks m1 ⊆ mem_locks m2.
Proof.
  rewrite !sep_subseteq_spec'; intros (m3&->&?).
  rewrite mem_locks_union by done. esolve_elem_of.
Qed.
Lemma index_typed_lock Γ m a o σ :
  ✓ Γ → ✓{Γ} m → mem_writable Γ a m → m ⊢ o : σ → mem_lock Γ a m ⊢ o : σ.
Proof.
  unfold mem_lock. intros ?? (v&?&?) ?.
  eauto using cmap_alter_index_typed, ctree_map_type_of.
Qed.
Lemma addr_typed_lock Γ m a a' τ' :
  ✓ Γ → ✓{Γ} m → mem_writable Γ a m →
  (Γ,m) ⊢ a' : τ' → (Γ,mem_lock Γ a m) ⊢ a' : τ'.
Proof. eauto using addr_typed_weaken, index_typed_lock. Qed.
Lemma val_typed_lock Γ m a v' τ' :
  ✓ Γ → ✓{Γ} m → mem_writable Γ a m →
  (Γ,m) ⊢ v' : τ' → (Γ,mem_lock Γ a m) ⊢ v' : τ'.
Proof. eauto using val_typed_weaken, index_typed_lock. Qed.
Lemma mem_lock_valid Γ m a :
  ✓ Γ → ✓{Γ} m → mem_writable Γ a m → ✓{Γ} (mem_lock Γ a m).
Proof.
  intros ?? (w&?&?) ?. assert ((Γ,m) ⊢ ctree_map pbit_lock w : type_of w).
  { eapply ctree_map_typed; eauto using cmap_lookup_Some,
      pbits_lock_valid, ctree_flatten_valid; by intros [??] <-. }
  eapply cmap_alter_valid, ctree_Forall_not; eauto.
  rewrite ctree_flatten_map.
  eapply pbits_mapped_lock, pbits_mapped, pbits_kind_weaken; eauto.
Qed.
Lemma ctree_unlock_typed Γ m w τ βs :
  ✓ Γ → (Γ,m) ⊢ w : τ → length βs = bit_size_of Γ τ →
  (Γ,m) ⊢ ctree_merge true pbit_unlock_if w βs : τ.
Proof.
  intros HΓ Hw. revert w τ Hw βs.
  refine (ctree_typed_ind _ _ _ _ _ _ _ _); simpl.
  * intros; typed_constructor; auto using pbits_unlock_if_valid.
  * intros ws τ Hws IH Hlen βs. rewrite bit_size_of_array.
    intros Hβs; typed_constructor; auto.
    + clear Hlen IH. revert βs Hβs. induction Hws; intros; f_equal'; auto.
    + clear Hlen. revert βs Hβs.
      induction Hws; intros; decompose_Forall_hyps'; constructor; auto.
  * intros s wxbss τs Hs Hws IH Hxbss Hindet Hlen βs.
    erewrite bit_size_of_struct by eauto. intros Hβs.
    typed_constructor; eauto; clear Hs.
    + clear Hxbss Hindet. revert wxbss βs Hws IH Hβs Hlen.
      unfold field_bit_padding. induction (bit_size_of_fields _ τs HΓ);
        intros [|[??] ?] ?????; decompose_Forall_hyps';
        erewrite ?type_of_correct by eauto; constructor; simpl; auto.
    + clear Hβs. revert βs. elim Hxbss; [|intros [??] ????];
        constructor; simpl; auto using pbits_unlock_if_valid.
    + clear Hβs. revert βs. elim Hindet; [|intros [??] ????]; constructor;
        simpl in *; auto; rewrite pbit_indetify_unlock_if; congruence.
    + clear Hxbss IH Hindet. revert wxbss βs Hws Hβs Hlen.
      unfold field_bit_padding. induction (bit_size_of_fields _ τs HΓ);
        intros [|[??] ?] ????; decompose_Forall_hyps';
        erewrite ?type_of_correct by eauto; f_equal; auto.
  * intros s i τs w xbs τ ??????? Hc βs ?. typed_constructor; eauto.
    + auto using pbits_unlock_if_valid.
    + rewrite pbit_indetify_unlock_if; congruence.
    + solve_length.
    + rewrite ctree_flatten_merge.
      intros [??]; destruct Hc; split; eapply pbits_unmapped_inv;
        eauto using ctree_flatten_valid, pbits_valid_sep_valid.
  * intros; typed_constructor; eauto using pbits_unlock_if_valid.
Qed.
Lemma index_typed_unlock m Ω o σ : m ⊢ o : σ → mem_unlock Ω m ⊢ o : σ.
Proof.
  unfold typed, index_typed, type_check, index_type_check.
  destruct m as [m], Ω as [Ω]; simpl; intros. rewrite lookup_merge by done.
  destruct (m !! o) as [w|], (Ω !! o) as [ω|]; simplify_equality'; f_equal.
  destruct w as [|? ws| | |]; f_equal'. generalize (natmap.to_bools ω).
  induction ws; intros; f_equal';
    rewrite ?app_length, ?resize_plus, ?drop_app_alt by auto; auto.
Qed.
Lemma addr_typed_unlock Γ m Ω a σ :
  ✓ Γ → (Γ,m) ⊢ a : σ → (Γ,mem_unlock Ω m) ⊢ a : σ.
Proof. eauto using addr_typed_weaken, index_typed_unlock. Qed.
Lemma val_typed_unlock Γ m Ω v σ :
  ✓ Γ → (Γ,m) ⊢ v : σ → (Γ,mem_unlock Ω m) ⊢ v : σ.
Proof. eauto using val_typed_weaken, index_typed_unlock. Qed.
Lemma mem_unlock_valid Γ m Ω : ✓ Γ → ✓{Γ} m → ✓{Γ} (mem_unlock Ω m).
Proof.
  intros ? Hm o w Hw; simpl. cut (∃ τ,
    (Γ,m) ⊢ w : τ ∧ ¬ctree_empty w ∧ int_typed (size_of Γ τ) sptrT).
  { intros (τ&?&?&?); eauto 7 using ctree_typed_weaken, index_typed_unlock. }
  revert Hw. destruct m as [m], Ω as [Ω HΩ']; simpl.
  rewrite lookup_merge by done; intros.
  destruct (m !! o) as [w'|] eqn:Hw',
    (Ω !! o) as [ω|] eqn:Hω; simplify_equality'; [|by apply (Hm o)].
  destruct (Hm o w') as (τ&?&Hemp&?); auto.
  exists τ; split_ands; auto using ctree_unlock_typed.
  rewrite ctree_flatten_merge; contradict Hemp.
  eapply pbits_unlock_empty_inv;
    eauto using ctree_flatten_valid, pbits_valid_sep_valid.
Qed.
Lemma ctree_unlock_type_of w βs :
  type_of (ctree_merge true pbit_unlock_if w βs) = type_of w.
Proof.
  destruct w as [|τ ws| | |]; f_equal'.
  revert βs. induction ws; intros; f_equal'; auto.
Qed.
End memory.
