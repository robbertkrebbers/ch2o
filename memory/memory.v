(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
From stdpp Require Import natmap fin_map_dom. 
Require Export values memory_map.
Local Open Scope ctype_scope.

Section memory_operations.
  Context `{Env K}.

  Global Instance mem_lookup:
      LookupE (env K) (addr K) (val K) (mem K) := λ Γ a m,
    w ← m !!{Γ} a;
    guard (ctree_Forall (λ γb, Some Readable ⊆ pbit_kind γb) w);
    Some (to_val Γ w).
  Definition mem_force (Γ : env K) (a : addr K) : mem K → mem K :=
    cmap_alter_ref Γ id (addr_index a) (addr_ref Γ a).
  Definition mem_forced (Γ : env K) (a : addr K) (m : mem K) : Prop :=
    mem_force Γ a m = m.

  Definition mem_writable (Γ : env K) (a : addr K) (m : mem K) : Prop :=
    ∃ w, m !!{Γ} a = Some w
         ∧ ctree_Forall (λ γb, Some Writable ⊆ pbit_kind γb) w.
  Global Instance mem_insert:
      InsertE (env K) (addr K) (val K) (mem K) := λ Γ a v,
    cmap_alter Γ (λ w, of_val Γ (tagged_perm <$> ctree_flatten w) v) a.

  Definition mem_alloc (Γ : env K) (o : index)
      (μ : bool) (γ : perm) (v : val K) (m : mem K) : mem K :=
    let τ := type_of v in
    let γs := replicate (bit_size_of Γ τ) γ in
    let (m) := m in CMap (<[o:=Obj (of_val Γ γs v) μ]>m).
  Fixpoint mem_alloc_list (Γ : env K)
      (os : list index) (vs : list (val K)) (m : mem K) : mem K :=
    match os, vs with
    | o :: os, v :: vs =>
       mem_alloc Γ o false perm_full v (mem_alloc_list Γ os vs m)
    | _, _ => m
    end.

  Definition mem_free (o : index) (m : mem K) : mem K :=
    let (m) := m in
    CMap (alter (λ x,
      match x with Obj w _ => Freed (type_of w) | _ => x end) o m).
  Definition mem_freeable_perm (o : index) (μ : bool) (m : mem K) : Prop := ∃ w,
    (**i 1.) *) cmap_car m !! o = Some (Obj w μ) ∧
    (**i 2.) *) ctree_Forall (λ γb, tagged_perm γb = perm_full) w.
  Definition mem_freeable (a : addr K) (m : mem K) : Prop :=
    (**i 1.) *) addr_is_top_array a ∧
    (**i 2.) *) mem_freeable_perm (addr_index a) true m.

  Program Definition mem_locks (m : mem K) : lockset :=
    let (m) := m in
    dexist (omap (λ x,
      '(w,_) ← maybe2 Obj x;
      let βs := bools_to_natset (pbit_locked <$> ctree_flatten w) in
      guard (βs ≠ ∅); Some βs
    ) m) _.
  Next Obligation.
    by intros ? ? o ω; rewrite lookup_omap, bind_Some;
      intros ([]&?&?); simplify_option_eq.
  Qed.
  Definition mem_lock (Γ : env K) : addr K → mem K → mem K :=
    cmap_alter Γ (ctree_map pbit_lock).
  Definition mem_unlock (Ω : lockset) (m : mem K) : mem K :=
    let (Ω,_) := Ω in let (m) := m in
    CMap $ merge (λ mω mx,
      match mω, mx with
      | Some ω, Some (Obj w μ) =>
         let sz := length (ctree_flatten w) in
         Some (Obj (ctree_merge pbit_unlock_if w (natset_to_bools sz ω)) μ)
      | _,_ => mx
      end) Ω m.
  Definition mem_unlock_all (m : mem K) : mem K := (mem_unlock (mem_locks m) m).
  Program Definition lock_singleton (Γ : env K) (a : addr K) : lockset :=
    let i := addr_object_offset Γ a in
    let n := ptr_bit_size_of Γ (type_of a) in
    let ω := bools_to_natset (replicate i false ++ replicate n true) in
    (**i does not happen for typed addresses, then [n] is always positive *)
    if decide (ω ≠ ∅) then dexist {[ addr_index a := ω ]} _ else ∅.
  Next Obligation. by simpl; intros ??? o ω ?; simplify_map_eq. Qed.

  Global Instance mem_forced_dec `{Env K} {Γ a m}: Decision (mem_forced Γ a m).
  Proof. unfold mem_forced. apply _. Defined.
End memory_operations.

Arguments mem_unlock _ !_ !_ /.

Section memory.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types Δ : memenv K.
Implicit Types τ : type K.
Implicit Types a : addr K.
Implicit Types w : mtree K.
Implicit Types v : val K.
Implicit Types m : mem K.
Implicit Types α β : bool.
Implicit Types βs : list bool.
Implicit Types γb : pbit K.
Implicit Types γbs : list (pbit K).
Implicit Types Ω : lockset.

Hint Resolve Forall_app_2 Forall2_app: core.
Hint Immediate cmap_lookup_typed val_typed_type_valid: core.

Ltac solve_length := repeat first 
  [ rewrite take_length | rewrite drop_length | rewrite app_length
  | rewrite zip_with_length | rewrite replicate_length | rewrite resize_length
  | rewrite fmap_length | erewrite ctree_flatten_length by eauto
  | erewrite val_flatten_length by eauto | rewrite natset_to_bools_length
  | rewrite bit_size_of_char ]; lia.
Hint Extern 0 (length _ = _) => solve_length: core.
Hint Extern 0 (_ ≤ length _) => solve_length: core.
Hint Extern 0 (length _ ≤ _) => solve_length: core.

Lemma mem_writable_weaken Γ1 Γ2 Δ m a σ :
  ✓ Γ1 → (Γ1,Δ) ⊢ a : TType σ → mem_writable Γ1 a m →
  Γ1 ⊆ Γ2 → mem_writable Γ2 a m.
Proof. intros ?? (w&?&?) ?; exists w; eauto using cmap_lookup_weaken. Qed.
Lemma mem_erase_writable Γ m a :
  mem_writable Γ a (cmap_erase m) = mem_writable Γ a m.
Proof. unfold mem_writable; simpl. by rewrite cmap_lookup_erase. Qed.

(** ** Properties of the [alloc] function *)
Lemma mem_alloc_memenv_of Γ Δ m o μ γ v τ :
  ✓ Γ → (Γ,Δ) ⊢ v : τ → '{mem_alloc Γ o μ γ v m} = <[o:=(τ,false)]>'{m}.
Proof.
  intros. apply map_eq; intros o'; destruct m as [m]; simpl.
  destruct (decide (o = o')); simplify_map_eq; f_equal.
  by erewrite of_val_type_of, type_of_correct by eauto.
Qed.
Lemma mem_alloc_alive_memenv_of Γ Δ m o μ γ v τ :
  ✓ Γ →'{m} ⊢ o : τ → index_alive '{m} o → (Γ,Δ) ⊢ v : τ →
  '{mem_alloc Γ o μ γ v m} = '{m}.
Proof.
  rewrite <-index_alive_spec'; unfold index_alive'; intros.
  destruct (index_typed_lookup_cmap m o τ) as ([|? w]&?&?);
    simplify_option_eq; try done.
  apply map_eq; intros o'; destruct m as [m]; simpl.
  destruct (decide (o = o')); simplify_map_eq; f_equal.
  by erewrite of_val_type_of, type_of_correct by eauto.
Qed.
Lemma mem_alloc_index_typed_inv Δ o τ β o' τ' :
  o ≠ o' → <[o:=(τ,β)]>Δ ⊢ o' : τ' → Δ ⊢ o' : τ'.
Proof. by intros ? [β' ?]; exists β'; simplify_map_eq. Qed.
Lemma mem_alloc_index_alive_ne Δ o τ β o' :
  o ≠ o' → index_alive Δ o' → index_alive (<[o:=(τ,β)]>Δ) o'.
Proof. by intros ? [τ' ?]; exists τ'; simplify_map_eq. Qed.
Lemma mem_alloc_index_alive_inv Δ o τ β o' :
  o ≠ o' → index_alive (<[o:=(τ,β)]>Δ) o' → index_alive Δ o'.
Proof. by intros ? [τ' ?]; exists τ'; simplify_map_eq. Qed.
Lemma mem_alloc_index_typed Δ o τ β : <[o:=(τ,β)]>Δ ⊢ o : τ.
Proof. by exists β; simplify_map_eq. Qed.
Lemma mem_alloc_index_alive Δ o τ : index_alive (<[o:=(τ,false)]>Δ) o.
Proof. by exists τ; simplify_map_eq. Qed.
Lemma mem_alloc_forward Δ o τ : Δ !! o = None → Δ ⇒ₘ <[o:=(τ,false)]>Δ.
Proof.
  split.
  * by intros ?? [β' ?]; exists β'; simplify_map_eq.
  * by intros ? τ' [??] [??]; exists τ'; simplify_map_eq.
Qed.
Lemma mem_alloc_memenv_compat Δ1 Δ2 o τ β :
  Δ1 ⇒ₘ Δ2 → <[o:=(τ,β)]>Δ1 ⇒ₘ <[o:=(τ,β)]>Δ2.
Proof.
  intros [Htyped Halive]; split.
  * intros o' τ' [β' ?]; destruct (decide (o = o')); simplify_map_eq.
    { apply mem_alloc_index_typed. }
    destruct (Htyped o' τ') as [β'' ?]; [by exists β'|].
    by exists β''; simplify_map_eq.
  * intros o' τ' [β' ?] [τ'' ?];
      destruct (decide (o = o')); simplify_map_eq.
    { apply mem_alloc_index_alive. }
    destruct (Halive o' τ') as [τ''' ?]; [by exists β'|by exists τ''|].
    by exists τ'''; simplify_map_eq.
Qed.
Lemma mem_alloc_forward_least Γ Δ Δ' m o μ γ v τ :
  (Γ,Δ') ⊢ v : τ →
  ✓{Γ,Δ'} (mem_alloc Γ o μ γ v m) → Δ ⇒ₘ Δ' → <[o:=(τ,false)]>Δ ⇒ₘ Δ'.
Proof.
  split.
  * intros o' τ'; destruct (decide (o' = o)) as [->|];
      eauto using mem_alloc_index_typed_inv, index_typed_weaken.
    intros [β ?]; simplify_map_eq.
    set (γs:=replicate (bit_size_of Γ (type_of v)) γ).
    destruct (cmap_valid_Obj Γ Δ' (mem_alloc Γ o μ γ v m) o
      (of_val Γ γs v) μ) as (τ&?&_&?&_); auto.
    { by destruct m; simplify_map_eq. }
    assert (type_of (of_val Γ γs v) = type_of v) by auto using of_val_type_of.
    by simplify_type_equality.
  * intros o' τ'; destruct (decide (o' = o)) as [->|];
      eauto using mem_alloc_index_alive, mem_alloc_index_alive_ne,
      memenv_forward_alive, mem_alloc_index_typed_inv.
Qed.
Lemma mem_alloc_memenv_valid Γ Δ o τ β :
  ✓{Γ} Δ → Δ !! o = None → ✓{Γ} τ → ✓{Γ}(<[o:=(τ,β)]>Δ).
Proof.
  intros HΔ ?? o' τ' [??].
  destruct (decide (o = o')); simplify_map_eq; eauto.
  eapply HΔ; do 2 red; eauto.
Qed.
Lemma mem_alloc_alive_valid Γ Δ m o μ γ v τ :
  ✓ Γ → ✓{Γ,Δ} m → Δ ⊢ o : τ → index_alive Δ o → sep_valid γ →
  ¬sep_unmapped γ → (Γ,Δ) ⊢ v : τ → ✓{Γ,Δ} (mem_alloc Γ o μ γ v m).
Proof.
  destruct m as [m]; intros HΓ Hm Ho Ho' Hx Hx' Hv; split_and !; simpl.
  * eauto using mem_alloc_memenv_valid, cmap_valid_memenv_valid.
  * intros o' τ'; rewrite lookup_insert_Some;
      intros [[??]|[??]]; simplify_equality'.
    destruct (cmap_valid_Freed Γ Δ (CMap m) o' τ') as (?&?&?); eauto.
  * assert ((Γ,Δ) ⊢ of_val Γ (replicate (bit_size_of Γ τ) γ) v : τ)
      by eauto using of_val_typed, Forall_replicate.
    intros o' w μ'; rewrite lookup_insert_Some;
      intros [[??]|[??]]; simplify_type_equality'.
    { exists τ; split_and ?; eauto 9 using ctree_Forall_not, Forall_replicate,
       of_val_mapped, @sep_unmapped_empty_alt, Forall_impl. }
    destruct (cmap_valid_Obj Γ Δ (CMap m) o' w μ')
      as (τ'&?&?&?&?); simplify_map_eq; eauto.
Qed.
Lemma mem_alloc_valid Γ Δ m o μ γ v τ :
  ✓ Γ → ✓{Γ,Δ} m → Δ !! o = None → sep_valid γ → ¬sep_unmapped γ →
  (Γ,<[o:=(τ,false)]>Δ) ⊢ v : τ →
  ✓{Γ,<[o:=(τ,false)]>Δ} (mem_alloc Γ o μ γ v m).
Proof.
  intros; eapply mem_alloc_alive_valid; eauto using mem_alloc_index_typed,
    mem_alloc_index_alive, cmap_valid_weaken, (insert_subseteq Δ),
    mem_alloc_memenv_valid, cmap_valid_memenv_valid.
Qed.
Lemma mem_allocable_memenv_of m o : o ∉ dom indexset m → '{m} !! o = None.
Proof. rewrite cmap_dom_alt. by intros; destruct m; simplify_map_eq. Qed.
Hint Extern 10 => erewrite mem_alloc_memenv_of by eauto: core.
Lemma mem_alloc_valid' Γ m o μ γ v τ :
  ✓ Γ → ✓{Γ} m → o ∉ dom indexset m → sep_valid γ → ¬sep_unmapped γ →
  (Γ,'{mem_alloc Γ o μ γ v m}) ⊢ v : τ → ✓{Γ} (mem_alloc Γ o μ γ v m).
Proof.
  unfold valid at 2 3, cmap_valid'; intros ????? Hv.
  erewrite mem_alloc_memenv_of in Hv by eauto.
  eauto using mem_alloc_valid, mem_allocable_memenv_of.
Qed.
Lemma mem_alloc_alive_valid' Γ m o μ γ v τ :
  ✓ Γ → ✓{Γ} m → '{m} ⊢ o : τ → index_alive '{m} o → sep_valid γ →
  ¬sep_unmapped γ → (Γ,'{m}) ⊢ v : τ → ✓{Γ} (mem_alloc Γ o μ γ v m).
Proof.
  unfold valid at 2 3, cmap_valid'; intros.
  erewrite mem_alloc_alive_memenv_of by eauto;eauto using mem_alloc_alive_valid.
Qed.
Lemma mem_alloc_new_valid' Γ m o μ γ τ :
  ✓ Γ → ✓{Γ} m → o ∉ dom indexset m → sep_valid γ → ¬sep_unmapped γ → ✓{Γ} τ →
  ✓{Γ} (mem_alloc Γ o μ γ (val_new Γ τ) m).
Proof. eauto using mem_alloc_valid', val_new_typed. Qed.
Lemma mem_alloc_index_typed' Γ Δ m o μ γ v τ :
  ✓ Γ → (Γ,Δ) ⊢ v : τ → '{mem_alloc Γ o μ γ v m} ⊢ o : τ.
Proof. eauto using mem_alloc_index_typed. Qed.
Lemma mem_alloc_index_alive' Γ Δ m o μ γ v τ :
  ✓ Γ → (Γ,Δ) ⊢ v : τ → index_alive '{mem_alloc Γ o μ γ v m} o.
Proof. eauto using mem_alloc_index_alive. Qed.
Lemma mem_alloc_new_index_typed' Γ m o μ γ τ :
  ✓ Γ → ✓{Γ} τ → '{mem_alloc Γ o μ γ (val_new Γ τ) m} ⊢ o : τ.
Proof. eauto using mem_alloc_index_typed', (val_new_typed _ ∅). Qed.
Lemma mem_alloc_new_index_alive' Γ m o μ γ τ :
  ✓ Γ → ✓{Γ} τ → index_alive '{mem_alloc Γ o μ γ (val_new Γ τ) m} o.
Proof. eauto using mem_alloc_index_alive', (val_new_typed _ ∅). Qed.
Lemma mem_alloc_index_typed_inv' Γ Δ m o μ γ v τ o' τ' :
  ✓ Γ → o ≠ o' → (Γ,Δ) ⊢ v : τ →
  '{mem_alloc Γ o μ γ v m} ⊢ o' : τ' → '{m} ⊢ o' : τ'.
Proof. eauto using mem_alloc_index_typed_inv. Qed.
Lemma mem_alloc_forward' Γ Δ m o μ γ v τ :
  ✓ Γ → o ∉ dom indexset m → (Γ,Δ) ⊢ v : τ →
  '{m} ⇒ₘ '{mem_alloc Γ o μ γ v m}.
Proof. eauto using mem_alloc_forward, mem_allocable_memenv_of. Qed.
Lemma mem_alloc_alive_forward' Γ Δ m o μ γ v τ :
  ✓ Γ → '{m} ⊢ o : τ → index_alive '{m} o → (Γ, Δ) ⊢ v : τ →
  '{m} ⇒ₘ '{mem_alloc Γ o μ γ v m}.
Proof. intros. by erewrite mem_alloc_alive_memenv_of by eauto. Qed.
Lemma mem_alloc_new_forward' Γ m o μ γ τ :
  ✓ Γ → o ∉ dom indexset m → ✓{Γ} τ →
  '{m} ⇒ₘ '{mem_alloc Γ o μ γ (val_new Γ τ) m}.
Proof. eauto using mem_alloc_forward', (val_new_typed _ ∅). Qed.
Lemma mem_alloc_writable_top Γ Δ m o μ γ v τ :
  ✓ Γ → (Γ,Δ) ⊢ v : τ → Some Writable ⊆ perm_kind γ →
  mem_writable Γ (addr_top o τ) (mem_alloc Γ o μ γ v m).
Proof.
  exists (of_val Γ (replicate (bit_size_of Γ τ) γ) v); split.
  * unfold lookupE, cmap_lookup.
    rewrite option_guard_True by eauto using addr_top_strict.
    destruct m as [m]; simplify_map_eq; simplify_type_equality.
    by rewrite decide_True by eauto using addr_top_is_obj.
  * erewrite ctree_flatten_of_val by eauto. generalize (val_flatten Γ v).
    induction (bit_size_of Γ τ); intros [|??]; simpl; constructor; auto.
Qed.
Lemma mem_alloc_writable Γ m o μ a γ v τ :
  o ∉ dom indexset m →
  mem_writable Γ a m → mem_writable Γ a (mem_alloc Γ o μ γ v m).
Proof.
  rewrite cmap_dom_alt. intros Ho (w&?&?); exists w; split; auto.
  unfold lookupE, cmap_lookup in *; destruct m as [m].
  case_option_guard; simplify_equality'.
  destruct (m !! addr_index a) as [w'|] eqn:?; simplify_equality'.
  by destruct (decide (o = addr_index a)); simplify_map_eq.
Qed.
Lemma mem_dom_alloc Γ m o μ γ v :
  dom indexset (mem_alloc Γ o μ γ v m) = {[ o ]} ∪ dom indexset m.
Proof. destruct m as [m]; f_equal'. apply dom_insert_L. Qed.
Lemma mem_erase_alloc Γ m o μ γ v :
  cmap_erase (mem_alloc Γ o μ γ v m) = mem_alloc Γ o μ γ v (cmap_erase m).
Proof.
  destruct m as [m]; f_equal'; apply map_eq; intros o'.
  by destruct (decide (o' = o)); simplify_map_eq.
Qed.
Lemma mem_alloc_valid_inv Γ Δ m o μ γ v :
  o ∉ dom indexset m → ✓{Γ,Δ} (mem_alloc Γ o μ γ v m) → ✓{Γ,Δ} m.
Proof.
  rewrite cmap_dom_alt; intros ? (?&Hfreed&Halive); split_and !; auto.
  * intros; eapply Hfreed; by destruct m; simplify_map_eq.
  * intros; eapply Halive; by destruct m; simplify_map_eq.
Qed.
Lemma mem_alloc_valid_index_inv Γ Δ m o μ γ v :
  ✓{Γ,Δ} (mem_alloc Γ o μ γ v m) → index_alive Δ o ∧ Δ ⊢ o : type_of v.
Proof.
  intros (_&_&Halive).
  edestruct Halive as (?&?&?&?&?); [by destruct m; simplify_map_eq|].
  by erewrite <-of_val_type_of, type_of_correct by eauto.
Qed.
Lemma mem_alloc_allocable_list Γ m o μ γ v os :
  Forall_fresh (dom indexset m) os → o ∉ os →
  Forall_fresh (dom indexset (mem_alloc Γ o μ γ v m)) os.
Proof. rewrite mem_dom_alloc, !Forall_fresh_alt; set_solver. Qed.
Lemma mem_dom_alloc_list Γ m os vs :
  length os = length vs →
  dom indexset (mem_alloc_list Γ os vs m) = list_to_set os ∪ dom indexset m.
Proof.
  rewrite <-Forall2_same_length; induction 1; simpl;
    rewrite ?mem_dom_alloc; set_solver.
Qed.
Lemma mem_alloc_list_valid Γ m os vs τs :
  ✓ Γ → ✓{Γ} m → Forall_fresh (dom indexset m) os → length os = length vs →
  (Γ,'{m}) ⊢* vs :* τs →
  (**i 1.) *) ✓{Γ} (mem_alloc_list Γ os vs m) ∧
  (**i 2.) *) '{mem_alloc_list Γ os vs m} ⊢* os :* τs ∧
  (**i 3.) *) '{m} ⇒ₘ '{mem_alloc_list Γ os vs m}.
Proof.
  rewrite <-Forall2_same_length. intros ? Hm Hfree Hovs Hvs.
  revert τs Hvs Hfree.
  induction Hovs as [|o v os vs ?? IH]; intros [|τ τs];
    inversion_clear 2 as [|?? Ho Ho' Hos];
    decompose_Forall_hyps; simplify_type_equality; auto.
  destruct (IH τs) as (?&?&?); eauto.
  assert (o ∉ dom indexset (mem_alloc_list Γ os vs m)).
  { rewrite mem_dom_alloc_list, elem_of_union, elem_of_list_to_set
       by eauto using Forall2_length; tauto. }
  split_and ?; eauto 6 using mem_alloc_valid', perm_full_valid,
    perm_full_mapped, val_typed_weaken, mem_alloc_forward',
    mem_alloc_allocable_list, mem_alloc_index_typed, indexes_typed_weaken.
Qed.
Lemma mem_alloc_list_index_typed Γ m os vs τs :
  ✓ Γ → ✓{Γ} m → Forall_fresh (dom indexset m) os → length os = length vs →
  (Γ,'{m}) ⊢* vs :* τs → '{mem_alloc_list Γ os vs m} ⊢* os :* τs.
Proof. eapply mem_alloc_list_valid. Qed.
Lemma mem_alloc_list_forward Γ m os vs τs :
  ✓ Γ → ✓{Γ} m → Forall_fresh (dom indexset m) os → length os = length vs →
  (Γ,'{m}) ⊢* vs :* τs → '{m} ⇒ₘ '{mem_alloc_list Γ os vs m}.
Proof. eapply mem_alloc_list_valid. Qed.

(** ** Properties of the [mem_free] fucntion *)
#[global] Instance mem_freeable_perm_dec o μ m: Decision (mem_freeable_perm o μ m).
Proof.
  refine
   match cmap_car m !! o as x return Decision (∃ w, x = Some (Obj w μ)
     ∧ ctree_Forall (λ γb, tagged_perm γb = perm_full) w)
   with
   | Some (Obj w μ') => cast_if_and (decide (μ = μ'))
      (decide (ctree_Forall (λ γb, tagged_perm γb = perm_full) w))
   | _ => right _
   end; abstract naive_solver.
Defined.
#[global] Instance mem_freeable_dec a m : Decision (mem_freeable a m) := _.
Lemma mem_free_memenv_of m o :
  '{mem_free o m} = alter (prod_map id (λ _, true)) o '{m}.
Proof.
  destruct m as [m]; simpl; apply map_eq; intros o'.
  destruct (decide (o = o')) as [->|?].
  { rewrite !lookup_fmap, !lookup_alter, lookup_fmap; simpl.
    by destruct (m !! o') as [[]|]. }
  by rewrite lookup_fmap, !lookup_alter_ne, lookup_fmap by done.
Qed.
Lemma mem_erase_freeable_perm m o μ :
  mem_freeable_perm o μ (cmap_erase m) ↔ mem_freeable_perm o μ m.
Proof.
  destruct m as [m]; unfold mem_freeable_perm; simpl. rewrite lookup_omap.
  destruct (m !! o) as [[]|]; naive_solver.
Qed.
Lemma mem_dom_free m o : dom indexset (mem_free o m) = dom indexset m.
Proof. destruct m as [m]; simpl; apply dom_alter_L. Qed.
Lemma mem_erase_freeable m o : mem_freeable o (cmap_erase m) ↔ mem_freeable o m.
Proof. unfold mem_freeable. by rewrite mem_erase_freeable_perm. Qed.
Lemma mem_free_index_typed_inv Δ o o' τ' :
  alter (prod_map id (λ _, true)) o Δ ⊢ o' : τ' → Δ ⊢ o' : τ'.
Proof.
  intros [β ?]; destruct (decide (o = o')); simplify_map_eq.
  * destruct (Δ !! o') as [[? β']|] eqn:?; simplify_equality'; by exists β'.
  * by exists β; simplify_map_eq.
Qed.
Lemma mem_free_index_alive_ne Δ o o' :
  o ≠ o' → index_alive Δ o' →
  index_alive (alter (prod_map id (λ _, true)) o Δ) o'.
Proof. by intros ? [τ ?]; exists τ; simplify_map_eq. Qed.
Lemma mem_free_index_alive Δ o :
  ¬index_alive (alter (prod_map id (λ _ : bool, true)) o Δ) o.
Proof. intros [??]; simplify_map_eq; simplify_option_eq. Qed.
Lemma mem_free_index_alive_inv Δ o o' :
  index_alive (alter (prod_map id (λ _, true)) o Δ) o' → index_alive Δ o'.
Proof.
  by intros [τ ?]; destruct (decide (o = o')); exists τ;
    simplify_map_eq; simplify_option_eq.
Qed.
Lemma mem_free_forward Δ o : Δ ⇒ₘ alter (prod_map id (λ _, true)) o Δ.
Proof.
  split; [|eauto using mem_free_index_alive_inv].
  intros o' ? [β ?]; destruct (decide (o = o')).
  * by exists true; simplify_map_eq.
  * by exists β; simplify_map_eq.
Qed.
Lemma mem_free_memenv_compat Δ1 Δ2 o :
  Δ1 ⇒ₘ Δ2 →
  alter (prod_map id (λ _, true)) o Δ1 ⇒ₘ alter (prod_map id (λ _, true)) o Δ2.
Proof.
  intros [Htyped Halive]; split.
  * eauto 4 using index_typed_weaken,mem_free_forward, mem_free_index_typed_inv.
  * intros o' τ [β ?] [τ' ?]; destruct (decide (o = o'));
      simplify_map_eq; [simplify_option_eq|].
    destruct (Halive o' τ) as [τ'' ?]; [by exists β|by exists τ'|].
    by exists τ''; simplify_map_eq.
Qed.
Lemma mem_free_forward_least Γ Δ Δ' m o μ :
  mem_freeable_perm o μ m →
  ✓{Γ,Δ'} (mem_free o m) → Δ ⇒ₘ Δ' → alter (prod_map id (λ _, true)) o Δ ⇒ₘ Δ'.
Proof.
  intros (w&?&_).
  split; eauto using mem_free_index_typed_inv, index_typed_weaken.
  intros o' τ'; destruct (decide (o' = o)) as [->|];
    eauto using mem_free_index_alive_ne, memenv_forward_alive,
    mem_free_index_typed_inv.
  intros _ [τ ?]; destruct (cmap_valid_Freed Γ Δ'
    (mem_free o m) o (type_of w)) as (?&[]&?); auto.
  { by destruct m; simplify_map_eq. }
  by exists τ.
Qed.
Lemma mem_free_env_valid Γ Δ o :
  ✓{Γ} Δ → ✓{Γ} (alter (prod_map id (λ _, true)) o Δ).
Proof.
  intros HΔ o' τ' [??]; specialize (HΔ o' τ').
  destruct (decide (o = o')); simplify_map_eq;
    [destruct (Δ !! o') as [[]|] eqn:?; simplify_map_eq|];
    eapply HΔ; do 2 red; eauto.
Qed.
Lemma mem_free_valid Γ Δ m o :
  ✓ Γ → ✓{Γ,Δ} m → ✓{Γ,alter (prod_map id (λ _, true)) o Δ} (mem_free o m).
Proof.
  destruct m as [m]; intros HΓ Hm; split_and !; simpl.
  { eauto using mem_free_env_valid, cmap_valid_memenv_valid. }
  { intros o' τ; rewrite lookup_alter_Some;
      intros [(?&[τ'|w μ']&?&?)|[??]]; simplify_equality'.
    * destruct (cmap_valid_Freed Γ Δ (CMap m) o' τ') as (?&?&?); eauto 10
        using mem_free_forward, index_typed_weaken, memenv_forward_alive.
    * destruct (cmap_valid_Obj Γ Δ (CMap m) o' w μ')
        as (?&?&?&?&?);simplify_type_equality';
        eauto 11 using ctree_typed_type_valid, mem_free_index_alive,
        mem_free_forward, index_typed_weaken, memenv_forward_alive.
    * destruct (cmap_valid_Freed Γ Δ (CMap m) o' τ) as (?&?&?); eauto 10 using
        mem_free_forward, index_typed_weaken, memenv_forward_alive. }
  intros o' w μ; rewrite lookup_alter_Some;
    intros [(?&[]&?&?)|[??]]; simplify_map_eq.
  destruct (cmap_valid_Obj Γ Δ (CMap m) o' w μ) as (τ'&?&?&?&?); eauto.
  exists τ'; split_and ?; eauto using
    ctree_typed_weaken, mem_free_index_alive_ne, mem_free_forward,
     mem_free_forward, index_typed_weaken, memenv_forward_alive.
Qed.
Lemma mem_free_valid' Γ m o : ✓ Γ → ✓{Γ} m → ✓{Γ} (mem_free o m).
Proof.
  unfold valid at 2 3, cmap_valid'; intros. rewrite mem_free_memenv_of.
  eauto using mem_free_valid.
Qed.
Lemma mem_free_forward' m o : '{m} ⇒ₘ '{mem_free o m}.
Proof. rewrite mem_free_memenv_of; eauto using mem_free_forward. Qed.
Lemma mem_free_valid_index_inv Γ Δ m μ o :
  ✓{Γ,Δ} (mem_free o m) → mem_freeable_perm o μ m → ¬index_alive Δ o.
Proof.
  intros (_&Hfree&_) (w&?&_).
  by destruct (Hfree o (type_of w)); [by destruct m; simplify_map_eq|].
Qed.
Lemma mem_foldr_free_forward m os : '{m} ⇒ₘ '{foldr mem_free m os}.
Proof. induction os; simpl; eauto using mem_free_forward'. Qed.
Lemma mem_foldr_free_valid Γ m os : ✓ Γ → ✓{Γ} m → ✓{Γ} (foldr mem_free m os).
Proof. induction os; simpl; auto using mem_free_valid'. Qed.
Lemma mem_dom_foldr_free m os :
  dom indexset (foldr mem_free m os) = dom indexset m.
Proof. induction os; simpl; rewrite ?mem_dom_free; auto. Qed.
Lemma mem_free_free m o1 o2 :
  mem_free o1 (mem_free o2 m) = mem_free o2 (mem_free o1 m).
Proof.
  destruct m as [m]; f_equal';
    destruct (decide (o1 = o2)) as [->|]; auto using alter_commute.
Qed.
Lemma mem_free_foldr_free m o os :
  mem_free o (foldr mem_free m os) = foldr mem_free (mem_free o m) os.
Proof. induction os; simpl; rewrite 1?mem_free_free; auto with f_equal. Qed.
Lemma mem_freeable_perm_free m o o' μ :
  o ≠ o' → mem_freeable_perm o μ m → mem_freeable_perm o μ (mem_free o' m).
Proof.
  intros ? (w&?&?); exists w; split_and ?; auto.
  by destruct m as [m]; simplify_map_eq.
Qed.
Lemma mem_freeable_perm_foldr_free m o os μ :
  o ∉ os →
  mem_freeable_perm o μ m → mem_freeable_perm o μ (foldr mem_free m os).
Proof.
  induction os as [|o' os IH]; simpl; auto.
  rewrite not_elem_of_cons; intros [??]; auto using mem_freeable_perm_free.
Qed.

(** ** Properties of the [lookup] function *)
Lemma mem_lookup_empty Γ a : ∅ !!{Γ} a = @None (val K).
Proof. unfold lookupE, mem_lookup. by rewrite cmap_lookup_empty. Qed.
Lemma mem_lookup_typed Γ Δ m a v τ :
  ✓ Γ → ✓{Γ,Δ} m → m !!{Γ} a = Some v → (Γ,Δ) ⊢ a : TType τ → (Γ,Δ) ⊢ v : τ.
Proof.
  unfold lookupE, mem_lookup. intros ? Hm Hv Ha. destruct (m !!{Γ} a)
    as [w|] eqn:?; simplify_option_eq; eauto using to_val_typed.
Qed.
Lemma mem_lookup_frozen Γ Δ m a v :
  ✓ Γ → ✓{Γ,Δ} m → m !!{Γ} a = Some v → frozen v.
Proof.
  unfold lookupE, mem_lookup. intros ? Hm Hv.
  destruct (m !!{Γ} a) as [w|] eqn:?; simplify_option_eq.
  eapply to_val_frozen, cmap_lookup_Some; eauto.
Qed.
Lemma mem_lookup_erase Γ m a :
  (cmap_erase m !!{Γ} a : option (val K)) = m !!{Γ} a.
Proof. unfold lookupE, mem_lookup. by rewrite cmap_lookup_erase. Qed.
Lemma mem_lookup_alloc Γ Δ m o μ γ v τ :
  ✓ Γ → (Γ,Δ) ⊢ v : τ → Some Readable ⊆ perm_kind γ →
  mem_alloc Γ o μ γ v m !!{Γ} addr_top o τ = Some (freeze true v).
Proof.
  unfold lookupE, mem_lookup, lookupE, cmap_lookup; intros.
  assert (ctree_Forall (λ γb, Some Readable ⊆ pbit_kind γb)
    (of_val Γ (replicate (bit_size_of Γ τ) γ) v)).
  { erewrite ctree_flatten_of_val by eauto. generalize (val_flatten Γ v).
    induction (bit_size_of Γ τ); intros [|??]; simpl; constructor; auto. }
  rewrite option_guard_True by eauto using addr_top_strict.
  destruct m as [m]; simplify_map_eq; simplify_type_equality.
  rewrite decide_True by eauto using addr_top_is_obj; simpl.
  by erewrite option_guard_True, to_of_val by eauto.
Qed.
Lemma mem_lookup_weaken Γ1 Γ2 Δ m a v τ :
  ✓ Γ1 → ✓{Γ1,Δ} m → (Γ1,Δ) ⊢ a : TType τ → m !!{Γ1} a = Some v →
  Γ1 ⊆ Γ2 → m !!{Γ2} a = Some v.
Proof.
  unfold lookupE, mem_lookup; rewrite bind_Some; intros ??? (w&?&?) ?.
  erewrite cmap_lookup_weaken by eauto; simplify_option_eq.
  by erewrite <-to_val_weaken by eauto.
Qed.

(** Properties of the [force] function *)
Lemma mem_forced_force Γ m a : mem_forced Γ a m → mem_force Γ a m = m.
Proof. done. Qed.
Lemma mem_force_memenv_of Γ Δ m a :
  ✓ Γ → ✓{Γ,Δ} m → is_Some (m !!{Γ} a) → '{mem_force Γ a m} = '{m}.
Proof.
  unfold mem_force, lookupE, mem_lookup; simpl; unfold lookupE, cmap_lookup.
  intros ?? [v ?]. by destruct (m !!{Γ} _) as [w|] eqn:?;
    simplify_option_eq; eauto using cmap_alter_ref_memenv_of.
Qed.
Lemma mem_force_forward Γ Δ m a :
  ✓ Γ → ✓{Γ,Δ} m → is_Some (m !!{Γ} a) → '{m} ⇒ₘ '{mem_force Γ a m}.
Proof. intros. by erewrite mem_force_memenv_of by eauto. Qed.
Lemma mem_force_valid Γ Δ m a :
  ✓ Γ → ✓{Γ,Δ} m → is_Some (m !!{Γ} a) → ✓{Γ,Δ} (mem_force Γ a m).
Proof.
  unfold mem_force, lookupE, mem_lookup; simpl; unfold lookupE, cmap_lookup.
  intros ?? [v ?]; case_option_guard; simplify_equality';
    destruct (m !!{Γ} _) as [w|] eqn:?; simplify_equality'.
  destruct (cmap_lookup_ref_Some Γ Δ m (addr_index a)
    (addr_ref Γ a) w) as (?&?&?&?&?); eauto.
  eapply cmap_alter_ref_valid; eauto.
  { eapply type_of_typed; eauto. }
  case_decide; simplify_equality'; case_option_guard; simplify_equality'.
  { eapply ctree_Forall_not; eauto using pbits_mapped. }
  destruct (w !!{Γ} _) as [w'|] eqn:?; simplify_option_eq.
  intros ?; eapply (ctree_Forall_not _ _ _ w');
    eauto using ctree_lookup_byte_Forall, pbit_unmapped_indetify,
    pbits_mapped, ctree_lookup_byte_typed.
Qed.
Lemma mem_force_valid' Γ m a :
  ✓ Γ → ✓{Γ} m → is_Some (m !!{Γ} a) → ✓{Γ} (mem_force Γ a m).
Proof.
  unfold valid at 2 3, cmap_valid'; intros.
  erewrite mem_force_memenv_of by eauto; eauto using mem_force_valid.
Qed.
Lemma mem_force_weaken Γ1 Γ2 Δ m a τ :
  ✓ Γ1 → Γ1 ⊆ Γ2 → ✓{Γ1,Δ} m → (Γ1,Δ) ⊢ a : TType τ →
  mem_force Γ1 a m = mem_force Γ2 a m.
Proof.
  unfold mem_force; intros. erewrite addr_ref_weaken by eauto.
  eauto using cmap_alter_ref_weaken.
Qed.
Lemma mem_forced_weaken Γ1 Γ2 Δ m a τ :
  ✓ Γ1 → Γ1 ⊆ Γ2 → ✓{Γ1,Δ} m → (Γ1,Δ) ⊢ a : TType τ →
  mem_forced Γ1 a m → mem_forced Γ2 a m.
Proof. unfold mem_forced; intros. by erewrite <-mem_force_weaken by eauto. Qed.
Lemma mem_erase_force Γ m a :
  cmap_erase (mem_force Γ a m) = mem_force Γ a (cmap_erase m).
Proof. apply cmap_erase_alter_ref. Qed.
Lemma mem_forced_erase Γ a m : mem_forced Γ a (cmap_erase m) ↔ mem_forced Γ a m.
Proof.
  unfold mem_forced; split; intros Hm; [|by rewrite <-mem_erase_force, Hm].
  destruct m as [m]; simplify_equality'; f_equal; apply map_eq; intros o.
  destruct (decide (o = addr_index a)); simplify_map_eq; auto.
  apply (f_equal (.!! (addr_index a))) in Hm; simplify_map_eq.
  destruct (m !! _) as [[]|]; simplify_equality'; congruence.
Qed.
Lemma mem_lookup_force Γ Δ m a v τ :
  ✓ Γ → ✓{Γ,Δ} m → (Γ,Δ) ⊢ a : TType τ → m !!{Γ} a = Some v → addr_is_obj a →
  mem_force Γ a m !!{Γ} a = Some v.
Proof.
  unfold mem_force, lookupE, mem_lookup; simpl; unfold lookupE, cmap_lookup.
  intros; case_option_guard; simplify_equality';
    destruct (m !!{Γ} _) as [w|] eqn:?; simplify_equality'.
  by erewrite cmap_lookup_ref_alter by
    eauto using cmap_lookup_ref_le, ref_freeze_le_r; simplify_option_eq.
Qed.
Lemma mem_lookup_force_disjoint Γ Δ m a1 a2 τ2 v1 :
  ✓ Γ → ✓{Γ,Δ} m → a1 ##{Γ} a2 → m !!{Γ} a1 = Some v1 →
  mem_force Γ a2 m !!{Γ} a1 = Some v1.
Proof.
  unfold mem_force, lookupE, mem_lookup; simpl; unfold lookupE, cmap_lookup.
  intros ?? Ha ?; case_option_guard; simplify_equality'.
  destruct (m !!{Γ} (addr_index a1,_)) as [w1|] eqn:?; simplify_equality'.
  destruct Ha as [|[[??]|(<-&?&?&?&?)]];
    erewrite ?cmap_lookup_ref_alter_disjoint by eauto; auto.
  by erewrite cmap_lookup_ref_alter
    by eauto using cmap_lookup_ref_le, ref_freeze_le_r.
Qed.
Lemma mem_force_commute Γ m a1 a2 :
  a1 ##{Γ} a2 →
  mem_force Γ a1 (mem_force Γ a2 m) = mem_force Γ a2 (mem_force Γ a1 m).
Proof.
  unfold mem_force; intros [?|[[??]|(<-&Hr&?&?&?)]];
    auto using cmap_alter_ref_commute.
  by rewrite <-!(cmap_alter_ref_le _ _ _ _ (addr_ref Γ a1)), !Hr,
    !(cmap_alter_ref_le _ _ _ (freeze true <$> addr_ref Γ a2) (addr_ref Γ a2)),
    <-!cmap_alter_ref_compose by eauto using ref_freeze_le_l.
Qed.
Lemma mem_force_forced Γ m a : mem_forced Γ a (mem_force Γ a m).
Proof. unfold mem_forced, mem_force. by rewrite <-cmap_alter_ref_compose. Qed.
Lemma mem_dom_force Γ m a : dom indexset (mem_force Γ a m) = dom indexset m.
Proof. destruct m; simpl; apply dom_alter_L. Qed.

(** Properties of the [insert] function *)
Lemma mem_writable_strict Γ m a : mem_writable Γ a m → addr_strict Γ a.
Proof. intros (w&?&?); eauto using cmap_lookup_strict. Qed.
Lemma mem_writable_alive Γ Δ m a :
  ✓ Γ → ✓{Γ,Δ} m → mem_writable Γ a m → index_alive Δ (addr_index a).
Proof.
  intros ? Hm (w&?&?).
  assert ((Γ,Δ) ⊢ w : type_of w) by eauto using cmap_lookup_Some.
  unfold lookupE, cmap_lookup, lookupE, cmap_lookup_ref in *;
    case_option_guard; simplify_equality'.
  destruct (cmap_car m !! addr_index a) as [[|w' μ]|] eqn:?; simplify_equality'.
  destruct (cmap_valid_Obj Γ Δ m (addr_index a) w' μ) as (τ&?&?&?); auto.
Qed.
#[global] Instance mem_writable_dec Γ a m : Decision (mem_writable Γ a m).
Proof.
  refine
   match Some_dec (m !!{Γ} a) with
   | inleft (w ↾ _) => cast_if
      (decide (ctree_Forall (λ γb, Some Writable ⊆ pbit_kind γb) w))
   | inright _ => right _
   end; abstract (unfold mem_writable; naive_solver).
Defined.
Lemma mem_writable_lookup Γ m a : mem_writable Γ a m → ∃ v, m !!{Γ} a = Some v.
Proof.
  unfold lookupE, mem_lookup; intros (w&->&?); simpl; exists (to_val Γ w).
  by rewrite option_guard_True by eauto using pbits_kind_weaken.
Qed.
Lemma mem_lookup_writable Γ m a : m !!{Γ} a = None → ¬mem_writable Γ a m.
Proof. intros ??. destruct (mem_writable_lookup Γ m a); naive_solver. Qed.
Lemma of_val_flatten_typed Γ Δ w v τ :
  ✓ Γ → (Γ,Δ) ⊢ w : τ → (Γ,Δ) ⊢ v : τ →
  ctree_Forall (λ γb, Some Writable ⊆ pbit_kind γb) w →
  (Γ,Δ) ⊢ of_val Γ (tagged_perm <$> ctree_flatten w) v : τ.
Proof.
  intros. eapply of_val_typed; eauto.
  * eauto using pbits_valid_perm_valid, ctree_flatten_valid.
  * eapply pbits_perm_mapped, pbits_mapped; eauto using pbits_kind_weaken,
      pbits_valid_sep_valid, ctree_flatten_valid.
Qed.
Hint Resolve of_val_flatten_typed: core.
Lemma of_val_flatten_mapped Γ Δ w v τ :
  ✓ Γ → (Γ,Δ) ⊢ w : τ → (Γ,Δ) ⊢ v : τ →
  ctree_Forall (λ γb, Some Writable ⊆ pbit_kind γb) w →
  ctree_Forall (not ∘ sep_unmapped)
    (of_val Γ (tagged_perm <$> ctree_flatten w) v).
Proof.
  intros. eapply of_val_mapped; eauto.
  eapply pbits_perm_mapped, pbits_mapped; eauto using pbits_kind_weaken,
    pbits_valid_sep_valid, ctree_flatten_valid.
Qed.
Lemma of_val_flatten_unshared Γ Δ w v τ :
  ✓ Γ → (Γ,Δ) ⊢ w : τ → (Γ,Δ) ⊢ v : τ →
  ctree_Forall (λ γb, Some Writable ⊆ pbit_kind γb) w →
  ctree_unshared (of_val Γ (tagged_perm <$> ctree_flatten w) v).
Proof.
  intros. eapply of_val_unshared; eauto.
  * eapply pbits_perm_unshared, pbits_unshared; eauto using
      pbits_kind_weaken, pbits_valid_sep_valid, ctree_flatten_valid.
  * eapply pbits_perm_mapped, pbits_mapped; eauto using
      pbits_kind_weaken, pbits_valid_sep_valid, ctree_flatten_valid.
Qed.
Lemma mem_insert_memenv_of Γ Δ m a v τ :
  ✓ Γ → ✓{Γ,Δ} m → (Γ,Δ) ⊢ a : TType τ → mem_writable Γ a m → (Γ,Δ) ⊢ v : τ →
  '{<[a:=v]{Γ}>m} = '{m}.
Proof.
  unfold insertE, mem_insert, lookupE, mem_lookup. intros ??? (w&?&?) ?.
  eapply cmap_alter_memenv_of; eauto.
  by erewrite of_val_type_of, !type_of_correct by eauto.
Qed.
Lemma mem_insert_forward Γ Δ m a v τ :
  ✓ Γ → ✓{Γ,Δ} m → (Γ,Δ) ⊢ a : TType τ → mem_writable Γ a m → (Γ,Δ) ⊢ v : τ →
  '{m} ⇒ₘ '{<[a:=v]{Γ}>m}.
Proof. intros. by erewrite mem_insert_memenv_of by eauto. Qed.
Lemma mem_insert_valid Γ Δ m a v τ :
  ✓ Γ → ✓{Γ,Δ} m → (Γ,Δ) ⊢ a : TType τ → mem_writable Γ a m → (Γ,Δ) ⊢ v : τ →
  ✓{Γ,Δ} (<[a:=v]{Γ}>m).
Proof.
  intros ??? (w&?&?) ?. assert ((Γ,Δ) ⊢ w : τ) by eauto.
  eapply cmap_alter_valid; eauto; simplify_type_equality;
    eauto using of_val_flatten_mapped, ctree_Forall_not, ctree_lookup_Some.
Qed.
Lemma mem_insert_valid' Γ m a v τ :
  ✓ Γ → ✓{Γ} m → (Γ,'{m}) ⊢ a : TType τ → mem_writable Γ a m →
  (Γ,'{m}) ⊢ v : τ → ✓{Γ} (<[a:=v]{Γ}>m).
Proof.
  unfold valid at 2 3, cmap_valid'; intros.
  erewrite mem_insert_memenv_of by eauto; eauto using mem_insert_valid.
Qed.
Lemma mem_erase_insert Γ m a v :
  cmap_erase (<[a:=v]{Γ}>m) = <[a:=v]{Γ}>(cmap_erase m).
Proof. apply cmap_erase_alter. Qed.
(** We need [addr_is_obj a] because writes at padding bytes are ignored *)
Lemma mem_lookup_insert Γ Δ m a v τ :
  ✓ Γ → ✓{Γ,Δ} m → (Γ,Δ) ⊢ a : TType τ → mem_writable Γ a m → addr_is_obj a →
  (Γ,Δ) ⊢ v : τ → <[a:=v]{Γ}>m !!{Γ} a = Some (freeze true v).
Proof.
  unfold insertE, lookupE, mem_insert, mem_lookup. intros ??? (w&?&Hw) ??.
  erewrite cmap_lookup_alter by eauto; csimpl.
  assert (ctree_Forall (λ γb, Some Readable ⊆ pbit_kind γb)
    (of_val Γ (tagged_perm <$> ctree_flatten w) v)).
  { erewrite ctree_flatten_of_val by eauto. generalize (val_flatten Γ v).
    induction Hw; intros [|??]; simpl; constructor; auto.
    by transitivity (Some Writable). }
  by erewrite option_guard_True, to_of_val by eauto.
Qed.
Lemma mem_lookup_insert_disjoint Γ Δ m a1 a2 v1 v2 τ2 :
  ✓ Γ → ✓{Γ,Δ} m → a1 ##{Γ} a2 → m !!{Γ} a1 = Some v1 →
  (Γ,Δ) ⊢ a2 : TType τ2 → mem_writable Γ a2 m → (Γ,Δ) ⊢ v2 : τ2 →
  <[a2:=v2]{Γ}>m !!{Γ} a1 = Some v1.
Proof.
  unfold insertE, lookupE, mem_insert, mem_lookup. intros ????? (w2&?&Hw2) ?.
  destruct (m !!{Γ} a1) as [w1|] eqn:?; simplify_equality'.
  by erewrite cmap_lookup_alter_disjoint by eauto using of_val_flatten_unshared.
Qed.
Lemma mem_insert_commute Γ Δ m a1 a2 v1 v2 τ1 τ2 :
  ✓ Γ → ✓{Γ,Δ} m → a1 ##{Γ} a2 →
  (Γ,Δ) ⊢ a1 : TType τ1 → mem_writable Γ a1 m → (Γ,Δ) ⊢ v1 : τ1 →
  (Γ,Δ) ⊢ a2 : TType τ2 → mem_writable Γ a2 m → (Γ,Δ) ⊢ v2 : τ2 →
  <[a1:=v1]{Γ}>(<[a2:=v2]{Γ}>m) = <[a2:=v2]{Γ}>(<[a1:=v1]{Γ}>m).
Proof. intros ???? (?&?&?) ?? (?&?&?) ?. eapply cmap_alter_commute; eauto. Qed.
Lemma mem_insert_force_commute Γ m a1 a2 v1 :
  a1 ##{Γ} a2 →
  <[a1:=v1]{Γ}>(mem_force Γ a2 m) = mem_force Γ a2 (<[a1:=v1]{Γ}>m).
Proof.
  unfold mem_force, insertE, mem_insert, cmap_alter.
  intros [?|[[??]|(<-&Hr&?&?&?)]]; auto using cmap_alter_ref_commute.
  by rewrite <-!(cmap_alter_ref_le _ _ _ _ (addr_ref Γ a1)), !Hr,
    !(cmap_alter_ref_le _ _ _ (freeze true <$> addr_ref Γ a2) (addr_ref Γ a2)),
    <-!cmap_alter_ref_compose by eauto using ref_freeze_le_l.
Qed.
Lemma mem_insert_force Γ m a v : <[a:=v]{Γ}>(mem_force Γ a m) = <[a:=v]{Γ}>m.
Proof.
  unfold insertE, mem_insert, mem_force, cmap_alter.
  by rewrite <-cmap_alter_ref_compose.
Qed.
Lemma mem_insert_forced Γ m a v : mem_forced Γ a (<[a:=v]{Γ}>m).
Proof. symmetry; apply (cmap_alter_ref_compose _ id). Qed.
Lemma mem_insert_writable Γ Δ m a1 a2 v2 τ2 :
  ✓ Γ → ✓{Γ,Δ} m → a1 = a2 ∨ a1 ##{Γ} a2 →
  (Γ,Δ) ⊢ a2 : TType τ2 → mem_writable Γ a2 m → (Γ,Δ) ⊢ v2 : τ2 →
  mem_writable Γ a1 m → mem_writable Γ a1 (<[a2:=v2]{Γ}>m).
Proof.
  intros ?? Ha ? (w2&?&Hw2) ? (w1&?&Hw1). red. unfold insertE, mem_insert.
  destruct Ha as [<-|?]; [|erewrite cmap_lookup_alter_disjoint
    by eauto using of_val_flatten_unshared; eauto].
  simplify_equality.
  assert (ctree_Forall (λ γb, Some Writable ⊆ pbit_kind γb)
    (of_val Γ (tagged_perm <$> ctree_flatten w2) v2)).
  { erewrite ctree_flatten_of_val by eauto. generalize (val_flatten Γ v2).
    induction Hw2; intros [|??]; simpl; constructor; auto. }
  destruct (decide (addr_is_obj a1)).
  { erewrite cmap_lookup_alter by eauto; eauto. }
  erewrite cmap_lookup_alter_not_obj by eauto using of_val_flatten_unshared.
  eauto using ctree_lookup_byte_after_Forall.
Qed.
Lemma mem_dom_insert Γ m a v :
  dom indexset (<[a:=v]{Γ}>m) = dom indexset m.
Proof. destruct m as [m]; simpl; apply dom_alter_L. Qed.

(** ** Locks *)
Lemma elem_of_mem_locks m o i :
  (o,i) ∈ mem_locks m ↔
    match cmap_car m !! o with
    | Some (Obj w μ) => pbit_locked <$> ctree_flatten w !! i = Some true
    | _ => False
    end.
Proof.
  destruct m as [m]; unfold elem_of, lockset_elem_of; simpl; rewrite lookup_omap.
  destruct (m !! o) as [[|w μ]|]; simplify_equality'; try naive_solver; split.
  { intros (ω&Hω&?); simplify_option_eq.
    by rewrite <-list_lookup_fmap, <-elem_of_bools_to_natset. }
  intros Hi. exists (bools_to_natset (pbit_locked <$> ctree_flatten w)).
  rewrite <-list_lookup_fmap, <-elem_of_bools_to_natset in Hi.
  by rewrite option_guard_True by set_solver.
Qed.
Lemma mem_locks_valid Γ m : ✓ Γ → ✓{Γ} m → ✓{Γ,'{m}} (mem_locks m).
Proof.
  intros ?? o i; rewrite elem_of_mem_locks. unfold typed, index_typed.
  destruct m as [m]; simpl; rewrite lookup_fmap; intros Ho.
  destruct (m !! o) as [[|w μ]|] eqn:?; try done.
  destruct (cmap_valid_Obj Γ '{CMap m} (CMap m) o w μ)
    as (τ&?&_&?&_); simplify_type_equality'; auto.
  exists τ; split_and ?; [naive_solver|eauto using ctree_typed_type_valid|].
  destruct (ctree_flatten w !! _) as [?|] eqn:?; simplify_equality'.
  erewrite <-ctree_flatten_length by eauto; eauto using lookup_lt_Some.
Qed.
Lemma mem_locks_empty : mem_locks ∅ = ∅.
Proof. apply dsig_eq; unfold mem_locks; simpl. by rewrite omap_empty. Qed.
Lemma mem_locks_erase m : mem_locks (cmap_erase m) = mem_locks m.
Proof.
  destruct m as [m]; f_equal'; apply dsig_eq; simpl; apply map_eq; intros o.
  rewrite !lookup_omap. by destruct (m !! o) as [[]|].
Qed.
Lemma mem_unlock_empty m : mem_unlock ∅ m = m.
Proof.
  destruct m as [m]; unfold mem_unlock; sep_unfold; f_equal.
  apply map_eq; intros i. by rewrite lookup_merge, lookup_empty; destruct (m !! i). 
Qed.
Lemma mem_lock_memenv_of Γ Δ m a  :
  ✓ Γ → ✓{Γ,Δ} m → mem_writable Γ a m → '{mem_lock Γ a m} = '{m}.
Proof.
  unfold mem_lock. intros ?? (v&?&?).
  by erewrite cmap_alter_memenv_of by eauto using ctree_map_type_of.
Qed.
Lemma mem_lock_forward Γ Δ m a  :
  ✓ Γ → ✓{Γ,Δ} m → mem_writable Γ a m → '{m} ⇒ₘ '{mem_lock Γ a m}.
Proof. intros. by erewrite mem_lock_memenv_of by eauto. Qed.
Lemma mem_lock_valid Γ Δ m a :
  ✓ Γ → ✓{Γ,Δ} m → mem_writable Γ a m → ✓{Γ,Δ} (mem_lock Γ a m).
Proof.
  intros ?? (w&?&?). assert ((Γ,Δ) ⊢ ctree_map pbit_lock w : type_of w).
  { eapply ctree_map_typed; eauto using cmap_lookup_Some, pbits_lock_valid,
      pbit_lock_indetified, ctree_flatten_valid, pbit_lock_mapped. }
  eapply cmap_alter_valid, ctree_Forall_not; eauto. rewrite ctree_flatten_map.
  eauto using pbits_lock_mapped, pbits_mapped, pbits_kind_weaken.
Qed.
Lemma mem_lock_valid' Γ m a :
  ✓ Γ → ✓{Γ} m → mem_writable Γ a m → ✓{Γ} (mem_lock Γ a m).
Proof.
  unfold valid at 2 3, cmap_valid'; intros.
  erewrite mem_lock_memenv_of by eauto. eauto using mem_lock_valid.
Qed.
Lemma mem_erase_lock Γ m a :
  cmap_erase (mem_lock Γ a m) = mem_lock Γ a (cmap_erase m).
Proof. apply cmap_erase_alter. Qed.
Lemma mem_lock_force Γ m a : dom indexset (mem_lock Γ a m) = dom indexset m.
Proof. destruct m; simpl; apply dom_alter_L. Qed.

Lemma ctree_unlock_typed Γ Δ w τ βs :
  ✓ Γ → (Γ,Δ) ⊢ w : τ → length βs = bit_size_of Γ τ →
  (Γ,Δ) ⊢ ctree_merge pbit_unlock_if w βs : τ.
Proof.
  intros HΓ Hw. revert w τ Hw βs.
  refine (ctree_typed_ind _ _ _ _ _ _ _ _); simpl.
  * intros; typed_constructor; auto using pbits_unlock_valid.
  * intros ws τ Hws IH Hlen βs. rewrite bit_size_of_array.
    intros Hβs; typed_constructor; auto.
    + clear Hlen IH. revert βs Hβs. induction Hws; intros; f_equal'; auto.
    + clear Hlen. revert βs Hβs.
      induction Hws; intros; decompose_Forall_hyps; constructor; auto.
  * intros t wγbss τs Ht Hws IH Hγbss Hindet Hlen βs.
    erewrite bit_size_of_struct by eauto. intros Hβs.
    typed_constructor; eauto; clear Ht.
    + clear Hγbss Hindet. revert wγbss βs Hws IH Hβs Hlen.
      unfold field_bit_padding. induction (bit_size_of_fields _ τs HΓ);
        intros [|[??] ?] ?????; decompose_Forall_hyps;
        erewrite ?type_of_correct by eauto; constructor; simpl; auto.
    + clear Hβs. revert βs. elim Hγbss; [|intros [??] ????];
        constructor; simpl; auto using pbits_unlock_valid.
    + clear Hβs. revert βs. elim Hindet; [|intros [??] ????]; constructor;
        simpl in *; auto; rewrite pbit_indetify_unlock; congruence.
    + clear Hγbss IH Hindet. revert wγbss βs Hws Hβs Hlen.
      unfold field_bit_padding. induction (bit_size_of_fields _ τs HΓ);
        intros [|[??] ?] ????; decompose_Forall_hyps;
        erewrite ?type_of_correct by eauto; f_equal; auto.
  * intros t i τs w γbs τ ??????? Hc βs ?. typed_constructor; eauto.
    + auto using pbits_unlock_valid.
    + rewrite pbit_indetify_unlock; congruence.
    + solve_length.
    + rewrite ctree_flatten_merge.
      intros [??]; destruct Hc; split; eapply pbits_unlock_mapped; 
        eauto using ctree_flatten_valid, pbits_valid_sep_valid.
  * intros; typed_constructor; eauto using pbits_unlock_valid.
Qed.
Lemma ctree_unlock_type_of w βs :
  type_of (ctree_merge pbit_unlock_if w βs) = type_of w.
Proof.
  destruct w as [|τ ws| | |]; f_equal'.
  revert βs. induction ws; intros; f_equal'; auto.
Qed.
Lemma mem_unlock_memenv_of m Ω : '{mem_unlock Ω m} = '{m}.
Proof.
  apply map_eq; intros o. destruct m as [m], Ω as [Ω]; simpl.
  rewrite !lookup_fmap, lookup_merge by done.
  destruct (m !! o) as [[|w μ]|], (Ω !! o) as [ω|]; simplify_equality'; f_equal.
  by rewrite ctree_unlock_type_of.
Qed.
Lemma mem_unlock_forward m Ω : '{m} ⇒ₘ '{mem_unlock Ω m}.
Proof. by rewrite mem_unlock_memenv_of. Qed.
Lemma mem_unlock_valid Γ Δ m Ω : ✓ Γ → ✓{Γ,Δ} m → ✓{Γ,Δ} (mem_unlock Ω m).
Proof.
  destruct m as [m], Ω as [Ω HΩ'];
    intros ? (HΔ&Hm1&Hm2); split_and !; simpl in *; auto.
  { intros o τ; rewrite lookup_merge by done; intros.
    destruct (Ω !! o), (m !! o) as [[]|] eqn:?; simplify_equality'; eauto. }
  intros o w μ; rewrite lookup_merge by done; intros.
  destruct (m !! o) as [[|w' ?]|] eqn:Hw',
    (Ω !! o) as [ω|] eqn:Hω; simplify_equality'; eauto.
  destruct (Hm2 o w' μ) as (τ&?&?&?&Hemp); auto.
  exists τ; split_and ?; auto using ctree_unlock_typed, natset_to_bools_length.
  rewrite ctree_flatten_merge; contradict Hemp.
  eapply pbits_unlock_empty_inv;
    eauto using ctree_flatten_valid, pbits_valid_sep_valid.
Qed.
Lemma mem_unlock_valid' Γ m Ω : ✓ Γ → ✓{Γ} m → ✓{Γ} (mem_unlock Ω m).
Proof.
  unfold valid at 2 3, cmap_valid'; intros.
  rewrite mem_unlock_memenv_of. eauto using mem_unlock_valid.
Qed.
Lemma mem_erase_unlock m Ω :
  cmap_erase (mem_unlock Ω m) = mem_unlock Ω (cmap_erase m).
Proof.
  destruct m as [m], Ω as [Ω]; f_equal'; apply map_eq; intros o.
  rewrite !lookup_omap, !lookup_merge, lookup_omap by done.
  by destruct (m !! o) as [[]|], (Ω !! o).
Qed.
Lemma mem_unlock_force Ω m : dom indexset (mem_unlock Ω m) = dom indexset m.
Proof.
  destruct m as [m], Ω as [Ω]; simpl; apply set_eq; intros o.
  rewrite !elem_of_dom; unfold is_Some; rewrite lookup_merge by done.
  destruct (Ω !! o), (m !! o) as [[]|]; naive_solver.
Qed.
Lemma elem_of_lock_singleton Γ a o i :
  (o,i) ∈ lock_singleton Γ a ↔
    o = addr_index a ∧ addr_object_offset Γ a ≤ i
    < addr_object_offset Γ a + ptr_bit_size_of Γ (type_of a).
Proof.
  destruct (decide (ptr_bit_size_of Γ (type_of a) = 0)) as [Hsz|].
  { split; [|lia]. unfold lock_singleton.
    destruct (decide _) as [[]|]; [|set_solver].
    rewrite Hsz; simpl; rewrite (right_id_L [] (++)).
    apply elem_of_equiv_empty_L; intros j.
    by rewrite elem_of_bools_to_natset, lookup_replicate; intros []. }
  assert (bools_to_natset (replicate (addr_object_offset Γ a) false
    ++ replicate (ptr_bit_size_of Γ (type_of a)) true) ≠ ∅).
  { rewrite elem_of_equiv_empty_L.
    intros Hx; destruct (Hx (addr_object_offset Γ a)).
    by rewrite elem_of_bools_to_natset,
      lookup_app_r, lookup_replicate_2 by solve_length. }
  unfold lock_singleton; case_decide; [split|done].
  * intros (?&?&Hi); simplify_map_eq; split; auto.
    rewrite elem_of_bools_to_natset in Hi.
    destruct (decide (i < addr_object_offset Γ a)).
    { by rewrite lookup_app_l, lookup_replicate_2 in Hi by solve_length. }
    rewrite lookup_app_r, lookup_replicate in Hi by solve_length.
    destruct Hi as [_ Hi]; revert Hi; solve_length.
  * intros (->&?&?); eexists; simplify_map_eq; split; auto.
    by rewrite elem_of_bools_to_natset,
      lookup_app_r, lookup_replicate_2 by solve_length.
Qed.
Lemma elem_of_lock_singleton_typed Γ Δ a τ o i :
  ✓ Γ → (Γ,Δ) ⊢ a : TType τ → (o,i) ∈ lock_singleton Γ a ↔ o = addr_index a ∧
    addr_object_offset Γ a ≤ i < addr_object_offset Γ a + bit_size_of Γ τ.
Proof. intros. rewrite elem_of_lock_singleton; by simplify_type_equality. Qed.
Lemma lock_singleton_valid Γ Δ a τ :
  ✓ Γ → (Γ,Δ) ⊢ a : TType τ → addr_strict Γ a → ✓{Γ,Δ} (lock_singleton Γ a).
Proof.
  intros ??? o i. rewrite elem_of_lock_singleton_typed by eauto.
  intros (->&?&?); exists (addr_type_object a); simpl; split_and ?;
    eauto using addr_typed_index,addr_typed_type_object_valid.
  eapply Nat.lt_le_trans; [|eapply addr_object_offset_bit_size; eauto].
  simpl; lia.
Qed.
Lemma lock_singleton_disjoint Γ Δ a1 a2 τ1 τ2 :
  ✓ Γ → (Γ,Δ) ⊢ a1 : TType τ1 → addr_strict Γ a1 →
  (Γ,Δ) ⊢ a2 : TType τ2 → addr_strict Γ a2 →
  a1 ##{Γ} a2 → lock_singleton Γ a1 ∩ lock_singleton Γ a2 = ∅.
Proof.
  intros. rewrite lockset_eq. intros. split.
  - rewrite elem_of_intersection, !elem_of_lock_singleton_typed by eauto.
    intros [(->&?&?) (?&?&?)].
    destruct (addr_disjoint_object_offset Γ Δ a1 a2 τ1 τ2); try done; lia.
  - set_solver.
Qed.
Lemma mem_unlock_union_locks Ω1 Ω2 m :
  mem_unlock (Ω1 ∪ Ω2) m = mem_unlock Ω1 (mem_unlock Ω2 m).
Proof.
  destruct m as [m], Ω1 as [Ω1], Ω2 as [Ω2]; f_equal'; apply map_eq; intros o.
  rewrite lookup_merge, !lookup_union_with, !lookup_merge by done.
  destruct (m !! o) as [[|w μ]|], (Ω1 !! o) as [ω1|],
    (Ω2 !! o) as [ω2|]; do 2 f_equal'; auto.
  by rewrite (comm_L (∪)), ctree_flatten_merge, zip_with_length_l_eq,
    (ctree_merge_merge _ _ pbit_unlock_if orb), natset_to_bools_union
    by auto using natset_to_bools_length, pbits_unlock_orb.
Qed.
Lemma mem_locks_alloc Γ Δ m o μ γ v τ :
  ✓ Γ → (Γ,Δ) ⊢ v : τ → perm_locked γ = false →
  o ∉ dom indexset m → mem_locks (mem_alloc Γ o μ γ v m) = mem_locks m.
Proof.
  rewrite cmap_dom_alt, lockset_eq; intros ???? o' i.
  rewrite !elem_of_mem_locks. destruct m as [m]; simplify_type_equality'.
  destruct (decide (o = o')); simplify_map_eq; split; try done.
  erewrite ctree_flatten_of_val by eauto.
  unfold pbit_locked; rewrite <-list_lookup_fmap, list_fmap_compose,
    fmap_zip_with_l, list_lookup_fmap, fmap_Some by auto.
  setoid_rewrite lookup_replicate; intros (?&[??]&?); congruence.
Qed.
Lemma mem_locks_alloc_list Γ Δ m vs os τs :
  ✓ Γ → Forall_fresh (dom indexset m) os → length os = length vs →
  (Γ,Δ) ⊢* vs :* τs → mem_locks (mem_alloc_list Γ os vs m) = mem_locks m.
Proof.
  rewrite <-Forall2_same_length; intros ? Hos Hovs Hvs; revert os m Hos Hovs.
  induction Hvs as [|v τ vs τs ?? IH];
    intros ? m [|o os ???] ?; decompose_Forall_hyps; auto.
  assert (o ∉ dom indexset (mem_alloc_list Γ os vs m)).
  { rewrite mem_dom_alloc_list by eauto using Forall2_length; set_solver. }
  by erewrite mem_locks_alloc, IH by eauto.
Qed.
Lemma mem_locks_free m o μ :
  mem_freeable_perm o μ m → mem_locks (mem_free o m) = mem_locks m.
Proof.
  intros (w&?&Hperm). apply lockset_eq; intros o' i.
  rewrite !elem_of_mem_locks. destruct m as [m]; simplify_equality'.
  destruct (decide (o = o')); simplify_map_eq; split; try done.
  rewrite fmap_Some; intros ([x b]&?&?); decompose_Forall_hyps.
Qed.
Lemma mem_locks_alter_ref Γ Δ g o r m w τ σ o' i :
  ✓Γ → ✓{Γ,Δ} m → Δ ⊢ o : τ → Γ ⊢ r : τ ↣ σ →
  m !!{Γ} (o,r) = Some w → (Γ,Δ) ⊢ g w : σ →
  (o',i) ∈ mem_locks (cmap_alter_ref Γ g o r m) ↔
    (o',i) ∈ mem_locks m ∧ o' ≠ o ∨
    (o',i) ∈ mem_locks m ∧ o' = o ∧ i < ref_object_offset Γ r ∨
    o' = o ∧
      ref_object_offset Γ r ≤ i < ref_object_offset Γ r + bit_size_of Γ σ ∧
      pbit_locked <$> ctree_flatten (g w)
      !! (i - ref_object_offset Γ r) = Some true ∨
    (o',i) ∈ mem_locks m ∧ o' = o ∧
      ref_object_offset Γ r + bit_size_of Γ σ ≤ i.
Proof.
  unfold lookupE, cmap_lookup_ref; intros ? Hm ????; simplify_equality'.
  destruct (cmap_car m !! o) as [[|w' μ]|] eqn:?; simplify_equality'.
  destruct (cmap_valid_Obj Γ Δ m o w' μ) as (τ'&?&_&?&_); auto.
  rewrite !elem_of_mem_locks; destruct m as [m]; simplify_equality'.
  destruct (decide (o = o')); simplify_map_eq;
    [rewrite or_r by tauto|destruct (m !! o) as [[]|]; naive_solver].
  simplify_type_equality. unfold pbit_locked.
  erewrite <-!list_lookup_fmap, !list_fmap_compose, ctree_alter_perm_flatten,
    !list_lookup_fmap by eauto using ctree_lookup_typed.
  assert (ref_object_offset Γ r + bit_size_of Γ σ ≤ bit_size_of Γ τ)
    by eauto using ref_object_offset_size'.
  destruct (le_lt_dec (ref_object_offset Γ r) i);
    [|rewrite lookup_app_l, lookup_take by solve_length; intuition lia].
  rewrite lookup_app_r, take_length_le by solve_length.
  destruct (le_lt_dec (ref_object_offset Γ r + bit_size_of Γ σ) i);
    [|rewrite lookup_app_l by auto; intuition lia].
  erewrite lookup_app_r, ctree_flatten_length, lookup_drop by eauto.
  replace (ref_object_offset Γ r + bit_size_of Γ σ
    + (i - ref_object_offset Γ r - bit_size_of Γ σ)) with i by lia.
  intuition lia.
Qed.
Lemma mem_locks_alter Γ Δ g a m w τ o i :
  ✓Γ → ✓{Γ,Δ} m → (Γ,Δ) ⊢ a : TType τ → m !!{Γ} a = Some w → (Γ,Δ) ⊢ g w : τ →
  (o,i) ∈ mem_locks (cmap_alter Γ g a m) ↔
    (o,i) ∈ mem_locks m ∧ o ≠ addr_index a ∨
    (o,i) ∈ mem_locks m ∧ o = addr_index a ∧ i < addr_object_offset Γ a ∨
    o = addr_index a ∧
      addr_object_offset Γ a ≤ i < addr_object_offset Γ a + bit_size_of Γ τ ∧
      pbit_locked <$> ctree_flatten (g w)
      !! (i - addr_object_offset Γ a) = Some true ∨
    (o,i) ∈ mem_locks m ∧ o = addr_index a ∧
      addr_object_offset Γ a + bit_size_of Γ τ ≤ i.
Proof.
  unfold lookupE, cmap_lookup, lookupE, cmap_lookup_ref; intros ? Hm ???.
  case_option_guard; simplify_equality'.
  erewrite addr_object_offset_alt by eauto.
  destruct (cmap_car m !! addr_index a) as [[|w' μ]|] eqn:?; simplify_equality'.
  destruct (cmap_valid_Obj Γ Δ m (addr_index a) w' μ) as (τ'&?&_&?&_); auto.
  assert (Δ ⊢ addr_index a : addr_type_object a)
    by eauto using addr_typed_index; simplify_type_equality.
  destruct (w' !!{Γ} addr_ref Γ a) as [w''|] eqn:?; simplify_equality'.
  assert ((Γ,Δ) ⊢ w'' : addr_type_base a)
    by eauto using ctree_lookup_typed, addr_typed_ref_typed.
  rewrite !elem_of_mem_locks. destruct m as [m]; simplify_equality'.
  destruct (decide (o = addr_index a)); simplify_map_eq;
    [rewrite or_r by tauto|destruct (m !! o) as [[]|]; naive_solver].
  unfold pbit_locked; rewrite <-!list_lookup_fmap, !list_fmap_compose.
  erewrite ctree_alter_perm_flatten, !list_lookup_fmap by eauto.
  assert (ref_object_offset Γ (addr_ref Γ a) + bit_size_of Γ (addr_type_base a)
    ≤ bit_size_of Γ (addr_type_object a))
    by eauto using ref_object_offset_size', addr_typed_ref_typed.
  assert (addr_ref_byte Γ a * char_bits + bit_size_of Γ τ
    ≤ bit_size_of Γ (addr_type_base a)) as Hbyte by eauto using addr_bit_range.
  destruct (le_lt_dec (ref_object_offset Γ (addr_ref Γ a)) i);
    [|rewrite lookup_app_l, lookup_take by solve_length; intuition lia].
  rewrite lookup_app_r, take_length_le by solve_length.
  case_decide; repeat case_option_guard; simplify_equality'.
  { assert (τ = addr_type_base a) by eauto using addr_is_obj_type; subst.
    erewrite addr_is_obj_ref_byte, Nat.mul_0_l, Nat.add_0_r by eauto.
    destruct (le_lt_dec (ref_object_offset Γ (addr_ref Γ a) +
      addr_ref_byte Γ a * char_bits + bit_size_of Γ (addr_type_base a)) i);
      [|rewrite lookup_app_l by auto; intuition lia].
    erewrite lookup_app_r, ctree_flatten_length, lookup_drop by eauto.
    replace (ref_object_offset Γ (addr_ref Γ a)
      + bit_size_of Γ (addr_type_base a)
      + (i - ref_object_offset Γ (addr_ref Γ a)
         - bit_size_of Γ (addr_type_base a))) with i by lia.
    intuition lia. }
  assert (τ = ucharT) by eauto using addr_not_is_obj_type; subst.
  rewrite bit_size_of_char; rewrite bit_size_of_char in Hbyte.
  erewrite <-!list_lookup_fmap, !fmap_app, !ctree_alter_byte_perm_flatten,
    <-!list_fmap_compose, !fmap_app by eauto; fold (@pbit_locked K).  
  erewrite <-!(ctree_lookup_flatten _ _ w') by eauto.
  rewrite take_mask, drop_mask, !pbits_locked_mask, <-!fmap_app.
  rewrite take_take, Min.min_l, (take_drop_commute _ (bit_size_of _ _)),
    drop_drop, <-!(assoc_L (++)), drop_take_drop by lia.
  rewrite !list_lookup_fmap.
  destruct (le_lt_dec (ref_object_offset Γ (addr_ref Γ a) +
      addr_ref_byte Γ a * char_bits) i);
    [rewrite or_r by lia|rewrite lookup_app_l, lookup_take,
       lookup_drop, <-le_plus_minus by solve_length; intuition lia].
  rewrite lookup_app_r, take_length_le by solve_length.
  rewrite Nat.sub_add_distr.
  destruct (le_lt_dec (ref_object_offset Γ (addr_ref Γ a)
    + addr_ref_byte Γ a * char_bits + char_bits) i);
    [|rewrite lookup_app_l by solve_length; intuition lia].
  erewrite lookup_app_r, ctree_flatten_length,
    bit_size_of_char, lookup_drop by eauto.
  replace (ref_object_offset Γ (addr_ref Γ a)
    + (char_bits + addr_ref_byte Γ a * char_bits)
    + (i - ref_object_offset Γ (addr_ref Γ a) - addr_ref_byte Γ a * char_bits -
       char_bits)) with i by lia.
  intuition lia.
Qed.
Lemma mem_Readable_locks Γ Δ m a w τ i :
  ✓ Γ → ✓{Γ,Δ} m → m !!{Γ} a = Some w → (Γ,Δ) ⊢ a : TType τ →
  ctree_Forall (λ γb, Some Readable ⊆ pbit_kind γb) w →
  (addr_index a,i) ∈ mem_locks m →
  i < addr_object_offset Γ a ∨ addr_object_offset Γ a + bit_size_of Γ τ ≤ i.
Proof.
  unfold lookupE, cmap_lookup, lookupE, cmap_lookup_ref.
  rewrite elem_of_mem_locks.
  intros ? Hm Hw ???; case_option_guard; simplify_equality'.
  destruct (decide (addr_object_offset Γ a ≤ i
    < addr_object_offset Γ a + bit_size_of Γ τ)) as [Hi|]; [exfalso|lia].
  erewrite addr_object_offset_alt in Hi by eauto.
  destruct (cmap_car m !! _) as [[|w' μ]|] eqn:?; simplify_equality'; try done.
  assert (Δ ⊢ addr_index a : addr_type_object a)
    by eauto using addr_typed_index.
  destruct (cmap_valid_Obj Γ Δ m (addr_index a) w' μ)
    as (?&?&_&?&_); auto; simplify_type_equality'.
  destruct (w' !!{Γ} addr_ref Γ a) as [w''|] eqn:Hw''; simplify_equality'.
  assert ((Γ,Δ) ⊢ w'' : addr_type_base a)
    by eauto using ctree_lookup_typed, addr_typed_ref_typed.
  assert (addr_ref_byte Γ a * char_bits + bit_size_of Γ τ
    ≤ bit_size_of Γ (addr_type_base a)) by eauto using addr_bit_range.
  assert (pbit_locked <$> ctree_flatten w''
    !! (i - ref_object_offset Γ (addr_ref Γ a)) = Some true) as Hperm.
  { erewrite <-(ctree_lookup_flatten _ _ w') by eauto.
    rewrite <-list_lookup_fmap, pbits_locked_mask, fmap_take, fmap_drop.
    rewrite lookup_take, lookup_drop, <-le_plus_minus by solve_length.
    by rewrite list_lookup_fmap. }
  case_decide; repeat case_option_guard; simplify_equality'.
  * erewrite addr_is_obj_ref_byte, Nat.mul_0_l, Nat.add_0_r in Hi by eauto.
    assert (τ = addr_type_base a) by eauto using addr_is_obj_type; subst.
    destruct (ctree_flatten w !! _) as [γb|] eqn:?; decompose_Forall_hyps.
    by rewrite pbit_Readable_locked in Hperm by done.
  * assert (τ = ucharT) by eauto using addr_not_is_obj_type; subst.
    rewrite bit_size_of_char in Hi.
    assert (pbit_locked <$> ctree_flatten w
      !! (i - ref_object_offset Γ (addr_ref Γ a)
            - addr_ref_byte Γ a * char_bits) = Some true) as Hperm'.
    { erewrite <-ctree_lookup_byte_flatten by eauto.
      by rewrite lookup_take, lookup_drop, <-le_plus_minus by solve_length. }
    destruct (ctree_flatten w !! _) as [γb|] eqn:?; decompose_Forall_hyps.
    by rewrite pbit_Readable_locked in Hperm' by done.
Qed.
Lemma mem_lookup_locks Γ Δ m a v τ :
  ✓ Γ → ✓{Γ,Δ} m → m !!{Γ} a = Some v → (Γ,Δ) ⊢ a : TType τ →
  mem_locks m ∩ lock_singleton Γ a = ∅.
Proof.
  unfold lookupE, mem_lookup;
    rewrite bind_Some; intros ?? (w&?&?) ?; simplify_option_eq.
  apply elem_of_equiv_empty_L; intros [o i].
  rewrite not_elem_of_intersection,
    elem_of_lock_singleton; simplify_type_equality'.
  destruct (decide ((o,i) ∈ mem_locks m)); [right; intros (->&?&?)|tauto].
  destruct (mem_Readable_locks Γ Δ m a w τ i); auto with lia.
Qed.
Lemma mem_locks_force Γ Δ a m v τ :
  ✓ Γ → ✓{Γ,Δ} m → (Γ,Δ) ⊢ a : TType τ →
  m !!{Γ} a = Some v → mem_locks (mem_force Γ a m) = mem_locks m.
Proof.
  unfold lookupE, mem_lookup, mem_force, lookupE, cmap_lookup; intros.
  case_option_guard; simplify_equality'.
  destruct (m !!{Γ} _) as [w|] eqn:?; simplify_equality'.
  destruct (cmap_lookup_ref_Some Γ Δ m (addr_index a)
    (addr_ref Γ a) w) as (τ'&σ&?&?&?); eauto.
  apply set_eq; intros [o i].
  erewrite mem_locks_alter_ref
    by eauto using addr_typed_index, addr_typed_ref_typed.
  destruct (decide (o = addr_index a)) as [->|]; [|tauto].
  destruct (decide (ref_object_offset Γ (addr_ref Γ a) ≤ i
    < ref_object_offset Γ (addr_ref Γ a) + bit_size_of Γ σ)).
  { rewrite 2!or_r, or_l, elem_of_mem_locks by intuition lia.
    unfold lookupE, cmap_lookup_ref in *; simplify_equality'.
    destruct (cmap_car m !! _) as [[|w' μ]|] eqn:?; simplify_equality'.
    destruct (cmap_valid_Obj Γ Δ m (addr_index a) w' μ)
      as (?&?&_&?&_); simplify_type_equality'; eauto.
    erewrite <-ctree_lookup_flatten by eauto.
    rewrite <-list_lookup_fmap, pbits_locked_mask, list_lookup_fmap.
    rewrite lookup_take, lookup_drop, le_plus_minus_r by lia.
    intuition lia. }
  destruct (decide (i < ref_object_offset Γ (addr_ref Γ a))); intuition lia.
Qed.
Lemma mem_locks_insert Γ Δ a m v τ :
  ✓ Γ → ✓{Γ,Δ} m → (Γ,Δ) ⊢ a : TType τ → mem_writable Γ a m → (Γ,Δ) ⊢ v : τ →
  mem_locks (<[a:=v]{Γ}>m) = mem_locks m.
Proof.
  unfold insertE, mem_insert; intros ??? (w&?&Hw) ?.
  apply set_eq; intros [o i]; erewrite mem_locks_alter by eauto.
  destruct (decide (o = addr_index a)) as [->|]; [|tauto].
  destruct (decide (addr_object_offset Γ a ≤ i
    < addr_object_offset Γ a + bit_size_of Γ τ));
    [|destruct (decide (i < addr_object_offset Γ a)); intuition lia].
  assert (ctree_Forall (λ γb, Some Readable ⊆ pbit_kind γb)
    (of_val Γ (tagged_perm <$> ctree_flatten w) v)).
  { erewrite ctree_flatten_of_val by eauto. generalize (val_flatten Γ v).
    induction Hw; intros [|??]; simpl; constructor; auto.
    by transitivity (Some Writable). }
  rewrite pbits_Readable_locked by auto.
  assert ((addr_index a,i) ∈ mem_locks m →
    i < addr_object_offset Γ a ∨ addr_object_offset Γ a + bit_size_of Γ τ ≤ i)
    by eauto using mem_Readable_locks, pbits_kind_weaken; intuition congruence.
Qed.
Lemma mem_locks_lock Γ Δ a m τ :
  ✓ Γ → ✓{Γ,Δ} m → (Γ,Δ) ⊢ a : TType τ → mem_writable Γ a m →
  mem_locks (mem_lock Γ a m) = mem_locks m ∪ lock_singleton Γ a.
Proof.
  unfold mem_lock; intros ??? (w&?&?).
  assert ((Γ,Δ) ⊢ ctree_map pbit_lock w : τ).
  { eapply ctree_map_typed; eauto using cmap_lookup_Some, pbits_lock_valid,
      pbit_lock_indetified, ctree_flatten_valid, pbit_lock_mapped. }
  apply set_eq; intros [o i]; erewrite mem_locks_alter by eauto.
  rewrite elem_of_union, elem_of_lock_singleton; simplify_type_equality'.
  destruct (decide (o = addr_index a)) as [->|]; [|tauto].
  destruct (decide (addr_object_offset Γ a ≤ i
    < addr_object_offset Γ a + bit_size_of Γ τ));
    [|destruct (decide (i < addr_object_offset Γ a)); intuition lia].
  rewrite ctree_flatten_map, list_lookup_fmap, <-option_fmap_compose.
  destruct (lookup_lt_is_Some_2 (ctree_flatten w) (i - addr_object_offset Γ a))
    as [[x b] Hγb]; auto; rewrite Hγb; decompose_Forall_hyps.
  rewrite perm_locked_lock by done. intuition congruence.
Qed.
Lemma mem_locks_subseteq_inv Ω m o :
  Ω ⊆ mem_locks m →
  match `Ω !! o, cmap_car m !! o with
  | Some ω, Some (Obj w _) =>
     natset_to_bools (length (ctree_flatten w)) ω
     =.>* pbit_locked <$> ctree_flatten w
  | Some ω, None => False
  | _, _ => True
  end.
Proof.
  destruct m as [m], Ω as [Ω HΩ]; intros HΩm; simpl.
  destruct (m !! o) as [[|w μ]|] eqn:?, (Ω !! o) as [ω|] eqn:?; try done.
  * apply Forall2_same_length_lookup_2.
    { rewrite fmap_length; auto using natset_to_bools_length. }
    intros i [] []; try done.
    destruct (decide (i < length (ctree_flatten w)));
      [|by rewrite lookup_natset_to_bools_ge by lia].
    rewrite lookup_natset_to_bools_true by done; intros.
    destruct (HΩm (o,i)) as (ω'&?&Hω'); [by exists ω|].
    simplify_map_eq; simplify_option_eq.
    rewrite elem_of_bools_to_natset in Hω'; congruence.
  * destruct (set_choose_L ω) as [i ?].
    { by apply (bool_decide_unpack _ HΩ o). }
    destruct (HΩm (o,i)) as (ω'&?&?); [by exists ω|]; simplify_map_eq.
Qed.
Lemma mem_locks_unlock Ω m :
  Ω ⊆ mem_locks m → mem_locks (mem_unlock Ω m) = mem_locks m ∖ Ω.
Proof.
  intros HΩm. apply set_eq; intros [o i].
  apply (mem_locks_subseteq_inv _ _ o) in HΩm; simpl in *.
  rewrite elem_of_difference, !elem_of_mem_locks.
  destruct m as [m], Ω as [Ω HΩ]; unfold elem_of, lockset_elem_of;
    simplify_equality'; rewrite lookup_merge by done.
  destruct (m !! o) as [[|w μ]|] eqn:?,
    (Ω !! o) as [ω|] eqn:?; split; try naive_solver; simpl.
  * rewrite ctree_flatten_merge, lookup_zip_with; intros Hw.
    destruct (ctree_flatten w !! i) as [γb|] eqn:Hγb; simplify_equality'.
    destruct (natset_to_bools (length (ctree_flatten w)) ω !! i)
      as [α|] eqn:Hα; simplify_equality'.
    assert (∃ α', pbit_locked <$> ctree_flatten w !! i = Some α' ∧ α =.> α')
      as (α'&?&?) by (rewrite <-list_lookup_fmap; decompose_Forall_hyps; eauto).
    destruct α; simplify_option_eq.
    { by rewrite perm_locked_unlock in Hw. }
    rewrite lookup_natset_to_bools_false in Hα by eauto using lookup_lt_Some.
    split; [simplify_option_eq; congruence|naive_solver].
  * intros [??]; simplify_equality'.
    destruct (ctree_flatten w !! i) as [γbs|] eqn:Hγbs; simplify_equality'.
    rewrite ctree_flatten_merge, lookup_zip_with, Hγbs; simpl.
    assert (natset_to_bools (length (ctree_flatten w)) ω !! i = Some false).
    { apply lookup_natset_to_bools_false; naive_solver eauto using lookup_lt_Some. }
    assert (∃ x, pbit_locked <$> ctree_flatten w !! i = Some x) as [x Hx].
    { rewrite <-list_lookup_fmap; decompose_Forall_hyps; eauto. }
    simplify_option_eq; congruence.
Qed.
Lemma mem_unlock_all_spec m : mem_unlock_all m = mem_unlock (mem_locks m) m.
Proof. done. Qed.
Lemma mem_unlock_all_spec_alt Ω m :
  mem_locks m = Ω → mem_unlock_all m = mem_unlock Ω m.
Proof. by intros <-. Qed. 
Lemma mem_unlock_all_empty_locks m : mem_locks m = ∅ → mem_unlock_all m = m.
Proof. by rewrite mem_unlock_all_spec; intros ->; rewrite mem_unlock_empty. Qed.
Lemma mem_unlock_all_empty : mem_unlock_all ∅ = ∅.
Proof. by rewrite mem_unlock_all_spec, mem_locks_empty, mem_unlock_empty. Qed.
Lemma mem_unlock_all_valid Γ Δ m : ✓ Γ → ✓{Γ,Δ} m → ✓{Γ,Δ} (mem_unlock_all m).
Proof. by apply mem_unlock_valid. Qed.
Lemma mem_erase_unlock_all m :
  cmap_erase (mem_unlock_all m) = mem_unlock_all (cmap_erase m).
Proof. by rewrite !mem_unlock_all_spec, mem_erase_unlock, mem_locks_erase. Qed.
Lemma mem_locks_unlock_all m : mem_locks (mem_unlock_all m) = ∅.
Proof. rewrite mem_unlock_all_spec,mem_locks_unlock by done. set_solver. Qed.
End memory.
