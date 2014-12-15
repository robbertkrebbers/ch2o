(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export values memory_map.
Require Import natmap.
Local Open Scope ctype_scope.

Section memory_operations.
  Context `{Env Ti}.

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

  Definition mem_allocable (o : index) (m : mem Ti) : Prop :=
    cmap_car m !! o = None.
  Definition mem_alloc (Γ : env Ti) (o : index)
      (malloc : bool) (τ : type Ti) (m : mem Ti) : mem Ti :=
    let (m) := m in CMap (<[o:=Obj (ctree_new Γ pbit_full τ) malloc]>m).

  Definition mem_free (o : index) (m : mem Ti) : mem Ti :=
    let (m) := m in
    CMap (alter (λ x,
      match x with Obj w _ => Freed (type_of w) | _ => x end) o m).
  Definition mem_freeable (a : addr Ti) (m : mem Ti) : Prop := ∃ w,
    (**i 1.) *) addr_is_top_array a ∧
    (**i 2.) *) cmap_car m !! addr_index a = Some (Obj w true) ∧
    (**i 3.) *) ctree_Forall (λ xb, tagged_perm xb = perm_full) w.

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
    dexist (omap (λ x,
      '(w,_) ← maybe2 Obj x;
      let βs := of_bools (pbit_locked <$> ctree_flatten w) in
      guard (βs ≠ ∅); Some βs
    ) m) _.
  Next Obligation.
    by intros o ω; rewrite lookup_omap, bind_Some;
      intros ([]&?&?); simplify_option_equality.
  Qed.
  Definition mem_lock (Γ : env Ti) : addr Ti → mem Ti → mem Ti :=
    cmap_alter Γ (ctree_map pbit_lock).
  Definition mem_unlock (Ω : lockset) (m : mem Ti) : mem Ti :=
    let (Ω,_) := Ω in let (m) := m in
    CMap $ merge (λ mω mx,
      match mω, mx with
      | Some ω, Some (Obj w β) =>
         let sz := length (ctree_flatten w) in
         Some (Obj (ctree_merge true pbit_unlock_if w (to_bools sz ω)) β)
      | _,_ => mx
      end) Ω m.
  Program Definition lock_singleton (Γ : env Ti) (a : addr Ti) : lockset :=
    let i := addr_object_offset Γ a in
    let n := bit_size_of' Γ a in
    let ω := of_bools (replicate i false ++ replicate n true) in
    (**i does not happen for typed addresses, then [n] is always positive *)
    if decide (ω ≠ ∅) then dexist {[ addr_index a, ω ]} _ else ∅.
  Next Obligation. by intros o ω ?; simplify_map_equality'. Qed.
End memory_operations.

Notation mem_unlock_all m := (mem_unlock (mem_locks m) m).
Notation mem_writable_all Γ m := (∀ o τ,
  '{m} ⊢ o : τ → mem_writable Γ (addr_top o τ) m).

Section memory.
Context `{EnvSpec Ti}.
Implicit Types Γ : env Ti.
Implicit Types Γm : memenv Ti.
Implicit Types τ : type Ti.
Implicit Types a : addr Ti.
Implicit Types p : ptr Ti.
Implicit Types w : mtree Ti.
Implicit Types v : val Ti.
Implicit Types m : mem Ti.
Implicit Types α β : bool.
Implicit Types βs : list bool.
Implicit Types xb : pbit Ti.
Implicit Types xbs : list (pbit Ti).
Implicit Types Ω : lockset.

Local Opaque nmap.Nempty.
Arguments union _ _ !_ !_ /.
Arguments difference _ _ !_ !_ /.
Arguments cmap_lookup _ _ _ !_ !_ /.

Hint Resolve Forall_app_2 Forall2_app.
Hint Immediate cmap_lookup_typed val_typed_type_valid.
Hint Extern 0 (Separation _) => apply (_ : Separation (pbit Ti)).
Hint Extern 0 (Separation _) => apply (_ : Separation bool).
Hint Extern 0 (Separation _) => apply (_ : Separation (map bool)).

Ltac solve_length := repeat first 
  [ rewrite take_length | rewrite drop_length | rewrite app_length
  | rewrite zip_with_length | rewrite replicate_length | rewrite resize_length
  | rewrite fmap_length | erewrite ctree_flatten_length by eauto
  | rewrite to_bools_length ]; lia.
Hint Extern 0 (length _ = _) => solve_length.
Hint Extern 0 (_ ≤ length _) => solve_length.
Hint Extern 0 (length _ ≤ _) => solve_length.

Lemma mem_writable_weaken Γ1 Γ2 Γm m a σ :
  ✓ Γ1 → (Γ1,Γm) ⊢ a : σ → mem_writable Γ1 a m → Γ1 ⊆ Γ2 → mem_writable Γ2 a m.
Proof. intros ?? (w&?&?) ?; exists w; eauto using cmap_lookup_weaken. Qed.
Lemma mem_writable_all_weaken Γ1 Γ2 m :
  ✓ Γ1 → ✓{Γ1} m → mem_writable_all Γ1 m → Γ1 ⊆ Γ2 → mem_writable_all Γ2 m.
Proof.
  intros ? Hm ?? o τ ?; eapply mem_writable_weaken; eauto using
    addr_top_typed, index_typed_representable, index_typed_valid.
Qed.
Lemma mem_empty_writable_all Γ : mem_writable_all Γ ∅.
Proof. intros ?? [??]; simplify_map_equality'. Qed.

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
Lemma mem_allocable_fresh m : mem_allocable (fresh (dom indexset m)) m.
Proof. eapply mem_allocable_alt, is_fresh. Qed.
Lemma mem_allocable_list_fresh m n :
  mem_allocable_list m (fresh_list n (dom indexset m)).
Proof.
  apply mem_allocable_list_alt; split; [apply fresh_list_nodup|].
  apply Forall_forall. intros o; simpl. rewrite mem_allocable_alt.
  apply fresh_list_is_fresh.
Qed.
Lemma mem_empty_allocable o : mem_allocable o (∅ : mem Ti).
Proof. by unfold mem_allocable; simplify_map_equality'. Qed.
Lemma mem_alloc_memenv_of Γ m o malloc τ :
  ✓ Γ → ✓{Γ} τ → '{mem_alloc Γ o malloc τ m} = <[o:=(τ,false)]>('{m}).
Proof.
  intros. apply map_eq; intros o'; destruct m as [m]; simpl.
  destruct (decide (o = o')); simplify_map_equality'; f_equal.
  by rewrite ctree_new_type_of by done.
Qed.
Lemma mem_alloc_index_typed_inv Γm o τ β o' τ' :
  o ≠ o' → <[o:=(τ,β)]>Γm ⊢ o' : τ' → Γm ⊢ o' : τ'.
Proof. by intros ? [β' ?]; exists β'; simplify_map_equality'. Qed.
Lemma mem_alloc_index_alive_neq Γm o τ β o' :
  Γm !! o = None → index_alive Γm o' → index_alive (<[o:=(τ,β)]>Γm) o'.
Proof. by intros ? [β' ?]; exists β'; simplify_map_equality'. Qed.
Lemma mem_alloc_index_alive_inv Γm o τ β o' :
  o ≠ o' → index_alive (<[o:=(τ,β)]>Γm) o' → index_alive Γm o'.
Proof. by intros ? [τ' ?]; exists τ'; simplify_map_equality'. Qed.
Lemma mem_alloc_index_typed Γm o τ β : <[o:=(τ,β)]>Γm ⊢ o : τ.
Proof. by exists β; simplify_map_equality'. Qed.
Lemma mem_alloc_index_alive Γm o τ : index_alive (<[o:=(τ,false)]>Γm) o.
Proof. by exists τ; simplify_map_equality'. Qed.
Lemma mem_alloc_forward Γm o τ : Γm !! o = None → Γm ⇒ₘ <[o:=(τ,false)]>Γm.
Proof.
  split.
  * by intros ?? [β' ?]; exists β'; simplify_map_equality'.
  * by intros ? τ' [??] [??]; exists τ'; simplify_map_equality'.
Qed.
Lemma mem_alloc_valid Γ Γm m o malloc τ :
  ✓ Γ → ✓{Γ,Γm} m → ✓{Γ} τ → Γm !! o = None → int_typed (size_of Γ τ) sptrT →
  ✓{Γ,<[o:=(τ,false)]>Γm} (mem_alloc Γ o malloc τ m).
Proof.
  destruct m as [m]; intros HΓ Hm Hx Hτ Hsz; split; simpl.
  { intros o' τ'; rewrite lookup_insert_Some;
      intros [[??]|[??]]; simplify_equality'.
    destruct (proj1 Hm o' τ') as (?&?&?&?); simplify_map_equality'; eauto 10
      using mem_alloc_forward, memenv_forward_typed, memenv_forward_alive. }
  intros o' w malloc'; rewrite lookup_insert_Some;
    intros [[??]|[??]]; simplify_equality'.
  { exists τ; split_ands; eauto 7 using (ctree_Forall_not _ _ Γm),
     ctree_new_typed, pbit_full_valid, ctree_new_Forall,
     mem_alloc_index_typed, mem_alloc_index_alive. }
  destruct (proj2 Hm o' w malloc')
    as (τ'&?&?&?&?&?); simplify_map_equality'; eauto.
  exists τ'; split_ands; eauto using ctree_typed_weaken, mem_alloc_forward,
    memenv_forward_typed, memenv_forward_alive, mem_alloc_index_alive_neq.
Qed.
Lemma mem_allocable_memenv_of m o : mem_allocable o m → '{m} !! o = None.
Proof.
  unfold mem_allocable. by intros; destruct m as [m]; simplify_map_equality'.
Qed.
Lemma mem_alloc_valid' Γ m o malloc τ :
  ✓ Γ → ✓{Γ} m → ✓{Γ} τ → mem_allocable o m →
  int_typed (size_of Γ τ) sptrT → ✓{Γ} (mem_alloc Γ o malloc τ m).
Proof.
  unfold valid at 2 4, cmap_valid'; intros. rewrite mem_alloc_memenv_of by done.
  eauto using mem_alloc_valid, mem_allocable_memenv_of.
Qed.
Hint Extern 10 => erewrite mem_alloc_memenv_of by eauto.
Lemma mem_alloc_index_typed' Γ m o malloc τ :
  ✓ Γ → ✓{Γ} τ → '{mem_alloc Γ o malloc τ m} ⊢ o : τ.
Proof. eauto using mem_alloc_index_typed. Qed.
Lemma mem_alloc_index_typed_inv' Γ m o malloc τ o' τ' :
  ✓ Γ → ✓{Γ} τ → o ≠ o' →
  '{mem_alloc Γ o malloc τ m} ⊢ o' : τ' → '{m} ⊢ o' : τ'.
Proof. eauto using mem_alloc_index_typed_inv. Qed.
Lemma mem_alloc_forward' Γ m o malloc τ :
  ✓ Γ → ✓{Γ} τ → mem_allocable o m → '{m} ⇒ₘ '{mem_alloc Γ o malloc τ m}.
Proof. eauto using mem_alloc_forward, mem_allocable_memenv_of. Qed.
Lemma mem_alloc_writable_top Γ m o malloc τ :
  ✓ Γ → ✓{Γ} τ → 
  mem_allocable o m → mem_writable Γ (addr_top o τ) (mem_alloc Γ o malloc τ m).
Proof.
  unfold mem_allocable. intros. exists (ctree_new Γ pbit_full τ); split.
  * unfold lookupE, cmap_lookup. 
    rewrite option_guard_True by eauto using addr_top_strict.
    by destruct m as [m]; simplify_map_equality'.
  * apply ctree_new_Forall; auto; by destruct alloc.
Qed.
Lemma mem_alloc_writable Γ m o malloc a τ :
  ✓ Γ → ✓{Γ} τ → mem_allocable o m →
  mem_writable Γ a m → mem_writable Γ a (mem_alloc Γ o malloc τ m).
Proof.
  intros ??? (w&?&?); exists w; split; auto.
  unfold mem_allocable, lookupE, cmap_lookup in *; destruct m as [m].
  case_option_guard; simplify_equality'.
  destruct (m !! addr_index a) as [w'|] eqn:?; simplify_equality'.
  by destruct (decide (o = addr_index a)); simplify_map_equality.
Qed.
Lemma mem_alloc_writable_all Γ m o malloc τ :
  ✓ Γ → ✓{Γ} τ → mem_allocable o m →
  mem_writable_all Γ m → mem_writable_all Γ (mem_alloc Γ o malloc τ m).
Proof.
  intros ???? o' τ' ?. destruct (decide (o = o')) as [<-|].
  * assert ('{mem_alloc Γ o malloc τ m} ⊢ o : τ)
      by eauto using mem_alloc_index_typed'; simplify_type_equality.
    eauto using mem_alloc_writable_top.
  * eauto using mem_alloc_writable, mem_alloc_index_typed_inv'.
Qed.
Lemma mem_alloc_allocable Γ m o malloc o' τ :
  mem_allocable o' m → o ≠ o' → mem_allocable o' (mem_alloc Γ o malloc τ m).
Proof.
  by destruct m as [m]; unfold mem_allocable; intros; simplify_map_equality'.
Qed.
Lemma mem_alloc_allocable_list Γ m o malloc os τ :
  mem_allocable_list m os → o ∉ os →
  mem_allocable_list (mem_alloc Γ o malloc τ m) os.
Proof.
  induction 1; rewrite ?elem_of_cons; constructor;
    naive_solver auto using mem_alloc_allocable.
Qed.

(** ** Properties of the [mem_free] fucntion *)
Global Instance mem_freeable_dec a m : Decision (mem_freeable a m).
Proof.
  refine
   match cmap_car m !! addr_index a as x return Decision (∃ w,
     addr_is_top_array a ∧ x = Some (Obj w true)
     ∧ ctree_Forall (λ xb, tagged_perm xb = perm_full) w)
   with
   | Some (Obj w true) => cast_if_and
      (decide (addr_is_top_array a))
      (decide (ctree_Forall (λ xb, tagged_perm xb = perm_full) w))
   | _ => right _
   end; abstract naive_solver.
Defined.
Lemma mem_free_memenv_of m o :
  '{mem_free o m} = alter (prod_map id (λ _, true)) o ('{m}).
Proof.
  destruct m as [m]; simpl; apply map_eq; intros o'.
  destruct (decide (o = o')) as [->|?].
  { rewrite !lookup_fmap, !lookup_alter, lookup_fmap; simpl.
    by destruct (m !! o') as [[]|]. }
  by rewrite lookup_fmap, !lookup_alter_ne, lookup_fmap by done.
Qed.
Lemma mem_free_index_typed_inv Γm o o' τ' :
  alter (prod_map id (λ _, true)) o Γm ⊢ o' : τ' → Γm ⊢ o' : τ'.
Proof.
  intros [β ?]; destruct (decide (o = o')); simplify_map_equality'.
  * destruct (Γm !! o') as [[? β']|] eqn:?; simplify_equality'; by exists β'.
  * by exists β; simplify_map_equality'.
Qed.
Lemma mem_free_index_alive_neq Γm o o' :
  o ≠ o' → index_alive Γm o' →
  index_alive (alter (prod_map id (λ _, true)) o Γm) o'.
Proof. by intros ? [τ ?]; exists τ; simplify_map_equality'. Qed.
Lemma mem_free_index_alive Γm o :
  ¬index_alive (alter (prod_map id (λ _ : bool, true)) o Γm) o.
Proof. intros [??]; simplify_map_equality; simplify_option_equality. Qed.
Lemma mem_free_index_alive_inv Γm o o' :
  index_alive (alter (prod_map id (λ _, true)) o Γm) o' → index_alive Γm o'.
Proof.
  by intros [τ ?]; destruct (decide (o = o')); exists τ;
    simplify_map_equality'; simplify_option_equality.
Qed.
Lemma mem_free_forward Γm o : Γm ⇒ₘ alter (prod_map id (λ _, true)) o Γm.
Proof.
  split; [|eauto using mem_free_index_alive_inv].
  intros o' ? [β ?]; destruct (decide (o = o')).
  * by exists true; simplify_map_equality'.
  * by exists β; simplify_map_equality'.
Qed.
Lemma mem_free_valid Γ Γm m o :
  ✓ Γ → ✓{Γ,Γm} m → ✓{Γ,alter (prod_map id (λ _, true)) o Γm} (mem_free o m).
Proof.
  destruct m as [m]; intros HΓ Hm; split; simpl.
  { intros o' τ; rewrite lookup_alter_Some;
      intros [(?&[τ'|w malloc']&?&?)|[??]]; simplify_equality'.
    * destruct (proj1 Hm o' τ') as (?&?&?&?); eauto 10 using
        mem_free_forward, memenv_forward_typed, memenv_forward_alive.
    * destruct (proj2 Hm o' w malloc') as (?&?&?&?&?&?);simplify_type_equality';
        eauto 11 using ctree_typed_type_valid, mem_free_index_alive,
        mem_free_forward, memenv_forward_typed, memenv_forward_alive.
    * destruct (proj1 Hm o' τ) as (?&?&?&?); eauto 10 using
        mem_free_forward, memenv_forward_typed, memenv_forward_alive. }
  intros o' w malloc; rewrite lookup_alter_Some;
    intros [(?&[]&?&?)|[??]]; simplify_map_equality'.
  destruct (proj2 Hm o' w malloc) as (τ'&?&?&?&?&?); eauto.
  exists τ'; split_ands; eauto using
    ctree_typed_weaken, mem_free_index_alive_neq, mem_free_forward,
     mem_free_forward, memenv_forward_typed, memenv_forward_alive.
Qed.
Lemma mem_free_valid' Γ m o : ✓ Γ → ✓{Γ} m → ✓{Γ} (mem_free o m).
Proof.
  unfold valid at 2 3, cmap_valid'; intros. rewrite mem_free_memenv_of.
  eauto using mem_free_valid.
Qed.
Lemma mem_free_forward' m o : '{m} ⇒ₘ '{mem_free o m}.
Proof. rewrite mem_free_memenv_of; eauto using mem_free_forward. Qed.
Lemma mem_foldr_free_forward m os : '{m} ⇒ₘ '{foldr mem_free m os}.
Proof.
  induction os; simpl; [done|]. etransitivity; eauto using mem_free_forward'.
Qed.
Lemma mem_foldr_free_valid Γ m os : ✓ Γ → ✓{Γ} m → ✓{Γ} (foldr mem_free m os).
Proof. induction os; simpl; auto using mem_free_valid'. Qed.

(** ** Properties of the [lookup] function *)
Lemma mem_lookup_typed Γ Γm m a v τ :
  ✓ Γ → ✓{Γ,Γm} m → m !!{Γ} a = Some v → (Γ,Γm) ⊢ a : τ → (Γ,Γm) ⊢ v : τ.
Proof.
  unfold lookupE, mem_lookup. intros ? Hm Hv Ha. destruct (m !!{Γ} a)
    as [w|] eqn:?; simplify_option_equality; eauto using to_val_typed.
Qed.
Lemma mem_lookup_frozen Γ Γm m a v :
  ✓ Γ → ✓{Γ,Γm} m → m !!{Γ} a = Some v → val_map (freeze true) v = v.
Proof.
  unfold lookupE, mem_lookup. intros ? Hm Hv.
  destruct (m !!{Γ} a) as [w|] eqn:?; simplify_option_equality.
  eapply to_val_frozen, cmap_lookup_Some; eauto.
Qed.
Lemma mem_lookup_subseteq Γ Γm m1 m2 a v1 :
  ✓ Γ → ✓{Γ,Γm} m1 → m1 ⊆ m2 → m1 !!{Γ} a = Some v1 → m2 !!{Γ} a = Some v1.
Proof.
  unfold lookupE, mem_lookup; intros.
  destruct (m1 !!{Γ} a) as [w1|] eqn:?; simplify_option_equality.
  destruct (cmap_lookup_subseteq Γ m1 m2 a w1) as (w2&->&?); simpl; auto.
  { eapply ctree_Forall_not; eauto using cmap_lookup_Some, pbits_mapped. }
  by erewrite option_guard_True, (to_val_subseteq _ _ w1 w2)
    by eauto using cmap_lookup_Some, pbits_mapped,
    pbits_kind_subseteq, @ctree_flatten_subseteq.
Qed.

(** Properties of the [force] function *)
Lemma mem_force_memenv_of Γ Γm m a :
  ✓ Γ → ✓{Γ,Γm} m → is_Some (m !!{Γ} a) → '{mem_force Γ a m} = '{m}.
Proof.
  unfold mem_force, lookupE, mem_lookup. intros ?? [v ?].
  destruct (m !!{Γ} a) as [w|] eqn:?; simplify_equality'.
  by erewrite cmap_alter_memenv_of by eauto.
Qed.
Lemma mem_force_forward Γ Γm m a :
  ✓ Γ → ✓{Γ,Γm} m → is_Some (m !!{Γ} a) → '{m} ⇒ₘ '{mem_force Γ a m}.
Proof. intros. by erewrite mem_force_memenv_of by eauto. Qed.
Lemma mem_force_valid Γ Γm m a :
  ✓ Γ → ✓{Γ,Γm} m → is_Some (m !!{Γ} a) → ✓{Γ,Γm} (mem_force Γ a m).
Proof.
  unfold mem_force, lookupE, mem_lookup. intros ?? [v ?].
  destruct (m !!{Γ} a) as [w|] eqn:?; simplify_option_equality.
  eapply cmap_alter_valid; eauto using cmap_lookup_Some,
    ctree_Forall_not, cmap_lookup_Some, pbits_mapped.
Qed.
Lemma mem_force_valid' Γ m a :
  ✓ Γ → ✓{Γ} m → is_Some (m !!{Γ} a) → ✓{Γ} (mem_force Γ a m).
Proof.
  unfold valid at 2 3, cmap_valid'; intros.
  erewrite mem_force_memenv_of by eauto; eauto using mem_force_valid.
Qed.
Lemma mem_lookup_force Γ Γm m a v τ :
  ✓ Γ → ✓{Γ,Γm} m → (Γ,Γm) ⊢ a : τ → m !!{Γ} a = Some v → addr_is_obj a →
  mem_force Γ a m !!{Γ} a = Some v.
Proof.
  unfold lookupE, mem_lookup, mem_force. intros.
  destruct (m !!{Γ} a) as [w'|] eqn:?; simplify_equality'.
  by erewrite cmap_lookup_alter by eauto; simplify_option_equality.
Qed.
Lemma mem_lookup_force_disjoint Γ Γm m a1 a2 τ2 v1 :
  ✓ Γ → ✓{Γ,Γm} m → a1 ⊥{Γ} a2 → m !!{Γ} a1 = Some v1 →
  (Γ,Γm) ⊢ a2 : τ2 → is_Some (m !!{Γ} a2) → mem_force Γ a2 m !!{Γ} a1 = Some v1.
Proof.
  unfold lookupE, mem_force, mem_lookup. intros ????? [??].
  destruct (m !!{Γ} a1) as [w1|] eqn:?,
    (m !!{Γ} a2) as [w2|] eqn:?; simplify_equality'.
  by erewrite cmap_lookup_alter_disjoint by eauto.
Qed.
Lemma mem_force_commute Γ Γm m a1 a2 τ1 τ2 :
  ✓ Γ → ✓{Γ,Γm} m → a1 ⊥{Γ} a2 →
  (Γ,Γm) ⊢ a1 : τ1 → is_Some (m !!{Γ} a1) →
  (Γ,Γm) ⊢ a2 : τ2 → is_Some (m !!{Γ} a2) →
  mem_force Γ a1 (mem_force Γ a2 m) = mem_force Γ a2 (mem_force Γ a1 m).
Proof.
  unfold lookupE, mem_lookup, mem_force. intros ???? [??] ? [??].
  destruct (m !!{Γ} a1) as [w1|] eqn:?, (m !!{Γ} a2) as [w2|] eqn:?;
    simplify_equality'; eauto using cmap_alter_commute.
Qed.
Lemma mem_force_disjoint Γ Γm1 m1 m2 a1 τ1 :
  ✓ Γ → ✓{Γ,Γm1} m1 → m1 ⊥ m2 →
  (Γ,Γm1) ⊢ a1 : τ1 → is_Some (m1 !!{Γ} a1) → mem_force Γ a1 m1 ⊥ m2.
Proof.
  unfold lookupE, mem_lookup, mem_force. intros ???? [??].
  destruct (m1 !!{Γ} a1) as [w1|] eqn:?; simplify_option_equality.
  eapply cmap_alter_disjoint; eauto using ctree_Forall_not, pbits_mapped.
Qed.
Lemma mem_force_disjoint_le Γ Γm m ms a v τ :
  ✓ Γ → ✓{Γ,Γm} m → (Γ,Γm) ⊢ a : τ → is_Some (m !!{Γ} a) →
  m :: ms ⊆⊥ mem_force Γ a m :: ms.
Proof.
  intros. apply sep_disjoint_cons_le_inj; intros m'.
  rewrite !sep_disjoint_list_double, !(symmetry_iff _ m').
  eauto using mem_force_disjoint.
Qed.
Lemma mem_force_union Γ Γm1 m1 m2 a1 v1 τ1 :
  ✓ Γ → ✓{Γ,Γm1} m1 → m1 ⊥ m2 →
  (Γ,Γm1) ⊢ a1 : τ1 → is_Some (m1 !!{Γ} a1) →
  mem_force Γ a1 (m1 ∪ m2) = mem_force Γ a1 m1 ∪ m2.
Proof.
  unfold lookupE, mem_lookup, mem_force. intros ???? [??].
  destruct (m1 !!{Γ} a1) as [w1|] eqn:?; simplify_option_equality.
  eapply cmap_alter_union; eauto using ctree_Forall_not, pbits_mapped.
Qed.

(** Properties of the [insert] function *)
Lemma mem_writable_strict Γ m a : mem_writable Γ a m → addr_strict Γ a.
Proof. intros (w&?&?); eauto using cmap_lookup_strict. Qed.
Lemma mem_writable_alive Γ Γm m a :
  ✓ Γ → ✓{Γ,Γm} m → mem_writable Γ a m → index_alive Γm (addr_index a).
Proof.
  intros ? Hm (w&?&?).
  assert ((Γ,Γm) ⊢ w : type_of w) by eauto using cmap_lookup_Some.
  unfold lookupE, cmap_lookup in *; case_option_guard; simplify_equality'.
  destruct (cmap_car m !! addr_index a) as [[|w' β]|] eqn:?; simplify_equality'.
  destruct (proj2 Hm (addr_index a) w' β) as (τ&?&?&?); auto.
Qed.
Global Instance mem_writable_dec Γ a m : Decision (mem_writable Γ a m).
Proof.
  refine
   match Some_dec (m !!{Γ} a) with
   | inleft (w ↾ _) => cast_if
      (decide (ctree_Forall (λ xb, Some Writable ⊆ pbit_kind xb) w))
   | inright _ => right _
   end; abstract (unfold mem_writable; naive_solver).
Defined.
Lemma mem_writable_subseteq Γ Γm m1 m2 a v1 :
  ✓ Γ → ✓{Γ,Γm} m1 → m1 ⊆ m2 → mem_writable Γ a m1 → mem_writable Γ a m2.
Proof.
  intros ??? (w1&?&?).
  destruct (cmap_lookup_subseteq Γ m1 m2 a w1) as (w2&?&?); auto.
  { eauto using ctree_Forall_not,
      cmap_lookup_Some, pbits_mapped, pbits_kind_weaken. }
  exists w2; eauto using pbits_kind_subseteq, @ctree_flatten_subseteq.
Qed.
Lemma of_val_flatten_typed Γ Γm w v τ :
  ✓ Γ → (Γ,Γm) ⊢ w : τ → (Γ,Γm) ⊢ v : τ →
  ctree_Forall (λ xb, Some Writable ⊆ pbit_kind xb) w →
  (Γ,Γm) ⊢ of_val Γ (tagged_perm <$> ctree_flatten w) v : τ.
Proof.
  intros. eapply of_val_typed; eauto.
  * eauto using pbits_valid_perm_valid, ctree_flatten_valid.
  * eapply pbits_perm_mapped, pbits_mapped; eauto using pbits_kind_weaken,
      pbits_valid_sep_valid, ctree_flatten_valid.
Qed.
Lemma of_val_flatten_mapped Γ Γm w v τ :
  ✓ Γ → (Γ,Γm) ⊢ w : τ → (Γ,Γm) ⊢ v : τ →
  ctree_Forall (λ xb, Some Writable ⊆ pbit_kind xb) w →
  ctree_Forall (not ∘ sep_unmapped)
    (of_val Γ (tagged_perm <$> ctree_flatten w) v).
Proof.
  intros. eapply of_val_mapped; eauto.
  eapply pbits_perm_mapped, pbits_mapped; eauto using pbits_kind_weaken,
    pbits_valid_sep_valid, ctree_flatten_valid.
Qed.
Lemma of_val_flatten_unshared Γ Γm w v τ :
  ✓ Γ → (Γ,Γm) ⊢ w : τ → (Γ,Γm) ⊢ v : τ →
  ctree_Forall (λ xb, Some Writable ⊆ pbit_kind xb) w →
  ctree_unshared (of_val Γ (tagged_perm <$> ctree_flatten w) v).
Proof.
  intros. eapply of_val_unshared; eauto.
  * eapply pbits_perm_unshared, pbits_unshared; eauto using
      pbits_kind_weaken, pbits_valid_sep_valid, ctree_flatten_valid.
  * eapply pbits_perm_mapped, pbits_mapped; eauto using
      pbits_kind_weaken, pbits_valid_sep_valid, ctree_flatten_valid.
Qed.
Lemma mem_insert_memenv_of Γ Γm m a v τ :
  ✓ Γ → ✓{Γ,Γm} m → (Γ,Γm) ⊢ a : τ → mem_writable Γ a m → (Γ,Γm) ⊢ v : τ →
  '{<[a:=v]{Γ}>m} = '{m}.
Proof.
  unfold insertE, mem_insert, lookupE, mem_lookup. intros ??? (w&?&?) ?.
  eapply cmap_alter_memenv_of; eauto.
  by erewrite of_val_type_of, !type_of_correct by eauto.
Qed.
Lemma mem_insert_forward Γ Γm m a v τ :
  ✓ Γ → ✓{Γ,Γm} m → (Γ,Γm) ⊢ a : τ → mem_writable Γ a m → (Γ,Γm) ⊢ v : τ →
  '{m} ⇒ₘ '{<[a:=v]{Γ}>m}.
Proof. intros. by erewrite mem_insert_memenv_of by eauto. Qed.
Lemma mem_insert_valid Γ Γm m a v τ :
  ✓ Γ → ✓{Γ,Γm} m → (Γ,Γm) ⊢ a : τ → mem_writable Γ a m → (Γ,Γm) ⊢ v : τ →
  ✓{Γ,Γm} (<[a:=v]{Γ}>m).
Proof.
  intros ??? (w&?&?) ?. assert ((Γ,Γm) ⊢ w : τ) by eauto.
  eapply cmap_alter_valid; eauto; simplify_type_equality;
    eauto using of_val_flatten_typed, of_val_flatten_mapped,
    ctree_Forall_not, ctree_lookup_Some.
Qed.
Lemma mem_insert_valid' Γ m a v τ :
  ✓ Γ → ✓{Γ} m → (Γ,'{m}) ⊢ a : τ → mem_writable Γ a m →
  (Γ,'{m}) ⊢ v : τ → ✓{Γ} (<[a:=v]{Γ}>m).
Proof.
  unfold valid at 2 3, cmap_valid'; intros.
  erewrite mem_insert_memenv_of by eauto; eauto using mem_insert_valid.
Qed.
(** We need [addr_is_obj a] because writes at padding bytes are ignored *)
Lemma mem_lookup_insert Γ Γm m a v τ :
  ✓ Γ → ✓{Γ,Γm} m → (Γ,Γm) ⊢ a : τ → mem_writable Γ a m → addr_is_obj a →
  (Γ,Γm) ⊢ v : τ → <[a:=v]{Γ}>m !!{Γ} a = Some (val_map (freeze true) v).
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
Lemma mem_lookup_insert_disjoint Γ Γm m a1 a2 v1 v2 τ2 :
  ✓ Γ → ✓{Γ,Γm} m → a1 ⊥{Γ} a2 → m !!{Γ} a1 = Some v1 →
  (Γ,Γm) ⊢ a2 : τ2 → mem_writable Γ a2 m → (Γ,Γm) ⊢ v2 : τ2 →
  <[a2:=v2]{Γ}>m !!{Γ} a1 = Some v1.
Proof.
  unfold insertE, lookupE, mem_insert, mem_lookup. intros ????? (w2&?&Hw2) ?.
  destruct (m !!{Γ} a1) as [w1|] eqn:?; simplify_equality'.
  by erewrite cmap_lookup_alter_disjoint
    by eauto using of_val_flatten_typed, of_val_flatten_unshared.
Qed.
Lemma mem_insert_commute Γ Γm m a1 a2 v1 v2 τ1 τ2 :
  ✓ Γ → ✓{Γ,Γm} m → a1 ⊥{Γ} a2 →
  (Γ,Γm) ⊢ a1 : τ1 → mem_writable Γ a1 m → (Γ,Γm) ⊢ v1 : τ1 →
  (Γ,Γm) ⊢ a2 : τ2 → mem_writable Γ a2 m → (Γ,Γm) ⊢ v2 : τ2 →
  <[a1:=v1]{Γ}>(<[a2:=v2]{Γ}>m) = <[a2:=v2]{Γ}>(<[a1:=v1]{Γ}>m).
Proof.
  intros ???? (?&?&?) ?? (?&?&?) ?.
  eapply cmap_alter_commute; eauto using of_val_flatten_typed.
Qed.
Lemma mem_insert_force_commute Γ Γm m a1 a2 v1 τ1 τ2 :
  ✓ Γ → ✓{Γ,Γm} m → a1 ⊥{Γ} a2 →
  (Γ,Γm) ⊢ a1 : τ1 → mem_writable Γ a1 m → (Γ,Γm) ⊢ v1 : τ1 →
  (Γ,Γm) ⊢ a2 : τ2 → is_Some (m !!{Γ} a2) →
  <[a1:=v1]{Γ}>(mem_force Γ a2 m) = mem_force Γ a2 (<[a1:=v1]{Γ}>m).
Proof.
  unfold lookupE, mem_lookup, mem_force. intros ???? (?&?&?) ?? [??].
  destruct (m !!{Γ} a2) as [w2|] eqn:?; simplify_equality'.
  eapply cmap_alter_commute; eauto using of_val_flatten_typed.
Qed.
Lemma mem_insert_writable Γ Γm m a1 a2 v2 τ2 :
  ✓ Γ → ✓{Γ,Γm} m → a1 = a2 ∨ a1 ⊥{Γ} a2 →
  (Γ,Γm) ⊢ a2 : τ2 → mem_writable Γ a2 m → (Γ,Γm) ⊢ v2 : τ2 →
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
Lemma mem_insert_top_writable_all Γ m o2 v2 τ2 :
  ✓ Γ → ✓{Γ} m → '{m} ⊢ o2 : τ2 → (Γ,'{m}) ⊢ v2 : τ2 →
  mem_writable_all Γ m → mem_writable_all Γ (<[addr_top o2 τ2:=v2]{Γ}>m).
Proof.
  intros ????? o τ; erewrite mem_insert_memenv_of by eauto using
    addr_top_typed, index_typed_representable; intros.
  eapply mem_insert_writable; eauto using addr_top_typed, index_typed_representable.
  eauto using mem_insert_writable, addr_top_disjoint.
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
Lemma mem_insert_disjoint Γ Γm1 m1 m2 a1 v1 τ1 :
  ✓ Γ → ✓{Γ,Γm1} m1 → m1 ⊥ m2 →
  (Γ,Γm1) ⊢ a1 : τ1 → mem_writable Γ a1 m1 → (Γ,Γm1) ⊢ v1 : τ1 →
  <[a1:=v1]{Γ}>m1 ⊥ m2.
Proof.
  intros ???? (w1&?&?) ?. assert (ctree_unshared w1).
  { eapply pbits_unshared; eauto using pbits_kind_weaken,
      pbits_valid_sep_valid, ctree_flatten_valid. }
  assert (ctree_Forall (not ∘ sep_unmapped) w1).
  { eapply pbits_mapped; eauto using pbits_kind_weaken. }
  eapply cmap_alter_disjoint; eauto using of_val_flatten_typed,
    of_val_flatten_mapped, of_val_disjoint, ctree_Forall_not.
Qed.
Lemma mem_insert_disjoint_le Γ Γm m ms a v τ :
  ✓ Γ → ✓{Γ,Γm} m → (Γ,Γm) ⊢ a : τ → mem_writable Γ a m → (Γ,Γm) ⊢ v : τ →
  m :: ms ⊆⊥ <[a:=v]{Γ}>m :: ms.
Proof.
  intros. apply sep_disjoint_cons_le_inj; intros m'.
  rewrite !sep_disjoint_list_double, !(symmetry_iff _ m').
  eauto using mem_insert_disjoint.
Qed.
Lemma mem_insert_union Γ Γm1 m1 m2 a1 v1 τ1 :
  ✓ Γ → ✓{Γ,Γm1} m1 → m1 ⊥ m2 →
  (Γ,Γm1) ⊢ a1 : τ1 → mem_writable Γ a1 m1 → (Γ,Γm1) ⊢ v1 : τ1 →
  <[a1:=v1]{Γ}>(m1 ∪ m2) = <[a1:=v1]{Γ}>m1 ∪ m2.
Proof.
  intros ???? (w1&?&?) ?. assert (ctree_unshared w1).
  { eapply pbits_unshared; eauto using pbits_kind_weaken,
      pbits_valid_sep_valid, ctree_flatten_valid. }
  assert (ctree_Forall (not ∘ sep_unmapped) w1).
  { eapply pbits_mapped; eauto using pbits_kind_weaken. }
  eapply cmap_alter_union; eauto using of_val_flatten_typed,
    of_val_flatten_mapped, of_val_disjoint, of_val_union, ctree_Forall_not.
Qed.
Lemma mem_alloc_val_valid Γ m malloc o v τ :
  ✓ Γ → ✓{Γ} m → mem_allocable o m →
  (Γ,'{m}) ⊢ v : τ → int_typed (size_of Γ τ) sptrT →
  ✓{Γ} (<[addr_top o τ:=v]{Γ}>(mem_alloc Γ o malloc τ m)).
Proof.
  intros. eapply mem_insert_valid'; eauto using mem_alloc_valid',
    addr_top_typed, mem_alloc_writable_top, val_typed_weaken,
    mem_alloc_index_typed', mem_alloc_forward'.
Qed.
Lemma mem_alloc_val_index_typed Γ m malloc o v τ :
  ✓ Γ → ✓{Γ} m → mem_allocable o m →
  (Γ,'{m}) ⊢ v : τ → int_typed (size_of Γ τ) sptrT →
  '{<[addr_top o τ:=v]{Γ}>(mem_alloc Γ o malloc τ m)} ⊢ o : τ.
Proof.
  intros. erewrite mem_insert_memenv_of by eauto using mem_alloc_valid',
    addr_top_typed, mem_alloc_index_typed', mem_alloc_writable_top,
    val_typed_weaken, mem_alloc_forward'; eauto using mem_alloc_index_typed'.
Qed.
Lemma mem_alloc_val_forward Γ m malloc o v τ :
  ✓ Γ → ✓{Γ} m → mem_allocable o m →
  (Γ,'{m}) ⊢ v : τ → int_typed (size_of Γ τ) sptrT →
  '{m} ⇒ₘ '{<[addr_top o τ:=v]{Γ}>(mem_alloc Γ o malloc τ m)}.
Proof.
  intros. erewrite mem_insert_memenv_of by eauto using mem_alloc_valid',
    addr_top_typed, mem_alloc_index_typed', mem_alloc_writable_top,
    val_typed_weaken, mem_alloc_forward'; eauto using mem_alloc_forward'.
Qed.
Lemma mem_alloc_val_allocable Γ m o malloc v τ o' :
  mem_allocable o' m → o ≠ o' →
  mem_allocable o' (<[addr_top o τ:=v]{Γ}>(mem_alloc Γ o malloc τ m)).
Proof. intros. by apply mem_insert_allocable, mem_alloc_allocable. Qed.
Lemma mem_alloc_val_writable_all Γ m o malloc v τ :
  ✓ Γ → ✓{Γ} m → mem_allocable o m → (Γ,'{m}) ⊢ v : τ →
  int_typed (size_of Γ τ) sptrT → mem_writable_all Γ m →
  mem_writable_all Γ (<[addr_top o τ:=v]{Γ}>(mem_alloc Γ o malloc τ m)).
Proof.
  intros. eapply mem_insert_top_writable_all; eauto using mem_alloc_valid',
    addr_top_typed, mem_alloc_index_typed', mem_alloc_writable_top,
    val_typed_weaken, mem_alloc_forward', mem_alloc_writable_all.
Qed.
Lemma mem_alloc_val_list_valid Γ m os vs τs :
  ✓ Γ → ✓{Γ} m → mem_allocable_list m os → length os = length vs →
  (Γ,'{m}) ⊢* vs :* τs → Forall (λ τ, int_typed (size_of Γ τ) sptrT) τs →
  (**i 1.) *) ✓{Γ} (mem_alloc_val_list Γ (zip os vs) m) ∧
  (**i 2.) *) '{mem_alloc_val_list Γ (zip os vs) m} ⊢* os :* τs ∧
  (**i 3.) *) '{m} ⇒ₘ '{mem_alloc_val_list Γ (zip os vs) m}.
Proof.
  rewrite <-Forall2_same_length. intros ? Hm Hfree Hovs Hvs Hτs.
  revert os vs m Hovs Hm Hvs Hfree.
  induction Hτs as [|τ τs ?? IH];
    intros ?? m [|o v os vs ??]; inversion_clear 3;
    decompose_Forall_hyps; simplify_type_equality; auto.
  destruct (IH os vs (<[addr_top o τ:=v]{Γ}> (mem_alloc Γ o false τ m))) as
    (IH1&IH2&IH3); eauto using mem_alloc_val_valid.
  { eauto using Forall2_impl, val_typed_weaken,
      mem_alloc_val_forward, memenv_forward_typed. }
  { by apply mem_insert_allocable_list, mem_alloc_allocable_list. }
  split_ands; eauto using mem_alloc_val_index_typed, memenv_forward_typed.
  transitivity ('{<[addr_top o τ:=v]{Γ}> (mem_alloc Γ o false τ m)});
    eauto using mem_alloc_val_forward.
Qed.
Lemma mem_alloc_val_list_index_typed Γ m os vs τs :
  ✓ Γ → ✓{Γ} m → mem_allocable_list m os → length os = length vs →
  (Γ,'{m}) ⊢* vs :* τs → Forall (λ τ, int_typed (size_of Γ τ) sptrT) τs →
  '{mem_alloc_val_list Γ (zip os vs) m} ⊢* os :* τs.
Proof. intros. eapply mem_alloc_val_list_valid; eauto. Qed.
Lemma mem_alloc_val_list_forward Γ m os vs τs :
  ✓ Γ → ✓{Γ} m → mem_allocable_list m os → length os = length vs →
  (Γ,'{m}) ⊢* vs :* τs → Forall (λ τ, int_typed (size_of Γ τ) sptrT) τs →
  '{m} ⇒ₘ '{mem_alloc_val_list Γ (zip os vs) m}.
Proof. intros. eapply mem_alloc_val_list_valid; eauto. Qed.

(** ** Locks *)
Lemma elem_of_mem_locks m o i :
  (o,i) ∈ mem_locks m ↔ ∃ w β, cmap_car m !! o = Some (Obj w β)
    ∧ pbit_locked <$> ctree_flatten w !! i = Some true.
Proof.
  destruct m as [m]; simpl; split.
  { intros (ω&Hω&?); simplify_equality'; rewrite lookup_omap in Hω.
    destruct (m !! o) as [[|w β]|]; simplify_option_equality.
    exists w β. by rewrite <-list_lookup_fmap, <-elem_of_of_bools. }
  intros (w&β&?&Hi). exists (of_bools (pbit_locked <$> ctree_flatten w));
    simpl; rewrite lookup_omap; simplify_map_equality'.
  rewrite <-list_lookup_fmap, <-elem_of_of_bools in Hi.
  by rewrite option_guard_True by esolve_elem_of.
Qed.
Lemma elem_of_mem_locks_alt m o i w β :
  cmap_car m !! o = Some (Obj w β) →
  (o,i) ∈ mem_locks m ↔ pbit_locked <$> ctree_flatten w !! i = Some true.
Proof. rewrite !elem_of_mem_locks. naive_solver. Qed.
Lemma mem_locks_valid m : ✓{'{m}} (mem_locks m).
Proof.
  intros o i; rewrite elem_of_mem_locks; intros (w&β&?&?).
  exists (type_of w) false. by destruct m; simplify_map_equality'.
Qed.
Lemma mem_locks_empty : mem_locks ∅ = ∅.
Proof. apply dsig_eq; unfold mem_locks; simpl. by rewrite omap_empty. Qed.
Lemma mem_locks_union m1 m2 :
  m1 ⊥ m2 → mem_locks (m1 ∪ m2) = mem_locks m1 ∪ mem_locks m2.
Proof.
  intros Hm. apply elem_of_equiv_L; intros [o i]; rewrite elem_of_union,
    !elem_of_mem_locks; destruct m1 as [m1], m2 as [m2]; simpl.
  rewrite lookup_union_with. specialize (Hm o). assert (∀ w1 w2,
    w1 ⊥ w2 → pbit_locked <$> ctree_flatten (w1 ∪ w2) !! i = Some true ↔
      pbit_locked <$> ctree_flatten w1 !! i = Some true
      ∨ pbit_locked <$> ctree_flatten w2 !! i = Some true).
  { intros w1 w2 ?. rewrite ctree_flatten_union, <-!list_lookup_fmap by done.
    assert (ctree_flatten w1 ⊥* ctree_flatten w2)
      by auto using @ctree_flatten_disjoint.
    rewrite pbits_locked_union, lookup_zip_with by done.
    set (βs1 := pbit_locked <$> ctree_flatten w1).
    set (βs2 := pbit_locked <$> ctree_flatten w2).
    assert (Forall2 (λ _ _, True) βs1 βs2).
    { eapply Forall2_fmap, Forall2_impl; eauto. }
    destruct (βs1 !! i) as [[]|] eqn:?, (βs2 !! i) as [[]|] eqn:?;
      decompose_Forall_hyps; intuition congruence. }
  destruct (m1 !! o) as [[]|], (m2 !! o) as [[]|]; naive_solver eauto 0.
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
Lemma mem_lock_memenv_of Γ Γm m a  :
  ✓ Γ → ✓{Γ,Γm} m → mem_writable Γ a m → '{mem_lock Γ a m} = '{m}.
Proof.
  unfold mem_lock. intros ?? (v&?&?).
  by erewrite cmap_alter_memenv_of by eauto using ctree_map_type_of.
Qed.
Lemma mem_lock_forward Γ Γm m a  :
  ✓ Γ → ✓{Γ,Γm} m → mem_writable Γ a m → '{m} ⇒ₘ '{mem_lock Γ a m}.
Proof. intros. by erewrite mem_lock_memenv_of by eauto. Qed.
Lemma mem_lock_valid Γ Γm m a :
  ✓ Γ → ✓{Γ,Γm} m → mem_writable Γ a m → ✓{Γ,Γm} (mem_lock Γ a m).
Proof.
  intros ?? (w&?&?). assert ((Γ,Γm) ⊢ ctree_map pbit_lock w : type_of w).
  { eapply ctree_map_typed; eauto using cmap_lookup_Some,
      pbits_lock_valid, ctree_flatten_valid; by intros [??] <-. }
  eapply cmap_alter_valid, ctree_Forall_not; eauto. rewrite ctree_flatten_map.
  eauto using pbits_lock_mapped, pbits_mapped, pbits_kind_weaken.
Qed.
Lemma mem_lock_valid' Γ m a :
  ✓ Γ → ✓{Γ} m → mem_writable Γ a m → ✓{Γ} (mem_lock Γ a m).
Proof.
  unfold valid at 2 3, cmap_valid'; intros.
  erewrite mem_lock_memenv_of by eauto. eauto using mem_lock_valid.
Qed.
Lemma ctree_unlock_typed Γ Γm w τ βs :
  ✓ Γ → (Γ,Γm) ⊢ w : τ → length βs = bit_size_of Γ τ →
  (Γ,Γm) ⊢ ctree_merge true pbit_unlock_if w βs : τ.
Proof.
  intros HΓ Hw. revert w τ Hw βs.
  refine (ctree_typed_ind _ _ _ _ _ _ _ _); simpl.
  * intros; typed_constructor; auto using pbits_unlock_valid.
  * intros ws τ Hws IH Hlen βs. rewrite bit_size_of_array.
    intros Hβs; typed_constructor; auto.
    + clear Hlen IH. revert βs Hβs. induction Hws; intros; f_equal'; auto.
    + clear Hlen. revert βs Hβs.
      induction Hws; intros; decompose_Forall_hyps; constructor; auto.
  * intros s wxbss τs Hs Hws IH Hxbss Hindet Hlen βs.
    erewrite bit_size_of_struct by eauto. intros Hβs.
    typed_constructor; eauto; clear Hs.
    + clear Hxbss Hindet. revert wxbss βs Hws IH Hβs Hlen.
      unfold field_bit_padding. induction (bit_size_of_fields _ τs HΓ);
        intros [|[??] ?] ?????; decompose_Forall_hyps;
        erewrite ?type_of_correct by eauto; constructor; simpl; auto.
    + clear Hβs. revert βs. elim Hxbss; [|intros [??] ????];
        constructor; simpl; auto using pbits_unlock_valid.
    + clear Hβs. revert βs. elim Hindet; [|intros [??] ????]; constructor;
        simpl in *; auto; rewrite pbit_indetify_unlock; congruence.
    + clear Hxbss IH Hindet. revert wxbss βs Hws Hβs Hlen.
      unfold field_bit_padding. induction (bit_size_of_fields _ τs HΓ);
        intros [|[??] ?] ????; decompose_Forall_hyps;
        erewrite ?type_of_correct by eauto; f_equal; auto.
  * intros s i τs w xbs τ ??????? Hc βs ?. typed_constructor; eauto.
    + auto using pbits_unlock_valid.
    + rewrite pbit_indetify_unlock; congruence.
    + solve_length.
    + rewrite ctree_flatten_merge.
      intros [??]; destruct Hc; split; eapply pbits_unlock_mapped; 
        eauto using ctree_flatten_valid, pbits_valid_sep_valid.
  * intros; typed_constructor; eauto using pbits_unlock_valid.
Qed.
Lemma ctree_unlock_type_of w βs :
  type_of (ctree_merge true pbit_unlock_if w βs) = type_of w.
Proof.
  destruct w as [|τ ws| | |]; f_equal'.
  revert βs. induction ws; intros; f_equal'; auto.
Qed.
Lemma mem_unlock_memenv_of m Ω : '{mem_unlock Ω m} = '{m}.
Proof.
  apply map_eq; intros o. destruct m as [m], Ω as [Ω]; simpl.
  rewrite !lookup_fmap, lookup_merge by done.
  destruct (m !! o) as [[|w β]|], (Ω !! o) as [ω|]; simplify_equality'; f_equal.
  by rewrite ctree_unlock_type_of.
Qed.
Lemma mem_unlock_forward m Ω : '{m} ⇒ₘ '{mem_unlock Ω m}.
Proof. by rewrite mem_unlock_memenv_of. Qed.
Lemma mem_unlock_valid Γ Γm m Ω : ✓ Γ → ✓{Γ,Γm} m → ✓{Γ,Γm} (mem_unlock Ω m).
Proof.
  destruct m as [m], Ω as [Ω HΩ']; intros ? [Hm1 Hm2]; split; simpl in *.
  { intros o τ; rewrite lookup_merge by done; intros.
    destruct (Ω !! o), (m !! o) as [[]|] eqn:?; simplify_equality'; eauto. }
  intros o w β; rewrite lookup_merge by done; intros.
  destruct (m !! o) as [[|w' ?]|] eqn:Hw',
    (Ω !! o) as [ω|] eqn:Hω; simplify_equality'; eauto.
  destruct (Hm2 o w' β) as (τ&?&?&?&Hemp&?); auto.
  exists τ; split_ands; auto using ctree_unlock_typed, to_bools_length.
  rewrite ctree_flatten_merge; contradict Hemp.
  eapply pbits_unlock_empty_inv;
    eauto using ctree_flatten_valid, pbits_valid_sep_valid.
Qed.
Lemma mem_unlock_valid' Γ m Ω : ✓ Γ → ✓{Γ} m → ✓{Γ} (mem_unlock Ω m).
Proof.
  unfold valid at 2 3, cmap_valid'; intros.
  rewrite mem_unlock_memenv_of. eauto using mem_unlock_valid.
Qed.
Lemma elem_of_lock_singleton Γ a o i :
  0 < bit_size_of' Γ a → (o,i) ∈ lock_singleton Γ a ↔ o = addr_index a ∧
    addr_object_offset Γ a ≤ i < addr_object_offset Γ a + bit_size_of' Γ a.
Proof.
  intros. assert (of_bools (replicate (addr_object_offset Γ a) false
    ++ replicate (bit_size_of' Γ a) true) ≠ ∅).
  { rewrite elem_of_equiv_empty_L.
    intros Hx; destruct (Hx (addr_object_offset Γ a)).
    by rewrite elem_of_of_bools,
      lookup_app_minus_r, lookup_replicate by solve_length. }
  unfold lock_singleton; case_decide; [split|done].
  * intros (?&?&Hi); simplify_map_equality'; split; auto.
    rewrite elem_of_of_bools in Hi.
    destruct (decide (i < addr_object_offset Γ a)).
    { by rewrite lookup_app_l, lookup_replicate in Hi by solve_length. }
    rewrite lookup_app_minus_r in Hi by solve_length.
    apply lookup_replicate_inv in Hi;
      destruct Hi as [_ Hi]; revert Hi; solve_length.
  * intros (->&?&?); eexists; simplify_map_equality'; split; auto.
    by rewrite elem_of_of_bools,
      lookup_app_minus_r, lookup_replicate by solve_length.
Qed.
Lemma elem_of_lock_singleton_typed Γ Γm a τ o i :
  ✓ Γ → (Γ,Γm) ⊢ a : τ → (o,i) ∈ lock_singleton Γ a ↔ o = addr_index a ∧
    addr_object_offset Γ a ≤ i < addr_object_offset Γ a + bit_size_of Γ τ.
Proof.
  intros. rewrite elem_of_lock_singleton by (simplify_type_equality;
    eauto using bit_size_of_pos, addr_typed_type_valid).
  by simplify_type_equality.
Qed.
Lemma lock_singleton_valid Γ Γm a τ :
  ✓ Γ → (Γ,Γm) ⊢ a : τ → ✓{Γm} (lock_singleton Γ a).
Proof.
  intros ?? o i. rewrite elem_of_lock_singleton_typed by eauto.
  intros (->&?&?); eauto using addr_typed_index.
Qed.
Lemma lock_singleton_disjoint Γ Γm a1 a2 τ1 τ2 :
  ✓ Γ → (Γ,Γm) ⊢ a1 : τ1 → addr_strict Γ a1 →
  (Γ,Γm) ⊢ a2 : τ2 → addr_strict Γ a2 →
  a1 ⊥{Γ} a2 → lock_singleton Γ a1 ∩ lock_singleton Γ a2 = ∅.
Proof.
  intros. apply equiv_empty_L. intros [o i].
  rewrite elem_of_intersection, !elem_of_lock_singleton_typed by eauto.
  intros [(->&?&?) (?&?&?)].
  destruct (addr_disjoint_object_offset Γ Γm a1 a2 τ1 τ2); try done; lia.
Qed.
End memory.
