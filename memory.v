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

  Fixpoint mem_insert_array (Γ : env Ti) (a : addr Ti)
      (vs : list (val Ti)) (m : mem Ti) : mem Ti :=
    match vs with
    | [] => m
    | v :: vs => <[a:=v]{Γ}>(mem_insert_array Γ (addr_plus Γ 1 a) vs m)
    end.

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
    (**i 3.) *) ctree_Forall (λ xb, Some Freeable ⊆ pbit_kind xb) w.

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
      '(w,_) ← maybe_Obj x;
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

  Global Instance locks_refine:
      Refine Ti (env Ti) lockset := λ Γ f Γm1 Γm2 Ω1 Ω2,
    (**i 1.) *) ✓{Γm1} Ω1 ∧ ✓{Γm2} Ω2 ∧
    (**i 2.) *) Γm1 ⊑{Γ,f} Γm2 ∧
    (**i 3.) *) (∀ o1 o2 r τ1 i,
      f !! o1 = Some (o2,r) → Γm1 ⊢ o1 : τ1 → index_alive Γm1 o1 →
      i < bit_size_of Γ τ1 →
      (o1,i) ∈ Ω1 ↔ (o2,ref_object_offset Γ r + i) ∈ Ω2).
End memory_operations.

Notation mem_unlock_all m := (mem_unlock (mem_locks m) m).

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
Implicit Types β : bool.
Implicit Types βs : list bool.
Implicit Types xb : pbit Ti.
Implicit Types xbs : list (pbit Ti).
Implicit Types Ω : lockset.

Local Opaque nmap.Nempty.
Arguments union _ _ !_ !_ /.
Arguments difference _ _ !_ !_ /.
Arguments cmap_lookup _ _ _ !_ !_ /.

Hint Resolve Forall_app_2 Forall2_app.
Hint Immediate cmap_lookup_typed.
Hint Immediate ctree_refine_typed_l ctree_refine_typed_r.
Hint Immediate val_typed_type_valid.
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
Lemma mem_alloc_extend Γm o τ : Γm !! o = None → Γm ⊆{⇒} <[o:=(τ,false)]>Γm.
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
      using mem_alloc_extend, memenv_extend_typed, memenv_extend_alive. }
  intros o' w malloc'; rewrite lookup_insert_Some;
    intros [[??]|[??]]; simplify_equality'.
  { exists τ; split_ands; eauto 7 using (ctree_Forall_not _ _ Γm),
     ctree_new_typed, pbit_full_valid, ctree_new_Forall,
     mem_alloc_index_typed, mem_alloc_index_alive. }
  destruct (proj2 Hm o' w malloc')
    as (τ'&?&?&?&?&?); simplify_map_equality'; eauto.
  exists τ'; split_ands; eauto using ctree_typed_weaken, mem_alloc_extend,
    memenv_extend_typed, memenv_extend_alive, mem_alloc_index_alive_neq.
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
Lemma mem_alloc_extend' Γ m o malloc τ :
  ✓ Γ → ✓{Γ} τ → mem_allocable o m → '{m} ⊆{⇒} '{mem_alloc Γ o malloc τ m}.
Proof. eauto using mem_alloc_extend, mem_allocable_memenv_of. Qed.
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
     ∧ ctree_Forall (λ xb, Some Freeable ⊆ pbit_kind xb) w)
   with
   | Some (Obj w true) => cast_if_and
      (decide (addr_is_top_array a))
      (decide (ctree_Forall (λ xb, Some Freeable ⊆ pbit_kind xb) w))
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
Lemma mem_free_extend Γm o : Γm ⊆{⇒} alter (prod_map id (λ _, true)) o Γm.
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
        mem_free_extend, memenv_extend_typed, memenv_extend_alive.
    * destruct (proj2 Hm o' w malloc') as (?&?&?&?&?&?);simplify_type_equality';
        eauto 11 using ctree_typed_type_valid, mem_free_index_alive,
        mem_free_extend, memenv_extend_typed, memenv_extend_alive.
    * destruct (proj1 Hm o' τ) as (?&?&?&?); eauto 10 using
        mem_free_extend, memenv_extend_typed, memenv_extend_alive. }
  intros o' w malloc; rewrite lookup_alter_Some;
    intros [(?&[]&?&?)|[??]]; simplify_map_equality'.
  destruct (proj2 Hm o' w malloc) as (τ'&?&?&?&?&?); eauto.
  exists τ'; split_ands; eauto using
    ctree_typed_weaken, mem_free_index_alive_neq, mem_free_extend,
     mem_free_extend, memenv_extend_typed, memenv_extend_alive.
Qed.
Lemma mem_free_valid' Γ m o : ✓ Γ → ✓{Γ} m → ✓{Γ} (mem_free o m).
Proof.
  unfold valid at 2 3, cmap_valid'; intros. rewrite mem_free_memenv_of.
  eauto using mem_free_valid.
Qed.
Lemma mem_free_extend' m o : '{m} ⊆{⇒} '{mem_free o m}.
Proof. rewrite mem_free_memenv_of; eauto using mem_free_extend. Qed.
Lemma mem_foldr_free_extend m os : '{m} ⊆{⇒} '{foldr mem_free m os}.
Proof.
  induction os; simpl; [done|]. etransitivity; eauto using mem_free_extend'.
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

(** Properties of the [force] function *)
Lemma mem_force_memenv_of Γ Γm m a :
  ✓ Γ → ✓{Γ,Γm} m → is_Some (m !!{Γ} a) → '{mem_force Γ a m} = '{m}.
Proof.
  unfold mem_force, lookupE, mem_lookup. intros ?? [v ?].
  destruct (m !!{Γ} a) as [w|] eqn:?; simplify_equality'.
  by erewrite cmap_alter_memenv_of by eauto.
Qed.
Lemma mem_force_extend Γ Γm m a :
  ✓ Γ → ✓{Γ,Γm} m → is_Some (m !!{Γ} a) → '{m} ⊆{⇒} '{mem_force Γ a m}.
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
Lemma mem_force_union Γ Γm1 m1 m2 a1 v1 τ1 :
  ✓ Γ → ✓{Γ,Γm1} m1 → m1 ⊥ m2 →
  (Γ,Γm1) ⊢ a1 : τ1 → is_Some (m1 !!{Γ} a1) →
  mem_force Γ a1 (m1 ∪ m2) =  mem_force Γ a1 m1 ∪ m2.
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
Lemma mem_insert_extend Γ Γm m a v τ :
  ✓ Γ → ✓{Γ,Γm} m → (Γ,Γm) ⊢ a : τ → mem_writable Γ a m → (Γ,Γm) ⊢ v : τ →
  '{m} ⊆{⇒} '{<[a:=v]{Γ}>m}.
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
(** Horrible premises, should be able to prove this without some. *)
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
    mem_alloc_index_typed', mem_alloc_extend'.
Qed.
Lemma mem_alloc_val_index_typed Γ m malloc o v τ :
  ✓ Γ → ✓{Γ} m → mem_allocable o m →
  (Γ,'{m}) ⊢ v : τ → int_typed (size_of Γ τ) sptrT →
  '{<[addr_top o τ:=v]{Γ}>(mem_alloc Γ o malloc τ m)} ⊢ o : τ.
Proof.
  intros. erewrite mem_insert_memenv_of by eauto using mem_alloc_valid',
    addr_top_typed, mem_alloc_index_typed', mem_alloc_writable_top,
    val_typed_weaken, mem_alloc_extend'; eauto using mem_alloc_index_typed'.
Qed.
Lemma mem_alloc_val_extend Γ m malloc o v τ :
  ✓ Γ → ✓{Γ} m → mem_allocable o m →
  (Γ,'{m}) ⊢ v : τ → int_typed (size_of Γ τ) sptrT →
  '{m} ⊆{⇒} '{<[addr_top o τ:=v]{Γ}>(mem_alloc Γ o malloc τ m)}.
Proof.
  intros. erewrite mem_insert_memenv_of by eauto using mem_alloc_valid',
    addr_top_typed, mem_alloc_index_typed', mem_alloc_writable_top,
    val_typed_weaken, mem_alloc_extend'; eauto using mem_alloc_extend'.
Qed.
Lemma mem_alloc_val_allocable Γ m o malloc v τ o' :
  mem_allocable o' m → o ≠ o' →
  mem_allocable o' (<[addr_top o τ:=v]{Γ}>(mem_alloc Γ o malloc τ m)).
Proof. intros. by apply mem_insert_allocable, mem_alloc_allocable. Qed.
Lemma mem_alloc_val_list_valid Γ m os vs τs :
  ✓ Γ → ✓{Γ} m → mem_allocable_list m os → length os = length vs →
  (Γ,'{m}) ⊢* vs :* τs → Forall (λ τ, int_typed (size_of Γ τ) sptrT) τs →
  (**i 1.) *) ✓{Γ} (mem_alloc_val_list Γ (zip os vs) m) ∧
  (**i 2.) *) '{mem_alloc_val_list Γ (zip os vs) m} ⊢* os :* τs ∧
  (**i 3.) *) '{m} ⊆{⇒} '{mem_alloc_val_list Γ (zip os vs) m}.
Proof.
  rewrite <-Forall2_same_length. intros ? Hm Hfree Hovs Hvs Hτs.
  revert os vs m Hovs Hm Hvs Hfree.
  induction Hτs as [|τ τs ?? IH];
    intros ?? m [|o v os vs ??]; inversion_clear 3;
    decompose_Forall_hyps; simplify_type_equality; auto.
  destruct (IH os vs (<[addr_top o τ:=v]{Γ}> (mem_alloc Γ o false τ m))) as
    (IH1&IH2&IH3); eauto using mem_alloc_val_valid.
  { eauto using Forall2_impl, val_typed_weaken,
      mem_alloc_val_extend, memenv_extend_typed. }
  { by apply mem_insert_allocable_list, mem_alloc_allocable_list. }
  split_ands; eauto using mem_alloc_val_index_typed, memenv_extend_typed.
  transitivity ('{<[addr_top o τ:=v]{Γ}> (mem_alloc Γ o false τ m)});
    eauto using mem_alloc_val_extend.
Qed.
Lemma mem_alloc_val_list_index_typed Γ m os vs τs :
  ✓ Γ → ✓{Γ} m → mem_allocable_list m os → length os = length vs →
  (Γ,'{m}) ⊢* vs :* τs → Forall (λ τ, int_typed (size_of Γ τ) sptrT) τs →
  '{mem_alloc_val_list Γ (zip os vs) m} ⊢* os :* τs.
Proof. intros. eapply mem_alloc_val_list_valid; eauto. Qed.
Lemma mem_alloc_val_list_extend Γ m os vs τs :
  ✓ Γ → ✓{Γ} m → mem_allocable_list m os → length os = length vs →
  (Γ,'{m}) ⊢* vs :* τs → Forall (λ τ, int_typed (size_of Γ τ) sptrT) τs →
  '{m} ⊆{⇒} '{mem_alloc_val_list Γ (zip os vs) m}.
Proof. intros. eapply mem_alloc_val_list_valid; eauto. Qed.

(** ** Non-aliassing results *)
Lemma mem_non_aliasing Γ Γm m a1 a2 τ1 τ2 :
  ✓ Γ → ✓{Γ,Γm} m → (Γ,Γm) ⊢ a1 : τ1 → frozen a1 → addr_is_obj a1 →
  (Γ,Γm) ⊢ a2 : τ2 → frozen a2 → addr_is_obj a2 →
  (**i 1.) *) (∀ j1 j2, addr_plus Γ j1 a1 ⊥{Γ} addr_plus Γ j2 a2) ∨
  (**i 2.) *) τ1 ⊆{Γ} τ2 ∨
  (**i 3.) *) τ2 ⊆{Γ} τ1 ∨
  (**i 4.) *) ∀ j1 j2,
    (∀ v1, <[addr_plus Γ j1 a1:=v1]{Γ}>m !!{Γ} addr_plus Γ j2 a2 = None) ∧
    mem_force Γ (addr_plus Γ j1 a1) m !!{Γ} addr_plus Γ j2 a2 = None ∧
    (∀ v2, <[addr_plus Γ j2 a2:=v2]{Γ}>m !!{Γ} addr_plus Γ j1 a1 = None) ∧
    mem_force Γ (addr_plus Γ j2 a2) m !!{Γ} addr_plus Γ j1 a1 = None.
Proof.
  intros.
  destruct (cmap_non_aliasing Γ Γm m a1 a2 τ1 τ2) as [?|[?|[?|Ha]]]; auto.
  unfold lookupE, mem_lookup, insertE, mem_insert, mem_force.
  by do 3 right; repeat split; intros;
    rewrite ?(proj1 (Ha _ _ _)), ?(proj2 (Ha _ _ _)).
Qed.

(** ** Refinements *)
Lemma mem_lookup_refine Γ f Γm1 Γm2 m1 m2 a1 a2 v1 τ :
  ✓ Γ → m1 ⊑{Γ,f@Γm1↦Γm2} m2 → a1 ⊑{Γ,f@Γm1↦Γm2} a2 : τ →
  m1 !!{Γ} a1 = Some v1 →
  ∃ v2, m2 !!{Γ} a2 = Some v2 ∧ v1 ⊑{Γ,f@Γm1↦Γm2} v2 : τ.
Proof.
  unfold lookupE, mem_lookup. intros.
  destruct (m1 !!{Γ} a1) as [w1|] eqn:?; simplify_option_equality.
  destruct (cmap_lookup_refine Γ f Γm1 Γm2 m1 m2 a1 a2 w1 τ) as (w2&->&?); auto.
  exists (to_val Γ w2); simplify_option_equality by eauto using
    pbits_refine_kind_subseteq, ctree_flatten_refine; eauto using to_val_refine.
Qed.
Lemma mem_force_refine Γ f Γm1 Γm2 m1 m2 a1 a2 τ :
  ✓ Γ → m1 ⊑{Γ,f@Γm1↦Γm2} m2 → a1 ⊑{Γ,f@Γm1↦Γm2} a2 : τ →
  is_Some (m1 !!{Γ} a1) → mem_force Γ a1 m1 ⊑{Γ,f@Γm1↦Γm2} mem_force Γ a2 m2.
Proof.
  unfold lookupE, mem_lookup, mem_force. intros ??? [v1 ?].
  destruct (m1 !!{Γ} a1) as [w1|] eqn:?; simplify_option_equality.
  destruct (cmap_lookup_refine Γ f Γm1 Γm2 m1 m2 a1 a2 w1 τ) as (w2&?&?); auto.
  eapply cmap_alter_refine; eauto using ctree_Forall_not, pbits_mapped,
    pbits_refine_kind_subseteq, ctree_flatten_refine.
Qed.
Lemma mem_force_refine' Γ f m1 m2 a1 a2 τ :
  ✓ Γ → m1 ⊑{Γ,f} m2 → a1 ⊑{Γ,f@'{m1}↦'{m2}} a2 : τ →
  is_Some (m1 !!{Γ} a1) → mem_force Γ a1 m1 ⊑{Γ,f} mem_force Γ a2 m2.
Proof.
  unfold refineM, cmap_refine'; intros ??? [v1 ?].
  destruct (mem_lookup_refine Γ f ('{m1}) ('{m2})
    m1 m2 a1 a2 v1 τ) as (v2&?&?); eauto.
  erewrite !mem_force_memenv_of by eauto using cmap_refine_valid_l',
    cmap_refine_valid_r'; eauto using mem_force_refine.
Qed.
Lemma mem_writable_refine Γ f Γm1 Γm2 m1 m2 a1 a2 τ :
  ✓ Γ → m1 ⊑{Γ,f@Γm1↦Γm2} m2 → a1 ⊑{Γ,f@Γm1↦Γm2} a2 : τ →
  mem_writable Γ a1 m1 → mem_writable Γ a2 m2.
Proof.
  intros ??? (w1&?&?).
  destruct (cmap_lookup_refine Γ f Γm1 Γm2 m1 m2 a1 a2 w1 τ) as (w2&?&?); auto.
  exists w2; eauto using pbits_refine_kind_subseteq, ctree_flatten_refine.
Qed.
Lemma mem_insert_refine Γ f Γm1 Γm2 m1 m2 a1 a2 v1 v2 τ :
  ✓ Γ → m1 ⊑{Γ,f@Γm1↦Γm2} m2 → a1 ⊑{Γ,f@Γm1↦Γm2} a2 : τ → mem_writable Γ a1 m1 →
  v1 ⊑{Γ,f@Γm1↦Γm2} v2 : τ → <[a1:=v1]{Γ}>m1 ⊑{Γ,f@Γm1↦Γm2} <[a2:=v2]{Γ}>m2.
Proof.
  intros ??? (w1&?&?) ?.
  destruct (cmap_lookup_refine Γ f Γm1 Γm2 m1 m2 a1 a2 w1 τ) as (w2&?&?); auto.
  eapply cmap_alter_refine; eauto 1.
  * eapply ctree_Forall_not, pbits_mapped; eauto using pbits_kind_weaken.
  * erewrite <-(pbits_refine_perm _ _ _ _ (ctree_flatten w1) (ctree_flatten w2))
      by eauto using ctree_flatten_refine.
    eapply of_val_refine; eauto.
    + eapply pbits_perm_unshared, pbits_unshared; eauto using
        pbits_kind_weaken, pbits_valid_sep_valid, ctree_flatten_valid.
    + eapply pbits_perm_mapped, pbits_mapped; eauto using
        pbits_kind_weaken, pbits_valid_sep_valid, ctree_flatten_valid.
  * eapply ctree_Forall_not, of_val_flatten_mapped; eauto using
      val_refine_typed_l, of_val_flatten_typed, cmap_lookup_Some.
Qed.
Lemma mem_insert_refine' Γ f m1 m2 a1 a2 v1 v2 τ :
  ✓ Γ → m1 ⊑{Γ,f} m2 → a1 ⊑{Γ,f@'{m1}↦'{m2}} a2 : τ → mem_writable Γ a1 m1 →
  v1 ⊑{Γ,f@'{m1}↦'{m2}} v2 : τ → <[a1:=v1]{Γ}>m1 ⊑{Γ,f} <[a2:=v2]{Γ}>m2.
Proof.
  unfold refineM, cmap_refine'; intros.
  erewrite !mem_insert_memenv_of by eauto using cmap_refine_valid_l',
    cmap_refine_valid_r', addr_refine_typed_l, addr_refine_typed_r,
    val_refine_typed_l, val_refine_typed_r, mem_writable_refine.
  eauto using mem_insert_refine.
Qed.

(* todo: prove a stronger version that allows to allocate multiple objects
on the left and all map to the same object on the right. *)
Lemma mem_refine_extend Γ f Γm1 Γm2 o1 o2 :
  ✓ Γ → Γm1 ⊑{Γ,f} Γm2 → Γm1 !! o1 = None → Γm2 !! o2 = None → ∃ f',
  (**i 1.) *) Γm1 ⊑{Γ,f'} Γm2 ∧
  (**i 2.) *) f' !! o1 = Some (o2,[]) ∧
  (**i 3.) *) mem_inj_extend f f' Γm1 Γm2.
Proof.
  intros ? (?&?&?&?) ??. unfold typed, index_typed, index_alive in *.
  set (f' := mem_inj_map $
    (<[o1:=(o2,[])]> (map_of_collection (f !!) (dom indexset Γm1)))).
  assert (∀ o' τ β, Γm1 !! o' = Some (τ,β) → f' !! o' = f !! o') as help.
  { intros o' τ β ?; unfold lookup at 1, f'; simpl.
    rewrite lookup_insert_ne by naive_solver.
    apply option_eq; intros [o2' r]; simpl.
    rewrite lookup_map_of_collection, elem_of_dom; naive_solver. }
  exists f'; repeat split.
  * intros o1' o1'' o2' r1 r2; unfold lookup, f'; simpl.
    rewrite !lookup_insert_Some, !lookup_map_of_collection, !elem_of_dom.
    intros [[??]|(?&[[??]?]&?)] [[??]|(?&[[??]?]&?)]; naive_solver.
  * intros o1' o2' r' τ Hf' [??]; erewrite help in Hf' by eauto; naive_solver.
  * intros o1' o2' r' τ Hf' [??]; revert Hf'. unfold lookup, f'; simpl.
    rewrite lookup_insert_Some, lookup_map_of_collection, elem_of_dom.
    intros [[??]|(?&[[??]?]&?)]; simplify_map_equality'; naive_solver.
  * intros o1' o2' r' Hf' [??]; erewrite help in Hf' by eauto; naive_solver.
  * by unfold f', lookup; intros; simplify_map_equality'.
  * unfold typed, index_typed; naive_solver.
  * intros o o' r τ [??]. unfold lookup at 1, f'; simpl.
    rewrite lookup_insert_Some, lookup_map_of_collection, elem_of_dom.
    intros [[??]|(?&[[??]?]&?)]; simplify_map_equality'; naive_solver.
Qed.
Lemma mem_alloc_refine_env Γ f Γm1 Γm2 τ o1 o2 :
  Γm1 ⊑{Γ,f} Γm2 → Γm1 !! o1 = None → Γm2 !! o2 = None →
  f !! o1 = Some (o2,[]) → <[o1:=(τ,false)]> Γm1 ⊑{Γ,f} <[o2:=(τ,false)]> Γm2.
Proof.
  intros (?&Htyped&Htyped'&?) ???; split; split_ands; auto.
  * intros o3 o4 r τ3 ? Ho3. destruct (decide (o1 = o3)) as [->|?].
    + destruct Ho3; simplify_map_equality'.
      setoid_rewrite ref_typed_nil; eauto using mem_alloc_index_typed.
    + destruct (Htyped o3 o4 r τ3) as (τ4&?&?); eauto using mem_alloc_extend,
        memenv_extend_typed, mem_alloc_index_typed_inv.
  * intros o3 o4 r τ4 ? Ho4. destruct (decide (o1 = o3)) as [->|?].
    { destruct Ho4; simplify_map_equality'.
      setoid_rewrite ref_typed_nil; eauto using mem_alloc_index_typed. }
    destruct (mem_inj_injective_ne f o1 o2 o3 o4 [] r)
      as [|[??]]; simplify_map_equality; eauto using memenv_refine_injective.
    + destruct (Htyped' o3 o4 r τ4) as (τ3&?&?); eauto using mem_alloc_extend,
        memenv_extend_typed, mem_alloc_index_typed_inv.
    + by destruct (ref_disjoint_nil_inv_l r).
  * intros o3 o4 r ??; destruct (decide (o1 = o3)) as [->|?].
    + simplify_equality; eauto using mem_alloc_index_alive.
    + eauto using mem_alloc_index_alive_neq, mem_alloc_index_alive_inv.
Qed.
Lemma mem_alloc_refine Γ f Γm1 Γm2 m1 m2 malloc τ o1 o2 :
  let Γm1' := <[o1:=(τ,false)]>Γm1 in let Γm2' := <[o2:=(τ,false)]>Γm2 in
  ✓ Γ → m1 ⊑{Γ,f@Γm1↦Γm2} m2 → ✓{Γ} τ → int_typed (size_of Γ τ) sptrT →
  Γm1 !! o1 = None → Γm2 !! o2 = None → f !! o1 = Some (o2,[]) →
  mem_alloc Γ o1 malloc τ m1 ⊑{Γ,f@Γm1'↦Γm2'} mem_alloc Γ o2 malloc τ m2.
Proof.
  simpl; intros ? (?&?&HΓm&Hm) ?????.
  split; split_ands; auto 2 using mem_alloc_valid, mem_alloc_refine_env.
  destruct m1 as [m1], m2 as [m2]; intros o3 o4 r w3 malloc' ?; simpl in *.
  rewrite lookup_insert_Some; intros [[??]|[??]]; simplify_map_equality.
  { exists (ctree_new Γ pbit_full τ) (ctree_new Γ pbit_full τ) τ.
    split_ands; auto. rewrite <-ctree_unflatten_replicate by done.
    apply ctree_unflatten_refine; auto.
    apply Forall2_replicate, PBit_BIndet_refine; auto using perm_full_valid. }
  destruct (mem_inj_injective_ne f o1 o2 o3 o4 [] r)
    as [|[??]]; simplify_map_equality; eauto using memenv_refine_injective.
  * destruct (Hm o3 o4 r w3 malloc') as (w2&w2'&τ2&?&?&?&?); auto.
    exists w2 w2' τ2; eauto 10 using ctree_refine_weaken,
      mem_alloc_extend, mem_alloc_refine_env, mem_inj_extend_reflexive.
  * by destruct (ref_disjoint_nil_inv_l r).
Qed.
Lemma mem_alloc_refine' Γ f m1 m2 malloc τ o1 o2 :
  ✓ Γ → m1 ⊑{Γ,f} m2 → ✓{Γ} τ → int_typed (size_of Γ τ) sptrT →
  mem_allocable o1 m1 → mem_allocable o2 m2 → ∃ f',
  (**i 1.) *) f' !! o1 = Some (o2,[]) ∧
  (**i 2.) *) mem_alloc Γ o1 malloc τ m1 ⊑{Γ,f'} mem_alloc Γ o2 malloc τ m2 ∧
  (**i 3.) *) mem_inj_extend f f' ('{m1}) ('{m2}).
Proof.
  intros. destruct (mem_refine_extend Γ f ('{m1}) ('{m2}) o1 o2) as
    (f'&?&?&?); eauto using mem_allocable_memenv_of,cmap_refine_memenv_refine.
  exists f'; split_ands; auto. unfold refineM, cmap_refine'.
  rewrite !mem_alloc_memenv_of by done.
  eauto using mem_alloc_refine, mem_allocable_memenv_of, cmap_refine_weaken.
Qed.
Lemma mem_alloc_refine'' Γ m1 m2 malloc τ o :
  ✓ Γ → m1 ⊑{Γ} m2 → ✓{Γ} τ → int_typed (size_of Γ τ) sptrT →
  mem_allocable o m1 → mem_allocable o m2 →
  mem_alloc Γ o malloc τ m1 ⊑{Γ} mem_alloc Γ o malloc τ m2.
Proof.
  intros. unfold refineM, cmap_refine'. rewrite !mem_alloc_memenv_of by done.
  eauto using mem_alloc_refine, mem_allocable_memenv_of, cmap_refine_weaken.
Qed.
Lemma mem_alloc_val_refine' Γ f m1 m2 malloc o1 o2 v1 v2 τ :
  ✓ Γ → m1 ⊑{Γ,f} m2 → v1 ⊑{Γ,f@'{m1}↦'{m2}} v2 : τ →
  int_typed (size_of Γ τ) sptrT →
  mem_allocable o1 m1 → mem_allocable o2 m2 → ∃ f',
  (**i 1.) *) f' !! o1 = Some (o2,[]) ∧
  (**i 2.) *) <[addr_top o1 τ:=v1]{Γ}>(mem_alloc Γ o1 malloc τ m1)
      ⊑{Γ,f'} <[addr_top o2 τ:=v2]{Γ}>(mem_alloc Γ o2 malloc τ m2) ∧
  (**i 3.) *) mem_inj_extend f f' ('{m1}) ('{m2}).
Proof.
  intros.
  assert (✓{Γ} τ) by eauto using val_refine_typed_l, val_typed_type_valid.
  destruct (mem_alloc_refine' Γ f m1 m2 malloc τ o1 o2) as (f'&?&?&?); auto.
  exists f'; split_ands; eauto 10 using mem_insert_refine',
    mem_alloc_writable_top, addr_top_refine, mem_alloc_index_typed',
    cmap_refine_memenv_refine, val_refine_weaken, mem_alloc_extend'.
Qed.
Hint Immediate cmap_refine_valid_l' cmap_refine_valid_r'.
Hint Immediate cmap_refine_memenv_refine.
Lemma mem_alloc_val_list_refine' Γ f m1 m2 os1 os2 vs1 vs2 τs :
  ✓ Γ → m1 ⊑{Γ,f} m2 → vs1 ⊑{Γ,f@'{m1}↦'{m2}}* vs2 :* τs →
  length os1 = length vs1 → length os2 = length vs2 →
  Forall (λ τ, int_typed (size_of Γ τ) sptrT) τs →
  mem_allocable_list m1 os1 → mem_allocable_list m2 os2 → ∃ f',
  (**i 1.) *) Forall2 (λ o1 o2, f' !! o1 = Some (o2,[])) os1 os2 ∧
  (**i 2.) *) mem_alloc_val_list Γ (zip os1 vs1) m1
      ⊑{Γ,f'} mem_alloc_val_list Γ (zip os2 vs2) m2 ∧
  (**i 3.) *) mem_inj_extend f f' ('{m1}) ('{m2}).
Proof.
  rewrite <-!Forall2_same_length. intros ? Hm Hvs Hovs1 Hovs2 Hτs Hos1 Hos2.
  revert f os1 os2 vs1 vs2 m1 m2 Hm Hos1 Hos2 Hvs Hovs1 Hovs2.
  induction Hτs as [|τ τs ?? IH];
    intros f ?? vs1' vs2' m1 m2 ? [|o1 os1 ???] [|o2 os2 ???];
    inversion_clear 1 as [|v1 v2 ? vs1 vs2 ?];
    intros; decompose_Forall_hyps; eauto using mem_inj_extend_reflexive.
  assert ((Γ,'{m1}) ⊢ v1 : τ) by eauto using val_refine_typed_l.
  assert ((Γ,'{m2}) ⊢ v2 : τ) by eauto using val_refine_typed_r.
  assert (✓{Γ} τ) by eauto using val_typed_type_valid.
  destruct (mem_alloc_val_refine' Γ f m1 m2 false o1 o2 v1 v2 τ)
    as (f'&?&?&?); auto; simplify_type_equality.
  edestruct (IH f' os1 os2 vs1 vs2) as (f''&?&?&?); eauto.
  { rewrite mem_insert_allocable_list; eauto using mem_alloc_allocable_list. }
  { rewrite mem_insert_allocable_list; eauto using mem_alloc_allocable_list. }
  { eauto using vals_refine_weaken, mem_alloc_val_extend. }
  exists f''; split_ands; eauto using mem_inj_extend_transitive.
  * constructor; [|done]. transitivity (f' !! o1);
      eauto using eq_sym, mem_alloc_val_index_typed, mem_inj_extend_left.
  * eauto using mem_inj_extend_transitive, mem_alloc_val_extend.
Qed.
Lemma mem_freeable_refine Γ f Γm1 Γm2 m1 m2 a1 a2 τ :
  ✓ Γ → m1 ⊑{Γ,f@Γm1↦Γm2} m2 →
  a1 ⊑{Γ,f@Γm1↦Γm2} a2 : τ → mem_freeable a1 m1 → mem_freeable a2 m2.
Proof.
  intros ? (_&_&_&Hm) ? (w1&Ha&?&?).
  rewrite addr_is_top_array_alt in Ha by eauto using addr_refine_typed_l.
  destruct Ha as (τ'&n&?&Ha1&?).
  destruct (addr_ref_refine Γ f Γm1 Γm2 a1 a2 τ) as (r&?&Ha2); auto.
  destruct (Hm (addr_index a1) (addr_index a2) r w1 true)
    as (?&w2&τ''&?&?&?&Hr); auto; specialize (Hr I); simplify_equality'.
  exists w2. rewrite addr_is_top_array_alt by eauto using addr_refine_typed_r.
  erewrite <-addr_ref_byte_refine, Ha2, (right_id_L [] (++)), Ha1 by eauto.
  split_ands; eauto using pbits_refine_kind_subseteq, ctree_flatten_refine.
  exists τ' n; split_ands; eauto using addr_strict_refine.
Qed.
Lemma mem_freeable_index_refine Γ f Γm1 Γm2 m1 m2 a1 a2 τ :
  ✓ Γ → m1 ⊑{Γ,f@Γm1↦Γm2} m2 → a1 ⊑{Γ,f@Γm1↦Γm2} a2 : τ →
  mem_freeable a1 m1 → f !! addr_index a1 = Some (addr_index a2, []).
Proof.
  intros ? (_&_&_&Hm) ? (w1&Ha&?&?).
  rewrite addr_is_top_array_alt in Ha by eauto using addr_refine_typed_l.
  destruct Ha as (τ'&n&?&Ha1&?).
  destruct (addr_ref_refine Γ f Γm1 Γm2 a1 a2 τ) as (r&?&Ha2); naive_solver.
Qed.
Lemma mem_free_refine_env_l Γ f Γm1 Γm2 o :
  Γm1 ⊑{Γ,f} Γm2 → alter (prod_map id (λ _, true)) o Γm1 ⊑{Γ,f} Γm2.
Proof.
  intros (?&Htyped&Htyped'&?); split; split_ands; auto.
  * eauto using mem_free_index_typed_inv.
  * naive_solver eauto using mem_free_extend, memenv_extend_typed.
  * eauto using mem_free_index_alive_inv.
Qed.
Lemma mem_free_refine_env_r Γ f Γm1 Γm2 o :
  Γm1 ⊑{Γ,f} Γm2 → (∀ o' r, f !! o' = Some (o,r) → ¬index_alive Γm1 o') →
  Γm1 ⊑{Γ,f} alter (prod_map id (λ _, true)) o Γm2.
Proof.
  intros (?&?&?&?) Hf; split; split_ands; auto.
  * naive_solver eauto using mem_free_extend, memenv_extend_typed.
  * eauto using mem_free_index_typed_inv.
  * intros o1 o2 r ??.
    destruct (decide (o2 = o)) as [->|?]; [by destruct (Hf o1 r)|].
    eauto using mem_free_index_alive_neq.
Qed.
Lemma mem_free_refine_l Γ f Γm1 Γm2 m1 m2 o :
  let Γm1' := alter (prod_map id (λ _, true)) o Γm1 in
  ✓ Γ → m1 ⊑{Γ,f@Γm1↦Γm2} m2 → mem_free o m1 ⊑{Γ,f@Γm1'↦Γm2} m2.
Proof.
  simpl; intros ?(?&?&?&Hm).
  split; split_ands; auto using mem_free_valid, mem_free_refine_env_l.
  destruct m1 as [m1], m2 as [m2]; simpl in *.
  intros o1 o2 r w1 malloc ?; rewrite lookup_alter_Some;
    intros [(?&[?|??]&?&?)|[??]]; simplify_equality'; eauto.
  destruct (Hm o1 o2 r w1 malloc) as (w2&w2'&τ2&?&?&?&?); auto.
  exists w2 w2' τ2; eauto 10 using ctree_refine_weaken,
    mem_free_extend, mem_free_refine_env_l, mem_inj_extend_reflexive.
Qed.
Lemma mem_free_refine_r Γ f Γm1 Γm2 m1 m2 o :
  let Γm2' := alter (prod_map id (λ _, true)) o Γm2 in ✓ Γ →
  (∀ o' r, f !! o' = Some (o,r) → ¬index_alive Γm1 o') →
  m1 ⊑{Γ,f@Γm1↦Γm2} m2 → m1 ⊑{Γ,f@Γm1↦Γm2'} mem_free o m2.
Proof.
  simpl; intros ? Hf (Hm1&?&?&Hm).
  split; split_ands; auto using mem_free_valid, mem_free_refine_env_r.
  destruct m1 as [m1], m2 as [m2]; simpl in *; intros o1 o2 r w1 malloc ??.
  destruct (proj2 Hm1 o1 w1 malloc) as (τ1&?&?&_); auto.
  destruct (decide (o2 = o)) as [->|?]; [by destruct (Hf o1 r)|].
  destruct (Hm o1 o2 r w1 malloc) as (w2&w2'&τ2&?&?&?&?); auto.
  exists w2 w2' τ2; simplify_map_equality; eauto 7 using ctree_refine_weaken,
    mem_free_extend, mem_free_refine_env_r, mem_inj_extend_reflexive.
Qed.
Lemma mem_free_refine' Γ f m1 m2 o1 o2 :
  ✓ Γ → m1 ⊑{Γ,f} m2 → f !! o1 = Some (o2,[]) →
  mem_free o1 m1 ⊑{Γ,f} mem_free o2 m2.
Proof.
  unfold refineM, cmap_refine'; intros ? Hm ?; rewrite !mem_free_memenv_of.
  eapply mem_free_refine_r; eauto using mem_free_refine_l.
  destruct Hm as (_&_&(?&?&_)&_); intros o1' r ?.
  destruct (mem_inj_injective_alt f o1 o1' o2 [] r) as [->|[??]]; auto.
  * eauto using mem_free_index_alive.
  * by destruct (ref_disjoint_nil_inv_l r).
Qed.
Lemma mem_foldr_free_refine Γ f m1 m2 os1 os2 :
  ✓ Γ → m1 ⊑{Γ,f} m2 → Forall2 (λ o1 o2, f !! o1 = Some (o2, [])) os1 os2 →
  foldr mem_free m1 os1 ⊑{Γ,f} foldr mem_free m2 os2.
Proof. induction 3; simpl; auto using mem_free_refine'. Qed.

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
Lemma mem_lock_extend Γ Γm m a  :
  ✓ Γ → ✓{Γ,Γm} m → mem_writable Γ a m → '{m} ⊆{⇒} '{mem_lock Γ a m}.
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
Lemma mem_unlock_extend m Ω : '{m} ⊆{⇒} '{mem_unlock Ω m}.
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

Lemma locks_refine_id Γ Γm Ω : ✓{Γm} Ω → Ω ⊑{Γ@Γm} Ω.
Proof.
  split; split_ands; intros; simplify_equality'; eauto using memenv_refine_id.
Qed.
Lemma locks_refine_compose Γ f g Γm1 Γm2 Γm3 Ω1 Ω2 Ω3 :
  ✓ Γ → Ω1 ⊑{Γ,f@Γm1↦Γm2} Ω2 → Ω2 ⊑{Γ,g@Γm2↦Γm3} Ω3 → Ω1 ⊑{Γ,f ◎ g@Γm1↦Γm3} Ω3.
Proof.
  intros ? (?&?&HΓm12&HΩ12) (?&?&HΓm23&HΩ23);
    split; split_ands; eauto using memenv_refine_compose.
  destruct HΓm12 as (?&HΓm12&?&?), HΓm23 as (?&HΓm23&?&?); intros o1 o3 r τ1 i.
  rewrite lookup_mem_inj_compose_Some; intros (o2&r2&r3&?&?&->) ???.
  destruct (HΓm12 o1 o2 r2 τ1) as (τ2&?&?); auto.
  destruct (HΓm23 o2 o3 r3 τ2) as (τ3&?&?); auto.
  assert (ref_object_offset Γ r2 + i < bit_size_of Γ τ2).
  { apply Nat.lt_le_trans with
      (ref_object_offset Γ r2 + bit_size_of Γ τ1); [lia|].
    eauto using ref_object_offset_size. }
  by rewrite HΩ12, HΩ23, ref_object_offset_app, Nat.add_assoc,
    (Nat.add_comm (ref_object_offset Γ r2)) by eauto.
Qed.
Lemma locks_refine_valid_l Γ f Γm1 Γm2 Ω1 Ω2 : Ω1 ⊑{Γ,f@Γm1↦Γm2} Ω2 → ✓{Γm1} Ω1.
Proof. by intros (?&?&?&?). Qed.
Lemma locks_refine_valid_r Γ f Γm1 Γm2 Ω1 Ω2 : Ω1 ⊑{Γ,f@Γm1↦Γm2} Ω2 → ✓{Γm2} Ω2.
Proof. by intros (?&?&?&?). Qed.
Lemma locks_refine_weaken Γ f f' Γm1 Γm2 Γm1' Γm2' Ω1 Ω2 :
  ✓ Γ → Ω1 ⊑{Γ,f@Γm1↦Γm2} Ω2 → Γm1' ⊑{Γ,f'} Γm2' → Γm1 ⊆{⇒} Γm1' →
  Γm2 ⊆{⇒} Γm2' → mem_inj_extend f f' Γm1 Γm2 → Ω1 ⊑{Γ,f'@Γm1'↦Γm2'} Ω2.
Proof.
  intros ? (HΩ1&HΩ2&(_&_&Htyped'&_)&HΩ) ? HΓm ? [??];
    split; split_ands; eauto 2 using lockset_valid_weaken.
  intros o1 o2 r τ1 i ????; split.
  * intros ?. destruct (HΩ1 o1 i) as [τ1' ?]; auto.
    assert (τ1 = τ1') by eauto using typed_unique, memenv_extend_typed.
    simplify_type_equality.
    by erewrite <-HΩ by eauto using memenv_extend_alive, option_eq_1.
  * intros ?. destruct (HΩ2 o2 (ref_object_offset Γ r + i)) as [τ2' ?]; auto.
    destruct (Htyped' o1 o2 r τ2') as (τ1'&?&?); eauto.
    assert (τ1 = τ1') by eauto using typed_unique, memenv_extend_typed.
    simplify_type_equality. by erewrite HΩ by eauto using memenv_extend_alive.
Qed.
Lemma locks_empty_refine Γ f Γm1 Γm2 :
  Γm1 ⊑{Γ,f} Γm2 → (∅ : lockset) ⊑{Γ,f@Γm1↦Γm2} ∅.
Proof. split; split_ands; eauto using lockset_empty_valid; solve_elem_of. Qed.
Lemma mem_locks_refine Γ f m1 m2 :
  ✓ Γ → m1 ⊑{Γ,f} m2 → mem_locks m1 ⊑{Γ,f@'{m1}↦'{m2}} mem_locks m2.
Proof.
  intros ? (Hm1&Hm2&?&Hm); split; split_ands; auto using mem_locks_valid.
  intros o1 o2 r σ1 i ?? [σ1' ?] ?. assert (∃ w1 malloc,
    cmap_car m1 !! o1 = Some (Obj w1 malloc)) as (w1&malloc&?).
  { destruct m1 as [m1]; simplify_map_equality'.
    destruct (m1 !! o1) as [[]|]; naive_solver. }
  destruct (Hm o1 o2 r w1 malloc) as (w2'&w2&τ2&?&?&?&?); auto; clear Hm.
  assert ((Γ,'{m1}) ⊢ w1 : τ2) by eauto.
  destruct (proj2 Hm1 o1 w1 malloc) as (?&?&?&?&_),
   (proj2 Hm2 o2 w2' malloc) as (τ'&?&?&?&_); auto; simplify_type_equality'.
  erewrite !elem_of_mem_locks_alt, <-!list_lookup_fmap by eauto.
  erewrite pbits_refine_locked; eauto using ctree_flatten_refine.
  rewrite <-(ctree_lookup_flatten Γ ('{m2}) w2' τ' r w2 σ1)
    by eauto using ctree_refine_typed_r, ctree_lookup_freeze.
  by rewrite pbits_locked_mask, fmap_take, fmap_drop, lookup_take, lookup_drop.
Qed.
Lemma mem_lock_refine Γ f Γm1 Γm2 m1 m2 a1 a2 τ : 
  ✓ Γ → m1 ⊑{Γ,f@Γm1↦Γm2} m2 → a1 ⊑{Γ,f@Γm1↦Γm2} a2 : τ →
  mem_writable Γ a1 m1 → mem_lock Γ a1 m1 ⊑{Γ,f@Γm1↦Γm2} mem_lock Γ a2 m2.
Proof.
  intros ??? (w1&?&?). assert (∀ xb, pbit_indetify xb = xb →
    pbit_indetify (pbit_lock xb) = pbit_lock xb) by (by intros ? <-).
  destruct (cmap_lookup_refine Γ f Γm1 Γm2 m1 m2 a1 a2 w1 τ) as (w2&?&?); auto.
  eapply cmap_alter_refine; eauto 1.
  * eapply ctree_Forall_not, pbits_mapped; eauto using pbits_kind_weaken.
  * apply ctree_map_refine; eauto using pbit_lock_unshared,
      pbits_lock_refine, ctree_flatten_refine. 
  * eapply ctree_Forall_not; eauto using ctree_map_typed,
      pbits_lock_valid, ctree_flatten_valid. rewrite ctree_flatten_map.
    eauto using pbits_lock_mapped, pbits_mapped, pbits_kind_weaken.
Qed.
Lemma mem_lock_refine' Γ f m1 m2 a1 a2 τ : 
  ✓ Γ → m1 ⊑{Γ,f} m2 → a1 ⊑{Γ,f@'{m1}↦'{m2}} a2 : τ →
  mem_writable Γ a1 m1 → mem_lock Γ a1 m1 ⊑{Γ,f} mem_lock Γ a2 m2.
Proof.
  intros. unfold refineM, cmap_refine'. erewrite !mem_lock_memenv_of by eauto
    using cmap_refine_valid_l, cmap_refine_valid_r, mem_writable_refine.
  eauto using mem_lock_refine.
Qed.
Lemma ctree_unlock_refine Γ f Γm1 Γm2 w1 w2 τ βs :
  ✓ Γ → w1 ⊑{Γ,f@Γm1↦Γm2} w2 : τ → length βs = bit_size_of Γ τ →
  ctree_merge true pbit_unlock_if w1 βs
    ⊑{Γ,f@Γm1↦Γm2} ctree_merge true pbit_unlock_if w2 βs : τ.
Proof.
  intros HΓ Hw Hlen.
  apply ctree_leaf_refine_refine; eauto using ctree_unlock_typed.
  revert w1 w2 τ Hw βs Hlen.
  refine (ctree_refine_ind _ _ _ _ _ _ _ _ _ _ _); simpl.
  * constructor; auto using pbits_unlock_refine.
  * intros τ n ws1 ws2 -> ? IH _ βs. rewrite bit_size_of_array. intros Hlen.
    constructor. revert βs Hlen. induction IH; intros; decompose_Forall_hyps;
      erewrite ?Forall2_length by eauto using ctree_flatten_refine; auto.
  * intros s τs wxbss1 wxbss2 Hs Hws IH Hxbss _ _ Hpad βs.
    erewrite bit_size_of_struct by eauto; clear Hs. constructor.
    + revert wxbss1 wxbss2 βs Hws IH Hxbss Hlen Hpad. unfold field_bit_padding.
      induction (bit_size_of_fields _ τs HΓ);
        intros [|[w1 xbs1] ?] [|[w2 xbs2] ?];
        do 2 inversion_clear 1; intros; decompose_Forall_hyps; [done|].
      erewrite ?ctree_flatten_length, <-(Forall2_length _ xbs1 xbs2) by eauto.
      constructor; eauto.
    + clear Hlen IH Hpad. revert βs. induction Hws as [|[w1 xbs1] [w2 xbs2]];
        intros; decompose_Forall_hyps; auto.
      erewrite ?ctree_flatten_length, <-(Forall2_length _ xbs1 xbs2) by eauto.
      constructor; eauto using pbits_unlock_refine.
  * intros. erewrite Forall2_length by eauto using ctree_flatten_refine.
    constructor; auto using pbits_unlock_refine.
  * constructor; auto using pbits_unlock_refine.
  * intros s i τs w1 xbs1 xbs2 τ ???????? βs ?.
    erewrite ctree_flatten_length by eauto.
    constructor; auto using pbits_unlock_unshared.
    rewrite ctree_flatten_merge, <-zip_with_app, take_drop by auto.
    auto using pbits_unlock_refine.
Qed.
Lemma mem_unlock_refine Γ f Γm1 Γm2 m1 m2 Ω1 Ω2 :
  ✓ Γ → m1 ⊑{Γ,f@Γm1↦Γm2} m2 → Ω1 ⊑{Γ,f@Γm1↦Γm2} Ω2 →
  mem_unlock Ω1 m1 ⊑{Γ,f@Γm1↦Γm2} mem_unlock Ω2 m2.
Proof.
  assert (∀ xb β,
    pbit_unlock_if (pbit_indetify xb) β = pbit_indetify (pbit_unlock_if xb β)).
  { by intros ? []. }
  assert (∀ xb β, sep_unshared xb → sep_unshared (pbit_unlock_if xb β)).
  { intros ? []; eauto using pbit_unlock_unshared. }
  assert (∀ n xbs,
    length xbs = n → zip_with pbit_unlock_if xbs (replicate n false) = xbs).
  { intros n xbs <-. rewrite zip_with_replicate_r by auto.
    by elim xbs; intros; f_equal'. }
  intros ? (Hm1&Hm2&?&Hm) (_&_&_&HΩ);
    split; split_ands; auto using mem_unlock_valid; intros o1 o2 r w1 β ? Hw1.
  destruct m1 as [m1], m2 as [m2], Ω1 as [Ω1 HΩ1], Ω2 as [Ω2 HΩ2]; simpl in *.
  unfold elem_of, lockset_elem_of in HΩ; simpl in HΩ; clear HΩ1 HΩ2.
  rewrite lookup_merge in Hw1 |- * by done.
  destruct (m1 !! o1) as [[|w1' β']|] eqn:?; try by destruct (Ω1 !! o1).
  destruct (Hm o1 o2 r w1' β') as (w2&w2'&τ1&Ho2&?&?&?); auto; clear Hm.
  assert ((Γ,Γm1) ⊢ w1' : τ1) by eauto using ctree_refine_typed_l.
  assert ((Γ,Γm2) ⊢ w2' : τ1) by eauto using ctree_refine_typed_r.
  destruct (proj2 Hm1 o1 w1' β')as (?&?&?&?&_),
    (proj2 Hm2 o2 w2 β') as (τ2&?&?&?&_); auto; simplify_type_equality.
  destruct (ctree_lookup_Some Γ Γm2 w2 τ2 (freeze true <$> r) w2')
    as (τ1'&?&?); auto; simplify_type_equality.
  assert (ref_object_offset Γ (freeze true <$> r) + bit_size_of Γ τ1
    ≤ bit_size_of Γ τ2) by eauto using ref_object_offset_size.
  erewrite Ho2, ctree_flatten_length by eauto.
  destruct (Ω1 !! o1) as [ω1|] eqn:?; simplify_equality'.
  { erewrite ctree_flatten_length by eauto. destruct (Ω2 !! o2) as [ω2|] eqn:?.
    * assert (take (bit_size_of Γ τ1) (drop (ref_object_offset Γ
        (freeze true <$> r)) (to_bools (bit_size_of Γ τ2) ω2))
        = to_bools (bit_size_of Γ τ1) ω1) as Hω2.
      { apply list_eq_same_length with (bit_size_of Γ τ1); try done.
        intros i β1 β2 ?.
        specialize (HΩ o1 o2 r τ1 i); feed specialize HΩ; auto.
        assert (i ∈ ω1 ↔ ref_object_offset Γ r + i ∈ ω2) as Hi by naive_solver.
        rewrite lookup_take, lookup_drop, !lookup_to_bools, Hi by omega.
        rewrite ref_object_offset_freeze. destruct β1, β2; intuition.   }
      do 3 eexists; split_ands; eauto using ctree_lookup_merge.
      rewrite Hω2; eauto using ctree_unlock_refine.
    * assert (to_bools (bit_size_of Γ τ1) ω1
        = replicate (bit_size_of Γ τ1) false) as Hω.
      { apply list_eq_same_length with (bit_size_of Γ τ1); try done.
        intros i β1 β2 ?. rewrite lookup_replicate by done.
        intros Hβ1 ?; destruct β1; simplify_equality'; try done.
        rewrite lookup_to_bools_true in Hβ1 by omega.
        specialize (HΩ o1 o2 r τ1 i); feed specialize HΩ; auto.
        destruct (proj1 HΩ) as (?&?&?); simplify_equality; eauto. }
      do 3 eexists; split_ands; eauto.
      rewrite Hω, ctree_merge_id by auto; eauto. }
  destruct (Ω2 !! o2) as [ω2|] eqn:?; [|by eauto 7].
  assert (take (bit_size_of Γ τ1) (drop (ref_object_offset Γ 
    (freeze true <$> r)) (to_bools (bit_size_of Γ τ2) ω2))
    = replicate (bit_size_of Γ τ1) false) as Hω2.
  { apply list_eq_same_length with (bit_size_of Γ τ1); try done.
    intros i β1 β2 ?.
    rewrite lookup_take, lookup_drop, lookup_replicate by done.
    intros Hβ1 ?; destruct β1; simplify_equality'; try done.
    rewrite lookup_to_bools_true, ref_object_offset_freeze in Hβ1 by omega.
    specialize (HΩ o1 o2 r τ1 i); feed specialize HΩ; auto.
    destruct (proj2 HΩ) as (?&?&?); simplify_equality; eauto. }
  do 3 eexists; split_ands; eauto using ctree_lookup_merge.
  rewrite Hω2, ctree_merge_id by auto; eauto.
Qed.
Lemma mem_unlock_refine' Γ f m1 m2 Ω1 Ω2 :
  ✓ Γ → m1 ⊑{Γ,f} m2 → Ω1 ⊑{Γ,f@'{m1}↦'{m2}} Ω2 →
  mem_unlock Ω1 m1 ⊑{Γ,f} mem_unlock Ω2 m2.
Proof.
  unfold refineM, cmap_refine'. rewrite !mem_unlock_memenv_of.
  eauto using mem_unlock_refine.
Qed.
Lemma lock_singleton_refine Γ f Γm1 Γm2 a1 a2 σ :
  ✓ Γ → Γm1 ⊑{Γ,f} Γm2 → a1 ⊑{Γ,f@Γm1↦Γm2} a2 : σ → addr_strict Γ a1 →
  lock_singleton Γ a1 ⊑{Γ,f@Γm1↦Γm2} lock_singleton Γ a2.
Proof.
  intros ? Hm Ha ?.
  assert ((Γ,Γm1) ⊢ a1 : σ) by eauto using addr_refine_typed_l.
  assert ((Γ,Γm2) ⊢ a2 : σ) by eauto using addr_refine_typed_r.
  split; split_ands; eauto using lock_singleton_valid.
  destruct Hm as (?&Hm&?); intros o1 o2 r τ i ????.
  rewrite !elem_of_lock_singleton_typed by eauto.
  erewrite !addr_object_offset_alt by eauto using addr_strict_refine.
  destruct (addr_ref_refine Γ f Γm1 Γm2 a1 a2 σ) as (r'&?&Ha2); auto.
  erewrite Ha2, <-(addr_ref_byte_refine _ _ _ _ a1 a2) by eauto.
  rewrite !ref_object_offset_app, ref_object_offset_freeze.
  split; [intros (->&?&?); simplify_equality'; intuition lia|intros (->&?&?)].
  destruct (mem_inj_injective_alt f o1 (addr_index a1) (addr_index a2) r r')
    as [->|[??]]; simplify_equality'; auto.
  { intuition lia. }
  exfalso. destruct (Hm o1 (addr_index a2) r τ) as (τ'&?&?); auto.
  destruct (Hm (addr_index a1) (addr_index a2)
    r' (addr_type_object a1)) as (?&?&?); eauto using addr_typed_index.
  simplify_type_equality.
  assert (addr_object_offset Γ a1 + bit_size_of Γ σ ≤ bit_size_of Γ
    (addr_type_object a1)) as Hlen by eauto using addr_object_offset_lt.
  erewrite addr_object_offset_alt in Hlen by eauto.
  destruct (ref_disjoint_object_offset Γ τ' r r' τ
    (addr_type_object a1)); intuition lia.
Qed.
Lemma locks_union_refine Γ f Γm1 Γm2 Ω1 Ω2 Ω1' Ω2' :
  Ω1 ⊑{Γ,f@Γm1↦Γm2} Ω2 → Ω1' ⊑{Γ,f@Γm1↦Γm2} Ω2' →
  Ω1 ∪ Ω1' ⊑{Γ,f@Γm1↦Γm2} Ω2 ∪ Ω2'.
Proof.
  intros (?&?&?&HΩ) (?&?&_&HΩ'); split; split_ands; auto using lockset_union_valid.
  intros o1 o2 r τ1 i ????. by rewrite !elem_of_union, HΩ, HΩ' by eauto.
Qed.
Lemma locks_union_list_refine Γ f Γm1 Γm2 Ωs1 Ωs2 :
  Γm1 ⊑{Γ,f} Γm2 → Ωs1 ⊑{Γ,f@Γm1↦Γm2}* Ωs2 → ⋃ Ωs1 ⊑{Γ,f@Γm1↦Γm2} ⋃ Ωs2.
Proof. induction 2; simpl; eauto using locks_union_refine, locks_empty_refine. Qed.
End memory.
