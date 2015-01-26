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
  Definition mem_freeable_perm (o : index) (m : mem Ti) : Prop := ∃ w,
    (**i 1.) *) cmap_car m !! o = Some (Obj w true) ∧
    (**i 2.) *) ctree_Forall (λ xb, tagged_perm xb = perm_full) w.
  Definition mem_freeable (a : addr Ti) (m : mem Ti) : Prop :=
    (**i 1.) *) addr_is_top_array a ∧
    (**i 2.) *) mem_freeable_perm (addr_index a) m.

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
  Definition mem_singleton (Γ : env Ti) (a : addr Ti)
      (malloc : bool) (x : perm) (v : val Ti) : mem Ti :=
    let w := of_val Γ (replicate (bit_size_of Γ (type_of v)) x) v in
    cmap_singleton Γ a malloc w.

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
    let n := ptr_bit_size_of Γ (type_of a) in
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
Implicit Types w : mtree Ti.
Implicit Types v : val Ti.
Implicit Types m : mem Ti.
Implicit Types α β : bool.
Implicit Types βs : list bool.
Implicit Types xb : pbit Ti.
Implicit Types xbs : list (pbit Ti).
Implicit Types Ω : lockset.

Local Opaque nmap.Nempty.
Arguments cmap_lookup _ _ _ !_ !_ /.

Hint Resolve Forall_app_2 Forall2_app.
Hint Immediate cmap_lookup_typed val_typed_type_valid.
Hint Extern 0 (Separation _) => apply (_ : Separation (pbit Ti)).

Ltac solve_length := repeat first 
  [ rewrite take_length | rewrite drop_length | rewrite app_length
  | rewrite zip_with_length | rewrite replicate_length | rewrite resize_length
  | rewrite fmap_length | erewrite ctree_flatten_length by eauto
  | erewrite val_flatten_length by eauto | rewrite to_bools_length
  | rewrite bit_size_of_uchar ]; lia.
Hint Extern 0 (length _ = _) => solve_length.
Hint Extern 0 (_ ≤ length _) => solve_length.
Hint Extern 0 (length _ ≤ _) => solve_length.

Lemma mem_writable_weaken Γ1 Γ2 Γm m a σ :
  ✓ Γ1 → (Γ1,Γm) ⊢ a : Some σ → mem_writable Γ1 a m →
  Γ1 ⊆ Γ2 → mem_writable Γ2 a m.
Proof. intros ?? (w&?&?) ?; exists w; eauto using cmap_lookup_weaken. Qed.
Lemma mem_writable_all_weaken Γ1 Γ2 m :
  ✓ Γ1 → ✓{Γ1} m → mem_writable_all Γ1 m → Γ1 ⊆ Γ2 → mem_writable_all Γ2 m.
Proof.
  intros ? Hm ?? o τ ?; eapply mem_writable_weaken; eauto using
    addr_top_typed, index_typed_representable, index_typed_valid.
Qed.
Lemma mem_writable_all_empty Γ : mem_writable_all Γ ∅.
Proof. intros ?? [??]; simplify_map_equality'. Qed.
Lemma mem_erase_writable Γ m a :
  mem_writable Γ a (cmap_erase m) = mem_writable Γ a m.
Proof. unfold mem_writable; simpl. by rewrite cmap_lookup_erase. Qed.

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
Lemma mem_erase_alloc Γ m o malloc τ :
  cmap_erase (mem_alloc Γ o malloc τ m) = mem_alloc Γ o malloc τ (cmap_erase m).
Proof.
  destruct m as [m]; f_equal'; apply map_eq; intros o'.
  by destruct (decide (o' = o)); simplify_map_equality.
Qed.

(** ** Properties of the [mem_free] fucntion *)
Global Instance mem_freeable_perm_dec o m : Decision (mem_freeable_perm o m).
Proof.
  refine
   match cmap_car m !! o as x return Decision (∃ w, x = Some (Obj w true)
     ∧ ctree_Forall (λ xb, tagged_perm xb = perm_full) w)
   with
   | Some (Obj w true) => cast_if
      (decide (ctree_Forall (λ xb, tagged_perm xb = perm_full) w))
   | _ => right _
   end; abstract naive_solver.
Defined.
Global Instance mem_freeable_dec a m : Decision (mem_freeable a m) := _.
Lemma mem_free_memenv_of m o :
  '{mem_free o m} = alter (prod_map id (λ _, true)) o ('{m}).
Proof.
  destruct m as [m]; simpl; apply map_eq; intros o'.
  destruct (decide (o = o')) as [->|?].
  { rewrite !lookup_fmap, !lookup_alter, lookup_fmap; simpl.
    by destruct (m !! o') as [[]|]. }
  by rewrite lookup_fmap, !lookup_alter_ne, lookup_fmap by done.
Qed.
Lemma mem_erase_freeable_perm m o :
  mem_freeable_perm o (cmap_erase m) ↔ mem_freeable_perm o m.
Proof.
  destruct m as [m]; unfold mem_freeable_perm; simpl. rewrite lookup_omap.
  destruct (m !! o) as [[]|]; naive_solver.
Qed.
Lemma mem_erase_freeable m o : mem_freeable o (cmap_erase m) ↔ mem_freeable o m.
Proof. unfold mem_freeable. by rewrite mem_erase_freeable_perm. Qed.
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
  ✓ Γ → ✓{Γ,Γm} m → m !!{Γ} a = Some v → (Γ,Γm) ⊢ a : Some τ → (Γ,Γm) ⊢ v : τ.
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
Lemma mem_lookup_erase Γ m a :
  (cmap_erase m !!{Γ} a : option (val Ti)) = m !!{Γ} a.
Proof. unfold lookupE, mem_lookup. by rewrite cmap_lookup_erase. Qed.

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
Lemma mem_erase_force Γ m a :
  cmap_erase (mem_force Γ a m) = mem_force Γ a (cmap_erase m).
Proof. apply cmap_erase_alter. Qed.
Lemma mem_lookup_force Γ Γm m a v τ :
  ✓ Γ → ✓{Γ,Γm} m → (Γ,Γm) ⊢ a : Some τ → m !!{Γ} a = Some v → addr_is_obj a →
  mem_force Γ a m !!{Γ} a = Some v.
Proof.
  unfold lookupE, mem_lookup, mem_force. intros.
  destruct (m !!{Γ} a) as [w'|] eqn:?; simplify_equality'.
  by erewrite cmap_lookup_alter by eauto; simplify_option_equality.
Qed.
Lemma mem_lookup_force_disjoint Γ Γm m a1 a2 τ2 v1 :
  ✓ Γ → ✓{Γ,Γm} m → a1 ⊥{Γ} a2 → m !!{Γ} a1 = Some v1 → (Γ,Γm) ⊢ a2 : Some τ2 →
  is_Some (m !!{Γ} a2) → mem_force Γ a2 m !!{Γ} a1 = Some v1.
Proof.
  unfold lookupE, mem_force, mem_lookup. intros ????? [??].
  destruct (m !!{Γ} a1) as [w1|] eqn:?,
    (m !!{Γ} a2) as [w2|] eqn:?; simplify_equality'.
  by erewrite cmap_lookup_alter_disjoint by eauto.
Qed.
Lemma mem_force_commute Γ Γm m a1 a2 τ1 τ2 :
  ✓ Γ → ✓{Γ,Γm} m → a1 ⊥{Γ} a2 →
  (Γ,Γm) ⊢ a1 : Some τ1 → is_Some (m !!{Γ} a1) →
  (Γ,Γm) ⊢ a2 : Some τ2 → is_Some (m !!{Γ} a2) →
  mem_force Γ a1 (mem_force Γ a2 m) = mem_force Γ a2 (mem_force Γ a1 m).
Proof.
  unfold lookupE, mem_lookup, mem_force. intros ???? [??] ? [??].
  destruct (m !!{Γ} a1) as [w1|] eqn:?, (m !!{Γ} a2) as [w2|] eqn:?;
    simplify_equality'; eauto using cmap_alter_commute.
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
Lemma mem_writable_lookup Γ m a : mem_writable Γ a m → ∃ v, m !!{Γ} a = Some v.
Proof.
  unfold lookupE, mem_lookup; intros (w&->&?); simpl; exists (to_val Γ w).
  by rewrite option_guard_True by eauto using pbits_kind_weaken.
Qed.
Lemma mem_lookup_writable Γ m a : m !!{Γ} a = None → ¬mem_writable Γ a m.
Proof. intros ??. destruct (mem_writable_lookup Γ m a); naive_solver. Qed.
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
Hint Resolve of_val_flatten_typed.
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
  ✓ Γ → ✓{Γ,Γm} m → (Γ,Γm) ⊢ a : Some τ → mem_writable Γ a m → (Γ,Γm) ⊢ v : τ →
  '{<[a:=v]{Γ}>m} = '{m}.
Proof.
  unfold insertE, mem_insert, lookupE, mem_lookup. intros ??? (w&?&?) ?.
  eapply cmap_alter_memenv_of; eauto.
  by erewrite of_val_type_of, !type_of_correct by eauto.
Qed.
Lemma mem_insert_forward Γ Γm m a v τ :
  ✓ Γ → ✓{Γ,Γm} m → (Γ,Γm) ⊢ a : Some τ → mem_writable Γ a m → (Γ,Γm) ⊢ v : τ →
  '{m} ⇒ₘ '{<[a:=v]{Γ}>m}.
Proof. intros. by erewrite mem_insert_memenv_of by eauto. Qed.
Lemma mem_insert_valid Γ Γm m a v τ :
  ✓ Γ → ✓{Γ,Γm} m → (Γ,Γm) ⊢ a : Some τ → mem_writable Γ a m → (Γ,Γm) ⊢ v : τ →
  ✓{Γ,Γm} (<[a:=v]{Γ}>m).
Proof.
  intros ??? (w&?&?) ?. assert ((Γ,Γm) ⊢ w : τ) by eauto.
  eapply cmap_alter_valid; eauto; simplify_type_equality;
    eauto using of_val_flatten_mapped, ctree_Forall_not, ctree_lookup_Some.
Qed.
Lemma mem_insert_valid' Γ m a v τ :
  ✓ Γ → ✓{Γ} m → (Γ,'{m}) ⊢ a : Some τ → mem_writable Γ a m →
  (Γ,'{m}) ⊢ v : τ → ✓{Γ} (<[a:=v]{Γ}>m).
Proof.
  unfold valid at 2 3, cmap_valid'; intros.
  erewrite mem_insert_memenv_of by eauto; eauto using mem_insert_valid.
Qed.
Lemma mem_erase_insert Γ m a v :
  cmap_erase (<[a:=v]{Γ}>m) = <[a:=v]{Γ}>(cmap_erase m).
Proof. apply cmap_erase_alter. Qed.
(** We need [addr_is_obj a] because writes at padding bytes are ignored *)
Lemma mem_lookup_insert Γ Γm m a v τ :
  ✓ Γ → ✓{Γ,Γm} m → (Γ,Γm) ⊢ a : Some τ → mem_writable Γ a m → addr_is_obj a →
  (Γ,Γm) ⊢ v : τ → <[a:=v]{Γ}>m !!{Γ} a = Some (val_map (freeze true) v).
Proof.
  unfold insertE, lookupE, mem_insert, mem_lookup. intros ??? (w&?&Hw) ??.
  erewrite cmap_lookup_alter by eauto; csimpl.
  assert (ctree_Forall (λ xb, Some Readable ⊆ pbit_kind xb)
    (of_val Γ (tagged_perm <$> ctree_flatten w) v)).
  { erewrite ctree_flatten_of_val by eauto. generalize (val_flatten Γ v).
    induction Hw; intros [|??]; simpl; constructor; auto.
    by transitivity (Some Writable). }
  by erewrite option_guard_True, to_of_val by eauto.
Qed.
Lemma mem_lookup_insert_disjoint Γ Γm m a1 a2 v1 v2 τ2 :
  ✓ Γ → ✓{Γ,Γm} m → a1 ⊥{Γ} a2 → m !!{Γ} a1 = Some v1 →
  (Γ,Γm) ⊢ a2 : Some τ2 → mem_writable Γ a2 m → (Γ,Γm) ⊢ v2 : τ2 →
  <[a2:=v2]{Γ}>m !!{Γ} a1 = Some v1.
Proof.
  unfold insertE, lookupE, mem_insert, mem_lookup. intros ????? (w2&?&Hw2) ?.
  destruct (m !!{Γ} a1) as [w1|] eqn:?; simplify_equality'.
  by erewrite cmap_lookup_alter_disjoint by eauto using of_val_flatten_unshared.
Qed.
Lemma mem_insert_commute Γ Γm m a1 a2 v1 v2 τ1 τ2 :
  ✓ Γ → ✓{Γ,Γm} m → a1 ⊥{Γ} a2 →
  (Γ,Γm) ⊢ a1 : Some τ1 → mem_writable Γ a1 m → (Γ,Γm) ⊢ v1 : τ1 →
  (Γ,Γm) ⊢ a2 : Some τ2 → mem_writable Γ a2 m → (Γ,Γm) ⊢ v2 : τ2 →
  <[a1:=v1]{Γ}>(<[a2:=v2]{Γ}>m) = <[a2:=v2]{Γ}>(<[a1:=v1]{Γ}>m).
Proof. intros ???? (?&?&?) ?? (?&?&?) ?. eapply cmap_alter_commute; eauto. Qed.
Lemma mem_insert_force_commute Γ Γm m a1 a2 v1 τ1 τ2 :
  ✓ Γ → ✓{Γ,Γm} m → a1 ⊥{Γ} a2 →
  (Γ,Γm) ⊢ a1 : Some τ1 → mem_writable Γ a1 m → (Γ,Γm) ⊢ v1 : τ1 →
  (Γ,Γm) ⊢ a2 : Some τ2 → is_Some (m !!{Γ} a2) →
  <[a1:=v1]{Γ}>(mem_force Γ a2 m) = mem_force Γ a2 (<[a1:=v1]{Γ}>m).
Proof.
  unfold lookupE, mem_lookup, mem_force. intros ???? (?&?&?) ?? [??].
  destruct (m !!{Γ} a2) as [w2|] eqn:?; simplify_equality'.
  eapply cmap_alter_commute; eauto.
Qed.
Lemma mem_insert_writable Γ Γm m a1 a2 v2 τ2 :
  ✓ Γ → ✓{Γ,Γm} m → a1 = a2 ∨ a1 ⊥{Γ} a2 →
  (Γ,Γm) ⊢ a2 : Some τ2 → mem_writable Γ a2 m → (Γ,Γm) ⊢ v2 : τ2 →
  mem_writable Γ a1 m → mem_writable Γ a1 (<[a2:=v2]{Γ}>m).
Proof.
  intros ?? Ha ? (w2&?&Hw2) ? (w1&?&Hw1). red. unfold insertE, mem_insert.
  destruct Ha as [<-|?]; [|erewrite cmap_lookup_alter_disjoint
    by eauto using of_val_flatten_unshared; eauto].
  assert (ctree_Forall (λ xb, Some Writable ⊆ pbit_kind xb)
    (of_val Γ (tagged_perm <$> ctree_flatten w2) v2)).
  { erewrite ctree_flatten_of_val by eauto. generalize (val_flatten Γ v2).
    induction Hw2; intros [|??]; simpl; constructor; auto. }
  destruct (decide (addr_is_obj a1)).
  { erewrite cmap_lookup_alter by eauto; eauto. }
  erewrite cmap_lookup_alter_not_obj by eauto using of_val_flatten_unshared.
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

(** ** Properties of the [singleton] memory *)
Lemma mem_singleton_freeze Γ Γm β a malloc x v τ :
  mem_singleton Γ (freeze β a) malloc x v = mem_singleton Γ a malloc x v.
Proof. apply cmap_singleton_freeze. Qed.
Lemma mem_singleton_valid Γ Γm a malloc x v τ :
  ✓ Γ → (Γ,Γm) ⊢ a : Some τ →
  index_alive Γm (addr_index a) → addr_is_obj a → addr_strict Γ a →
  (Γ,Γm) ⊢ v : τ → sep_valid x → ¬sep_unmapped x →
  ✓{Γ,Γm} (mem_singleton Γ a malloc x v).
Proof.
  intros. assert ((Γ,Γm) ⊢ of_val Γ (replicate (bit_size_of Γ τ) x) v : τ).
  { apply of_val_typed; eauto using Forall_replicate, replicate_length. }
  eapply cmap_singleton_valid; simplify_type_equality; eauto.
  eapply ctree_Forall_not, of_val_mapped; eauto using Forall_replicate.
Qed.
Lemma mem_lookup_singleton Γ Γm a malloc x v τ :
  ✓ Γ → (Γ,Γm) ⊢ a : Some τ → addr_is_obj a → addr_strict Γ a →
  (Γ,Γm) ⊢ v : τ → Some Readable ⊆ perm_kind x →
  mem_singleton Γ a malloc x v !!{Γ} a = Some (val_freeze true v).
Proof.
  intros. unfold mem_singleton, lookupE, mem_lookup; simplify_type_equality.
  erewrite cmap_lookup_singleton by eauto; simpl.
  rewrite option_guard_True by (erewrite ctree_flatten_of_val,
    zip_with_replicate_l, Forall_fmap by eauto; by apply Forall_true).
  by erewrite to_of_val by eauto.
Qed.
Lemma mem_writable_singleton Γ Γm a malloc x v τ :
  ✓ Γ → (Γ,Γm) ⊢ a : Some τ → addr_is_obj a → addr_strict Γ a →
  (Γ,Γm) ⊢ v : τ → Some Writable ⊆ perm_kind x →
  mem_writable Γ a (mem_singleton Γ a malloc x v).
Proof.
  intros; unfold mem_singleton; simplify_type_equality.
  eexists (of_val _ _ _); split; eauto using cmap_lookup_singleton.
  erewrite ctree_flatten_of_val, zip_with_replicate_l, Forall_fmap by eauto.
  by apply Forall_true.
Qed.
Lemma mem_force_singleton Γ Γm a malloc x v τ :
  ✓ Γ → (Γ,Γm) ⊢ a : Some τ → addr_is_obj a → addr_strict Γ a →
  mem_force Γ a (mem_singleton Γ a malloc x v)
  = mem_singleton Γ a malloc x v.
Proof. by apply (cmap_alter_singleton _ Γm id _ _ _ τ). Qed.
Lemma mem_insert_singleton Γ Γm a malloc x v1 v2 τ :
  ✓ Γ → (Γ,Γm) ⊢ a : Some τ → addr_is_obj a → addr_strict Γ a →
  (Γ,Γm) ⊢ v1 : τ → (Γ,Γm) ⊢ v2 : τ →
  <[a:=v2]{Γ}>(mem_singleton Γ a malloc x v1)
  = mem_singleton Γ a malloc x v2.
Proof.
  unfold insertE, mem_insert, mem_singleton; intros; simplify_type_equality.
  by erewrite cmap_alter_singleton,
    ctree_flatten_of_val, fmap_zip_with_l by eauto.
Qed.

(** ** Locks *)
Lemma elem_of_mem_locks m o i :
  (o,i) ∈ mem_locks m ↔
    match cmap_car m !! o with
    | Some (Obj w β) => pbit_locked <$> ctree_flatten w !! i = Some true
    | _ => False
    end.
Proof.
  destruct m as [m]; unfold elem_of, lockset_elem_of; simpl; rewrite lookup_omap.
  destruct (m !! o) as [[|w β]|]; simplify_equality'; try naive_solver; split.
  { intros (ω&Hω&?); simplify_option_equality.
    by rewrite <-list_lookup_fmap, <-elem_of_of_bools. }
  intros Hi. exists (of_bools (pbit_locked <$> ctree_flatten w)).
  rewrite <-list_lookup_fmap, <-elem_of_of_bools in Hi.
  by rewrite option_guard_True by esolve_elem_of.
Qed.
Lemma mem_locks_valid m : ✓{'{m}} (mem_locks m).
Proof.
  intros o i; rewrite elem_of_mem_locks. unfold typed, index_typed.
  destruct m as [m]; simpl; rewrite lookup_fmap.
  destruct (m !! o) as [[]|]; naive_solver.
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
  apply map_eq; intros i. by rewrite lookup_merge, lookup_empty by done.
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
Lemma mem_erase_unlock m Ω :
  cmap_erase (mem_unlock Ω m) = mem_unlock Ω (cmap_erase m).
Proof.
  destruct m as [m], Ω as [Ω]; f_equal'; apply map_eq; intros o.
  rewrite !lookup_omap, !lookup_merge, lookup_omap by done.
  by destruct (m !! o) as [[]|], (Ω !! o).
Qed.
Lemma elem_of_lock_singleton Γ a o i :
  (o,i) ∈ lock_singleton Γ a ↔
    o = addr_index a ∧ addr_object_offset Γ a ≤ i
    < addr_object_offset Γ a + ptr_bit_size_of Γ (type_of a).
Proof.
  destruct (decide (ptr_bit_size_of Γ (type_of a) = 0)) as [Hsz|].
  { split; [|lia]. unfold lock_singleton.
    destruct (decide _) as [[]|]; [|solve_elem_of].
    rewrite Hsz; simpl; rewrite (right_id_L [] (++)).
    apply elem_of_equiv_empty_L; intros j.
    by rewrite elem_of_of_bools, lookup_replicate; intros []. }
  assert (of_bools (replicate (addr_object_offset Γ a) false
    ++ replicate (ptr_bit_size_of Γ (type_of a)) true) ≠ ∅).
  { rewrite elem_of_equiv_empty_L.
    intros Hx; destruct (Hx (addr_object_offset Γ a)).
    by rewrite elem_of_of_bools,
      lookup_app_r, lookup_replicate_2 by solve_length. }
  unfold lock_singleton; case_decide; [split|done].
  * intros (?&?&Hi); simplify_map_equality'; split; auto.
    rewrite elem_of_of_bools in Hi.
    destruct (decide (i < addr_object_offset Γ a)).
    { by rewrite lookup_app_l, lookup_replicate_2 in Hi by solve_length. }
    rewrite lookup_app_r, lookup_replicate in Hi by solve_length.
    destruct Hi as [_ Hi]; revert Hi; solve_length.
  * intros (->&?&?); eexists; simplify_map_equality'; split; auto.
    by rewrite elem_of_of_bools,
      lookup_app_r, lookup_replicate_2 by solve_length.
Qed.
Lemma elem_of_lock_singleton_typed Γ Γm a τ o i :
  ✓ Γ → (Γ,Γm) ⊢ a : Some τ → (o,i) ∈ lock_singleton Γ a ↔ o = addr_index a ∧
    addr_object_offset Γ a ≤ i < addr_object_offset Γ a + bit_size_of Γ τ.
Proof. intros. rewrite elem_of_lock_singleton; by simplify_type_equality. Qed.
Lemma lock_singleton_valid Γ Γm a τ :
  ✓ Γ → (Γ,Γm) ⊢ a : Some τ → ✓{Γm} (lock_singleton Γ a).
Proof.
  intros ?? o i. rewrite elem_of_lock_singleton_typed by eauto.
  intros (->&?&?); eauto using addr_typed_index.
Qed.
Lemma lock_singleton_disjoint Γ Γm a1 a2 τ1 τ2 :
  ✓ Γ → (Γ,Γm) ⊢ a1 : Some τ1 → addr_strict Γ a1 →
  (Γ,Γm) ⊢ a2 : Some τ2 → addr_strict Γ a2 →
  a1 ⊥{Γ} a2 → lock_singleton Γ a1 ∩ lock_singleton Γ a2 = ∅.
Proof.
  intros. apply equiv_empty_L. intros [o i].
  rewrite elem_of_intersection, !elem_of_lock_singleton_typed by eauto.
  intros [(->&?&?) (?&?&?)].
  destruct (addr_disjoint_object_offset Γ Γm a1 a2 τ1 τ2); try done; lia.
Qed.
Lemma mem_unlock_union_locks Ω1 Ω2 m :
  mem_unlock (Ω1 ∪ Ω2) m = mem_unlock Ω1 (mem_unlock Ω2 m).
Proof.
  destruct m as [m], Ω1 as [Ω1], Ω2 as [Ω2]; f_equal'; apply map_eq; intros o.
  rewrite lookup_merge, !lookup_union_with, !lookup_merge by done.
  destruct (m !! o) as [[|w β]|], (Ω1 !! o) as [ω1|],
    (Ω2 !! o) as [ω2|]; do 2 f_equal'; auto.
  by rewrite (commutative_L (∪)), ctree_flatten_merge, zip_with_length_l_eq,
    (ctree_merge_merge _ _ pbit_unlock_if orb), to_bools_union
    by auto using to_bools_length, pbits_unlock_orb.
Qed.
Lemma mem_locks_alloc Γ o malloc τ m :
  ✓ Γ → ✓{Γ} τ →
  mem_allocable o m → mem_locks (mem_alloc Γ o malloc τ m) = mem_locks m.
Proof.
  intros. apply elem_of_equiv_L; intros [o' i]. rewrite !elem_of_mem_locks.
  unfold mem_allocable in *; destruct m as [m]; simplify_equality'.
  destruct (decide (o = o')); simplify_map_equality; split; try done.
  unfold ctree_new; rewrite ctree_flatten_unflatten by done.
  destruct (decide (type_mask Γ τ !! i = Some true)).
  * rewrite lookup_mask, <-option_fmap_compose, fmap_Some by done.
    intros (xb&Hxb&?); apply lookup_replicate in Hxb; naive_solver.
  * rewrite lookup_mask_notin, fmap_Some by done.
    intros (xb&Hxb&?); apply lookup_replicate in Hxb; naive_solver.
Qed.
Lemma mem_locks_free Γ o m v :
  mem_freeable_perm o m → mem_locks (mem_free o m) = mem_locks m.
Proof.
  intros (w&?&Hperm). apply elem_of_equiv_L; intros [o' i].
  rewrite !elem_of_mem_locks. destruct m as [m]; simplify_equality'.
  destruct (decide (o = o')); simplify_map_equality'; split; try done.
  rewrite fmap_Some; intros ([x b]&?&?); decompose_Forall_hyps.
Qed.
Lemma mem_locks_alter Γ Γm g a m w τ o i :
  ✓Γ → ✓{Γ,Γm} m → (Γ,Γm) ⊢ a : Some τ → m !!{Γ} a = Some w → (Γ,Γm) ⊢ g w : τ →
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
  unfold lookupE, cmap_lookup; intros ? Hm ???.
  case_option_guard; simplify_equality'.
  erewrite addr_object_offset_alt by eauto.
  destruct (cmap_car m !! addr_index a) as [[|w' β]|] eqn:?; simplify_equality'.
  destruct (proj2 Hm (addr_index a) w' β) as (τ'&?&_&?&_); auto.
  assert (Γm ⊢ addr_index a : addr_type_object a)
    by eauto using addr_typed_index; simplify_type_equality.
  destruct (w' !!{Γ} addr_ref Γ a) as [w''|] eqn:?; simplify_equality'.
  assert ((Γ,Γm) ⊢ w'' : addr_type_base a)
    by eauto using ctree_lookup_typed, addr_typed_ref_typed.
  rewrite !elem_of_mem_locks. destruct m as [m]; simplify_equality'.
  destruct (decide (o = addr_index a)); simplify_map_equality';
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
      [|rewrite lookup_app_l by auto; intuition omega].
    erewrite lookup_app_r, ctree_flatten_length, lookup_drop by eauto.
    replace (ref_object_offset Γ (addr_ref Γ a)
      + bit_size_of Γ (addr_type_base a)
      + (i - ref_object_offset Γ (addr_ref Γ a)
         - bit_size_of Γ (addr_type_base a))) with i by lia.
    intuition lia. }
  assert (τ = ucharT) by eauto using addr_not_is_obj_type; subst.
  rewrite bit_size_of_uchar; rewrite bit_size_of_uchar in Hbyte.
  erewrite <-!list_lookup_fmap, !fmap_app, !ctree_alter_byte_perm_flatten,
    <-!list_fmap_compose, !fmap_app by eauto; fold (@pbit_locked Ti).  
  erewrite <-!(ctree_lookup_flatten _ _ w') by eauto.
  rewrite take_mask, drop_mask, !pbits_locked_mask, <-!fmap_app.
  rewrite take_take, Min.min_l, (take_drop_commute _ (bit_size_of _ _)),
    drop_drop, <-!(associative_L (++)), drop_take_drop by lia.
  rewrite !list_lookup_fmap.
  destruct (le_lt_dec (ref_object_offset Γ (addr_ref Γ a) +
      addr_ref_byte Γ a * char_bits) i);
    [rewrite or_r by lia|rewrite lookup_app_l, lookup_take,
       lookup_drop, <-le_plus_minus by solve_length; intuition lia].
  rewrite lookup_app_r, take_length_le by solve_length.
  rewrite Nat.sub_add_distr.
  destruct (le_lt_dec (ref_object_offset Γ (addr_ref Γ a)
    + addr_ref_byte Γ a * char_bits + char_bits) i);
    [|rewrite lookup_app_l by solve_length; intuition omega].
  erewrite lookup_app_r, ctree_flatten_length,
    bit_size_of_uchar, lookup_drop by eauto.
  replace (ref_object_offset Γ (addr_ref Γ a)
    + (char_bits + addr_ref_byte Γ a * char_bits)
    + (i - ref_object_offset Γ (addr_ref Γ a) - addr_ref_byte Γ a * char_bits -
       char_bits)) with i by lia.
  intuition lia.
Qed.
Lemma mem_Readable_locks Γ Γm m a w τ i :
  ✓ Γ → ✓{Γ,Γm} m → m !!{Γ} a = Some w → (Γ,Γm) ⊢ a : Some τ →
  ctree_Forall (λ xb, Some Readable ⊆ pbit_kind xb) w →
  (addr_index a,i) ∈ mem_locks m →
  i < addr_object_offset Γ a ∨ addr_object_offset Γ a + bit_size_of Γ τ ≤ i.
Proof.
  unfold lookupE, cmap_lookup. rewrite elem_of_mem_locks.
  intros ? Hm Hw ???; case_option_guard; simplify_equality'.
  destruct (decide (addr_object_offset Γ a ≤ i
    < addr_object_offset Γ a + bit_size_of Γ τ)) as [Hi|]; [exfalso|lia].
  erewrite addr_object_offset_alt in Hi by eauto.
  destruct (cmap_car m !! _) as [[|w' β]|] eqn:?; simplify_equality'; try done.
  assert (Γm ⊢ addr_index a : addr_type_object a)
    by eauto using addr_typed_index.
  destruct (proj2 Hm (addr_index a) w' β)
    as (?&?&_&?&_); auto; simplify_type_equality'.
  destruct (w' !!{Γ} addr_ref Γ a) as [w''|] eqn:Hw''; simplify_equality'.
  assert ((Γ,Γm) ⊢ w'' : addr_type_base a)
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
    destruct (ctree_flatten w !! _) as [xb|] eqn:?; decompose_Forall_hyps.
    by rewrite pbit_Readable_locked in Hperm by done.
  * assert (τ = ucharT) by eauto using addr_not_is_obj_type; subst.
    rewrite bit_size_of_uchar in Hi.
    assert (pbit_locked <$> ctree_flatten w
      !! (i - ref_object_offset Γ (addr_ref Γ a)
            - addr_ref_byte Γ a * char_bits) = Some true) as Hperm'.
    { erewrite <-ctree_lookup_byte_flatten by eauto.
      by rewrite lookup_take, lookup_drop, <-le_plus_minus by solve_length. }
    destruct (ctree_flatten w !! _) as [xb|] eqn:?; decompose_Forall_hyps.
    by rewrite pbit_Readable_locked in Hperm' by done.
Qed.
Lemma mem_lookup_locks Γ Γm m a v τ :
  ✓ Γ → ✓{Γ,Γm} m → m !!{Γ} a = Some v → (Γ,Γm) ⊢ a : Some τ →
  mem_locks m ∩ lock_singleton Γ a = ∅.
Proof.
  unfold lookupE, mem_lookup;
    rewrite bind_Some; intros ?? (w&?&?) ?; simplify_option_equality.
  apply elem_of_equiv_empty_L; intros [o i].
  rewrite not_elem_of_intersection,
    elem_of_lock_singleton; simplify_type_equality'.
  destruct (decide ((o,i) ∈ mem_locks m)); [right; intros (->&?&?)|tauto].
  destruct (mem_Readable_locks Γ Γm m a w τ i); auto with lia.
Qed.
Lemma mem_locks_force Γ Γm a m v τ :
  ✓ Γ → ✓{Γ,Γm} m → (Γ,Γm) ⊢ a : Some τ →
  m !!{Γ} a = Some v → mem_locks (mem_force Γ a m) = mem_locks m.
Proof.
  unfold lookupE, mem_lookup, mem_force;
    rewrite bind_Some; intros ??? (w&?&?); simplify_option_equality.
  apply elem_of_equiv_L; intros [o i]; erewrite mem_locks_alter by eauto.
  destruct (decide (o = addr_index a)) as [->|]; [|tauto].
  destruct (decide (addr_object_offset Γ a ≤ i
    < addr_object_offset Γ a + bit_size_of Γ τ));
    [|destruct (decide (i < addr_object_offset Γ a)); intuition omega].
  rewrite pbits_Readable_locked by auto.
  assert ((addr_index a,i) ∈ mem_locks m →
    i < addr_object_offset Γ a ∨ addr_object_offset Γ a + bit_size_of Γ τ ≤ i)
    by eauto using mem_Readable_locks; intuition congruence.
Qed.
Lemma mem_locks_insert Γ Γm a m v τ :
  ✓ Γ → ✓{Γ,Γm} m → (Γ,Γm) ⊢ a : Some τ → mem_writable Γ a m → (Γ,Γm) ⊢ v : τ →
  mem_locks (<[a:=v]{Γ}>m) = mem_locks m.
Proof.
  unfold insertE, mem_insert; intros ??? (w&?&Hw) ?.
  apply elem_of_equiv_L; intros [o i]; erewrite mem_locks_alter by eauto.
  destruct (decide (o = addr_index a)) as [->|]; [|tauto].
  destruct (decide (addr_object_offset Γ a ≤ i
    < addr_object_offset Γ a + bit_size_of Γ τ));
    [|destruct (decide (i < addr_object_offset Γ a)); intuition omega].
  assert (ctree_Forall (λ xb, Some Readable ⊆ pbit_kind xb)
    (of_val Γ (tagged_perm <$> ctree_flatten w) v)).
  { erewrite ctree_flatten_of_val by eauto. generalize (val_flatten Γ v).
    induction Hw; intros [|??]; simpl; constructor; auto.
    by transitivity (Some Writable). }
  rewrite pbits_Readable_locked by auto.
  assert ((addr_index a,i) ∈ mem_locks m →
    i < addr_object_offset Γ a ∨ addr_object_offset Γ a + bit_size_of Γ τ ≤ i)
    by eauto using mem_Readable_locks, pbits_kind_weaken; intuition congruence.
Qed.
Lemma mem_locks_lock Γ Γm a m τ :
  ✓ Γ → ✓{Γ,Γm} m → (Γ,Γm) ⊢ a : Some τ → mem_writable Γ a m →
  mem_locks (mem_lock Γ a m) = mem_locks m ∪ lock_singleton Γ a.
Proof.
  unfold mem_lock; intros ??? (w&?&?).
  assert ((Γ,Γm) ⊢ ctree_map pbit_lock w : τ).
  { eapply ctree_map_typed; eauto using cmap_lookup_Some, pbits_lock_valid,
      pbit_lock_indetified, ctree_flatten_valid, pbit_lock_mapped. }
  apply elem_of_equiv_L; intros [o i]; erewrite mem_locks_alter by eauto.
  rewrite elem_of_union, elem_of_lock_singleton; simplify_type_equality'.
  destruct (decide (o = addr_index a)) as [->|]; [|tauto].
  destruct (decide (addr_object_offset Γ a ≤ i
    < addr_object_offset Γ a + bit_size_of Γ τ));
    [|destruct (decide (i < addr_object_offset Γ a)); intuition omega].
  rewrite ctree_flatten_map, list_lookup_fmap, <-option_fmap_compose.
  destruct (lookup_lt_is_Some_2 (ctree_flatten w) (i - addr_object_offset Γ a))
    as [[x b] Hxb]; auto; rewrite Hxb; decompose_Forall_hyps.
  rewrite perm_locked_lock by done. intuition congruence.
Qed.
Lemma mem_locks_subseteq_inv Ω m o :
  Ω ⊆ mem_locks m →
  match `Ω !! o, cmap_car m !! o with
  | Some ω, Some (Obj w _) =>
     to_bools (length (ctree_flatten w)) ω
     =.>* pbit_locked <$> ctree_flatten w
  | Some ω, None => False
  | _, _ => True
  end.
Proof.
  destruct m as [m], Ω as [Ω HΩ]; intros HΩm; simpl.
  destruct (m !! o) as [[|w β]|] eqn:?, (Ω !! o) as [ω|] eqn:?; try done.
  * apply Forall2_lookup_2.
    { rewrite fmap_length; auto using to_bools_length. }
    intros i [] []; try done.
    destruct (decide (i < length (ctree_flatten w)));
      [|by rewrite lookup_to_bools_ge by lia].
    rewrite lookup_to_bools_true by done; intros.
    destruct (HΩm (o,i)) as (ω'&?&Hω'); [by exists ω|].
    simplify_map_equality'; simplify_option_equality.
    rewrite elem_of_of_bools in Hω'; congruence.
  * destruct (collection_choose_L ω) as [i ?].
    { by apply (bool_decide_unpack _ HΩ o). }
    destruct (HΩm (o,i)) as (ω'&?&?); [by exists ω|]; simplify_map_equality'.
Qed.
Lemma mem_locks_unlock Ω m :
  Ω ⊆ mem_locks m → mem_locks (mem_unlock Ω m) = mem_locks m ∖ Ω.
Proof.
  intros HΩm. apply elem_of_equiv_L; intros [o i].
  apply (mem_locks_subseteq_inv _ _ o) in HΩm; simpl in *.
  rewrite elem_of_difference, !elem_of_mem_locks.
  destruct m as [m], Ω as [Ω HΩ]; unfold elem_of, lockset_elem_of;
    simplify_equality'; rewrite lookup_merge by done.
  destruct (m !! o) as [[|w β]|] eqn:?,
    (Ω !! o) as [ω|] eqn:?; split; try naive_solver.
  * rewrite ctree_flatten_merge, lookup_zip_with; intros Hw.
    destruct (ctree_flatten w !! i) as [xb|] eqn:Hxb; simplify_equality'.
    destruct (to_bools (length (ctree_flatten w)) ω !! i)
      as [α|] eqn:Hα; simplify_equality'.
    assert (∃ α', pbit_locked <$> ctree_flatten w !! i = Some α' ∧ α =.> α')
      as (α'&?&?) by (rewrite <-list_lookup_fmap; decompose_Forall_hyps; eauto).
    destruct α; simplify_option_equality.
    { by rewrite perm_locked_unlock in Hw. }
    rewrite lookup_to_bools_false in Hα by eauto using lookup_lt_Some.
    split; [simplify_option_equality; congruence|naive_solver].
  * intros [??]; simplify_equality'.
    destruct (ctree_flatten w !! i) as [xbs|] eqn:Hxbs; simplify_equality'.
    rewrite ctree_flatten_merge, lookup_zip_with, Hxbs; simpl.
    assert (to_bools (length (ctree_flatten w)) ω !! i = Some false).
    { apply lookup_to_bools_false; naive_solver eauto using lookup_lt_Some. }
    assert (∃ x, pbit_locked <$> ctree_flatten w !! i = Some x) as [x Hx].
    { rewrite <-list_lookup_fmap; decompose_Forall_hyps; eauto. }
    simplify_option_equality; congruence.
Qed.
Lemma mem_locks_unlock_all m : mem_locks (mem_unlock_all m) = ∅.
Proof. rewrite mem_locks_unlock by done. solve_elem_of. Qed.
Lemma mem_locks_singleton_empty Γ Γm a malloc x v τ :
  ✓ Γ → (Γ,Γm) ⊢ a : Some τ → addr_strict Γ a → (Γ,Γm) ⊢ v : τ →
  perm_locked x = false → mem_locks (mem_singleton Γ a malloc x v) = ∅.
Proof.
  intros. apply elem_of_equiv_empty_L; intros [o i].
  rewrite elem_of_mem_locks; simplify_type_equality'.
  destruct (decide (o = addr_index a)); simplify_map_equality; [|tauto].
  erewrite ctree_singleton_flatten
    by eauto using addr_typed_ref_typed, addr_typed_type_object_valid.
  erewrite ctree_flatten_of_val, zip_with_replicate_l, <-list_lookup_fmap,
    !fmap_app, !fmap_replicate, <-list_fmap_compose by eauto; simpl.
  rewrite !lookup_app_Some, !lookup_replicate, list_lookup_fmap, fmap_Some.
  intros [[??]|[_ [(?&?&?)|(?&?&?)]]]; simplify_equality'; congruence.
Qed.
Lemma mem_locks_singleton Γ Γm a malloc x v τ :
  ✓ Γ → (Γ,Γm) ⊢ a : Some τ → addr_strict Γ a → addr_is_obj a →
  (Γ,Γm) ⊢ v : τ → perm_locked x = true →
  mem_locks (mem_singleton Γ a malloc x v) = lock_singleton Γ a.
Proof.
  intros. apply elem_of_equiv_L; intros [o i].
  rewrite elem_of_lock_singleton, elem_of_mem_locks; simplify_type_equality'.
  destruct (decide (o = addr_index a)); simplify_map_equality; [|tauto].
  erewrite ctree_singleton_flatten
    by eauto using addr_typed_ref_typed, addr_typed_type_object_valid.
  erewrite ctree_flatten_of_val, zip_with_replicate_l, <-list_lookup_fmap,
    !fmap_app, !fmap_replicate, <-list_fmap_compose by eauto; simpl.
  erewrite addr_object_offset_alt, addr_is_obj_ref_byte,
    Nat.mul_0_l, Nat.add_0_r by eauto.
  erewrite !lookup_app_Some, !lookup_replicate, replicate_length,
    fmap_length, val_flatten_length, list_lookup_fmap, fmap_Some by eauto.
  split.
  * intros [[??]|[? [(?&Hi&_)|(?&?&?)]]]; simplify_equality'.
    apply lookup_lt_Some in Hi;
      erewrite val_flatten_length in Hi by eauto; auto with lia.
  * intros (_&?&?). right; split; [done|left].
    destruct (lookup_lt_is_Some_2 (val_flatten Γ v)
      (i - ref_object_offset Γ (addr_ref Γ a))) as [? ->]; eauto.
Qed.
Lemma mem_lock_singleton Γ Γm a malloc x v τ :
  ✓ Γ → (Γ,Γm) ⊢ a : Some τ → addr_is_obj a → addr_strict Γ a →
  mem_lock Γ a (mem_singleton Γ a malloc x v)
  = mem_singleton Γ a malloc (perm_lock x) v.
Proof.
  intros; unfold mem_lock, mem_singleton.
  erewrite cmap_alter_singleton by eauto; f_equal.
  by rewrite (ctree_map_of_val _ _ perm_lock), fmap_replicate by done.
Qed.
Lemma mem_unlock_singleton Γ Γm a malloc x v τ :
  ✓ Γ → (Γ,Γm) ⊢ a : Some τ → addr_strict Γ a → addr_is_obj a →
  (Γ,Γm) ⊢ v : τ → sep_valid x → perm_locked x = true →
  mem_unlock (lock_singleton Γ a) (mem_singleton Γ a malloc x v)
  = mem_singleton Γ a malloc (perm_unlock x) v.
Proof.
  intros; unfold mem_unlock, mem_singleton, cmap_singleton, lock_singleton.
  destruct (decide _) as [|[]]; simplify_type_equality'; f_equal'.
  * assert ((Γ,Γm) ⊢ of_val Γ (replicate (bit_size_of Γ τ) x) v : τ).
    { apply of_val_typed;
        eauto using Forall_replicate, replicate_length, perm_locked_mapped. }
    assert (¬ctree_unmapped (of_val Γ (replicate (bit_size_of Γ τ) x) v)).
    { eapply ctree_Forall_not, of_val_mapped;
        eauto using Forall_replicate, perm_locked_mapped. }
    assert (ref_object_offset Γ (addr_ref Γ a) +
      bit_size_of Γ (addr_type_base a) ≤ bit_size_of Γ (addr_type_object a)).
    { eauto using ref_object_offset_size', addr_typed_ref_typed. }
    assert (τ = addr_type_base a) by eauto using addr_is_obj_type; subst.
    erewrite merge_singleton by done.
    erewrite ctree_flatten_length, to_of_bools
      by eauto using ctree_singleton_typed, addr_typed_ref_typed.
    erewrite ctree_merge_singleton, addr_object_offset_alt, addr_is_obj_ref_byte,
      ?resize_ge, <-?(associative_L (++)), ?drop_app_alt, ?take_app_alt
      by eauto using addr_typed_ref_typed, pbit_unlock_if_empty.
    erewrite (ctree_merge_map _ pbit_unlock) by (rewrite
      ?zip_with_replicate_r by auto; eauto using pbit_unlock_if_empty).
    by erewrite (ctree_map_of_val _ _ perm_unlock), fmap_replicate by auto.
  * rewrite elem_of_equiv_empty_L;
      intros Htrue; apply (Htrue (addr_object_offset Γ a)).
    rewrite elem_of_of_bools, lookup_app_r,
      replicate_length, Nat.sub_diag, lookup_replicate by auto.
    eauto using bit_size_of_pos, addr_typed_type_valid.
Qed.
Lemma mem_unlock_all_singleton Γ Γm m a malloc x v τ :
  ✓ Γ → (Γ,Γm) ⊢ a : Some τ → addr_strict Γ a → addr_is_obj a →
  (Γ,Γm) ⊢ v : τ → sep_valid x → perm_locked x = true →
  mem_unlock_all (mem_singleton Γ a malloc x v)
  = mem_singleton Γ a malloc (perm_unlock x) v.
Proof.
  intros. erewrite mem_locks_singleton by eauto.
  eauto using mem_unlock_singleton.
Qed.
End memory.
