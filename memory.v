(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Import fin_maps mapset.
Require Export values.
Local Open Scope ctype_scope.

(** * Definition of the memory *)
(** We pack the memory into a record so as to avoid ambiguity with already
existing type class instances for finite maps. *)
Inductive obj (Ti : Set) :=
  | Freed : type Ti → obj Ti
  | Obj : mval Ti → obj Ti.
Arguments Freed {_} _.
Arguments Obj {_} _.

Definition maybe_Obj {Ti} (o : obj Ti) : option (mval Ti) :=
  match o with Obj w => Some w | _ => None end.
Definition obj_map {Ti} (f : mval Ti → mval Ti) (o : obj Ti) : obj Ti :=
  match o with Obj w => Obj (f w) | Freed τ => Freed τ end.

Section object_operations.
  Context `{IntEnv Ti} `{PtrEnv Ti} `{TypeOfIndex Ti M}.

  Inductive obj_typed' (m : M) : obj Ti → type Ti → Prop :=
    | Freed_typed τ : type_valid get_env τ → obj_typed' m (Freed τ) τ
    | Obj_typed w τ : m ⊢ w : τ → obj_typed' m (Obj w) τ.
  Global Instance obj_typed:
    Typed M (type Ti) (obj Ti) := obj_typed'.

  Global Instance type_of_obj: TypeOf (type Ti) (obj Ti) := λ o,
    match o with Obj w => type_of w | Freed τ => τ end.
  Global Instance obj_type_check: TypeCheck M (type Ti) (obj Ti) := λ  m o,
    match o with
    | Obj w => type_check m w
    | Freed τ => guard (type_valid get_env τ); Some τ
    end.
  Inductive obj_le' (m : M) : relation (obj Ti) :=
    | Freed_le τ : obj_le' m (Freed τ) (Freed τ)
    | Obj_le w1 w2 : w1 ⊑@{m} w2 → obj_le' m (Obj w1) (Obj w2).
  Global Instance obj_le: SubsetEqEnv M (obj Ti) := obj_le'.
End object_operations.

Record mem (Ti : Set) := Mem { MMap : indexmap (obj Ti) }.
Add Printing Constructor mem.
Arguments Mem {_} _.
Arguments MMap {_} _.

Section objects.
Context `{MemorySpec Ti M}.
Implicit Types o : obj Ti.
Implicit Types m : M.
Implicit Types τ : type Ti.

Lemma obj_typed_type_valid m v τ : m ⊢ v : τ → type_valid get_env τ.
Proof. destruct 1; try econstructor; eauto using mtyped_type_valid. Qed.

Global Instance: TypeOfSpec M (type Ti) (obj Ti).
Proof. destruct 1; simpl; auto. eapply type_of_correct; eauto. Qed.
Global Instance: TypeCheckSpec M (type Ti) (obj Ti).
Proof.
  intros m v τ. split.
  * destruct v; intros; simplify_option_equality;
      constructor; eauto. eapply type_check_sound; eauto.
  * by destruct 1; simplify_option_equality;
      erewrite ?type_check_complete by eauto.
Qed.
Lemma obj_typed_weaken_mem m1 m2 o τ :
  (∀ x σ, type_of_index m1 x = Some σ → type_of_index m2 x = Some σ) →
  m1 ⊢ o : τ → m2 ⊢ o : τ.
Proof. destruct 2; econstructor; eauto using mtyped_weaken_mem. Qed.
Lemma obj_map_typed f m o τ :
  (∀ w, m ⊢ w : τ → m ⊢ f w : τ) → m ⊢ o : τ → m ⊢ obj_map f o : τ.
Proof. destruct 2; simpl; constructor; auto. Qed.

Lemma obj_le_type_of m o1 o2 : o1 ⊑@{m} o2 → type_of o1 = type_of o2.
Proof. destruct 1; simpl; eauto using mval_le_type_of. Qed.
Lemma obj_typed_ge m o1 o2 τ : m ⊢ o1 : τ → o1 ⊑@{m} o2 → m ⊢ o2 : τ.
Proof. destruct 1; inversion 1; subst; constructor; eauto using mtyped_ge. Qed.
Lemma obj_typed_le m o1 o2 τ : m ⊢ o1 : τ → o2 ⊑@{m} o1 → m ⊢ o2 : τ.
Proof. destruct 1; inversion 1; subst; constructor; eauto using mtyped_le. Qed.
Lemma obj_le_weaken_mem m1 m2 o1 o2 :
  (∀ x σ, type_of_index m1 x = Some σ → type_of_index m2 x = Some σ) →
  o1 ⊑@{m1} o2 → o1 ⊑@{m2} o2.
Proof. destruct 2; econstructor; eauto using mval_le_weaken_mem. Qed.
Global Instance: PartialOrder (@subseteq_env M (obj Ti) _ m).
Proof.
  intros m. repeat split.
  * by intros [?|?]; constructor.
  * destruct 1; inversion 1; subst; constructor; etransitivity; eauto.
  * destruct 1; inversion 1; subst; f_equal. by apply (anti_symmetric (⊑@{m})).
Qed.
End objects.

Section memory_operations.
  Context `{IntEnv Ti} `{PtrEnv Ti}.

  Global Instance mem_type_of_index: TypeOfIndex Ti (mem Ti) := λ m x,
    type_of <$> MMap m !! x.
  Global Instance mem_index_alive: IndexAlive (mem Ti) := λ m x,
    ∃ w, MMap m !! x = Some (Obj w).

  Global Instance mem_empty: Empty (mem Ti) := Mem ∅.
  Global Instance mem_lookup: Lookup (addr Ti) (val Ti) (mem Ti) := λ a m,
    o ← MMap m !! addr_index a;
    w ← maybe_Obj o;
    w' ← w !! addr_ref a;
    guard (addr_byte a < addr_byte_size a);
    guard (type_of a ≠ void);
    if decide (addr_is_obj a) then Some (mval_to_val w')
    else w' !! addr_ref_byte a.

  Definition mem_force (a : addr Ti) (m : mem Ti) : mem Ti :=
    match m with
    | Mem m => Mem $ alter (obj_map (alter id (addr_ref a))) (addr_index a) m
    end.
  Global Instance mem_insert: Insert (addr Ti) (val Ti) (mem Ti) := λ a v m,
    let f w :=
      if decide (addr_is_obj a) then mval_of_val v else <[addr_ref_byte a:=v]>w
    in match m with
    | Mem m => Mem $ alter (obj_map (alter f (addr_ref a))) (addr_index a) m
    end.
  Fixpoint mem_insert_array (a : addr Ti) (vs : list (val Ti))
      (m : mem Ti) : mem Ti :=
    match vs with
    | [] => m
    | v :: vs => <[a:=v]>(mem_insert_array (addr_plus 1 a) vs m)
    end.

  Definition is_free (x : index) (m : mem Ti) := MMap m !! x = None.
  Definition mem_alloc (x : index) (τ : type Ti) (m : mem Ti) : mem Ti :=
    Mem $ <[x:=Obj (mval_new τ)]>(MMap m).

  Global Instance mem_delete: Delete index (mem Ti) := λ x m,
    match m with Mem m => Mem $ alter (λ o, Freed (type_of o)) x m end.

  Global Instance mem_valid: Valid () (mem Ti) := λ _ m, map_forall
    (λ _ o, ∃ τ, m ⊢ o : τ ∧ int_typed (size_of τ) sptr)
    (MMap m).
  Global Instance mem_subseteq: SubsetEq (mem Ti) := λ m1 m2, ∀ x o1,
    MMap m1 !! x = Some o1 → ∃ o2, MMap m2 !! x = Some o2 ∧ o1 ⊑@{m2} o2.
End memory_operations.

Section memory.
Context `{EnvSpec Ti}.
Implicit Types τ : type Ti.
Implicit Types a : addr Ti.
Implicit Types p : ptr Ti.
Implicit Types w : mval Ti.
Implicit Types v : val Ti.
Implicit Types o : obj Ti.
Implicit Types m : mem Ti.

Global Instance mem_index_alive_dec m i : Decision (index_alive m i).
Proof.
 refine
  match MMap m !! i as mo return Decision (∃ w, mo = Some (Obj w)) with
  | Some (Obj w) => left (ex_intro _ w eq_refl)
  | _ => right _
  end; by intros [??].
Defined.

Global Instance: MemorySpec Ti (mem Ti).
Proof.
  split; try apply _.
  * constructor. apply ∅.
  * unfold type_of_index, mem_type_of_index. intros m x τ Hm Hτ.
    destruct (MMap m !! x) as [o|] eqn:Ho; simplify_equality.
    destruct (Hm x o) as (τ&?&?); auto.
    erewrite type_of_correct by eauto. eauto using obj_typed_type_valid.
  * unfold type_of_index, mem_type_of_index. intros m x τ Hm Hτ.
    destruct (MMap m !! x) as [o|] eqn:Ho; simplify_equality.
    destruct (Hm x o) as (τ&?&?); auto.
    by erewrite type_of_correct by eauto.
Qed.

Lemma mem_lookup_raw m x o :
  ⊢ valid m → MMap m !! x = Some o →
  ∃ τ, m ⊢ o : τ ∧ type_of_index m x = Some τ ∧ int_typed (size_of τ) sptr.
Proof.
  intros Hm Hx. destruct (Hm x o) as (τ&Ho&?); auto. exists τ.
  unfold type_of_index, mem_type_of_index. rewrite Hx; simpl.
  erewrite type_of_correct by eauto. eauto.
Qed.
Lemma mem_lookup_raw_Obj m x w :
  ⊢ valid m → MMap m !! x = Some (Obj w) →
  ∃ τ, m ⊢ w : τ ∧ type_of_index m x = Some τ ∧ int_typed (size_of τ) sptr.
Proof.
  intros. destruct (mem_lookup_raw m x (Obj w)) as (?&Ho&?&?); eauto.
  inversion Ho; naive_solver.
Qed.
Lemma size_of_type_of_index m x τ :
  ⊢ valid m → type_of_index m x = Some τ → int_typed (size_of τ) sptr.
Proof.
  unfold type_of_index, mem_type_of_index. intros Hm Hx.
  destruct (MMap m !! x) as [o|] eqn:?; simplify_equality'.
  destruct (Hm x o) as (?&?&?); auto. by erewrite type_of_correct by eauto.
Qed.

Lemma type_of_index_alloc m x τ :
  type_valid get_env τ → type_of_index (mem_alloc x τ m) x = Some τ.
Proof.
  intros. unfold type_of_index, mem_type_of_index; simpl.
  (* hack: why will it unfold mval_new too eagerly at Qed? *)
  remember (mval_new τ) as w. rewrite lookup_insert; simpl; f_equal.
  by apply type_of_correct with m; subst; apply mval_new_typed.
Qed.
Lemma type_of_index_alloc_ne m x τ y σ :
  is_free x m →
  type_of_index m y = Some σ → type_of_index (mem_alloc x τ m) y = Some σ.
Proof.
  unfold type_of_index, mem_type_of_index, is_free; simpl.
  intros. destruct (decide (x = y)); simplify_option_equality.
  rewrite lookup_insert_ne by done. by simplify_option_equality.
Qed.

Lemma addr_typed_alloc m x τ a σ :
  is_free x m → m ⊢ a : σ → mem_alloc x τ m ⊢ a : σ.
Proof. eauto using addr_typed_weaken_mem, type_of_index_alloc_ne. Qed.
Lemma addr_new_typed_alloc m x τ a :
  type_valid get_env τ → mem_alloc x τ m ⊢ addr_new x τ : τ.
Proof.
  intros. apply Addr_typed with τ; try done.
  * by apply type_of_index_alloc.
  * constructor.
  * lia.
  * by apply Nat.mod_0_l, size_of_ne_0.
Qed.
Lemma ptr_typed_alloc m x τ p σ :
  is_free x m → m ⊢ p : σ → mem_alloc x τ m ⊢ p : σ.
Proof. eauto using ptr_typed_weaken_mem, type_of_index_alloc_ne. Qed.
Lemma vtyped_alloc m x τ v σ :
  is_free x m → m ⊢ v : σ → mem_alloc x τ m ⊢ v : σ.
Proof. eauto using vtyped_weaken_mem, type_of_index_alloc_ne. Qed.
Lemma mtyped_alloc m x τ w σ :
  is_free x m → m ⊢ w : σ → mem_alloc x τ m ⊢ w : σ.
Proof. eauto using mtyped_weaken_mem, type_of_index_alloc_ne. Qed.
Lemma obj_typed_alloc m x τ o σ :
  is_free x m → m ⊢ o : σ → mem_alloc x τ m ⊢ o : σ.
Proof. eauto using obj_typed_weaken_mem, type_of_index_alloc_ne. Qed.

Lemma type_of_index_delete m x y σ :
  type_of_index m y = Some σ → type_of_index (delete x m) y = Some σ.
Proof.
  destruct m as [m].
  unfold type_of_index, mem_type_of_index, delete, mem_delete; simpl.
  intros. destruct (decide (x = y)); simplify_equality.
  * rewrite lookup_alter. by simplify_option_equality.
  * by rewrite lookup_alter_ne.
Qed.
Lemma addr_typed_delete m x a σ : m ⊢ a : σ → delete x m ⊢ a : σ.
Proof. eauto using addr_typed_weaken_mem, type_of_index_delete. Qed.
Lemma ptr_typed_delete m x p σ : m ⊢ p : σ → delete x m ⊢ p : σ.
Proof. eauto using ptr_typed_weaken_mem, type_of_index_delete. Qed.
Lemma vtyped_delete m x v σ : m ⊢ v : σ → delete x m ⊢ v : σ.
Proof. eauto using vtyped_weaken_mem, type_of_index_delete. Qed.
Lemma mtyped_delete m x w σ : m ⊢ w : σ → delete x m ⊢ w : σ.
Proof. eauto using mtyped_weaken_mem, type_of_index_delete. Qed.
Lemma obj_typed_delete m x o σ : m ⊢ o : σ → delete x m ⊢ o : σ.
Proof. eauto using obj_typed_weaken_mem, type_of_index_delete. Qed.

Lemma mem_lookup_Some m a v :
  ⊢ valid m → m !! a = Some v → ∃ w τ w' τ',
    MMap m !! addr_index a = Some (Obj w) ∧
    type_of_index m (addr_index a) = Some τ ∧
    m ⊢ w : τ ∧ addr_ref a @ τ ↣ τ' ∧
    w !! addr_ref a = Some w' ∧ m ⊢ w' : τ' ∧
    addr_byte a < addr_byte_size a ∧ type_of a ≠ void ∧
    (addr_is_obj a → v = mval_to_val w') ∧
    (¬addr_is_obj a → w' !! addr_ref_byte a = Some v).
Proof.
  intros Hm Hav. unfold lookup, mem_lookup in Hav.
  destruct (MMap m !! addr_index a) as [o|] eqn:Ho; simplify_equality'.
  destruct o as [|w]; simplify_equality'.
  destruct (w !! addr_ref a) as [w'|] eqn:Hw'; simplify_equality'.
  repeat case_option_guard; simplify_equality.
  destruct (mem_lookup_raw_Obj m (addr_index a) w) as (τ&?&?&?); auto.
  destruct (mval_lookup_Some m w τ (addr_ref a) w') as (τ'&?&?); auto.
  by exists w τ w' τ'; split_ands; auto;
    repeat case_decide; simplify_equality.
Qed.

Lemma mem_empty_valid : ⊢ valid ∅.
Proof. intros x o; simpl. by rewrite lookup_empty. Qed.
Lemma mem_alloc_valid x m τ :
  ⊢ valid m → is_free x m →
  type_valid get_env τ → int_typed (size_of τ) sptr →
  ⊢ valid (mem_alloc x τ m).
Proof.
  intros Hm Hx Hτ Hsz y o; simpl. rewrite lookup_insert_Some.
  intros [[??]|[??]]; subst.
  { exists τ. split; auto. constructor. by apply mval_new_typed. }
  destruct (Hm y o) as (σ&?&?); eauto using obj_typed_alloc.
Qed.
Lemma mem_delete_valid x m : ⊢ valid m → ⊢ valid (delete x m).
Proof.
  destruct m as [m]; intros Hm y o; unfold delete; simpl.
  rewrite lookup_alter_Some. intros [(?&o'&?&?)|[??]]; subst.
  * destruct (Hm y o') as (σ&?&?); auto. exists σ. split; auto.
    erewrite type_of_correct by eauto.
    constructor; eauto using obj_typed_type_valid.
  * destruct (Hm y o) as (σ&?&?); auto. exists σ. split; auto.
    eapply obj_typed_weaken_mem with (Mem m); auto.
    unfold type_of_index, mem_type_of_index; simpl. intros z ??.
    destruct (decide (x = z)); simplify_equality.
    + rewrite lookup_alter. by simplify_option_equality.
    + by rewrite lookup_alter_ne.
Qed.

Lemma mem_lookup_strict m a : is_Some (m !! a) → addr_strict m a.
Proof.
  unfold lookup, mem_lookup, addr_strict, index_alive, mem_index_alive.
  intros [v Hv].
  destruct (MMap m !! addr_index a) as [o|] eqn:Ho; simplify_equality'.
  destruct o; repeat (simplify_option_equality || case_decide);
    eauto with congruence.
Qed.
Lemma mem_lookup_typed m a v σ :
  ⊢ valid m → m !! a = Some v → m ⊢ a : σ → m ⊢ v : σ.
Proof.
  intros Hm Hv Ha. apply mem_lookup_Some in Hv; auto.
  destruct Hv as (w&τ&w'&τ'&?&?&?&?&_&?&?&?&Hobj&Hbyte); simplify_type_equality.
  destruct (decide (addr_is_obj a)).
  * destruct (addr_typed_ref m a σ) as (σ'&?&Href); auto.
    { split. by exists w. by simplify_type_equality. }
    erewrite addr_is_obj_type_base in Href by eauto.
    rewrite Hobj by done. simplify_option_equality; simplify_type_equality.
    by apply mval_to_val_typed.
  * erewrite addr_not_is_obj_type by eauto. eauto using mval_lookup_byte_typed.
Qed.
Lemma mem_lookup_frozen m a v :
  ⊢ valid m → m !! a = Some v → val_forall frozen v.
Proof.
  intros Hm Hv. apply mem_lookup_Some in Hv; auto.
  destruct Hv as (w&τ&w'&τ'&?&?&?&?&?&?&?&?&Hobj&Hbyte).
  destruct (decide (addr_is_obj a)).
  * rewrite Hobj by done. eauto using mval_to_val_frozen.
  * apply (vtyped_int_frozen m _ uchar). eauto using mval_lookup_byte_typed.
Qed.

Lemma type_of_index_force m a τ y σ :
  ⊢ valid m → m ⊢ a : τ →
  type_of_index m y = Some σ → type_of_index (mem_force a m) y = Some σ.
Proof.
  intros Hm Ha Hy. destruct m as [m].
  unfold type_of_index, mem_type_of_index, mem_force in *; simpl in *.
  destruct (decide (addr_index a = y)); simplify_option_equality;
    [|by rewrite lookup_alter_ne; simplify_option_equality].
  rewrite lookup_alter.
  destruct (m !! addr_index a) as [[|w]|] eqn:?; simplify_equality'; auto.
  destruct (addr_typed_ref_base (Mem m) a τ) as (?&?&?); auto.
  destruct (mem_lookup_raw_Obj (Mem m) (addr_index a) w) as (τ'&?&?&_); auto.
  simplify_type_equality; simplify_option_equality.
  f_equal. eapply type_of_correct with (Mem m), mval_alter_typed; eauto.
Qed.
Lemma addr_typed_force m a τ a' σ :
  ⊢ valid m → m ⊢ a : τ → m ⊢ a' : σ → mem_force a m ⊢ a' : σ.
Proof. eauto using addr_typed_weaken_mem, type_of_index_force. Qed.
Lemma ptr_typed_force m a τ p σ :
  ⊢ valid m → m ⊢ a : τ → m ⊢ p : σ → mem_force a m ⊢ p : σ.
Proof. eauto using ptr_typed_weaken_mem, type_of_index_force. Qed.
Lemma vtyped_force m a τ v σ :
  ⊢ valid m → m ⊢ a : τ → m ⊢ v : σ → mem_force a m ⊢ v : σ.
Proof. eauto using vtyped_weaken_mem, type_of_index_force. Qed.
Lemma mtyped_force m a τ w σ :
  ⊢ valid m → m ⊢ a : τ → m ⊢ w : σ → mem_force a m ⊢ w : σ.
Proof. eauto using mtyped_weaken_mem, type_of_index_force. Qed.
Lemma obj_typed_force m a τ o σ :
  ⊢ valid m → m ⊢ a : τ → m ⊢ o : σ → mem_force a m ⊢ o : σ.
Proof. eauto using obj_typed_weaken_mem, type_of_index_force. Qed.
Lemma mem_force_valid m a σ : ⊢ valid m → m ⊢ a : σ → ⊢ valid (mem_force a m).
Proof.
  destruct m as [m]; intros Hm Ha x o Hx; simpl in *.
  rewrite lookup_alter_Some in Hx.
  destruct Hx as [(<-&o'&?&->)|[??]]; simplify_option_equality.
  * destruct (addr_typed_ref_base (Mem m) a σ) as (τ&?&?); auto.
    destruct (mem_lookup_raw (Mem m) (addr_index a) o') as (?&?&?&?); auto.
    simplify_option_equality; simplify_type_equality.
    exists τ; split; auto. apply obj_map_typed.
    + intros. eapply mval_alter_typed; eauto.
    + eapply (obj_typed_force (Mem m)); eauto.
  * destruct (mem_lookup_raw (Mem m) x o) as (τ&?&_&?);
      simplify_type_equality; auto.
    exists τ; split; auto. eapply (obj_typed_force (Mem m)); eauto.
Qed.

Lemma type_of_index_insert m a j v τ y σ :
  ⊢ valid m → m ⊢ a : τ → m ⊢ v : τ →
  type_of_index m y = Some σ →
  type_of_index (<[addr_plus j a:=v]>m) y = Some σ.
Proof.
  intros Hm Haτ Hvτ Hy. destruct m as [m]; unfold type_of_index,
    mem_type_of_index, insert, mem_insert in *; simpl in *.
  rewrite addr_index_plus.
  destruct (decide (addr_index a = y)); simplify_equality;
    [rewrite lookup_alter | by rewrite lookup_alter_ne].
  destruct (addr_typed_ref_base (Mem m) a τ) as (?&Hx&Hr); auto.
  unfold type_of_index, mem_type_of_index in Hx.
  destruct (m !! addr_index a) as [[?|w]|] eqn:Hw; simplify_equality'; auto.
  destruct (Hm (addr_index a) (Obj w)) as (τ'&Hwτ&_); auto.
  inversion Hwτ; simplify_option_equality; simplify_type_equality.
  f_equal; eapply type_of_correct with (Mem m).
  eapply mval_alter_typed; rewrite ?addr_ref_base_plus; eauto.
  intros ??. case_decide as Hobj; rewrite addr_is_obj_plus in Hobj;
    simplify_type_equality.
  * erewrite addr_is_obj_type_base by eauto.
    eauto using mval_of_val_typed.
  * eapply mval_insert_byte_typed; auto.
    by rewrite <-(addr_not_is_obj_type (Mem m) a τ) by
      (rewrite ?addr_is_obj_plus; eauto using vtyped_not_void).
Qed.
Lemma addr_typed_insert m a j v τ a' σ :
  ⊢ valid m → m ⊢ a : τ → m ⊢ v : τ →
  m ⊢ a' : σ → <[addr_plus j a:=v]>m ⊢ a' : σ.
Proof. eauto using addr_typed_weaken_mem, type_of_index_insert. Qed.
Lemma ptr_typed_insert m a j v τ p σ :
  ⊢ valid m → m ⊢ a : τ → m ⊢ v : τ →
  m ⊢ p : σ → <[addr_plus j a:=v]>m ⊢ p : σ.
Proof. eauto using ptr_typed_weaken_mem, type_of_index_insert. Qed.
Lemma vtyped_insert m a j v τ v' σ :
  ⊢ valid m → m ⊢ a : τ → m ⊢ v : τ →
  m ⊢ v' : σ → <[addr_plus j a:=v]>m ⊢ v' : σ.
Proof. eauto using vtyped_weaken_mem, type_of_index_insert. Qed.
Lemma mtyped_insert m a j v τ w σ :
  ⊢ valid m → m ⊢ a : τ → m ⊢ v : τ →
  m ⊢ w : σ → <[addr_plus j a:=v]>m ⊢ w : σ.
Proof. eauto using mtyped_weaken_mem, type_of_index_insert. Qed.
Lemma obj_typed_insert m a j v τ o σ :
  ⊢ valid m → m ⊢ a : τ → m ⊢ v : τ →
  m ⊢ o : σ → <[addr_plus j a:=v]>m ⊢ o : σ.
Proof. eauto using obj_typed_weaken_mem, type_of_index_insert. Qed.
Lemma mem_insert_valid m a j v σ :
  ⊢ valid m → m ⊢ a : σ → m ⊢ v : σ → ⊢ valid (<[addr_plus j a:=v]>m).
Proof.
  destruct m as [m]; intros Hm Ha Hv x o Hx; simpl in *.
  rewrite !addr_index_plus, lookup_alter_Some in Hx.
  destruct Hx as [(<-&o'&?&->)|[??]]; simplify_option_equality.
  * destruct (addr_typed_ref_base (Mem m) a σ) as (τ&?&?); auto.
    destruct (mem_lookup_raw (Mem m) (addr_index a) o') as (?&?&?&?); auto.
    simplify_option_equality; simplify_type_equality.
    exists τ; split; auto. apply obj_map_typed; eauto using obj_typed_insert.
    intros w Hw. eapply mval_alter_typed; rewrite ?addr_ref_base_plus; eauto.
    intros w' Hw'. case_decide as Hobj; simplify_type_equality.
    + rewrite addr_is_obj_plus in Hobj.
      erewrite addr_is_obj_type_base by eauto. apply mval_of_val_typed.
      eauto using vtyped_insert.
    + eapply mval_insert_byte_typed; auto.
      rewrite addr_is_obj_plus in Hobj.
      rewrite <-(addr_not_is_obj_type (Mem m) a σ)
         by eauto using vtyped_not_void; eauto using vtyped_insert.
  * destruct (mem_lookup_raw (Mem m) x o) as (τ&?&_&?);
      simplify_type_equality; eauto using obj_typed_insert.
Qed.

Lemma mem_insert_array_app m a vs1 vs2 :
  mem_insert_array a (vs1 ++ vs2) m = mem_insert_array a vs1 $
    mem_insert_array (addr_plus (length vs1) a) vs2 m.
Proof.
  revert a. induction vs1 as [|v1 vs1 IH]; intros a; simpl.
  { by rewrite addr_plus_0. }
  rewrite Zpos_P_of_succ_nat, IH.
  by rewrite addr_plus_plus, Z.add_1_r by auto with zpos.
Qed.

(* todo, generalize for (j : Z) *)
Lemma type_of_index_insert_array_help m a (j : nat) vs τ y :
  ⊢ valid m → m ⊢ a : τ → m ⊢* vs : τ →
  (∀ σ, type_of_index m y = Some σ →
    type_of_index (mem_insert_array (addr_plus j a) vs m) y = Some σ) ∧
  ⊢ valid (mem_insert_array (addr_plus j a) vs m) ∧
  (∀ a' σ, m ⊢ a' : σ → mem_insert_array (addr_plus j a) vs m ⊢ a' : σ) ∧
  (∀ v σ, m ⊢ v : σ → mem_insert_array (addr_plus j a) vs m ⊢ v : σ).
Proof.
  intros Hm Haτ Hvs. revert j.
  induction Hvs as [|v vs Hv Hvs IH]; simpl; auto.
  intros j; destruct (IH (1 + j)) as (?&?&?&?).
  rewrite !(addr_plus_plus_nat _ 1). naive_solver eauto using
    type_of_index_insert, mem_insert_valid, addr_typed_insert, vtyped_insert.
Qed.
Lemma type_of_index_insert_array m a (j : nat) vs τ y σ :
  ⊢ valid m → m ⊢ a : τ → m ⊢* vs : τ →
  type_of_index m y = Some σ →
  type_of_index (mem_insert_array (addr_plus j a) vs m) y = Some σ.
Proof. intros. eapply type_of_index_insert_array_help; eauto. Qed.

Lemma mem_lookup_insert m a v σ :
  ⊢ valid m → m ⊢ a : σ → is_Some (m !! a) → addr_is_obj a →
  m ⊢ v : σ → <[a:=v]>m !! a = Some (val_map freeze v).
Proof.
  unfold insert, mem_insert, lookup, mem_lookup.
  intros Hm Haσ [v' Hv'] ? Hv; destruct m as [m]; simpl in *.
  rewrite lookup_alter.
  destruct (m !! addr_index a) as [o|] eqn:Hao; simplify_equality'.
  destruct (Hm (addr_index a) o) as (?&Ho&_); auto; simplify_equality'.
  destruct Ho as [|w τ Hw]; simplify_equality'.
  destruct (w !! addr_ref a) as [w'|] eqn:Hw'; simplify_equality'.
  erewrite mval_lookup_alter
    by eauto using mval_lookup_unfreeze; simplify_equality'.
  repeat (case_decide || simplify_option_equality).
  by erewrite mval_to_of_val by eauto.
Qed.
Lemma mem_lookup_insert_disjoint m a1 a2 τ2 v1 v2 :
  ⊢ valid m → a1 ⊥ a2 → m !! a1 = Some v1 →
  m ⊢ a2 : τ2 → m ⊢ v2 : τ2 → <[a2:=v2]>m !! a1 = Some v1.
Proof.
  intros Hm Ha12 Hv1 Ha2 Hv2. apply mem_lookup_Some in Hv1; auto.
  destruct Hv1 as (w1&τ1&w1'&τ1'&?&?&?&?&?&?&?&?&?&?).
  unfold lookup, insert, mem_lookup, mem_insert. destruct m as [m]; simpl.
  destruct Ha12 as [?|[[Hidx ?]|(Hidx&Ha&?&?&?)]].
  * rewrite lookup_alter_ne by done. simplify_option_equality.
    case_decide; eauto using f_equal, eq_sym.
  * destruct Hidx. rewrite lookup_alter. simplify_option_equality.
    erewrite mval_lookup_alter_disjoint by (by eauto); simpl.
    repeat (done || case_decide || case_option_guard);
      eauto using f_equal, eq_sym.
  * destruct Hidx. rewrite lookup_alter. simplify_option_equality.
    assert (w1 !! (unfreeze <$> addr_ref a2) = Some w1').
    { rewrite <-ref_unfreeze_freeze, <-Ha, ref_unfreeze_freeze.
      eauto using mval_lookup_unfreeze. }
    erewrite (mval_lookup_freeze (alter _ _ w1))
      by (rewrite Ha; eauto using mval_lookup_alter_freeze).
    simpl; repeat (done || case_decide || case_option_guard).
    eapply mval_lookup_insert_byte; eauto.
    by erewrite <-(addr_not_is_obj_type _ _ τ2)
      by eauto using vtyped_not_void.
Qed.
Lemma mem_insert_commute m a1 a2 τ1 τ2 v1 v2 :
  ⊢ valid m → a1 ⊥ a2 → m ⊢ a1 : τ1 → m ⊢ a2 : τ2 →
  m ⊢ v1 : τ1 → m ⊢ v2 : τ2 →
  <[a1:=v1]>(<[a2:=v2]>m) = <[a2:=v2]>(<[a1:=v1]>m).
Proof.
  unfold insert, mem_insert. destruct m as [m]; simpl.
  intros Hm [?|[[<- ?]|(<-&Ha&?&?&?)]] Ha1 Ha2 Hv1 Hv2; f_equal.
  * by rewrite alter_commute.
  * rewrite <-!alter_compose. apply alter_ext. intros [|w]; simpl; auto.
    f_equal. by rewrite <-mval_alter_commute.
  * rewrite <-!alter_compose. apply alter_ext. intros [|w] Hw; simpl; auto.
    destruct (mem_lookup_raw_Obj (Mem m) (addr_index a1) w) as (τ&?&?&_); auto.
    feed pose proof (addr_not_is_obj_type (Mem m) a1 τ1);
      eauto using vtyped_not_void; subst.
    feed pose proof (addr_not_is_obj_type (Mem m) a2 τ2);
      eauto using vtyped_not_void; subst.
    f_equal. rewrite <-!(mval_alter_freeze _ (addr_ref a1)),
      <-!(mval_alter_freeze _ (addr_ref a2)), <-!Ha.
    rewrite !mval_alter_freeze, <-!mval_alter_compose.
    destruct (addr_typed_ref_base (Mem m) a1 uchar) as (σ&?&?); auto.
    simplify_option_equality.
    apply (mval_alter_ext_typed (Mem m) _ _ _ τ _ _ (addr_type_base a1)); auto.
    intros w' Hw'; simpl.
    by repeat case_decide; eauto using mval_insert_byte_commute.
Qed.

Lemma mem_alloc_lookup m x τ a :
  addr_index a ≠ x → mem_alloc x τ m !! a = m !! a.
Proof.
  intros Ha. destruct m as [m]. unfold lookup, mem_lookup; simpl.
  by rewrite lookup_insert_ne by done.
Qed.
Lemma mem_alloc_lookup_new m x τ a :
  addr_index a ≠ x → mem_alloc x τ m !! a = m !! a.
Proof.
  intros Ha. destruct m as [m]. unfold lookup, mem_lookup; simpl.
  by rewrite lookup_insert_ne by done.
Qed.
Lemma mem_delete_lookup m x a : addr_index a ≠ x → delete x m !! a = m !! a.
Proof.
  intros Ha. destruct m as [m]. unfold lookup, mem_lookup; simpl.
  by rewrite lookup_alter_ne by done.
Qed.
Lemma mem_delete_lookup_freed m x a : addr_index a = x → delete x m !! a = None.
Proof.
  intros Ha. destruct m as [m]. unfold lookup, mem_lookup; simpl. rewrite Ha.
  rewrite lookup_alter. by destruct (m !! x); simplify_option_equality.
Qed.

Lemma mem_aliasing_help m a1 a2 σ1 σ2 :
  let mem_alter f a :=
    Mem (alter (obj_map (alter f (addr_ref a))) (addr_index a) (MMap m)) in
  ⊢ valid m → m ⊢ a1 : σ1 → m ⊢ a2 : σ2 →
  frozen a1 → frozen a2 → addr_is_obj a1 → addr_is_obj a2 →
  (**i 1.) *) (∀ j1 j2, addr_plus j1 a1 ⊥ addr_plus j2 a2) ∨
  (**i 2.) *) σ1 ⊆ σ2 ∨
  (**i 3.) *) σ2 ⊆ σ1 ∨
  (**i 4.) *) ∀ f j1 j2,
    mem_alter f (addr_plus j2 a2) !! addr_plus j1 a1 = None ∧
    mem_alter f (addr_plus j1 a1) !! addr_plus j2 a2 = None.
Proof.
  intros. destruct (addr_disjoint_cases m a1 a2 σ1 σ2)
    as [Ha12|[?|[?|(Hidx&s&r1'&i1&r2'&i2&r'&Ha1&Ha2&?)]]]; auto.
  do 3 right. intros f j1 j2. unfold mem_alter, lookup, mem_lookup, mem_force.
  destruct m as [m]; simpl.
  rewrite !addr_index_plus, <-!Hidx, !lookup_alter.
  destruct (m !! addr_index a1) as [[|w]|] eqn:Hw; simpl; auto.
  destruct (mem_lookup_raw_Obj (Mem m) (addr_index a1) w) as (τ&?&?&_); auto.
  destruct (addr_typed_ref_base (Mem m) a1 σ1) as (τ'&Hidx1&Hr1); auto.
  destruct (addr_typed_ref_base (Mem m) a2 σ2) as (τ''&Hidx2&Hr2); auto.
  rewrite <-Hidx in Hidx2; rewrite Ha1 in Hr1; rewrite Ha2 in Hr2.
  unfold addr_ref;
    rewrite !addr_ref_base_plus, Ha1, Ha2; simplify_option_equality.
  by erewrite !mval_lookup_non_aliasing by eauto.
Qed.
Lemma mem_aliasing m a1 a2 σ1 σ2 :
  ⊢ valid m → m ⊢ a1 : σ1 → m ⊢ a2 : σ2 →
  frozen a1 → frozen a2 → addr_is_obj a1 → addr_is_obj a2 →
  (**i 1.) *) (∀ j1 j2, addr_plus j1 a1 ⊥ addr_plus j2 a2) ∨
  (**i 2.) *) σ1 ⊆ σ2 ∨
  (**i 3.) *) σ2 ⊆ σ1 ∨
  (**i 4.) *) ∀ j1 j2,
    (∀ v1, <[addr_plus j1 a1:=v1]>m !! addr_plus j2 a2 = None) ∧
    mem_force (addr_plus j1 a1) m !! addr_plus j2 a2 = None ∧
    (∀ v2, <[addr_plus j2 a2:=v2]>m !! addr_plus j1 a1 = None) ∧
    mem_force (addr_plus j2 a2) m !! addr_plus j1 a1 = None.
Proof.
  intros. destruct (mem_aliasing_help m a1 a2 σ1 σ2) as [?|[?|[?|Hf]]]; auto.
  do 3 right. destruct m as [m]. intros j1 j2; split_ands.
  * intros. unfold insert, mem_insert; simpl. by rewrite (proj2 (Hf _ _ _)).
  * intros. unfold mem_force; simpl. by rewrite (proj2 (Hf _ _ _)).
  * intros. unfold insert, mem_insert; simpl. by rewrite (proj1 (Hf _ _ _)).
  * intros. unfold mem_force; simpl. by rewrite (proj1 (Hf _ _ _)).
Qed.

Lemma type_of_index_mem_le m1 m2 y σ :
  type_of_index m1 y = Some σ → m1 ⊆ m2 → type_of_index m2 y = Some σ.
Proof.
  unfold type_of_index, mem_type_of_index; simpl. intros ? Hm12.
  destruct (MMap m1 !! y) as [o1|] eqn:Ho1; simplify_equality'.
  destruct (Hm12 y o1) as (o2&Ho2&?); auto.
  rewrite Ho2; simpl; f_equal. symmetry; eauto using obj_le_type_of.
Qed.
Lemma addr_typed_mem_le m1 m2 a σ : m1 ⊢ a : σ → m1 ⊆ m2 → m2 ⊢ a : σ.
Proof. eauto using addr_typed_weaken_mem, type_of_index_mem_le. Qed.
Lemma ptr_typed_mem_le m1 m2 p σ : m1 ⊢ p : σ → m1 ⊆ m2 → m2 ⊢ p : σ.
Proof. eauto using ptr_typed_weaken_mem, type_of_index_mem_le. Qed.
Lemma vtyped_mem_le m1 m2 v σ : m1 ⊢ v : σ → m1 ⊆ m2 → m2 ⊢ v : σ.
Proof. eauto using vtyped_weaken_mem, type_of_index_mem_le. Qed.
Lemma mtyped_mem_le m1 m2 w σ : m1 ⊢ w : σ → m1 ⊆ m2 → m2 ⊢ w : σ.
Proof. eauto using mtyped_weaken_mem, type_of_index_mem_le. Qed.
Lemma obj_typed_mem_le m1 m2 o σ : m1 ⊢ o : σ → m1 ⊆ m2 → m2 ⊢ o : σ.
Proof. eauto using obj_typed_weaken_mem, type_of_index_mem_le. Qed.
Lemma val_le_mem_le m1 m2 v1 v2 : v1 ⊑@{m1} v2 → m1 ⊆ m2 → v1 ⊑@{m2} v2.
Proof. eauto using val_le_weaken_mem, type_of_index_mem_le. Qed.
Lemma mval_le_mem_le m1 m2 w1 w2 : w1 ⊑@{m1} w2 → m1 ⊆ m2 → w1 ⊑@{m2} w2.
Proof. eauto using mval_le_weaken_mem, type_of_index_mem_le. Qed.
Lemma obj_le_mem_le m1 m2 o1 o2 : o1 ⊑@{m1} o2 → m1 ⊆ m2 → o1 ⊑@{m2} o2.
Proof. eauto using obj_le_weaken_mem, type_of_index_mem_le. Qed.

Lemma mem_lookup_le m1 m2 a v1 :
  ⊢ valid m1 → m1 ⊆ m2 →
  m1 !! a = Some v1 → ∃ v2, m2 !! a = Some v2 ∧ v1 ⊑@{m2} v2.
Proof.
  intros Ha Hm12 Hmv1. apply mem_lookup_Some in Hmv1; auto.
  destruct Hmv1 as (w1&τ1&w3&τ3&?&?&?&?&?&?&?&?&Hobj&Hbyte).
  destruct (Hm12 (addr_index a) (Obj w1)) as (o2&?&Ho2); auto.
  inversion Ho2 as [|? w2 Hw12]; clear Ho2; subst.
  destruct (mval_lookup_le m2 w1 w2 (addr_ref a) w3) as (w4&?&?); auto.
  unfold lookup, mem_lookup; simplify_option_equality.
  destruct (decide (addr_is_obj a)).
  { exists (mval_to_val w4). rewrite Hobj by done. split; auto.
    eapply mval_to_val_le; eauto using mtyped_mem_le. }
  destruct (mval_lookup_byte_le m2 w3 w4 τ3 (addr_ref_byte a) v1)
    as (v2&?&?); eauto using mtyped_mem_le.
Qed.
Lemma mem_lookup_ge m1 m2 a v2 :
  ⊢ valid m2 → m1 ⊆ m2 → m2 !! a = Some v2 →
  m1 !! a = None ∨ ∃ v1, m1 !! a = Some v1 ∧ v1 ⊑@{m2} v2.
Proof.
  intros Hm Hm12 Hmv2. apply mem_lookup_Some in Hmv2; auto.
  destruct Hmv2 as (w2&τ2&w4&τ4&?&?&?&?&?&?&?&?&Hobj&Hbyte); auto.
  unfold lookup, mem_lookup. simpl.
  destruct (MMap m1 !! addr_index a) as [o1|] eqn:Ho1; simpl; auto.
  destruct (Hm12 (addr_index a) o1) as (o2&?&Ho2); auto.
  inversion Ho2 as [|w1 ?]; clear Ho2; simplify_option_equality.
  destruct (mval_lookup_ge m2 w1 w2 (addr_ref a) w4) as [|(w3&?&?)];
    simplify_option_equality; auto.
  right. destruct (decide (addr_is_obj a)).
  { exists (mval_to_val w3). rewrite Hobj by done. split; auto.
    eapply mval_to_val_le; eauto using mtyped_le. }
  destruct (mval_lookup_byte_ge m2 w3 w4 τ4 (addr_ref_byte a) v2)
    as (v1&?&?); eauto using mtyped_le.
Qed.
Lemma mem_insert_le m1 m2 a j σ v1 v2 :
  ⊢ valid m2 → m1 ⊆ m2 → m2 ⊢ a : σ → m2 ⊢ v1 : σ →
  v1 ⊑@{m2} v2 → <[addr_plus j a:=v1]>m1 ⊆ <[addr_plus j a:=v2]>m2.
Proof.
  destruct m1 as [m1], m2 as [m2]. unfold insert, mem_insert.
  intros Hm Hm12 Ha Hv1 Hv12 x o1; simpl.
  rewrite addr_index_plus, lookup_alter_Some. intros [(<-&o1'&?&->)|[??]].
  * destruct (Hm12 (addr_index a) o1') as (o2&Ho2&Ho12); simpl in *; auto.
    rewrite lookup_alter, Ho2; simpl. eexists; split; auto.
    apply obj_le_weaken_mem with (Mem m2); auto.
    { intros ??. rewrite <-(addr_index_plus a j).
      eapply (type_of_index_insert (Mem m2)); eauto using vtyped_ge. }
    inversion Ho12; subst; clear Ho12; constructor.
    destruct (addr_typed_ref_base (Mem m2) a σ) as (τ&?&?); auto.
    destruct (mem_lookup_raw_Obj (Mem m2) (addr_index a) w2)
      as (?&?&?&_); auto; simplify_option_equality.
    eapply mval_alter_le; rewrite ?addr_ref_base_plus; eauto using mtyped_le.
    intros w3 s4 ??. case_decide as Hobj; eauto using mval_of_val_le.
    rewrite addr_is_obj_plus in Hobj.
    eapply mval_insert_byte_le; eauto.
    by rewrite <-(addr_not_is_obj_type (Mem m2) a σ)
      by eauto using vtyped_not_void.
  * destruct (Hm12 x o1) as (o2&?&?); auto. exists o2.
    rewrite !lookup_alter_ne by done. split; auto.
    apply obj_le_weaken_mem with (Mem m2); auto.
    intros ??. rewrite <-(addr_index_plus a j).
    eapply (type_of_index_insert (Mem m2)); eauto using vtyped_ge.
Qed.
Lemma mem_force_le m1 m2 a σ :
  ⊢ valid m2 → m1 ⊆ m2 → m2 ⊢ a : σ → mem_force a m1 ⊆ mem_force a m2.
Proof.
  destruct m1 as [m1], m2 as [m2]. unfold insert, mem_insert.
  intros Hm Hm12 Ha x o1; simpl. rewrite lookup_alter_Some.
  intros [(<-&o1'&?&->)|[??]].
  * destruct (Hm12 (addr_index a) o1') as (o2&Ho2&Ho12); simpl in *; auto.
    rewrite lookup_alter, Ho2; simpl. eexists; split; auto.
    apply obj_le_weaken_mem with (Mem m2); auto.
    { intros ??. eapply (type_of_index_force (Mem m2)); eauto. }
    inversion Ho12; subst; clear Ho12; constructor.
    destruct (addr_typed_ref_base (Mem m2) a σ) as (τ&?&?); auto.
    destruct (mem_lookup_raw_Obj (Mem m2) (addr_index a) w2)
      as (?&?&?&_); auto; simplify_option_equality.
    eapply mval_alter_le; eauto using mtyped_le.
  * destruct (Hm12 x o1) as (o2&?&?); auto. exists o2.
    rewrite !lookup_alter_ne by done. split; auto.
    apply obj_le_weaken_mem with (Mem m2); auto.
    intros ??. eapply (type_of_index_force (Mem m2)); eauto.
Qed.

Lemma mem_alloc_le m1 m2 x τ :
  is_free x m2 → m1 ⊆ m2 → mem_alloc x τ m1 ⊆ mem_alloc x τ m2.
Proof.
  unfold mem_alloc. destruct m1 as [m1], m2 as [m2].
  intros Hx Hm x1 o1; simpl. rewrite lookup_insert_Some. intros [[-> <-]|[??]].
  * exists (Obj (mval_new τ)). by rewrite lookup_insert.
  * destruct (Hm x1 o1) as (o2&?&?); auto. exists o2.
    rewrite lookup_insert_ne by done. split; auto.
    apply obj_le_weaken_mem with (Mem m2); auto.
    intros ??. by apply type_of_index_alloc_ne.
Qed.
Lemma mem_delete_le m1 m2 x τ : m1 ⊆ m2 → delete x m1 ⊆ delete x m2.
Proof.
  unfold delete, mem_delete. destruct m1 as [m1], m2 as [m2].
  intros Hm x1 o1; simpl. rewrite lookup_alter_Some.
  intros [(->&o1'&?&->)|[??]].
  * exists (Freed (type_of o1')). rewrite lookup_alter; simpl. split; auto.
    destruct (Hm x1 o1') as (o2&?&?); auto.
    simplify_option_equality; do 2 f_equal. eauto using eq_sym, obj_le_type_of.
  * destruct (Hm x1 o1) as (o2&?&?); auto. exists o2.
    rewrite lookup_alter_ne by done. split; auto.
    apply obj_le_weaken_mem with (Mem m2); auto.
    intros ??. apply (type_of_index_delete (Mem m2)).
Qed.

Lemma mem_lookup_value_bytes m a v σ :
  ⊢ valid m → m ⊢ a : σ → m !! a = Some v → ∃ cs,
  (**i 1.) *) length cs = size_of σ ∧
  (**i 2.) *) m ⊢* cs : uchar ∧
  (**i 3.) *) (∀ j : nat,
    j < size_of σ → m !! addr_plus j (addr_cast uchar a) = cs !! j) ∧
  (**i 4.) *) val_to_bits v ⊑@{m}* mjoin (val_to_bits <$> cs).
Proof.
  intros Hm Ha Hav. pose proof (mem_lookup_Some _ _ _ Hm Hav) as Hav'.
  destruct Hav' as (w&τ&w'&τ'&Hma&?&?&?&Hwa&Hw'&?&?&Hobj&Hbyte).
  destruct (decide (addr_is_obj a)) as [Ha1|Ha1].
  { specialize (Hobj Ha1); subst.
    feed pose proof (addr_typed_ref_type_base_inv m a σ τ τ'); auto; subst.
    erewrite addr_is_obj_type_base in Hw' by eauto; simplify_type_equality'.
    exists (val_of_bits uchar <$>
      reshape (replicate (size_of σ) char_bits) (mval_to_bits w')); split_ands.
    * by rewrite fmap_length, reshape_length, replicate_length.
    * eapply Forall_fmap, Forall_impl;
        [eapply Forall_reshape, mval_to_bits_valid; eauto |].
      eauto using val_of_bits_typed, TBase_valid, TInt_valid.
    * intros j Hj. unfold lookup at 1, mem_lookup.
      rewrite addr_index_plus, addr_index_cast, Hma; simpl.
      erewrite list_lookup_fmap, <-mval_lookup_reshape by eauto.
      erewrite addr_ref_plus_char_cast, Hwa by eauto; simpl.
      rewrite option_guard_True by (rewrite addr_byte_size_plus,
        addr_byte_size_cast; eauto using addr_byte_lt_size_char_cast).
      rewrite option_guard_True by (by rewrite addr_type_plus, addr_type_cast).
      case_decide as Hobj.
      + erewrite addr_is_obj_plus, addr_is_obj_cast,
          addr_is_obj_type_base in Hobj by eauto; simplify_equality.
        replace j with 0 by (rewrite size_of_int, int_size_char in Hj; lia).
        by erewrite mval_lookup_byte_char by eauto.
      + by erewrite addr_ref_byte_plus_char_cast by eauto.
    * assert (Forall (λ bs, val_to_bits (val_of_bits uchar bs) = bs)
        (reshape (replicate (size_of σ) char_bits) (mval_to_bits w'))).
      { generalize (mval_to_bits_length _ _ _ Hw'); unfold bit_size_of.
        rewrite <-(int_bits_char Unsigned), <-bit_size_of_int.
        generalize (mval_to_bits w').
        induction (size_of σ) as [|n IH]; intros bs; simpl; constructor; auto.
        + rewrite val_of_bits_base; unfold val_to_bits; simpl.
          by rewrite base_val_to_of_bits_char by (rewrite take_length_le; lia).
        + apply IH. rewrite drop_length. lia. }
      erewrite <-list_fmap_compose, (proj1 (Forall_fmap_ext _ id _)) by done.
      rewrite list_fmap_id, join_reshape by
        (by erewrite sum_list_replicate, mval_to_bits_length by eauto).
      eapply mval_to_bits_le, mval_of_to_val; eauto. }
  simplify_type_equality.
  feed pose proof (addr_not_is_obj_type m a σ); auto; subst.
  rewrite size_of_int, int_size_char. exists [v]; split_ands; auto.
  * apply Forall_singleton. eauto using mval_lookup_byte_typed.
  * intros [|?] ?; auto with lia; simpl.
    by erewrite addr_plus_0, addr_cast_self by eauto.
  * by simpl; rewrite (right_id_L [] (++)).
Qed.

Lemma mem_lookup_insert_raw m a v x :
  addr_index a = x →
  let f w :=
   if decide (addr_is_obj a) then mval_of_val v else <[addr_ref_byte a:=v]> w in
  MMap (<[a:=v]>m) !! x = obj_map (alter f (addr_ref a)) <$> MMap m !! x.
Proof. intros <-. destruct m as [m]; simpl. by rewrite lookup_alter. Qed.
Lemma mem_lookup_insert_ne_raw m a v x  :
  addr_index a ≠ x → MMap (<[a:=v]>m) !! x = MMap m !! x.
Proof. intros. destruct m as [m]; simpl. by rewrite lookup_alter_ne. Qed.

Lemma mem_lookup_insert_array_raw m a σ (j : nat) cs :
  ⊢ valid m → m ⊢ a : σ → addr_is_obj a →
  m ⊢* cs : uchar → length cs + j = size_of σ → 0 < length cs →
  MMap (mem_insert_array (addr_plus j (addr_cast uchar a)) cs m)
    !! addr_index a = obj_map (alter (mval_insert_bytes j cs) (addr_ref a))
                      <$> MMap m !! addr_index a.
Proof.
  intros Hm Haσ Hobj Hcs; revert j.
  destruct (decide (addr_is_obj (addr_cast uchar a))) as [Hobj'|?].
  { intros j Hj Hlen. rewrite addr_is_obj_cast in Hobj'.
    erewrite addr_is_obj_type_base in Hobj' by eauto. subst.
    rewrite size_of_int, int_size_char in Hj.
    destruct cs as [|c []]; simplify_equality'; auto with lia.
    rewrite Forall_singleton in Hcs.
    rewrite mem_lookup_insert_raw by (by destruct a).
    destruct (MMap m !! _) as [[|w]|] eqn:Hw; simpl; do 2 f_equal.
    destruct (mem_lookup_raw_Obj m (addr_index a) w) as (τ&?&?&_); auto.
    destruct (addr_typed_ref_base m a uchar) as (τ'&?&?); auto.
    simplify_option_equality. rewrite addr_plus_0, addr_ref_cast.
    eapply mval_alter_ext_typed; eauto. intros w' Hw'. case_decide as Hobj'.
    { rewrite addr_is_obj_cast in Hobj'; rewrite <-Hobj' in Hw'.
      by erewrite mval_insert_byte_char by eauto. }
    by erewrite addr_ref_byte_cast, addr_is_obj_ref_byte by eauto. }
  induction Hcs as [|c1 cs Hc1 Hcs IH]; simpl; intros j Hj Hlen; auto with lia.
  destruct (nil_or_length_pos cs); simplify_equality'.
  { rewrite mem_lookup_insert_raw by (by destruct a).
    destruct (MMap m !! _) as [[|w]|]; simpl; do 2 f_equal.
    erewrite addr_ref_plus_char_cast by eauto with lia.
    eapply mval_alter_ext; intros w'. case_decide as Hobj'.
    * by rewrite addr_is_obj_plus in Hobj'.
    * by erewrite addr_ref_byte_plus_char_cast by eauto with lia. }
  rewrite (addr_plus_plus_nat _ 1 j).
  rewrite mem_lookup_insert_raw by (by destruct a); rewrite IH by lia.
  destruct (MMap m !! _) as [[|w]|]; simpl; do 2 f_equal.
  erewrite addr_ref_plus_char_cast by eauto with lia.
  rewrite <-mval_alter_compose.
  eapply mval_alter_ext; intros w'. case_decide as Hobj'.
  * by rewrite addr_is_obj_plus in Hobj'.
  * simpl. by erewrite addr_ref_byte_plus_char_cast by eauto with lia.
Qed.
Lemma mem_lookup_insert_array_ne_raw m a cs x :
  addr_index a ≠ x → MMap (mem_insert_array a cs m) !! x = MMap m !! x.
Proof.
  revert a. induction cs as [|c cs IH]; simpl; intros; auto.
  by rewrite mem_lookup_insert_ne_raw, IH by (by rewrite ?addr_index_plus).
Qed.

Lemma mem_insert_value_bytes m a v σ cs :
  ⊢ valid m → m ⊢ a : σ → addr_strict m a → m ⊢ v : σ →
  length cs = size_of σ → m ⊢* cs : uchar →
  val_to_bits v ⊑@{m}* mjoin (val_to_bits <$> cs) →
  <[a:=v]>m ⊆ mem_insert_array (addr_cast uchar a) cs m.
Proof.
  destruct m as [m]; intros Hm Haσ Ha Hvσ Hlen Hcs Hvcs x o; simpl.
  rewrite lookup_alter_Some. intros [(<-&o'&Hx&->)|[? Hx]].
  { destruct (mem_lookup_raw (Mem m) (addr_index a) o') as (τ&Ho'&?&_); auto.
    destruct (addr_typed_ref_base (Mem m) a σ) as (τ'&?&Hr); auto.
    simplify_option_equality. destruct (decide (addr_is_obj a)).
    * erewrite addr_is_obj_type_base in Hr by eauto.
      exists (obj_map (alter (λ _, mval_of_bits σ $
        mjoin (val_to_bits <$> cs)) (addr_ref a)) o'); split.
      { rewrite <-(addr_plus_0 (addr_cast _ _)).
        feed pose proof (size_of_pos σ); eauto using vtyped_type_valid.
        erewrite (mem_lookup_insert_array_raw _ _ _ 0); eauto with lia; simpl.
        rewrite Hx. destruct Ho' as [|w τ Hw]; simpl; do 2 f_equal; auto.
        eapply mval_alter_ext_typed; eauto using mval_insert_bytes_join. }
      apply obj_le_weaken_mem with (Mem m).
      { intros ??. rewrite <-(addr_plus_0 (addr_cast uchar a)).
        eapply (type_of_index_insert_array _ _ 0);
          eauto using addr_cast_ok_typed, addr_cast_ok_uchar. }
      destruct Ho' as [|w τ Hw]; constructor.
      eapply mval_alter_le; eauto; intros w3 w4 ??.
      transitivity (mval_of_bits σ (val_to_bits v)).
      { unfold val_to_bits.
        erewrite mval_of_to_bits by eauto using mval_of_val_typed.
        eapply munion_reset_above; eauto using mval_of_val_typed. }
      eapply mval_of_bits_le; eauto using vtyped_type_valid.
    * feed pose proof (addr_not_is_obj_type (Mem m) a σ);
        eauto using vtyped_not_void; subst.
      rewrite size_of_int, int_size_char in Hlen.
      destruct Hcs as [|c ? Hc []]; simplify_equality'.
      rewrite (right_id_L [] (++)) in Hvcs.
      apply (val_of_bits_le _ uchar) in Hvcs;
        eauto using TBase_valid, TInt_valid, val_to_bits_valid.
      erewrite !val_of_to_bits in Hvcs by eauto using union_free_base.
      erewrite !val_frozen_freeze in Hvcs by eauto using val_frozen_int.
      rewrite addr_index_cast, lookup_alter, Hx.
      rewrite addr_ref_cast, addr_ref_byte_cast.
      eexists; split; [done|]. apply obj_le_weaken_mem with (Mem m).
      { intros ??. rewrite <-(addr_plus_0 (addr_cast uchar a)).
        eapply (type_of_index_insert _ _ 0);
          eauto using addr_cast_ok_typed, addr_cast_ok_uchar. }
      destruct Ho' as [|w τ Hw]; constructor.
      eapply mval_alter_le; eauto; intros w3 w4 Hw3 ?. case_decide as Hobj.
      { feed pose proof (addr_byte_range (Mem m) a uchar) as Hbyte; auto.
        rewrite addr_is_obj_cast in Hobj. rewrite <-Hobj in Hw3, Hbyte.
        rewrite size_of_int, int_size_char in Hbyte.
        replace (addr_ref_byte a) with 0 by lia.
        erewrite mval_insert_byte_char by eauto. eauto using mval_of_val_le. }
      eauto using mval_insert_byte_le. }
  exists o. split; auto.
  by rewrite mem_lookup_insert_array_ne_raw by (by destruct a).
Qed.
End memory.
