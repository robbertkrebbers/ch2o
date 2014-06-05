(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export refinements.
Require Import pointer_casts.
Local Open Scope ctype_scope.

Record addr (Ti : Set) : Set := Addr {
  addr_index : index;
  addr_ref_base : ref Ti;
  addr_byte : nat;
  addr_type_object : type Ti;
  addr_type_base : type Ti;
  addr_type : type Ti
}.
Add Printing Constructor addr.
Arguments Addr {_} _ _ _ _ _ _.
Arguments addr_index {_} _.
Arguments addr_ref_base {_} _.
Arguments addr_byte {_} _.
Arguments addr_type_object {_} _.
Arguments addr_type_base {_} _.
Arguments addr_type {_} _.

Instance addr_eq_dec `{Ti : Set, ∀ k1 k2 : Ti, Decision (k1 = k2)}
  (a1 a2 : addr Ti) : Decision (a1 = a2).
Proof. solve_decision. Defined.

Section address_operations.
  Context `{TypeOfIndex Ti M, Refine Ti M, IndexAlive M, IntEnv Ti, PtrEnv Ti,
    ∀ m x, Decision (index_alive m x)}.

  Inductive addr_typed' (Γ : env Ti) (m : M) : addr Ti → type Ti → Prop :=
    Addr_typed o r i τ σ σc :
      type_of_index m o = Some τ →
      ✓{Γ} τ →
      int_typed (size_of Γ τ) sptrT →
      Γ ⊢ r : τ ↣ σ →
      ref_offset r = 0 →
      i ≤ size_of Γ σ * ref_size r →
      i `mod` size_of Γ σc = 0 →
      σ >*> σc →
      addr_typed' Γ m (Addr o r i τ σ σc) σc.
  Global Instance addr_typed :
    Typed (env Ti * M) (type Ti) (addr Ti) := curry addr_typed'.
  Global Instance addr_freeze : Freeze (addr Ti) := λ β a,
    let 'Addr x r i τ σ σc := a in Addr x (freeze β <$> r) i τ σ σc.

  Global Instance type_of_addr: TypeOf (type Ti) (addr Ti) := addr_type.
  Global Instance addr_type_check:
      TypeCheck (env Ti * M) (type Ti) (addr Ti) := λ Γm a,
    let (Γ,m) := Γm in
    let 'Addr o r i τ σ σc := a in
    τ' ← type_of_index m o; guard (τ' = τ);
    guard (✓{Γ} τ);
    guard (int_typed (size_of Γ τ) sptrT);
    guard (Γ ⊢ r : τ ↣ σ);
    guard (σ >*> σc);
    guard (ref_offset r = 0);
    guard (i ≤ size_of Γ σ * ref_size r);
    guard (i `mod` size_of Γ σc = 0);
    Some σc.
  Global Arguments addr_type_check _ !_ /.

  Definition addr_strict (Γ : env Ti) (a : addr Ti) : Prop :=
    addr_byte a < size_of Γ (addr_type_base a) * ref_size (addr_ref_base a) ∧
    type_of a ≠ voidT.
  Global Arguments addr_strict _ !_ /.
  Definition addr_is_obj (a : addr Ti) : Prop :=
    type_of a = addr_type_base a.
  Global Arguments addr_is_obj !_ /.
  Definition addr_offset (Γ : env Ti) (a : addr Ti) : nat :=
    addr_byte a `div` size_of' Γ a.
  Global Arguments addr_offset _ !_ /.
  Definition addr_ref (Γ : env Ti) (a : addr Ti) : ref Ti :=
    ref_set_offset (addr_byte a `div` size_of Γ (addr_type_base a))
      (addr_ref_base a).
  Global Arguments addr_ref _ !_ /.
  Definition addr_ref_byte (Γ : env Ti) (a : addr Ti) : nat :=
    addr_byte a `mod` size_of Γ (addr_type_base a).
  Global Arguments addr_ref_byte _ !_ /.
  Definition addr_object_offset (Γ : env Ti) (a : addr Ti) : nat :=
    ref_object_offset Γ (addr_ref_base a) + addr_byte a * char_bits.

  Global Arguments addr_object_offset _ !_ /.
  Global Instance addr_disjoint: DisjointE (env Ti) (addr Ti) := λ Γ a1 a2,
    (addr_index a1 ≠ addr_index a2) ∨
    (addr_index a1 = addr_index a2 ∧ addr_ref Γ a1 ⊥ addr_ref Γ a2) ∨
    (addr_index a1 = addr_index a2 ∧
      freeze true <$> addr_ref Γ a1 = freeze true <$> addr_ref Γ a2 ∧
      ¬addr_is_obj a1 ∧ ¬addr_is_obj a2 ∧
      addr_ref_byte Γ a1 ≠ addr_ref_byte Γ a2).
  Definition addr_top (o : index) (σ : type Ti) : addr Ti := Addr o [] 0 σ σ σ.

  Definition addr_plus_ok (Γ : env Ti) (m : M) (j : Z) (a : addr Ti) : Prop :=
    index_alive m (addr_index a) ∧
    (0 ≤ addr_byte a + j * size_of' Γ a
       ≤ size_of Γ (addr_type_base a) * ref_size (addr_ref_base a))%Z.
  Global Arguments addr_plus_ok _ _ _ !_ /.
  Definition addr_plus (Γ : env Ti) (j : Z) (a : addr Ti): addr Ti :=
    let 'Addr x r i τ σ σc := a
    in Addr x r (Z.to_nat (i + j * size_of Γ σc)) τ σ σc.
  Global Arguments addr_plus _ _ !_ /.

  Definition addr_minus_ok (m : M) (a1 a2 : addr Ti) : Prop :=
    index_alive m (addr_index a1) ∧
    addr_index a1 = addr_index a2 ∧
    freeze true <$> addr_ref_base a1 = freeze true <$> addr_ref_base a2.
  Global Arguments addr_minus_ok _ !_ !_ /.
  Definition addr_minus (Γ : env Ti) (a1 a2 : addr Ti) : Z :=
    ((addr_byte a1 - addr_byte a2) `div` size_of' Γ a1)%Z.
  Global Arguments addr_minus _ !_ !_ /.

  Definition addr_cast_ok (Γ : env Ti) (σc : type Ti) (a : addr Ti) : Prop :=
    addr_type_base a >*> σc ∧ addr_byte a `mod` size_of Γ σc = 0.
  Global Arguments addr_cast_ok _ _ !_ /.
  Definition addr_cast (σc : type Ti) (a : addr Ti) : addr Ti :=
    let 'Addr o r i τ σ _ := a in Addr o r i τ σ σc.
  Global Arguments addr_cast _ !_ /.

  Definition addr_elt (Γ : env Ti) (a : addr Ti) : addr Ti :=
    from_option a $
      '(σ,n) ← maybe_TArray (type_of a);
      Some (Addr (addr_index a) (RArray 0 σ n :: addr_ref Γ a) 0
                 (addr_type_object a) σ σ).
  Global Arguments addr_elt _ !_ /.
  Definition addr_field (Γ : env Ti) (i : nat) (a : addr Ti) : addr Ti :=
    from_option a $
      '(c,s) ← maybe_TCompound (type_of a);
      σ ← Γ !! s ≫= (!! i);
      let rs := match c with
                | Struct_kind => RStruct i s | Union_kind => RUnion i s false
                end in
      Some (Addr (addr_index a) (rs :: addr_ref Γ a) 0
                 (addr_type_object a) σ σ).
  Global Arguments addr_field _ _ !_ /.

  Inductive ref_refine (r' : ref Ti) (sz : nat) :
       ref Ti → nat → ref Ti → nat → Prop :=
    | ref_refine_nil i :
       ref_refine r' sz [] i (ref_base r') (i + sz * ref_offset r')
    | ref_refine_ne_nil rs r i :
       ref_refine r' sz (rs :: r) i (rs :: r ++ r') i.
  Inductive addr_refine' (Γ : env Ti) (f : mem_inj Ti) (m1 m2 : M) :
       addr Ti → addr Ti → type Ti → Prop :=
    | Addr_refine' o o' r r' r'' i i'' τ τ' σ σc :
       f !! o = Some (o',r') →
       type_of_index m1 o = Some τ →
       type_of_index m2 o' = Some τ' →
       ✓{Γ} τ' →
       int_typed (size_of Γ τ') sptrT →
       Γ ⊢ r' : τ' ↣ τ → Γ ⊢ r : τ ↣ σ →
       ref_offset r = 0 →
       i ≤ size_of Γ σ * ref_size r →
       i `mod` size_of Γ σc = 0 →
       σ >*> σc →
       ref_refine (freeze true <$> r') (size_of Γ σ) r i r'' i'' →
       addr_refine' Γ f m1 m2 (Addr o r i τ σ σc) (Addr o' r'' i'' τ' σ σc) σc.
  Global Instance addr_refine: RefineT Ti M (addr Ti) (type Ti) := addr_refine'.
End address_operations.

Typeclasses Opaque addr_strict addr_is_obj addr_disjoint.

Section addresses.
  Context `{MemSpec Ti M}.
  Implicit Types Γ : env Ti.
  Implicit Types m : M.
  Implicit Types τ σ : type Ti.
  Implicit Types r : ref Ti.
  Implicit Types a : addr Ti.

  (** ** Typing and general properties *)
  Lemma addr_freeze_freeze β1 β2 a : freeze β1 (freeze β2 a) = freeze β1 a.
  Proof. destruct a; f_equal'; auto using ref_freeze_freeze. Qed.
  Lemma addr_typed_alt Γ m a σ :
    (Γ,m) ⊢ a : σ ↔
      type_of_index m (addr_index a) = Some (addr_type_object a) ∧
      ✓{Γ} (addr_type_object a) ∧
      int_typed (size_of Γ (addr_type_object a)) sptrT ∧
      Γ ⊢ addr_ref_base a : addr_type_object a ↣ addr_type_base a ∧
      ref_offset (addr_ref_base a) = 0 ∧
      addr_byte a ≤ size_of Γ (addr_type_base a) * ref_size (addr_ref_base a) ∧
      addr_byte a `mod` size_of Γ σ = 0 ∧
      addr_type_base a >*> σ ∧
      type_of a = σ.
  Proof.
    split; [destruct 1; naive_solver|intros (?&?&?&?&?&?&?&?&?)].
    by destruct a; simplify_equality; constructor.
  Qed.
  Lemma addr_typed_index Γ m a σ :
    (Γ,m) ⊢ a : σ → type_of_index m (addr_index a) = Some (addr_type_object a).
  Proof. by destruct 1. Qed.
  Lemma addr_typed_offset Γ m a σ :
    (Γ,m) ⊢ a : σ → ref_offset (addr_ref_base a) = 0.
  Proof. by destruct 1. Qed.
  Lemma addr_typed_type_object_valid Γ m a σ :
    (Γ,m) ⊢ a : σ → ✓{Γ} (addr_type_object a).
  Proof. by destruct 1. Qed.
  Lemma addr_typed_ref_base_typed Γ m a σ :
    (Γ,m) ⊢ a : σ → Γ ⊢ addr_ref_base a : addr_type_object a ↣ addr_type_base a.
  Proof. by destruct 1. Qed.
  Lemma addr_typed_type_base_valid Γ m a σ :
    ✓ Γ → (Γ,m) ⊢ a : σ → ✓{Γ} (addr_type_base a).
  Proof.
    eauto using ref_typed_type_valid,
      addr_typed_ref_base_typed, addr_typed_type_object_valid.
  Qed.
  Lemma addr_typed_ref_typed Γ m a σ :
    ✓ Γ → (Γ,m) ⊢ a : σ → addr_strict Γ a →
    Γ ⊢ addr_ref Γ a : addr_type_object a ↣ addr_type_base a.
  Proof.
    intros ?? [??].
    apply ref_set_offset_typed; eauto using addr_typed_ref_base_typed.
    apply Nat.div_lt_upper_bound;
      eauto using size_of_ne_0, addr_typed_type_base_valid.
  Qed.
  Lemma addr_typed_cast Γ m a σ : (Γ,m) ⊢ a : σ → addr_type_base a >*> σ.
  Proof. by destruct 1. Qed.
  Lemma addr_offset_aligned Γ m a σ :
    (Γ,m) ⊢ a : σ → addr_byte a `mod` size_of Γ σ = 0.
  Proof. by destruct 1. Qed.
  Lemma addr_typed_type_of_object_base Γ m a σ :
    (Γ,m) ⊢ a : σ → type_of_object Γ m (addr_index a)
      (addr_ref_base a) = Some (addr_type_base a).
  Proof.
    intros Ha. rewrite type_of_object_Some.
    exists (addr_type_object a). by destruct Ha.
  Qed.
  Lemma addr_typed_type_of_object Γ m a σ :
    ✓ Γ → (Γ,m) ⊢ a : σ → addr_strict Γ a →
    type_of_object Γ m (addr_index a) (addr_ref Γ a) = Some (addr_type_base a).
  Proof.
    intros. unfold type_of_object. erewrite addr_typed_index by eauto; simpl.
    eapply path_type_check_complete, addr_typed_ref_typed; eauto.
  Qed.
  Lemma addr_typed_type_valid Γ m a σ :
    ✓ Γ → (Γ,m) ⊢ a : σ → ✓{Γ} σ ∨ σ = voidT.
  Proof.
    destruct 2 as [o r i τ σ σc]; destruct (castable_type_valid Γ σ σc);
      subst; eauto using ref_typed_type_valid.
  Qed.
  Lemma addr_size_of_type_pos Γ m a σ : ✓ Γ → (Γ,m) ⊢ a : σ → 0 < size_of Γ σ.
  Proof.
    intros. destruct (addr_typed_type_valid Γ m a σ) as [?| ->];
      auto using size_of_pos. rewrite size_of_void; lia.
  Qed.
  Lemma addr_size_of_type_ne_0 Γ m a σ: ✓ Γ → (Γ,m) ⊢ a : σ → size_of Γ σ ≠ 0.
  Proof. rewrite Nat.neq_0_lt_0. by apply addr_size_of_type_pos. Qed.
  Lemma addr_offset_aligned_alt Γ m a σ :
     ✓ Γ → (Γ,m) ⊢ a : σ → (size_of Γ σ | addr_byte a).
  Proof.
    intros. apply Nat.mod_divide;
      eauto using addr_offset_aligned, addr_size_of_type_ne_0.
  Qed.
  Lemma addr_typed_ptr_type_valid Γ m a σ :
    ✓ Γ → (Γ,m) ⊢ a : σ → ptr_type_valid Γ σ.
  Proof.
    intros. destruct (addr_typed_type_valid Γ m a σ) as [?| ->];
      auto using TVoid_ptr_valid, type_valid_ptr_type_valid.
  Qed.
  Global Instance: TypeOfSpec (env Ti * M) (type Ti) (addr Ti).
  Proof. by intros [??]; destruct 1. Qed.
  Global Instance: TypeCheckSpec (env Ti * M) (type Ti) (addr Ti) (λ _, True).
  Proof.
    intros [Γ m] a σ _. split.
    * destruct a; intros; simplify_option_equality; constructor; auto.
    * by destruct 1; simplify_option_equality.
  Qed.
  Lemma addr_typed_weaken Γ1 Γ2 m1 m2 a σ :
    ✓ Γ1 → (Γ1,m1) ⊢ a : σ → Γ1 ⊆ Γ2 →
    (∀ o σ, type_of_index m1 o = Some σ → type_of_index m2 o = Some σ) →
    (Γ2,m2) ⊢ a : σ.
  Proof.
    intros ? [o r i τ σ' σc'] ??. constructor; simpl; split_ands;
      eauto using type_valid_weaken, ref_typed_weaken.
    { by erewrite <-size_of_weaken by eauto. }
    { by erewrite <-size_of_weaken by eauto using ref_typed_type_valid. }
    destruct (castable_type_valid Γ1 σ' σc') as [| ->];
      eauto using ref_typed_type_valid.
    * by erewrite <-size_of_weaken by eauto.
    * by rewrite size_of_void.
  Qed.
  Global Instance addr_strict_dec Γ a : Decision (addr_strict Γ a).
  Proof. unfold addr_strict; apply _. Defined.
  Global Instance addr_is_obj_dec a : Decision (addr_is_obj a).
  Proof. unfold addr_is_obj; apply _. Defined.
  Global Instance addr_disjoint_dec Γ a1 a2 : Decision (a1 ⊥{Γ} a2).
  Proof. unfold disjointE, addr_disjoint; apply _. Defined.
  Lemma addr_offset_representable Γ m a σc :
    ✓ Γ → (Γ,m) ⊢ a : σc → int_typed (addr_offset Γ a) sptrT.
  Proof.
    intros ? Ha. assert (0 < size_of Γ σc)%Z.
    { apply (Nat2Z.inj_lt 0); eauto using addr_size_of_type_pos. }
    destruct Ha as [o r i τ σ σc ?? [_ ?]]; simpl; split.
    { transitivity 0; auto using int_lower_nonpos with zpos. }
    rewrite Z2Nat_inj_div. apply Z.div_lt_upper_bound; [done|].
    apply Z.lt_le_trans with (1 * int_upper sptrT)%Z;
      [|apply Z.mul_le_mono_pos_r; auto using int_upper_pos with lia].
    apply Z.le_lt_trans with (size_of Γ τ); [rewrite <-Nat2Z.inj_le|lia].
    transitivity (size_of Γ σ * ref_size r); auto using size_of_ref.
  Qed.
  Lemma addr_index_freeze β a : addr_index (freeze β a) = addr_index a.
  Proof. by destruct a. Qed.
  Lemma addr_ref_base_freeze β a :
    addr_ref_base (freeze β a) = freeze β <$> addr_ref_base a.
  Proof. by destruct a. Qed.
  Lemma addr_byte_freeze β a : addr_byte (freeze β a) = addr_byte a.
  Proof. by destruct a. Qed.
  Lemma addr_type_base_freeze β a :
    addr_type_base (freeze β a) = addr_type_base a.
  Proof. by destruct a. Qed.
  Lemma addr_type_of_freeze β a : type_of (freeze β a) = type_of a.
  Proof. by destruct a. Qed.
  Lemma addr_offset_freeze Γ β a : addr_offset Γ (freeze β a) = addr_offset Γ a.
  Proof. by destruct a. Qed.
  Lemma addr_ref_freeze Γ β a :
    addr_ref Γ (freeze β a) = freeze β <$> addr_ref Γ a.
  Proof.
    unfold addr_ref. by rewrite !addr_ref_base_freeze, addr_byte_freeze,
      addr_type_base_freeze, ref_set_offset_freeze.
  Qed.
  Lemma addr_is_obj_freeze β a : addr_is_obj (freeze β a) ↔ addr_is_obj a.
  Proof.
    unfold addr_is_obj. by rewrite addr_type_of_freeze, addr_type_base_freeze.
  Qed.
  Lemma addr_is_obj_freeze_2 β a : addr_is_obj a → addr_is_obj (freeze β a).
  Proof. by rewrite addr_is_obj_freeze. Qed.
  Lemma addr_strict_freeze Γ β a : addr_strict Γ (freeze β a) ↔ addr_strict Γ a.
  Proof.
    unfold addr_strict. by rewrite addr_byte_freeze, addr_type_base_freeze,
      addr_ref_base_freeze, addr_type_of_freeze, ref_size_freeze.
  Qed.
  Lemma addr_strict_freeze_2 Γ β a :
    addr_strict Γ a → addr_strict Γ (freeze β a).
  Proof. by rewrite addr_strict_freeze. Qed.
  Lemma addr_ref_byte_freeze Γ β a :
    addr_ref_byte Γ (freeze β a) = addr_ref_byte Γ a.
  Proof.
    unfold addr_ref_byte. by rewrite addr_byte_freeze, addr_type_base_freeze.
  Qed.
  Lemma addr_typed_freeze Γ m β a σ : (Γ,m) ⊢ freeze β a : σ ↔ (Γ,m) ⊢ a : σ.
  Proof.
    rewrite !addr_typed_alt; destruct a; simpl. by rewrite ref_offset_freeze,
      ref_size_freeze; setoid_rewrite ref_typed_freeze.
  Qed.
  Lemma addr_type_check_freeze Γm β a :
    type_check Γm (freeze β a) = type_check Γm a.
  Proof.
    destruct Γm. apply option_eq; intros.
    by rewrite !type_check_correct, addr_typed_freeze.
  Qed.
  Lemma addr_strict_not_void Γ m a σ :
    (Γ,m) ⊢ a : σ → addr_strict Γ a → σ ≠ voidT.
  Proof. by intros ? (?&?); simplify_type_equality. Qed.
  Lemma addr_is_obj_ref_byte Γ m a σ :
    (Γ,m) ⊢ a : σ → addr_is_obj a → addr_ref_byte Γ a = 0.
  Proof. by destruct 1; intros; simplify_equality'. Qed.
  Lemma addr_is_obj_type_base Γ m a σ :
    (Γ,m) ⊢ a : σ → addr_is_obj a → addr_type_base a = σ.
  Proof. by destruct 1. Qed.
  Lemma addr_not_obj_type Γ m a σ :
    (Γ,m) ⊢ a : σ → ¬addr_is_obj a → σ ≠ voidT → σ = ucharT.
  Proof.
    intros [o r i τ σ' σc] ??. destruct (proj1 (castable_alt σ' σc))
      as [?|[?|?]]; simplify_equality'; auto.
  Qed.
  Lemma addr_not_obj_size_of Γ m a σ :
    (Γ,m) ⊢ a : σ → ¬addr_is_obj a → size_of Γ σ = 1.
  Proof.
    intros. destruct (decide (σ = voidT)) as [->|]; auto using size_of_void.
    by rewrite (addr_not_obj_type _ _ a σ), size_of_int, int_size_char by eauto.
  Qed.
  Lemma addr_not_obj_bit_size_of Γ m a σ :
    (Γ,m) ⊢ a : σ → ¬addr_is_obj a → bit_size_of Γ σ = char_bits.
  Proof.
    intros. unfold bit_size_of. erewrite addr_not_obj_size_of by eauto; lia.
  Qed.
  Lemma addr_byte_range Γ m a σ :
    ✓ Γ → (Γ,m) ⊢ a : σ → addr_strict Γ a →
    addr_ref_byte Γ a < size_of Γ (addr_type_base a).
  Proof.
    intros. apply Nat.mod_bound_pos; auto with lia.
    eapply size_of_pos, addr_typed_type_base_valid; eauto.
  Qed.
  Lemma addr_size_of_weaken Γ1 Γ2 m1 a σ :
    ✓ Γ1 → (Γ1,m1) ⊢ a : σ → Γ1 ⊆ Γ2 → size_of' Γ1 a = size_of' Γ2 a.
  Proof.
    intros ? [o r i τ σ' σc'] ?; simpl. destruct (castable_type_valid Γ1 σ' σc')
      as [| ->]; eauto using ref_typed_type_valid.
    * by erewrite size_of_weaken by eauto using ref_typed_type_valid.
    * by rewrite !size_of_void.
  Qed.
  Lemma addr_strict_weaken Γ1 Γ2 m1 a σ :
    ✓ Γ1 → (Γ1,m1) ⊢ a : σ → addr_strict Γ1 a → Γ1 ⊆ Γ2 → addr_strict Γ2 a.
  Proof.
    unfold addr_strict. intros ?? [] ?.
    by erewrite <-size_of_weaken by eauto using addr_typed_type_base_valid.
  Qed.
  Lemma addr_offset_weaken Γ1 Γ2 m1 a σ :
    ✓ Γ1 → (Γ1,m1) ⊢ a : σ → Γ1 ⊆ Γ2 → addr_offset Γ1 a = addr_offset Γ2 a.
  Proof.
    unfold addr_offset. intros. by erewrite addr_size_of_weaken by eauto.
  Qed.
  Lemma addr_ref_weaken Γ1 Γ2 m1 a σ :
    ✓ Γ1 → (Γ1,m1) ⊢ a : σ → Γ1 ⊆ Γ2 → addr_ref Γ1 a = addr_ref Γ2 a.
  Proof.
    intros ? [] ?; simpl.
    erewrite size_of_weaken by eauto using ref_typed_type_valid.
    eauto using addr_offset_weaken.
  Qed.
  Lemma addr_ref_byte_weaken Γ1 Γ2 m1 a σ :
    ✓ Γ1 → (Γ1,m1) ⊢ a : σ → Γ1 ⊆ Γ2 → addr_ref_byte Γ1 a = addr_ref_byte Γ2 a.
  Proof.
    intros ? [] ?; simpl.
    by erewrite size_of_weaken by eauto using ref_typed_type_valid.
  Qed.
  Lemma addr_object_offset_alt Γ m a σ :
    ✓ Γ → (Γ,m) ⊢ a : σ → addr_strict Γ a → addr_object_offset Γ a
    = ref_object_offset Γ (addr_ref Γ a) + addr_ref_byte Γ a * char_bits.
  Proof.
    intros ? [o r i τ σ' σc' Hor] [??]; simpl in *.
    erewrite ref_object_offset_set_offset_0
      by eauto using Nat.div_lt_upper_bound, size_of_ne_0, ref_typed_type_valid.
    rewrite (Nat.div_mod i (size_of Γ σ')) at 1
      by eauto using size_of_ne_0,ref_typed_type_valid; unfold bit_size_of; lia.
  Qed.

  (** ** Operations *)
  Lemma addr_plus_ok_typed Γ m a σ j :
    ✓ Γ → (Γ,m) ⊢ a : σ → addr_plus_ok Γ m j a → (Γ,m) ⊢ addr_plus Γ j a : σ.
  Proof.
    intros ? [o r i τ σ' σc ??????] (?&?&?);
      constructor; simpl in *; split_ands; auto.
    { apply Nat2Z.inj_le. by rewrite Nat2Z.inj_mul, Z2Nat.id by done. }
    apply Nat2Z.inj. rewrite Z2Nat_inj_mod, Z2Nat.id by done.
    rewrite Z.mod_add, <-Z2Nat_inj_mod; auto with f_equal.
    rewrite (Nat2Z.inj_iff _ 0).
    eauto using castable_size_of_ne_0, ref_typed_type_valid.
  Qed.
  Lemma addr_plus_ok_weaken Γ1 Γ2 m1 m2 a σ j :
    ✓ Γ1 → (Γ1,m1) ⊢ a : σ → addr_plus_ok Γ1 m1 j a →
    Γ1 ⊆ Γ2 → (∀ o, index_alive m1 o → index_alive m2 o) →
    addr_plus_ok Γ2 m2 j a.
  Proof.
    unfold addr_plus_ok. intros ?? (?&?&?) ??. erewrite <-addr_size_of_weaken,
      <-(size_of_weaken _ Γ2) by eauto using addr_typed_type_base_valid; eauto.
  Qed.
  Lemma addr_plus_weaken Γ1 Γ2 m1 a σ j :
    ✓ Γ1 → (Γ1,m1) ⊢ a : σ → Γ1 ⊆ Γ2 → addr_plus Γ1 j a = addr_plus Γ2 j a.
  Proof.
    intros ? [o r i τ σ' σc'] ?; simpl. destruct (castable_type_valid Γ1 σ' σc')
      as [| ->]; eauto using ref_typed_type_valid.
    * by erewrite size_of_weaken by eauto using ref_typed_type_valid.
    * by rewrite !size_of_void.
  Qed.
  Lemma addr_type_plus Γ a j : type_of (addr_plus Γ j a) = type_of a.
  Proof. by destruct a. Qed.
  Lemma addr_type_base_plus Γ a j :
    addr_type_base (addr_plus Γ j a) = addr_type_base a.
  Proof. by destruct a. Qed.
  Lemma addr_index_plus Γ a j : addr_index (addr_plus Γ j a) = addr_index a.
  Proof. by destruct a. Qed.
  Lemma addr_plus_0 Γ a : addr_plus Γ 0 a = a.
  Proof. destruct a; simpl. by rewrite Z.mul_0_l, Z.add_0_r, Nat2Z.id. Qed.
  Lemma addr_plus_plus Γ a j1 j2 :
    (0 ≤ addr_byte a + j2 * size_of' Γ a)%Z →
    addr_plus Γ j1 (addr_plus Γ j2 a) = addr_plus Γ (j1 + j2) a.
  Proof.
    intros. destruct a as [o r i σ σc]; do 2 f_equal'.
    by rewrite Z2Nat.id, (Z.add_comm j1), Z.mul_add_distr_r, Z.add_assoc.
  Qed.
  Lemma addr_plus_plus_nat Γ a (j1 j2 : nat) :
    addr_plus Γ j1 (addr_plus Γ j2 a) = addr_plus Γ(j1 + j2)%nat a.
  Proof. rewrite Nat2Z.inj_add. apply addr_plus_plus; auto with zpos. Qed.
  Lemma addr_is_obj_plus Γ a j : addr_is_obj (addr_plus Γ j a) ↔ addr_is_obj a.
  Proof. by destruct a. Qed.
  Lemma addr_ref_base_plus Γ a j :
    addr_ref_base (addr_plus Γ j a) = addr_ref_base a.
  Proof. by destruct a. Qed.
  Lemma addr_minus_alt Γ m a1 a2 σ :
    ✓ Γ → (Γ,m) ⊢ a1 : σ → (Γ,m) ⊢ a2 : σ →
    addr_minus Γ a1 a2 = (addr_offset Γ a1 - addr_offset Γ a2)%Z.
  Proof.
    intros. assert (size_of Γ σ ≠ 0) by eauto using addr_size_of_type_ne_0.
    unfold addr_minus, addr_offset; simplify_type_equality.
    destruct (addr_offset_aligned_alt Γ m a1 σ) as [z1 ->]; auto.
    destruct (addr_offset_aligned_alt Γ m a2 σ) as [z2 ->]; auto.
    rewrite !Z2Nat_inj_div, !Nat2Z.inj_mul, <-Z.mul_sub_distr_r.
    by rewrite !Z.div_mul by lia.
  Qed.
  Lemma addr_minus_ok_typed Γ m a1 a2 σ :
    ✓ Γ → (Γ,m) ⊢ a1 : σ → (Γ,m) ⊢ a2 : σ →
    int_typed (addr_minus Γ a1 a2) sptrT.
  Proof.
    intros HΓ Ha1 Ha2. erewrite addr_minus_alt by eauto.
    destruct (addr_offset_representable Γ m a1 σ HΓ Ha1),
      (addr_offset_representable Γ m a2 σ HΓ Ha2).
    red; change (int_lower sptrT) with (-int_upper sptrT)%Z; lia.
  Qed.
  Lemma addr_minus_ok_weaken m1 m2 a1 a2:
    addr_minus_ok m1 a1 a2 → (∀ o, index_alive m1 o → index_alive m2 o) →
    addr_minus_ok m2 a1 a2.
  Proof. intros [??]; split; eauto. Qed.
  Lemma addr_minus_weaken Γ1 Γ2 mm1 a1 a2 σ1 σ2 :
    ✓ Γ1 → (Γ1,mm1) ⊢ a1 : σ1 →
    Γ1 ⊆ Γ2 → addr_minus Γ1 a1 a2 = addr_minus Γ2 a1 a2.
  Proof.
    intros. unfold addr_minus; simplify_type_equality.
    destruct (addr_typed_type_valid Γ1 mm1 a1 σ1) as [?| ->]; auto.
    * by erewrite (size_of_weaken Γ1 Γ2) by eauto using addr_typed_type_valid.
    * by rewrite !size_of_void.
  Qed.
  Lemma addr_cast_ok_uchar Γ a : addr_cast_ok Γ ucharT a.
  Proof. split. constructor. by rewrite size_of_int, int_size_char. Qed.
  Lemma addr_cast_ok_typed Γ m a σ σc :
    (Γ,m) ⊢ a : σ → addr_cast_ok Γ σc a → (Γ,m) ⊢ addr_cast σc a : σc.
  Proof. intros [] [??]; constructor; naive_solver. Qed.
  Lemma addr_cast_ok_weaken Γ1 Γ2 mm1 a σ σc :
    ✓ Γ1 → (Γ1,mm1) ⊢ a : σ →
    addr_cast_ok Γ1 σc a → Γ1 ⊆ Γ2 → addr_cast_ok Γ2 σc a.
  Proof.
    intros ? [o r i τ σ' σc'] [??] ?; simpl.
    destruct (castable_type_valid Γ1 σ' σc)
      as [| ->]; eauto using ref_typed_type_valid.
    * by erewrite <-size_of_weaken by eauto.
    * by rewrite !size_of_void.
  Qed.
  Lemma addr_type_cast a σc : type_of (addr_cast σc a) = σc.
  Proof. by destruct a. Qed.
  Lemma addr_index_cast a σc : addr_index (addr_cast σc a) = addr_index a.
  Proof. by destruct a. Qed.
  Lemma addr_ref_cast Γ a σc : addr_ref Γ (addr_cast σc a) = addr_ref Γ a.
  Proof. by destruct a. Qed.
  Lemma addr_ref_byte_cast Γ a σc :
    addr_ref_byte Γ (addr_cast σc a) = addr_ref_byte Γ a.
  Proof. by destruct a. Qed.
  Lemma addr_cast_self Γ m a σ : (Γ,m) ⊢ a : σ → addr_cast σ a = a.
  Proof. by destruct 1. Qed.
  Lemma addr_is_obj_cast a σc :
    addr_is_obj (addr_cast σc a) ↔ σc = addr_type_base a.
  Proof. by destruct a. Qed.
  Lemma addr_ref_plus_char_cast Γ m a σ j :
    ✓ Γ → (Γ,m) ⊢ a : σ → addr_is_obj a → j < size_of Γ σ →
    addr_ref Γ (addr_plus Γ j (addr_cast ucharT a)) = addr_ref Γ a.
  Proof.
    destruct 2 as [o r i τ σ σc ?????]; intros ??; simplify_equality'.
    f_equal. rewrite size_of_int, int_size_char; simpl.
    rewrite Z.mul_1_r, Z2Nat.inj_add, !Nat2Z.id by auto with zpos.
    symmetry. apply Nat.div_unique with (i `mod` size_of Γ σ + j); [lia|].
    by rewrite Nat.add_assoc, <-Nat.div_mod
      by eauto using ref_typed_type_valid, size_of_ne_0.
  Qed.
  Lemma addr_ref_byte_plus_char_cast Γ m a σ j :
    ✓ Γ → (Γ,m) ⊢ a : σ → addr_is_obj a → j < size_of Γ σ →
    addr_ref_byte Γ (addr_plus Γ j (addr_cast ucharT a)) = j.
  Proof.
    destruct 2 as [o r i τ σ σc ?????? Hiσ]; intros; simplify_equality'.
    f_equal. rewrite size_of_int, int_size_char; simpl.
    rewrite Z.mul_1_r, Z2Nat.inj_add, !Nat2Z.id by auto with zpos.
    rewrite <-Nat.add_mod_idemp_l
      by eauto using ref_typed_type_valid, size_of_ne_0.
    rewrite Hiσ, Nat.add_0_l. by apply Nat.mod_small.
  Qed.
  Lemma addr_byte_lt_size_char_cast Γ m a σ j :
    ✓ Γ → (Γ,m) ⊢ a : σ → addr_is_obj a → j < size_of Γ σ →
    addr_byte a < size_of Γ (addr_type_base a) * ref_size (addr_ref_base a) →
    addr_byte (addr_plus Γ j (addr_cast ucharT a))
      < size_of Γ (addr_type_base a) * ref_size (addr_ref_base a).
  Proof.
    destruct 2 as [o r i τ σ σc ?????? Hiσ]; intros; simplify_equality'.
    rewrite size_of_int, int_size_char; simpl.
    rewrite Z.mul_1_r, Z2Nat.inj_add, !Nat2Z.id by auto with zpos.
    apply Nat.lt_le_trans with (i + size_of Γ σ); [lia|].
    apply Nat.div_exact in Hiσ; eauto using ref_typed_type_valid, size_of_ne_0.
    rewrite Hiσ, <-Nat.mul_succ_r. apply Nat.mul_le_mono_l, Nat.le_succ_l.
    apply Nat.div_lt_upper_bound;
      eauto using ref_typed_type_valid, size_of_ne_0.
  Qed.
  Lemma addr_elt_typed Γ m a n σ :
    ✓ Γ → (Γ,m) ⊢ a : σ.[n] → addr_strict Γ a → (Γ,m) ⊢ addr_elt Γ a : σ.
  Proof.
    rewrite addr_typed_alt. intros ? (?&?&?&?&?&?&?&Hcast&?) (?&?).
    destruct a as [o r i σ' σc]; inversion Hcast; simplify_equality'.
    assert (✓{Γ} σ ∧ n ≠ 0) as [??]
      by eauto using ref_typed_type_valid, TArray_valid_inv.
    constructor; simplify_equality'; auto.
    * assert (i `div` size_of Γ (σ.[n]) < ref_size r).
      { apply Nat.div_lt_upper_bound;
          eauto using size_of_ne_0, ref_typed_type_valid. }
      apply list_typed_cons; exists (σ.[n]); split;
        [auto using ref_set_offset_typed|constructor; lia].
    * lia.
    * by rewrite Nat.mod_0_l by eauto using size_of_ne_0.
  Qed.
  Lemma addr_elt_weaken Γ1 Γ2 mm1 a σ :
    ✓ Γ1 → (Γ1,mm1) ⊢ a : σ → Γ1 ⊆ Γ2 → addr_elt Γ1 a = addr_elt Γ2 a.
  Proof. intros. unfold addr_elt. by erewrite addr_ref_weaken by eauto. Qed.
  Lemma addr_field_typed Γ m c a j s σs σ :
    ✓ Γ → (Γ,m) ⊢ a : compoundT{c} s → addr_strict Γ a →
    Γ !! s = Some σs → σs !! j = Some σ → (Γ,m) ⊢ addr_field Γ j a : σ.
  Proof.
    rewrite addr_typed_alt. intros ? (?&?&?&?&?&?&?&Hcast&?) (?&?) ??.
    destruct a as [o r i σ' σc]; inversion Hcast; simplify_option_equality.
    constructor; simpl; eauto using env_valid_lookup_lookup.
    * apply list_typed_cons; eexists (compoundT{c} s); split.
      + apply ref_set_offset_typed; auto. apply Nat.div_lt_upper_bound;
          eauto using size_of_ne_0, TCompound_valid.
      + destruct c; econstructor; eauto.
    * by destruct c.
    * lia.
    * by rewrite Nat.mod_0_l
        by eauto using size_of_ne_0, env_valid_lookup_lookup.
  Qed.
  Lemma addr_field_weaken Γ1 Γ2 mm1 c a s i :
    ✓ Γ1 → (Γ1,mm1) ⊢ a : compoundT{c} s → Γ1 ⊆ Γ2 →
    addr_field Γ1 i a = addr_field Γ2 i a.
  Proof.
    intros. unfold addr_field. erewrite !type_of_correct by eauto; simpl.
    assert (is_Some (Γ1 !! s)) as [σs Hσs].
    { by destruct (addr_typed_type_valid Γ1 mm1 a (compoundT{c} s));
        eauto using TCompound_valid_inv. }
    by erewrite Hσs, (lookup_weaken Γ1 Γ2 s σs), addr_ref_weaken by eauto.
  Qed.

  (** ** Disjointness *)
  Lemma addr_disjoint_cases Γ m a1 a2 σ1 σ2 :
    ✓ Γ → (Γ,m) ⊢ a1 : σ1 → frozen a1 → addr_is_obj a1 →
    (Γ,m) ⊢ a2 : σ2 → frozen a2 → addr_is_obj a2 →
    (**i 1.) *) (∀ j1 j2, addr_plus Γ j1 a1 ⊥{Γ} addr_plus Γ j2 a2) ∨
    (**i 2.) *) σ1 ⊆{Γ} σ2 ∨
    (**i 3.) *) σ2 ⊆{Γ} σ1 ∨
    (**i 4.) *) addr_index a1 = addr_index a2 ∧ (∃ s r1' i1 r2' i2 r',
      addr_ref_base a1 = r1' ++ RUnion i1 s true :: r' ∧
      addr_ref_base a2 = r2' ++ RUnion i2 s true :: r' ∧ i1 ≠ i2).
  Proof.
    unfold frozen. intros ? [o1 r1 i1 τ1 σ1' σc1] ??
      [o2 r2 i2 τ2 σ2' σc2] ??; simplify_equality'.
    destruct (decide (o1 = o2)); [simplify_equality|by do 2 left].
    destruct (ref_disjoint_cases Γ τ2 r1 r2 σ1' σ2')
      as [?|[?|[?|(s&r1'&i1'&r2'&i2'&r'&->&->&?)]]]; auto.
    * left; intros j1 j2; right; left; split; simpl; auto.
    * do 3 right; split; [done|]. by eexists s, r1', i1', r2', i2', r'.
  Qed.
  Lemma addr_disjoint_weaken Γ1 Γ2 m1 a1 a2 σ1 σ2 :
    ✓ Γ1 → (Γ1,m1) ⊢ a1 : σ1 → (Γ1,m1) ⊢ a2 : σ2 →
    a1 ⊥{Γ1} a2 → Γ1 ⊆ Γ2 → a1 ⊥{Γ2} a2.
  Proof.
    unfold disjointE, addr_disjoint. intros. by erewrite
      <-!(addr_ref_weaken Γ1 Γ2), <-!(addr_ref_byte_weaken Γ1 Γ2) by eauto.
  Qed.

  (** ** Refinements *)
  Lemma ref_refine_nil_alt r' sz r'' i i' :
    i' = i + sz * ref_offset r' → r'' = ref_base r' →
    ref_refine r' sz [] i r'' i'.
  Proof. intros -> ->. by constructor. Qed.
  Lemma ref_refine_ne_nil_alt r' sz rs r r'' i :
    r'' = rs :: r ++ r' → ref_refine r' sz (rs :: r) i r'' i.
  Proof. intros ->. by constructor. Qed.
  Lemma addr_refine_eq Γ m a1 a2 σ : a1 ⊑{Γ@m} a2 : σ → a1 = a2.
  Proof.
    destruct 1 as [o o' r' r r'' i i'' τ τ' σ σc ??????????? []];
      simplify_type_equality'.
    * by rewrite Nat.mul_0_r, Nat.add_0_r.
    * by rewrite (right_id_L [] (++)).
  Qed.
  Lemma addr_refine_typed_l Γ f m1 m2 a1 a2 σ :
    ✓ Γ → a1 ⊑{Γ,f@m1↦m2} a2 : σ → (Γ,m1) ⊢ a1 : σ.
  Proof.
    intros ?. assert (∀ r τ1 τ2, ✓{Γ} τ1 → Γ ⊢ r : τ1 ↣ τ2 →
      int_typed (size_of Γ τ1) sptrT → int_typed (size_of Γ τ2) sptrT).
    { intros r τ1 τ2 ?? [_ ?]; split.
      { transitivity 0; auto using int_lower_nonpos with zpos. }
      apply Z.le_lt_trans with (size_of Γ τ1); [apply Nat2Z.inj_le|done].
      eauto using size_of_ref'. }
    destruct 1; constructor; eauto using ref_typed_type_valid.
  Qed.
  Lemma addr_refine_typed_r Γ f m1 m2 a1 a2 σ :
    ✓ Γ → a1 ⊑{Γ,f@m1↦m2} a2 : σ → (Γ,m2) ⊢ a2 : σ.
  Proof.
    destruct 2 as [o o' r r' r'' i i'' τ τ' σ σc ??????????? Hr''].
    assert (ref_offset (freeze true <$> r') < ref_size (freeze true <$> r')).
    { intros. eapply ref_typed_size, ref_typed_freeze; eauto. }
    constructor; auto.
    * destruct Hr''; simplify_type_equality'.
      + apply ref_set_offset_typed, ref_typed_freeze; auto with lia.
      + rewrite app_comm_cons, list_typed_app.
        exists τ. by rewrite ref_typed_freeze.
    * destruct Hr''; simplify_equality'; auto.
      by rewrite ref_offset_set_offset by lia.
    * destruct Hr''; simplify_equality'; auto. rewrite ref_size_set_offset.
      transitivity (size_of Γ σ * S (ref_offset (freeze true <$> r'))); [lia|].
      apply Nat.mul_le_mono_l; lia.
    * destruct Hr''; simplify_equality'; auto.
      destruct (castable_divide Γ σ σc) as [z ->]; auto.
      by rewrite <-Nat.mul_assoc, (Nat.mul_comm (size_of _ _)), Nat.mul_assoc,
        Nat.mod_add by eauto using castable_size_of_ne_0, ref_typed_type_valid.
  Qed.
  Lemma addr_refine_type_of_l Γ f m1 m2 a1 a2 σ :
    a1 ⊑{Γ,f@m1↦m2} a2 : σ → type_of a1 = σ.
  Proof. by destruct 1. Qed.
  Lemma addr_refine_type_of_r Γ f m1 m2 a1 a2 σ :
    a1 ⊑{Γ,f@m1↦m2} a2 : σ → type_of a2 = σ.
  Proof. by destruct 1. Qed.
  Lemma addr_refine_frozen Γ f m1 m2 a1 a2 σ :
  a1 ⊑{Γ,f@m1↦m2} a2 : σ → frozen a1 ↔ frozen a2.
  Proof.
    unfold frozen.
    destruct 1 as [o o' r' r r'' i i'' τ τ' σ σc ??????????? []]; simpl.
    * by rewrite ref_set_offset_freeze, ref_freeze_freeze.
    * rewrite fmap_app, ref_freeze_freeze.
      by split; intro; simplify_list_equality'; repeat f_equal.
  Qed.
  Definition addr_refine_id Γ m a σ : (Γ,m) ⊢ a : σ → a ⊑{Γ@m} a : σ.
  Proof.
    destruct 1 as [o r i τ σ σc].
    eexists []; simpl; auto; [by apply list_typed_nil|].
    destruct r as [|rs r]; [apply ref_refine_nil_alt; simpl; auto with lia|].
    apply ref_refine_ne_nil_alt. by rewrite (right_id_L [] (++)).
  Qed.
  Lemma addr_refine_compose Γ f g m1 m2 m3 a1 a2 a3 σ :
    a1 ⊑{Γ,f@m1↦m2} a2 : σ → a2 ⊑{Γ,g@m2↦m3} a3 : σ →
    a1 ⊑{Γ,f ◎ g@m1↦m3} a3 : σ.
  Proof.
    destruct 1 as [o o2 r r2 r3 i i3 τ τ2 σ σc ??????????? Hr3];
      inversion 1 as [? o4 ? r4 r5 ? i5 ? τ3 ????????????? Hr5]; subst.
    exists (r2 ++ r4); auto.
    { by rewrite lookup_mem_inj_compose; simplify_option_equality. }
    { rewrite list_typed_app; eauto. }
    destruct Hr3 as [?|rs r i]; inversion Hr5; subst.
    * destruct r2; simplify_equality'. apply ref_refine_nil_alt; auto with lia.
    * destruct r2; simplify_equality'.
      by apply ref_refine_nil_alt; rewrite ?fmap_cons, ?fmap_app.
    * apply ref_refine_ne_nil_alt. by rewrite fmap_app, (associative_L (++)).
  Qed.
  Lemma addr_refine_weaken Γ Γ' f f' m1 m2 m1' m2' a1 a2 σ :
    ✓ Γ → a1 ⊑{Γ,f@m1↦m2} a2 : σ → Γ ⊆ Γ' → f ⊆ f' →
    (∀ o τ, type_of_index m1 o = Some τ → type_of_index m1' o = Some τ) →
    (∀ o τ, type_of_index m2 o = Some τ → type_of_index m2' o = Some τ) →
    a1 ⊑{Γ',f'@m1'↦m2'} a2 : σ.
  Proof.
    destruct 2 as [o o2 r r2 r3 i i3 τ τ2 σ σc ????????? Hsz];
      intros; econstructor; eauto using type_valid_weaken, ref_typed_weaken.
    * by erewrite <-size_of_weaken by eauto.
    * by erewrite <-size_of_weaken by eauto using ref_typed_type_valid.
    * destruct (castable_type_valid Γ σ σc) as [?| ->];
        eauto using ref_typed_type_valid.
      + by erewrite <-size_of_weaken by eauto.
      + by rewrite size_of_void in Hsz |- *.
    * by erewrite <-size_of_weaken by eauto using ref_typed_type_valid.
  Qed.
  Lemma addr_refine_unique Γ f m1 m2 a1 a2 a3 σ2 σ3 :
    a1 ⊑{Γ,f@m1↦m2} a2 : σ2 → a1 ⊑{Γ,f@m1↦m2} a3 : σ3 → a2 = a3.
  Proof.
    destruct 1 as [?????????????????????? []];
      inversion 1 as [?????????????????????? Hr2]; inversion Hr2;
      simplify_type_equality'; naive_solver.
  Qed.
  Lemma addr_freeze_refine Γ f m1 m2 a1 a2 σ :
    a1 ⊑{Γ,f@m1↦m2} a2 : σ → freeze true a1 ⊑{Γ,f@m1↦m2} freeze true a2 : σ.
  Proof.
    intros Ha. destruct Ha as [o o' r r' r'' i i'' τ τ' σ σc ??????????? Hr''];
      simpl; econstructor; eauto;
      rewrite ?ref_typed_freeze, ?ref_offset_freeze, ?ref_size_freeze; auto.
    destruct Hr'' as [|r'' i'']; simpl.
    * eapply ref_refine_nil_alt; eauto.
      by rewrite <-ref_set_offset_freeze, ref_freeze_freeze.
    * eapply ref_refine_ne_nil_alt; eauto.
      by rewrite fmap_app, ref_freeze_freeze.
  Qed.
  Lemma addr_ref_refine Γ f m1 m2 a1 a2 σ :
    a1 ⊑{Γ,f@m1↦m2} a2 : σ → addr_strict Γ a1 →
    ∃ r, f !! addr_index a1 = Some (addr_index a2, r)
      ∧ addr_ref Γ a2 = addr_ref Γ a1 ++ freeze true <$> r.
  Proof.
    intros [?? r r' r'' i i'' τ τ' σ' ???????????? Hr'']
      [? _]; simplify_equality'.
    exists r'; split; auto. destruct Hr''; simplify_equality'; auto.
    rewrite Nat.mul_comm, Nat.div_add, Nat.div_small, Nat.add_0_l by lia.
    by rewrite ref_set_offset_set_offset, ref_set_offset_offset.
  Qed.
  Lemma addr_ref_byte_refine Γ f m1 m2 a1 a2 σ :
    a1 ⊑{Γ,f@m1↦m2} a2 : σ → addr_strict Γ a1 →
    addr_ref_byte Γ a1 = addr_ref_byte Γ a2.
  Proof.
    intros [?? r r' r'' i i'' τ τ' σ' ???????????? Hr''] [? _];
      simplify_equality'; destruct Hr''; simplify_equality'; auto.
    by rewrite Nat.mul_comm, Nat.mod_add by lia.
  Qed.
  Lemma addr_is_obj_refine Γ f m1 m2 a1 a2 σ :
    a1 ⊑{Γ,f@m1↦m2} a2 : σ → addr_is_obj a1 ↔ addr_is_obj a2.
  Proof. by destruct 1. Qed.
  Lemma addr_disjoint_refine Γ f m1 m2 a1 a2 a3 a4 σ1 σ3 :
    ✓ Γ → mem_inj_injective f → addr_strict Γ a1 → addr_strict Γ a3 →
    a1 ⊑{Γ,f@m1↦m2} a2 : σ1 → a3 ⊑{Γ,f@m1↦m2} a4 : σ3 → a1 ⊥{Γ} a3 → a2 ⊥{Γ} a4.
  Proof.
    intros ??????.
    destruct (addr_ref_refine Γ f m1 m2 a1 a2 σ1) as (r1&Hf1&Hr1); auto.
    destruct (addr_ref_refine Γ f m1 m2 a3 a4 σ3) as (r2&Hf2&Hr2); auto.
    intros [?|[[Hidx ?]|(Hidx&Ha&?&?&?)]].
    * edestruct (mem_inj_injective_ne f (addr_index a1) (addr_index a2))
        as [|[??]]; eauto; [by left|].
      right; left; split; [done|]. rewrite Hr1, Hr2.
      by apply ref_disjoint_app, ref_disjoint_freeze_l, ref_disjoint_freeze_r.
    * rewrite Hidx in Hf1; simplify_option_equality. right; left; split; auto.
      rewrite Hr1, Hr2. by apply ref_disjoint_here_app_1.
    * rewrite Hidx in Hf1; simplify_option_equality. do 2 right; split; [done|].
      by erewrite Hr1, Hr2, !fmap_app, Ha,
        <-!(addr_ref_byte_refine _ _ _ _ a1 a2),
        <-!(addr_ref_byte_refine _ _ _ _ a3 a4),
        <-!(addr_is_obj_refine _ _ _ _ a1 a2),
        <-!(addr_is_obj_refine _ _ _ _ a3 a4) by eauto.
  Qed.
  Lemma addr_disjoint_refine_inv Γ f m1 m2 a1 a2 a3 a4 σ1 σ3 :
    ✓ Γ → addr_strict Γ a1 → addr_strict Γ a3 →
    a1 ⊑{Γ,f@m1↦m2} a2 : σ1 → a3 ⊑{Γ,f@m1↦m2} a4 : σ3 → a2 ⊥{Γ} a4 → a1 ⊥{Γ} a3.
  Proof.
    intros ?????.
    destruct (addr_ref_refine Γ f m1 m2 a1 a2 σ1) as (r1&Hf1&Hr1); auto.
    destruct (addr_ref_refine Γ f m1 m2 a3 a4 σ3) as (r2&Hf2&Hr2); auto.
    destruct (decide (addr_index a1 = addr_index a3)) as [Hidx|]; [|by left].
    intros [?|[[Hidx' ?]|(Hidx'&Ha&?&?&?)]]; [congruence| |].
    * right; left; split; [done|]. rewrite Hidx in Hf1; simplify_equality.
      apply ref_disjoint_here_app_2 with (freeze true <$> r1); congruence.
    * right; right; split; [done|]. rewrite Hidx in Hf1; simplify_equality.
      erewrite !(addr_ref_byte_refine _ _ _ _ a1 a2),
        !(addr_ref_byte_refine _ _ _ _ a3 a4),
        !(addr_is_obj_refine _ _ _ _ a1 a2),
        !(addr_is_obj_refine _ _ _ _ a3 a4) by eauto; split_ands; auto.
      apply (injective (++ freeze true <$> freeze true <$> r1)).
      rewrite <-!fmap_app. congruence.
  Qed.
  Lemma addr_byte_refine_help Γ f m1 m2 a1 a2 σ :
    a1 ⊑{Γ,f@m1↦m2} a2 : σ →
    ∃ i, i + size_of Γ (addr_type_base a1) * ref_size (addr_ref_base a1)
      ≤ size_of Γ (addr_type_base a2) * ref_size (addr_ref_base a2)
    ∧ addr_byte a2 = i + addr_byte a1.
  Proof.
    destruct 1 as [o o' r r' r'' i i'' τ τ' σ' σc ??????????? Hr''].
    destruct Hr'' as [|r'' i'']; simplify_type_equality'; [|by exists 0].
    rewrite ref_size_set_offset.
    exists (size_of Γ σ' * ref_offset (freeze true <$> r')). split; [|lia].
    rewrite <-Nat.mul_add_distr_l, Nat.add_comm. eapply Nat.mul_le_mono_l,
      Nat.le_succ_l, ref_typed_size, ref_typed_freeze; eauto.
  Qed.
  Lemma addr_strict_refine Γ f m1 m2 a1 a2 σ :
    a1 ⊑{Γ,f@m1↦m2} a2 : σ → addr_strict Γ a1 → addr_strict Γ a2.
  Proof.
    intros ? [??].
    destruct (addr_byte_refine_help Γ f m1 m2 a1 a2 σ) as (i&?&?); auto.
    split; [lia|]. by erewrite addr_refine_type_of_r,
      <-(addr_refine_type_of_l _ _ _ _ a1 a2 σ) by eauto.
  Qed.
  Lemma addr_plus_ok_refine Γ f m1 m2 a1 a2 σ j :
    ✓ Γ → m1 ⊑{Γ,f} m2 → a1 ⊑{Γ,f@m1↦m2} a2 : σ →
    addr_plus_ok Γ m1 j a1 → addr_plus_ok Γ m2 j a2.
  Proof.
    unfold addr_plus_ok. intros ?? Ha (?&?&?).
    destruct (addr_byte_refine_help Γ f m1 m2 a1 a2 σ) as (i&?&?); auto.
    destruct Ha; simplify_equality'. split. eauto using mem_refine_alive. lia.
  Qed.
  Lemma addr_plus_refine Γ f m1 m2 a1 a2 σ j :
    ✓ Γ → m1 ⊑{Γ,f} m2 → addr_plus_ok Γ m1 j a1 →
    a1 ⊑{Γ,f@m1↦m2} a2 : σ → addr_plus Γ j a1 ⊑{Γ,f@m1↦m2} addr_plus Γ j a2 : σ.
  Proof.
    intros ?? Ha' Ha. destruct Ha' as (_&?&?), Ha as
      [o o' r r' r'' i i'' τ τ' σ σc ??????????? Hr'']; simplify_equality'.
    econstructor; eauto.
    { apply Nat2Z.inj_le. by rewrite Nat2Z.inj_mul, Z2Nat.id by done. }
    { apply Nat2Z.inj. rewrite Z2Nat_inj_mod, Z2Nat.id by done.
      rewrite Z.mod_add, <-Z2Nat_inj_mod; auto with f_equal.
      rewrite (Nat2Z.inj_iff _ 0).
      eauto using castable_size_of_ne_0, ref_typed_type_valid. }
    destruct Hr'' as [i|r i]; simplify_equality'; [|by constructor].
    apply ref_refine_nil_alt; auto. rewrite ref_offset_freeze.
    rewrite Nat2Z.inj_add, Nat2Z.inj_mul. 
    transitivity (Z.to_nat ((i + j * size_of Γ σc) +
      size_of Γ σ * ref_offset r')); [f_equal; lia |].
    by rewrite Z2Nat.inj_add, Z2Nat.inj_mul, !Nat2Z.id
      by auto using Z.mul_nonneg_nonneg with lia.
  Qed.
  Lemma addr_minus_ok_refine Γ f m1 m2 a1 a2 a3 a4 σ :
    ✓ Γ → m1 ⊑{Γ,f} m2 → a1 ⊑{Γ,f@m1↦m2} a2 : σ → a3 ⊑{Γ,f@m1↦m2} a4 : σ →
    addr_minus_ok m1 a1 a3 → addr_minus_ok m2 a2 a4.
  Proof.
    destruct 3 as [?????????????????????? []],
      1 as [?????????????????????? []]; intros (?&?&Hr);
      simplify_equality'; eauto using mem_refine_alive.
    rewrite !fmap_app, !ref_freeze_freeze by eauto.
    split. eauto using mem_refine_alive. intuition congruence.
  Qed.
  Lemma addr_minus_refine Γ f m1 m2 a1 a2 a3 a4 σ :
    ✓ Γ → addr_minus_ok m1 a1 a3 →
    a1 ⊑{Γ,f@m1↦m2} a2 : σ → a3 ⊑{Γ,f@m1↦m2} a4 : σ →
    addr_minus Γ a1 a3 = addr_minus Γ a2 a4.
  Proof.
    intros ? (?&?&?).
    destruct 1 as [o1 o2 r1 r2 r3 i1 i3 τ1 τ2 σ1 σc ??????????? Hr3],
      1 as [o4 o5 r4 r5 r6 i4 i6 τ4 τ5 σ3 σc4 ??????????? Hr6].
    destruct Hr3, Hr6; simplify_type_equality'; f_equal; lia.
  Qed.
  Lemma addr_cast_ok_refine Γ f m1 m2 a1 a2 σ σc :
    a1 ⊑{Γ,f@m1↦m2} a2 : σ → addr_cast_ok Γ σc a1 → addr_cast_ok Γ σc a2.
  Proof.
    destruct 1 as [o o' r r' r'' i i'' τ τ' σ σc' ??????????? []];
      intros (?&?); simplify_equality'; split_ands; auto.
    destruct (castable_divide Γ σ σc) as [z ->]; auto.
    rewrite ref_offset_freeze.
    destruct (decide (size_of Γ σc = 0)) as [->|?]; [done|].
    by rewrite !(Nat.mul_comm (_ * size_of _ _)), Nat.mul_assoc, Nat.mod_add.
  Qed.
  Lemma addr_cast_refine Γ f m1 m2 a1 a2 σ σc :
    addr_cast_ok Γ σc a1 → a1 ⊑{Γ,f@m1↦m2} a2 : σ →
    addr_cast σc a1 ⊑{Γ,f@m1↦m2} addr_cast σc a2 : σc.
  Proof. intros [??]. destruct 1; simplify_equality'; econstructor; eauto. Qed.
  Lemma addr_elt_refine Γ f m1 m2 a1 a2 σ n :
    ✓ Γ → addr_strict Γ a1 → a1 ⊑{Γ,f@m1↦m2} a2 : σ.[n] →
    addr_elt Γ a1 ⊑{Γ,f@m1↦m2} addr_elt Γ a2 : σ.
  Proof.
    intros ? [? _].
    inversion 1 as [o o' r r' r'' i i'' τ τ' ???????????? Hc Hr''];
      inversion Hc; clear Hc; simplify_equality'.
    assert (✓{Γ} σ ∧ n ≠ 0) as [??]
      by eauto using TArray_valid_inv, ref_typed_type_valid.
    econstructor; eauto.
    * assert (i `div` size_of Γ (σ.[n]) < ref_size r).
      { apply Nat.div_lt_upper_bound;
          eauto using size_of_ne_0, ref_typed_type_valid. }
      apply list_typed_cons; exists (σ.[n]); split;
        [auto using ref_set_offset_typed|constructor; lia].
    * lia.
    * by rewrite Nat.mod_0_l by eauto using size_of_ne_0.
    * destruct Hr'' as [i''|]; simplify_equality'; [|by constructor].
      apply ref_refine_ne_nil_alt.
      by rewrite ref_set_offset_set_offset, (Nat.mul_comm (size_of _ _)),
        Nat.div_add, Nat.div_small, Nat.add_0_l, ref_set_offset_offset by lia.
  Qed.
  Lemma addr_field_refine Γ f m1 m2 c s σs j a1 a2 σ :
    ✓ Γ → addr_strict Γ a1 →
    a1 ⊑{Γ,f@m1↦m2} a2 : compoundT{c} s → Γ !! s = Some σs → σs !! j = Some σ →
    addr_field Γ j a1 ⊑{Γ,f@m1↦m2} addr_field Γ j a2 : σ.
  Proof.
    intros ? [? _].
    inversion 1 as [o o' r r' r'' i i'' τ τ' ???????????? Hc Hr''];
      inversion Hc; clear Hc; intros; simplify_option_equality.
    econstructor; eauto using env_valid_lookup_lookup.
    * apply list_typed_cons; eexists (compoundT{c} s); split.
      + apply ref_set_offset_typed; auto. apply Nat.div_lt_upper_bound;
          eauto using size_of_ne_0, TCompound_valid, ref_typed_type_valid.
      + destruct c; econstructor; eauto.
    * by destruct c.
    * lia.
    * by rewrite Nat.mod_0_l
        by eauto using size_of_ne_0, env_valid_lookup_lookup.
    * destruct Hr'' as [i''|]; simplify_equality'; [|constructor].
      rewrite ref_set_offset_set_offset, (Nat.mul_comm (size_of _ _)),
        Nat.div_add, Nat.div_small, Nat.add_0_l, ref_set_offset_offset by lia.
      destruct c; constructor.
  Qed.
End addresses.
