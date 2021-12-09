(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export references memory_basics.
Require Import pointer_casts.

Local Open Scope ctype_scope.

Record addr (K : iType) : iType := Addr {
  addr_index : index;
  addr_ref_base : ref K;
  addr_byte : nat;
  addr_type_object : type K;
  addr_type_base : type K;
  addr_type : ptr_type K
}.
Add Printing Constructor addr.
Arguments Addr {_} _ _ _ _ _ _.
Arguments addr_index {_} _.
Arguments addr_ref_base {_} _.
Arguments addr_byte {_} _.
Arguments addr_type_object {_} _.
Arguments addr_type_base {_} _.
Arguments addr_type {_} _.

#[global] Instance addr_eq_dec `{EqDecision K}: EqDecision (addr K).
Proof. solve_decision. Defined.

Section address_operations.
  Context `{EqDecision K, Env K}.

  Inductive addr_typed' (Γ : env K) (Δ : memenv K) :
      addr K → ptr_type K → Prop :=
    Addr_typed o r i τ σ σp :
      Δ ⊢ o : τ →
      ✓{Γ} τ →
      Γ ⊢ r : τ ↣ σ →
      ref_offset r = 0 →
      i ≤ size_of Γ σ * ref_size r →
      (ptr_size_of Γ σp | i) →
      σ >*> σp →
      addr_typed' Γ Δ (Addr o r i τ σ σp) σp.
  Global Instance addr_typed :
    Typed (env K * memenv K) (ptr_type K) (addr K) := uncurry addr_typed'.
  Global Instance addr_freeze : Freeze (addr K) := λ β a,
    let 'Addr x r i τ σ σp := a in Addr x (freeze β <$> r) i τ σ σp.

  Global Instance type_of_addr: TypeOf (ptr_type K) (addr K) := addr_type.
  Global Instance addr_type_check:
      TypeCheck (env K * memenv K) (ptr_type K) (addr K) := λ ΓΔ a,
    let (Γ,Δ) := ΓΔ in
    let 'Addr o r i τ σ σp := a in
    guard (Δ ⊢ o : τ);
    guard (✓{Γ} τ);
    guard (Γ ⊢ r : τ ↣ σ);
    guard (σ >*> σp);
    guard (ref_offset r = 0);
    guard (i ≤ size_of Γ σ * ref_size r);
    guard (ptr_size_of Γ σp | i);
    Some σp.

  Definition addr_strict (Γ : env K) (a : addr K) : Prop :=
    addr_byte a < size_of Γ (addr_type_base a) * ref_size (addr_ref_base a).
  Definition addr_is_obj (a : addr K) : Prop :=
    type_of a = TType (addr_type_base a).
  Definition addr_ref (Γ : env K) (a : addr K) : ref K :=
    ref_set_offset (addr_byte a `div` size_of Γ (addr_type_base a))
      (addr_ref_base a).
  Definition addr_ref_byte (Γ : env K) (a : addr K) : nat :=
    addr_byte a `mod` size_of Γ (addr_type_base a).
  Definition addr_object_offset (Γ : env K) (a : addr K) : nat :=
    ref_object_offset Γ (addr_ref_base a) + addr_byte a * char_bits.
  Global Instance addr_disjoint: DisjointE (env K) (addr K) := λ Γ a1 a2,
    (addr_index a1 ≠ addr_index a2) ∨
    (addr_index a1 = addr_index a2 ∧ addr_ref Γ a1 ## addr_ref Γ a2) ∨
    (addr_index a1 = addr_index a2 ∧
      freeze true <$> addr_ref Γ a1 = freeze true <$> addr_ref Γ a2 ∧
      ¬addr_is_obj a1 ∧ ¬addr_is_obj a2 ∧
      addr_ref_byte Γ a1 ≠ addr_ref_byte Γ a2).

  Definition addr_elt (Γ : env K) (rs : ref_seg K) (a : addr K) : addr K :=
    default a $
      σ ← maybe TType (type_of a) ≫= lookupE Γ rs;
      Some (Addr (addr_index a)
        (ref_seg_base rs :: addr_ref Γ a) (size_of Γ σ * ref_seg_offset rs)
        (addr_type_object a) σ (TType σ)).
  Definition addr_top (o : index) (σ : type K) : addr K :=
    Addr o [] 0 σ σ (TType σ).
  Definition addr_top_array (o : index) (σ : type K) (n : Z) : addr K :=
    let n' := Z.to_nat n in Addr o [RArray 0 σ n'] 0 (σ.[n']) σ (TType σ).
  Inductive addr_is_top_array : addr K → Prop :=
    | Addr_is_top_array o σ n σp :
       addr_is_top_array (Addr o [RArray 0 σ n] 0 (σ.[n]) σ σp).
End address_operations.

Typeclasses Opaque addr_strict addr_is_obj addr_disjoint.

Section addresses.
Context `{EqDecision K, EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types Δ : memenv K.
Implicit Types τ σ : type K.
Implicit Types τp σp : ptr_type K.
Implicit Types rs : ref_seg K.
Implicit Types r : ref K.
Implicit Types a : addr K.
Local Hint Immediate ref_typed_type_valid: core.

Arguments addr_type_check _ _ _ _ !a / : assert.
Arguments addr_strict _ _ _ !a / : assert.
Arguments addr_is_obj _ !a / : assert.
Arguments addr_ref _ _ _ !a / : assert.
Arguments addr_ref_byte _ _ _ !a / : assert.
Arguments addr_object_offset _ _ _ !a / : assert.
Arguments addr_elt _ _ _ _ _ !a / : assert.

(** ** Typing and general properties *)
Lemma addr_freeze_freeze β1 β2 a : freeze β1 (freeze β2 a) = freeze β1 a.
Proof. destruct a; f_equal'; auto using ref_freeze_freeze. Qed.
Lemma addr_typed_alt Γ Δ a σp :
  (Γ,Δ) ⊢ a : σp ↔
    Δ ⊢ addr_index a: addr_type_object a ∧
    ✓{Γ} (addr_type_object a) ∧
    Γ ⊢ addr_ref_base a : addr_type_object a ↣ addr_type_base a ∧
    ref_offset (addr_ref_base a) = 0 ∧
    addr_byte a ≤ size_of Γ (addr_type_base a) * ref_size (addr_ref_base a) ∧
    (ptr_size_of Γ σp | addr_byte a) ∧
    addr_type_base a >*> σp ∧
    type_of a = σp.
Proof.
  split; [destruct 1; naive_solver|intros (?&?&?&?&?&?&?&?)].
  by destruct a; simplify_equality; constructor.
Qed.
Lemma addr_typed_index Γ Δ a σp :
  (Γ,Δ) ⊢ a : σp → Δ ⊢ addr_index a : addr_type_object a.
Proof. by destruct 1. Qed.
Lemma addr_typed_offset Γ Δ a σp :
  (Γ,Δ) ⊢ a : σp → ref_offset (addr_ref_base a) = 0.
Proof. by destruct 1. Qed.
Lemma addr_typed_type_object_valid Γ Δ a σp :
  (Γ,Δ) ⊢ a : σp → ✓{Γ} (addr_type_object a).
Proof. by destruct 1. Qed.
Lemma addr_typed_ref_base_typed Γ Δ a σp :
  (Γ,Δ) ⊢ a : σp → Γ ⊢ addr_ref_base a : addr_type_object a ↣ addr_type_base a.
Proof. by destruct 1. Qed.
Lemma addr_typed_type_base_valid Γ Δ a σp :
  ✓ Γ → (Γ,Δ) ⊢ a : σp → ✓{Γ} (addr_type_base a).
Proof.
  eauto using ref_typed_type_valid,
    addr_typed_ref_base_typed, addr_typed_type_object_valid.
Qed.
Lemma addr_typed_ref_typed Γ Δ a σp :
  ✓ Γ → (Γ,Δ) ⊢ a : σp → addr_strict Γ a →
  Γ ⊢ addr_ref Γ a : addr_type_object a ↣ addr_type_base a.
Proof.
  intros. apply ref_set_offset_typed; eauto using addr_typed_ref_base_typed.
  apply Nat.div_lt_upper_bound;
    eauto using size_of_ne_0, addr_typed_type_base_valid.
Qed.
Lemma addr_typed_cast Γ Δ a σp : (Γ,Δ) ⊢ a : σp → addr_type_base a >*> σp.
Proof. by destruct 1. Qed.
Lemma addr_typed_type_valid Γ Δ a σ : ✓ Γ → (Γ,Δ) ⊢ a : TType σ → ✓{Γ} σ.
Proof. inversion 2; eauto using castable_type_valid. Qed.
Lemma addr_typed_ptr_type_valid Γ Δ a σp : ✓ Γ → (Γ,Δ) ⊢ a : σp → ✓{Γ} σp.
Proof. destruct 2; eauto using castable_ptr_type_valid. Qed.
Lemma addr_size_of_ne_0 Γ Δ a σp: ✓ Γ → (Γ,Δ) ⊢ a : σp → ptr_size_of Γ σp ≠ 0.
Proof. destruct σp; eauto using size_of_ne_0, addr_typed_type_valid. Qed.
#[global] Instance: TypeOfSpec (env K * memenv K) (ptr_type K) (addr K).
Proof. by intros [??]; destruct 1. Qed.
#[global] Instance:
  TypeCheckSpec (env K * memenv K) (ptr_type K) (addr K) (λ _, True).
Proof.
  intros [Γ Δ] a σ _. split.
  * destruct a; intros; simplify_option_eq; constructor; auto.
  * by destruct 1; simplify_option_eq.
Qed.
Lemma addr_size_of_weaken Γ1 Γ2 Δ a σp :
  ✓ Γ1 → (Γ1,Δ) ⊢ a : σp → Γ1 ⊆ Γ2 → ptr_size_of Γ1 σp = ptr_size_of Γ2 σp.
Proof. destruct σp; eauto using size_of_weaken, addr_typed_type_valid. Qed.
Lemma addr_typed_weaken Γ1 Γ2 Δ1 Δ2 a σp :
  ✓ Γ1 → (Γ1,Δ1) ⊢ a : σp → Γ1 ⊆ Γ2 → Δ1 ⇒ₘ Δ2 → (Γ2,Δ2) ⊢ a : σp.
Proof.
  destruct 2 as [o r i τ σ σp]; intros ? [??].
  constructor; simpl; split_and ?;
    eauto using type_valid_weaken, ref_typed_weaken.
  * by erewrite <-size_of_weaken by eauto.
  * by erewrite <-addr_size_of_weaken by (eauto; econstructor; eauto).
Qed.
Lemma addr_dead_weaken Γ Δ1 Δ2 a σp :
  (Γ,Δ1) ⊢ a : σp → index_alive Δ2 (addr_index a) → Δ1 ⇒ₘ Δ2 →
  index_alive Δ1 (addr_index a).
Proof. intros [] ? []; naive_solver. Qed.
Lemma addr_type_object_eq Γ Δ a1 a2 σp1 σp2 :
  (Γ,Δ) ⊢ a1 : σp1 → (Γ,Δ) ⊢ a2 : σp2 → addr_index a1 = addr_index a2 →
  addr_type_object a1 = addr_type_object a2.
Proof. by destruct 1, 1; intros; simplify_type_equality'. Qed.
#[global] Instance addr_strict_dec Γ a : Decision (addr_strict Γ a).
Proof. unfold addr_strict; apply _. Defined.
#[global] Instance addr_is_obj_dec a : Decision (addr_is_obj a).
Proof. unfold addr_is_obj; apply _. Defined.
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
    addr_ref_base_freeze, ref_size_freeze.
Qed.
Lemma addr_strict_freeze_2 Γ β a : addr_strict Γ a → addr_strict Γ (freeze β a).
Proof. by rewrite addr_strict_freeze. Qed.
Lemma addr_ref_byte_freeze Γ β a :
  addr_ref_byte Γ (freeze β a) = addr_ref_byte Γ a.
Proof.
  unfold addr_ref_byte. by rewrite addr_byte_freeze, addr_type_base_freeze.
Qed.
Lemma addr_typed_freeze Γ Δ β a σp :
  (Γ,Δ) ⊢ freeze β a : σp ↔ (Γ,Δ) ⊢ a : σp.
Proof.
  rewrite !addr_typed_alt; destruct a; simpl. by rewrite ref_offset_freeze,
    ref_size_freeze; setoid_rewrite ref_typed_freeze.
Qed.
Lemma addr_is_obj_ref_byte Γ Δ a σp :
  ✓ Γ → (Γ,Δ) ⊢ a : σp → addr_is_obj a → addr_ref_byte Γ a = 0.
Proof.
  destruct 2; intros; simplify_equality';
    apply Nat.mod_divide; eauto using size_of_ne_0.
Qed.
Lemma addr_is_obj_type Γ Δ a σ :
  (Γ,Δ) ⊢ a : TType σ → addr_is_obj a → σ = addr_type_base a.
Proof. inversion 1; naive_solver. Qed.
Lemma addr_not_is_obj_type Γ Δ a σ :
  (Γ,Δ) ⊢ a : TType σ → ¬addr_is_obj a → σ = ucharT.
Proof.
  inversion 1;
    match goal with H : _ >*> _ |- _ => inversion H end; naive_solver.
Qed.
Lemma addr_byte_range Γ Δ a σ :
  ✓ Γ → (Γ,Δ) ⊢ a : TType σ → addr_strict Γ a →
  addr_ref_byte Γ a + size_of Γ σ ≤ size_of Γ (addr_type_base a).
Proof.
  intros. destruct (decide (addr_is_obj a)).
  { by erewrite <-addr_is_obj_type, addr_is_obj_ref_byte by eauto. }
  erewrite (addr_not_is_obj_type _ _ _ σ), size_of_char by eauto.
  rewrite Nat.add_1_r, Nat.le_succ_l.
  apply Nat.mod_bound_pos; auto with lia.
  eapply size_of_pos, addr_typed_type_base_valid; eauto.
Qed.
Lemma addr_bit_range Γ Δ a σ :
  ✓ Γ → (Γ,Δ) ⊢ a : TType σ → addr_strict Γ a →
  addr_ref_byte Γ a * char_bits + bit_size_of Γ σ
    ≤ bit_size_of Γ (addr_type_base a).
Proof.
  intros. unfold bit_size_of. rewrite <-Nat.mul_add_distr_r,
    <-Nat.mul_le_mono_pos_r by auto using char_bits_pos.
  eauto using addr_byte_range.
Qed.
Lemma addr_strict_weaken Γ1 Γ2 m1 a σp :
  ✓ Γ1 → (Γ1,m1) ⊢ a : σp → addr_strict Γ1 a → Γ1 ⊆ Γ2 → addr_strict Γ2 a.
Proof.
  unfold addr_strict. intros ????.
  by erewrite <-size_of_weaken by eauto using addr_typed_type_base_valid.
Qed.
Lemma addr_ref_weaken Γ1 Γ2 m1 a σp :
  ✓ Γ1 → (Γ1,m1) ⊢ a : σp → Γ1 ⊆ Γ2 → addr_ref Γ1 a = addr_ref Γ2 a.
Proof.
  intros ? [] ?; simpl.
  by erewrite size_of_weaken by eauto using ref_typed_type_valid.
Qed.
Lemma addr_ref_byte_weaken Γ1 Γ2 m1 a σp :
  ✓ Γ1 → (Γ1,m1) ⊢ a : σp → Γ1 ⊆ Γ2 → addr_ref_byte Γ1 a = addr_ref_byte Γ2 a.
Proof.
  intros ? [] ?; simpl.
  by erewrite size_of_weaken by eauto using ref_typed_type_valid.
Qed.
Lemma addr_object_offset_weaken Γ1 Γ2 Δ a σp :
  ✓ Γ1 → (Γ1,Δ) ⊢ a : σp → Γ1 ⊆ Γ2 →
  addr_object_offset Γ1 a = addr_object_offset Γ2 a.
Proof.
  intros. unfold addr_object_offset; eauto using ref_object_offset_weaken,
    addr_typed_ref_base_typed, addr_typed_type_object_valid.
Qed.
Lemma addr_object_offset_alt Γ Δ a σp :
  ✓ Γ → (Γ,Δ) ⊢ a : σp → addr_strict Γ a → addr_object_offset Γ a
  = ref_object_offset Γ (addr_ref Γ a) + addr_ref_byte Γ a * char_bits.
Proof.
  intros ? [o r i τ σ' σp' Hor] ?; simpl in *.
  erewrite ref_object_offset_set_offset_0
    by eauto using Nat.div_lt_upper_bound, size_of_ne_0, ref_typed_type_valid.
  rewrite (Nat.div_mod i (size_of Γ σ')) at 1
    by eauto using size_of_ne_0,ref_typed_type_valid; unfold bit_size_of; lia.
Qed.
Lemma align_of_addr_object_offset Γ Δ a σ :
  ✓ Γ → (Γ,Δ) ⊢ a : TType σ → (bit_align_of Γ σ | addr_object_offset Γ a).
Proof.
  inversion_clear 2; simplify_equality'; apply Nat.divide_add_r;
    eauto using Nat.mul_divide_mono_r, Nat.divide_trans,
    bit_align_of_castable, align_of_divide, castable_type_valid,
    size_of_ne_0, bit_align_of_ref_object_offset.
Qed.
Lemma addr_object_offset_bit_size Γ Δ a σp :
  ✓ Γ → (Γ,Δ) ⊢ a : σp → addr_strict Γ a →
  addr_object_offset Γ a + ptr_bit_size_of Γ σp
  ≤ bit_size_of Γ (addr_type_object a).
Proof.
  destruct 2 as [o r i τ σ σp ??? Hoff _ Hi Hcast];
    intros Ha; simplify_equality'.
  eapply Nat.le_trans; [|eapply ref_object_offset_size; eauto].
  rewrite <-Nat.add_assoc, <-Nat.add_le_mono_l, Hoff, Nat.sub_0_r.
  unfold bit_size_of; rewrite ptr_bit_size_of_alt.
  rewrite Nat.mul_assoc, <-Nat.mul_add_distr_r.
  rewrite <-Nat.mul_le_mono_pos_r by auto using char_bits_pos.
  destruct Hi as [z ->]; inversion Hcast; simplify_equality'.
  { rewrite Nat.mul_comm; lia. }
  { rewrite size_of_char in Ha |- *; rewrite Nat.mul_comm; lia. }
  rewrite <-Nat.mul_succ_l, <-Nat.mul_le_mono_pos_r
    by eauto using size_of_pos, ref_typed_type_valid.
  rewrite <-Nat.mul_comm, <-Nat.mul_lt_mono_pos_l in Ha
    by eauto using size_of_pos, ref_typed_type_valid; lia.
Qed.
Lemma addr_elt_typed Γ Δ a rs σ σ' :
  ✓ Γ → (Γ,Δ) ⊢ a : TType σ → addr_strict Γ a → Γ ⊢ rs : σ ↣ σ' →
  (Γ,Δ) ⊢ addr_elt Γ rs a : TType σ'.
Proof.
  rewrite addr_typed_alt. intros ? (?&?&?&?&?&?&Hcast&?) ? Hrs.
  destruct a as [o r' i τ σ'' σp]; simplify_equality'.
  inversion Hcast; simplify_equality'; try solve [inversion Hrs].
  assert (ref_seg_offset rs < ref_seg_size rs)
    by eauto using ref_seg_typed_size.
  erewrite path_type_check_complete by eauto; constructor; simpl; auto.
  * apply ref_typed_cons; exists σ; split.
    + apply ref_set_offset_typed; auto.
      apply Nat.div_lt_upper_bound;
        eauto using size_of_ne_0, ref_typed_type_valid.
    + apply ref_seg_set_offset_typed; auto with lia.
  * by rewrite ref_seg_offset_set_offset by lia.
  * rewrite ref_seg_size_set_offset. apply Nat.mul_le_mono_l; lia.
  * by apply Nat.divide_factor_l.
  * constructor.
Qed.
Lemma addr_elt_strict Γ Δ a rs σ σ' :
  ✓ Γ → (Γ,Δ) ⊢ a : TType σ → Γ ⊢ rs : σ ↣ σ' → addr_strict Γ (addr_elt Γ rs a).
Proof.
  rewrite addr_typed_alt. intros ? (?&?&?&?&?&?&Hcast&?) Hrs.
  destruct a as [o r i τ σ'' σp]; simplify_equality'.
  inversion Hcast; simplify_equality'; try solve [inversion Hrs].
  erewrite path_type_check_complete by eauto; simpl.
  rewrite ref_seg_size_set_offset, <-Nat.mul_lt_mono_pos_l
    by eauto using size_of_pos, ref_typed_type_valid, ref_seg_typed_type_valid;
    eauto using ref_seg_typed_size.
Qed.
Lemma addr_elt_is_obj Γ Δ a rs σ σ' :
  (Γ,Δ) ⊢ a : TType σ → Γ ⊢ rs : σ ↣ σ' → addr_is_obj (addr_elt Γ rs a).
Proof.
  rewrite addr_typed_alt. intros (?&?&?&?&?&?&Hcast&?) Hrs.
  destruct a as [o r' i τ σ'' σp]; simplify_equality'.
  by erewrite path_type_check_complete by eauto.
Qed.
Lemma addr_elt_weaken Γ1 Γ2 Δ1 a rs σ σ' :
  ✓ Γ1 → (Γ1,Δ1) ⊢ a : TType σ → Γ1 ⊢ rs : σ ↣ σ' → Γ1 ⊆ Γ2 →
  addr_elt Γ1 rs a = addr_elt Γ2 rs a.
Proof.
  intros. unfold addr_elt; simplify_type_equality'.
  erewrite !path_type_check_complete by eauto using ref_seg_typed_weaken; simpl.
  by erewrite addr_ref_weaken, size_of_weaken
    by eauto using addr_typed_type_valid, ref_seg_typed_type_valid.
Qed.
Lemma addr_ref_byte_is_obj_parent Γ Δ rs a σ σ' :
  ✓ Γ → (Γ,Δ) ⊢ a : TType σ → Γ ⊢ rs : σ ↣ σ' → addr_is_obj a.
Proof.
  rewrite addr_typed_alt. intros ? (?&?&?&?&?&?&Hcast&?) Hrs.
  destruct a as [o r i τ σ'' σp]; simplify_equality'.
  by inversion Hcast; simplify_equality'; try solve [inversion Hrs].
Qed.
Lemma addr_ref_byte_is_obj Γ Δ rs a σ σ' :
  ✓ Γ → (Γ,Δ) ⊢ a : TType σ → Γ ⊢ rs : σ ↣ σ' → addr_is_obj (addr_elt Γ rs a).
Proof.
  unfold addr_elt; intros; simplify_type_equality'.
  by erewrite !path_type_check_complete by eauto.
Qed.
Lemma addr_index_elt Γ rs a : addr_index (addr_elt Γ rs a) = addr_index a.
Proof. by destruct a; simpl; destruct (_ ≫= lookupE _ _). Qed.
Lemma addr_ref_elt Γ Δ rs a σ σ' :
  ✓ Γ → (Γ,Δ) ⊢ a : TType σ → Γ ⊢ rs : σ ↣ σ' → 
  addr_ref Γ (addr_elt Γ rs a) = rs :: addr_ref Γ a.
Proof.
  unfold addr_elt; intros; simplify_type_equality'.
  erewrite !path_type_check_complete by eauto; f_equal'.
  rewrite Nat.mul_comm, Nat.div_mul by eauto using size_of_ne_0,
    addr_typed_type_valid, ref_seg_typed_type_valid.
  by destruct rs.
Qed.
Lemma addr_ref_byte_elt Γ Δ rs a σ σ' :
  ✓ Γ → (Γ,Δ) ⊢ a : TType σ → addr_strict Γ a → Γ ⊢ rs : σ ↣ σ' →
  addr_ref_byte Γ (addr_elt Γ rs a) = 0.
Proof.
  eauto using addr_is_obj_ref_byte, addr_ref_byte_is_obj, addr_elt_typed.
Qed.
Lemma addr_top_typed Γ Δ o τ :
  ✓ Γ → Δ ⊢ o : τ → ✓{Γ} τ → (Γ,Δ) ⊢ addr_top o τ : TType τ.
Proof.
  constructor; simpl; rewrite ?ref_typed_nil;
    eauto using Nat.divide_0_r, castable_TType with lia.
Qed.
Lemma addr_top_strict Γ o τ : ✓ Γ → ✓{Γ} τ → addr_strict Γ (addr_top o τ).
Proof.
  unfold addr_strict, addr_top; simpl. rewrite Nat.mul_1_r.
  eauto using size_of_pos.
Qed.
Lemma addr_top_is_obj o τ : addr_is_obj (addr_top o τ).
Proof. done. Qed.
Lemma addr_top_array_alt Γ o τ n :
  Z.to_nat n ≠ 0 → let n' := Z.to_nat n in
  addr_top_array o τ n = addr_elt Γ (RArray 0 τ n') (addr_top o (τ.[n'])).
Proof.
  unfold addr_elt, addr_top_array; simplify_option_eq;
    auto with f_equal lia.
Qed.
Lemma addr_top_array_typed Γ Δ o τ (n : Z) :
  ✓ Γ → Δ ⊢ o : τ.[Z.to_nat n] → ✓{Γ} τ → Z.to_nat n ≠ 0 →
  (Γ,Δ) ⊢ addr_top_array o τ n : TType τ.
Proof.
  intros. rewrite (addr_top_array_alt Γ) by done.
  assert (0 ≤ n)%Z by (by destruct n).
  eapply addr_elt_typed; eauto using addr_top_strict,
    addr_top_typed, TArray_valid; constructor; lia.
Qed.
Lemma addr_top_array_strict Γ o τ n :
  ✓ Γ → ✓{Γ} τ → Z.to_nat n ≠ 0 → addr_strict Γ (addr_top_array o τ n).
Proof.
  intros. apply Nat.mul_pos_pos; simpl; eauto using size_of_pos with lia.
Qed.
Lemma addr_is_top_array_alt Γ Δ a σp :
  ✓ Γ → (Γ,Δ) ⊢ a : σp →
  addr_is_top_array a ↔ ∃ τ n, addr_strict Γ a ∧
    addr_ref Γ a = [RArray 0 τ n] ∧ addr_ref_byte Γ a = 0.
Proof.
  rewrite addr_typed_alt; intros ? (_&?&Hr&?&?&_); split.
  * destruct 1 as [o τ' n σp']; simplify_equality'; exists τ', n.
    assert (✓{Γ} τ' ∧ n ≠ 0) as [??] by auto using TArray_valid_inv.
    rewrite Nat.div_0_l, Nat.mod_0_l by eauto using size_of_ne_0.
    split_and ?; auto using Nat.mul_pos_pos, size_of_pos with lia.
  * intros (?&n&?&?&Hi); destruct a as [o [|[] r] i τ' σ σp']; simplify_equality'.
    rewrite ref_typed_singleton in Hr; inversion Hr; simplify_equality'.
    rewrite <-(Nat.mod_small i (size_of Γ σ)), Hi by
     (apply Nat.div_small_iff; eauto using size_of_ne_0, TArray_valid_inv_type).
    constructor.
Qed.
#[global] Instance addr_is_top_array_dec a : Decision (addr_is_top_array a).
Proof.
 refine
  match a with
  | Addr o [RArray 0 σ1 n1] 0 (σ2.[n2]) σ3 σ4 =>
     cast_if_and3 (decide (n1 = n2)) (decide (σ1 = σ2)) (decide (σ2 = σ3))
  | _ => right _
  end; abstract first [by inversion 1 | subst; constructor].
Defined.

(** ** Disjointness *)
#[global] Instance addr_disjoint_dec Γ a1 a2 : Decision (a1 ##{Γ} a2).
Proof. unfold disjointE, addr_disjoint; apply _. Defined.
Lemma addr_disjoint_weaken Γ1 Γ2 m1 a1 a2 σp1 σp2 :
  ✓ Γ1 → (Γ1,m1) ⊢ a1 : σp1 → (Γ1,m1) ⊢ a2 : σp2 →
  a1 ##{Γ1} a2 → Γ1 ⊆ Γ2 → a1 ##{Γ2} a2.
Proof.
  unfold disjointE, addr_disjoint. intros. by erewrite
    <-!(addr_ref_weaken Γ1 Γ2), <-!(addr_ref_byte_weaken Γ1 Γ2) by eauto.
Qed.
Lemma addr_top_disjoint Γ Δ o1 o2 τ1 τ2 :
  Δ ⊢ o1 : τ1 → Δ ⊢ o2 : τ2 → 
  addr_top o1 τ1 = addr_top o2 τ2 ∨ addr_top o1 τ1 ##{Γ} addr_top o2 τ2.
Proof.
  intros. destruct (decide (o1 = o2)); simplify_type_equality; auto.
  by right; left.
Qed.
Lemma addr_disjoint_object_offset Γ Δ a1 a2 σ1 σ2 :
  ✓ Γ → (Γ,Δ) ⊢ a1 : TType σ1 → addr_strict Γ a1 →
  (Γ,Δ) ⊢ a2 : TType σ2 → addr_strict Γ a2 → a1 ##{Γ} a2 →
  (**i 1.) *) addr_index a1 ≠ addr_index a2 ∨
  (**i 2.) *)
    addr_object_offset Γ a1 + bit_size_of Γ σ1 ≤ addr_object_offset Γ a2 ∨
  (**i 3.) *)
    addr_object_offset Γ a2 + bit_size_of Γ σ2 ≤ addr_object_offset Γ a1.
Proof.
  intros ?????. erewrite !addr_object_offset_alt by eauto.
  intros [?|[[??]|(?&Hr&?&?&?)]]; auto.
  { destruct (ref_disjoint_object_offset Γ (addr_type_object a1)
      (addr_ref Γ a1) (addr_ref Γ a2) (addr_type_base a1) (addr_type_base a2));
      eauto using addr_typed_ref_typed;
      erewrite ?(addr_type_object_eq _ _ a1 a2) by eauto;
      eauto using addr_typed_ref_typed.
    * feed pose proof (addr_bit_range Γ Δ a1 σ1); auto. right; left; lia.
    * feed pose proof (addr_bit_range Γ Δ a2 σ2); auto. do 2 right; lia. }
  erewrite (addr_not_is_obj_type _ _ _ σ1), (addr_not_is_obj_type _ _ _ σ2),
    <-(ref_object_offset_freeze Γ true (addr_ref Γ a1)), Hr,
    ref_object_offset_freeze, !bit_size_of_char by eauto.
  destruct (decide (addr_ref_byte Γ a1 < addr_ref_byte Γ a2)).
  * right; left. rewrite <-Nat.add_assoc, <-Nat.mul_succ_l.
    apply Nat.add_le_mono_l, Nat.mul_le_mono_nonneg_r; lia.
  * do 2 right. rewrite <-Nat.add_assoc, <-Nat.mul_succ_l.
    apply Nat.add_le_mono_l, Nat.mul_le_mono_nonneg_r; lia.
Qed.
End addresses.