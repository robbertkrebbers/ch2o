(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export references memory_basics.
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
  Context `{Env Ti}.

  Inductive addr_typed' (Γ : env Ti) (Γm : memenv Ti) : addr Ti → type Ti → Prop :=
    Addr_typed o r i τ σ σc :
      Γm ⊢ o : τ →
      ✓{Γ} τ →
      int_typed (size_of Γ τ) sptrT →
      Γ ⊢ r : τ ↣ σ →
      ref_offset r = 0 →
      i ≤ size_of Γ σ * ref_size r →
      i `mod` size_of Γ σc = 0 →
      σ >*> σc →
      addr_typed' Γ Γm (Addr o r i τ σ σc) σc.
  Global Instance addr_typed :
    Typed (env Ti * memenv Ti) (type Ti) (addr Ti) := curry addr_typed'.
  Global Instance addr_freeze : Freeze (addr Ti) := λ β a,
    let 'Addr x r i τ σ σc := a in Addr x (freeze β <$> r) i τ σ σc.

  Global Instance type_of_addr: TypeOf (type Ti) (addr Ti) := addr_type.
  Global Instance addr_type_check:
      TypeCheck (env Ti * memenv Ti) (type Ti) (addr Ti) := λ ΓΓm a,
    let (Γ,Γm) := ΓΓm in
    let 'Addr o r i τ σ σc := a in
    guard (Γm ⊢ o : τ);
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
    addr_byte a < size_of Γ (addr_type_base a) * ref_size (addr_ref_base a).
  Global Arguments addr_strict _ !_ /.
  Definition addr_is_obj (a : addr Ti) : Prop :=
    type_of a = addr_type_base a.
  Global Arguments addr_is_obj !_ /.
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
  Definition addr_top_array (o : index) (σ : type Ti) (n : Z) : addr Ti :=
    let n' := Z.to_nat n in Addr o [RArray 0 σ n'] 0 (σ.[n']) σ σ.
  Inductive addr_is_top_array : addr Ti → Prop :=
    | Addr_is_top_array o σ n σc :
       addr_is_top_array (Addr o [RArray 0 σ n] 0 (σ.[n]) σ σc).
End address_operations.

Typeclasses Opaque addr_strict addr_is_obj addr_disjoint.

Section addresses.
Context `{EnvSpec Ti}.
Implicit Types Γ : env Ti.
Implicit Types Γm : memenv Ti.
Implicit Types τ σ : type Ti.
Implicit Types r : ref Ti.
Implicit Types a : addr Ti.

(** ** Typing and general properties *)
Lemma addr_freeze_freeze β1 β2 a : freeze β1 (freeze β2 a) = freeze β1 a.
Proof. destruct a; f_equal'; auto using ref_freeze_freeze. Qed.
Lemma addr_typed_alt Γ Γm a σ :
  (Γ,Γm) ⊢ a : σ ↔
    Γm ⊢ addr_index a: addr_type_object a ∧
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
Lemma addr_typed_index Γ Γm a σ :
  (Γ,Γm) ⊢ a : σ → Γm ⊢ addr_index a : addr_type_object a.
Proof. by destruct 1. Qed.
Lemma addr_typed_offset Γ Γm a σ :
  (Γ,Γm) ⊢ a : σ → ref_offset (addr_ref_base a) = 0.
Proof. by destruct 1. Qed.
Lemma addr_typed_type_object_valid Γ Γm a σ :
  (Γ,Γm) ⊢ a : σ → ✓{Γ} (addr_type_object a).
Proof. by destruct 1. Qed.
Lemma addr_typed_ref_base_typed Γ Γm a σ :
  (Γ,Γm) ⊢ a : σ → Γ ⊢ addr_ref_base a : addr_type_object a ↣ addr_type_base a.
Proof. by destruct 1. Qed.
Lemma addr_typed_type_base_valid Γ Γm a σ :
  ✓ Γ → (Γ,Γm) ⊢ a : σ → ✓{Γ} (addr_type_base a).
Proof.
  eauto using ref_typed_type_valid,
    addr_typed_ref_base_typed, addr_typed_type_object_valid.
Qed.
Lemma addr_typed_ref_typed Γ Γm a σ :
  ✓ Γ → (Γ,Γm) ⊢ a : σ → addr_strict Γ a →
  Γ ⊢ addr_ref Γ a : addr_type_object a ↣ addr_type_base a.
Proof.
  intros. apply ref_set_offset_typed; eauto using addr_typed_ref_base_typed.
  apply Nat.div_lt_upper_bound;
    eauto using size_of_ne_0, addr_typed_type_base_valid.
Qed.
Lemma addr_typed_cast Γ Γm a σ : (Γ,Γm) ⊢ a : σ → addr_type_base a >*> σ.
Proof. by destruct 1. Qed.
Lemma addr_typed_type_valid Γ Γm a σ : ✓ Γ → (Γ,Γm) ⊢ a : σ → ✓{Γ} σ.
Proof. destruct 2; eauto using castable_type_valid, ref_typed_type_valid. Qed.
Global Instance: TypeOfSpec (env Ti * memenv Ti) (type Ti) (addr Ti).
Proof. by intros [??]; destruct 1. Qed.
Global Instance:
  TypeCheckSpec (env Ti * memenv Ti) (type Ti) (addr Ti) (λ _, True).
Proof.
  intros [Γ Γm] a σ _. split.
  * destruct a; intros; simplify_option_equality; constructor; auto.
  * by destruct 1; simplify_option_equality.
Qed.
Lemma addr_typed_weaken Γ1 Γ2 Γm1 Γm2 a σ :
  ✓ Γ1 → (Γ1,Γm1) ⊢ a : σ → Γ1 ⊆ Γ2 → Γm1 ⇒ₘ Γm2 → (Γ2,Γm2) ⊢ a : σ.
Proof.
  intros ? [o r i τ σ' σc'] ? [??]. constructor; simpl; split_ands;
    eauto using type_valid_weaken, ref_typed_weaken.
  { by erewrite <-size_of_weaken by eauto. }
  { by erewrite <-size_of_weaken by eauto using ref_typed_type_valid. }
  by erewrite <-size_of_weaken
    by eauto using castable_type_valid, ref_typed_type_valid.
Qed.
Lemma addr_dead_weaken Γ Γm1 Γm2 a σ :
  (Γ,Γm1) ⊢ a : σ → index_alive Γm2 (addr_index a) → Γm1 ⇒ₘ Γm2 →
  index_alive Γm1 (addr_index a).
Proof. intros [] ? []; naive_solver. Qed.
Lemma addr_type_object_eq Γ Γm a1 a2 σ1 σ2 :
  (Γ,Γm) ⊢ a1 : σ1 → (Γ,Γm) ⊢ a2 : σ2 → addr_index a1 = addr_index a2 →
  addr_type_object a1 = addr_type_object a2.
Proof. by destruct 1, 1; intros; simplify_type_equality'. Qed.
Global Instance addr_strict_dec Γ a : Decision (addr_strict Γ a).
Proof. unfold addr_strict; apply _. Defined.
Global Instance addr_is_obj_dec a : Decision (addr_is_obj a).
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
Lemma addr_typed_freeze Γ Γm β a σ : (Γ,Γm) ⊢ freeze β a : σ ↔ (Γ,Γm) ⊢ a : σ.
Proof.
  rewrite !addr_typed_alt; destruct a; simpl. by rewrite ref_offset_freeze,
    ref_size_freeze; setoid_rewrite ref_typed_freeze.
Qed.
Lemma addr_is_obj_ref_byte Γ Γm a σ :
  (Γ,Γm) ⊢ a : σ → addr_is_obj a → addr_ref_byte Γ a = 0.
Proof. by destruct 1; intros; simplify_equality'. Qed.
Lemma addr_is_obj_type_base Γ Γm a σ :
  (Γ,Γm) ⊢ a : σ → addr_is_obj a → addr_type_base a = σ.
Proof. by destruct 1. Qed.
Lemma addr_not_obj_type Γ Γm a σ :
  (Γ,Γm) ⊢ a : σ → ¬addr_is_obj a → σ ≠ voidT → σ = ucharT.
Proof.
  intros [o r i τ σ' σc] ??. destruct (proj1 (castable_alt σ' σc))
    as [?|[?|?]]; simplify_equality'; auto.
Qed.
Lemma addr_not_obj_size_of Γ Γm a σ :
  (Γ,Γm) ⊢ a : σ → ¬addr_is_obj a → size_of Γ σ = 1.
Proof.
  intros. destruct (decide (σ = voidT)) as [->|]; auto using size_of_void.
  by erewrite (addr_not_obj_type _ _ a σ), size_of_uchar by eauto.
Qed.
Lemma addr_not_obj_bit_size_of Γ Γm a σ :
  (Γ,Γm) ⊢ a : σ → ¬addr_is_obj a → bit_size_of Γ σ = char_bits.
Proof.
  intros. unfold bit_size_of. erewrite addr_not_obj_size_of by eauto; lia.
Qed.
Lemma addr_byte_range Γ Γm a σ :
  ✓ Γ → (Γ,Γm) ⊢ a : σ → addr_strict Γ a →
  addr_ref_byte Γ a + size_of Γ σ ≤ size_of Γ (addr_type_base a).
Proof.
  intros. destruct (decide (addr_is_obj a)).
  { erewrite addr_is_obj_type_base, addr_is_obj_ref_byte by eauto; lia. }
  erewrite addr_not_obj_size_of by eauto.
  cut (addr_ref_byte Γ a < size_of Γ (addr_type_base a)); [lia|].
  apply Nat.mod_bound_pos; auto with lia.
  eapply size_of_pos, addr_typed_type_base_valid; eauto.
Qed.
Lemma addr_bit_range Γ Γm a σ :
  ✓ Γ → (Γ,Γm) ⊢ a : σ → addr_strict Γ a →
  addr_ref_byte Γ a * char_bits + bit_size_of Γ σ
    ≤ bit_size_of Γ (addr_type_base a).
Proof.
  intros. unfold bit_size_of. rewrite <-Nat.mul_add_distr_r,
    <-Nat.mul_le_mono_pos_r by auto using char_bits_pos.
  eauto using addr_byte_range.
Qed.
Lemma addr_size_of_weaken Γ1 Γ2 m1 a σ :
  ✓ Γ1 → (Γ1,m1) ⊢ a : σ → Γ1 ⊆ Γ2 → size_of' Γ1 a = size_of' Γ2 a.
Proof.
  intros ? [o r i τ σ' σc'] ?; simpl. by erewrite size_of_weaken
    by eauto using ref_typed_type_valid, castable_type_valid.
Qed.
Lemma addr_strict_weaken Γ1 Γ2 m1 a σ :
  ✓ Γ1 → (Γ1,m1) ⊢ a : σ → addr_strict Γ1 a → Γ1 ⊆ Γ2 → addr_strict Γ2 a.
Proof.
  unfold addr_strict. intros ????.
  by erewrite <-size_of_weaken by eauto using addr_typed_type_base_valid.
Qed.
Lemma addr_ref_weaken Γ1 Γ2 m1 a σ :
  ✓ Γ1 → (Γ1,m1) ⊢ a : σ → Γ1 ⊆ Γ2 → addr_ref Γ1 a = addr_ref Γ2 a.
Proof.
  intros ? [] ?; simpl.
  by erewrite size_of_weaken by eauto using ref_typed_type_valid.
Qed.
Lemma addr_ref_byte_weaken Γ1 Γ2 m1 a σ :
  ✓ Γ1 → (Γ1,m1) ⊢ a : σ → Γ1 ⊆ Γ2 → addr_ref_byte Γ1 a = addr_ref_byte Γ2 a.
Proof.
  intros ? [] ?; simpl.
  by erewrite size_of_weaken by eauto using ref_typed_type_valid.
Qed.
Lemma addr_object_offset_alt Γ Γm a σ :
  ✓ Γ → (Γ,Γm) ⊢ a : σ → addr_strict Γ a → addr_object_offset Γ a
  = ref_object_offset Γ (addr_ref Γ a) + addr_ref_byte Γ a * char_bits.
Proof.
  intros ? [o r i τ σ' σc' Hor] ?; simpl in *.
  erewrite ref_object_offset_set_offset_0
    by eauto using Nat.div_lt_upper_bound, size_of_ne_0, ref_typed_type_valid.
  rewrite (Nat.div_mod i (size_of Γ σ')) at 1
    by eauto using size_of_ne_0,ref_typed_type_valid; unfold bit_size_of; lia.
Qed.
Lemma addr_top_typed Γ Γm o τ :
  ✓ Γ → Γm ⊢ o : τ → ✓{Γ} τ → int_typed (size_of Γ τ) sptrT →
  (Γ,Γm) ⊢ addr_top o τ : τ.
Proof.
  constructor; simpl; eauto using Nat.mod_0_l, size_of_ne_0; [|lia].
  by apply ref_typed_nil.
Qed.
Lemma addr_top_strict Γ o τ : ✓ Γ → ✓{Γ} τ → addr_strict Γ (addr_top o τ).
Proof.
  unfold addr_strict, addr_top; simpl. rewrite Nat.mul_1_r.
  eauto using size_of_pos.
Qed.
Lemma addr_top_array_typed Γ Γm o τ (n : Z) :
  ✓ Γ → Γm ⊢ o : τ.[Z.to_nat n] → ✓{Γ} τ → Z.to_nat n ≠ 0 →
  int_typed (n * size_of Γ τ) sptrT → (Γ,Γm) ⊢ addr_top_array o τ n : τ.
Proof.
  intros. assert (0 ≤ n)%Z by (by destruct n). constructor; simpl; auto.
  * apply TArray_valid; auto with lia.
  * by rewrite size_of_array, Nat2Z.inj_mul, Z2Nat.id by done.
  * repeat typed_constructor; lia. 
  * lia.
  * eauto using Nat.mod_0_l, size_of_ne_0.
Qed.
Lemma addr_top_array_strict Γ o τ n :
  ✓ Γ → ✓{Γ} τ → Z.to_nat n ≠ 0 → addr_strict Γ (addr_top_array o τ n).
Proof.
  intros. apply Nat.mul_pos_pos; simpl; eauto using size_of_pos with lia.
Qed.
Lemma addr_is_top_array_alt Γ Γm a τ :
  ✓ Γ → (Γ,Γm) ⊢ a : τ → addr_is_top_array a ↔ ∃ τ' n, addr_strict Γ a ∧
    addr_ref Γ a = [RArray 0 τ' n] ∧ addr_ref_byte Γ a = 0.
Proof.
  rewrite addr_typed_alt; intros ? (_&?&_&Hr&?&?&?&_&?); split.
  * destruct 1 as [o τ' n σc]; simplify_equality'; exists τ' n.
    assert (✓{Γ} τ' ∧ n ≠ 0) as [??] by auto using TArray_valid_inv.
    rewrite Nat.div_0_l, Nat.mod_0_l by eauto using size_of_ne_0.
    split_ands; auto using Nat.mul_pos_pos, size_of_pos with lia.
  * intros (?&n&?&?&Hi); destruct a as [o [|[] r] i τ' σ σc]; simplify_equality'.
    rewrite ref_typed_singleton in Hr; inversion Hr; simplify_equality'.
    rewrite <-(Nat.mod_small i (size_of Γ σ)), Hi
      by (apply Nat.div_small_iff; eauto using size_of_ne_0, TArray_valid_inv_type).
    constructor.
Qed.
Global Instance addr_is_top_array_dec a : Decision (addr_is_top_array a).
Proof.
 refine
  match a with
  | Addr o [RArray 0 σ1 n1] 0 (σ2.[n2]) σ3 σ4 =>
     cast_if_and3 (decide (n1 = n2)) (decide (σ1 = σ2)) (decide (σ2 = σ3))
  | _ => right _
  end; abstract first [by inversion 1 | subst; constructor].
Defined.

(** ** Disjointness *)
Global Instance addr_disjoint_dec Γ a1 a2 : Decision (a1 ⊥{Γ} a2).
Proof. unfold disjointE, addr_disjoint; apply _. Defined.
Lemma addr_disjoint_weaken Γ1 Γ2 m1 a1 a2 σ1 σ2 :
  ✓ Γ1 → (Γ1,m1) ⊢ a1 : σ1 → (Γ1,m1) ⊢ a2 : σ2 →
  a1 ⊥{Γ1} a2 → Γ1 ⊆ Γ2 → a1 ⊥{Γ2} a2.
Proof.
  unfold disjointE, addr_disjoint. intros. by erewrite
    <-!(addr_ref_weaken Γ1 Γ2), <-!(addr_ref_byte_weaken Γ1 Γ2) by eauto.
Qed.
Lemma addr_top_disjoint Γ Γm o1 o2 τ1 τ2 :
  Γm ⊢ o1 : τ1 → Γm ⊢ o2 : τ2 → 
  addr_top o1 τ1 = addr_top o2 τ2 ∨ addr_top o1 τ1 ⊥{Γ} addr_top o2 τ2.
Proof.
  intros. destruct (decide (o1 = o2)); simplify_type_equality; auto.
  by right; left.
Qed.
Lemma addr_disjoint_object_offset Γ Γm a1 a2 σ1 σ2 :
  ✓ Γ → (Γ,Γm) ⊢ a1 : σ1 → addr_strict Γ a1 →
  (Γ,Γm) ⊢ a2 : σ2 → addr_strict Γ a2 → a1 ⊥{Γ} a2 →
  (** 1.) *) addr_index a1 ≠ addr_index a2 ∨
  (** 2.) *)
    addr_object_offset Γ a1 + bit_size_of Γ σ1 ≤ addr_object_offset Γ a2 ∨
  (** 3.) *)
    addr_object_offset Γ a2 + bit_size_of Γ σ2 ≤ addr_object_offset Γ a1.
Proof.
  intros ?????. erewrite !addr_object_offset_alt by eauto.
  intros [?|[[??]|(?&Hr&?&?&?)]]; auto.
  { destruct (ref_disjoint_object_offset Γ (addr_type_object a1)
      (addr_ref Γ a1) (addr_ref Γ a2) (addr_type_base a1) (addr_type_base a2));
      eauto using addr_typed_ref_typed;
      erewrite ?(addr_type_object_eq _ _ a1 a2) by eauto;
      eauto using addr_typed_ref_typed.
    * feed pose proof (addr_bit_range Γ Γm a1 σ1); auto. right; left; lia.
    * feed pose proof (addr_bit_range Γ Γm a2 σ2); auto. do 2 right; lia. }
  erewrite ?addr_not_obj_bit_size_of,
    <-(ref_object_offset_freeze Γ true (addr_ref Γ a1)), Hr,
    ref_object_offset_freeze by eauto.
  destruct (decide (addr_ref_byte Γ a1 < addr_ref_byte Γ a2)).
  * right; left. rewrite <-Nat.add_assoc, <-Nat.mul_succ_l.
    apply Nat.add_le_mono_l, Nat.mul_le_mono_nonneg_r; lia.
  * do 2 right. rewrite <-Nat.add_assoc, <-Nat.mul_succ_l.
    apply Nat.add_le_mono_l, Nat.mul_le_mono_nonneg_r; lia.
Qed.
End addresses.
