(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export operations values_refine.
Require Import pointer_casts.

Local Open Scope ctype_scope.
Local Coercion Z.of_nat: nat >-> Z.

Section operations.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types Δ : memenv K.
Implicit Types τb σb : base_type K.
Implicit Types τ σ : type K.
Implicit Types τp σp : ptr_type K.
Implicit Types a : addr K.
Implicit Types vb : base_val K.
Implicit Types v : val K.
Implicit Types m : mem K.
Hint Immediate index_alive_1': core.
Hint Resolve ptr_alive_1' index_alive_2': core.
Hint Immediate addr_refine_typed_l addr_refine_typed_r: core.

(** ** Refinements of operations on addresses *)
Lemma addr_alive_refine' Γ α f m1 m2 a1 a2 σp :
  index_alive' m1 (addr_index a1) → a1 ⊑{Γ,α,f@'{m1}↦'{m2}} a2 : σp →
  index_alive' m2 (addr_index a2).
Proof. eauto using addr_alive_refine. Qed.
Lemma addr_compare_ok_refine Γ α f m1 m2 c a1 a2 a3 a4 σp :
  a1 ⊑{Γ,α,f@'{m1}↦'{m2}} a2 : σp → a3 ⊑{Γ,α,f@'{m1}↦'{m2}} a4 : σp →
  addr_compare_ok Γ m1 c a1 a3 → addr_compare_ok Γ m2 c a2 a4.
Proof.
  intros Ha1 Ha2 (?&?&?); split_and !; eauto using addr_alive_refine'.
  intros. destruct (decide (addr_index a1 = addr_index a3));
    [destruct Ha1, Ha2; naive_solver|intuition eauto using addr_strict_refine].
Qed.
Lemma addr_compare_refine Γ α f m1 m2 c a1 a2 a3 a4 σp :
  ✓ Γ → addr_compare_ok Γ m1 c a1 a3 →
  a1 ⊑{Γ,α,f@'{m1}↦'{m2}} a2 : σp → a3 ⊑{Γ,α,f@'{m1}↦'{m2}} a4 : σp →
  addr_compare Γ c a1 a3 = addr_compare Γ c a2 a4.
Proof.
  intros ? (_&_&Hstrict) Ha1 Ha2; unfold addr_compare; apply bool_decide_iff.
  assert ('{m1} ⊑{Γ,α,f} '{m2}) as HΔ by eauto using addr_refine_memenv_refine.
  destruct (addr_object_offset_refine Γ α f
    '{m1} '{m2} a1 a2 σp) as (r1&?&?&->); auto.
  destruct (addr_object_offset_refine Γ α f
    '{m1} '{m2} a3 a4 σp) as (r3&?&?&->); auto.
  destruct (decide (addr_index a1 = addr_index a3)).
  { replace r1 with r3 by congruence. clear Hstrict.
    destruct c; simplify_equality'; intuition auto with congruence lia. }
  split; [by intros []|intros [Ha ?]].
  destruct Hstrict as (->&?&?); auto; csimpl in *.
  destruct (meminj_injective_alt f (addr_index a1) (addr_index a3)
    (addr_index a2) r1 r3) as [|[_ ?]];
    eauto using memenv_refine_injective with congruence.
  assert (addr_object_offset Γ a1 + ptr_bit_size_of Γ σp ≤ bit_size_of Γ
    (addr_type_object a1)) by eauto using addr_object_offset_bit_size.
  assert (addr_object_offset Γ a3 + ptr_bit_size_of Γ σp ≤ bit_size_of Γ
    (addr_type_object a3)) by eauto using addr_object_offset_bit_size.
  assert (0 < ptr_bit_size_of Γ σp).
  { destruct σp; simpl; eauto using char_bits_pos,
      bit_size_of_pos, addr_typed_type_valid. }
  assert (addr_type_object a2 = addr_type_object a4).
  { eapply typed_unique; eauto using addr_typed_index.
    rewrite Ha; eauto using addr_typed_index. }
  destruct (ref_disjoint_object_offset Γ (addr_type_object a2) r1 r3
    (addr_type_object a1) (addr_type_object a3)); auto with congruence lia.
Qed.
Lemma addr_plus_ok_refine Γ α f m1 m2 a1 a2 σp j :
  a1 ⊑{Γ,α,f@'{m1}↦'{m2}} a2 : σp →
  addr_plus_ok Γ m1 j a1 → addr_plus_ok Γ m2 j a2.
Proof.
  unfold addr_plus_ok. intros Ha (?&?&?).
  destruct (addr_byte_refine_help Γ α f
    '{m1} '{m2} a1 a2 σp) as (i&?&?); auto.
  destruct Ha as [??????????? []]; simplify_equality'; split; eauto; lia.
Qed.
Lemma addr_plus_refine Γ α f m1 m2 a1 a2 σp j :
  ✓ Γ → addr_plus_ok Γ m1 j a1 → a1 ⊑{Γ,α,f@'{m1}↦'{m2}} a2 : σp →
  addr_plus Γ j a1 ⊑{Γ,α,f@'{m1}↦'{m2}} addr_plus Γ j a2 : σp.
Proof.
  intros ? Ha' Ha. unfold addr_plus; simpl.
  destruct Ha' as (_&?&?), Ha as
    [o1 o2 r1 r' r2 i1 i2 τ1 τ2 σ σp ?????????? Hr]; simplify_equality'.
  refine_constructor; eauto.
  { apply Nat2Z.inj_le. by rewrite Nat2Z.inj_mul, Z2Nat.id by done. }
  { rewrite <-(Nat2Z.id (ptr_size_of Γ σp)) at 1.
    rewrite Z2Nat_divide by auto with zpos.
    apply Z.divide_add_r; [by apply Nat2Z_divide|by apply Z.divide_mul_r]. }
  destruct Hr as [|r1 i1 r2 i2 Hr|r1' r1 r2 i];
    simplify_type_equality'; constructor; auto.
  rewrite Nat2Z.inj_add, Nat2Z.inj_mul.
  transitivity (Z.to_nat ((i1 + j * ptr_size_of Γ σp) +
    size_of Γ σ * ref_offset r1)); [f_equal; lia |].
  by rewrite Z2Nat.inj_add, Z2Nat.inj_mul, !Nat2Z.id
    by auto using Z.mul_nonneg_nonneg with lia.
Qed.
Lemma addr_minus_refine Γ α f m1 m2 a1 a2 a3 a4 σp :
  addr_minus_ok Γ m1 a1 a3 → a1 ⊑{Γ,α,f@'{m1}↦'{m2}} a2 : σp →
  a3 ⊑{Γ,α,f@'{m1}↦'{m2}} a4 : σp → addr_minus Γ a1 a3 = addr_minus Γ a2 a4.
Proof.
  intros (?&?&?&?).
  destruct 1 as [o1 o2 r1 r2 r3 i1 i3 τ1 τ2 σ1 σp ?????????? Hr],
    1 as [o4 o5 r4 r5 r6 i4 i6 τ4 τ5 σ3 σp4 ?????????? Hr'].
  destruct Hr, Hr'; simplify_list_eq;
    simplify_type_equality; f_equal; lia.
Qed.
Lemma addr_minus_ok_refine Γ α f m1 m2 a1 a2 a3 a4 σp :
  a1 ⊑{Γ,α,f@'{m1}↦'{m2}} a2 : σp → a3 ⊑{Γ,α,f@'{m1}↦'{m2}} a4 : σp →
  addr_minus_ok Γ m1 a1 a3 → addr_minus_ok Γ m2 a2 a4.
Proof.
  intros Ha1 Ha3 Ha. assert (∀ r1 r2 r3 r4 r : ref K,
    r1 ++ r ⊆* r2 → r3 ++ r ⊆* r4 → freeze true <$> r1 = freeze true <$> r3 →
    freeze true <$> r2 = freeze true <$> r4).
  { intros r1 r2 r3 r4 r ???.
    erewrite <-(ref_freeze_le _ _ r2), <-(ref_freeze_le _ _ r4) by eauto.
    rewrite !fmap_app. by f_equal. }
  unfold addr_minus_ok; erewrite <-addr_minus_refine by eauto. 
  destruct Ha1 as [??????????? [] ????????? Hr1],
    Ha3 as [??????????? [] ????????? Hr2]; destruct Hr1; inversion Hr2;
    destruct Ha as (?&?&?&?); simplify_list_eq;
    split_and ?; eauto using ref_le_unique.
Qed.
Lemma addr_cast_ok_refine Γ α f m1 m2 a1 a2 σp τp :
  ✓ Γ → a1 ⊑{Γ,α,f@'{m1}↦'{m2}} a2 : σp →
  addr_cast_ok Γ m1 τp a1 → addr_cast_ok Γ m2 τp a2.
Proof.
  destruct 2 as [o o' r r' r'' i i'' τ τ' σ σp' [] ????????? []];
    intros (?&?&?); simplify_equality'; split_and ?;
    eauto using size_of_castable, Nat.divide_add_r, Nat.divide_mul_l.
Qed.
Lemma addr_cast_refine Γ α f m1 m2 a1 a2 σp τp :
  addr_cast_ok Γ m1 τp a1 → a1 ⊑{Γ,α,f@'{m1}↦'{m2}} a2 : σp →
  addr_cast τp a1 ⊑{Γ,α,f@'{m1}↦'{m2}} addr_cast τp a2 : τp.
Proof. intros (?&?&?). destruct 1; simplify_equality'; econstructor; eauto. Qed.

(** ** Refinements of operations on pointers *)
Lemma ptr_alive_refine' Γ α f m1 m2 p1 p2 σp :
  ptr_alive' m1 p1 → p1 ⊑{Γ,α,f@'{m1}↦'{m2}} p2 : σp → ptr_alive' m2 p2.
Proof. destruct 2; simpl in *; eauto using addr_alive_refine. Qed.
Lemma ptr_compare_ok_refine Γ α f m1 m2 c p1 p2 p3 p4 σp :
  p1 ⊑{Γ,α,f@'{m1}↦'{m2}} p2 : σp → p3 ⊑{Γ,α,f@'{m1}↦'{m2}} p4 : σp →
  ptr_compare_ok Γ m1 c p1 p3 → ptr_compare_ok Γ m2 c p2 p4.
Proof.
  destruct 1, 1, c; simpl; eauto using addr_minus_ok_refine,
    addr_alive_refine, addr_compare_ok_refine.
Qed.
Lemma ptr_compare_refine Γ α f m1 m2 c p1 p2 p3 p4 σp :
  ✓ Γ → ptr_compare_ok Γ m1 c p1 p3 →
  p1 ⊑{Γ,α,f@'{m1}↦'{m2}} p2 : σp → p3 ⊑{Γ,α,f@'{m1}↦'{m2}} p4 : σp →
  ptr_compare Γ c p1 p3 = ptr_compare Γ c p2 p4.
Proof.
  destruct 3, 1; simpl; repeat case_match; eauto 2 using addr_compare_refine.
Qed.
Lemma ptr_plus_ok_refine Γ α f m1 m2 p1 p2 σp j :
  p1 ⊑{Γ,α,f@'{m1}↦'{m2}} p2 : σp →
  ptr_plus_ok Γ m1 j p1 → ptr_plus_ok Γ m2 j p2.
Proof. destruct 1; simpl; eauto using addr_plus_ok_refine. Qed.
Lemma ptr_plus_refine Γ α f m1 m2 p1 p2 σp j :
  ✓ Γ → ptr_plus_ok Γ m1 j p1 → p1 ⊑{Γ,α,f@'{m1}↦'{m2}} p2 : σp →
  ptr_plus Γ j p1 ⊑{Γ,α,f@'{m1}↦'{m2}} ptr_plus Γ j p2 : σp.
Proof. destruct 3; simpl; constructor; eauto using addr_plus_refine. Qed.
Lemma ptr_minus_ok_refine Γ α f m1 m2 p1 p2 p3 p4 σp :
  p1 ⊑{Γ,α,f@'{m1}↦'{m2}} p2 : σp → p3 ⊑{Γ,α,f@'{m1}↦'{m2}} p4 : σp →
  ptr_minus_ok Γ m1 p1 p3 → ptr_minus_ok Γ m2 p2 p4.
Proof. destruct 1, 1; simpl; eauto using addr_minus_ok_refine. Qed.
Lemma ptr_minus_refine Γ α f m1 m2 p1 p2 p3 p4 σp :
  ✓ Γ → ptr_minus_ok Γ m1 p1 p3 →
  p1 ⊑{Γ,α,f@'{m1}↦'{m2}} p2 : σp → p3 ⊑{Γ,α,f@'{m1}↦'{m2}} p4 : σp →
  ptr_minus Γ p1 p3 = ptr_minus Γ p2 p4.
Proof. destruct 3, 1; simpl; eauto using addr_minus_refine. Qed.
Lemma ptr_cast_ok_refine Γ α f m1 m2 p1 p2 σp τp :
  ✓ Γ → p1 ⊑{Γ,α,f@'{m1}↦'{m2}} p2 : σp →
  ptr_cast_ok Γ m1 τp p1 → ptr_cast_ok Γ m2 τp p2.
Proof. destruct 2; simpl; eauto using addr_cast_ok_refine. Qed.
Lemma ptr_cast_refine Γ α f m1 m2 p1 p2 σp τp :
  ptr_cast_ok Γ m1 τp p1 → ptr_cast_typed σp τp → ✓{Γ} τp →
  p1 ⊑{Γ,α,f@'{m1}↦'{m2}} p2 : σp →
  ptr_cast τp p1 ⊑{Γ,α,f@'{m1}↦'{m2}} ptr_cast τp p2 : τp.
Proof.
  destruct 2; inversion 2; intros; simplify_equality';
    constructor; eauto using addr_cast_refine.
Qed.

(** ** Refinements of operations on base values *)
Lemma base_val_branchable_refine Γ α f m1 m2 vb1 vb2 τb :
  vb1 ⊑{Γ,α,f@'{m1}↦'{m2}} vb2 : τb →
  base_val_branchable m1 vb1 → base_val_branchable m2 vb2.
Proof. destruct 1; naive_solver eauto 10 using ptr_alive_refine'. Qed.
Lemma base_val_is_0_refine Γ α f Δ1 Δ2 vb1 vb2 τb :
  vb1 ⊑{Γ,α,f@Δ1↦Δ2} vb2 : τb → base_val_is_0 vb1 → base_val_is_0 vb2.
Proof. by destruct 1 as [| | | |??? []|???? []| | |]. Qed.
Lemma base_val_is_0_refine_inv Γ α f m1 m2 vb1 vb2 τb :
  vb1 ⊑{Γ,α,f@'{m1}↦'{m2}} vb2 : τb → base_val_branchable m1 vb1 →
  base_val_is_0 vb2 → base_val_is_0 vb1.
Proof.
  destruct 1 as [| | | |??? []|???? []| | |];
    naive_solver eauto 10 using addr_alive_refine.
Qed.
Lemma base_val_true_refine_inv Γ α f m1 m2 vb1 vb2 τb :
  vb1 ⊑{Γ,α,f@'{m1}↦'{m2}} vb2 : τb →
  base_val_branchable m2 vb2 → ¬base_val_is_0 vb2 →
  (**i 1.) *) base_val_branchable m1 vb1 ∧ ¬base_val_is_0 vb1 ∨
  (**i 2.) *) α ∧ ¬base_val_branchable m1 vb1.
Proof.
  intros; destruct α; eauto 10 using base_val_branchable_refine,
    base_val_refine_inverse, base_val_is_0_refine.
  destruct (decide (base_val_branchable m1 vb1));
    eauto 10 using base_val_is_0_refine.
Qed.
Lemma base_val_false_refine_inv Γ α f m1 m2 vb1 vb2 τb :
  vb1 ⊑{Γ,α,f@'{m1}↦'{m2}} vb2 : τb → base_val_is_0 vb2 →
  base_val_is_0 vb1 ∨ (α ∧ ¬base_val_branchable m1 vb1).
Proof.
  intros; destruct α; eauto using base_val_is_0_refine, base_val_refine_inverse.
  destruct (decide (base_val_branchable m1 vb1));
    eauto using base_val_is_0_refine_inv.
Qed.

Lemma base_val_unop_ok_refine Γ α f m1 m2 op vb1 vb2 τb :
  vb1 ⊑{Γ,α,f@'{m1}↦'{m2}} vb2 : τb →
  base_val_unop_ok m1 op vb1 → base_val_unop_ok m2 op vb2.
Proof. destruct op, 1; naive_solver eauto using ptr_alive_refine'. Qed.
Lemma base_val_unop_refine Γ α f m1 m2 op vb1 vb2 τb σb :
  ✓ Γ → base_unop_typed op τb σb → base_val_unop_ok m1 op vb1 →
  vb1 ⊑{Γ,α,f@'{m1}↦'{m2}} vb2 : τb →
  base_val_unop op vb1 ⊑{Γ,α,f@'{m1}↦'{m2}} base_val_unop op vb2 : σb.
Proof.
  intros ? Hvτb ? Hvb. assert ((Γ,'{m2}) ⊢ base_val_unop op vb2 : σb) as Hvb2.
  { eauto using base_val_unop_typed,
      base_val_refine_typed_r, base_val_unop_ok_refine. }
  destruct Hvτb; inversion Hvb as [| | | |p1 p2 ? Hp| | | |];
    simplify_equality'; try done.
  * refine_constructor. by apply int_unop_typed.
  * destruct Hp; refine_constructor; by apply int_typed_small.
  * naive_solver.
Qed.
Lemma base_val_binop_ok_refine Γ α f m1 m2 op vb1 vb2 vb3 vb4 τb1 τb3 σb :
  ✓ Γ → base_binop_typed op τb1 τb3 σb →
  vb1 ⊑{Γ,α,f@'{m1}↦'{m2}} vb2 : τb1 → vb3 ⊑{Γ,α,f@'{m1}↦'{m2}} vb4 : τb3 →
  base_val_binop_ok Γ m1 op vb1 vb3 → base_val_binop_ok Γ m2 op vb2 vb4.
Proof.
  intros ? Hσ. destruct 1, 1; try done; inversion Hσ;
   try naive_solver eauto using ptr_minus_ok_alive_l, ptr_minus_ok_alive_r,
    ptr_plus_ok_alive, ptr_plus_ok_refine, ptr_minus_ok_refine,
    ptr_compare_ok_refine, ptr_compare_ok_alive_l, ptr_compare_ok_alive_r.
Qed.
Lemma base_val_binop_refine Γ α f m1 m2 op vb1 vb2 vb3 vb4 τb1 τb3 σb :
  ✓ Γ → base_binop_typed op τb1 τb3 σb → base_val_binop_ok Γ m1 op vb1 vb3 →
  vb1 ⊑{Γ,α,f@'{m1}↦'{m2}} vb2 : τb1 → vb3 ⊑{Γ,α,f@'{m1}↦'{m2}} vb4 : τb3 →
  base_val_binop Γ op vb1 vb3
    ⊑{Γ,α,f@'{m1}↦'{m2}} base_val_binop Γ op vb2 vb4 : σb.
Proof.
  intros ? Hσ ?; destruct 1 as [| | | |p1 p2| | | |],
    1 as [| | | |p3 p4| | | |]; try done; inversion Hσ; simplify_equality';
    try first
    [ by refine_constructor; eauto using int_binop_typed, ptr_plus_refine
    | exfalso; by eauto using ptr_minus_ok_alive_l, ptr_minus_ok_alive_r,
        ptr_plus_ok_alive, ptr_compare_ok_alive_l, ptr_compare_ok_alive_r ].
  * erewrite ptr_compare_refine by eauto.
    refine_constructor. by case_match; apply int_typed_small.
  * erewrite <-(ptr_minus_refine _ _ _ _ _ p1 p2 p3 p4) by eauto.
    refine_constructor; eauto using ptr_minus_typed.
Qed.
Lemma base_val_cast_ok_refine Γ α f m1 m2 vb1 vb2 τb σb :
  ✓ Γ → vb1 ⊑{Γ,α,f@'{m1}↦'{m2}} vb2 : τb →
  base_val_cast_ok Γ m1 σb vb1 → base_val_cast_ok Γ m2 σb vb2.
Proof.
  assert (∀ vb, (Γ,'{m2}) ⊢ vb : ucharT%BT → base_val_cast_ok Γ m2 ucharT vb).
  { inversion 1; simpl; eauto using int_unsigned_pre_cast_ok,int_cast_ok_more. }
  destruct σb, 2; simpl; try naive_solver eauto using
    ptr_cast_ok_refine, ptr_cast_ok_alive, base_val_cast_ok_void,
    int_unsigned_pre_cast_ok, int_cast_ok_more, ptr_alive_refine'.
Qed.
Lemma base_val_cast_refine Γ α f m1 m2 vb1 vb2 τb σb :
  ✓ Γ → base_cast_typed τb σb → ✓{Γ} σb → base_val_cast_ok Γ m1 σb vb1 →
  vb1 ⊑{Γ,α,f@'{m1}↦'{m2}} vb2 : τb →
  base_val_cast σb vb1 ⊑{Γ,α,f@'{m1}↦'{m2}} base_val_cast σb vb2 : σb.
Proof.
  assert (∀ vb,
    (Γ,'{m2}) ⊢ vb : ucharT%BT → base_val_cast ucharT vb = vb) as help.
  { inversion 1; f_equal'. by rewrite int_cast_spec, int_typed_pre_cast
      by eauto using int_unsigned_pre_cast_ok,int_cast_ok_more. }
  destruct 2; inversion 3;
    simplify_equality'; intuition; simplify_equality'; try first
    [ by exfalso; eauto using ptr_cast_ok_alive
    | rewrite ?base_val_cast_void, ?help, ?int_cast_spec, ?int_typed_pre_cast
        by eauto using int_unsigned_pre_cast_ok,int_cast_ok_more;
      by refine_constructor; eauto using ptr_cast_refine, int_cast_typed,
        ptr_cast_refine, TPtr_valid_inv, base_val_typed_type_valid,
        base_val_refine_typed_l ].
Qed.

(** ** Refinements of operations on values *)
Lemma val_unop_ok_refine Γ α f m1 m2 op v1 v2 τ :
  v1 ⊑{Γ,α,f@'{m1}↦'{m2}} v2 : τ →
  val_unop_ok m1 op v1 → val_unop_ok m2 op v2.
Proof. destruct op, 1; simpl; eauto using base_val_unop_ok_refine. Qed.
Lemma val_unop_refine Γ α f m1 m2 op v1 v2 τ σ :
  ✓ Γ → unop_typed op τ σ → val_unop_ok m1 op v1 →
  v1 ⊑{Γ,α,f@'{m1}↦'{m2}} v2 : τ →
  val_unop op v1 ⊑{Γ,α,f@'{m1}↦'{m2}} val_unop op v2 : σ.
Proof.
  destruct 2; inversion 2; intros; simplify_equality';
    refine_constructor; eauto using base_val_unop_refine.
Qed.
Lemma val_binop_ok_refine Γ α f m1 m2 op v1 v2 v3 v4 τ1 τ3 σ :
  ✓ Γ → binop_typed op τ1 τ3 σ →
  v1 ⊑{Γ,α,f@'{m1}↦'{m2}} v2 : τ1 → v3 ⊑{Γ,α,f@'{m1}↦'{m2}} v4 : τ3 →
  val_binop_ok Γ m1 op v1 v3 → val_binop_ok Γ m2 op v2 v4.
Proof.
  unfold val_binop_ok; destruct 2; do 2 inversion 1;
    simplify_equality'; eauto using base_val_binop_ok_refine.
Qed.
Lemma val_binop_refine Γ α f m1 m2 op v1 v2 v3 v4 τ1 τ3 σ :
  ✓ Γ → binop_typed op τ1 τ3 σ → val_binop_ok Γ m1 op v1 v3 →
  v1 ⊑{Γ,α,f@'{m1}↦'{m2}} v2 : τ1 → v3 ⊑{Γ,α,f@'{m1}↦'{m2}} v4 : τ3 →
  val_binop Γ op v1 v3 ⊑{Γ,α,f@'{m1}↦'{m2}} val_binop Γ op v2 v4 : σ.
Proof.
  destruct 2; intro; do 2 inversion 1; simplify_equality';
    refine_constructor; eauto using base_val_binop_refine.
Qed.
Lemma val_cast_ok_refine Γ α f m1 m2 v1 v2 τ σ :
  ✓ Γ → v1 ⊑{Γ,α,f@'{m1}↦'{m2}} v2 : τ →
  val_cast_ok Γ m1 (TType σ) v1 → val_cast_ok Γ m2 (TType σ) v2.
Proof.
  unfold val_cast_ok; destruct σ, 2; eauto using base_val_cast_ok_refine.
Qed.
Lemma val_cast_refine Γ α f m1 m2 v1 v2 τ σ :
  ✓ Γ → cast_typed τ σ → ✓{Γ} σ → val_cast_ok Γ m1 (TType σ) v1 →
  v1 ⊑{Γ,α,f@'{m1}↦'{m2}} v2 : τ →
  val_cast (TType σ) v1 ⊑{Γ,α,f@'{m1}↦'{m2}} val_cast (TType σ) v2 : σ.
Proof.
  destruct 2; inversion 1; inversion 2; simplify_equality;
    repeat refine_constructor;
    eauto using base_val_cast_refine, TVoid_cast_typed, base_cast_typed_self.
Qed.
End operations.
