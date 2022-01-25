(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This files describes the syntax and semantics of operations on integers. *)
Require Export orders integer_coding.

Local Open Scope Z_scope.
Local Open Scope int_type_scope.
Local Coercion Z.of_nat: nat >-> Z.

(** * Syntax of integer operations *)
Inductive compop := EqOp | LtOp | LeOp.
Inductive bitop := AndOp | OrOp | XorOp.
Inductive arithop := PlusOp | MinusOp | MultOp | DivOp | ModOp.
Inductive shiftop := ShiftLOp | ShiftROp.
Inductive binop :=
  | CompOp : compop → binop
  | ArithOp : arithop → binop
  | ShiftOp : shiftop → binop
  | BitOp : bitop → binop.
Inductive unop := NegOp | ComplOp | NotOp.

#[global] Instance comp_kind_dec: EqDecision compop.
Proof. solve_decision. Defined.
#[global] Instance bitop_dec: EqDecision bitop.
Proof. solve_decision. Defined.
#[global] Instance arithop_dec: EqDecision arithop.
Proof. solve_decision. Defined.
#[global] Instance shiftop_dec: EqDecision shiftop.
Proof. solve_decision. Defined.
#[global] Instance binop_dec: EqDecision binop.
Proof. solve_decision. Defined.
#[global] Instance unop_dec: EqDecision unop.
Proof. solve_decision. Defined.

Definition Z_comp (c : compop) (x y : Z) : Prop :=
  match c with EqOp => x = y | LtOp => x < y | LeOp => x ≤ y end.
#[global] Instance Z_comp_dec (c : compop) (x y : Z) : Decision (Z_comp c x y).
Proof. case c; solve_decision. Defined.
Definition bool_bitop (op : bitop) : bool → bool → bool :=
  match op with AndOp => (&&) | OrOp => (||) | XorOp => xorb end.

Section pre_operations.
  Context `{IntCoding K}.

  Inductive int_subseteq : SubsetEq (int_type K) :=
    | int_subseteq_same_sign si (k1 k2 : K) :
       k1 ⊆ k2 → IntType si k1 ⊆ IntType si k2
    | int_subseteq_Signed_Unsigned (k1 k2 : K) :
       k1 ⊆ k2 → IntType Signed k1 ⊆ IntType Unsigned k2
    | int_subseteq_Unsigned_Signed (k1 k2 : K) :
       int_upper (IntType Unsigned k1) ≤ int_upper (IntType Signed k2) →
       IntType Unsigned k1 ⊆ IntType Signed k2.
  #[global] Existing Instance int_subseteq.

  Definition int_promote (τi : int_type K) : int_type K :=
    if decide (rank τi ⊆ int_rank) then
      if decide (int_upper τi ≤ int_upper sintT) then sintT else uintT
    else τi.
  Global Instance rank_union : Union K := λ k1 k2,
    if decide (k1 ⊆ k2) then k2 else k1.
  Global Instance int_union : Union (int_type K) := λ τi1 τi2,
    match τi1, τi2 with
    | IntType Signed k1, IntType Signed k2 => IntType Signed (k1 ∪ k2)
    | IntType Unsigned k1, IntType Unsigned k2 => IntType Unsigned (k1 ∪ k2)
    | IntType Signed k1, IntType Unsigned k2
    | IntType Unsigned k2, IntType Signed k1 =>
       if decide (k1 ⊆ k2) then IntType Unsigned k2
       else if decide (int_upper (IntType Unsigned k2) ≤
                       int_upper (IntType Signed k1)) then IntType Signed k1
       else IntType Unsigned k1
    end.
  Definition int_pre_arithop_ok
      (op : arithop) (x y : Z) (τi : int_type K) : Prop :=
    match op, sign τi with
    | PlusOp, Signed => int_lower τi ≤ x + y < int_upper τi
    | PlusOp, Unsigned => True
    | MinusOp, Signed => int_lower τi ≤ x - y < int_upper τi
    | MinusOp, Unsigned => True
    | MultOp, Signed => int_lower τi ≤ x * y < int_upper τi
    | MultOp, Unsigned => True
      (* Can still overflow, e.g. [-10 `quot` -1 = 10]. Maybe a tighter
         condition is possible. *)
    | (DivOp | ModOp), Signed =>
       y ≠ 0 ∧ int_lower τi ≤ x `quot` y < int_upper τi
    | (DivOp | ModOp), Unsigned => y ≠ 0
    end.
  Definition int_pre_arithop (op : arithop) (x y : Z) (τi : int_type K) : Z :=
    match op, sign τi with
    | PlusOp, Signed => x + y
    | PlusOp, Unsigned => (x + y) `mod` int_upper τi
    | MinusOp, Signed => x - y
    | MinusOp, Unsigned => (x - y) `mod` int_upper τi
    | MultOp, Signed => x * y
    | MultOp, Unsigned => (x * y) `mod` int_upper τi
    | DivOp, _ => x `quot` y
    | ModOp, _ => x `rem` y
    end.
  Definition int_pre_shiftop_ok
      (op : shiftop) (x y : Z) (τi : int_type K) : Prop :=
    match op, sign τi with
    | ShiftLOp, Signed => 0 ≤ x ∧ 0 ≤ y < int_width τi ∧ x ≪ y < int_upper τi
    | ShiftLOp, Unsigned => 0 ≤ y < int_width τi
    | ShiftROp, Signed => 0 ≤ x ∧ 0 ≤ y < int_width τi
    | ShiftROp, Unsigned => 0 ≤ y < int_width τi
    end.
  Definition int_pre_shiftop (op : shiftop) (x y : Z) (τi : int_type K) : Z :=
    match op, sign τi with
    | ShiftLOp, Signed => x ≪ y
    | ShiftLOp, Unsigned => (x ≪ y) `mod` int_upper τi
    | ShiftROp, _ => x ≫ y
    end.
  Definition int_pre_cast_ok (σi : int_type K) (x : Z) :=
    match sign σi with
    | Signed => (**i actually implementation defined, see 6.3.1.3 *)
       int_lower σi ≤ x < int_upper σi
    | Unsigned => True
    end.
  Definition int_pre_cast (σi : int_type K) (x : Z) :=
    match sign σi with Signed => x | Unsigned => x `mod` int_upper σi end.

  Global Instance int_pre_arithop_ok_dec op x y τi :
    Decision (int_pre_arithop_ok op x y τi).
  Proof. unfold int_pre_arithop_ok. destruct op, (sign τi); apply _. Defined.
  Global Instance int_pre_shiftop_ok_dec op x y τi :
    Decision (int_pre_shiftop_ok op x y τi).
  Proof. unfold int_pre_shiftop_ok. destruct op, (sign τi); apply _. Defined.
  Global Instance int_pre_cast_ok_dec σi x : Decision (int_pre_cast_ok σi x).
  Proof. unfold int_pre_cast_ok. destruct (sign σi); apply _. Defined.
End pre_operations.

(** To deal with partiality, the class [IntEnv] does not just contain a
function [int_binop] to perform a binary operation, but also a predicate
[int_binop_ok τi op x y] that describes whether [op] is allowed to be performed
on integers [x] and [y] of type [τi]. This is to allow both strict
implementations that make integer overflow undefined, and those that let it
wrap (as for example GCC with the -fno-strict-overflow flag does). When an
operation is allowed by the C standard, the result of [int_binop τi op x y]
should correspond to its specification by the standard. *)
Class IntEnv (K : iType) : iType := {
  int_coding :> IntCoding K;
  int_arithop_ok : arithop → Z → int_type K → Z → int_type K → Prop;
  int_arithop : arithop → Z → int_type K → Z → int_type K → Z;
  int_shiftop_ok : shiftop → Z → int_type K → Z → int_type K → Prop;
  int_shiftop : shiftop → Z → int_type K → Z → int_type K → Z;
  int_cast_ok : int_type K → Z → Prop;
  int_cast : int_type K → Z → Z;
  int_arithop_ok_dec op x τi1 y τi2 :> Decision (int_arithop_ok op x τi1 y τi2);
  int_shiftop_ok_dec op x τi1 y τi2 :> Decision (int_shiftop_ok op x τi1 y τi2);
  int_cast_ok_dec σi x :> Decision (int_cast_ok σi x)
}.
Arguments int_arithop_ok _ _ _ _ _ _ _ : simpl never.
Arguments int_arithop _ _ _ _ _ _ _ : simpl never.
Arguments int_shiftop_ok _ _ _ _ _ _ _ : simpl never.
Arguments int_shiftop _ _ _ _ _ _ _ : simpl never.
Arguments int_cast_ok _ _ _ _ : simpl never.
Arguments int_cast _ _ _ _ : simpl never.

Class IntEnvSpec K `{IntEnv K} := {
  int_coding_spec :> IntCodingSpec K;
  int_arithop_ok_more op x y τi1 τi2 :
    int_typed x τi1 → int_typed y τi2 →
    let τi' := int_promote τi1 ∪ int_promote τi2 in
    int_pre_arithop_ok op (int_pre_cast τi' x) (int_pre_cast τi' y) τi' →
    int_arithop_ok op x τi1 y τi2;
  int_arithop_typed op x y τi1 τi2 :
    int_typed x τi1 → int_typed y τi2 →
    int_arithop_ok op x τi1 y τi2 →
    int_typed (int_arithop op x τi1 y τi2) (int_promote τi1 ∪ int_promote τi2);
  int_arithop_spec op x y τi1 τi2 :
    int_typed x τi1 → int_typed y τi2 →
    let τi' := int_promote τi1 ∪ int_promote τi2 in
    int_pre_arithop_ok op (int_pre_cast τi' x) (int_pre_cast τi' y) τi' →
    int_arithop op x τi1 y τi2
    = int_pre_arithop op (int_pre_cast τi' x) (int_pre_cast τi' y) τi';
  int_shiftop_ok_more op x y τi1 τi2 :
    int_typed x τi1 → int_typed y τi2 →
    let τi' := int_promote τi1 in
    int_pre_shiftop_ok op (int_pre_cast τi' x) y τi' →
    int_shiftop_ok op x τi1 y τi2;
  int_shiftop_typed op x y τi1 τi2 :
    int_typed x τi1 → int_typed y τi2 → int_shiftop_ok op x τi1 y τi2 →
    int_typed (int_shiftop op x τi1 y τi2) (int_promote τi1);
  int_shiftop_spec op x y τi1 τi2 :
    int_typed x τi1 → int_typed y τi2 →
    let τi' := int_promote τi1 in
    int_pre_shiftop_ok op x y τi' →
    int_shiftop op x τi1 y τi2 = int_pre_shiftop op x y τi';
  int_cast_ok_more σi x : int_pre_cast_ok σi x → int_cast_ok σi x;
  int_cast_typed σi x : int_cast_ok σi x → int_typed (int_cast σi x) σi;
  int_cast_spec σi x : int_pre_cast_ok σi x → int_cast σi x = int_pre_cast σi x
}.

Section int_operations.
  Context `{IntEnv K}.

  Definition int_unop_type_of (op : unop) (τi : int_type K) : int_type K :=
    match op with NotOp => sintT | _ => int_promote τi end.
  Definition int_unop_ok (op : unop) (x : Z) (τi : int_type K) : Prop :=
    match op with NegOp => int_arithop_ok MinusOp 0 τi x τi | _ => True end.
  Definition int_unop (op : unop) (x : Z) (τi : int_type K) : Z :=
    match op with
    | NegOp => int_arithop MinusOp 0 τi x τi
    | ComplOp =>
       let τi' := int_promote τi in int_of_bits τi' (negb <$> int_to_bits τi' x)
    | NotOp => if decide (x = 0) then 1 else 0
    end.

  Definition int_binop_type_of (op : binop)
      (τi1 τi2 : int_type K) : int_type K :=
    match op with
    | CompOp _ => sintT
    | ArithOp _ | BitOp _ => int_promote τi1 ∪ int_promote τi2
    | ShiftOp _ => int_promote τi1
    end.
  Definition int_binop_ok (op : binop)
      (x1 : Z) (τi1 : int_type K) (x2 : Z) (τi2 : int_type K) : Prop :=
    match op with
    | (CompOp _ | BitOp _) => True
    | ArithOp op => int_arithop_ok op x1 τi1 x2 τi2
    | ShiftOp op => int_shiftop_ok op x1 τi1 x2 τi2
    end.
  Definition int_binop (op : binop)
      (x1 : Z) (τi1 : int_type K) (x2 : Z) (τi2 : int_type K) : Z :=
    match op with
    | CompOp op =>
       let τi' := int_promote τi1 ∪ int_promote τi2 in
       if decide (Z_comp op (int_cast τi' x1) (int_cast τi' x2)) then 1 else 0
    | ArithOp op => int_arithop op x1 τi1 x2 τi2
    | ShiftOp op => int_shiftop op x1 τi1 x2 τi2
    | BitOp op =>
       let τi' := int_promote τi1 ∪ int_promote τi2 in
       int_of_bits τi'
         (zip_with (bool_bitop op) (int_to_bits τi' x1) (int_to_bits τi' x2))
    end.
End int_operations.

Section pre_properties.
Context `{IntCodingSpec K}.
Implicit Types τi : int_type K.
Implicit Types k : K.
Implicit Types x y : Z.
Implicit Types n : nat.

Local Hint Resolve int_width_pos_alt int_width_pred_nonneg: core.
Local Hint Resolve int_lower_nonpos int_upper_pos int_mod_lower_upper: core.
Local Hint Resolve rank_size_preserving: core.

Lemma rank_size_union k1 k2 :
  (rank_size (k1 ∪ k2) : Z) = Z.max (rank_size k1) (rank_size k2).
Proof.
  unfold union, rank_union at 1; case_decide; [by rewrite Z.max_r by auto|].
  by rewrite Z.max_l by (by apply rank_size_preserving, total_not).
Qed.
Lemma rank_size_reflecting k1 k2 : rank_size k1 < rank_size k2 → k1 ⊂ k2.
Proof.
  intros. destruct (trichotomy (⊂) k1 k2) as [?|[->|[Hk _]]]; auto with lia.
  apply rank_size_preserving in Hk; lia.
Qed.
Lemma int_upper_le_invert_alt k1 k2 :
  int_upper (IntType Unsigned k1) ≤ int_upper (IntType Signed k2) → k1 ⊆ k2.
Proof. intros. apply rank_size_reflecting; auto using int_upper_le_invert. Qed.
Lemma rank_preserving τi1 τi2 : τi1 ⊆ τi2 → rank τi1 ⊆ rank τi2.
Proof. destruct 1; simpl; auto using int_upper_le_invert_alt. Qed.

Local Arguments int_promote _ _ !_ /.
Local Arguments union _ _ !_ !_ /.
Local Arguments int_union _ _ !_ !_ /.
Lemma int_promote_int si :
  int_promote (IntType si int_rank) = IntType si int_rank.
Proof.
  simpl; rewrite decide_True by done; destruct si.
  * by rewrite decide_True by done.
  * by rewrite decide_False by auto using Zlt_not_le, int_upper_signed_unsigned.
Qed.
Lemma int_promote_promote τi : int_promote (int_promote τi) = int_promote τi.
Proof.
  assert (int_upper sintT < int_upper uintT).
  { unfold int_upper. rewrite int_precision_Unsigned_Signed.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by auto with zpos.
    assert (0 < 2 ^ int_precision sintT) by auto with zpos. lia. }
  destruct τi as [si k]; simplify_option_eq; auto with lia.
Qed.
Lemma int_promote_typed x τi : int_typed x τi → int_typed x (int_promote τi).
Proof.
  destruct τi as [[] k]; simpl; intros; repeat case_decide;
    naive_solver eauto using int_typed_rank_weaken,
    int_typed_rank_strict_weaken, int_upper_le_invert, rank_le_upper.
Qed.
#[global] Instance: PartialOrder (⊆@{int_type K}).
Proof.
  repeat split.
  * by intros [[] ?]; constructor.
  * destruct 1; inversion 1; subst; constructor;
      eauto using (transitivity (R:=@subseteq K _)),
      Z.le_trans, rank_le_upper, int_upper_le_invert_alt.
  * destruct 1; inversion 1; subst.
    + by f_equal; apply (anti_symm (⊆)).
    + destruct (irreflexivity (⊂) k1); eapply strict_transitive_r,
        rank_size_reflecting, int_upper_le_invert; eauto.
    + destruct (irreflexivity (⊂) k2); eapply strict_transitive_r,
        rank_size_reflecting, int_upper_le_invert; eauto.
Qed.
#[global] Instance: JoinSemiLattice K.
Proof.
  split; try apply _;
    unfold union, rank_union; intros; case_decide; auto using (total_not (R := (⊆@{K}))).
Qed.
#[global] Instance: JoinSemiLattice (int_type K).
Proof.
  split; try apply _.
  * intros [[] k1] [[] k2]; simpl.
    + constructor. apply union_subseteq_l.
    + repeat case_decide; constructor; auto.
    + repeat case_decide; constructor; auto using (total_not (R := (⊆@{K}))).
    + constructor. apply union_subseteq_l.
  * intros [[] k1] [[] k2]; simpl.
    + constructor. apply union_subseteq_r.
    + repeat case_decide; constructor; auto using (total_not (R := (⊆@{K}))).
    + repeat case_decide; constructor; auto.
    + constructor. apply union_subseteq_r.
  * destruct 1; inversion 1; simplify_equality'.
    + case_match; constructor; eapply union_least; eauto.
    + repeat case_decide; constructor; auto.
    + repeat case_decide; constructor; auto with lia.
      eapply rank_lt_upper, Z.le_lt_trans; [|eauto using int_upper_le_invert].
      apply int_upper_le_invert_2; lia.
    + repeat case_decide; constructor; auto with lia.
    + constructor. eapply union_least; eauto.
    + repeat case_decide; constructor; auto with lia.
      eapply rank_lt_upper, Z.le_lt_trans; [|eauto using int_upper_le_invert].
      apply int_upper_le_invert_2; lia.
    + constructor. apply rank_lt_upper.
      rewrite rank_size_union. apply Z.max_lub_lt; auto using int_upper_le_invert.
Qed.

Lemma int_pre_arithop_typed op x y τi :
  int_typed x τi → int_typed y τi →
  int_pre_arithop_ok op x y τi → int_typed (int_pre_arithop op x y τi) τi.
Proof.
  unfold int_typed, int_pre_arithop_ok, int_pre_arithop.
  intros [??] [??]. destruct op.
  * destruct (sign τi); auto with lia.
  * destruct (sign τi); auto with lia.
  * destruct (sign τi); auto with lia.
  * intros Hy. unfold int_lower, int_upper in *. destruct (sign τi); [lia|].
    apply Z_quot_range_nonneg; auto with lia.
  * intros Hy. unfold int_lower, int_upper in *. destruct (sign τi).
    + generalize (Z.rem_bound_abs x y (proj1 Hy)). destruct (decide (0 < y)).
      - rewrite (Z.abs_eq y), Z.abs_lt by lia. lia.
      - rewrite (Z.abs_neq y), Z.abs_lt by lia. lia.
    + split; [apply Z.rem_bound_pos; lia|].
      transitivity y; auto. apply Z.rem_bound_pos; lia.
Qed.
Lemma int_pre_shiftop_typed op x y τi τi2 :
  int_typed x τi → int_typed y τi2 →
  int_pre_shiftop_ok op x y τi → int_typed (int_pre_shiftop op x y τi) τi.
Proof.
  unfold int_typed, int_pre_shiftop_ok, int_pre_shiftop.
  intros [??] [??]. destruct op.
  * destruct (sign τi); auto with lia. intros (?&[? _]&?). split; auto.
    rewrite Z.shiftl_mul_pow2 by done. transitivity 0; auto with zpos.
  * intros ?. assert (0 ≤ x ∧ 0 ≤ y) as [??].
    { unfold int_lower, int_upper in *. destruct (sign τi); auto with lia. }
    rewrite Z.shiftr_div_pow2 by done. split.
    { transitivity 0; auto. apply Z.div_pos; auto with zpos. }
    apply Z.le_lt_trans with x; auto.
    apply Z.div_le_upper_bound; auto with zpos.
    transitivity (1 * x); auto with lia.
    assert (0 < 2 ^ y) by auto with zpos.
    apply Z.mul_le_mono_nonneg_r; auto with zpos.
Qed.
Lemma int_pre_cast_typed x σi :
  int_pre_cast_ok σi x → int_typed (int_pre_cast σi x) σi.
Proof.
  unfold int_typed, int_pre_cast_ok, int_pre_cast.
  destruct (sign σi); auto with lia.
Qed.
Lemma int_typed_pre_cast_ok x σi : int_typed x σi → int_pre_cast_ok σi x.
Proof. unfold int_pre_cast_ok. by destruct (sign σi). Qed.
Lemma int_typed_pre_cast x σi : int_typed x σi → int_pre_cast σi x = x.
Proof.
  unfold int_pre_cast, int_typed, int_lower, int_upper.
  destruct (sign σi); auto using Z.mod_small.
Qed.
Lemma int_unsigned_pre_cast_ok x σi : sign σi = Unsigned → int_pre_cast_ok σi x.
Proof. unfold int_pre_cast_ok. by intros ->. Qed.
Lemma int_pre_cast_ok_subseteq x τi1 τi2 :
  int_typed x τi1 → τi1 ⊆ τi2 → int_pre_cast_ok τi2 x.
Proof.
  intros Hx; destruct 1; eauto using int_unsigned_pre_cast_ok,
    int_typed_pre_cast_ok, int_typed_rank_weaken.
  pose proof (int_lower_nonpos (IntType Signed k2)).
  destruct Hx as [Hxl Hxu]; rewrite int_lower_unsigned in Hxl; split; lia.
Qed.
Lemma int_pre_cast_ok_self x τi : int_typed x τi → int_pre_cast_ok τi x.
Proof. by unfold int_pre_cast_ok; destruct (sign _). Qed.
Lemma int_pre_cast_self x τi : int_typed x τi → int_pre_cast τi x = x.
Proof.
  unfold int_typed, int_lower, int_pre_cast;
    destruct (sign _); auto using Z.mod_small.
Qed.
End pre_properties.

Section properties.
Context `{IntEnvSpec K}.
Implicit Types τi : int_type K.
Implicit Types x y : Z.

Lemma int_unop_typed op x τi :
  int_typed x τi → int_unop_ok op x τi →
  int_typed (int_unop op x τi) (int_unop_type_of op τi).
Proof.
  unfold int_unop, int_unop_ok, int_unop_type_of; destruct op; intros.
  * rewrite <-(idemp_L (∪) (int_promote τi)).
    apply int_arithop_typed; auto. by apply int_typed_small.
  * apply int_of_bits_typed. by rewrite fmap_length, int_to_bits_length.
  * by apply int_typed_small; case_decide.
Qed.
Lemma int_binop_typed op x1 τi1 x2 τi2 :
  int_typed x1 τi1 → int_typed x2 τi2 → int_binop_ok op x1 τi1 x2 τi2 →
  int_typed (int_binop op x1 τi1 x2 τi2) (int_binop_type_of op τi1 τi2).
Proof.
  unfold int_binop, int_binop_ok, int_binop_type_of; destruct op; intros.
  * by apply int_typed_small; case_match.
  * by apply int_arithop_typed.
  * by apply int_shiftop_typed.
  * apply int_of_bits_typed. rewrite zip_with_length, !int_to_bits_length; lia.
Qed.
Lemma int_cast_ok_self x τi : int_typed x τi → int_cast_ok τi x.
Proof. eauto using int_cast_ok_more, int_pre_cast_ok_self. Qed.
Lemma int_cast_self x τi : int_typed x τi → int_cast τi x = x.
Proof.
  intros; rewrite int_cast_spec by eauto using int_pre_cast_ok_self.
  eauto using int_pre_cast_self.
Qed.
End properties.
