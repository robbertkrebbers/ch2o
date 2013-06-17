(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file describes an axiomatization of machine integers. *)
Require Import finite.
Require Export prelude.
Local Open Scope Z_scope.

(** * Operations *)
(** We define inductive data types [unop] and [binop] describing the operations
that can be performed on integers, and give denotations using mathematical
integers. These denotations are used in the axiomatization to describe the
operations on machine integers. *)
Inductive comp_kind := CEq | CLt | CLe.
Inductive unop := NegOp | ComplOp.
Inductive bitop := And | Or | Xor.
Inductive binop :=
  | PlusOp | MinusOp | MultOp | ShiftLOp | ShiftROp | DivOp | ModOp
  | CompOp : comp_kind → binop | BitOp : bitop → binop.
Notation EqOp := (CompOp CEq).
Notation LtOp := (CompOp CLt).
Notation LeOp := (CompOp CLe).
Notation AndOp := (BitOp And).
Notation OrOp := (BitOp Or).
Notation XorOp := (BitOp Xor).

Instance unop_dec (op1 op2 : unop) : Decision (op1 = op2).
Proof. solve_decision. Defined.
Instance comp_kind_dec (c1 c2 : comp_kind) : Decision (c1 = c2).
Proof. solve_decision. Defined.
Instance bitop_dec (op1 op2 : bitop) : Decision (op1 = op2).
Proof. solve_decision. Defined.
Instance binop_dec (op1 op2 : binop) : Decision (op1 = op2).
Proof. solve_decision. Defined.

Definition Z_comp (c : comp_kind) : Z → Z → Prop :=
  match c with CEq => (=) | CLt => (<) | CLe => (≤) end.
Instance Z_comp_dec c : ∀ x y, Decision (Z_comp c x y) :=
  match c return ∀ x y : Z, Decision (Z_comp c x y) with
  | CEq => decide_rel (=) | CLt => decide_rel (<) | CLe => decide_rel (≤)
  end.
Definition nat_comp (c : comp_kind) : nat → nat → Prop :=
  match c with CEq => (=) | CLt => (<) | CLe => (≤) end.
Instance nat_comp_dec c : ∀ x y, Decision (nat_comp c x y) :=
  match c return ∀ x y : nat, Decision (nat_comp c x y) with
  | CEq => decide_rel (=) | CLt => decide_rel (<) | CLe => decide_rel (≤)
  end.
Definition bool_bitop (op : bitop) : bool → bool → bool :=
  match op with And => andb | Or => orb | Xor => xorb end.

(** * The required operations on machine integers *)
(** The axiomatization of machine integers is parametrized by a type [Ti]
that represents the set of integer ranks (char, short, int). *)

(** We consider both signed and unsigned integers. Signed integers are an
interval between [-x] (included) and [x] of mathematical integers. Similarly,
unsigned integers are an interval between [0] (included) and [2 * x] of
mathematical integers. *)
Inductive signedness := Signed | Unsigned.
Instance signedness_eq_dec (s1 s2 : signedness) : Decision (s1 = s2).
Proof. solve_decision. Defined.

Inductive int_type (Ti : Set) := IntType { ISign : signedness; IKind : Ti }.
Add Printing Constructor int_type.
Delimit Scope int_type_scope with IT.
Bind Scope int_type_scope with int_type.
Arguments IntType {_} _ _.
Arguments ISign {_} _%IT.
Arguments IKind {_} _%IT.

Instance int_type_eq_dec {Ti : Set} `{∀ k1 k2 : Ti, Decision (k1 = k2)}
  (τ1 τ2 : int_type Ti) : Decision (τ1 = τ2).
Proof. solve_decision. Defined.

Local Unset Elimination Schemes.
Class IntCoding (Ti : Set) := {
  char_rank : Ti;
  int_rank : Ti;
  ptr_rank : Ti;
  char_bits : nat;
  rank_size : Ti → nat;
  endianize : Ti → list bool → list bool;
  deendianize : Ti → list bool → list bool
}.
Class IntEnv (Ti : Set) := {
  int_coding :>> IntCoding Ti;
  int_binop_ok : int_type Ti → binop → Z → Z → Prop;
  int_binop : int_type Ti → binop → Z → Z → Z;
  int_cast_ok : int_type Ti → Z → Prop;
  int_cast : int_type Ti → Z → Z;
  int_binop_ok_dec τ op x y :> Decision (int_binop_ok τ op x y);
  int_cast_ok_dec τ x :> Decision (int_cast_ok τ x);
  int_rank_eq_dec (k1 k2 : Ti) :> Decision (k1 = k2)
}.

Notation "'uchar'" := (IntType Unsigned char_rank) : int_type_scope.
Notation "'schar'" := (IntType Signed char_rank) : int_type_scope.
Notation "'uint'" := (IntType Unsigned int_rank) : int_type_scope.
Notation "'sint'" := (IntType Signed int_rank) : int_type_scope.
Notation "'uptr'" := (IntType Unsigned ptr_rank) : int_type_scope.
Notation "'sptr'" := (IntType Signed ptr_rank) : int_type_scope.

Arguments rank_size _ _ _ : simpl never.
Arguments char_rank _ _ : simpl never.
Arguments int_rank _ _ : simpl never.
Arguments ptr_rank _ _ : simpl never.
Arguments endianize _ _ _ _ : simpl never.
Arguments deendianize _ _ _ _ : simpl never.
Arguments int_binop_ok _ _ _ _ _ _ : simpl never.
Arguments int_binop _ _ _ _ _ _ : simpl never.
Arguments int_cast_ok _ _ _ _ : simpl never.
Arguments int_cast _ _ _ _ : simpl never.

Section least_operations.
  Context `{IntCoding Ti}.

  Definition int_size (τ : int_type Ti) : nat := rank_size (IKind τ).
  Global Arguments int_size !_ /.
  Definition int_bits (τ : int_type Ti) : nat := (int_size τ * char_bits)%nat.
  Definition int_lower (τ : int_type Ti) : Z :=
    match ISign τ with
    | Signed => -2 ^ (int_bits τ - 1)
    | Unsigned => 0
    end.
  Definition int_upper (τ : int_type Ti) : Z :=
    match ISign τ with
    | Signed => 2 ^ (int_bits τ - 1)
    | Unsigned => 2 ^ int_bits τ
    end.
  Definition int_typed (x : Z) (τ : int_type Ti) : Prop :=
    int_lower τ ≤ x < int_upper τ.

  Fixpoint Z_to_bits (n : nat) (x : Z) : list bool :=
    match n with
    | O => []
    | S n => bool_decide (x `mod` 2 = 1) :: Z_to_bits n (x `div` 2)
    end.
  Fixpoint Z_of_bits (bs : list bool) : Z :=
    match bs with
    | [] => 0
    | b :: bs => Z.b2z b + 2 * Z_of_bits bs
    end.

  Definition to_bits (τ : int_type Ti) (x : Z) : list bool :=
    endianize (IKind τ) $ Z_to_bits (int_bits τ) $
      match ISign τ with
      | Signed => if decide (0 ≤ x) then x else x + 2 ^ int_bits τ
      | Unsigned => x
      end.
  Definition of_bits (τ : int_type Ti) (bs : list bool) : Z :=
    let x := Z_of_bits (deendianize (IKind τ) bs) in
    match ISign τ with
    | Signed =>
       if decide (2 * x < 2 ^ int_bits τ) then x else x - 2 ^ int_bits τ
    | Unsigned => x
    end.

  Definition int_binop_ok_ (τ : int_type Ti)
      (op : binop) (x y : Z) : Prop :=
    match op, ISign τ with
    | PlusOp, Signed => int_lower τ ≤ x + y < int_upper τ
    | PlusOp, Unsigned => True
    | MinusOp, Signed => int_lower τ ≤ x - y < int_upper τ
    | MinusOp, Unsigned => True
    | MultOp, Signed => int_lower τ ≤ x * y < int_upper τ
    | MultOp, Unsigned => True
    | ShiftLOp, Signed => 0 ≤ x ∧ 0 ≤ y < int_bits τ ∧ x ≪ y < int_upper τ
    | ShiftLOp, Unsigned => y < int_bits τ
    | ShiftROp, Signed => 0 ≤ x ∧ 0 ≤ y < int_bits τ
    | ShiftROp, Unsigned => y < int_bits τ
      (* Can still overflow, e.g. [-10 `quot` -1 = 10]. Maybe a tighter
         condition is possible. *)
    | DivOp, Signed => y ≠ 0 ∧ int_lower τ ≤ x `quot` y < int_upper τ
    | DivOp, Unsigned => y ≠ 0
    | ModOp, _ => y ≠ 0
    | CompOp c, _ => True
    | BitOp _, _ => True
    end.
  Definition int_binop_ (τ : int_type Ti) (op : binop) (x y : Z) : Z :=
    match op, ISign τ with
    | PlusOp, Signed => x + y
    | PlusOp, Unsigned => (x + y) `mod` int_upper τ
    | MinusOp, Signed => x - y
    | MinusOp, Unsigned => (x - y) `mod` int_upper τ
    | MultOp, Signed => x * y
    | MultOp, Unsigned => (x * y) `mod` int_upper τ
    | ShiftLOp, Signed => x ≪ y
    | ShiftLOp, Unsigned => (x ≪ y) `mod` int_upper τ
    | ShiftROp, _ => x ≫ y
    | DivOp, _ => x `quot` y
    | ModOp, _ => x `rem` y
    | CompOp c, _ => Z_of_sumbool (decide_rel (Z_comp c) x y)
    | BitOp op, _ =>
       of_bits τ (zip_with (bool_bitop op) (to_bits τ x) (to_bits τ y))
    end.

  Definition int_cast_ok_ (σ : int_type Ti) (x : Z) :=
    match ISign σ with
    | Signed => int_lower σ ≤ x < int_upper σ
    | Unsigned => True
    end.
  Definition int_cast_ (σ : int_type Ti) (x : Z) :=
    match ISign σ with
    | Signed => x
    | Unsigned => x `mod` int_upper σ
    end.

  Global Instance int_binop_ok_dec_ τ op x y :
    Decision (int_binop_ok_ τ op x y).
  Proof. unfold int_binop_ok_. destruct op, (ISign τ); apply _. Qed.
  Global Instance int_cast_ok_dec_ σ x : Decision (int_cast_ok_ σ x).
  Proof. unfold int_cast_ok_. destruct (ISign σ); apply _. Qed.
End least_operations.

Section operations.
  Context `{IntEnv Ti}.

  Definition int_unop_ok (τ : int_type Ti) (op : unop) (x : Z) : Prop :=
    match op with NegOp => int_binop_ok τ MinusOp 0 x | ComplOp => True end.
  Definition int_unop (τ : int_type Ti) (op : unop) (x : Z) : Z :=
    match op with
    | NegOp => int_binop τ MinusOp 0 x
    | ComplOp => of_bits τ (negb <$> to_bits τ x)
    end.
End operations.

(** * The axiomatization of machine integers *)
(** The following class defines the laws that an implementation of machine
integers should satisfy. Most of these laws are straightforward. Keep in mind,
that like the C standard, overflow of unsigned integers is defined behavior
(namely, it wraps modulo), whereas overflow of signed integers is undefined
behavior. As [int_eval_unop], [int_eval_binop], and [int_cast], are partial
functions, an implementation is thus free to decide whether to yield a bogus
values, or to make the result actual undefined behavior (by returning
[None]). *)
Class IntCodingSpec Ti `{IntCoding Ti} := {
  char_bits_ge_8 : (8 ≤ char_bits)%nat;
  rank_size_char : rank_size char_rank = 1%nat;
  rank_size_pos k : (0 < rank_size k)%nat;

  endianize_permutation τ bs : endianize τ bs ≡ₚ bs;
  deendianize_endianize τ bs : deendianize τ (endianize τ bs) = bs;
  endianize_deendianize τ bs : endianize τ (deendianize τ bs) = bs
}.

Class IntEnvSpec Ti `{IntEnv Ti} := {
  int_coding_spec :>> IntCodingSpec Ti;

  int_binop_ok_more τ op x y :
    int_binop_ok_ τ op x y → int_binop_ok τ op x y;
  int_binop_ok_typed τ op x y :
    int_typed x τ → int_typed y τ →
    int_binop_ok τ op x y → int_typed (int_binop τ op x y) τ;
  int_binop_spec τ op x y :
    int_typed x τ → int_typed y τ → int_binop_ok_ τ op x y →
    int_binop τ op x y = int_binop_ τ op x y;

  int_cast_ok_more σ x : int_cast_ok_ σ x → int_cast_ok σ x;
  int_cast_ok_typed σ x : int_cast_ok σ x → int_typed (int_cast σ x) σ;
  int_cast_spec σ x : int_cast_ok_ σ x → int_cast σ x = int_cast_ σ x
}.

(** * Theorems *)
Lemma Z_to_bits_length n x : length (Z_to_bits n x) = n.
Proof. revert x. induction n; simpl; auto. Qed.
Lemma Z_to_of_bits bs : Z_to_bits (length bs) (Z_of_bits bs) = bs.
Proof.
  induction bs as [|[] bs IH]; simpl; try case_bool_decide as Hb; auto.
  * f_equal. by rewrite (Z.mul_comm 2), Z.div_add.
  * by rewrite (Z.mul_comm 2), Z.mod_add in Hb.
  * by rewrite (Z.mul_comm 2), Z.mod_add in Hb.
  * f_equal. by rewrite (Z.mul_comm 2), Z.div_add.
Qed.
Lemma Z_of_bits_range bs : 0 ≤ Z_of_bits bs < 2 ^ length bs.
Proof.
  induction bs as [|[] bs IH]; simpl; try case_bool_decide;
    rewrite ?Zpos_P_of_succ_nat, ?Z.pow_succ_r; auto with lia.
Qed.
Lemma Z_of_to_bits (n : nat) x : 0 ≤ x < 2 ^ n → Z_of_bits (Z_to_bits n x) = x.
Proof.
  revert x.
  induction n as [|n IH]; intros x; simpl; rewrite ?Zpos_P_of_succ_nat.
  { rewrite Z.pow_0_r; lia. }
  rewrite Z.pow_succ_r by auto with zpos. intros [??].
  rewrite IH by auto using Z.div_pos, Z.div_lt_upper_bound with lia.
  case_bool_decide as Hb; revert Hb; simpl.
  * rewrite Z.mod_eq by done; lia.
  * generalize (Z.mod_pos_bound x 2). rewrite Z.mod_eq; lia.
Qed.
Lemma Z_of_zero_bits n : Z_of_bits (replicate n false) = 0.
Proof. induction n; simpl; lia. Qed.

Section int_coding.
Context `{IntCodingSpec Ti}.
Implicit Types τ : int_type Ti.
Implicit Types k : Ti.
Implicit Types x y : Z.
Implicit Types n : nat.

Lemma deendianize_permutation k bs : deendianize k bs ≡ₚ bs.
Proof.
  rewrite <-(endianize_deendianize k bs) at 2. by rewrite endianize_permutation.
Qed.
Global Instance: Proper ((≡ₚ) ==> (≡ₚ)) (endianize k).
Proof. intros k bs1 bs2. by rewrite !endianize_permutation. Qed.
Global Instance: Injective (≡ₚ) (≡ₚ) (endianize k).
Proof. intros k bs1 bs2. by rewrite !endianize_permutation. Qed.
Global Instance: Proper ((≡ₚ) ==> (≡ₚ)) (deendianize k).
Proof. intros k bs1 bs2. by rewrite !deendianize_permutation. Qed.
Global Instance: Injective (≡ₚ) (≡ₚ) (deendianize k).
Proof. intros k bs1 bs2. by rewrite !deendianize_permutation. Qed.
Lemma endianize_length k bs : length (endianize k bs) = length bs.
Proof. by rewrite endianize_permutation. Qed.
Lemma deendianize_length k bs : length (deendianize k bs) = length bs.
Proof. by rewrite deendianize_permutation. Qed.

Lemma int_size_pos τ : (0 < int_size τ)%nat.
Proof. apply rank_size_pos. Qed.
Lemma int_size_ne_0 τ : (int_size τ ≠ 0)%nat.
Proof. apply Nat.neq_0_lt_0, rank_size_pos. Qed.
Lemma int_size_pos_alt τ : 0 < int_size τ.
Proof. apply (Nat2Z.inj_lt 0), rank_size_pos. Qed.

Lemma int_size_char si : int_size (IntType si char_rank) = 1%nat.
Proof. apply rank_size_char. Qed.
Lemma int_bits_char si : int_bits (IntType si char_rank) = char_bits.
Proof.
  unfold int_bits, int_size; simpl. by rewrite rank_size_char, Nat.mul_1_l.
Qed.
Lemma char_bits_pos : (0 < char_bits)%nat.
Proof. pose proof char_bits_ge_8; lia. Qed.
Lemma char_bits_ne_0 : char_bits ≠ 0%nat.
Proof. pose proof char_bits_ge_8; lia. Qed.
Lemma int_bits_ge_8 τ : (8 ≤ int_bits τ)%nat.
Proof.
  unfold int_bits. transitivity (1 * char_bits)%nat.
  * by rewrite char_bits_ge_8, Nat.mul_1_l.
  * apply Nat.mul_le_mono_r. generalize (int_size_pos τ); lia.
Qed.
Lemma int_bits_ge_8_alt τ : 8 ≤ int_bits τ.
Proof. apply (Nat2Z.inj_le 8), int_bits_ge_8. Qed.
Lemma int_bits_pos τ : (0 < int_bits τ)%nat.
Proof. pose proof (int_bits_ge_8 τ); lia. Qed.
Lemma int_bits_pos_alt τ : 0 < int_bits τ.
Proof. apply (Nat2Z.inj_lt 0), int_bits_pos. Qed.

Lemma int_bits_pred_nonneg τ : 0 ≤ int_bits τ - 1.
Proof. pose proof (int_bits_pos_alt τ); lia. Qed.
Hint Resolve int_bits_pos_alt int_bits_pred_nonneg.

Lemma int_typed_lower x τ : int_typed x τ → int_lower τ ≤ x.
Proof. by intros [??]. Qed.
Lemma int_typed_upper x τ : int_typed x τ → x < int_upper τ.
Proof. by intros [??]. Qed.

Lemma int_lower_u τ : ISign τ = Unsigned → int_lower τ = 0.
Proof. by destruct τ as [[]?]. Qed.
Lemma int_lower_nonpos τ : int_lower τ ≤ 0.
Proof.
  unfold int_lower. destruct (ISign τ); [|done].
  apply Z.opp_nonpos_nonneg; auto with zpos.
Qed.
Lemma int_upper_pos τ : 0 < int_upper τ.
Proof. unfold int_upper. destruct (ISign τ); auto with zpos. Qed.
Hint Resolve int_lower_nonpos int_upper_pos.

Lemma int_mod_lower_upper x τ :
  int_lower τ ≤ x `mod` int_upper τ < int_upper τ.
Proof.
  split.
  * transitivity 0; auto. apply Z.mod_pos_bound; auto.
  * apply Z.mod_pos_bound; auto.
Qed.
Hint Resolve int_mod_lower_upper.
Lemma int_upper_lower τ : int_upper τ = 2 ^ int_bits τ + int_lower τ.
Proof.
  unfold int_upper, int_lower. destruct τ as [[] k]; simpl.
  * apply (Z.mul_cancel_l _ _ 2); [done |]. rewrite Z.mul_add_distr_l,
      Z.mul_opp_r, !Z.sub_1_r, !Z_pow_pred_r; auto with zpos.
  * lia.
Qed.

Lemma int_typed_spec_alt x τ :
  int_typed x τ ↔
    match ISign τ with
    | Signed => -2 ^ int_bits τ ≤ 2 * x < 2 ^ int_bits τ
    | Unsigned => 0 ≤ x < 2 ^ int_bits τ
    end.
Proof.
  unfold int_typed, int_lower, int_upper.
  destruct τ as [[] k]; simpl; [|done].
  rewrite (Z.mul_lt_mono_pos_l 2 x), (Z.mul_le_mono_pos_l _ _ 2) by done.
  by rewrite Z.mul_opp_r, Z.sub_1_r, Z_pow_pred_r by auto.
Qed.
Lemma int_typed_nonneg_signed x τ :
  0 ≤ 2 * x < 2 ^ int_bits τ → int_typed x τ.
Proof. rewrite int_typed_spec_alt. destruct (ISign _); lia. Qed.
Lemma int_typed_small x τ : 0 ≤ x < 128 → int_typed x τ.
Proof.
  intros [??]. apply int_typed_nonneg_signed. split; [lia|].
  apply Z.lt_le_trans with (2 ^ 8); [lia |].
  by apply Z.pow_le_mono_r; auto using int_bits_ge_8_alt.
Qed.
Lemma to_bits_length τ x : length (to_bits τ x) = int_bits τ.
Proof.
  unfold to_bits, int_bits. rewrite endianize_permutation.
  by destruct τ as [[] k]; simpl; rewrite Z_to_bits_length.
Qed.
Lemma to_of_bits τ bs :
  length bs = int_bits τ → to_bits τ (of_bits τ bs) = bs.
Proof.
  intros Hlen. unfold to_bits, of_bits.
  rewrite <-!Hlen, <-!(deendianize_length (IKind τ) bs); clear Hlen.
  pose proof (Z_of_bits_range (deendianize (IKind τ) bs)).
  destruct τ as [[] k]; simpl in *.
  * repeat case_decide; auto with lia.
    + by rewrite Z_to_of_bits, endianize_deendianize.
    + rewrite <-Z.sub_sub_distr, Z.sub_diag, Z.sub_0_r.
      by rewrite Z_to_of_bits, endianize_deendianize.
  * by rewrite Z_to_of_bits, endianize_deendianize.
Qed.
Lemma of_bits_inj τ bs1 bs2 :
  length bs1 = int_bits τ → length bs2 = int_bits τ →
  of_bits τ bs1 = of_bits τ bs2 →  bs1 = bs2.
Proof.
  intros. rewrite <-(to_of_bits τ bs1),
    <-(to_of_bits τ bs2) by done; congruence.
Qed.

Lemma of_bits_typed τ bs : length bs = int_bits τ → int_typed (of_bits τ bs) τ.
Proof.
  intros Hlen. unfold of_bits. generalize (int_bits_pos τ).
  generalize (Z_of_bits_range (deendianize (IKind τ) bs)).
  rewrite int_typed_spec_alt, <-!Hlen, <-!(deendianize_length (IKind τ) bs).
  destruct τ as [[] k]; simpl; repeat case_decide; auto with lia.
Qed.
Lemma of_to_bits τ x : int_typed x τ → of_bits τ (to_bits τ x) = x.
Proof.
  unfold of_bits, to_bits. rewrite int_typed_spec_alt.
  destruct τ as [[] k]; simpl in *.
  * intros [??]. repeat case_decide; repeat_on_hyps
      (fun H => rewrite deendianize_endianize, !Z_of_to_bits in H by lia);
      rewrite deendianize_endianize, Z_of_to_bits; lia.
  * intros [??]. by rewrite deendianize_endianize, Z_of_to_bits.
Qed.

Lemma of_zero_bits τ : of_bits τ (replicate (int_bits τ) false) = 0.
Proof.
  assert (∀ k n b, deendianize k (replicate n b) = replicate n b) as Hrepl.
  { intros k n b. apply replicate_Permutation.
    by rewrite deendianize_permutation. }
  unfold of_bits. destruct (ISign τ).
  * case_decide as Hbs.
    { by rewrite Hrepl, Z_of_zero_bits. }
    destruct Hbs. rewrite Hrepl, Z_of_zero_bits, Z.mul_0_r. auto with zpos.
  * by rewrite Hrepl, Z_of_zero_bits.
Qed.
Lemma to_bits_signed_unsigned k x :
  0 ≤ x → to_bits (IntType Signed k) x = to_bits (IntType Unsigned k) x.
Proof. unfold to_bits; simpl; case_decide; auto with lia. Qed.

Lemma int_binop_ok_typed_ τ op x y :
  int_typed x τ → int_typed y τ →
  int_binop_ok_ τ op x y → int_typed (int_binop_ τ op x y) τ.
Proof.
  unfold int_typed, int_binop_ok_, int_binop_. intros [??] [??]. destruct op.
  * destruct (ISign τ); auto with lia.
  * destruct (ISign τ); auto with lia.
  * destruct (ISign τ); auto with lia.
  * destruct (ISign τ); auto with lia.
    intros (?&[? _]&?). split; auto.
    rewrite Z.shiftl_mul_pow2 by done. transitivity 0; auto with zpos.
  * intros ?. assert (0 ≤ x ∧ 0 ≤ y) as [??].
    { unfold int_lower, int_upper in *. destruct (ISign τ); auto with lia. }
    rewrite Z.shiftr_div_pow2 by done. split.
    + transitivity 0; auto. apply Z.div_pos; auto with zpos.
    + apply Z.le_lt_trans with x; auto.
      apply Z.div_le_upper_bound; auto with zpos.
      transitivity (1 * x); auto with lia.
      apply Z.mul_le_mono_nonneg_r; auto with zpos.
      assert (0 < 2 ^ y); auto with zpos.
  * intros Hy. unfold int_lower, int_upper in *. destruct (ISign τ).
    + lia.
    + apply Z_quot_range_nonneg; auto with lia.
  * intros Hy. unfold int_lower, int_upper in *. destruct (ISign τ).
    + generalize (Z.rem_bound_abs x y Hy). destruct (decide (0 < y)).
      - rewrite (Z.abs_eq y), Z.abs_lt by lia. lia.
      - rewrite (Z.abs_neq y), Z.abs_lt by lia. lia.
    + split.
      - apply Z.rem_bound_pos; lia.
      - transitivity y; auto. apply Z.rem_bound_pos; lia.
  * intros _. by case_decide; apply int_typed_small.
  * intros ?. apply of_bits_typed.
    by rewrite zip_with_length; rewrite !to_bits_length.
Qed.
Lemma int_cast_ok_typed_ σ x :
  int_cast_ok_ σ x → int_typed (int_cast_ σ x) σ.
Proof.
  unfold int_typed, int_cast_ok_, int_cast_.
  destruct (ISign σ); auto with lia.
Qed.
End int_coding.

Section int_env.
Context `{IntEnvSpec Ti}.

Lemma int_unop_ok_typed op x τ :
  int_typed x τ → int_unop_ok τ op x → int_typed (int_unop τ op x) τ.
Proof.
  destruct op; simpl.
  * intros. apply int_binop_ok_typed; auto. by apply int_typed_small.
  * intros. apply of_bits_typed. by rewrite fmap_length, to_bits_length.
Qed.
End int_env.
