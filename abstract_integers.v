(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file describes an abstract interface to capture different
implementations of machine integers. It deals with integer representations and
the underspecification of integer operations by the C standard. The majority of
our subsequent Coq development is parametrized by this interface. *)

(** Compared to the C standard we make some changes. First of all, since all
modern architectures use two's complement representation, we allow
representations to differ solely in endianness. Secondly, to keep the interface
abstract, we only require three integer ranks to be present (char, int,
ptr_diff/size_t), and put few restrictions on the range of these integer
ranks. *)
Require Import finite.
Require Export prelude.
Local Open Scope Z_scope.

(** * Syntax of integer operations *)
(** The inductive types [unop] and [binop] describe the abstract syntax of the
C integer operations. *)
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

Instance comp_kind_dec (op1 op2 : compop) : Decision (op1 = op2).
Proof. solve_decision. Defined.
Instance bitop_dec (op1 op2 : bitop) : Decision (op1 = op2).
Proof. solve_decision. Defined.
Instance arithop_dec (op1 op2 : arithop) : Decision (op1 = op2).
Proof. solve_decision. Defined.
Instance shiftop_dec (op1 op2 : shiftop) : Decision (op1 = op2).
Proof. solve_decision. Defined.
Instance binop_dec (op1 op2 : binop) : Decision (op1 = op2).
Proof. solve_decision. Defined.
Instance unop_dec (op1 op2 : unop) : Decision (op1 = op2).
Proof. solve_decision. Defined.

Definition Z_comp (c : compop) (x y : Z) : bool :=
  match c with
  | EqOp => bool_decide (x = y)
  | LtOp => bool_decide (x < y)
  | LeOp => bool_decide (x ≤ y)
  end.
Definition bool_bitop (op : bitop) : bool → bool → bool :=
  match op with AndOp => (&&) | OrOp => (||) | XorOp => xorb end.

(** * Operations on machine integers *)
(** The abstract interface for machine integers is parametrized by a type [Ti]
of integer ranks (char, short, int). Integer types consist of a rank and its
signedness (signed/unsigned), and machine integers are just arbitrary precision
integers [Z] that should be within the range of the corresponding type. *)
Inductive signedness := Signed | Unsigned.
Instance signedness_eq_dec (s1 s2 : signedness) : Decision (s1 = s2).
Proof. solve_decision. Defined.

Inductive int_type (Ti : Set) := IntType { sign : signedness; rank : Ti }.
Add Printing Constructor int_type.
Delimit Scope int_type_scope with IT.
Bind Scope int_type_scope with int_type.
Arguments IntType {_} _ _.
Arguments sign {_} _%IT.
Arguments rank {_} _%IT.

Instance int_type_eq_dec {Ti : Set} `{∀ k1 k2 : Ti, Decision (k1 = k2)}
  (τ1 τ2 : int_type Ti) : Decision (τ1 = τ2).
Proof. solve_decision. Defined.

(** The class [IntCoding] describes functions related to representation and
sizes of machine integers. The rank [char_rank] is the rank of the smallest
available integer type, and [ptr_rank] the rank of the types size_t and
ptrdiff_t. At an actual machine, integers of rank [char_rank] corresponds to a
byte, and its bit size is [char_bits] (called CHAR_BIT in the C header
files). *)

(** The function [rank_size k] gives the byte size of an integer with rank [k].
Since we restrict to two's complement, signed integers of rank [k] are between
[-int_rank k] (included) and [int_rank k], and unsigned integers of rank [k]
are between [0] (included) and [2 * int_rank k]. The operation [endianize]
takes a list of bits in little endian order and permutes them according to the
implementation's endianness. The function [deendianize] performs the inverse. *)
Local Unset Elimination Schemes.
Class IntCoding (Ti : Set) := {
  char_rank : Ti;
  char_signedness : signedness;
  short_rank : Ti;
  int_rank : Ti;
  long_rank : Ti;
  longlong_rank : Ti;
  ptr_rank : Ti;
  char_bits : nat;
  rank_size : Ti → nat;
  endianize : Ti → list bool → list bool;
  deendianize : Ti → list bool → list bool;
  int_rank_eq_dec (k1 k2 : Ti) :> Decision (k1 = k2)
}.

Arguments char_rank _ _ : simpl never.
Arguments char_signedness _ _ : simpl never.
Arguments short_rank _ _ : simpl never.
Arguments int_rank _ _ : simpl never.
Arguments long_rank _ _ : simpl never.
Arguments longlong_rank _ _ : simpl never.
Arguments ptr_rank _ _ : simpl never.
Arguments char_bits _ _ : simpl never.
Arguments rank_size _ _ _ : simpl never.
Arguments endianize _ _ _ _ : simpl never.
Arguments deendianize _ _ _ _ : simpl never.
Arguments int_rank_eq_dec _ _ _ _ : simpl never.

Notation "'ucharT'" := (IntType Unsigned char_rank) : int_type_scope.
Notation "'scharT'" := (IntType Signed char_rank) : int_type_scope.
Notation "'uintT'" := (IntType Unsigned int_rank) : int_type_scope.
Notation "'sintT'" := (IntType Signed int_rank) : int_type_scope.
Notation "'uptrT'" := (IntType Unsigned ptr_rank) : int_type_scope.
Notation "'sptrT'" := (IntType Signed ptr_rank) : int_type_scope.

(** * The abstract interface for machine integers *)
(** In order to declare classes to describe the laws of an implementation of
machine integers, we first define functions to encode and decode integers, and
functions to relate binary operations and casts to its specification. *)
Section int_coding.
  Context `{IntCoding Ti}.

  Definition int_bits (τ : int_type Ti) : nat :=
    (rank_size (rank τ) * char_bits)%nat.
  Definition int_lower (τ : int_type Ti) : Z :=
    match sign τ with Signed => -2 ^ (int_bits τ - 1) | Unsigned => 0 end.
  Definition int_upper (τ : int_type Ti) : Z :=
    match sign τ with
    | Signed => 2 ^ (int_bits τ - 1) | Unsigned => 2 ^ int_bits τ
    end.
  Definition int_typed (x : Z) (τ : int_type Ti) : Prop :=
    int_lower τ ≤ x < int_upper τ.
  Global Instance int_typed_dec x τ : Decision (int_typed x τ) := _.

  Fixpoint Z_to_bits (n : nat) (x : Z) : list bool :=
    match n with
    | O => [] | S n => bool_decide (x `mod` 2 = 1) :: Z_to_bits n (x `div` 2)
    end.
  Fixpoint Z_of_bits (bs : list bool) : Z :=
    match bs with [] => 0 | b :: bs => Z.b2z b + 2 * Z_of_bits bs end.

  Definition int_to_bits (τ : int_type Ti) (x : Z) : list bool :=
    endianize (rank τ) $ Z_to_bits (int_bits τ) $
      match sign τ with
      | Signed => if decide (0 ≤ x) then x else x + 2 ^ int_bits τ
      | Unsigned => x
      end.
  Definition int_of_bits (τ : int_type Ti) (bs : list bool) : Z :=
    let x := Z_of_bits (deendianize (rank τ) bs) in
    match sign τ with
    | Signed =>
       if decide (2 * x < 2 ^ int_bits τ) then x else x - 2 ^ int_bits τ
    | Unsigned => x
    end.

  Definition int_pre_arithop_ok
      (op : arithop) (x y : Z) (τ : int_type Ti) : Prop :=
    match op, sign τ with
    | PlusOp, Signed => int_lower τ ≤ x + y < int_upper τ
    | PlusOp, Unsigned => True
    | MinusOp, Signed => int_lower τ ≤ x - y < int_upper τ
    | MinusOp, Unsigned => True
    | MultOp, Signed => int_lower τ ≤ x * y < int_upper τ
    | MultOp, Unsigned => True
      (* Can still overflow, e.g. [-10 `quot` -1 = 10]. Maybe a tighter
         condition is possible. *)
    | (DivOp | ModOp), Signed =>
       y ≠ 0 ∧ int_lower τ ≤ x `quot` y < int_upper τ
    | (DivOp | ModOp), Unsigned => y ≠ 0
    end.
  Definition int_pre_arithop (op : arithop) (x y : Z) (τ : int_type Ti) : Z :=
    match op, sign τ with
    | PlusOp, Signed => x + y
    | PlusOp, Unsigned => (x + y) `mod` int_upper τ
    | MinusOp, Signed => x - y
    | MinusOp, Unsigned => (x - y) `mod` int_upper τ
    | MultOp, Signed => x * y
    | MultOp, Unsigned => (x * y) `mod` int_upper τ
    | DivOp, _ => x `quot` y
    | ModOp, _ => x `rem` y
    end.
  Definition int_pre_shiftop_ok
      (op : shiftop) (x y : Z) (τ : int_type Ti) : Prop :=
    match op, sign τ with
    | ShiftLOp, Signed => 0 ≤ x ∧ 0 ≤ y < int_bits τ ∧ x ≪ y < int_upper τ
    | ShiftLOp, Unsigned => 0 ≤ y < int_bits τ
    | ShiftROp, Signed => 0 ≤ x ∧ 0 ≤ y < int_bits τ
    | ShiftROp, Unsigned => 0 ≤ y < int_bits τ
    end.
  Definition int_pre_shiftop (op : shiftop) (x y : Z) (τ : int_type Ti) : Z :=
    match op, sign τ with
    | ShiftLOp, Signed => x ≪ y
    | ShiftLOp, Unsigned => (x ≪ y) `mod` int_upper τ
    | ShiftROp, _ => x ≫ y
    end.
  Definition int_pre_cast_ok (σ : int_type Ti) (x : Z) :=
    match sign σ with
    | Signed =>
       (**i actually implementation defined, see 6.3.1.3 *)
       int_lower σ ≤ x < int_upper σ
    | Unsigned => True
    end.
  Definition int_pre_cast (σ : int_type Ti) (x : Z) :=
    match sign σ with Signed => x | Unsigned => x `mod` int_upper σ end.

  Global Instance int_pre_arithop_ok_dec op x y τ :
    Decision (int_pre_arithop_ok op x y τ).
  Proof. unfold int_pre_arithop_ok. destruct op, (sign τ); apply _. Defined.
  Global Instance int_pre_shiftop_ok_dec op x y τ :
    Decision (int_pre_shiftop_ok op x y τ).
  Proof. unfold int_pre_shiftop_ok. destruct op, (sign τ); apply _. Defined.
  Global Instance int_pre_cast_ok_dec σ x : Decision (int_pre_cast_ok σ x).
  Proof. unfold int_pre_cast_ok. destruct (sign σ); apply _. Defined.

  Definition int_promote (τ : int_type Ti) : int_type Ti :=
    if decide (rank_size (rank τ) < rank_size int_rank)
    then sintT%IT else τ.
  Global Instance int_union : Union (int_type Ti) := λ τ1 τ2,
    if decide (rank_size (rank τ1) < rank_size (rank τ2)) then τ2
    else if decide (rank_size (rank τ2) < rank_size (rank τ1)) then τ1
    else if decide (sign τ1 = Unsigned) then τ1 else τ2.
End int_coding.
Typeclasses Opaque int_typed.

(** The classes [IntCodingSpec] describe the laws that an implementation of
machine integers should satisfy with respect to representatons. *)
Class IntCodingSpec Ti `{IntCoding Ti} := {
  char_bits_ge_8 : (8 ≤ char_bits)%nat;
  rank_size_char : rank_size char_rank = 1%nat;
  rank_size_pos k : (0 < rank_size k)%nat;
  rank_size_injective :> Injective (=) (=) rank_size;
  endianize_permutation k bs : endianize k bs ≡ₚ bs;
  deendianize_endianize k bs : deendianize k (endianize k bs) = bs;
  endianize_deendianize k bs : endianize k (deendianize k bs) = bs
}.

(** In order to deal with underspecification of operations, the class [IntEnv]
does not just contain a function [int_binop] to perform a binary operation, but
also a predicate [int_binop_ok τ op x y] that describes when [op] is allowed to
be performed on integers [x] and [y] of type [τ]. This is to allow both strict
implementations that make integer overflow undefined, and those that let it
wrap (as for example GCC with the -fno-strict-overflow flag does). When an
operation is allowed by the C standard, the result of [int_binop τ op x y]
should correspond to its specification by the standard. *)
Class IntEnv (Ti : Set) := {
  int_coding :> IntCoding Ti;
  int_arithop_ok : arithop → Z → int_type Ti → Z → int_type Ti → Prop;
  int_arithop : arithop → Z → int_type Ti → Z → int_type Ti → Z;
  int_shiftop_ok : shiftop → Z → int_type Ti → Z → int_type Ti → Prop;
  int_shiftop : shiftop → Z → int_type Ti → Z → int_type Ti → Z;
  int_cast_ok : int_type Ti → Z → Prop;
  int_cast : int_type Ti → Z → Z;
  int_arithop_ok_dec op x τ1 y τ2 :> Decision (int_arithop_ok op x τ1 y τ2);
  int_shiftop_ok_dec op x τ1 y τ2 :> Decision (int_shiftop_ok op x τ1 y τ2);
  int_cast_ok_dec σ x :> Decision (int_cast_ok σ x)
}.
Arguments int_arithop_ok _ _ _ _ _ _ _ : simpl never.
Arguments int_arithop _ _ _ _ _ _ _ : simpl never.
Arguments int_shiftop_ok _ _ _ _ _ _ _ : simpl never.
Arguments int_shiftop _ _ _ _ _ _ _ : simpl never.
Arguments int_cast_ok _ _ _ _ : simpl never.
Arguments int_cast _ _ _ _ : simpl never.

Class IntEnvSpec Ti `{IntEnv Ti} := {
  int_coding_spec :>> IntCodingSpec Ti;
  int_arithop_ok_more op x y τ1 τ2 :
    int_typed x τ1 → int_typed y τ2 →
    let τ' := int_promote τ1 ∪ int_promote τ2 in
    int_pre_arithop_ok op (int_pre_cast τ' x) (int_pre_cast τ' y) τ' →
    int_arithop_ok op x τ1 y τ2;
  int_arithop_typed op x y τ1 τ2 :
    int_typed x τ1 → int_typed y τ2 →
    int_arithop_ok op x τ1 y τ2 →
    int_typed (int_arithop op x τ1 y τ2) (int_promote τ1 ∪ int_promote τ2);
  int_arithop_spec op x y τ1 τ2 :
    int_typed x τ1 → int_typed y τ2 →
    let τ' := int_promote τ1 ∪ int_promote τ2 in
    int_pre_arithop_ok op (int_pre_cast τ' x) (int_pre_cast τ' y) τ' →
    int_arithop op x τ1 y τ2
    = int_pre_arithop op (int_pre_cast τ' x) (int_pre_cast τ' y) τ';
  int_shiftop_ok_more op x y τ1 τ2 :
    int_typed x τ1 → int_typed y τ2 →
    let τ' := int_promote τ1 in
    int_pre_shiftop_ok op (int_pre_cast τ' x) y τ' →
    int_shiftop_ok op x τ1 y τ2;
  int_shiftop_typed op x y τ1 τ2 :
    int_typed x τ1 → int_typed y τ2 → int_shiftop_ok op x τ1 y τ2 →
    int_typed (int_shiftop op x τ1 y τ2) (int_promote τ1);
  int_shiftop_spec op x y τ1 τ2 :
    int_typed x τ1 → int_typed y τ2 →
    let τ' := int_promote τ1 in
    int_pre_shiftop_ok op x y τ' →
    int_shiftop op x τ1 y τ2 = int_pre_shiftop op x y τ';
  int_cast_ok_more σ x : int_pre_cast_ok σ x → int_cast_ok σ x;
  int_cast_typed σ x : int_cast_ok σ x → int_typed (int_cast σ x) σ;
  int_cast_spec σ x : int_pre_cast_ok σ x → int_cast σ x = int_pre_cast σ x
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

Section properties.
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

Lemma rank_size_ne_0 k : (rank_size k ≠ 0)%nat.
Proof. apply Nat.neq_0_lt_0, rank_size_pos. Qed.
Lemma int_bits_char si : int_bits (IntType si char_rank) = char_bits.
Proof. unfold int_bits; simpl. by rewrite rank_size_char, Nat.mul_1_l. Qed.
Lemma char_bits_pos : (0 < char_bits)%nat.
Proof. pose proof char_bits_ge_8; lia. Qed.
Lemma char_bits_ne_0 : char_bits ≠ 0%nat.
Proof. pose proof char_bits_ge_8; lia. Qed.
Lemma int_bits_ge_8 τ : (8 ≤ int_bits τ)%nat.
Proof.
  unfold int_bits. transitivity (1 * char_bits)%nat.
  * by rewrite char_bits_ge_8, Nat.mul_1_l.
  * apply Nat.mul_le_mono_r. generalize (rank_size_pos (rank τ)); lia.
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
Lemma int_lower_u τ : sign τ = Unsigned → int_lower τ = 0.
Proof. by destruct τ as [[]?]. Qed.
Lemma int_lower_nonpos τ : int_lower τ ≤ 0.
Proof.
  unfold int_lower. destruct (sign τ); [|done].
  apply Z.opp_nonpos_nonneg; auto with zpos.
Qed.
Lemma int_upper_pos τ : 0 < int_upper τ.
Proof. unfold int_upper. destruct (sign τ); auto with zpos. Qed.
Hint Resolve int_lower_nonpos int_upper_pos.
Lemma int_mod_lower_upper x τ :
  int_lower τ ≤ x `mod` int_upper τ < int_upper τ.
Proof.
  split; [transitivity 0; auto; apply Z.mod_pos_bound; auto|].
  apply Z.mod_pos_bound; auto.
Qed.
Hint Resolve int_mod_lower_upper.
Lemma int_upper_lower τ : int_upper τ = 2 ^ int_bits τ + int_lower τ.
Proof.
  unfold int_upper, int_lower. destruct τ as [[] k]; simpl; [|lia].
  apply (Z.mul_cancel_l _ _ 2); [done |]. rewrite Z.mul_add_distr_l,
    Z.mul_opp_r, !Z.sub_1_r, !Z_pow_pred_r; auto with zpos.
Qed.
Lemma int_lower_upper_signed τ : sign τ = Signed → int_lower τ = -int_upper τ.
Proof. by intros; destruct τ; simplify_equality'. Qed.
Lemma int_typed_spec_alt x τ :
  int_typed x τ ↔
    match sign τ with
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
Proof. rewrite int_typed_spec_alt. destruct (sign _); lia. Qed.
Lemma int_typed_small x τ : 0 ≤ x < 128 → int_typed x τ.
Proof.
  intros [??]. apply int_typed_nonneg_signed. split; [lia|].
  apply Z.lt_le_trans with (2 ^ 8); [lia |].
  by apply Z.pow_le_mono_r; auto using int_bits_ge_8_alt.
Qed.
Lemma int_to_bits_length τ x : length (int_to_bits τ x) = int_bits τ.
Proof.
  unfold int_to_bits, int_bits. rewrite endianize_permutation.
  by destruct τ as [[] k]; simpl; rewrite Z_to_bits_length.
Qed.
Lemma int_to_of_bits τ bs :
  length bs = int_bits τ → int_to_bits τ (int_of_bits τ bs) = bs.
Proof.
  intros Hlen. unfold int_to_bits, int_of_bits.
  rewrite <-!Hlen, <-!(deendianize_length (rank τ) bs); clear Hlen.
  pose proof (Z_of_bits_range (deendianize (rank τ) bs)).
  destruct τ as [[] k]; simpl in *.
  * repeat case_decide; auto with lia.
    + by rewrite Z_to_of_bits, endianize_deendianize.
    + rewrite <-Z.sub_sub_distr, Z.sub_diag, Z.sub_0_r.
      by rewrite Z_to_of_bits, endianize_deendianize.
  * by rewrite Z_to_of_bits, endianize_deendianize.
Qed.
Lemma int_of_bits_inj τ bs1 bs2 :
  length bs1 = int_bits τ → length bs2 = int_bits τ →
  int_of_bits τ bs1 = int_of_bits τ bs2 →  bs1 = bs2.
Proof.
  intros. rewrite <-(int_to_of_bits τ bs1),
    <-(int_to_of_bits τ bs2) by done; congruence.
Qed.
Lemma int_of_bits_typed τ bs :
  length bs = int_bits τ → int_typed (int_of_bits τ bs) τ.
Proof.
  intros Hlen. unfold int_of_bits. generalize (int_bits_pos τ).
  generalize (Z_of_bits_range (deendianize (rank τ) bs)).
  rewrite int_typed_spec_alt, <-!Hlen, <-!(deendianize_length (rank τ) bs).
  destruct τ as [[] k]; simpl; repeat case_decide; auto with lia.
Qed.
Lemma int_of_to_bits τ x : int_typed x τ → int_of_bits τ (int_to_bits τ x) = x.
Proof.
  unfold int_of_bits, int_to_bits. rewrite int_typed_spec_alt.
  destruct τ as [[] k]; simpl in *.
  * intros [??]. repeat case_decide; repeat_on_hyps
      (fun H => rewrite deendianize_endianize, !Z_of_to_bits in H by lia);
      rewrite deendianize_endianize, Z_of_to_bits; lia.
  * intros [??]. by rewrite deendianize_endianize, Z_of_to_bits.
Qed.
Lemma int_of_zero_bits τ : int_of_bits τ (replicate (int_bits τ) false) = 0.
Proof.
  assert (∀ k n b, deendianize k (replicate n b) = replicate n b) as Hrepl.
  { intros k n b. symmetry. apply replicate_Permutation.
    by rewrite deendianize_permutation. }
  unfold int_of_bits. destruct (sign τ).
  * case_decide as Hbs; [by rewrite Hrepl, Z_of_zero_bits |].
    destruct Hbs. rewrite Hrepl, Z_of_zero_bits, Z.mul_0_r. auto with zpos.
  * by rewrite Hrepl, Z_of_zero_bits.
Qed.
Lemma int_to_bits_signed_unsigned k x :
  0 ≤ x → int_to_bits (IntType Signed k) x = int_to_bits (IntType Unsigned k) x.
Proof. unfold int_to_bits; simpl; case_decide; auto with lia. Qed.
Lemma int_lower_lt_upper τi : int_lower τi < int_upper τi.
Proof.
  rewrite int_upper_lower. assert (0 < 2 ^ int_bits τi) by auto with zpos; lia.
Qed.
Lemma int_lower_typed τi : int_typed (int_lower τi) τi.
Proof. pose proof (int_lower_lt_upper τi). split; lia. Qed.
Lemma int_upper_typed τi : int_typed (int_upper τi - 1) τi.
Proof. pose proof (int_lower_lt_upper τi). split; lia. Qed.
Lemma int_bits_typed τi : int_typed (int_bits τi) τi.
Proof.
  split; [transitivity 0; auto with zpos|].
  unfold int_upper; destruct (sign _); [|apply Z.pow_gt_lin_r; lia].
  pose proof (int_bits_ge_8 τi) as Hτi; replace (int_bits τi : Z)
    with (Z.succ (Z.succ (Z.succ (int_bits τi - 3)%nat))) by lia; clear Hτi.
  rewrite Z.sub_1_r, Z.pred_succ.
  induction (int_bits τi - 3)%nat as [|n IH]; [done|].
  rewrite !Nat2Z.inj_succ, Z.pow_succ_r by auto with zpos; lia.
Qed.
Lemma int_pre_arithop_typed op x y τ :
  int_typed x τ → int_typed y τ →
  int_pre_arithop_ok op x y τ → int_typed (int_pre_arithop op x y τ) τ.
Proof.
  unfold int_typed, int_pre_arithop_ok, int_pre_arithop.
  intros [??] [??]. destruct op.
  * destruct (sign τ); auto with lia.
  * destruct (sign τ); auto with lia.
  * destruct (sign τ); auto with lia.
  * intros Hy. unfold int_lower, int_upper in *. destruct (sign τ); [lia|].
    apply Z_quot_range_nonneg; auto with lia.
  * intros Hy. unfold int_lower, int_upper in *. destruct (sign τ).
    + generalize (Z.rem_bound_abs x y (proj1 Hy)). destruct (decide (0 < y)).
      - rewrite (Z.abs_eq y), Z.abs_lt by lia. lia.
      - rewrite (Z.abs_neq y), Z.abs_lt by lia. lia.
    + split; [apply Z.rem_bound_pos; lia|].
      transitivity y; auto. apply Z.rem_bound_pos; lia.
Qed.
Lemma int_pre_shiftop_typed op x y τ τ2 :
  int_typed x τ → int_typed y τ2 →
  int_pre_shiftop_ok op x y τ → int_typed (int_pre_shiftop op x y τ) τ.
Proof.
  unfold int_typed, int_pre_shiftop_ok, int_pre_shiftop.
  intros [??] [??]. destruct op.
  * destruct (sign τ); auto with lia. intros (?&[? _]&?). split; auto.
    rewrite Z.shiftl_mul_pow2 by done. transitivity 0; auto with zpos.
  * intros ?. assert (0 ≤ x ∧ 0 ≤ y) as [??].
    { unfold int_lower, int_upper in *. destruct (sign τ); auto with lia. }
    rewrite Z.shiftr_div_pow2 by done. split.
    + transitivity 0; auto. apply Z.div_pos; auto with zpos.
    + apply Z.le_lt_trans with x; auto.
      apply Z.div_le_upper_bound; auto with zpos.
      transitivity (1 * x); auto with lia.
      apply Z.mul_le_mono_nonneg_r; auto with zpos.
      assert (0 < 2 ^ y); auto with zpos.
Qed.
Lemma int_pre_cast_typed x σ :
  int_pre_cast_ok σ x → int_typed (int_pre_cast σ x) σ.
Proof.
  unfold int_typed, int_pre_cast_ok, int_pre_cast.
  destruct (sign σ); auto with lia.
Qed.
Lemma int_typed_pre_cast_ok x σ : int_typed x σ → int_pre_cast_ok σ x.
Proof. unfold int_pre_cast_ok. by destruct (sign σ). Qed.
Lemma int_typed_pre_cast x σ : int_typed x σ → int_pre_cast σ x = x.
Proof.
  unfold int_pre_cast, int_typed, int_lower, int_upper.
  destruct (sign σ); auto using Z.mod_small.
Qed.
Lemma int_unsigned_pre_cast_ok x σ : sign σ = Unsigned → int_pre_cast_ok σ x.
Proof. unfold int_pre_cast_ok. by intros ->. Qed.

Lemma int_rank_bits_le τ σ :
  rank_size (rank τ) ≤ rank_size (rank σ) → int_bits τ ≤ int_bits σ.
Proof.
  intros. unfold int_bits. rewrite !Nat2Z.inj_mul.
  apply Z.mul_le_mono_nonneg_r; lia.
Qed.
Lemma int_rank_bits_lt τ σ :
  rank_size (rank τ) < rank_size (rank σ) → int_bits τ < int_bits σ.
Proof.
  intros. unfold int_bits. rewrite !Nat2Z.inj_mul.
  apply Z.mul_lt_mono_pos_r; auto. apply (Nat2Z.inj_lt 0), char_bits_pos.
Qed.
Lemma int_typed_rank_le x τ σ :
  sign τ = sign σ → rank_size (rank τ) ≤ rank_size (rank σ) →
  int_typed x τ → int_typed x σ.
Proof.
  rewrite !int_typed_spec_alt; intros <-; destruct (sign τ).
  * intros ? [??]; split.
    + transitivity (- 2 ^ int_bits τ); [|done]. rewrite <-Z.opp_le_mono.
      by apply Z.pow_le_mono_r; auto using int_rank_bits_le.
    + apply Z.lt_le_trans with (2 ^ int_bits τ); [done|].
      by apply Z.pow_le_mono_r; auto using int_rank_bits_le.
  * intros ? [??]; split; [done|].
    apply Z.lt_le_trans with (2 ^ int_bits τ); [done|].
    by apply Z.pow_le_mono_r; auto using int_rank_bits_le.
Qed.
Lemma int_typed_rank_lt x τ σ :
  sign τ = Unsigned → rank_size (rank τ) < rank_size (rank σ) →
  int_typed x τ → int_typed x σ.
Proof.
  destruct (decide (sign σ = sign τ));[eauto using int_typed_rank_le with lia|].
  rewrite !int_typed_spec_alt. destruct (sign σ); [|congruence].
  intros -> ? [??]; split.
  * transitivity (-0); [|lia]. rewrite <-Z.opp_le_mono. by apply Z.pow_nonneg.
  * rewrite <-Z_pow_pred_r, <-Z.mul_lt_mono_pos_l by (by auto).
    apply Z.lt_le_trans with (2 ^ int_bits τ); [done|].
    by apply Z.pow_le_mono_r, Z.lt_le_pred; auto using int_rank_bits_lt.
Qed.

Local Arguments int_promote _ _ !_ /.
Local Arguments union _ _ !_ !_ /.
Local Arguments int_union _ _ !_ !_ /.
Lemma int_promote_promote σ : int_promote (int_promote σ) = int_promote σ.
Proof. destruct σ; simplify_option_equality; congruence. Qed.
Lemma int_promote_typed x σ : int_typed x σ → int_typed x (int_promote σ).
Proof.
  destruct σ as [[] k]; simpl in *; repeat case_decide; auto.
  * apply int_typed_rank_le; simpl; auto with lia.
  * by apply int_typed_rank_lt.
Qed.
Global Instance: Commutative (=) (@union (int_type Ti) _).
Proof.
  intros [s1 k1] [s2 k2]; simpl.
  repeat case_decide; simplify_equality'; f_equal; try lia.
  * apply (injective rank_size); lia.
  * destruct s1, s2; congruence.
  * apply (injective rank_size); lia.
Qed.
Global Instance: Associative (=) (@union (int_type Ti) _).
Proof.
  intros [s1 k1] [s2 k2] [s3 k3]; repeat
    match goal with
    | _ => reflexivity
    | _ => progress simplify_equality'
    | _ => case_decide
    end; intuition lia.
Qed.
Global Instance: Idempotent (=) (@union (int_type Ti) _).
Proof. by intros [s k]; simplify_option_equality. Qed.
Lemma int_union_pre_cast_ok_l x τ1 τ2 :
  int_typed x τ1 → int_pre_cast_ok (τ1 ∪ τ2) x.
Proof.
  unfold union, int_union; repeat case_decide;
    eauto using int_typed_pre_cast_ok, int_typed_rank_le.
  * destruct (sign τ1) eqn:?;
      [|eauto using int_typed_pre_cast_ok, int_typed_rank_lt].
    destruct (sign τ2) eqn:?; [|eauto using int_unsigned_pre_cast_ok].
    assert (sign τ1 = sign τ2) by congruence.
    eauto using int_typed_pre_cast_ok, int_typed_rank_le with lia.
  * destruct (sign τ2) eqn:?; [|eauto using int_unsigned_pre_cast_ok].
    assert (sign τ1 = sign τ2) by (destruct (sign τ1); congruence).
    eauto using int_typed_pre_cast_ok, int_typed_rank_le with lia.
Qed.
Lemma int_union_pre_cast_ok_r x τ1 τ2 :
  int_typed x τ1 → int_pre_cast_ok (τ2 ∪ τ1) x.
Proof. intros. rewrite (commutative (∪)). by apply int_union_pre_cast_ok_l. Qed.
End properties.
