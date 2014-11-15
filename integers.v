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
Local Open Scope int_type_scope.
Bind Scope int_type_scope with int_type.
Arguments IntType {_} _ _.
Arguments sign {_} _%IT.
Arguments rank {_} _%IT.

Instance int_type_eq_dec {Ti : Set} `{∀ k1 k2 : Ti, Decision (k1 = k2)}
  (τi1 τi2 : int_type Ti) : Decision (τi1 = τi2).
Proof. solve_decision. Defined.

(** The class [IntCoding] describes functions related to representation and
sizes of machine integers. The rank [char_rank] is the rank of the smallest
available integer type, and [ptr_rank] the rank of the types size_t and
ptrdiff_t. At an actual machine, integers of rank [char_rank] corresponds to a
byte, and its bit size is [char_bits] (called CHAR_BIT in the C header
files). *)

(** The function [rank_size k] gives the byte size of an integer with rank [k].
Since we restrict to two's complement, signed integers of rank [k] are between
[-2 ^ (rank_size k*char_bits-1)] (included) and [2 ^ (rank_size k*char_bits-1)],
and unsigned integers of rank [k] are between [0] (included) and
[2 ^ (rank_size k*char_bits)]. The operation [endianize] takes a list of bits
in little endian order and permutes them according to the implementation's
endianness. The function [deendianize] performs the inverse. *)
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
  rank_subseteq :> SubsetEq Ti;
  rank_eq_dec (k1 k2 : Ti) :> Decision (k1 = k2);
  rank_subseteq_dec (k1 k2 : Ti) :> Decision (k1 ⊆ k2)
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
Arguments rank_subseteq _ _ _ _ : simpl never.
Arguments deendianize _ _ _ _ : simpl never.
Arguments rank_eq_dec _ _ _ _ : simpl never.
Arguments rank_subseteq_dec _ _ _ _ : simpl never.

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

  Definition int_width (τi : int_type Ti) : nat :=
    (rank_size (rank τi) * char_bits)%nat.
  Definition int_precision (τi : int_type Ti) : nat :=
    match sign τi with
    | Signed => int_width τi - 1 | Unsigned => int_width τi
    end%nat.
  Definition int_lower (τi : int_type Ti) : Z :=
    match sign τi with Signed => -2 ^ int_precision τi | Unsigned => 0 end.
  Definition int_upper (τi : int_type Ti) : Z := 2 ^ int_precision τi.
  Definition int_typed (x : Z) (τi : int_type Ti) : Prop :=
    int_lower τi ≤ x < int_upper τi.
  Global Instance int_typed_dec x τi : Decision (int_typed x τi) := _.
  Fixpoint Z_to_bits (n : nat) (x : Z) : list bool :=
    match n with
    | O => []
    | S n => let (q,r) := Z.div_eucl x 2 in bool_decide (r = 1) :: Z_to_bits n q
    end.
  Fixpoint Z_of_bits (bs : list bool) : Z :=
    match bs with [] => 0 | b :: bs => Z.b2z b + 2 * Z_of_bits bs end.

  Definition int_to_bits (τi : int_type Ti) (x : Z) : list bool :=
    endianize (rank τi) $ Z_to_bits (int_width τi) $
      match sign τi with
      | Signed => if decide (0 ≤ x) then x else x + 2 ^ int_width τi
      | Unsigned => x
      end.
  Definition int_of_bits (τi : int_type Ti) (bs : list bool) : Z :=
    let x := Z_of_bits (deendianize (rank τi) bs) in
    match sign τi with
    | Signed =>
       if decide (2 * x < 2 ^ int_width τi) then x else x - 2 ^ int_width τi
    | Unsigned => x
    end.

  Definition int_pre_arithop_ok
      (op : arithop) (x y : Z) (τi : int_type Ti) : Prop :=
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
  Definition int_pre_arithop (op : arithop) (x y : Z) (τi : int_type Ti) : Z :=
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
      (op : shiftop) (x y : Z) (τi : int_type Ti) : Prop :=
    match op, sign τi with
    | ShiftLOp, Signed => 0 ≤ x ∧ 0 ≤ y < int_width τi ∧ x ≪ y < int_upper τi
    | ShiftLOp, Unsigned => 0 ≤ y < int_width τi
    | ShiftROp, Signed => 0 ≤ x ∧ 0 ≤ y < int_width τi
    | ShiftROp, Unsigned => 0 ≤ y < int_width τi
    end.
  Definition int_pre_shiftop (op : shiftop) (x y : Z) (τi : int_type Ti) : Z :=
    match op, sign τi with
    | ShiftLOp, Signed => x ≪ y
    | ShiftLOp, Unsigned => (x ≪ y) `mod` int_upper τi
    | ShiftROp, _ => x ≫ y
    end.
  Definition int_pre_cast_ok (σi : int_type Ti) (x : Z) :=
    match sign σi with
    | Signed => (**i actually implementation defined, see 6.3.1.3 *)
       int_lower σi ≤ x < int_upper σi
    | Unsigned => True
    end.
  Definition int_pre_cast (σi : int_type Ti) (x : Z) :=
    match sign σi with Signed => x | Unsigned => x `mod` int_upper σi end.

  Global Instance int_pre_arithop_ok_dec op x y τi :
    Decision (int_pre_arithop_ok op x y τi).
  Proof. unfold int_pre_arithop_ok. destruct op, (sign τi); apply _. Defined.
  Global Instance int_pre_shiftop_ok_dec op x y τi :
    Decision (int_pre_shiftop_ok op x y τi).
  Proof. unfold int_pre_shiftop_ok. destruct op, (sign τi); apply _. Defined.
  Global Instance int_pre_cast_ok_dec σi x : Decision (int_pre_cast_ok σi x).
  Proof. unfold int_pre_cast_ok. destruct (sign σi); apply _. Defined.

  Inductive int_subseteq : SubsetEq (int_type Ti) :=
    | int_subseteq_same_sign si (k1 k2 : Ti) :
       k1 ⊆ k2 → IntType si k1 ⊆ IntType si k2
    | int_subseteq_Signed_Unsigned (k1 k2 : Ti) :
       k1 ⊆ k2 → IntType Signed k1 ⊆ IntType Unsigned k2
    | int_subseteq_Unsigned_Signed (k1 k2 : Ti) :
       int_upper (IntType Unsigned k1) ≤ int_upper (IntType Signed k2) →
       IntType Unsigned k1 ⊆ IntType Signed k2.
  Global Existing Instance int_subseteq.

  Definition int_promote (τi : int_type Ti) : int_type Ti :=
    if decide (rank τi ⊆ int_rank) then
      if decide (int_upper τi ≤ int_upper sintT) then sintT else uintT
    else τi.
  Global Instance rank_union : Union Ti := λ k1 k2,
    if decide (k1 ⊆ k2) then k2 else k1.
  Global Instance int_union : Union (int_type Ti) := λ τi1 τi2,
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
End int_coding.
Typeclasses Opaque int_typed.

(** The classes [IntCodingSpec] describe the laws that an implementation of
machine integers should satisfy with respect to representatons. *)
Class IntCodingSpec Ti `{IntCoding Ti} := {
  char_bits_ge_8 : (8 ≤ char_bits)%nat;
  rank_size_char : rank_size char_rank = 1%nat;
  rank_size_preserving (k1 k2 : Ti) : k1 ⊆ k2 → rank_size k1 ≤ rank_size k2;
  rank_total :> TotalOrder ((⊆) : relation Ti);
  char_least k : char_rank ⊆ k;
  char_short : char_rank ⊂ short_rank;
  short_int : short_rank ⊂ int_rank;
  int_long : int_rank ⊂ long_rank;
  long_longlong : long_rank ⊂ longlong_rank;
  endianize_permutation k bs : endianize k bs ≡ₚ bs;
  deendianize_endianize k bs : deendianize k (endianize k bs) = bs;
  endianize_deendianize k bs : endianize k (deendianize k bs) = bs
}.
(** In order to deal with underspecification of operations, the class [IntEnv]
does not just contain a function [int_binop] to perform a binary operation, but
also a predicate [int_binop_ok τi op x y] that describes when [op] is allowed to
be performed on integers [x] and [y] of type [τi]. This is to allow both strict
implementations that make integer overflow undefined, and those that let it
wrap (as for example GCC with the -fno-strict-overflow flag does). When an
operation is allowed by the C standard, the result of [int_binop τi op x y]
should correspond to its specification by the standard. *)
Class IntEnv (Ti : Set) := {
  int_coding :> IntCoding Ti;
  int_arithop_ok : arithop → Z → int_type Ti → Z → int_type Ti → Prop;
  int_arithop : arithop → Z → int_type Ti → Z → int_type Ti → Z;
  int_shiftop_ok : shiftop → Z → int_type Ti → Z → int_type Ti → Prop;
  int_shiftop : shiftop → Z → int_type Ti → Z → int_type Ti → Z;
  int_cast_ok : int_type Ti → Z → Prop;
  int_cast : int_type Ti → Z → Z;
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

Class IntEnvSpec Ti `{IntEnv Ti} := {
  int_coding_spec :>> IntCodingSpec Ti;
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

(** * Theorems *)
Lemma Z_to_bits_length n x : length (Z_to_bits n x) = n.
Proof. revert x. by induction n; intros; simpl; try case_match; f_equal'. Qed.
Lemma Z_to_of_bits bs : Z_to_bits (length bs) (Z_of_bits bs) = bs.
Proof.
  induction bs as [|b bs IH]; f_equal'.
  feed pose proof (Z_div_mod (Z.b2z b + 2 * Z_of_bits bs) 2); [lia|].
  destruct (Z.div_eucl _ _) as [q r].
  assert (0 ≤ Z.b2z b ≤ 1 ∧ bool_decide (Z.b2z b = 1) = b) by (by destruct b).
  replace r with (Z.b2z b) by lia; replace q with (Z_of_bits bs) by lia.
  f_equal; naive_solver.
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
  rewrite Z.pow_succ_r by auto with zpos; intros [??].
  feed pose proof (Z_div_mod x 2); [lia|]; destruct (Z.div_eucl _ _) as [q r].
  case_bool_decide; simpl; rewrite IH by lia; lia.
Qed.
Lemma Z_of_zero_bits n : Z_of_bits (replicate n false) = 0.
Proof. induction n; simpl; lia. Qed.

Section properties.
Context `{IntCodingSpec Ti}.
Implicit Types τi : int_type Ti.
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

Lemma rank_size_pos k : (0 < rank_size k)%nat.
Proof.
  rewrite <-Nat.le_succ_l, <-rank_size_char, Nat2Z.inj_le.
  apply rank_size_preserving, char_least.
Qed.
Lemma rank_size_ne_0 k : (rank_size k ≠ 0)%nat.
Proof. apply Nat.neq_0_lt_0, rank_size_pos. Qed.
Lemma int_width_char si : int_width (IntType si char_rank) = char_bits.
Proof. unfold int_width; simpl. by rewrite rank_size_char, Nat.mul_1_l. Qed.
Lemma char_bits_pos : (0 < char_bits)%nat.
Proof. pose proof char_bits_ge_8; lia. Qed.
Lemma char_bits_ne_0 : char_bits ≠ 0%nat.
Proof. pose proof char_bits_ge_8; lia. Qed.
Lemma int_width_ge_8 τi : (8 ≤ int_width τi)%nat.
Proof.
  unfold int_width. transitivity (1 * char_bits)%nat.
  * by rewrite char_bits_ge_8, Nat.mul_1_l.
  * apply Nat.mul_le_mono_r. generalize (rank_size_pos (rank τi)); lia.
Qed.
Lemma int_width_ge_8_alt τi : 8 ≤ int_width τi.
Proof. apply (Nat2Z.inj_le 8), int_width_ge_8. Qed.
Lemma int_width_pos τi : (0 < int_width τi)%nat.
Proof. pose proof (int_width_ge_8 τi); lia. Qed.
Lemma int_width_pos_alt τi : 0 < int_width τi.
Proof. apply (Nat2Z.inj_lt 0), int_width_pos. Qed.
Lemma int_width_pred_nonneg τi : 0 ≤ int_width τi - 1.
Proof. pose proof (int_width_pos_alt τi); lia. Qed.
Hint Resolve int_width_pos_alt int_width_pred_nonneg.
Lemma int_width_Unsigned_Signed k :
  int_width (IntType Unsigned k) = int_width (IntType Signed k).
Proof. done. Qed.
Lemma int_precision_Unsigned_Signed k :
  int_precision (IntType Unsigned k) = S (int_precision (IntType Signed k)).
Proof.
  unfold int_precision; simpl; rewrite int_width_Unsigned_Signed.
  pose proof (int_width_pos (IntType Signed k)); lia.
Qed.
Lemma int_typed_lower x τi : int_typed x τi → int_lower τi ≤ x.
Proof. by intros [??]. Qed.
Lemma int_typed_upper x τi : int_typed x τi → x < int_upper τi.
Proof. by intros [??]. Qed.
Lemma int_lower_u τi : sign τi = Unsigned → int_lower τi = 0.
Proof. by destruct τi as [[] ?]. Qed.
Lemma int_lower_nonpos τi : int_lower τi ≤ 0.
Proof.
  unfold int_lower. destruct (sign τi); [|done].
  apply Z.opp_nonpos_nonneg; auto with zpos.
Qed.
Lemma int_upper_pos τi : 0 < int_upper τi.
Proof. unfold int_upper. destruct (sign τi); auto with zpos. Qed.
Hint Resolve int_lower_nonpos int_upper_pos.
Lemma int_mod_lower_upper x τi :
  int_lower τi ≤ x `mod` int_upper τi < int_upper τi.
Proof.
  split; [transitivity 0; auto; apply Z.mod_pos_bound; auto|].
  apply Z.mod_pos_bound; auto.
Qed.
Hint Resolve int_mod_lower_upper.
Lemma int_upper_lower τi : int_upper τi = 2 ^ int_width τi + int_lower τi.
Proof.
  unfold int_upper, int_lower, int_precision; destruct (sign τi); simpl; [|lia].
  apply (Z.mul_cancel_l _ _ 2); [done |]. pose proof (int_width_pos τi).
  rewrite Z.mul_add_distr_l, Z.mul_opp_r, Nat2Z.inj_sub,
    !Z.sub_1_r, !Z_pow_pred_r; auto with zpos.
Qed.
Lemma int_lower_upper_signed τi :
  sign τi = Signed → int_lower τi = -int_upper τi.
Proof. by intros; destruct τi; simplify_equality'. Qed.
Lemma int_typed_spec_alt x τi :
  int_typed x τi ↔
    match sign τi with
    | Signed => -2 ^ int_width τi ≤ 2 * x < 2 ^ int_width τi
    | Unsigned => 0 ≤ x < 2 ^ int_width τi
    end.
Proof.
  unfold int_typed, int_lower, int_upper, int_precision.
  destruct (sign τi); simpl; [|done]. pose proof (int_width_pos τi).
  rewrite (Z.mul_lt_mono_pos_l 2 x), (Z.mul_le_mono_pos_l _ _ 2) by done.
  by rewrite Nat2Z.inj_sub, Z.mul_opp_r, Z.sub_1_r, Z_pow_pred_r by auto.
Qed.
Lemma int_typed_nonneg_signed x τi :
  0 ≤ 2 * x < 2 ^ int_width τi → int_typed x τi.
Proof. rewrite int_typed_spec_alt. destruct (sign _); lia. Qed.
Lemma int_typed_small x τi : 0 ≤ x < 128 → int_typed x τi.
Proof.
  intros [??]. apply int_typed_nonneg_signed. split; [lia|].
  apply Z.lt_le_trans with (2 ^ 8); [lia |].
  by apply Z.pow_le_mono_r; auto using int_width_ge_8_alt.
Qed.
Lemma int_to_bits_length τi x : length (int_to_bits τi x) = int_width τi.
Proof.
  unfold int_to_bits, int_width. rewrite endianize_permutation.
  by destruct τi as [[] k]; simpl; rewrite Z_to_bits_length.
Qed.
Lemma int_to_of_bits τi bs :
  length bs = int_width τi → int_to_bits τi (int_of_bits τi bs) = bs.
Proof.
  intros Hlen. unfold int_to_bits, int_of_bits.
  rewrite <-!Hlen, <-!(deendianize_length (rank τi) bs); clear Hlen.
  pose proof (Z_of_bits_range (deendianize (rank τi) bs)).
  destruct τi as [[] k]; simpl in *.
  * repeat case_decide; auto with lia.
    + by rewrite Z_to_of_bits, endianize_deendianize.
    + rewrite <-Z.sub_sub_distr, Z.sub_diag, Z.sub_0_r.
      by rewrite Z_to_of_bits, endianize_deendianize.
  * by rewrite Z_to_of_bits, endianize_deendianize.
Qed.
Lemma int_of_bits_inj τi bs1 bs2 :
  length bs1 = int_width τi → length bs2 = int_width τi →
  int_of_bits τi bs1 = int_of_bits τi bs2 →  bs1 = bs2.
Proof.
  intros. rewrite <-(int_to_of_bits τi bs1),
    <-(int_to_of_bits τi bs2) by done; congruence.
Qed.
Lemma int_of_bits_typed τi bs :
  length bs = int_width τi → int_typed (int_of_bits τi bs) τi.
Proof.
  intros Hlen. unfold int_of_bits. generalize (int_width_pos τi).
  generalize (Z_of_bits_range (deendianize (rank τi) bs)).
  rewrite int_typed_spec_alt, <-!Hlen, <-!(deendianize_length (rank τi) bs).
  destruct τi as [[] k]; simpl; repeat case_decide; auto with lia.
Qed.
Lemma int_of_to_bits τi x :
  int_typed x τi → int_of_bits τi (int_to_bits τi x) = x.
Proof.
  unfold int_of_bits, int_to_bits. rewrite int_typed_spec_alt.
  destruct τi as [[] k]; simpl in *.
  * intros [??]. repeat case_decide; repeat_on_hyps
      (fun H => rewrite deendianize_endianize, !Z_of_to_bits in H by lia);
      rewrite deendianize_endianize, Z_of_to_bits; lia.
  * intros [??]. by rewrite deendianize_endianize, Z_of_to_bits.
Qed.
Lemma int_of_zero_bits τi : int_of_bits τi (replicate (int_width τi) false) = 0.
Proof.
  assert (∀ k n b, deendianize k (replicate n b) = replicate n b) as Hrepl.
  { intros k n b. symmetry. apply replicate_Permutation.
    by rewrite deendianize_permutation. }
  unfold int_of_bits. destruct (sign τi).
  * case_decide as Hbs; [by rewrite Hrepl, Z_of_zero_bits |].
    destruct Hbs. rewrite Hrepl, Z_of_zero_bits, Z.mul_0_r. auto with zpos.
  * by rewrite Hrepl, Z_of_zero_bits.
Qed.
Lemma int_to_bits_signed_unsigned k x :
  0 ≤ x → int_to_bits (IntType Signed k) x = int_to_bits (IntType Unsigned k) x.
Proof. unfold int_to_bits; simpl; case_decide; auto with lia. Qed.
Lemma int_lower_lt_upper τi : int_lower τi < int_upper τi.
Proof.
  rewrite int_upper_lower. assert (0 < 2 ^ int_width τi) by auto with zpos; lia.
Qed.
Lemma int_lower_typed τi : int_typed (int_lower τi) τi.
Proof. pose proof (int_lower_lt_upper τi). split; lia. Qed.
Lemma int_upper_typed τi : int_typed (int_upper τi - 1) τi.
Proof. pose proof (int_lower_lt_upper τi). split; lia. Qed.
Lemma int_width_typed τi : int_typed (int_width τi) τi.
Proof.
  split; [transitivity 0; auto with zpos|]. unfold int_upper, int_precision;
    destruct (sign _); [|apply Z.pow_gt_lin_r; lia].
  pose proof (int_width_ge_8 τi); rewrite Nat2Z.inj_sub by lia.
  replace (int_width τi : Z)
    with (Z.succ (Z.succ (Z.succ (int_width τi - 3)%nat))) by lia.
  rewrite Z.sub_1_r, Z.pred_succ by lia.
  induction (int_width τi - 3)%nat as [|n IH]; [done|].
  rewrite !Nat2Z.inj_succ, Z.pow_succ_r by auto with zpos; lia.
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
    apply Z.mul_le_mono_nonneg_r; auto with zpos.
    assert (0 < 2 ^ y); auto with zpos.
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

Hint Resolve rank_size_preserving.
Lemma rank_size_union k1 k2 :
  (rank_size (k1 ∪ k2) : Z) = Z.max (rank_size k1) (rank_size k2).
Proof.
  unfold union, rank_union at 1; case_decide; [by rewrite Z.max_r by auto|].
  by rewrite Z.max_l by (by apply rank_size_preserving, total_not).
Qed.
Lemma rank_le_width τi1 τi2 :
  rank_size (rank τi1) ≤ rank_size (rank τi2) → int_width τi1 ≤ int_width τi2.
Proof.
  unfold int_width; intros. rewrite !Nat2Z.inj_mul.
  apply Z.mul_le_mono_nonneg_r; auto with zpos.
Qed.
Lemma rank_lt_width τi1 τi2 :
  rank_size (rank τi1) < rank_size (rank τi2) → int_width τi1 < int_width τi2.
Proof.
  intros. unfold int_width. rewrite !Nat2Z.inj_mul.
  apply Z.mul_lt_mono_pos_r; auto. apply (Nat2Z.inj_lt 0), char_bits_pos.
Qed.
Lemma rank_le_upper si k1 k2 :
  rank_size k1 ≤ rank_size k2 →
  int_upper (IntType si k1) ≤ int_upper (IntType si k2).
Proof.
  intros; apply Z.pow_le_mono_r_iff; auto with zpos.
  assert (int_width (IntType si k1) ≤ int_width (IntType si k2))
    by auto using rank_le_width; unfold int_precision; destruct (sign _); lia.
Qed.
Lemma rank_lt_upper k1 k2 :
  rank_size k1 < rank_size k2 →
  int_upper (IntType Unsigned k1) ≤ int_upper (IntType Signed k2).
Proof.
  intros; apply Z.pow_le_mono_r_iff; auto with zpos.
  assert (int_width (IntType Unsigned k1) < int_width (IntType Signed k2))
    by auto using rank_lt_width; unfold int_precision; simpl; lia.
Qed.
Lemma int_typed_rank_weaken x si k1 k2 :
  int_typed x (IntType si k1) → rank_size k1 ≤ rank_size k2 →
  int_typed x (IntType si k2).
Proof.
  rewrite !int_typed_spec_alt; destruct si; simpl.
  * intros [??] ?; split.
    + transitivity (- 2 ^ int_width (IntType Signed k1)); [|done].
      rewrite <-Z.opp_le_mono.
      by apply Z.pow_le_mono_r; auto using rank_le_width.
    + apply Z.lt_le_trans with (2 ^ int_width (IntType Signed k1)); [done|].
      by apply Z.pow_le_mono_r; auto using rank_le_width.
  * intros [??] ?; split; [done|].
    apply Z.lt_le_trans with (2 ^ int_width (IntType Signed k1)); [done|].
    by apply Z.pow_le_mono_r; auto using rank_le_width.
Qed.
Lemma int_typed_rank_strict_weaken x si k1 k2 :
  int_typed x (IntType Unsigned k1) → rank_size k1 < rank_size k2 →
  int_typed x (IntType si k2).
Proof.
  destruct si; eauto using int_typed_rank_weaken with lia.
  rewrite !int_typed_spec_alt. intros [??] ?; split.
  * transitivity (-0); [|lia]. rewrite <-Z.opp_le_mono. by apply Z.pow_nonneg.
  * rewrite <-Z_pow_pred_r, <-Z.mul_lt_mono_pos_l by (by auto).
    apply Z.lt_le_trans with (2 ^ int_width (IntType Signed k1)); [done|].
    by apply Z.pow_le_mono_r, Z.lt_le_pred; auto using rank_lt_width.
Qed.
Lemma int_upper_le_invert k1 k2 :
  int_upper (IntType Unsigned k1) ≤ int_upper (IntType Signed k2) →
  rank_size k1 < rank_size k2.
Proof.
  unfold int_upper, int_precision, int_width; simpl.
  pose proof char_bits_ge_8; pose proof (rank_size_pos k2).
  rewrite <-Z.pow_le_mono_r_iff by auto with zpos.
  rewrite Nat2Z.inj_sub by (apply Nat.le_succ_l, Nat.mul_pos_pos; lia); intros.
  apply (Z.mul_lt_mono_pos_r char_bits); lia.
Qed.
Lemma int_upper_le_invert_2 k1 k2 :
  int_upper (IntType Signed k1) ≤ int_upper (IntType Unsigned k2) →
  rank_size k1 ≤ rank_size k2.
Proof.
  unfold int_upper, int_precision, int_width; simpl.
  pose proof char_bits_ge_8; pose proof (rank_size_pos k2).
  rewrite <-Z.pow_le_mono_r_iff, <-!Nat2Z.inj_le by auto with zpos; intros.
  rewrite <-Nat.lt_succ_r, (Nat.mul_lt_mono_pos_r char_bits); lia.
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
Lemma int_promote_promote τi : int_promote (int_promote τi) = int_promote τi.
Proof.
  assert (int_upper sintT < int_upper uintT).
  { unfold int_upper. rewrite int_precision_Unsigned_Signed.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by auto with zpos.
    assert (0 < 2 ^ int_precision sintT) by auto with zpos. lia. }
  destruct τi as [si k]; simplify_option_equality; auto with lia.
Qed.
Lemma int_promote_typed x τi : int_typed x τi → int_typed x (int_promote τi).
Proof.
  destruct τi as [[] k]; simpl; intros; repeat case_decide;
    naive_solver eauto using int_typed_rank_weaken,
    int_typed_rank_strict_weaken, int_upper_le_invert, rank_le_upper.
Qed.
Global Instance: PartialOrder ((⊆) : relation (int_type Ti)).
Proof.
  repeat split.
  * by intros [[] ?]; constructor.
  * destruct 1; inversion 1; subst; constructor;
      eauto using (transitivity (R:=@subseteq Ti _)),
      Z.le_trans, rank_le_upper, int_upper_le_invert_alt.
  * destruct 1; inversion 1; subst.
    + by f_equal; apply (anti_symmetric (⊆)).
    + destruct (irreflexivity (⊂) k1); eapply strict_transitive_r,
        rank_size_reflecting, int_upper_le_invert; eauto.
    + destruct (irreflexivity (⊂) k2); eapply strict_transitive_r,
        rank_size_reflecting, int_upper_le_invert; eauto.
Qed.
Global Instance: JoinSemiLattice Ti.
Proof.
  split; try apply _;
    unfold union, rank_union; intros; case_decide; auto using total_not.
Qed.
Global Instance: JoinSemiLattice (int_type Ti).
Proof.
  split; try apply _.
  * intros [[] k1] [[] k2]; simpl.
    + constructor. apply union_subseteq_l.
    + repeat case_decide; constructor; auto.
    + repeat case_decide; constructor; auto using total_not.
    + constructor. apply union_subseteq_l.
  * intros [[] k1] [[] k2]; simpl.
    + constructor. apply union_subseteq_r.
    + repeat case_decide; constructor; auto using total_not.
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
Lemma int_pre_cast_ok_subseteq x τi1 τi2 :
  int_typed x τi1 → τi1 ⊆ τi2 → int_pre_cast_ok τi2 x.
Proof.
  intros Hx; destruct 1; eauto using int_unsigned_pre_cast_ok,
    int_typed_pre_cast_ok, int_typed_rank_weaken.
  pose proof (int_lower_nonpos (IntType Signed k2)).
  destruct Hx as [Hxl Hxu]; rewrite int_lower_u in Hxl; split; lia.
Qed.
End properties.
