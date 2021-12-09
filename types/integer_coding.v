(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file describes an abstract interface to capture different
representations of machine integers. The majority of our subsequent Coq
development is parametrized by this interface. Contrary to the C standard,
since all modern architectures use two's complement representation, we require
all representations to be two's complement. *)
Require Export prelude.

Local Open Scope positive_scope.
Local Open Scope Z_scope.
Local Coercion Z.of_nat: nat >-> Z.

(** * Operations on machine integers *)
(** The abstract interface for machine integers is parametrized by a type [K]
of integer ranks (char, short, int). Integer types consist of a rank and its
signedness (signed/unsigned), and machine integers are just arbitrary precision
integers [Z] that should be within the range of the corresponding type. *)
Inductive signedness := Signed | Unsigned.
#[global] Instance signedness_eq_dec: EqDecision signedness.
Proof. solve_decision. Defined.

Definition iType := Type.
Inductive int_type (K : iType) : iType := IntType { sign : signedness; rank : K }.
Add Printing Constructor int_type.

Global Declare Scope int_type_scope.
Delimit Scope int_type_scope with IT.
Local Open Scope int_type_scope.
Bind Scope int_type_scope with int_type.

Arguments IntType {_} _ _.
Arguments sign {_} _%IT.
Arguments rank {_} _%IT.

#[global] Instance int_type_eq_dec `{EqDecision K}: EqDecision (int_type K).
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
Class IntCoding (K : iType): iType := {
  char_rank : K;
  char_signedness : signedness;
  short_rank : K;
  int_rank : K;
  long_rank : K;
  longlong_rank : K;
  ptr_rank : K;
  char_bits : nat;
  rank_size : K → nat;
  endianize : K → list bool → list bool;
  deendianize : K → list bool → list bool;
  rank_subseteq :> SubsetEq K;
  rank_eq_dec :> EqDecision K;
  rank_subseteq_dec (k1 k2 : K) :> Decision (k1 ⊆ k2)
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

Notation "'charT{' K }" :=
  (IntType (@char_signedness K _) (@char_rank K _)) : int_type_scope.
Notation "'charT'" := (charT{ _ })%IT : int_type_scope.
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
  Context `{IntCoding K}.

  Definition int_width (τi : int_type K) : nat :=
    (rank_size (rank τi) * char_bits)%nat.
  Definition int_precision (τi : int_type K) : nat :=
    match sign τi with
    | Signed => int_width τi - 1 | Unsigned => int_width τi
    end%nat.
  Definition int_lower (τi : int_type K) : Z :=
    match sign τi with Signed => -2 ^ int_precision τi | Unsigned => 0 end.
  Definition int_upper (τi : int_type K) : Z := 2 ^ int_precision τi.
  Definition int_typed (x : Z) (τi : int_type K) : Prop :=
    int_lower τi ≤ x < int_upper τi.
  Global Instance int_typed_dec x τi : Decision (int_typed x τi) := _.
  Fixpoint Z_to_bits (n : nat) (x : Z) : list bool :=
    match n with
    | O => []
    | S n => let (q,r) := Z.div_eucl x 2 in bool_decide (r = 1) :: Z_to_bits n q
    end.
  Fixpoint Z_of_bits (βs : list bool) : Z :=
    match βs with [] => 0 | β :: βs => Z.b2z β + 2 * Z_of_bits βs end%Z.

  Definition int_to_bits (τi : int_type K) (x : Z) : list bool :=
    endianize (rank τi) $ Z_to_bits (int_width τi) $
      match sign τi with
      | Signed => if decide (0 ≤ x) then x else x + 2 ^ int_width τi
      | Unsigned => x
      end.
  Definition int_of_bits (τi : int_type K) (βs : list bool) : Z :=
    let x := Z_of_bits (deendianize (rank τi) βs) in
    match sign τi with
    | Signed =>
       if decide (2 * x < 2 ^ int_width τi) then x else x - 2 ^ int_width τi
    | Unsigned => x
    end.
End int_coding.
Typeclasses Opaque int_typed.

(** The classes [IntCodingSpec] describe the laws that an implementation of
machine integers should satisfy with respect to representatons. *)
Class IntCodingSpec K `{IntCoding K} := {
  char_bits_ge_8 : (8 ≤ char_bits)%nat;
  rank_size_char : rank_size char_rank = 1%nat;
  rank_size_preserving (k1 k2 : K) : k1 ⊆ k2 → rank_size k1 ≤ rank_size k2;
  rank_total :> TotalOrder ((⊆) : relation K);
  char_least k : char_rank ⊆ k;
  char_short : char_rank ⊂ short_rank;
  short_int : short_rank ⊂ int_rank;
  int_long : int_rank ⊂ long_rank;
  long_longlong : long_rank ⊂ longlong_rank;
  endianize_permutation k βs : endianize k βs ≡ₚ βs;
  deendianize_endianize k βs : deendianize k (endianize k βs) = βs;
  endianize_deendianize k βs : endianize k (deendianize k βs) = βs
}.

(** * Theorems *)
Section properties.
Context `{IntCodingSpec K}.
Implicit Types τi : int_type K.
Implicit Types βs : list bool.
Implicit Types k : K.
Implicit Types x y : Z.
Implicit Types n : nat.

Lemma Z_to_bits_length n x : length (Z_to_bits n x) = n.
Proof. revert x. by induction n; intros; simpl; try case_match; f_equal'. Qed.
Lemma Z_to_of_bits βs : Z_to_bits (length βs) (Z_of_bits βs) = βs.
Proof.
  induction βs as [|β βs IH]; f_equal'.
  feed pose proof (Z_div_mod (Z.b2z β + 2 * Z_of_bits βs) 2); [lia|].
  destruct (Z.div_eucl _ _) as [q r].
  assert (0 ≤ Z.b2z β ≤ 1 ∧ bool_decide (Z.b2z β = 1) = β) by (by destruct β).
  replace r with (Z.b2z β) by lia; replace q with (Z_of_bits βs) by lia.
  f_equal; naive_solver.
Qed.
Lemma Z_of_bits_range βs : 0 ≤ Z_of_bits βs < 2 ^ length βs.
Proof.
  induction βs as [|[] βs IH]; simpl; [lia|..];
  rewrite Nat2Z.inj_succ, ?Z.pow_succ_r; auto with lia.
Qed.
Lemma Z_of_to_bits n x : 0 ≤ x < 2 ^ n → Z_of_bits (Z_to_bits n x) = x.
Proof.
  revert x.
  induction n as [|n IH]; intros x; simpl; rewrite ?Zpos_P_of_succ_nat.
  { rewrite Z.pow_0_r; lia. }
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by auto with zpos; intros [??].
  feed pose proof (Z_div_mod x 2); [lia|]; destruct (Z.div_eucl _ _) as [q r].
  case_bool_decide; simpl; rewrite IH by lia; lia.
Qed.
Lemma Z_of_zero_bits n : Z_of_bits (replicate n false) = 0.
Proof. induction n; simpl; lia. Qed.

Lemma deendianize_permutation k βs : deendianize k βs ≡ₚ βs.
Proof.
  rewrite <-(endianize_deendianize k βs) at 2. by rewrite endianize_permutation.
Qed.
#[global] Instance: `{Proper ((≡ₚ) ==> (≡ₚ)) (endianize k)}.
Proof. intros k βs1 βs2. by rewrite !endianize_permutation. Qed.
#[global] Instance: `{Inj (≡ₚ) (≡ₚ) (endianize k)}.
Proof. intros k βs1 βs2. by rewrite !endianize_permutation. Qed.
#[global] Instance: `{Proper ((≡ₚ) ==> (≡ₚ)) (deendianize k)}.
Proof. intros k βs1 βs2. by rewrite !deendianize_permutation. Qed.
#[global] Instance: `{Inj (≡ₚ) (≡ₚ) (deendianize k)}.
Proof. intros k βs1 βs2. by rewrite !deendianize_permutation. Qed.
Lemma endianize_length k βs : length (endianize k βs) = length βs.
Proof. by rewrite endianize_permutation. Qed.
Lemma deendianize_length k βs : length (deendianize k βs) = length βs.
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
Local Hint Resolve int_width_pos_alt int_width_pred_nonneg: core.
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
Lemma int_lower_unsigned k : int_lower (IntType Unsigned k) = 0.
Proof. done. Qed.
Lemma int_typed_unsigned_nonneg x k : int_typed x (IntType Unsigned k) → 0 ≤ x.
Proof. by intros [??]. Qed.
Lemma int_lower_nonpos τi : int_lower τi ≤ 0.
Proof.
  unfold int_lower. destruct (sign τi); [|done].
  apply Z.opp_nonpos_nonneg; auto with zpos.
Qed.
Lemma int_upper_pos τi : 0 < int_upper τi.
Proof. unfold int_upper. destruct (sign τi); auto with zpos. Qed.
Local Hint Resolve int_lower_nonpos int_upper_pos: core.
Lemma int_mod_lower_upper x τi :
  int_lower τi ≤ x `mod` int_upper τi < int_upper τi.
Proof.
  split; [transitivity 0; auto; apply Z.mod_pos_bound; auto|].
  apply Z.mod_pos_bound; auto.
Qed.
Local Hint Resolve int_mod_lower_upper: core.
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
Lemma int_upper_signed_unsigned k :
  int_upper (IntType Signed k) < int_upper (IntType Unsigned k).
Proof.
  assert (0 < int_width (IntType Signed k)) by auto using int_width_pos.
  apply Z.pow_lt_mono_r; unfold int_precision, int_width in *; simpl in *; lia.
Qed.
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
Lemma int_to_of_bits τi βs :
  length βs = int_width τi → int_to_bits τi (int_of_bits τi βs) = βs.
Proof.
  intros Hlen. unfold int_to_bits, int_of_bits.
  rewrite <-!Hlen, <-!(deendianize_length (rank τi) βs); clear Hlen.
  pose proof (Z_of_bits_range (deendianize (rank τi) βs)).
  destruct τi as [[] k]; simpl in *.
  * repeat case_decide; auto with lia.
    + by rewrite Z_to_of_bits, endianize_deendianize.
    + rewrite <-Z.sub_sub_distr, Z.sub_diag, Z.sub_0_r.
      by rewrite Z_to_of_bits, endianize_deendianize.
  * by rewrite Z_to_of_bits, endianize_deendianize.
Qed.
Lemma int_of_bits_inj τi βs1 βs2 :
  length βs1 = int_width τi → length βs2 = int_width τi →
  int_of_bits τi βs1 = int_of_bits τi βs2 →  βs1 = βs2.
Proof.
  intros. rewrite <-(int_to_of_bits τi βs1),
    <-(int_to_of_bits τi βs2) by done; congruence.
Qed.
Lemma int_of_bits_typed τi βs :
  length βs = int_width τi → int_typed (int_of_bits τi βs) τi.
Proof.
  intros Hlen. unfold int_of_bits. generalize (int_width_pos τi).
  generalize (Z_of_bits_range (deendianize (rank τi) βs)).
  rewrite int_typed_spec_alt, <-!Hlen, <-!(deendianize_length (rank τi) βs).
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
  * case_decide as Hβs; [by rewrite Hrepl, Z_of_zero_bits |].
    destruct Hβs. rewrite Hrepl, Z_of_zero_bits, Z.mul_0_r. auto with zpos.
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
End properties.
