(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file defines a two's complements implementation of the interface for
machine integers. This implementation is parametrized by its endianness, and
the number of bits of which a byte consists. Internally, it uses Coq's type
of binary arbitrary precision integers [Z], and all operations are based on the
corresponding functions from Coq's standard library. This representation does
not include padding bits, and ensures unique integer representations. *)

(** This implementation is inspired by CompCert's implementation of machine
integers, but unlike CompCert, we make signed integer overflow undefined
behavior instead of letting it wrap around. *)
Require Import abstract_integers.
Open Local Scope Z_scope.

Local Hint Resolve Z.lt_le_incl.
Local Hint Resolve Z.add_nonneg_pos.
Local Hint Resolve Z.add_pos_nonneg.
Local Hint Resolve Z.add_nonneg_nonneg.
Local Hint Resolve Z.mul_nonneg_nonneg.
Local Hint Resolve Z.pow_pos_nonneg.
Local Hint Resolve Z.pow_nonzero.
Local Hint Resolve neq_0_lt.
Local Hint Resolve Zle_0_nat.
Local Hint Resolve NPeano.Nat.le_0_l.
Local Hint Resolve NPeano.Nat.add_nonneg_pos.
Local Hint Resolve NPeano.Nat.add_pos_nonneg.
Local Hint Resolve NPeano.Nat.add_nonneg_nonneg.
Local Hint Extern 1000 => lia.
Local Arguments Z.of_nat _ : simpl never.

(** The data type [int_type] describes infinitely many signed and unsigned
integer types of arbitrary size. The length of an integer type [σ] in bits is
[(1 + ILen σ) * Csz], where [Csz] is length of a byte in bits. *)
Inductive int_type : Set := IntType {
  ISign : signedness;
  ILen : nat
}.
Add Printing Constructor int_type.

Definition int_type_bits_ (Csz : nat) (σ : int_type) : nat :=
  (S (ILen σ) * Csz)%nat.

(** The data type of integers [int_ be Csz] is indexed by a boolean [be]
and a natural [Csz]. The boolean [be] describes whether a big endian (in case
it is [true] or little endian (in case it is [false]) representation should be
used. The natural number [Csz] describes the number of bits of which an
individual byte consists. We equip the data type with a boolean proof of being
in range to ensure canonicity. *)
Inductive int_ (be: bool) (Csz: nat) : Set := CInt' {
  IType : int_type;
  INum : Z;
  INum_prf' : bool_decide (0 ≤ INum < 2 ^ int_type_bits_ Csz IType)
}.
Arguments CInt' {_ _} _ _ _.
Arguments IType {_ _} _.
Arguments INum {_ _} _.
Arguments INum_prf' {_ _} _.
Add Printing Constructor int_.

Section int.
Context {be: bool} {Csz : nat}.

Global Instance int_type_eq_dec_ (σ1 σ2 : int_type) :
  Decision (σ1 = σ2).
Proof. solve_decision. Defined.

Definition Int (σ : int_type) (x : Z)
    (H : 0 ≤ x < 2 ^ int_type_bits_ Csz σ) : int_ be Csz :=
  CInt' σ x (bool_decide_pack _ H).
Definition INum_prf (i : int_ be Csz) :
    0 ≤ INum i < 2 ^ int_type_bits_ Csz (IType i) :=
  bool_decide_unpack _ (INum_prf' i).
Definition INum_lower (i : int_ be Csz) : 0 ≤ INum i :=
  proj1 (INum_prf i).
Definition INum_upper (i : int_ be Csz) :
  INum i < 2 ^ int_type_bits_ Csz (IType i) := proj2 (INum_prf i).
Local Hint Resolve INum_lower INum_upper.

Lemma int_eq_ (i1 i2 : int_ be Csz) :
  i1 = i2 ↔ IType i1 = IType i2 ∧ INum i1 = INum i2.
Proof.
  split; [intuition congruence |].
  destruct i1, i2; simpl; intros [??]; subst. f_equal. apply proof_irrel.
Qed.
Lemma int_mod_eq_ (i : int_ be Csz) :
  INum i `mod` 2 ^ int_type_bits_ Csz (IType i) = INum i.
Proof. by apply Z.mod_small, INum_prf. Qed.

Global Instance int_eq_dec_ (i1 i2 : int_ be Csz) : Decision (i1 = i2).
Proof.
  refine (cast_if_and (decide (IType i1 = IType i2))
    (decide (INum i1 = INum i2))); rewrite int_eq_; tauto.
Defined.

Definition mk_int_mod_range_ (σ : int_type) x :
  0 ≤ x `mod` (2 ^ int_type_bits_ Csz σ) < 2 ^ int_type_bits_ Csz σ.
Proof. apply Z.mod_pos_bound; auto. Qed.
Definition mk_int_mod_ (σ : int_type) (x : Z) : int_ be Csz :=
  Int _ _ (mk_int_mod_range_ σ x).
Lemma mk_int_mod_INum (i : int_ be Csz) :
  mk_int_mod_ (IType i) (INum i) = i.
Proof. unfold mk_int_mod_. apply int_eq_. simpl. by rewrite int_mod_eq_. Qed.

Definition mk_int_ (σ : int_type) (x : Z) : option (int_ be Csz) :=
  match ISign σ with
  | Signed =>
     guard (-2 ^ pred (int_type_bits_ Csz σ)
       ≤ x < 2 ^ pred (int_type_bits_ Csz σ));
     Some (mk_int_mod_ σ x)
  | Unsigned => Some (mk_int_mod_ σ x)
  end.
Lemma mk_int_type_ (σ : int_type) x i :
  mk_int_ σ x = Some i → IType i = σ.
Proof.
  unfold mk_int_. intros. by destruct (ISign _); simplify_option_equality.
Qed.

Notation char_type_ := (IntType Unsigned 0).
Notation char_ := { x : int_ be Csz | IType x = char_type_ }.

Lemma IType_char (c : char_) : IType (`c) = char_type_.
Proof. by destruct c. Qed.
Lemma char_eq_ (c1 c2 : char_) :
  c1 = c2 ↔ INum (`c1) = INum (`c2).
Proof.
  split; intros; subst; auto.
  apply (sig_eq_pi _), int_eq_. by rewrite !IType_char.
Qed.

Lemma char_bits_: int_type_bits_ Csz char_type_ = Csz.
Proof. unfold int_type_bits_. simpl. by rewrite plus_0_r. Qed.
Definition INum_char_upper (c : char_) : INum (`c) < 2 ^ Csz.
Proof. generalize (INum_upper (`c)). by rewrite IType_char, char_bits_. Qed.
Hint Resolve INum_char_upper.

Definition mk_char_mod_ (x : Z) : char_ :=
  mk_int_mod_ _ x ↾ eq_refl.
Lemma char_mod_eq_ (c : char_) :
  INum (`c) `mod` 2 ^ Csz = INum (`c).
Proof. generalize (int_mod_eq_ (`c)). by rewrite IType_char, char_bits_. Qed.

Fixpoint encode_Z (n : nat) (x : Z) : list char_ :=
  match n with
  | O => [mk_char_mod_ x]
  | S n => mk_char_mod_ x :: encode_Z n (x `div` (2 ^ Csz))
  end.
Fixpoint decode_Z (cs : list char_) : Z :=
  match cs with
  | [] => 0
  | c :: cs => INum (`c) + 2 ^ Csz * decode_Z cs
  end.

Lemma encode_Z_length n x :
  length (encode_Z n x) = S n.
Proof. revert x. induction n; simpl; intros; f_equal; auto. Qed.
Lemma decode_encode_Z n x :
  decode_Z (encode_Z n x) = x `mod` (2 ^ (S n * Csz)%nat).
Proof.
  rewrite Nat2Z.inj_mul.
  revert x. induction n as [|n IH]; intros x; rewrite ?Nat2Z.inj_succ; simpl.
  * rewrite char_bits_, Z.mul_1_l. ring.
  * rewrite char_bits_, IH, <-Z.rem_mul_r, <-Z.pow_add_r by auto.
    do 2 f_equal. lia.
Qed.
Lemma encode_decode_Z c cs :
  encode_Z (length cs) (decode_Z (c :: cs)) = c :: cs.
Proof.
  revert c. induction cs as [|c2 cs]; intros c1; simpl.
  * f_equal. apply char_eq_. simpl. rewrite char_bits_.
    by rewrite Z.mul_0_r, Z.add_0_r, char_mod_eq_.
  * rewrite <-IHcs. simpl. rewrite !(Z.mul_comm (2^_) (_+_)). f_equal.
    + apply char_eq_. simpl.
      rewrite char_bits_, Z.mod_add, char_mod_eq_; auto.
    + f_equal. by rewrite Z.div_add, Z.div_small by auto.
Qed.
Lemma decode_Z_range cs :
  0 ≤ decode_Z cs < 2 ^ (length cs * Csz)%nat.
Proof.
  rewrite Nat2Z.inj_mul. split.
  * induction cs; simpl; auto.
  * induction cs as [|c cs IH]; simpl; auto.
    rewrite Nat2Z.inj_succ, Z.mul_succ_l.
    rewrite Z.pow_add_r, (Z.add_comm (INum _)) by auto.
    apply Z.lt_le_trans with (2 ^ Csz * decode_Z cs + 2 ^ Csz).
    { apply Z.add_lt_mono_l; auto. }
    rewrite Zmult_succ_r_reverse, (Z.mul_comm (2^_)).
    apply Z.mul_le_mono_pos_r; auto.
Qed.
Lemma decode_Z_zeroes n (c : char_) :
  INum (`c) = 0 →
  decode_Z (replicate n c) = 0.
Proof.
  intros Hc. induction n as [|n IH]; simpl; auto.
  rewrite Hc, IH. ring.
Qed.

Definition reverse_if_be {A} (l : list A) :=
  if be then reverse l else l.
Lemma reverse_if_be_length {A} (l : list A) :
  length (reverse_if_be l) = length l.
Proof. unfold reverse_if_be. by destruct be; rewrite ?reverse_length. Qed.
Lemma reverse_if_be_involutive {A} (l : list A) :
  reverse_if_be (reverse_if_be l) = l.
Proof. unfold reverse_if_be. by destruct be; rewrite ?reverse_involutive. Qed.
Lemma reverse_if_be_replicate {A} n (x : A) :
  reverse_if_be (replicate n x) = replicate n x.
Proof. unfold reverse_if_be. by destruct be; rewrite ?reverse_replicate. Qed.

Lemma decode_Z_range_alt (σ : int_type) cs :
  S (ILen σ) = length cs →
  0 ≤ decode_Z (reverse_if_be cs) < 2 ^ int_type_bits_ Csz σ.
Proof.
  intros Hcs. unfold int_type_bits_.
  rewrite Hcs, <-(reverse_if_be_length cs). apply decode_Z_range.
Qed.

Definition encode_int_ (i : int_ be Csz) : list char_ :=
  reverse_if_be $ encode_Z (ILen (IType i)) (INum i).
Definition decode_int_ (σ : int_type)
    (cs : list char_) : option (int_ be Csz) :=
  match decide_rel (=) (S (ILen σ)) (length cs) with
  | left H =>
     Some $ Int σ (decode_Z (reverse_if_be cs)) (decode_Z_range_alt _ _ H)
  | right _ => None
  end.

Definition signed_Z (b : nat) (x : Z) : Z :=
  let z := 2 ^ pred b in
  if decide (x < z) then x else x - 2 ^ b.
Definition int_to_Z_ (i : int_ be Csz) : Z :=
  match ISign (IType i) with
  | Signed => signed_Z (int_type_bits_ Csz (IType i)) (INum i)
  | Unsigned => INum i
  end.

(** Operations are evaluated by translation to [Z] and back. For some signed
operations (e.g. plus and mult), this is slightly inefficient as they could
be evaluated directly on the underlaying numeral. *)
Global Instance: IntEnv int_type (int_ be Csz) := {|
  int_type_size := S ∘ ILen;
  int_type_sign := ISign;
  int_type_range := λ σ,
    2 ^ pred (int_type_bits_ Csz σ);
  type_of_int := IType;
  TuChar := IntType Unsigned 0;
  TuChar_bits := Csz;
  TsInt := IntType Signed 3;
  encode_int := λ i, {[ encode_int_ i ]};
  decode_int := decode_int_;
  int_to_Z := int_to_Z_;
  int_of_Z := mk_int_mod_;
  int_eval_unop := λ op i,
    mk_int_ (IType i) $ Z_eval_unop op (int_to_Z_ i);
  int_eval_binop := λ op i1 i2,
    let σ := IType i1 in
    y ← Z_eval_binop (int_type_bits_ Csz σ) op (int_to_Z_ i1) (int_to_Z_ i2);
    mk_int_ σ y;
  int_cast := λ σ i,
    mk_int_ σ (int_to_Z_ i)
|}.

Context `{PropHolds (0 < Csz)%nat}.

Lemma int_bits_pos_ (σ : int_type) : (0 < int_type_bits_ Csz σ)%nat.
Proof. unfold int_type_bits_. apply NPeano.Nat.mul_pos_pos; auto. Qed.
Local Hint Resolve int_bits_pos_.
Lemma int_bits_pow_pred_ (σ : int_type) :
  2 * 2 ^ pred (int_type_bits_ Csz σ) = 2 ^ int_type_bits_ Csz σ.
Proof. by rewrite <-Z.pow_succ_r, Nat2Z.inj_pred, Z.succ_pred by auto. Qed.
Lemma int_bits_TuChar_:
  int_type_bits_ Csz (TuChar (Ti:=int_type)) = Csz.
Proof. unfold int_type_bits_. simpl. by rewrite plus_0_r. Qed.

Global Instance: IntEnvSpec int_type (int_ be Csz).
Proof.
  split.
  * unfold int_type_range; intros [[] n]; simpl; auto.
  * done.
  * done.
  * unfold int_type_range, TuChar_bits, TuChar; simpl.
    rewrite int_bits_pow_pred_. unfold int_type_bits_; simpl.
    by rewrite plus_0_r.
  * unfold int_type_range; intros; simpl. by rewrite int_bits_pow_pred_.
  * unfold encode_int; simpl. intros c.
    unfold encode_int_; simpl. esolve_elem_of.
  * unfold encode_int; simpl. intros x cs. rewrite elem_of_singleton.
    intros. subst. unfold encode_int_.
    by rewrite reverse_if_be_length, encode_Z_length.
  * intros τ cs x. unfold decode_int; simpl.
    unfold decode_int_. intros. by case_decide; simplify_equality.
  * intros τ cs x.  unfold decode_int, encode_int; simpl.
    unfold char, type_of_int, TuChar in cs; simpl in cs.
    unfold decode_int_, encode_int_. intros.
    case_decide as Hlen; simplify_equality; simpl. apply elem_of_singleton.
    rewrite <-(reverse_if_be_length cs) in Hlen.
    rewrite <-(reverse_if_be_involutive cs) at 1.
    destruct (reverse_if_be cs) as [|c cs']; simplify_equality.
    replace (ILen τ) with (length cs') by done.
    by rewrite encode_decode_Z.
  * intros cs x. unfold decode_int, encode_int; simpl.
    unfold decode_int_, encode_int_. rewrite elem_of_singleton. intros.
    case_decide as Hlen; simplify_equality.
    + f_equal. apply int_eq_. simpl. split; auto.
      rewrite reverse_if_be_involutive, decode_encode_Z. by apply int_mod_eq_.
    + by rewrite reverse_if_be_length, encode_Z_length in Hlen.
  * intros τ. cut (int_type_size τ = S (ILen τ)); [|done].
    generalize (int_type_size τ). intros sz ? c.
    unfold decode_int, int_to_Z; simpl.
    unfold decode_int_, int_to_Z_. rewrite IType_char. simpl.
    intros. destruct (decide_rel _ _ _) as [Hsz|Hsz]; simpl.
    + f_equal. apply int_eq_; simpl.
      by rewrite reverse_if_be_replicate, decode_Z_zeroes.
    + rewrite replicate_length in Hsz. congruence.
  * intros x. unfold int_lower, int_type_lower, int_upper, int_type_upper.
    unfold int_type_sign, int_type_range, type_of_int, int_to_Z; simpl.
    unfold int_to_Z_. destruct (ISign (IType x)).
    + unfold signed_Z. case_decide; split; auto.
      - transitivity 0; auto. apply Z.opp_nonpos_nonneg. auto.
      - apply Z.le_add_le_sub_r.
        destruct (int_type_bits_ Csz (IType x)) as [|n] eqn:?; simpl in *.
        { pose proof (int_bits_pos_ (IType x)). lia. }
        rewrite Nat2Z.inj_succ, Z.pow_succ_r; auto.
      - assert (0 < 2 ^ pred (int_type_bits_ Csz (IType x))) by auto.
        apply Z.lt_sub_lt_add_r.
        transitivity (2 ^ int_type_bits_ Csz (IType x)); auto.
    + rewrite int_bits_pow_pred_. auto.
  * done.
  * intros x. unfold type_of_int, int_of_Z, int_to_Z; simpl. unfold int_to_Z_.
    destruct (ISign _); simpl; rewrite ?mk_int_mod_INum; auto.
    unfold signed_Z. case_decide; rewrite ?mk_int_mod_INum; auto.
    apply int_eq_. simpl; split; auto.
    replace (INum x - 2 ^ int_type_bits_ Csz (IType x))
      with (INum x + (-1) * 2 ^ int_type_bits_ Csz (IType x)) by ring.
    rewrite Z.mod_add by auto. by apply int_mod_eq_.
  * intros τ x Hτ. unfold int_type_lower, int_type_upper.
    unfold int_type_range, int_to_Z, int_of_Z, int_type_sign in *; simpl in *.
    unfold int_to_Z_, signed_Z. simpl. rewrite Hτ, <-int_bits_pow_pred_.
    generalize (2 ^ pred (int_type_bits_ Csz τ)). intros y [??].
    destruct (Z_lt_le_dec x 0).
    { rewrite decide_false.
      + apply Z.sub_move_r. symmetry. apply Z.mod_unique_pos with (-1); auto.
      + apply Z.le_ngt. replace (x `mod` (2 * y)) with (x + 2 * y); auto.
        apply Z.mod_unique_pos with (-1); auto. }
    rewrite decide_true; [apply Z.mod_small; lia |].
    apply Z.le_lt_trans with x; auto using Z.mod_le.
  * intros τ x Hτ. unfold int_type_lower, int_type_upper. rewrite Hτ.
    unfold int_type_range, int_to_Z, int_of_Z, int_type_sign in *; simpl in *.
    unfold int_to_Z_. simpl. by rewrite Hτ, int_bits_pow_pred_.
  * intros op x τ y. unfold type_of_int, int_eval_unop; simpl.
    intros Hy. apply mk_int_type_ in Hy. congruence.
  * intros op x τ. unfold int_type_lower, int_type_upper, int_type_range.
    unfold type_of_int, int_type_sign, int_eval_unop, int_of_Z, int_to_Z; simpl.
    intros ? Hsi. subst. unfold mk_int_. rewrite Hsi.
    by simplify_option_equality.
  * intros op x τ. unfold type_of_int, int_type_sign, int_eval_unop; simpl.
    intros ? Hsi. subst. unfold mk_int_. by rewrite Hsi.
  * intros op x1 x2 τ y. unfold type_of_int, int_eval_binop; simpl.
    intros Hy. simplify_option_equality. apply mk_int_type_ in Hy. congruence.
  * intros op x1 x2 τ y. unfold int_type_lower, int_type_upper, int_type_range.
    unfold type_of_int, int_type_sign, int_eval_binop,
      int_of_Z, int_to_Z; simpl.
    intros ??? Hsi. subst. unfold mk_int_. rewrite Hsi.
    by simplify_option_equality.
  * intros op x1 x2 τ y.
    unfold type_of_int, int_type_sign, int_eval_binop; simpl.
    intros ??? Hsi. subst. unfold mk_int_. rewrite Hsi.
    by simplify_option_equality.
  * intros τ x y. unfold int_cast; simpl.
    intros Hy. by apply mk_int_type_ in Hy.
  * intros τ x. unfold int_type_lower, int_type_upper, int_type_range.
    unfold type_of_int, int_type_sign, int_cast, int_of_Z, int_to_Z; simpl.
    intros Hsi. unfold mk_int_. rewrite Hsi. by simplify_option_equality.
  * intros τ x. unfold int_type_sign, int_cast; simpl.
    intros Hsi. unfold mk_int_. by rewrite Hsi.
Qed.
End int.
