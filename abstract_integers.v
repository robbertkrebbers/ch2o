(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file describes an axiomatization of machine integers. It differs
in two important aspects from the specification in the C11 standard. *)

(** First of all, the C standard allows sign-and-magnitude, ones' complement,
and two's complement representations for signed integers. However, this design
dates back to the seventies (when machines using such representations actually
existed) and is hardly of any relevance today (all machines use two's
complement). Although our axiomatization does not explicitly enforce a two's
complement representation, any implementation has to be in order to give
an efficient implementation of our axiomatization of bitwise operations
(and [&], or [|], xor [^], and complement [~]). *)

(** We describe all operations, including bitwise operations, by their
translation to mathematical integers, so as to make the axiomatization more
uniform. The C standard, on the other hand, specifies bitwise operations using
the values of individual bits (and is quite unclear whether padding bits should
be taken into account), and uses mathematical values for all other operations.
In spire of our restriction to two's complement, we still allow multiple integer
representations for the same integer from any type apart from unsigned char.
Hence, an implementation is allowed to include padding bits. *)

(** Also, we attempt to be fairly minimal, and thereby also allow certain
implementations than are forbidden by the C standard. For example, we only
require two integer types to be present (unsigned char, and signed int), and
do not put restrictions on the range of these integer types. In future work we
may define a more restricted axiomatization that is a proper subclass of the
implementations allowed by the C standard. *)
Require Export prelude.

(** * Operations *)
(** We define inductive data types [unop] and [binop] describing the operations
that can be performed on integers, and give denotations using mathematical
integers. These denotations are used in the axiomatization to describe the
operations on machine integers. *)
Inductive unop :=
  | NegOp | ComplOp.
Inductive comp_kind :=
  | CEq | CLt | CLe.
Inductive binop :=
  | PlusOp | MinusOp | MultOp
  | ShiftLOp | ShiftROp
  | AndOp | OrOp | XorOp
  | DivOp | ModOp
  | CompOp : comp_kind → binop.
Notation EqOp := (CompOp CEq).
Notation LtOp := (CompOp CLt).
Notation LeOp := (CompOp CLe).

Instance unop_dec (op1 op2 : unop) : Decision (op1 = op2).
Proof. solve_decision. Defined.
Instance comp_kind_dec (c1 c2 : comp_kind) : Decision (c1 = c2).
Proof. solve_decision. Defined.
Instance binop_dec (op1 op2 : binop) : Decision (op1 = op2).
Proof. solve_decision. Defined.

Definition Z_eval_unop (op : unop) (x : Z) : Z :=
  match op with
  | NegOp => -x
  | ComplOp => Z.lnot x
  end%Z.

Definition Z_comp (c : comp_kind) : Z → Z → Prop :=
  match c with CEq => (=) | CLt => (<) | CLe => (≤) end%Z.
Instance Z_comp_dec c : ∀ x y, Decision (Z_comp c x y) :=
  match c return ∀ x y : Z, Decision (Z_comp c x y) with
  | CEq => decide_rel (=)
  | CLt => decide_rel (<)
  | CLe => decide_rel (≤)
  end%Z.
Definition nat_comp (c : comp_kind) : nat → nat → Prop :=
  match c with CEq => (=) | CLt => (<) | CLe => (≤) end.
Instance nat_comp_dec c : ∀ x y, Decision (nat_comp c x y) :=
  match c return ∀ x y : nat, Decision (nat_comp c x y) with
  | CEq => decide_rel (=)
  | CLt => decide_rel (<)
  | CLe => decide_rel (≤)
  end.

Definition Z_eval_binop (x2m : Z) (op : binop) (x1 x2 : Z) : option Z :=
  match op with
  | PlusOp => Some (x1 + x2)
  | MinusOp => Some (x1 - x2)
  | MultOp => Some (x1 * x2)
  | ShiftLOp => guard (0 ≤ x1); guard (0 ≤ x2 < x2m); Some (Z.shiftl x1 x2)
  | ShiftROp => guard (0 ≤ x1); guard (0 ≤ x2 < x2m); Some (Z.shiftr x1 x2)
  | AndOp => Some (Z.land x1 x2)
  | OrOp => Some (Z.lor x1 x2)
  | XorOp => Some (Z.lxor x1 x2)
  | DivOp => guard (x2 ≠ 0); Some (x1 `quot` x2)
  | ModOp => guard (x2 ≠ 0); Some (x1 `rem` x2)
  | CompOp c => Some $ Z_of_sumbool (decide_rel (Z_comp c) x1 x2)
  end%Z.

(** We consider both signed and unsigned integers. Signed integers are an
interval between [-x] (included) and [x] of mathematical integers.
Similarly, unsigned integers are an interval between [0] (included) and [2 * x]
of mathematical integers. *)
Inductive signedness := Signed | Unsigned.
Instance signedness_eq_dec (s1 s2 : signedness) : Decision (s1 = s2).
Proof. solve_decision. Defined.

(** * The required operations on machine integers *)
(** The axiomatization of machine integers is parametrized by two data types:
- [Ti] represents the set of integer types, and,
- [Vi] represents the set of integer values.

We require various operations to be implemented on these data types. *)
Local Unset Elimination Schemes.

Class IntEnv (Ti Vi : Set) := {
  int_type_size : Ti → nat;
  int_type_sign : Ti → signedness;
  int_type_range : Ti → Z;
  type_of_int : Vi → Ti;
  TuChar : Ti;
  TuChar_bits : nat;
  TsInt : Ti;
  char := { x | type_of_int x = TuChar };
  encode_int : Vi → listset (list char);
  decode_int : Ti → list char → option Vi;
  int_to_Z : Vi → Z;
  int_of_Z : Ti → Z → Vi;
  int_eval_unop : unop → Vi → option Vi;
  int_eval_binop : binop → Vi → Vi → option Vi;
  int_cast : Ti → Vi → option Vi;
  int_type_eq_dec (τ1 τ2 : Ti) :> Decision (τ1 = τ2);
  int_eq_dec (x1 x2 : Vi) :> Decision (x1 = x2)
}.

Arguments int_type_size _ _ _ _ : simpl never.
Arguments int_type_sign _ _ _ _ : simpl never.
Arguments int_type_range _ _ _ _ : simpl never.
Arguments type_of_int _ _ _ _ : simpl never.
Arguments TuChar _ _ _ : simpl never.
Arguments TuChar_bits _ _ _ : simpl never.
Arguments TsInt _ _ _ : simpl never.
Arguments char _ _ {_} : clear implicits.
Arguments encode_int _ _ _ _ : simpl never.
Arguments decode_int _ _ _ _ _ : simpl never.
Arguments int_to_Z _ _ _ _ : simpl never.
Arguments int_of_Z _ _ _ _ _ : simpl never.
Arguments int_eval_unop _ _ _ _ _ : simpl never.
Arguments int_eval_binop _ _ _ _ _ _ : simpl never.
Arguments int_cast _ _ _ _ _ : simpl never.

Definition int_type_lower `{IntEnv Ti Vi} (τ : Ti) : Z :=
  match int_type_sign τ with
  | Signed => -int_type_range τ
  | Unsigned => 0
  end%Z.
Definition int_type_upper `{IntEnv Ti Vi} (τ : Ti) : Z :=
  match int_type_sign τ with
  | Signed => int_type_range τ
  | Unsigned => 2 * int_type_range τ
  end%Z.
Definition int_type_bits `{IntEnv Ti Vi} (τ : Ti) : nat :=
  int_type_size τ * TuChar_bits.

Definition int_sign `{IntEnv Ti Vi} : Vi → signedness :=
  int_type_sign ∘ type_of_int.
Definition int_lower `{IntEnv Ti Vi} : Vi → Z := int_type_lower ∘ type_of_int.
Definition int_upper `{IntEnv Ti Vi} : Vi → Z := int_type_upper ∘ type_of_int.

Definition maybe_int_of_Z `{IntEnv Ti Vi} (τ : Ti) (x : Z) : option Vi :=
  guard (int_type_lower τ ≤ x ≤ int_type_upper τ)%Z;
  Some (int_of_Z τ x).
Definition int_true `{IntEnv Ti Vi} : Vi := int_of_Z TsInt 1.
Definition int_false `{IntEnv Ti Vi} : Vi := int_of_Z TsInt 0.
Definition int_of_sumbool `{IntEnv Ti Vi} {P Q} (p : {P} + {Q}) : Vi :=
  (if p then int_true else int_false)%Z.

(** * The axiomatization of machine integers *)
(** The following class defines the laws that an implementation of machine
integers should satisfy. Most of these laws are straightforward. Keep in mind,
that like the C standard, overflow of unsigned integers is defined behavior
(namely, it wraps modulo), whereas overflow of signed integers is undefined
behavior. As [int_eval_unop], [int_eval_binop], and [int_cast], are partial
functions, an implementation is thus free to decide whether to yield a bogus
values, or to make the result actual undefined behavior. *)
Class IntEnvSpec Ti Vi `{IntEnv Ti Vi} := {
  int_type_range_pos τ : (0 < int_type_range τ)%Z;
  size_TuChar : int_type_size TuChar = 1;
  sign_TuChar : int_type_sign TuChar = Unsigned;
  range_TuChar : (2 * int_type_range TuChar = 2 ^ TuChar_bits)%Z;
  int_type_size_enough (τ: Ti) : (2 * int_type_range τ ≤ 2 ^ int_type_bits τ)%Z;

  encode_int_exists x : ∃ cs, cs ∈ encode_int x;
  encode_int_length x cs :
    cs ∈ encode_int x → length cs = int_type_size (type_of_int x);
  decode_int_typed τ cs x : decode_int τ cs = Some x → type_of_int x = τ;
  decode_encode_int τ cs x : decode_int τ cs = Some x → cs ∈ encode_int x;
  encode_decode_int (cs : list (char Ti Vi)) x :
    cs ∈ encode_int x → decode_int (type_of_int x) cs = Some x;
  decode_int_zeros τ c :
    int_to_Z (`c) = 0%Z →
    decode_int τ (replicate (int_type_size τ) c) = Some (int_of_Z τ 0);

  int_to_Z_in_range x : (int_lower x ≤ int_to_Z x < int_upper x)%Z;
  int_of_Z_typed τ x : type_of_int (int_of_Z τ x) = τ;
  int_of_to_Z x : int_of_Z (type_of_int x) (int_to_Z x) = x;
  int_to_of_Z_signed τ x :
    int_type_sign τ = Signed → (int_type_lower τ ≤ x < int_type_upper τ)%Z →
    int_to_Z (int_of_Z τ x) = x;
  int_to_of_Z_unsigned τ x :
    int_type_sign τ = Unsigned →
    int_to_Z (int_of_Z τ x) = (x `mod` int_type_upper τ)%Z;

  int_unop_typed op x τ y :
    int_eval_unop op x = Some y →
    type_of_int x = τ → type_of_int y = τ;
  int_unop_signed op x τ :
    type_of_int x = τ → int_type_sign τ = Signed →
    (int_type_lower τ ≤ Z_eval_unop op (int_to_Z x) < int_type_upper τ)%Z →
    int_eval_unop op x = Some (int_of_Z τ (Z_eval_unop op (int_to_Z x)));
  int_unop_unsigned op x τ :
    type_of_int x = τ → int_type_sign τ = Unsigned →
    int_eval_unop op x = Some (int_of_Z τ (Z_eval_unop op (int_to_Z x)));

  int_binop_typed op x1 x2 τ y :
    int_eval_binop op x1 x2 = Some y →
    type_of_int x1 = τ → type_of_int x2 = τ → type_of_int y = τ;
  int_binop_signed op x1 x2 τ y :
    Z_eval_binop (int_type_bits τ) op (int_to_Z x1) (int_to_Z x2) = Some y →
    type_of_int x1 = τ → type_of_int x2 = τ → int_type_sign τ = Signed →
    (int_type_lower τ ≤ y < int_type_upper τ)%Z →
    int_eval_binop op x1 x2 = Some (int_of_Z τ y);
  int_binop_unsigned op x1 x2 τ y :
    Z_eval_binop (int_type_bits τ) op (int_to_Z x1) (int_to_Z x2) = Some y →
    type_of_int x1 = τ → type_of_int x2 = τ → int_type_sign τ = Unsigned →
    int_eval_binop op x1 x2 = Some (int_of_Z τ y);

  int_cast_typed τ x y : int_cast τ x = Some y → type_of_int y = τ;
  int_cast_signed τ x :
    int_type_sign τ = Signed →
    (int_type_lower τ ≤ int_to_Z x < int_type_upper τ)%Z →
    int_cast τ x = Some (int_of_Z τ (int_to_Z x));
  int_cast_unsigned τ x :
    int_type_sign τ = Unsigned → int_cast τ x = Some (int_of_Z τ (int_to_Z x))
}.

(** * Theorems *)
(** Some derived properties. *)
Section abstract_integers.
  Context `{IntEnvSpec Ti Vi}.

  Lemma int_type_size_ne_0 τ : int_type_size τ ≠ 0.
  Proof.
    intros Hτ. eapply Zlt_not_le, (int_type_size_enough τ).
    unfold int_type_bits. rewrite Hτ, mult_0_l, Z.pow_0_r.
    pose proof (int_type_range_pos τ). lia.
  Qed.
  Lemma int_type_size_pos τ : (0 < int_type_size τ)%Z.
  Proof. pose proof (int_type_size_ne_0 τ). lia. Qed.

  Lemma decode_int_nil τ : decode_int τ [] = None.
  Proof.
    destruct (decode_int τ []) eqn:E; [|done].
    apply decode_encode_int, encode_int_length in E.
    by destruct (int_type_size_ne_0 (type_of_int v)).
  Qed.
End abstract_integers.
