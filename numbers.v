(* Copyright (c) 2012, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects some trivial facts on the Coq types [nat] and [N] for
natural numbers, and the type [Z] for integers. It also declares some useful
notations. *)
Require Export PArith NArith ZArith.
Require Export base decidable.

Infix "≤" := le : nat_scope.
Instance nat_eq_dec: ∀ x y : nat, Decision (x = y) := eq_nat_dec.

Lemma lt_n_SS n : n < S (S n).
Proof. auto with arith. Qed.
Lemma lt_n_SSS n : n < S (S (S n)).
Proof. auto with arith. Qed.

Instance positive_eq_dec: ∀ x y : positive, Decision (x = y) := Pos.eq_dec.
Notation "(~0)" := xO (only parsing) : positive_scope.
Notation "(~1)" := xI (only parsing) : positive_scope.

Infix "≤" := N.le : N_scope.
Notation "(≤)" := N.le (only parsing) : N_scope.
Notation "(<)" := N.lt (only parsing) : N_scope.

Instance N_eq_dec: ∀ x y : N, Decision (x = y) := N.eq_dec.
Program Instance N_le_dec (x y : N) : Decision (x ≤ y)%N :=
  match Ncompare x y with
  | Gt => right _
  | _ => left _
  end.
Next Obligation. congruence. Qed.
Program Instance N_lt_dec (x y : N) : Decision (x < y)%N :=
  match Ncompare x y with
  | Lt => left _
  | _ => right _
  end.
Next Obligation. congruence. Qed.

Infix "≤" := Z.le : Z_scope.
Notation "(≤)" := Z.le (only parsing) : Z_scope.
Notation "(<)" := Z.lt (only parsing) : Z_scope.
Instance Z_eq_dec: ∀ x y : Z, Decision (x = y) := Z.eq_dec.
Instance Z_le_dec: ∀ x y : Z, Decision (x ≤ y)%Z := Z_le_dec.
Instance Z_lt_dec: ∀ x y : Z, Decision (x < y)%Z := Z_lt_dec.

(** * Conversions *)
(** The function [Z_to_option_N] converts an integer [x] into a natural number
by giving [None] in case [x] is negative. *)
Definition Z_to_option_N (x : Z) : option N :=
  match x with
  | Z0 => Some N0
  | Zpos p => Some (Npos p)
  | Zneg _ => None
  end.

(** The function [Z_decide] converts a decidable proposition [P] into an integer
by yielding one if [P] holds and zero if [P] does not. *)
Definition Z_decide (P : Prop) {dec : Decision P} : Z :=
  (if dec then 1 else 0)%Z.

(** The function [Z_decide_rel] is the more efficient variant of [Z_decide] when
used for binary relations. It yields one if [R x y] and zero if not [R x y]. *)
Definition Z_decide_rel {A B} (R : A → B → Prop)
    {dec : ∀ x y, Decision (R x y)} (x : A) (y : B) : Z :=
  (if dec x y then 1 else 0)%Z.
