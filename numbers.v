(* Copyright (c) 2012, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects some trivial facts on the Coq types [nat] and [N] for
natural numbers, and the type [Z] for integers. It also declares some useful
notations. *)
Require Export PArith NArith ZArith.
Require Export base decidable.

Coercion Z.of_nat : nat >-> Z.

Reserved Notation "x ≤ y ≤ z" (at level 70, y at next level).
Reserved Notation "x ≤ y < z" (at level 70, y at next level).
Reserved Notation "x < y < z" (at level 70, y at next level).
Reserved Notation "x < y ≤ z" (at level 70, y at next level).

Infix "≤" := le : nat_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z)%nat : nat_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z)%nat : nat_scope.
Notation "x < y < z" := (x < y ∧ y < z)%nat : nat_scope.
Notation "x < y ≤ z" := (x < y ∧ y ≤ z)%nat : nat_scope.
Notation "(≤)" := le (only parsing) : nat_scope.
Notation "(<)" := lt (only parsing) : nat_scope.

Infix "`div`" := NPeano.div (at level 35) : nat_scope.
Infix "`mod`" := NPeano.modulo (at level 35) : nat_scope.

Instance nat_eq_dec: ∀ x y : nat, Decision (x = y) := eq_nat_dec.
Instance nat_le_dec: ∀ x y : nat, Decision (x ≤ y) := le_dec.
Instance nat_lt_dec: ∀ x y : nat, Decision (x < y) := lt_dec.
Instance nat_inhabited: Inhabited nat := populate 0%nat.

Lemma lt_n_SS n : n < S (S n).
Proof. auto with arith. Qed.
Lemma lt_n_SSS n : n < S (S (S n)).
Proof. auto with arith. Qed.

Definition sum_list_with {A} (f : A → nat) : list A → nat :=
  fix go l :=
  match l with
  | [] => 0
  | x :: l => f x + go l
  end.
Notation sum_list := (sum_list_with id).

Instance positive_eq_dec: ∀ x y : positive, Decision (x = y) := Pos.eq_dec.
Instance positive_inhabited: Inhabited positive := populate 1%positive.

Notation "(~0)" := xO (only parsing) : positive_scope.
Notation "(~1)" := xI (only parsing) : positive_scope.

Instance: Injective (=) (=) xO.
Proof. by injection 1. Qed.
Instance: Injective (=) (=) xI.
Proof. by injection 1. Qed.

Infix "≤" := N.le : N_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z)%N : N_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z)%N : N_scope.
Notation "x < y < z" := (x < y ∧ y < z)%N : N_scope.
Notation "x < y ≤ z" := (x < y ∧ y ≤ z)%N : N_scope.
Notation "(≤)" := N.le (only parsing) : N_scope.
Notation "(<)" := N.lt (only parsing) : N_scope.

Infix "`div`" := N.div (at level 35) : N_scope.
Infix "`mod`" := N.modulo (at level 35) : N_scope.

Instance: Injective (=) (=) Npos.
Proof. by injection 1. Qed.

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
Instance N_inhabited: Inhabited N := populate 1%N.

Infix "≤" := Z.le : Z_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z)%Z : Z_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z)%Z : Z_scope.
Notation "x < y < z" := (x < y ∧ y < z)%Z : Z_scope.
Notation "x < y ≤ z" := (x < y ∧ y ≤ z)%Z : Z_scope.
Notation "(≤)" := Z.le (only parsing) : Z_scope.
Notation "(<)" := Z.lt (only parsing) : Z_scope.

Infix "`div`" := Z.div (at level 35) : Z_scope.
Infix "`mod`" := Z.modulo (at level 35) : Z_scope.

Instance Z_eq_dec: ∀ x y : Z, Decision (x = y) := Z.eq_dec.
Instance Z_le_dec: ∀ x y : Z, Decision (x ≤ y)%Z := Z_le_dec.
Instance Z_lt_dec: ∀ x y : Z, Decision (x < y)%Z := Z_lt_dec.
Instance Z_inhabited: Inhabited Z := populate 1%Z.

(** * Conversions *)
(** The function [Z_to_option_N] converts an integer [x] into a natural number
by giving [None] in case [x] is negative. *)
Definition Z_to_option_N (x : Z) : option N :=
  match x with
  | Z0 => Some N0
  | Zpos p => Some (Npos p)
  | Zneg _ => None
  end.
Definition Z_to_option_nat (x : Z) : option nat :=
  match x with
  | Z0 => Some 0
  | Zpos p => Some (Pos.to_nat p)
  | Zneg _ => None
  end.

Lemma Z_to_option_N_Some x y :
  Z_to_option_N x = Some y ↔ (0 ≤ x)%Z ∧ y = Z.to_N x.
Proof.
  split.
  * intros. by destruct x; simpl in *; simplify_equality;
      auto using Zle_0_pos.
  * intros [??]. subst. destruct x; simpl; auto; lia.
Qed.
Lemma Z_to_option_N_Some_alt x y :
  Z_to_option_N x = Some y ↔ (0 ≤ x)%Z ∧ x = Z.of_N y.
Proof.
  rewrite Z_to_option_N_Some.
  split; intros [??]; subst; auto using N2Z.id, Z2N.id, eq_sym.
Qed.

Lemma Z_to_option_nat_Some x y :
  Z_to_option_nat x = Some y ↔ (0 ≤ x)%Z ∧ y = Z.to_nat x.
Proof.
  split.
  * intros. by destruct x; simpl in *; simplify_equality;
      auto using Zle_0_pos.
  * intros [??]. subst. destruct x; simpl; auto; lia.
Qed.
Lemma Z_to_option_nat_Some_alt x y :
  Z_to_option_nat x = Some y ↔ (0 ≤ x)%Z ∧ x = Z.of_nat y.
Proof.
  rewrite Z_to_option_nat_Some.
  split; intros [??]; subst; auto using Nat2Z.id, Z2Nat.id, eq_sym.
Qed.
Lemma Z_to_option_of_nat x :
  Z_to_option_nat (Z.of_nat x) = Some x.
Proof. apply Z_to_option_nat_Some_alt. auto using Nat2Z.is_nonneg. Qed.

(** The function [Z_of_sumbool] converts a sumbool [P] into an integer
by yielding one if [P] and zero if [Q]. *)
Definition Z_of_sumbool {P Q : Prop} (p : {P} + {Q}) : Z :=
  (if p then 1 else 0)%Z.

(** Some correspondence lemmas between [nat] and [N] that are not part of the
standard library. We declare a hint database [natify] to rewrite a goal
involving [N] into a corresponding variant involving [nat]. *)
Lemma N_to_nat_lt x y : N.to_nat x < N.to_nat y ↔ (x < y)%N.
Proof. by rewrite <-N.compare_lt_iff, nat_compare_lt, N2Nat.inj_compare. Qed.
Lemma N_to_nat_le x y : N.to_nat x ≤ N.to_nat y ↔ (x ≤ y)%N.
Proof. by rewrite <-N.compare_le_iff, nat_compare_le, N2Nat.inj_compare. Qed.
Lemma N_to_nat_0 : N.to_nat 0 = 0.
Proof. done. Qed.
Lemma N_to_nat_1 : N.to_nat 1 = 1.
Proof. done. Qed.
Lemma N_to_nat_div x y : N.to_nat (x `div` y) = N.to_nat x `div` N.to_nat y.
Proof.
  destruct (decide (y = 0%N)).
  { subst. by destruct x. }
  apply NPeano.Nat.div_unique with (N.to_nat (x `mod` y)).
  { by apply N_to_nat_lt, N.mod_lt. }
  rewrite (N.div_unique_exact (x * y) y x), N.div_mul by lia.
  by rewrite <-N2Nat.inj_mul, <-N2Nat.inj_add, <-N.div_mod.
Qed.
(* We have [x `mod` 0 = 0] on [nat], and [x `mod` 0 = x] on [N]. *)
Lemma N_to_nat_mod x y :
  y ≠ 0%N →
  N.to_nat (x `mod` y) = N.to_nat x `mod` N.to_nat y.
Proof.
  intros.
  apply NPeano.Nat.mod_unique with (N.to_nat (x `div` y)).
  { by apply N_to_nat_lt, N.mod_lt. }
  rewrite (N.div_unique_exact (x * y) y x), N.div_mul by lia.
  by rewrite <-N2Nat.inj_mul, <-N2Nat.inj_add, <-N.div_mod.
Qed.

Hint Rewrite <-N2Nat.inj_iff : natify.
Hint Rewrite <-N_to_nat_lt : natify.
Hint Rewrite <-N_to_nat_le : natify.
Hint Rewrite Nat2N.id : natify.
Hint Rewrite N2Nat.inj_add : natify.
Hint Rewrite N2Nat.inj_mul : natify.
Hint Rewrite N2Nat.inj_sub : natify.
Hint Rewrite N2Nat.inj_succ : natify.
Hint Rewrite N2Nat.inj_pred : natify.
Hint Rewrite N_to_nat_div : natify.
Hint Rewrite N_to_nat_0 : natify.
Hint Rewrite N_to_nat_1 : natify.
Ltac natify := repeat autorewrite with natify in *.

Hint Extern 100 (Nlt _ _) => natify : natify.
Hint Extern 100 (Nle _ _) => natify : natify.
Hint Extern 100 (@eq N _ _) => natify : natify.
Hint Extern 100 (lt _ _) => natify : natify.
Hint Extern 100 (le _ _) => natify : natify.
Hint Extern 100 (@eq nat _ _) => natify : natify.

Instance: ∀ x, PropHolds (0 < x)%N → PropHolds (0 < N.to_nat x).
Proof. unfold PropHolds. intros. by natify. Qed.
Instance: ∀ x, PropHolds (0 ≤ x)%N → PropHolds (0 ≤ N.to_nat x).
Proof. unfold PropHolds. intros. by natify. Qed.
