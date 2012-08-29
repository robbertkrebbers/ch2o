(* Copyright (c) 2012, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects some trivial facts on Coq's number data types [nat],
[N], and [Z], and introduces some useful notations. *)
Require Export PArith NArith ZArith.
Require Export base decidable fin_collections.

Infix "≤" := le : nat_scope.

Instance nat_eq_dec: ∀ x y : nat, Decision (x = y) := eq_nat_dec.
Instance positive_eq_dec: ∀ x y : positive, Decision (x = y) := Pos.eq_dec.
Notation "(~0)" := xO (only parsing) : positive_scope.
Notation "(~1)" := xI (only parsing) : positive_scope.

Infix "≤" := N.le : N_scope.
Notation "(≤)" := N.le (only parsing) : N_scope.

Instance N_eq_dec: ∀ x y : N, Decision (x = y) := N.eq_dec.
Program Instance N_le_dec (x y : N) : Decision (x ≤ y)%N :=
  match Ncompare x y with
  | Gt => right _
  | _ => left _
  end.
Next Obligation. congruence. Qed.

Infix "≤" := Z.le : Z_scope.
Notation "(≤)" := Z.le (only parsing) : Z_scope.
Instance Z_eq_dec: ∀ x y : Z, Decision (x = y) := Z.eq_dec.
Instance Z_le_dec: ∀ x y : Z, Decision (x ≤ y)%Z := Z_le_dec.

(** * Conversions *)
(** Converts an integer [x] into a natural number by giving [None] in case [x]
is negative. *)
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

(** The function [Z_decide_rel] is the more efficient variant of [Z_decide] for
decidable binary relations. It yields one if [R x y] and zero if not [R x y]. *)
Definition Z_decide_rel {A B} (R : A → B → Prop)
    {dec : ∀ x y, Decision (R x y)} (x : A) (y : B) : Z :=
  (if dec x y then 1 else 0)%Z.

(** * Fresh binary naturals *)
(** Given a finite set of binary naturals [N], we generate a fresh element by
taking the maximum, and adding one to it. *)
Definition Nmax `{Elements N C} : C → N := collection_fold Nmax 0%N.

Instance Nmax_proper `{FinCollection N C} : Proper ((≡) ==> (=)) Nmax.
Proof.
  apply collection_fold_proper. intros.
  rewrite !N.max_assoc. f_equal. apply N.max_comm.
Qed.

Lemma Nmax_max `{FinCollection N C} X x : x ∈ X → (x ≤ Nmax X)%N.
Proof.
  change ((λ b X, x ∈ X → (x ≤ b)%N) (collection_fold N.max 0%N X) X).
  apply collection_fold_ind.
  * solve_proper.
  * solve_elem_of.
  * solve_elem_of (eauto using N.le_max_l, N.le_max_r, N.le_trans).
Qed.

Instance Nfresh `{FinCollection N C} : Fresh N C := λ l, (1 + Nmax l)%N.
Instance Nfresh_spec `{FinCollection N C} : FreshSpec N C.
Proof.
  split.
  * intros. unfold fresh, Nfresh.
    setoid_replace X with Y; [easy |].
    now apply elem_of_equiv.
  * intros X E. assert (1 ≤ 0)%N as []; [| easy].
    apply N.add_le_mono_r with (Nmax X).
    now apply Nmax_max.
Qed.
