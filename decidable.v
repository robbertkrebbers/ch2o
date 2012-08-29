(* Copyright (c) 2012, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects theorems, definitions, tactics, related to propositions
with a decidable equality. Such propositions are collected by the [Decision]
type class. *)
Require Export base.

(** We introduce [decide_rel] to avoid inefficienct computation due to eager
evaluation of propositions by [vm_compute]. This inefficiency occurs if
[(x = y) := (f x = f y)] as [decide (x = y)] evaluates to [decide (f x = f y)]
which then might lead to evaluation of [f x] and [f y]. Using [decide_rel]
we hide [f] under a lambda abstraction to avoid this unnecessary evaluation. *)
Definition decide_rel {A B} (R : A → B → Prop) {dec : ∀ x y, Decision (R x y)}
  (x : A) (y : B) : Decision (R x y) := dec x y.
Lemma decide_rel_correct {A B} (R : A → B → Prop) `{∀ x y, Decision (R x y)}
  (x : A) (y : B) : decide_rel R x y = decide (R x y).
Proof. easy. Qed.

(** The tactic [case_decide] performs case analysis on an arbitrary occurrence
of [decide] or [decide_rel] in the conclusion or assumptions. *)
Ltac case_decide :=
  match goal with
  | H : context [@decide ?P ?dec] |- _ =>
    destruct (@decide P dec)
  | H : context [@decide_rel _ _ ?R ?x ?y ?dec] |- _ =>
    destruct (@decide_rel _ _ R x y dec)
  | |- context [@decide ?P ?dec] =>
    destruct (@decide P dec)
  | |- context [@decide_rel _ _ ?R ?x ?y ?dec] =>
    destruct (@decide_rel _ _ R x y dec)
  end.

(** The tactic [solve_decision] uses Coq's [decide equality] tactic together
with instance resolution to automatically generate decision procedures. *)
Ltac solve_trivial_decision :=
  match goal with
  | [ |- Decision (?P) ] => apply _
  | [ |- sumbool ?P (¬?P) ] => change (Decision P); apply _
  end.
Ltac solve_decision :=
  intros; first [ solve_trivial_decision
                | unfold Decision; decide equality; solve_trivial_decision ].

(** We can convert decidable propositions to booleans. *)
Definition bool_decide (P : Prop) {dec : Decision P} : bool :=
  if dec then true else false.

Lemma bool_decide_unpack (P : Prop) {dec : Decision P} : bool_decide P → P.
Proof. unfold bool_decide. now destruct dec. Qed.
Lemma bool_decide_pack (P : Prop) {dec : Decision P} : P → bool_decide P.
Proof. unfold bool_decide. now destruct dec. Qed.

(** * Decidable Sigma types *)
(** Leibniz equality on Sigma types requires the equipped proofs to be
equal as Coq does not support proof irrelevance. For decidable we
propositions we define the type [dsig P] whose Leibniz equality is proof
irrelevant. That is [∀ x y : dsig P, x = y ↔ `x = `y]. *)
Definition dsig `(P : A → Prop) `{∀ x : A, Decision (P x)} :=
  { x | bool_decide (P x) }.
Definition proj2_dsig `{∀ x : A, Decision (P x)} (x : dsig P) : P (`x) :=
  bool_decide_unpack _ (proj2_sig x).
Definition dexist `{∀ x : A, Decision (P x)} (x : A) (p : P x) : dsig P :=
  x↾bool_decide_pack _ p.

Lemma dsig_eq {A} (P : A → Prop) {dec : ∀ x, Decision (P x)}
  (x y : dsig P) : x = y ↔ `x = `y.
Proof.
  split.
  * destruct x, y. apply proj1_sig_inj.
  * intro. destruct x as [x Hx], y as [y Hy].
    simpl in *. subst. f_equal.
    revert Hx Hy. case (bool_decide (P y)).
    + now intros [] [].
    + easy.
Qed.

(** * Instances of Decision *)
(** Instances of [Decision] for operators of propositional logic. *)
Program Instance True_dec: Decision True := left _.
Program Instance False_dec: Decision False := right _.
Program Instance and_dec `(P_dec : Decision P) `(Q_dec : Decision Q) :
    Decision (P ∧ Q) :=
  match P_dec with
  | left _ => match Q_dec with left _ => left _ | right _ => right _ end
  | right _ => right _
  end.
Solve Obligations using intuition.
Program Instance or_dec `(P_dec : Decision P) `(Q_dec : Decision Q) :
    Decision (P ∨ Q) :=
  match P_dec with
  | left _ => left _
  | right _ => match Q_dec with left _ => left _ | right _ => right _ end
  end.
Solve Obligations using intuition.

(** Instances of [Decision] for common data types. *)
Program Instance prod_eq_dec `(A_dec : ∀ x y : A, Decision (x = y))
    `(B_dec : ∀ x y : B, Decision (x = y)) (x y : A * B) : Decision (x = y) :=
  match A_dec (fst x) (fst y) with
  | left _ =>
    match B_dec (snd x) (snd y) with
    | left _ => left _
    | right _ => right _
    end
  | right _ => right _
  end.
Solve Obligations using intuition (simpl;congruence).
