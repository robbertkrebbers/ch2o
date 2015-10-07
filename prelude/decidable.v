(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects theorems, definitions, tactics, related to propositions
with a decidable equality. Such propositions are collected by the [Decision]
type class. *)
Require Export proof_irrel.

Hint Extern 200 (Decision _) => progress (lazy beta) : typeclass_instances.

Lemma dec_stable `{Decision P} : ¬¬P → P.
Proof. firstorder. Qed.

Lemma Is_true_reflect (b : bool) : reflect b b.
Proof. destruct b. by left. right. intros []. Qed.
Instance: Injective (=) (↔) Is_true.
Proof. intros [] []; simpl; intuition. Qed.

(** We introduce [decide_rel] to avoid inefficienct computation due to eager
evaluation of propositions by [vm_compute]. This inefficiency occurs if
[(x = y) := (f x = f y)] as [decide (x = y)] evaluates to [decide (f x = f y)]
which then might lead to evaluation of [f x] and [f y]. Using [decide_rel]
we hide [f] under a lambda abstraction to avoid this unnecessary evaluation. *)
Definition decide_rel {A B} (R : A → B → Prop) {dec : ∀ x y, Decision (R x y)}
  (x : A) (y : B) : Decision (R x y) := dec x y.
Lemma decide_rel_correct {A B} (R : A → B → Prop) `{∀ x y, Decision (R x y)}
  (x : A) (y : B) : decide_rel R x y = decide (R x y).
Proof. done. Qed.

Lemma decide_True {A} `{Decision P} (x y : A) :
  P → (if decide P then x else y) = x.
Proof. by destruct (decide P). Qed.
Lemma decide_False {A} `{Decision P} (x y : A) :
  ¬P → (if decide P then x else y) = y.
Proof. by destruct (decide P). Qed.
Lemma decide_iff {A} P Q `{Decision P, Decision Q} (x y : A) :
  (P ↔ Q) → (if decide P then x else y) = (if decide Q then x else y).
Proof. intros [??]. destruct (decide P), (decide Q); intuition. Qed.

(** The tactic [destruct_decide] destructs a sumbool [dec]. If one of the
components is double negated, it will try to remove the double negation. *)
Tactic Notation "destruct_decide" constr(dec) "as" ident(H) :=
  destruct dec as [H|H];
  try match type of H with
  | ¬¬_ => apply dec_stable in H
  end.
Tactic Notation "destruct_decide" constr(dec) :=
  let H := fresh in destruct_decide dec as H.

(** The tactic [case_decide] performs case analysis on an arbitrary occurrence
of [decide] or [decide_rel] in the conclusion or hypotheses. *)
Tactic Notation "case_decide" "as" ident(Hd) :=
  match goal with
  | H : context [@decide ?P ?dec] |- _ =>
    destruct_decide (@decide P dec) as Hd
  | H : context [@decide_rel _ _ ?R ?x ?y ?dec] |- _ =>
    destruct_decide (@decide_rel _ _ R x y dec) as Hd
  | |- context [@decide ?P ?dec] =>
    destruct_decide (@decide P dec) as Hd
  | |- context [@decide_rel _ _ ?R ?x ?y ?dec] =>
    destruct_decide (@decide_rel _ _ R x y dec) as Hd
  end.
Tactic Notation "case_decide" :=
  let H := fresh in case_decide as H.

(** The tactic [solve_decision] uses Coq's [decide equality] tactic together
with instance resolution to automatically generate decision procedures. *)
Ltac solve_trivial_decision :=
  match goal with
  | |- Decision (?P) => apply _
  | |- sumbool ?P (¬?P) => change (Decision P); apply _
  end.
Ltac solve_decision := intros; first
  [ solve_trivial_decision
  | unfold Decision; decide equality; solve_trivial_decision ].

(** The following combinators are useful to create Decision proofs in
combination with the [refine] tactic. *)
Notation swap_if S := (match S with left H => right H | right H => left H end).
Notation cast_if S := (if S then left _ else right _).
Notation cast_if_and S1 S2 := (if S1 then cast_if S2 else right _).
Notation cast_if_and3 S1 S2 S3 := (if S1 then cast_if_and S2 S3 else right _).
Notation cast_if_and4 S1 S2 S3 S4 :=
  (if S1 then cast_if_and3 S2 S3 S4 else right _).
Notation cast_if_and5 S1 S2 S3 S4 S5 :=
  (if S1 then cast_if_and4 S2 S3 S4 S5 else right _).
Notation cast_if_and6 S1 S2 S3 S4 S5 S6 :=
  (if S1 then cast_if_and5 S2 S3 S4 S5 S6 else right _).
Notation cast_if_or S1 S2 := (if S1 then left _ else cast_if S2).
Notation cast_if_or3 S1 S2 S3 := (if S1 then left _ else cast_if_or S2 S3).
Notation cast_if_not_or S1 S2 := (if S1 then cast_if S2 else left _).
Notation cast_if_not S := (if S then right _ else left _).

(** We can convert decidable propositions to booleans. *)
Definition bool_decide (P : Prop) {dec : Decision P} : bool :=
  if dec then true else false.

Lemma bool_decide_reflect P `{dec : Decision P} : reflect P (bool_decide P).
Proof. unfold bool_decide. destruct dec. by left. by right. Qed.

Tactic Notation "case_bool_decide" "as" ident (Hd) :=
  match goal with
  | H : context [@bool_decide ?P ?dec] |- _ =>
    destruct_decide (@bool_decide_reflect P dec) as Hd
  | |- context [@bool_decide ?P ?dec] =>
    destruct_decide (@bool_decide_reflect P dec) as Hd
  end.
Tactic Notation "case_bool_decide" :=
  let H := fresh in case_bool_decide as H.

Lemma bool_decide_spec (P : Prop) {dec : Decision P} : bool_decide P ↔ P.
Proof. unfold bool_decide. by destruct dec. Qed.
Lemma bool_decide_unpack (P : Prop) {dec : Decision P} : bool_decide P → P.
Proof. by rewrite bool_decide_spec. Qed.
Lemma bool_decide_pack (P : Prop) {dec : Decision P} : P → bool_decide P.
Proof. by rewrite bool_decide_spec. Qed.
Lemma bool_decide_true (P : Prop) `{Decision P} : P → bool_decide P = true.
Proof. by case_bool_decide. Qed.
Lemma bool_decide_false (P : Prop) `{Decision P} : ¬P → bool_decide P = false.
Proof. by case_bool_decide. Qed.
Lemma bool_decide_iff (P Q : Prop) `{Decision P, Decision Q} :
  (P ↔ Q) → bool_decide P = bool_decide Q.
Proof. repeat case_bool_decide; tauto. Qed.

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
Lemma dsig_eq `(P : A → Prop) `{∀ x, Decision (P x)}
  (x y : dsig P) : x = y ↔ `x = `y.
Proof. apply (sig_eq_pi _). Qed.
Lemma dexists_proj1 `(P : A → Prop) `{∀ x, Decision (P x)} (x : dsig P) p :
  dexist (`x) p = x.
Proof. by apply dsig_eq. Qed.

(** * Instances of Decision *)
(** Instances of [Decision] for operators of propositional logic. *)
Instance True_dec: Decision True := left I.
Instance False_dec: Decision False := right (False_rect False).
Instance Is_true_dec b : Decision (Is_true b).
Proof. destruct b; apply _. Defined.

Section prop_dec.
  Context `(P_dec : Decision P) `(Q_dec : Decision Q).

  Global Instance not_dec: Decision (¬P).
  Proof. refine (cast_if_not P_dec); intuition. Defined.
  Global Instance and_dec: Decision (P ∧ Q).
  Proof. refine (cast_if_and P_dec Q_dec); intuition. Defined.
  Global Instance or_dec: Decision (P ∨ Q).
  Proof. refine (cast_if_or P_dec Q_dec); intuition. Defined.
  Global Instance impl_dec: Decision (P → Q).
  Proof. refine (if P_dec then cast_if Q_dec else left _); intuition. Defined.
End prop_dec.
Instance iff_dec `(P_dec : Decision P) `(Q_dec : Decision Q) :
  Decision (P ↔ Q) := and_dec _ _.

(** Instances of [Decision] for common data types. *)
Instance bool_eq_dec (x y : bool) : Decision (x = y).
Proof. solve_decision. Defined.
Instance unit_eq_dec (x y : unit) : Decision (x = y).
Proof. solve_decision. Defined.
Instance prod_eq_dec `(A_dec : ∀ x y : A, Decision (x = y))
  `(B_dec : ∀ x y : B, Decision (x = y)) (x y : A * B) : Decision (x = y).
Proof. solve_decision. Defined.
Instance sum_eq_dec `(A_dec : ∀ x y : A, Decision (x = y))
  `(B_dec : ∀ x y : B, Decision (x = y)) (x y : A + B) : Decision (x = y).
Proof. solve_decision. Defined.

Instance curry_dec `(P_dec : ∀ (x : A) (y : B), Decision (P x y)) p :
    Decision (curry P p) :=
  match p as p return Decision (curry P p) with
  | (x,y) => P_dec x y
  end.
Instance uncurry_dec `(P_dec : ∀ (p : A * B), Decision (P p)) x y :
  Decision (uncurry P x y) := P_dec (x,y).

Instance sig_eq_dec `(P : A → Prop) `{∀ x, ProofIrrel (P x)}
  `{∀ x y : A, Decision (x = y)} (x y : sig P) : Decision (x = y).
Proof. refine (cast_if (decide (`x = `y))); by rewrite sig_eq_pi. Defined.

(** Some laws for decidable propositions *)
Lemma not_and_l {P Q : Prop} `{Decision P} : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q.
Proof. destruct (decide P); tauto. Qed.
Lemma not_and_r {P Q : Prop} `{Decision Q} : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q.
Proof. destruct (decide Q); tauto. Qed.
Lemma not_and_l_alt {P Q : Prop} `{Decision P} : ¬(P ∧ Q) ↔ ¬P ∨ (¬Q ∧ P).
Proof. destruct (decide P); tauto. Qed.
Lemma not_and_r_alt {P Q : Prop} `{Decision Q} : ¬(P ∧ Q) ↔ (¬P ∧ Q) ∨ ¬Q.
Proof. destruct (decide Q); tauto. Qed.
