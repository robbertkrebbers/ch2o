(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects facts on proof irrelevant types/propositions. *)
Require Export Eqdep_dec tactics.

Hint Extern 200 (ProofIrrel _) => progress (lazy beta) : typeclass_instances.

Instance: ProofIrrel True.
Proof. by intros [] []. Qed.
Instance: ProofIrrel False.
Proof. by intros []. Qed.

Instance and_pi (A B : Prop) :
  ProofIrrel A → ProofIrrel B → ProofIrrel (A ∧ B).
Proof. intros ?? [??] [??]. by f_equal. Qed.
Instance prod_pi (A B : Type) :
  ProofIrrel A → ProofIrrel B → ProofIrrel (A * B).
Proof. intros ?? [??] [??]. by f_equal. Qed.

Instance eq_pi {A} `{∀ x y : A, Decision (x = y)} (x y : A) :
  ProofIrrel (x = y).
Proof.
  intros ??. apply eq_proofs_unicity.
  intros x' y'. destruct (decide (x' = y')); tauto.
Qed.

Instance Is_true_pi (b : bool) : ProofIrrel (Is_true b).
Proof. destruct b; simpl; apply _. Qed.

Lemma sig_eq_pi `(P : A → Prop) `{∀ x, ProofIrrel (P x)}
  (x y : sig P) : x = y ↔ `x = `y.
Proof.
  split; [by intros <- |].
  destruct x as [x Hx], y as [y Hy]; simpl; intros; subst.
  f_equal. apply proof_irrel.
Qed.

Lemma exists_proj1_pi `(P : A → Prop) `{∀ x, ProofIrrel (P x)}
  (x : sig P) p : `x ↾ p = x.
Proof. by apply (sig_eq_pi _). Qed.
