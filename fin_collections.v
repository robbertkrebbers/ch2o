(* Copyright (c) 2012, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects definitions and theorems on finite collections. Most
importantly, it implements a fold and size function and some useful induction
principles on finite collections . *)
Require Import Permutation.
Require Export collections listset.

Instance collection_size `{Elements A C} : Size C := λ X, length (elements X).
Definition collection_fold `{Elements A C} {B} (f : A → B → B)
  (b : B) (X : C) : B := fold_right f b (elements X).

Section fin_collection.
Context `{FinCollection A C}.

Global Instance elements_proper: Proper ((≡) ==> Permutation) elements.
Proof.
  intros ?? E. apply NoDup_Permutation.
  * apply elements_nodup.
  * apply elements_nodup.
  * intros. now rewrite <-!elements_spec, E.
Qed.
Global Instance collection_size_proper: Proper ((≡) ==> (=)) size.
Proof. intros ?? E. apply Permutation_length. now rewrite E. Qed.

Lemma size_empty : size ∅ = 0.
Proof.
  unfold size, collection_size. rewrite (in_nil_inv (elements ∅)).
  * easy.
  * intro. rewrite <-elements_spec. solve_elem_of.
Qed.
Lemma size_empty_inv X : size X = 0 → X ≡ ∅.
Proof.
  intros. apply equiv_empty. intro. rewrite elements_spec.
  rewrite (nil_length (elements X)); intuition.
Qed.
Lemma size_empty_iff X : size X = 0 ↔ X ≡ ∅.
Proof. split. apply size_empty_inv. intros E. now rewrite E, size_empty. Qed.

Lemma size_singleton x : size {[ x ]} = 1.
Proof.
  change (length (elements {[ x ]}) = length [x]).
  apply Permutation_length, NoDup_Permutation.
  * apply elements_nodup.
  * apply NoDup_singleton.
  * intros. rewrite <-elements_spec. esolve_elem_of firstorder.
Qed.
Lemma size_singleton_inv X x y : size X = 1 → x ∈ X → y ∈ X → x = y.
Proof.
  unfold size, collection_size. rewrite !elements_spec.
  generalize (elements X). intros [|? l].
  * discriminate.
  * injection 1. intro. rewrite (nil_length l) by easy.
    simpl. intuition congruence.
Qed.

Lemma choose X : X ≢ ∅ → { x | x ∈ X }.
Proof.
  destruct (elements X) as [|x l] eqn:E.
  * intros []. apply equiv_empty.
    intros x. rewrite elements_spec, E. contradiction.
  * exists x. rewrite elements_spec, E. now left.
Qed.
Lemma size_pos_choose X : 0 < size X → { x | x ∈ X }.
Proof.
  intros E. apply choose.
  intros E2. rewrite E2, size_empty in E.
  now destruct (Lt.lt_n_0 0).
Qed.
Lemma size_1_choose X : size X = 1 → { x | X ≡ {[ x ]} }.
Proof.
  intros E. destruct (size_pos_choose X).
  * rewrite E. auto with arith.
  * exists x. apply elem_of_equiv. split.
    + intro. rewrite elem_of_singleton. eauto using size_singleton_inv.
    + solve_elem_of.
Qed.

Program Instance collection_car_eq_dec_slow (x y : A) :
    Decision (x = y) | 100 :=
  match Compare_dec.zerop (size ({[ x ]} ∩ {[ y ]})) with
  | left _ => right _
  | right _ => left _
  end.
Next Obligation.
  intro. apply empty_ne_singleton with x.
  transitivity ({[ x ]} ∩ {[ y ]}).
  * symmetry. now apply size_empty_iff.
  * solve_elem_of.
Qed.
Next Obligation. edestruct size_pos_choose; esolve_elem_of. Qed.

Instance elem_of_dec_slow (x : A) (X : C) : Decision (x ∈ X) | 100 :=
  match decide_rel In x (elements X) with
  | left Hx => left (proj2 (elements_spec _ _) Hx)
  | right Hx => right (Hx ∘ proj1 (elements_spec _ _))
  end.

Lemma union_difference X Y : X ∪ Y ∖ X ≡ X ∪ Y.
Proof. split; intros x; destruct (decide (x ∈ X)); solve_elem_of. Qed.

Lemma size_union X Y : X ∩ Y ≡ ∅ → size (X ∪ Y) = size X + size Y.
Proof.
  intros [E _]. unfold size, collection_size. rewrite <-app_length.
  apply Permutation_length, NoDup_Permutation.
  * apply elements_nodup.
  * apply NoDup_app; try apply elements_nodup.
    intros x. rewrite <-!elements_spec. esolve_elem_of.
  * intros. rewrite in_app_iff, <-!elements_spec. solve_elem_of.
Qed.
Lemma size_union_alt X Y : size (X ∪ Y) = size X + size (Y ∖ X).
Proof.
  rewrite <-size_union. now rewrite union_difference. solve_elem_of.
Qed.
Lemma size_add X x : x ∉ X → size ({[ x ]} ∪ X) = S (size X).
Proof.
  intros. rewrite size_union. now rewrite size_singleton. solve_elem_of.
Qed.
Lemma size_difference X Y : X ⊆ Y → size X + size (Y ∖ X) = size Y.
Proof. intros. now rewrite <-size_union_alt, subseteq_union_1. Qed.
Lemma size_remove X x : x ∈ X → S (size (X ∖ {[ x ]})) = size X.
Proof.
  intros. rewrite <-(size_difference {[ x ]} X).
  * rewrite size_singleton. auto with arith.
  * solve_elem_of.
Qed.

Lemma subseteq_size X Y : X ⊆ Y → size X ≤ size Y.
Proof.
  intros. rewrite <-(subseteq_union_1 X Y) by easy.
  rewrite <-(union_difference X Y), size_union by solve_elem_of.
  auto with arith.
Qed.

Lemma collection_wf_ind (P : C → Prop) :
  (∀ X, (∀ Y, size Y < size X → P Y) → P X) →
  ∀ X, P X.
Proof.
  intros Hind. cut (∀ n X, size X < n → P X).
  { intros help X. apply help with (S (size X)). auto with arith. }
  induction n; intros.
  * now destruct (Lt.lt_n_0 (size X)).
  * apply Hind. intros. apply IHn. eauto with arith.
Qed.

Lemma collection_ind (P : C → Prop) :
  Proper ((≡) ==> iff) P →
  P ∅ →
  (∀ x X, x ∉ X → P X → P ({[ x ]} ∪ X)) →
  ∀ X, P X.
Proof.
  intros ? Hemp Hadd. apply collection_wf_ind.
  intros X IH. destruct (Compare_dec.zerop (size X)).
  * now rewrite size_empty_inv.
  * destruct (size_pos_choose X); auto.
    rewrite <-(subseteq_union_1 {[ x ]} X) by solve_elem_of.
    rewrite <-union_difference.
    apply Hadd; [solve_elem_of |]. apply IH.
    rewrite <-(size_remove X x); auto with arith.
Qed.

Lemma collection_fold_ind {B} (P : B → C → Prop) (f : A → B → B) (b : B) :
  Proper ((=) ==> (≡) ==> iff) P →
  P b ∅ →
  (∀ x X r, x ∉ X → P r X → P (f x r) ({[ x ]} ∪ X)) →
  ∀ X, P (collection_fold f b X) X.
Proof.
  intros ? Hemp Hadd.
  cut (∀ l, NoDup l → ∀ X, (∀ x, x ∈ X ↔ In x l) → P (fold_right f b l) X).
  { intros help ?. apply help. apply elements_nodup. apply elements_spec. }
  induction 1 as [|x l ?? IHl]; simpl.
  * intros X HX. rewrite equiv_empty. easy. intros ??. firstorder.
  * intros X HX.
    rewrite <-(subseteq_union_1 {[ x ]} X) by esolve_elem_of.
    rewrite <-union_difference.
    apply Hadd. solve_elem_of. apply IHl.
    intros y. split.
    + intros. destruct (proj1 (HX y)); solve_elem_of.
    + esolve_elem_of.
Qed.

Lemma collection_fold_proper {B} (f : A → B → B) (b : B) :
  (∀ a1 a2 b, f a1 (f a2 b) = f a2 (f a1 b)) →
  Proper ((≡) ==> (=)) (collection_fold f b).
Proof. intros ??? E. apply fold_right_permutation. auto. now rewrite E. Qed.

Global Program Instance cforall_dec `(P : A → Prop)
    `{∀ x, Decision (P x)} X : Decision (cforall P X) | 100 :=
  match decide (Forall P (elements X)) with
  | left Hall => left _
  | right Hall => right _
  end.
Next Obligation.
  red. setoid_rewrite elements_spec. now apply Forall_forall.
Qed.
Next Obligation.
  intro. apply Hall, Forall_forall. setoid_rewrite <-elements_spec. auto.
Qed.

Global Program Instance cexists_dec `(P : A → Prop)
    `{∀ x, Decision (P x)} X : Decision (cexists P X) | 100 :=
  match decide (Exists P (elements X)) with
  | left Hex => left _
  | right Hex => right _
  end.
Next Obligation.
  red. setoid_rewrite elements_spec. now apply Exists_exists.
Qed.
Next Obligation.
  intro. apply Hex, Exists_exists. setoid_rewrite <-elements_spec. auto.
Qed.

Global Instance rel_elem_of_dec `{∀ x y, Decision (R x y)} x X :
  Decision (elem_of_upto R x X) | 100 := decide (cexists (R x) X).

Lemma not_elem_of_intersection x X Y : x ∉ X ∩ Y ↔ x ∉ X ∨ x ∉ Y.
Proof. destruct (decide (x ∈ X)); solve_elem_of. Qed.
Lemma not_elem_of_difference x X Y : x ∉ X ∖ Y ↔ x ∉ X ∨ x ∈ Y.
Proof. destruct (decide (x ∈ Y)); solve_elem_of. Qed.
End fin_collection.
