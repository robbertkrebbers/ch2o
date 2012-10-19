(* Copyright (c) 2012, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects definitions and theorems on finite collections. Most
importantly, it implements a fold and size function and some useful induction
principles on finite collections . *)
Require Import Permutation.
Require Export collections listset numbers.

Instance collection_size `{Elements A C} : Size C := λ X, length (elements X).
Definition collection_fold `{Elements A C} {B} (f : A → B → B)
  (b : B) (X : C) : B := foldr f b (elements X).

Section fin_collection.
Context `{FinCollection A C}.

Global Instance elements_proper: Proper ((≡) ==> Permutation) elements.
Proof.
  intros ?? E. apply NoDup_Permutation.
  * apply elements_nodup.
  * apply elements_nodup.
  * intros. by rewrite <-!elements_spec, E.
Qed.
Global Instance collection_size_proper: Proper ((≡) ==> (=)) size.
Proof. intros ?? E. apply Permutation_length. by rewrite E. Qed.

Lemma size_empty : size ∅ = 0.
Proof.
  unfold size, collection_size. rewrite (in_nil_inv (elements ∅)).
  * done.
  * intro. rewrite <-elements_spec. solve_elem_of.
Qed.
Lemma size_empty_inv X : size X = 0 → X ≡ ∅.
Proof.
  intros. apply equiv_empty. intro. rewrite elements_spec.
  rewrite (nil_length (elements X)); intuition.
Qed.
Lemma size_empty_iff X : size X = 0 ↔ X ≡ ∅.
Proof. split. apply size_empty_inv. intros E. by rewrite E, size_empty. Qed.

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
  * done.
  * injection 1. intro. rewrite (nil_length l) by done.
    simpl. intuition congruence.
Qed.

Lemma elem_of_or_empty X : (∃ x, x ∈ X) ∨ X ≡ ∅.
Proof.
  destruct (elements X) as [|x xs] eqn:E.
  * right. apply equiv_empty. intros x Ex.
    by rewrite elements_spec, E in Ex.
  * left. exists x. rewrite elements_spec, E.
    by constructor.
Qed.

Lemma choose X : X ≢ ∅ → ∃ x, x ∈ X.
Proof.
  destruct (elem_of_or_empty X) as [[x ?]|?].
  * by exists x.
  * done.
Qed.
Lemma size_pos_choose X : 0 < size X → ∃ x, x ∈ X.
Proof.
  intros E1. apply choose.
  intros E2. rewrite E2, size_empty in E1.
  by apply (Lt.lt_n_0 0).
Qed.
Lemma size_1_choose X : size X = 1 → ∃ x, X ≡ {[ x ]}.
Proof.
  intros E. destruct (size_pos_choose X).
  * rewrite E. auto with arith.
  * exists x. apply elem_of_equiv. split.
    + intro. rewrite elem_of_singleton.
      eauto using size_singleton_inv.
    + solve_elem_of.
Qed.

Lemma size_union X Y : X ∩ Y ≡ ∅ → size (X ∪ Y) = size X + size Y.
Proof.
  intros [E _]. unfold size, collection_size. rewrite <-app_length.
  apply Permutation_length, NoDup_Permutation.
  * apply elements_nodup.
  * apply NoDup_app; try apply elements_nodup.
    intros x. rewrite <-!elements_spec. esolve_elem_of.
  * intros. rewrite in_app_iff, <-!elements_spec. solve_elem_of.
Qed.

Instance elem_of_dec_slow (x : A) (X : C) : Decision (x ∈ X) | 100.
Proof.
  refine (cast_if (decide_rel In x (elements X)));
    by rewrite (elements_spec _).
Defined.
Global Program Instance collection_subseteq_dec_slow (X Y : C) :
    Decision (X ⊆ Y) | 100 :=
  match decide_rel (=) (size (X ∖ Y)) 0 with
  | left E1 => left _
  | right E1 => right _
  end.
Next Obligation.
  intros x Ex; apply dec_stable; intro.
  destruct (proj1 (elem_of_empty x)).
  apply (size_empty_inv _ E1).
  by rewrite elem_of_difference.
Qed.
Next Obligation.
  intros E2. destruct E1.
  apply size_empty_iff, equiv_empty. intros x.
  rewrite elem_of_difference. intros [E3 ?].
  by apply E2 in E3.
Qed.

Lemma size_union_alt X Y : size (X ∪ Y) = size X + size (Y ∖ X).
Proof.
  rewrite <-size_union. by rewrite union_difference. solve_elem_of.
Qed.
Lemma size_add X x : x ∉ X → size ({[ x ]} ∪ X) = S (size X).
Proof.
  intros. rewrite size_union. by rewrite size_singleton. solve_elem_of.
Qed.

Lemma size_difference X Y : X ⊆ Y → size X + size (Y ∖ X) = size Y.
Proof. intros. by rewrite <-size_union_alt, subseteq_union_1. Qed.
Lemma size_remove X x : x ∈ X → S (size (X ∖ {[ x ]})) = size X.
Proof.
  intros. rewrite <-(size_difference {[ x ]} X).
  * rewrite size_singleton. auto with arith.
  * solve_elem_of.
Qed.

Lemma subseteq_size X Y : X ⊆ Y → size X ≤ size Y.
Proof.
  intros. rewrite <-(subseteq_union_1 X Y) by done.
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
  * by destruct (Lt.lt_n_0 (size X)).
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
  * by rewrite size_empty_inv.
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
  cut (∀ l, NoDup l → ∀ X, (∀ x, x ∈ X ↔ In x l) → P (foldr f b l) X).
  { intros help ?. apply help. apply elements_nodup. apply elements_spec. }
  induction 1 as [|x l ?? IHl]; simpl.
  * intros X HX. rewrite equiv_empty; firstorder.
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
Proof. intros ??? E. apply foldr_permutation. auto. by rewrite E. Qed.

Global Instance cforall_dec `(P : A → Prop)
    `{∀ x, Decision (P x)} X : Decision (cforall P X) | 100.
Proof.
  refine (cast_if (decide (Forall P (elements X))));
  abstract (unfold cforall; setoid_rewrite elements_spec;
    by rewrite <-Forall_forall).
Defined.

Global Instance cexists_dec `(P : A → Prop) `{∀ x, Decision (P x)} X :
  Decision (cexists P X) | 100.
Proof.
  refine (cast_if (decide (Exists P (elements X))));
  abstract (unfold cexists; setoid_rewrite elements_spec;
    by rewrite <-Exists_exists).
Defined.

Global Instance rel_elem_of_dec `{∀ x y, Decision (R x y)} x X :
  Decision (elem_of_upto R x X) | 100 := decide (cexists (R x) X).
End fin_collection.
