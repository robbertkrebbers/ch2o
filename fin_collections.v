(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects definitions and theorems on finite collections. Most
importantly, it implements a fold and size function and some useful induction
principles on finite collections . *)
Require Import Permutation ars listset.
Require Export numbers collections.

Definition collection_choose `{Elements A C} (X : C) : option A :=
  head (elements X).
Instance collection_size `{Elements A C} : Size C := length ∘ elements.
Definition collection_fold `{Elements A C} {B}
  (f : A → B → B) (b : B) : C → B := foldr f b ∘ elements.

Section fin_collection.
Context `{FinCollection A C}.

Global Instance elements_proper: Proper ((≡) ==> (≡ₚ)) elements.
Proof.
  intros ?? E. apply NoDup_Permutation.
  * apply elements_nodup.
  * apply elements_nodup.
  * intros. by rewrite <-!elements_spec, E.
Qed.
Global Instance collection_size_proper: Proper ((≡) ==> (=)) size.
Proof. intros ?? E. apply Permutation_length. by rewrite E. Qed.

Lemma size_empty : size (∅ : C) = 0.
Proof.
  unfold size, collection_size. simpl.
  rewrite (elem_of_nil_inv (elements ∅)); [done |].
  intro. rewrite <-elements_spec. solve_elem_of.
Qed.
Lemma size_empty_inv (X : C) : size X = 0 → X ≡ ∅.
Proof.
  intros. apply equiv_empty. intro. rewrite elements_spec.
  rewrite (nil_length_inv (elements X)). by rewrite elem_of_nil. done.
Qed.
Lemma size_empty_iff (X : C) : size X = 0 ↔ X ≡ ∅.
Proof. split. apply size_empty_inv. intros E. by rewrite E, size_empty. Qed.
Lemma size_non_empty_iff (X : C) : size X ≠ 0 ↔ X ≢ ∅.
Proof. by rewrite size_empty_iff. Qed.

Lemma size_singleton (x : A) : size {[ x ]} = 1.
Proof.
  change (length (elements {[ x ]}) = length [x]).
  apply Permutation_length, NoDup_Permutation.
  * apply elements_nodup.
  * apply NoDup_singleton.
  * intros.
    by rewrite <-elements_spec, elem_of_singleton, elem_of_list_singleton.
Qed.
Lemma size_singleton_inv X x y : size X = 1 → x ∈ X → y ∈ X → x = y.
Proof.
  unfold size, collection_size. simpl. rewrite !elements_spec.
  generalize (elements X). intros [|? l]; intro; simplify_equality.
  rewrite (nil_length_inv l), !elem_of_list_singleton by done. congruence.
Qed.

Lemma collection_choose_Some X x : collection_choose X = Some x → x ∈ X.
Proof.
  unfold collection_choose. destruct (elements X) eqn:E; intros;
    simplify_equality. rewrite elements_spec, E. by left.
Qed.
Lemma collection_choose_None X : collection_choose X = None → X ≡ ∅.
Proof.
  unfold collection_choose.
  destruct (elements X) eqn:E; intros; simplify_equality.
  apply equiv_empty. intros x. by rewrite elements_spec, E, elem_of_nil.
Qed.
Lemma elem_of_or_empty X : (∃ x, x ∈ X) ∨ X ≡ ∅.
Proof.
  destruct (collection_choose X) eqn:?;
    eauto using collection_choose_Some, collection_choose_None.
Qed.
Lemma collection_choose_is_Some X : X ≢ ∅ ↔ is_Some (collection_choose X).
Proof.
  destruct (collection_choose X) eqn:?.
  * rewrite elem_of_equiv_empty. split; eauto using collection_choose_Some.
  * split. intros []; eauto using collection_choose_None. by intros [??].
Qed.
Lemma not_elem_of_equiv_empty X : X ≢ ∅ ↔ (∃ x, x ∈ X).
Proof.
  destruct (elem_of_or_empty X) as [?|E]; [esolve_elem_of |].
  setoid_rewrite E. setoid_rewrite elem_of_empty. naive_solver.
Qed.
Lemma size_pos_elem_of X : 0 < size X → ∃ x, x ∈ X.
Proof.
  intros E1. apply not_elem_of_equiv_empty. intros E2.
  rewrite E2, size_empty in E1. lia.
Qed.
Lemma size_1_elem_of X : size X = 1 → ∃ x, X ≡ {[ x ]}.
Proof.
  intros E. destruct (size_pos_elem_of X); auto with lia.
  exists x. apply elem_of_equiv. split.
  * rewrite elem_of_singleton. eauto using size_singleton_inv.
  * solve_elem_of.
Qed.

Lemma size_union X Y : X ∩ Y ≡ ∅ → size (X ∪ Y) = size X + size Y.
Proof.
  intros [E _]. unfold size, collection_size. simpl. rewrite <-app_length.
  apply Permutation_length, NoDup_Permutation.
  * apply elements_nodup.
  * apply NoDup_app; repeat split; try apply elements_nodup.
    intros x. rewrite <-!elements_spec. esolve_elem_of.
  * intros. rewrite elem_of_app, <-!elements_spec. solve_elem_of.
Qed.

Instance elem_of_dec_slow (x : A) (X : C) : Decision (x ∈ X) | 100.
Proof.
  refine (cast_if (decide_rel (∈) x (elements X)));
    by rewrite (elements_spec _).
Defined.
Global Program Instance collection_subseteq_dec_slow (X Y : C) :
    Decision (X ⊆ Y) | 100 :=
  match decide_rel (=) (size (X ∖ Y)) 0 with
  | left E1 => left _
  | right E1 => right _
  end.
Next Obligation.
  intros x Ex; apply dec_stable; intro. destruct (proj1 (elem_of_empty x)).
  apply (size_empty_inv _ E1). by rewrite elem_of_difference.
Qed.
Next Obligation.
  intros E2. destruct E1. apply size_empty_iff, equiv_empty. intros x.
  rewrite elem_of_difference. intros [E3 ?]. by apply E2 in E3.
Qed.

Lemma size_union_alt X Y : size (X ∪ Y) = size X + size (Y ∖ X).
Proof.
  rewrite <-size_union by solve_elem_of.
  setoid_replace (Y ∖ X) with ((Y ∪ X) ∖ X) by esolve_elem_of.
  rewrite <-union_difference, (commutative (∪)); solve_elem_of.
Qed.

Lemma subseteq_size X Y : X ⊆ Y → size X ≤ size Y.
Proof. intros. rewrite (union_difference X Y), size_union_alt by done. lia. Qed.
Lemma subset_size X Y : X ⊂ Y → size X < size Y.
Proof.
  intros. rewrite (union_difference X Y) by solve_elem_of.
  rewrite size_union_alt, difference_twice.
  cut (size (Y ∖ X) ≠ 0); [lia |].
  by apply size_non_empty_iff, non_empty_difference.
Qed.

Lemma collection_wf : wf (strict (@subseteq C _)).
Proof. apply (wf_projected (<) size); auto using subset_size, lt_wf. Qed.

Lemma collection_ind (P : C → Prop) :
  Proper ((≡) ==> iff) P →
  P ∅ → (∀ x X, x ∉ X → P X → P ({[ x ]} ∪ X)) → ∀ X, P X.
Proof.
  intros ? Hemp Hadd. apply well_founded_induction with (⊂).
  { apply collection_wf. }
  intros X IH. destruct (elem_of_or_empty X) as [[x ?]|HX].
  * rewrite (union_difference {[ x ]} X) by solve_elem_of.
    apply Hadd. solve_elem_of. apply IH. esolve_elem_of.
  * by rewrite HX.
Qed.

Lemma collection_fold_ind {B} (P : B → C → Prop) (f : A → B → B) (b : B) :
  Proper ((=) ==> (≡) ==> iff) P →
  P b ∅ → (∀ x X r, x ∉ X → P r X → P (f x r) ({[ x ]} ∪ X)) →
  ∀ X, P (collection_fold f b X) X.
Proof.
  intros ? Hemp Hadd.
  cut (∀ l, NoDup l → ∀ X, (∀ x, x ∈ X ↔ x ∈ l) → P (foldr f b l) X).
  { intros help ?. apply help. apply elements_nodup. apply elements_spec. }
  induction 1 as [|x l ?? IH]; simpl.
  * intros X HX. setoid_rewrite elem_of_nil in HX.
    rewrite equiv_empty. done. esolve_elem_of.
  * intros X HX. setoid_rewrite elem_of_cons in HX.
    rewrite (union_difference {[ x ]} X) by esolve_elem_of.
    apply Hadd. solve_elem_of. apply IH. esolve_elem_of.
Qed.

Lemma collection_fold_proper {B} (R : relation B) `{!Equivalence R}
    (f : A → B → B) (b : B) `{!Proper ((=) ==> R ==> R) f}
    (Hf : ∀ a1 a2 b, R (f a1 (f a2 b)) (f a2 (f a1 b))) :
  Proper ((≡) ==> R) (collection_fold f b).
Proof. intros ?? E. apply (foldr_permutation R f b); auto. by rewrite E. Qed.

Global Instance set_Forall_dec `(P : A → Prop)
  `{∀ x, Decision (P x)} X : Decision (set_Forall P X) | 100.
Proof.
  refine (cast_if (decide (Forall P (elements X))));
    abstract (unfold set_Forall; setoid_rewrite elements_spec;
      by rewrite <-Forall_forall).
Defined.
Global Instance set_Exists_dec `(P : A → Prop) `{∀ x, Decision (P x)} X :
  Decision (set_Exists P X) | 100.
Proof.
  refine (cast_if (decide (Exists P (elements X))));
    abstract (unfold set_Exists; setoid_rewrite elements_spec;
      by rewrite <-Exists_exists).
Defined.
Global Instance rel_elem_of_dec `{∀ x y, Decision (R x y)} x X :
  Decision (elem_of_upto R x X) | 100 := decide (set_Exists (R x) X).
End fin_collection.
