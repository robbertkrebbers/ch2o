Require Import Permutation.
Require Export collections listset.

Instance collection_size `{Elements A C} : Size C := λ X, length (elements X).
Definition collection_fold `{Elements A C} {B} (f : A → B → B) (b : B) (X : C) : B := 
  fold_right f b (elements X).

Section fin_collection.
Context `{FinCollection A C}.

Global Instance elements_proper: Proper ((≡) ==> Permutation) elements.
Proof.
  intros ?? E. apply NoDup_Permutation.
    apply elements_nodup.
   apply elements_nodup.
  intros. now rewrite <-!elements_spec, E.
Qed.
Global Instance collection_size_proper: Proper ((≡) ==> (=)) size.
Proof. intros ?? E. apply Permutation_length. now rewrite E. Qed.

Lemma size_empty : size ∅ = 0.
Proof.
  unfold size, collection_size. rewrite (in_nil_inv (elements ∅)).
   easy.
  intro. rewrite <-elements_spec. simplify_elem_of.
Qed.
Lemma size_empty_inv X : size X = 0 → X ≡ ∅.
Proof.
  intros. apply equiv_empty. intro. rewrite elements_spec.
  rewrite (nil_length (elements X)); intuition.
Qed.
Lemma size_empty_iff X : size X = 0 ↔ X ≡ ∅.
Proof. split. apply size_empty_inv. intros E. now rewrite E, size_empty. Qed.

Lemma size_singleton x : size {{ x }} = 1.
Proof.
  change (length (elements {{x}}) = length [x]).
  apply Permutation_length, NoDup_Permutation.
    apply elements_nodup.
   apply NoDup_singleton.
  intros. rewrite <-elements_spec. esimplify_elem_of firstorder.
Qed.
Lemma size_singleton_inv X x y : size X = 1 → x ∈ X → y ∈ X → x = y.
Proof.
  unfold size, collection_size. rewrite !elements_spec.
  generalize (elements X). intros [|? l].
   discriminate.
  injection 1. intro. rewrite (nil_length l) by easy.
  simpl. intuition congruence.
Qed.

Lemma choose X : X ≢ ∅ → { x | x ∈ X }.
Proof.
  case_eq (elements X).
   intros E. intros []. apply equiv_empty.
   intros x. rewrite elements_spec, E. contradiction.
  intros x l E. exists x. rewrite elements_spec, E. now left.
Qed.
Lemma size_pos_choose X : 0 < size X → { x | x ∈ X }.
Proof. 
  intros E. apply choose.
  intros E2. rewrite E2, size_empty in E. now destruct (Lt.lt_n_0 0).
Qed.
Lemma size_1_choose X : size X = 1 → { x | X ≡ {{ x }} }.
Proof.
  intros E. destruct (size_pos_choose X).
   rewrite E. auto with arith.
  exists x. simplify_elem_of. eapply size_singleton_inv; eauto.
Qed.

Program Instance collection_car_eq_dec_slow (x y : A) : Decision (x = y) | 100 :=
  match Compare_dec.zerop (size ({{ x }} ∩ {{ y }})) with
  | left _ => right _
  | right _ => left _
  end.
Next Obligation.
  intro. apply empty_ne_singleton with x.
  transitivity ({{ x }} ∩ {{ y }}).
   symmetry. now apply size_empty_iff.
  simplify_elem_of.
Qed.
Next Obligation. edestruct size_pos_choose; esimplify_elem_of. Qed.

Instance elem_of_dec_slow (x : A) (X : C) : Decision (x ∈ X) | 100 :=
  match decide_rel In x (elements X) with
  | left Hx => left (proj2 (elements_spec _ _) Hx)
  | right Hx => right (Hx ∘ proj1 (elements_spec _ _))
  end.

Lemma union_diff_1 X Y : X ⊆ Y → X ∪ Y ∖ X ≡ Y.
Proof. split; intros x; destruct (decide (x ∈ X)); simplify_elem_of. Qed.
Lemma union_diff_2 X Y : X ∪ Y ≡ X ∪ Y ∖ X.
Proof. split; intros x; destruct (decide (x ∈ X)); simplify_elem_of. Qed.

Lemma size_union X Y : X ∩ Y ≡ ∅ → size (X ∪ Y) = size X + size Y.
Proof.
  intros [E _]. unfold size, collection_size. rewrite <-app_length.
  apply Permutation_length, NoDup_Permutation.
    apply elements_nodup.
   apply NoDup_app; try apply elements_nodup.
   intros x. rewrite <-!elements_spec.
   intros ??. apply (elem_of_empty x), E. simplify_elem_of.
  intros. rewrite in_app_iff, <-!elements_spec. simplify_elem_of.
Qed.
Lemma size_union_alt X Y : size (X ∪ Y) = size X + size (Y ∖ X).
Proof. rewrite <-size_union. now rewrite union_diff_2. simplify_elem_of. Qed.
Lemma size_add X x : x ∉ X → size ({{ x }} ∪ X) = S (size X).
Proof. intros. rewrite size_union. now rewrite size_singleton. simplify_elem_of. Qed.
Lemma size_diff X Y : X ⊆ Y → size X + size (Y ∖ X) = size Y.
Proof. intros. now rewrite <-size_union_alt, subseteq_union_1. Qed.
Lemma size_remove X x : x ∈ X → S (size (X ∖ {{ x }})) = size X.
Proof.
  intros. rewrite <-(size_diff {{ x }} X).
   rewrite size_singleton. auto with arith.
  simplify_elem_of.
Qed.

Lemma subseteq_size X Y : X ⊆ Y → size X ≤ size Y.
Proof. intros. rewrite <-(union_diff_1 X Y), size_union by simplify_elem_of. auto with arith. Qed. 

Lemma collection_wf_ind (P : C → Prop) :
  (∀ X, (∀ Y, size Y < size X → P Y) → P X) → ∀ X, P X.
Proof.
  intros Hind. assert (∀ n X, size X < n → P X) as help.
   induction n.
    intros. now destruct (Lt.lt_n_0 (size X)).
   intros. apply Hind. intros. apply IHn. eauto with arith.
  intros. apply help with (S (size X)). auto with arith.
Qed.

Lemma collection_ind (P : C → Prop) :
  Proper ((≡) ==> iff) P → P ∅ → (∀ x X, x ∉ X → P X → P ({{ x }} ∪ X)) → ∀ X, P X.
Proof.
  intros ? Hemp Hadd. apply collection_wf_ind.
  intros X IH. destruct (Compare_dec.zerop (size X)).
   now rewrite size_empty_inv.
  destruct (size_pos_choose X); auto.
  rewrite <-(union_diff_1 {{ x }} X); simplify_elem_of.
  apply Hadd; simplify_elem_of. apply IH.
  rewrite <-(size_remove X x); auto with arith.
Qed.

Lemma collection_fold_ind {B} (P : B → C → Prop) (f : A → B → B) (b : B) :
  Proper ((=) ==> (≡) ==> iff) P →
  P b ∅ → (∀ x X r, x ∉ X → P r X → P (f x r) ({{ x }} ∪ X)) → ∀ X, P (collection_fold f b X) X.
Proof.
  intros ? Hemp Hadd.
  assert (∀ l, NoDup l → ∀ X, (∀ x, x ∈ X ↔ In x l) → P (fold_right f b l) X) as help.
   induction 1 as [|x l ?? IHl]; simpl.
    intros X HX. rewrite equiv_empty; esimplify_elem_of.
   intros X HX. rewrite <-(union_diff_1 {{ x }} X).
    apply Hadd. simplify_elem_of. apply IHl.
    intros y. split.
     intros. destruct (proj1 (HX y)); simplify_elem_of.
    esimplify_elem_of.
   esimplify_elem_of.
  intros. apply help. apply elements_nodup. apply elements_spec.
Qed.

Lemma collection_fold_proper {B} (f : A → B → B) (b : B) :
  (∀ a1 a2 b, f a1 (f a2 b) = f a2 (f a1 b)) → Proper ((≡) ==> (=)) (collection_fold f b).
Proof. intros ??? E. apply fold_right_permutation. auto. now rewrite E. Qed. 

Global Program Instance cforall_dec `(P : A → Prop) `{∀ x, Decision (P x)} X : Decision (cforall P X) | 100 :=
  match decide (Forall P (elements X)) with
  | left Hall => left _
  | right Hall => right _
  end.
Next Obligation. red. setoid_rewrite elements_spec. now apply Forall_forall. Qed. 
Next Obligation. intro. apply Hall, Forall_forall. setoid_rewrite <-elements_spec. auto. Qed.

Global Program Instance cexists_dec `(P : A → Prop) `{∀ x, Decision (P x)} X : Decision (cexists P X) | 100 :=
  match decide (Exists P (elements X)) with
  | left Hex => left _
  | right Hex => right _
  end.
Next Obligation. red. setoid_rewrite elements_spec. now apply Exists_exists. Qed. 
Next Obligation. intro. apply Hex, Exists_exists. setoid_rewrite <-elements_spec. auto. Qed.

Global Instance rel_elem_of_dec `{∀ x y, Decision (R x y)} x X : Decision (elem_of_upto R x X) | 100 := 
  decide (cexists (R x) X).
End fin_collection.
