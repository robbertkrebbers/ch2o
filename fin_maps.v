(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** Finite maps associate data to keys. This file defines an interface for
finite maps and collects some theory on it. Most importantly, it proves useful
induction principles for finite maps and implements the tactic
[simplify_map_equality] to simplify goals involving finite maps. *)
Require Import Permutation.
Require Export ars vector orders.

(** * Axiomatization of finite maps *)
(** We require Leibniz equality to be extensional on finite maps. This of
course limits the space of finite map implementations, but since we are mainly
interested in finite maps with numbers as indexes, we do not consider this to
be a serious limitation. The main application of finite maps is to implement
the memory, where extensionality of Leibniz equality is very important for a
convenient use in the assertions of our axiomatic semantics. *)

(** Finiteness is axiomatized by requiring that each map can be translated
to an association list. The translation to association lists is used to
prove well founded recursion on finite maps. *)

(** Finite map implementations are required to implement the [merge] function
which enables us to give a generic implementation of [union_with],
[intersection_with], and [difference_with]. *)

Class FinMapToList K A M := map_to_list: M → list (K * A).

Class FinMap K M `{!FMap M}
    `{∀ A, Lookup K A (M A)} `{∀ A, Empty (M A)} `{∀ A, PartialAlter K A (M A)}
    `{!Merge M} `{∀ A, FinMapToList K A (M A)}
    `{∀ i j : K, Decision (i = j)} := {
  map_eq {A} (m1 m2 : M A) : (∀ i, m1 !! i = m2 !! i) → m1 = m2;
  lookup_empty {A} i : (∅ : M A) !! i = None;
  lookup_partial_alter {A} f (m : M A) i :
    partial_alter f i m !! i = f (m !! i);
  lookup_partial_alter_ne {A} f (m : M A) i j :
    i ≠ j → partial_alter f i m !! j = m !! j;
  lookup_fmap {A B} (f : A → B) (m : M A) i : (f <$> m) !! i = f <$> m !! i;
  map_to_list_nodup {A} (m : M A) : NoDup (map_to_list m);
  elem_of_map_to_list {A} (m : M A) i x :
    (i,x) ∈ map_to_list m ↔ m !! i = Some x;
  lookup_merge {A B C} (f : option A → option B → option C)
      `{!PropHolds (f None None = None)} m1 m2 i :
    merge f m1 m2 !! i = f (m1 !! i) (m2 !! i)
}.

(** * Derived operations *)
(** All of the following functions are defined in a generic way for arbitrary
finite map implementations. These generic implementations do not cause a
significant performance loss to make including them in the finite map interface
worthwhile. *)
Instance map_insert `{PartialAlter K A M} : Insert K A M :=
  λ i x, partial_alter (λ _, Some x) i.
Instance map_alter `{PartialAlter K A M} : Alter K A M :=
  λ f, partial_alter (fmap f).
Instance map_delete `{PartialAlter K A M} : Delete K M :=
  partial_alter (λ _, None).
Instance map_singleton `{PartialAlter K A M}
  `{Empty M} : Singleton (K * A) M := λ p, <[fst p:=snd p]>∅.

Definition map_of_list `{Insert K A M} `{Empty M}
  (l : list (K * A)) : M := insert_list l ∅.

Instance map_union_with `{Merge M} {A} : UnionWith A (M A) :=
  λ f, merge (union_with f).
Instance map_intersection_with `{Merge M} {A} : IntersectionWith A (M A) :=
  λ f, merge (intersection_with f).
Instance map_difference_with `{Merge M} {A} : DifferenceWith A (M A) :=
  λ f, merge (difference_with f).

(** The relation [intersection_forall R] on finite maps describes that the
relation [R] holds for each pair in the intersection. *)
Definition map_forall `{Lookup K A M} (P : K → A → Prop) : M → Prop :=
  λ m, ∀ i x, m !! i = Some x → P i x.
Definition map_intersection_forall `{Lookup K A M}
    (R : relation A) : relation M := λ m1 m2,
  ∀ i x1 x2, m1 !! i = Some x1 → m2 !! i = Some x2 → R x1 x2.
Instance map_disjoint `{∀ A, Lookup K A (M A)} : Disjoint (M A) :=
  λ A, map_intersection_forall (λ _ _, False).

(** The union of two finite maps only has a meaningful definition for maps
that are disjoint. However, as working with partial functions is inconvenient
in Coq, we define the union as a total function. In case both finite maps
have a value at the same index, we take the value of the first map. *)
Instance map_union `{Merge M} {A} : Union (M A) := union_with (λ x _, Some x).
Instance map_intersection `{Merge M} {A} : Intersection (M A) :=
  intersection_with (λ x _, Some x).

(** The difference operation removes all values from the first map whose
index contains a value in the second map as well. *)
Instance map_difference `{Merge M} {A} : Difference (M A) :=
  difference_with (λ _ _, None).

(** * Theorems *)
Section theorems.
Context `{FinMap K M}.

Global Instance map_subseteq {A} : SubsetEq (M A) := λ m1 m2,
  ∀ i x, m1 !! i = Some x → m2 !! i = Some x.
Global Instance: BoundedPreOrder (M A).
Proof. split; [firstorder |]. intros m i x. by rewrite lookup_empty. Qed.
Global Instance : PartialOrder (@subseteq (M A) _).
Proof.
  split; [apply _ |].
  intros ????. apply map_eq. intros i. apply option_eq. naive_solver.
Qed.

Lemma lookup_weaken {A} (m1 m2 : M A) i x :
  m1 !! i = Some x → m1 ⊆ m2 → m2 !! i = Some x.
Proof. auto. Qed.
Lemma lookup_weaken_is_Some {A} (m1 m2 : M A) i :
  is_Some (m1 !! i) → m1 ⊆ m2 → is_Some (m2 !! i).
Proof. inversion 1. eauto using lookup_weaken. Qed.
Lemma lookup_weaken_None {A} (m1 m2 : M A) i :
  m2 !! i = None → m1 ⊆ m2 → m1 !! i = None.
Proof.
  rewrite eq_None_not_Some. intros Hm2 Hm1m2.
  specialize (Hm1m2 i). destruct (m1 !! i); naive_solver.
Qed.

Lemma lookup_weaken_inv {A} (m1 m2 : M A) i x y :
  m1 !! i = Some x → m1 ⊆ m2 → m2 !! i = Some y → x = y.
Proof. intros Hm1 ? Hm2. eapply lookup_weaken in Hm1; eauto. congruence. Qed.

Lemma lookup_ne {A} (m : M A) i j : m !! i ≠ m !! j → i ≠ j.
Proof. congruence. Qed.
Lemma map_empty {A} (m : M A) : (∀ i, m !! i = None) → m = ∅.
Proof. intros Hm. apply map_eq. intros. by rewrite Hm, lookup_empty. Qed.
Lemma lookup_empty_is_Some {A} i : ¬is_Some ((∅ : M A) !! i).
Proof. rewrite lookup_empty. by inversion 1. Qed.
Lemma lookup_empty_Some {A} i (x : A) : ¬∅ !! i = Some x.
Proof. by rewrite lookup_empty. Qed.

Lemma map_subset_empty {A} (m : M A) : m ⊄ ∅.
Proof. intros [? []]. intros i x. by rewrite lookup_empty. Qed.

(** ** Properties of the [partial_alter] operation *)
Lemma partial_alter_compose {A} (m : M A) i f g :
  partial_alter (f ∘ g) i m = partial_alter f i (partial_alter g i m).
Proof.
  intros. apply map_eq. intros ii. case (decide (i = ii)).
  * intros. subst. by rewrite !lookup_partial_alter.
  * intros. by rewrite !lookup_partial_alter_ne.
Qed.
Lemma partial_alter_commute {A} (m : M A) i j f g :
  i ≠ j → partial_alter f i (partial_alter g j m) =
    partial_alter g j (partial_alter f i m).
Proof.
  intros. apply map_eq. intros jj. destruct (decide (jj = j)).
  * subst. by rewrite lookup_partial_alter_ne,
      !lookup_partial_alter, lookup_partial_alter_ne.
  * destruct (decide (jj = i)).
    + subst. by rewrite lookup_partial_alter,
       !lookup_partial_alter_ne, lookup_partial_alter by congruence.
    + by rewrite !lookup_partial_alter_ne by congruence.
Qed.
Lemma partial_alter_self_alt {A} (m : M A) i x :
  x = m !! i → partial_alter (λ _, x) i m = m.
Proof.
  intros. apply map_eq. intros ii. destruct (decide (i = ii)).
  * subst. by rewrite lookup_partial_alter.
  * by rewrite lookup_partial_alter_ne.
Qed.
Lemma partial_alter_self {A} (m : M A) i : partial_alter (λ _, m !! i) i m = m.
Proof. by apply partial_alter_self_alt. Qed.

Lemma partial_alter_subseteq {A} (m : M A) i f :
  m !! i = None → m ⊆ partial_alter f i m.
Proof. intros Hi j x Hj. rewrite lookup_partial_alter_ne; congruence. Qed.
Lemma partial_alter_subset {A} (m : M A) i f :
  m !! i = None → is_Some (f (m !! i)) → m ⊂ partial_alter f i m.
Proof.
  intros Hi Hfi. split.
  * by apply partial_alter_subseteq.
  * inversion Hfi as [x Hx]. intros Hm.
    apply (Some_ne_None x). rewrite <-(Hm i x); [done|].
    by rewrite lookup_partial_alter.
Qed.

(** ** Properties of the [alter] operation *)
Lemma lookup_alter {A} (f : A → A) m i : alter f i m !! i = f <$> m !! i.
Proof. apply lookup_partial_alter. Qed.
Lemma lookup_alter_ne {A} (f : A → A) m i j : i ≠ j → alter f i m !! j = m !! j.
Proof. apply lookup_partial_alter_ne. Qed.

Lemma lookup_alter_Some {A} (f : A → A) m i j y :
  alter f i m !! j = Some y ↔
    (i = j ∧ ∃ x, m !! j = Some x ∧ y = f x) ∨ (i ≠ j ∧ m !! j = Some y).
Proof.
  destruct (decide (i = j)); subst.
  * rewrite lookup_alter. naive_solver (simplify_option_equality; eauto).
  * rewrite lookup_alter_ne by done. naive_solver.
Qed.
Lemma lookup_alter_None {A} (f : A → A) m i j :
  alter f i m !! j = None ↔ m !! j = None.
Proof.
  destruct (decide (i = j)); subst.
  * by rewrite lookup_alter, fmap_None.
  * by rewrite lookup_alter_ne.
Qed.

Lemma alter_None {A} (f : A → A) m i : m !! i = None → alter f i m = m.
Proof.
  intros Hi. apply map_eq. intros j. destruct (decide (i = j)); subst.
  * by rewrite lookup_alter, !Hi.
  * by rewrite lookup_alter_ne.
Qed.

(** ** Properties of the [delete] operation *)
Lemma lookup_delete {A} (m : M A) i : delete i m !! i = None.
Proof. apply lookup_partial_alter. Qed.
Lemma lookup_delete_ne {A} (m : M A) i j : i ≠ j → delete i m !! j = m !! j.
Proof. apply lookup_partial_alter_ne. Qed.

Lemma lookup_delete_Some {A} (m : M A) i j y :
  delete i m !! j = Some y ↔ i ≠ j ∧ m !! j = Some y.
Proof.
  split.
  * destruct (decide (i = j)); subst;
      rewrite ?lookup_delete, ?lookup_delete_ne; intuition congruence.
  * intros [??]. by rewrite lookup_delete_ne.
Qed.
Lemma lookup_delete_None {A} (m : M A) i j :
  delete i m !! j = None ↔ i = j ∨ m !! j = None.
Proof.
  destruct (decide (i = j)).
  * subst. rewrite lookup_delete. tauto.
  * rewrite lookup_delete_ne; tauto.
Qed.

Lemma delete_empty {A} i : delete i (∅ : M A) = ∅.
Proof. rewrite <-(partial_alter_self ∅) at 2. by rewrite lookup_empty. Qed.
Lemma delete_singleton {A} i (x : A) : delete i {[i, x]} = ∅.
Proof. setoid_rewrite <-partial_alter_compose. apply delete_empty. Qed.
Lemma delete_commute {A} (m : M A) i j :
  delete i (delete j m) = delete j (delete i m).
Proof. destruct (decide (i = j)). by subst. by apply partial_alter_commute. Qed.
Lemma delete_insert_ne {A} (m : M A) i j x :
  i ≠ j → delete i (<[j:=x]>m) = <[j:=x]>(delete i m).
Proof. intro. by apply partial_alter_commute. Qed.

Lemma delete_notin {A} (m : M A) i : m !! i = None → delete i m = m.
Proof.
  intros. apply map_eq. intros j. destruct (decide (i = j)).
  * subst. by rewrite lookup_delete.
  * by apply lookup_delete_ne.
Qed.

Lemma delete_partial_alter {A} (m : M A) i f :
  m !! i = None → delete i (partial_alter f i m) = m.
Proof.
  intros. unfold delete, map_delete. rewrite <-partial_alter_compose.
  unfold compose. by apply partial_alter_self_alt.
Qed.
Lemma delete_insert {A} (m : M A) i x :
  m !! i = None → delete i (<[i:=x]>m) = m.
Proof. apply delete_partial_alter. Qed.
Lemma insert_delete {A} (m : M A) i x :
  m !! i = Some x → <[i:=x]>(delete i m) = m.
Proof.
  intros Hmi. unfold delete, map_delete, insert, map_insert.
  rewrite <-partial_alter_compose. unfold compose. rewrite <-Hmi.
  by apply partial_alter_self_alt.
Qed.

Lemma delete_subseteq {A} (m : M A) i : delete i m ⊆ m.
Proof. intros j x. rewrite lookup_delete_Some. tauto. Qed.
Lemma delete_subseteq_compat {A} (m1 m2 : M A) i :
  m1 ⊆ m2 → delete i m1 ⊆ delete i m2.
Proof. intros ? j x. rewrite !lookup_delete_Some. intuition eauto. Qed.
Lemma delete_subset_alt {A} (m : M A) i x : m !! i = Some x → delete i m ⊂ m.
Proof.
  split.
  * apply delete_subseteq.
  * intros Hi. apply (None_ne_Some x).
    by rewrite <-(lookup_delete m i), (Hi i x).
Qed.
Lemma delete_subset {A} (m : M A) i : is_Some (m !! i) → delete i m ⊂ m.
Proof. inversion 1. eauto using delete_subset_alt. Qed.

(** ** Properties of the [insert] operation *)
Lemma lookup_insert {A} (m : M A) i x : <[i:=x]>m !! i = Some x.
Proof. unfold insert. apply lookup_partial_alter. Qed.
Lemma lookup_insert_rev {A}  (m : M A) i x y : <[i:=x]>m !! i = Some y → x = y.
Proof. rewrite lookup_insert. congruence. Qed.
Lemma lookup_insert_ne {A} (m : M A) i j x : i ≠ j → <[i:=x]>m !! j = m !! j.
Proof. unfold insert. apply lookup_partial_alter_ne. Qed.
Lemma insert_commute {A} (m : M A) i j x y :
  i ≠ j → <[i:=x]>(<[j:=y]>m) = <[j:=y]>(<[i:=x]>m).
Proof. apply partial_alter_commute. Qed.

Lemma lookup_insert_Some {A} (m : M A) i j x y :
  <[i:=x]>m !! j = Some y ↔ (i = j ∧ x = y) ∨ (i ≠ j ∧ m !! j = Some y).
Proof.
  split.
  * destruct (decide (i = j)); subst;
      rewrite ?lookup_insert, ?lookup_insert_ne; intuition congruence.
  * intros [[??]|[??]].
    + subst. apply lookup_insert.
    + by rewrite lookup_insert_ne.
Qed.
Lemma lookup_insert_None {A} (m : M A) i j x :
  <[i:=x]>m !! j = None ↔ m !! j = None ∧ i ≠ j.
Proof.
  split.
  * destruct (decide (i = j)); subst;
      rewrite ?lookup_insert, ?lookup_insert_ne; intuition congruence.
  * intros [??]. by rewrite lookup_insert_ne.
Qed.

Lemma insert_subseteq {A} (m : M A) i x : m !! i = None → m ⊆ <[i:=x]>m.
Proof. apply partial_alter_subseteq. Qed.
Lemma insert_subset {A} (m : M A) i x : m !! i = None → m ⊂ <[i:=x]>m.
Proof. intro. apply partial_alter_subset; eauto. Qed.
Lemma insert_subseteq_r {A} (m1 m2 : M A) i x :
  m1 !! i = None → m1 ⊆ m2 → m1 ⊆ <[i:=x]>m2.
Proof.
  intros ?? j ?. destruct (decide (j = i)); subst.
  * congruence.
  * rewrite lookup_insert_ne; auto.
Qed.

Lemma insert_delete_subseteq {A} (m1 m2 : M A) i x :
  m1 !! i = None → <[i:=x]> m1 ⊆ m2 → m1 ⊆ delete i m2.
Proof.
  intros Hi Hix j y Hj. destruct (decide (i = j)); subst.
  * congruence.
  * rewrite lookup_delete_ne by done. apply Hix.
    by rewrite lookup_insert_ne by done.
Qed.
Lemma delete_insert_subseteq {A} (m1 m2 : M A) i x :
  m1 !! i = Some x → delete i m1 ⊆ m2 → m1 ⊆ <[i:=x]> m2.
Proof.
  intros Hix Hi j y Hj. destruct (decide (i = j)); subst.
  * rewrite lookup_insert. congruence.
  * rewrite lookup_insert_ne by done. apply Hi. by rewrite lookup_delete_ne.
Qed.

Lemma insert_delete_subset {A} (m1 m2 : M A) i x :
  m1 !! i = None → <[i:=x]> m1 ⊂ m2 → m1 ⊂ delete i m2.
Proof.
  intros ? [Hm12 Hm21]. split.
  * eauto using insert_delete_subseteq.
  * contradict Hm21. apply delete_insert_subseteq; auto.
    apply Hm12. by rewrite lookup_insert.
Qed.

Lemma insert_subset_inv {A} (m1 m2 : M A) i x :
  m1 !! i = None → <[i:=x]> m1 ⊂ m2 →
  ∃ m2', m2 = <[i:=x]>m2' ∧ m1 ⊂ m2' ∧ m2' !! i = None.
Proof.
  intros Hi Hm1m2. exists (delete i m2). split_ands.
  * rewrite insert_delete. done. eapply lookup_weaken, subset_subseteq; eauto.
    by rewrite lookup_insert.
  * eauto using insert_delete_subset.
  * by rewrite lookup_delete.
Qed.

(** ** Properties of the singleton maps *)
Lemma lookup_singleton_Some {A} i j (x y : A) :
  {[i, x]} !! j = Some y ↔ i = j ∧ x = y.
Proof.
  unfold singleton, map_singleton.
  rewrite lookup_insert_Some, lookup_empty. simpl. intuition congruence.
Qed.
Lemma lookup_singleton_None {A} i j (x : A) : {[i, x]} !! j = None ↔ i ≠ j.
Proof.
  unfold singleton, map_singleton.
  rewrite lookup_insert_None, lookup_empty. simpl. tauto.
Qed.
Lemma lookup_singleton {A} i (x : A) : {[i, x]} !! i = Some x.
Proof. by rewrite lookup_singleton_Some. Qed.
Lemma lookup_singleton_ne {A} i j (x : A) : i ≠ j → {[i, x]} !! j = None.
Proof. by rewrite lookup_singleton_None. Qed.

Lemma insert_singleton {A} i (x y : A) : <[i:=y]>{[i, x]} = {[i, y]}.
Proof.
  unfold singleton, map_singleton, insert, map_insert.
  by rewrite <-partial_alter_compose.
Qed.
Lemma alter_singleton {A} (f : A → A) i x : alter f i {[i,x]} = {[i, f x]}.
Proof.
  intros. apply map_eq. intros i'. destruct (decide (i = i')); subst.
  * by rewrite lookup_alter, !lookup_singleton.
  * by rewrite lookup_alter_ne, !lookup_singleton_ne.
Qed.
Lemma alter_singleton_ne {A} (f : A → A) i j x :
  i ≠ j → alter f i {[j,x]} = {[j,x]}.
Proof.
  intros. apply map_eq. intros i'. destruct (decide (i = i')); subst.
  * by rewrite lookup_alter, lookup_singleton_ne.
  * by rewrite lookup_alter_ne.
Qed.

(** ** Properties of conversion to lists *)
Lemma map_to_list_unique {A} (m : M A) i x y :
  (i,x) ∈ map_to_list m → (i,y) ∈ map_to_list m → x = y.
Proof. rewrite !elem_of_map_to_list. congruence. Qed.
Lemma map_to_list_key_nodup {A} (m : M A) : NoDup (fst <$> map_to_list m).
Proof. eauto using NoDup_fmap_fst, map_to_list_unique, map_to_list_nodup. Qed.

Lemma elem_of_map_of_list_1 {A} (l : list (K * A)) i x :
  NoDup (fst <$> l) → (i,x) ∈ l → map_of_list l !! i = Some x.
Proof.
  induction l as [|[j y] l IH]; simpl.
  { by rewrite elem_of_nil. }
  rewrite NoDup_cons, elem_of_cons, elem_of_list_fmap.
  intros [Hl ?] [?|?]; simplify_equality.
  { by rewrite lookup_insert. }
  destruct (decide (i = j)); simplify_equality.
  * destruct Hl. by exists (j,x).
  * rewrite lookup_insert_ne; auto.
Qed.
Lemma elem_of_map_of_list_2 {A} (l : list (K * A)) i x :
  map_of_list l !! i = Some x → (i,x) ∈ l.
Proof.
  induction l as [|[j y] l IH]; simpl.
  { by rewrite lookup_empty. }
  rewrite elem_of_cons. destruct (decide (i = j)); simplify_equality.
  * rewrite lookup_insert; intuition congruence.
  * rewrite lookup_insert_ne; intuition congruence.
Qed.
Lemma elem_of_map_of_list {A} (l : list (K * A)) i x :
  NoDup (fst <$> l) → (i,x) ∈ l ↔ map_of_list l !! i = Some x.
Proof. split; auto using elem_of_map_of_list_1, elem_of_map_of_list_2. Qed.

Lemma not_elem_of_map_of_list_1 {A} (l : list (K * A)) i :
  i ∉ fst <$> l → map_of_list l !! i = None.
Proof.
  rewrite elem_of_list_fmap, eq_None_not_Some.
  intros Hi [x ?]. destruct Hi. exists (i,x). simpl.
  auto using elem_of_map_of_list_2.
Qed.
Lemma not_elem_of_map_of_list_2 {A} (l : list (K * A)) i :
  map_of_list l !! i = None → i ∉ fst <$> l.
Proof.
  induction l as [|[j y] l IH]; simpl.
  { rewrite elem_of_nil. tauto. }
  rewrite elem_of_cons. destruct (decide (i = j)); simplify_equality.
  * by rewrite lookup_insert.
  * by rewrite lookup_insert_ne; intuition.
Qed.
Lemma not_elem_of_map_of_list {A} (l : list (K * A)) i :
  i ∉ fst <$> l ↔ map_of_list l !! i = None.
Proof.
  split; auto using not_elem_of_map_of_list_1, not_elem_of_map_of_list_2.
Qed.

Lemma map_of_list_proper {A} (l1 l2 : list (K * A)) :
  NoDup (fst <$> l1) → l1 ≡ₚ l2 → map_of_list l1 = map_of_list l2.
Proof.
  intros ? Hperm. apply map_eq. intros i. apply option_eq. intros x.
  by rewrite <-!elem_of_map_of_list; rewrite <-?Hperm.
Qed.
Lemma map_of_list_inj {A} (l1 l2 : list (K * A)) :
  NoDup (fst <$> l1) → NoDup (fst <$> l2) →
  map_of_list l1 = map_of_list l2 → l1 ≡ₚ l2.
Proof.
  intros ?? Hl1l2. apply NoDup_Permutation; auto using (NoDup_fmap_1 fst).
  intros [i x]. by rewrite !elem_of_map_of_list, Hl1l2.
Qed.
Lemma map_of_to_list {A} (m : M A) : map_of_list (map_to_list m) = m.
Proof.
  apply map_eq. intros i. apply option_eq. intros x.
  by rewrite <-elem_of_map_of_list, elem_of_map_to_list
    by auto using map_to_list_key_nodup.
Qed.
Lemma map_to_of_list {A} (l : list (K * A)) :
  NoDup (fst <$> l) → map_to_list (map_of_list l) ≡ₚ l.
Proof. auto using map_of_list_inj, map_to_list_key_nodup, map_of_to_list. Qed.
Lemma map_to_list_inj {A} (m1 m2 : M A) :
  map_to_list m1 ≡ₚ map_to_list m2 → m1 = m2.
Proof.
  intros. rewrite <-(map_of_to_list m1), <-(map_of_to_list m2).
  auto using map_of_list_proper, map_to_list_key_nodup.
Qed.

Lemma map_to_list_empty {A} : map_to_list ∅ = @nil (K * A).
Proof.
  apply elem_of_nil_inv. intros [i x].
  rewrite elem_of_map_to_list. apply lookup_empty_Some.
Qed.
Lemma map_to_list_insert {A} (m : M A) i x :
  m !! i = None → map_to_list (<[i:=x]>m) ≡ₚ (i,x) :: map_to_list m.
Proof.
  intros. apply map_of_list_inj; simpl.
  * apply map_to_list_key_nodup.
  * constructor; auto using map_to_list_key_nodup.
    rewrite elem_of_list_fmap. intros [[??] [? Hlookup]]; subst; simpl in *.
    rewrite elem_of_map_to_list in Hlookup. congruence.
  * by rewrite !map_of_to_list.
Qed.

Lemma map_of_list_nil {A} : map_of_list (@nil (K * A)) = ∅.
Proof. done. Qed.
Lemma map_of_list_cons {A} (l : list (K * A)) i x :
  map_of_list ((i, x) :: l) = <[i:=x]>(map_of_list l).
Proof. done. Qed.

Lemma map_to_list_empty_inv_alt {A}  (m : M A) : map_to_list m ≡ₚ [] → m = ∅.
Proof. rewrite <-map_to_list_empty. apply map_to_list_inj. Qed.
Lemma map_to_list_empty_inv {A} (m : M A) : map_to_list m = [] → m = ∅.
Proof. intros Hm. apply map_to_list_empty_inv_alt. by rewrite Hm. Qed.

Lemma map_to_list_insert_inv {A} (m : M A) l i x :
  map_to_list m ≡ₚ (i,x) :: l → m = <[i:=x]>(map_of_list l).
Proof.
  intros Hperm. apply map_to_list_inj.
  assert (NoDup (fst <$> (i, x) :: l)) as Hnodup.
  { rewrite <-Hperm. auto using map_to_list_key_nodup. }
  simpl in Hnodup. rewrite NoDup_cons in Hnodup. destruct Hnodup.
  rewrite Hperm, map_to_list_insert, map_to_of_list;
    auto using not_elem_of_map_of_list_1.
Qed.

(** * Induction principles *)
Lemma map_ind {A} (P : M A → Prop) :
  P ∅ → (∀ i x m, m !! i = None → P m → P (<[i:=x]>m)) → ∀ m, P m.
Proof.
  intros Hemp Hins.
  cut (∀ l, NoDup (fst <$> l) → ∀ m, map_to_list m ≡ₚ l → P m).
  { intros help m.
    apply (help (map_to_list m)); auto using map_to_list_key_nodup. }
  induction l as [|[i x] l IH]; intros Hnodup m Hml.
  { apply map_to_list_empty_inv_alt in Hml. by subst. }
  inversion_clear Hnodup.
  apply map_to_list_insert_inv in Hml. subst. apply Hins.
  * by apply not_elem_of_map_of_list_1.
  * apply IH; auto using map_to_of_list.
Qed.

Lemma map_to_list_length {A} (m1 m2 : M A) :
  m1 ⊂ m2 → length (map_to_list m1) < length (map_to_list m2).
Proof.
  revert m2. induction m1 as [|i x m ? IH] using map_ind.
  { intros m2 Hm2. rewrite map_to_list_empty. simpl.
    apply neq_0_lt. intros Hlen. symmetry in Hlen.
    apply nil_length, map_to_list_empty_inv in Hlen.
    rewrite Hlen in Hm2. destruct (irreflexivity (⊂) ∅ Hm2). }
  intros m2 Hm2.
  destruct (insert_subset_inv m m2 i x) as (m2'&?&?&?); auto; subst.
  rewrite !map_to_list_insert; simpl; auto with arith.
Qed.

Lemma map_wf {A} : wf (@subset (M A) _).
Proof.
  apply (wf_projected (<) (length ∘ map_to_list)).
  * by apply map_to_list_length.
  * by apply lt_wf.
Qed.

(** ** Properties of the [map_forall] predicate *)
Section map_forall.
Context {A} (P : K → A → Prop).

Lemma map_forall_to_list m : map_forall P m ↔ Forall (curry P) (map_to_list m).
Proof.
  rewrite Forall_forall. split.
  * intros Hforall [i x]. rewrite elem_of_map_to_list. by apply (Hforall i x).
  * intros Hforall i x. rewrite <-elem_of_map_to_list. by apply (Hforall (i,x)).
Qed.

Context `{∀ i x, Decision (P i x)}.
Global Instance map_forall_dec m : Decision (map_forall P m).
Proof.
  refine (cast_if (decide (Forall (curry P) (map_to_list m))));
    by rewrite map_forall_to_list.
Defined.

Lemma map_not_forall (m : M A) :
  ¬map_forall P m ↔ ∃ i x, m !! i = Some x ∧ ¬P i x.
Proof.
  split.
  * rewrite map_forall_to_list. intros Hm.
    apply (not_Forall_Exists _), Exists_exists in Hm.
    destruct Hm as ([i x]&?&?). exists i x. by rewrite <-elem_of_map_to_list.
  * intros (i&x&?&?) Hm. specialize (Hm i x). tauto.
Qed.
End map_forall.

(** ** Properties of the [merge] operation *)
Lemma merge_Some {A B C} (f : option A → option B → option C)
    `{!PropHolds (f None None = None)} m1 m2 m :
  (∀ i, m !! i = f (m1 !! i) (m2 !! i)) ↔ merge f m1 m2 = m.
Proof.
  split; [| intro; subst; apply (lookup_merge _) ].
  intros Hlookup. apply map_eq. intros. rewrite Hlookup. apply (lookup_merge _).
Qed.

Section merge.
Context {A} (f : option A → option A → option A).

Global Instance: LeftId (=) None f → LeftId (=) ∅ (merge f).
Proof.
  intros ??. apply map_eq. intros.
  by rewrite !(lookup_merge f), lookup_empty, (left_id_L None f).
Qed.
Global Instance: RightId (=) None f → RightId (=) ∅ (merge f).
Proof.
  intros ??. apply map_eq. intros.
  by rewrite !(lookup_merge f), lookup_empty, (right_id_L None f).
Qed.

Context `{!PropHolds (f None None = None)}.

Lemma merge_commutative m1 m2 :
  (∀ i, f (m1 !! i) (m2 !! i) = f (m2 !! i) (m1 !! i)) →
  merge f m1 m2 = merge f m2 m1.
Proof. intros. apply map_eq. intros. by rewrite !(lookup_merge f). Qed.
Global Instance: Commutative (=) f → Commutative (=) (merge f).
Proof.
  intros ???. apply merge_commutative. intros. by apply (commutative f).
Qed.
Lemma merge_associative m1 m2 m3 :
  (∀ i, f (m1 !! i) (f (m2 !! i) (m3 !! i)) =
        f (f (m1 !! i) (m2 !! i)) (m3 !! i)) →
  merge f m1 (merge f m2 m3) = merge f (merge f m1 m2) m3.
Proof. intros. apply map_eq. intros. by rewrite !(lookup_merge f). Qed.
Global Instance: Associative (=) f → Associative (=) (merge f).
Proof.
  intros ????. apply merge_associative. intros. by apply (associative_L f).
Qed.
Lemma merge_idempotent m1 :
  (∀ i, f (m1 !! i) (m1 !! i) = m1 !! i) → merge f m1 m1 = m1.
Proof. intros. apply map_eq. intros. by rewrite !(lookup_merge f). Qed.
Global Instance: Idempotent (=) f → Idempotent (=) (merge f).
Proof. intros ??. apply merge_idempotent. intros. by apply (idempotent f). Qed.

Lemma partial_alter_merge (g g1 g2 : option A → option A) m1 m2 i :
  g (f (m1 !! i) (m2 !! i)) = f (g1 (m1 !! i)) (g2 (m2 !! i)) →
  partial_alter g i (merge f m1 m2) =
    merge f (partial_alter g1 i m1) (partial_alter g2 i m2).
Proof.
  intro. apply map_eq. intros j. destruct (decide (i = j)); subst.
  * by rewrite (lookup_merge _), !lookup_partial_alter, !(lookup_merge _).
  * by rewrite (lookup_merge _), !lookup_partial_alter_ne, (lookup_merge _).
Qed.
Lemma partial_alter_merge_l (g g1 : option A → option A) m1 m2 i :
  g (f (m1 !! i) (m2 !! i)) = f (g1 (m1 !! i)) (m2 !! i) →
  partial_alter g i (merge f m1 m2) = merge f (partial_alter g1 i m1) m2.
Proof.
  intro. apply map_eq. intros j. destruct (decide (i = j)); subst.
  * by rewrite (lookup_merge _), !lookup_partial_alter, !(lookup_merge _).
  * by rewrite (lookup_merge _), !lookup_partial_alter_ne, (lookup_merge _).
Qed.
Lemma partial_alter_merge_r (g g2 : option A → option A) m1 m2 i :
  g (f (m1 !! i) (m2 !! i)) = f (m1 !! i) (g2 (m2 !! i)) →
  partial_alter g i (merge f m1 m2) = merge f m1 (partial_alter g2 i m2).
Proof.
  intro. apply map_eq. intros j. destruct (decide (i = j)); subst.
  * by rewrite (lookup_merge _), !lookup_partial_alter, !(lookup_merge _).
  * by rewrite (lookup_merge _), !lookup_partial_alter_ne, (lookup_merge _).
Qed.

Lemma insert_merge_l m1 m2 i x :
  f (Some x) (m2 !! i) = Some x →
  <[i:=x]>(merge f m1 m2) = merge f (<[i:=x]>m1) m2.
Proof.
  intros. unfold insert, map_insert, alter, map_alter.
  by apply partial_alter_merge_l.
Qed.
Lemma insert_merge_r m1 m2 i x :
  f (m1 !! i) (Some x) = Some x →
  <[i:=x]>(merge f m1 m2) = merge f m1 (<[i:=x]>m2).
Proof.
  intros. unfold insert, map_insert, alter, map_alter.
  by apply partial_alter_merge_r.
Qed.
End merge.

(** ** Properties on the [map_intersection_forall] relation *)
Section intersection_forall.
Context {A} (R : relation A).

Global Instance map_intersection_forall_sym:
  Symmetric R → Symmetric (map_intersection_forall R).
Proof. firstorder auto. Qed.
Lemma map_intersection_forall_empty_l (m : M A) : map_intersection_forall R ∅ m.
Proof. intros ???. by rewrite lookup_empty. Qed.
Lemma map_intersection_forall_empty_r (m : M A) : map_intersection_forall R m ∅.
Proof. intros ???. by rewrite lookup_empty. Qed.

Lemma map_intersection_forall_alt (m1 m2 : M A) :
  map_intersection_forall R m1 m2 ↔
    map_forall (λ _, curry R) (merge (λ x y,
      match x, y with
      | Some x, Some y => Some (x,y)
      | _, _ => None
      end) m1 m2).
Proof.
  split.
  * intros Hm12 i [x y]. rewrite lookup_merge by done. intros.
    destruct (m1 !! i) eqn:?, (m2 !! i) eqn:?; simplify_equality.
    eapply Hm12; eauto.
  * intros Hm12 i x y ??. apply (Hm12 i (x,y)).
    rewrite lookup_merge by done. by simplify_option_equality.
Qed.

(** Due to the finiteness of finite maps, we can extract a witness if the
relation does not hold. *)
Lemma map_not_intersection_forall `{∀ x y, Decision (R x y)} (m1 m2 : M A) :
  ¬map_intersection_forall R m1 m2
    ↔ ∃ i x1 x2, m1 !! i = Some x1 ∧ m2 !! i = Some x2 ∧ ¬R x1 x2.
Proof.
  split.
  * rewrite map_intersection_forall_alt, (map_not_forall _).
    intros (i & [x y] & Hm12 & ?). rewrite lookup_merge in Hm12 by done.
    exists i x y. by destruct (m1 !! i), (m2 !! i); simplify_equality.
  * intros (i & x1 & x2 & Hx1 & Hx2 & Hx1x2) Hm12.
    by apply Hx1x2, (Hm12 i x1 x2).
Qed.
End intersection_forall.

(** ** Properties on the disjoint maps *)
Lemma map_disjoint_alt {A} (m1 m2 : M A) :
  m1 ⊥ m2 ↔ ∀ i, m1 !! i = None ∨ m2 !! i = None.
Proof.
  split; intros Hm1m2 i; specialize (Hm1m2 i);
    destruct (m1 !! i), (m2 !! i); naive_solver.
Qed.
Lemma map_not_disjoint {A} (m1 m2 : M A) :
  ¬m1 ⊥ m2 ↔ ∃ i x1 x2, m1 !! i = Some x1 ∧ m2 !! i = Some x2.
Proof.
  unfold disjoint, map_disjoint. rewrite map_not_intersection_forall.
  * naive_solver.
  * right. auto.
Qed.

Global Instance: Symmetric (@disjoint (M A) _).
Proof. intro. apply map_intersection_forall_sym. auto. Qed.
Lemma map_disjoint_empty_l {A} (m : M A) : ∅ ⊥ m.
Proof. apply map_intersection_forall_empty_l. Qed.
Lemma map_disjoint_empty_r {A} (m : M A) : m ⊥ ∅.
Proof. apply map_intersection_forall_empty_r. Qed.

Lemma map_disjoint_weaken {A} (m1 m1' m2 m2' : M A) :
  m1' ⊥ m2' → m1 ⊆ m1' → m2 ⊆ m2' → m1 ⊥ m2.
Proof.
  intros Hdisjoint Hm1 Hm2 i x1 x2 Hx1 Hx2.
  destruct (Hdisjoint i x1 x2); auto.
Qed.
Lemma map_disjoint_weaken_l {A} (m1 m1' m2  : M A) :
  m1' ⊥ m2 → m1 ⊆ m1' → m1 ⊥ m2.
Proof. eauto using map_disjoint_weaken. Qed.
Lemma map_disjoint_weaken_r {A} (m1 m2 m2' : M A) :
  m1 ⊥ m2' → m2 ⊆ m2' → m1 ⊥ m2.
Proof. eauto using map_disjoint_weaken. Qed.

Lemma map_disjoint_Some_l {A} (m1 m2 : M A) i x:
  m1 ⊥ m2 → m1 !! i = Some x → m2 !! i = None.
Proof.
  intros Hdisjoint ?. rewrite eq_None_not_Some.
  intros [x2 ?]. by apply (Hdisjoint i x x2).
Qed.
Lemma map_disjoint_Some_r {A} (m1 m2 : M A) i x:
  m1 ⊥ m2 → m2 !! i = Some x → m1 !! i = None.
Proof. rewrite (symmetry_iff (⊥)). apply map_disjoint_Some_l. Qed.

Lemma map_disjoint_singleton_l {A} (m : M A) i x : {[i, x]} ⊥ m ↔ m !! i = None.
Proof.
  split.
  * intro. apply (map_disjoint_Some_l {[i, x]} _ _ x);
      auto using lookup_singleton.
  * intros ? j y1 y2. destruct (decide (i = j)); subst.
    + rewrite lookup_singleton. intuition congruence.
    + by rewrite lookup_singleton_ne.
Qed.
Lemma map_disjoint_singleton_r {A} (m : M A) i x :
  m ⊥ {[i, x]} ↔ m !! i = None.
Proof. by rewrite (symmetry_iff (⊥)), map_disjoint_singleton_l. Qed.

Lemma map_disjoint_singleton_l_2 {A} (m : M A) i x :
  m !! i = None → {[i, x]} ⊥ m.
Proof. by rewrite map_disjoint_singleton_l. Qed.
Lemma map_disjoint_singleton_r_2 {A} (m : M A) i x :
  m !! i = None → m ⊥ {[i, x]}.
Proof. by rewrite map_disjoint_singleton_r. Qed.

Lemma map_disjoint_delete_l {A} (m1 m2 : M A) i : m1 ⊥ m2 → delete i m1 ⊥ m2.
Proof.
  rewrite !map_disjoint_alt.
  intros Hdisjoint j. destruct (Hdisjoint j); auto.
  rewrite lookup_delete_None. tauto.
Qed.
Lemma map_disjoint_delete_r {A} (m1 m2 : M A) i : m1 ⊥ m2 → m1 ⊥ delete i m2.
Proof. symmetry. by apply map_disjoint_delete_l. Qed.

(** ** Properties of the [union_with] operation *)
Section union_with.
Context {A} (f : A → A → option A).

Lemma lookup_union_with m1 m2 i z :
  union_with f m1 m2 !! i = z ↔
    (m1 !! i = None ∧ m2 !! i = None ∧ z = None) ∨
    (∃ x, m1 !! i = Some x ∧ m2 !! i = None ∧ z = Some x) ∨
    (∃ y, m1 !! i = None ∧ m2 !! i = Some y ∧ z = Some y) ∨
    (∃ x y, m1 !! i = Some x ∧ m2 !! i = Some y ∧ z = f x y).
Proof.
  unfold union_with, map_union_with. rewrite (lookup_merge _).
  destruct (m1 !! i), (m2 !! i); compute; naive_solver.
Qed.
Lemma lookup_union_with_Some m1 m2 i z :
  union_with f m1 m2 !! i = Some z ↔
    (m1 !! i = Some z ∧ m2 !! i = None) ∨
    (m1 !! i = None ∧ m2 !! i = Some z) ∨
    (∃ x y, m1 !! i = Some x ∧ m2 !! i = Some y ∧ f x y = Some z).
Proof. rewrite lookup_union_with. naive_solver. Qed.
Lemma lookup_union_with_None m1 m2 i :
  union_with f m1 m2 !! i = None ↔
    (m1 !! i = None ∧ m2 !! i = None) ∨
    (∃ x y, m1 !! i = Some x ∧ m2 !! i = Some y ∧ f x y = None).
Proof. rewrite lookup_union_with. naive_solver. Qed.

Lemma lookup_union_with_Some_lr m1 m2 i x y z :
  m1 !! i = Some x → m2 !! i = Some y → f x y = Some z →
  union_with f m1 m2 !! i = Some z.
Proof. rewrite lookup_union_with. naive_solver. Qed.
Lemma lookup_union_with_Some_l m1 m2 i x :
  m1 !! i = Some x → m2 !! i = None → union_with f m1 m2 !! i = Some x.
Proof. rewrite lookup_union_with. naive_solver. Qed.
Lemma lookup_union_with_Some_r m1 m2 i y :
  m1 !! i = None → m2 !! i = Some y → union_with f m1 m2 !! i = Some y.
Proof. rewrite lookup_union_with. naive_solver. Qed.

Global Instance: LeftId (@eq (M A)) ∅ (union_with f).
Proof. unfold union_with, map_union_with. apply _. Qed.
Global Instance: RightId (@eq (M A)) ∅ (union_with f).
Proof. unfold union_with, map_union_with. apply _. Qed.

Lemma union_with_commutative m1 m2 :
  (∀ i x y, m1 !! i = Some x → m2 !! i = Some y → f x y = f y x) →
  union_with f m1 m2 = union_with f m2 m1.
Proof.
  intros. apply (merge_commutative _). intros i.
  destruct (m1 !! i) eqn:?, (m2 !! i) eqn:?; simpl; eauto.
Qed.
Global Instance: Commutative (=) f → Commutative (@eq (M A)) (union_with f).
Proof. intros ???. apply union_with_commutative. eauto. Qed.

Lemma union_with_idempotent m :
  (∀ i x, m !! i = Some x → f x x = Some x) → union_with f m m = m.
Proof.
  intros. apply (merge_idempotent _). intros i.
  destruct (m !! i) eqn:?; simpl; eauto.
Qed.

Lemma alter_union_with (g : A → A) m1 m2 i :
  (∀ x y, m1 !! i = Some x → m2 !! i = Some y → g <$> f x y = f (g x) (g y)) →
  alter g i (union_with f m1 m2) =
    union_with f (alter g i m1) (alter g i m2).
Proof.
  intros. apply (partial_alter_merge _).
  destruct (m1 !! i) eqn:?, (m2 !! i) eqn:?; simpl; eauto.
Qed.
Lemma alter_union_with_l (g : A → A) m1 m2 i :
  (∀ x y, m1 !! i = Some x → m2 !! i = Some y → g <$> f x y = f (g x) y) →
  (∀ y, m1 !! i = None → m2 !! i = Some y → g y = y) →
  alter g i (union_with f m1 m2) = union_with f (alter g i m1) m2.
Proof.
  intros. apply (partial_alter_merge_l _).
  destruct (m1 !! i) eqn:?, (m2 !! i) eqn:?; simpl; eauto using f_equal.
Qed.
Lemma alter_union_with_r (g : A → A) m1 m2 i :
  (∀ x y, m1 !! i = Some x → m2 !! i = Some y → g <$> f x y = f x (g y)) →
  (∀ x, m1 !! i = Some x → m2 !! i = None → g x = x) →
  alter g i (union_with f m1 m2) = union_with f m1 (alter g i m2).
Proof.
  intros. apply (partial_alter_merge_r _).
  destruct (m1 !! i) eqn:?, (m2 !! i) eqn:?; simpl; eauto using f_equal.
Qed.

Lemma delete_union_with m1 m2 i :
  delete i (union_with f m1 m2) = union_with f (delete i m1) (delete i m2).
Proof. by apply (partial_alter_merge _). Qed.

Lemma delete_list_union_with (m1 m2 : M A) is :
  delete_list is (union_with f m1 m2) =
    union_with f (delete_list is m1) (delete_list is m2).
Proof. induction is; simpl. done. by rewrite IHis, delete_union_with. Qed.

Lemma insert_union_with m1 m2 i x :
  (∀ x, f x x = Some x) →
  <[i:=x]>(union_with f m1 m2) = union_with f (<[i:=x]>m1) (<[i:=x]>m2).
Proof. intros. apply (partial_alter_merge _). simpl. auto. Qed.
Lemma insert_union_with_l m1 m2 i x :
  m2 !! i = None → <[i:=x]>(union_with f m1 m2) = union_with f (<[i:=x]>m1) m2.
Proof.
  intros Hm2. unfold union_with, map_union_with.
  rewrite (insert_merge_l _). done. by rewrite Hm2.
Qed.
Lemma insert_union_with_r m1 m2 i x :
  m1 !! i = None → <[i:=x]>(union_with f m1 m2) = union_with f m1 (<[i:=x]>m2).
Proof.
  intros Hm1. unfold union_with, map_union_with.
  rewrite (insert_merge_r _). done. by rewrite Hm1.
Qed.
End union_with.

(** ** Properties of the [union] operation *)
Global Instance: LeftId (@eq (M A)) ∅ (∪) := _.
Global Instance: RightId (@eq (M A)) ∅ (∪) := _.
Global Instance: Associative (@eq (M A)) (∪).
Proof.
  intros A m1 m2 m3. unfold union, map_union, union_with, map_union_with.
  apply (merge_associative _). intros i.
  by destruct (m1 !! i), (m2 !! i), (m3 !! i).
Qed.
Global Instance: Idempotent (@eq (M A)) (∪).
Proof. intros A ?. by apply union_with_idempotent. Qed.

Lemma lookup_union_Some_raw {A} (m1 m2 : M A) i x :
  (m1 ∪ m2) !! i = Some x ↔
    m1 !! i = Some x ∨ (m1 !! i = None ∧ m2 !! i = Some x).
Proof.
  unfold union, map_union, union_with, map_union_with. rewrite (lookup_merge _).
  destruct (m1 !! i), (m2 !! i); compute; intuition congruence.
Qed.
Lemma lookup_union_None {A} (m1 m2 : M A) i :
  (m1 ∪ m2) !! i = None ↔ m1 !! i = None ∧ m2 !! i = None.
Proof.
  unfold union, map_union, union_with, map_union_with. rewrite (lookup_merge _).
  destruct (m1 !! i), (m2 !! i); compute; intuition congruence.
Qed.

Lemma lookup_union_Some {A} (m1 m2 : M A) i x :
  m1 ⊥ m2 → (m1 ∪ m2) !! i = Some x ↔ m1 !! i = Some x ∨ m2 !! i = Some x.
Proof.
  intros Hdisjoint. rewrite lookup_union_Some_raw.
  intuition eauto using map_disjoint_Some_r.
Qed.

Lemma lookup_union_Some_l {A} (m1 m2 : M A) i x :
  m1 !! i = Some x → (m1 ∪ m2) !! i = Some x.
Proof. intro. rewrite lookup_union_Some_raw; intuition. Qed.
Lemma lookup_union_Some_r {A} (m1 m2 : M A) i x :
  m1 ⊥ m2 → m2 !! i = Some x → (m1 ∪ m2) !! i = Some x.
Proof. intro. rewrite lookup_union_Some; intuition. Qed.

Lemma map_union_commutative {A} (m1 m2 : M A) : m1 ⊥ m2 → m1 ∪ m2 = m2 ∪ m1.
Proof.
  intros Hdisjoint. apply (merge_commutative (union_with (λ x _, Some x))).
  intros i. specialize (Hdisjoint i).
  destruct (m1 !! i), (m2 !! i); compute; naive_solver.
Qed.

Lemma map_subseteq_union {A} (m1 m2 : M A) : m1 ⊆ m2 → m1 ∪ m2 = m2.
Proof.
  intros Hm1m2. apply map_eq. intros i. apply option_eq. intros x.
  rewrite lookup_union_Some_raw. split; [by intuition |].
  intros Hm2. specialize (Hm1m2 i). destruct (m1 !! i) as [y|]; [| by auto].
  rewrite (Hm1m2 y eq_refl) in Hm2. intuition congruence.
Qed.

Lemma map_union_subseteq_l {A} (m1 m2 : M A) : m1 ⊆ m1 ∪ m2.
Proof. intros ? i x. rewrite lookup_union_Some_raw. intuition. Qed.
Lemma map_union_subseteq_r {A} (m1 m2 : M A) : m1 ⊥ m2 → m2 ⊆ m1 ∪ m2.
Proof.
  intros. rewrite map_union_commutative by done. by apply map_union_subseteq_l.
Qed.

Lemma map_union_subseteq_l_alt {A} (m1 m2 m3 : M A) : m1 ⊆ m2 → m1 ⊆ m2 ∪ m3.
Proof. intros. transitivity m2; auto using map_union_subseteq_l. Qed.
Lemma map_union_subseteq_r_alt {A} (m1 m2 m3 : M A) :
  m2 ⊥ m3 → m1 ⊆ m3 → m1 ⊆ m2 ∪ m3.
Proof. intros. transitivity m3; auto using map_union_subseteq_r. Qed.

Lemma map_union_preserving_l {A} (m1 m2 m3 : M A) : m1 ⊆ m2 → m3 ∪ m1 ⊆ m3 ∪ m2.
Proof. intros ???. rewrite !lookup_union_Some_raw. naive_solver. Qed.
Lemma map_union_preserving_r {A} (m1 m2 m3 : M A) :
  m2 ⊥ m3 → m1 ⊆ m2 → m1 ∪ m3 ⊆ m2 ∪ m3.
Proof.
  intros. rewrite !(map_union_commutative _ m3)
    by eauto using map_disjoint_weaken_l.
  by apply map_union_preserving_l.
Qed.

Lemma map_union_reflecting_l {A} (m1 m2 m3 : M A) :
  m3 ⊥ m1 → m3 ⊥ m2 → m3 ∪ m1 ⊆ m3 ∪ m2 → m1 ⊆ m2.
Proof.
  intros Hm3m1 Hm3m2 E b x ?. specialize (E b x).
  rewrite !lookup_union_Some in E by done.
  destruct E; auto. by destruct (Hm3m1 b x x).
Qed.
Lemma map_union_reflecting_r {A} (m1 m2 m3 : M A) :
  m1 ⊥ m3 → m2 ⊥ m3 → m1 ∪ m3 ⊆ m2 ∪ m3 → m1 ⊆ m2.
Proof.
  intros ??. rewrite !(map_union_commutative _ m3) by done.
  by apply map_union_reflecting_l.
Qed.

Lemma map_union_cancel_l {A} (m1 m2 m3 : M A) :
  m1 ⊥ m3 → m2 ⊥ m3 → m3 ∪ m1 = m3 ∪ m2 → m1 = m2.
Proof.
  intros. by apply (anti_symmetric _);
    apply map_union_reflecting_l with m3; auto with congruence.
Qed.
Lemma map_union_cancel_r {A} (m1 m2 m3 : M A) :
  m1 ⊥ m3 → m2 ⊥ m3 → m1 ∪ m3 = m2 ∪ m3 → m1 = m2.
Proof.
  intros. apply (anti_symmetric _);
    apply map_union_reflecting_r with m3; auto with congruence.
Qed.

Lemma map_disjoint_union_l {A} (m1 m2 m3 : M A) :
  m1 ∪ m2 ⊥ m3 ↔ m1 ⊥ m3 ∧ m2 ⊥ m3.
Proof.
  rewrite !map_disjoint_alt. setoid_rewrite lookup_union_None. naive_solver.
Qed.
Lemma map_disjoint_union_r {A} (m1 m2 m3 : M A) :
  m1 ⊥ m2 ∪ m3 ↔ m1 ⊥ m2 ∧ m1 ⊥ m3.
Proof.
  rewrite !map_disjoint_alt. setoid_rewrite lookup_union_None. naive_solver.
Qed.
Lemma map_disjoint_union_l_2 {A} (m1 m2 m3 : M A) :
  m1 ⊥ m3 → m2 ⊥ m3 → m1 ∪ m2 ⊥ m3.
Proof. by rewrite map_disjoint_union_l. Qed.
Lemma map_disjoint_union_r_2 {A} (m1 m2 m3 : M A) :
  m1 ⊥ m2 → m1 ⊥ m3 → m1 ⊥ m2 ∪ m3.
Proof. by rewrite map_disjoint_union_r. Qed.

Lemma insert_union_singleton_l {A} (m : M A) i x : <[i:=x]>m = {[i,x]} ∪ m.
Proof.
  apply map_eq. intros j. apply option_eq. intros y.
  rewrite lookup_union_Some_raw.
  destruct (decide (i = j)); subst.
  * rewrite !lookup_singleton, lookup_insert. intuition congruence.
  * rewrite !lookup_singleton_ne, lookup_insert_ne; intuition congruence.
Qed.
Lemma insert_union_singleton_r {A} (m : M A) i x :
  m !! i = None → <[i:=x]>m = m ∪ {[i,x]}.
Proof.
  intro. rewrite insert_union_singleton_l, map_union_commutative; [done |].
  by apply map_disjoint_singleton_l.
Qed.

Lemma map_disjoint_insert_l {A} (m1 m2 : M A) i x :
  <[i:=x]>m1 ⊥ m2 ↔ m2 !! i = None ∧ m1 ⊥ m2.
Proof.
  rewrite insert_union_singleton_l.
  by rewrite map_disjoint_union_l, map_disjoint_singleton_l.
Qed.
Lemma map_disjoint_insert_r {A} (m1 m2 : M A) i x :
  m1 ⊥ <[i:=x]>m2 ↔ m1 !! i = None ∧ m1 ⊥ m2.
Proof.
  rewrite insert_union_singleton_l.
  by rewrite map_disjoint_union_r, map_disjoint_singleton_r.
Qed.

Lemma map_disjoint_insert_l_2 {A} (m1 m2 : M A) i x :
  m2 !! i = None → m1 ⊥ m2 → <[i:=x]>m1 ⊥ m2.
Proof. by rewrite map_disjoint_insert_l. Qed.
Lemma map_disjoint_insert_r_2 {A} (m1 m2 : M A) i x :
  m1 !! i = None → m1 ⊥ m2 → m1 ⊥ <[i:=x]>m2.
Proof. by rewrite map_disjoint_insert_r. Qed.

Lemma insert_union_l {A} (m1 m2 : M A) i x :
  <[i:=x]>(m1 ∪ m2) = <[i:=x]>m1 ∪ m2.
Proof. by rewrite !insert_union_singleton_l, (associative_L (∪)). Qed.
Lemma insert_union_r {A} (m1 m2 : M A) i x :
  m1 !! i = None → <[i:=x]>(m1 ∪ m2) = m1 ∪ <[i:=x]>m2.
Proof.
  intro. rewrite !insert_union_singleton_l, !(associative_L (∪)).
  rewrite (map_union_commutative m1); [done |].
  by apply map_disjoint_singleton_r.
Qed.

Lemma insert_list_union {A} (m : M A) l : insert_list l m = map_of_list l ∪ m.
Proof.
  induction l; simpl.
  * by rewrite (left_id_L _ _).
  * by rewrite IHl, insert_union_l.
Qed.

Lemma delete_union {A} (m1 m2 : M A) i :
  delete i (m1 ∪ m2) = delete i m1 ∪ delete i m2.
Proof. apply delete_union_with. Qed.

(** ** Properties of the [union_list] operation *)
Lemma map_disjoint_union_list_l {A} (ms : list (M A)) (m : M A) :
  ⋃ ms ⊥ m ↔ Forall (.⊥ m) ms.
Proof.
  split.
  * induction ms; simpl; rewrite ?map_disjoint_union_l; intuition.
  * induction 1; simpl.
    + apply map_disjoint_empty_l.
    + by rewrite map_disjoint_union_l.
Qed.
Lemma map_disjoint_union_list_r {A} (ms : list (M A)) (m : M A) :
  m ⊥ ⋃ ms ↔ Forall (.⊥ m) ms.
Proof. by rewrite (symmetry_iff (⊥)), map_disjoint_union_list_l. Qed.

Lemma map_disjoint_union_list_l_2 {A} (ms : list (M A)) (m : M A) :
  Forall (.⊥ m) ms → ⋃ ms ⊥ m.
Proof. by rewrite map_disjoint_union_list_l. Qed.
Lemma map_disjoint_union_list_r_2 {A} (ms : list (M A)) (m : M A) :
  Forall (.⊥ m) ms → m ⊥ ⋃ ms.
Proof. by rewrite map_disjoint_union_list_r. Qed.

Lemma map_union_sublist {A} (ms1 ms2 : list (M A)) :
  ⊥ ms2 → ms1 `sublist` ms2 → ⋃ ms1 ⊆ ⋃ ms2.
Proof.
  intros Hms2. revert ms1.
  induction Hms2 as [|m2 ms2]; intros ms1; [by inversion 1|].
  rewrite sublist_cons_r. intros [?|(ms1' &?&?)]; subst; simpl.
  * transitivity (⋃ ms2); auto. by apply map_union_subseteq_r.
  * apply map_union_preserving_l; auto.
Qed.

(** ** Properties of the [intersection] operation *)
Lemma lookup_intersection_Some {A} (m1 m2 : M A) i x :
  (m1 ∩ m2) !! i = Some x ↔ m1 !! i = Some x ∧ is_Some (m2 !! i).
Proof.
  unfold intersection, map_intersection, intersection_with,
    map_intersection_with. rewrite (lookup_merge _).
  destruct (m1 !! i), (m2 !! i); compute; naive_solver.
Qed.

(** ** Properties of the [delete_list] function *)
Lemma lookup_delete_list {A} (m : M A) is j :
  j ∈ is → delete_list is m !! j = None.
Proof.
  induction 1 as [|i j is]; simpl.
  * by rewrite lookup_delete.
  * destruct (decide (i = j)).
    + subst. by rewrite lookup_delete.
    + rewrite lookup_delete_ne; auto.
Qed.
Lemma lookup_delete_list_not_elem_of {A} (m : M A) is j :
  j ∉ is → delete_list is m !! j = m !! j.
Proof.
  induction is; simpl; [done |]. rewrite elem_of_cons. intros.
  intros. rewrite lookup_delete_ne; intuition.
Qed.
Lemma delete_list_notin {A} (m : M A) is :
  Forall (λ i, m !! i = None) is → delete_list is m = m.
Proof.
  induction 1; simpl; [done |]. rewrite delete_notin; congruence.
Qed.

Lemma delete_list_insert_ne {A} (m : M A) is j x :
  j ∉ is → delete_list is (<[j:=x]>m) = <[j:=x]>(delete_list is m).
Proof.
  induction is; simpl; [done |]. rewrite elem_of_cons. intros.
  rewrite IHis, delete_insert_ne; intuition.
Qed.

Lemma map_disjoint_delete_list_l {A} (m1 m2 : M A) is :
  m1 ⊥ m2 → delete_list is m1 ⊥ m2.
Proof. induction is; simpl; auto using map_disjoint_delete_l. Qed.
Lemma map_disjoint_delete_list_r {A} (m1 m2 : M A) is :
  m1 ⊥ m2 → m1 ⊥ delete_list is m2.
Proof. induction is; simpl; auto using map_disjoint_delete_r. Qed.

Lemma delete_list_union {A} (m1 m2 : M A) is :
  delete_list is (m1 ∪ m2) = delete_list is m1 ∪ delete_list is m2.
Proof. apply delete_list_union_with. Qed.

(** ** Properties on disjointness of conversion to lists *)
Lemma map_disjoint_of_list_l {A} (m : M A) ixs :
  map_of_list ixs ⊥ m ↔ Forall (λ ix, m !! fst ix = None) ixs.
Proof.
  split.
  * induction ixs; simpl; rewrite ?map_disjoint_insert_l in *; intuition.
  * induction 1; simpl.
    + apply map_disjoint_empty_l.
    + rewrite map_disjoint_insert_l. auto.
Qed.
Lemma map_disjoint_of_list_r {A} (m : M A) ixs :
  m ⊥ map_of_list ixs ↔ Forall (λ ix, m !! fst ix = None) ixs.
Proof. by rewrite (symmetry_iff (⊥)), map_disjoint_of_list_l. Qed.

Lemma map_disjoint_of_list_zip_l {A} (m : M A) is xs :
  is `same_length` xs →
  map_of_list (zip is xs) ⊥ m ↔ Forall (λ i, m !! i = None) is.
Proof.
  intro. rewrite map_disjoint_of_list_l.
  rewrite <-(zip_fst is xs) at 2 by done. by rewrite Forall_fmap.
Qed.
Lemma map_disjoint_of_list_zip_r {A} (m : M A) is xs :
  is `same_length` xs →
  m ⊥ map_of_list (zip is xs) ↔ Forall (λ i, m !! i = None) is.
Proof.
  intro. by rewrite (symmetry_iff (⊥)), map_disjoint_of_list_zip_l.
Qed.
Lemma map_disjoint_of_list_zip_l_2 {A} (m : M A) is xs :
  is `same_length` xs → Forall (λ i, m !! i = None) is →
  map_of_list (zip is xs) ⊥ m.
Proof. intro. by rewrite map_disjoint_of_list_zip_l. Qed.
Lemma map_disjoint_of_list_zip_r_2 {A} (m : M A) is xs :
  is `same_length` xs → Forall (λ i, m !! i = None) is →
  m ⊥ map_of_list (zip is xs).
Proof. intro. by rewrite map_disjoint_of_list_zip_r. Qed.

(** ** Properties with respect to vectors *)
Lemma union_delete_vec {A n} (ms : vec (M A) n) (i : fin n) :
  ⊥ ms → ms !!! i ∪ ⋃ delete (fin_to_nat i) (vec_to_list ms) = ⋃ ms.
Proof.
  induction ms as [|m ? ms]; inversion_clear 1;
    inv_fin i; simpl; [done | intros i].
  rewrite (map_union_commutative m), (associative_L (∪)), IHms.
  * by rewrite map_union_commutative.
  * done.
  * apply map_disjoint_weaken_r with (⋃ ms); [done |].
    apply map_union_sublist; auto using sublist_delete.
Qed.

Lemma union_insert_vec {A n} (ms : vec (M A) n) (i : fin n) m :
  m ⊥ ⋃ delete (fin_to_nat i) (vec_to_list ms) →
  ⋃ vinsert i m ms = m ∪ ⋃ delete (fin_to_nat i) (vec_to_list ms).
Proof.
  induction ms as [|m' ? ms IH]; inv_fin i; simpl; [done | intros i Hdisjoint].
  rewrite map_disjoint_union_r in Hdisjoint.
  rewrite IH, !(associative_L (∪)), (map_union_commutative m); intuition.
Qed.

(** ** Properties of the [difference_with] operation *)
Section difference_with.
Context {A} (f : A → A → option A).

Lemma lookup_difference_with m1 m2 i z :
  difference_with f m1 m2 !! i = z ↔
    (m1 !! i = None ∧ z = None) ∨
    (∃ x, m1 !! i = Some x ∧ m2 !! i = None ∧ z = Some x) ∨
    (∃ x y, m1 !! i = Some x ∧ m2 !! i = Some y ∧ z = f x y).
Proof.
  unfold difference_with, map_difference_with. rewrite (lookup_merge _).
  destruct (m1 !! i), (m2 !! i); compute; naive_solver.
Qed.
Lemma lookup_difference_with_Some m1 m2 i z :
  difference_with f m1 m2 !! i = Some z ↔
    (m1 !! i = Some z ∧ m2 !! i = None) ∨
    (∃ x y, m1 !! i = Some x ∧ m2 !! i = Some y ∧ f x y = Some z).
Proof. rewrite lookup_difference_with. naive_solver. Qed.
Lemma lookup_difference_with_None m1 m2 i :
  difference_with f m1 m2 !! i = None ↔
    (m1 !! i = None) ∨
    (∃ x y, m1 !! i = Some x ∧ m2 !! i = Some y ∧ f x y = None).
Proof. rewrite lookup_difference_with. naive_solver. Qed.

Lemma lookup_difference_with_Some_lr m1 m2 i x y z :
  m1 !! i = Some x → m2 !! i = Some y → f x y = Some z →
  difference_with f m1 m2 !! i = Some z.
Proof. rewrite lookup_difference_with. naive_solver. Qed.
Lemma lookup_difference_with_None_lr m1 m2 i x y :
  m1 !! i = Some x → m2 !! i = Some y → f x y = None →
  difference_with f m1 m2 !! i = None.
Proof. rewrite lookup_difference_with. naive_solver. Qed.
Lemma lookup_difference_with_Some_l m1 m2 i x :
  m1 !! i = Some x → m2 !! i = None → difference_with f m1 m2 !! i = Some x.
Proof. rewrite lookup_difference_with. naive_solver. Qed.
End difference_with.

(** ** Properties of the [difference] operation *)
Lemma lookup_difference_Some {A} (m1 m2 : M A) i x :
  (m1 ∖ m2) !! i = Some x ↔ m1 !! i = Some x ∧ m2 !! i = None.
Proof.
  unfold difference, map_difference, difference_with, map_difference_with.
  rewrite (lookup_merge _).
  destruct (m1 !! i), (m2 !! i); compute; intuition congruence.
Qed.

Lemma map_disjoint_difference_l {A} (m1 m2 : M A) : m1 ⊆ m2 → m2 ∖ m1 ⊥ m1.
Proof.
  intros E i. specialize (E i). unfold difference, map_difference. intros x1 x2.
  rewrite lookup_difference_with_Some. intros [?| (?&?&?&?&?)] ?.
  * specialize (E x2). intuition congruence.
  * done.
Qed.
Lemma map_disjoint_difference_r {A} (m1 m2 : M A) : m1 ⊆ m2 → m1 ⊥ m2 ∖ m1.
Proof. intros. symmetry. by apply map_disjoint_difference_l. Qed.

Lemma map_difference_union {A} (m1 m2 : M A) :
  m1 ⊆ m2 → m1 ∪ m2 ∖ m1 = m2.
Proof.
  intro Hm1m2. apply map_eq. intros i.
  apply option_eq. intros v. specialize (Hm1m2 i).
  unfold difference, map_difference, difference_with, map_difference_with.
  rewrite lookup_union_Some_raw, (lookup_merge _).
  destruct (m1 !! i) as [v'|], (m2 !! i);
    try specialize (Hm1m2 v'); compute; intuition congruence.
Qed.
End theorems.

(** * Tactics *)
(** The tactic [decompose_map_disjoint] simplifies occurrences of [disjoint]
in the hypotheses that involve the empty map [∅], the union [(∪)] or insert
[<[_:=_]>] operation, the singleton [{[ _ ]}] map, and disjointness of lists of
maps. This tactic does not yield any information loss as all simplifications
performed are reversible. *)
Ltac decompose_map_disjoint := repeat
  match goal with
  | H : _ ∪ _ ⊥ _ |- _ => apply map_disjoint_union_l in H; destruct H
  | H : _ ⊥ _ ∪ _ |- _ => apply map_disjoint_union_r in H; destruct H
  | H : {[ _ ]} ⊥ _ |- _ => apply map_disjoint_singleton_l in H
  | H : _ ⊥ {[ _ ]} |- _ =>  apply map_disjoint_singleton_r in H
  | H : <[_:=_]>_ ⊥ _ |- _ => apply map_disjoint_insert_l in H; destruct H
  | H : _ ⊥ <[_:=_]>_ |- _ => apply map_disjoint_insert_r in H; destruct H
  | H : ⋃ _ ⊥ _ |- _ => apply map_disjoint_union_list_l in H
  | H : _ ⊥ ⋃ _ |- _ => apply map_disjoint_union_list_r in H
  | H : ∅ ⊥ _ |- _ => clear H
  | H : _ ⊥ ∅ |- _ => clear H
  | H : ⊥ [] |- _ => clear H
  | H : ⊥ [_] |- _ => clear H
  | H : ⊥ (_ :: _) |- _ => apply disjoint_list_cons in H; destruct H
  | H : Forall (.⊥ _) _ |- _ => rewrite Forall_vlookup in H
  | H : Forall (.⊥ _) [] |- _ => clear H
  | H : Forall (.⊥ _) (_ :: _) |- _ => rewrite Forall_cons in H; destruct H
  | H : Forall (.⊥ _) (_ :: _) |- _ => rewrite Forall_app in H; destruct H
  end.

(** To prove a disjointness property, we first decompose all hypotheses, and
then use an auto database to prove the required property. *)
Create HintDb map_disjoint.
Ltac solve_map_disjoint :=
  solve [decompose_map_disjoint; auto with map_disjoint].

(** We declare these hints using [Hint Extern] instead of [Hint Resolve] as
[eauto] works badly with hints parametrized by type class constraints. *)
Hint Extern 1 (_ ⊥ _) => done : map_disjoint.
Hint Extern 2 (∅ ⊥ _) => apply map_disjoint_empty_l : map_disjoint.
Hint Extern 2 (_ ⊥ ∅) => apply map_disjoint_empty_r : map_disjoint.
Hint Extern 2 ({[ _ ]} ⊥ _) =>
  apply map_disjoint_singleton_l_2 : map_disjoint.
Hint Extern 2 (_ ⊥ {[ _ ]}) =>
  apply map_disjoint_singleton_r_2 : map_disjoint.
Hint Extern 2 (⊥ []) => apply disjoint_nil_2 : map_disjoint.
Hint Extern 2 (⊥ (_ :: _)) => apply disjoint_cons_2 : map_disjoint.
Hint Extern 2 (_ ∪ _ ⊥ _) => apply map_disjoint_union_l_2 : map_disjoint.
Hint Extern 2 (_ ⊥ _ ∪ _) => apply map_disjoint_union_r_2 : map_disjoint.
Hint Extern 2 (<[_:=_]>_ ⊥ _) => apply map_disjoint_insert_l_2 : map_disjoint.
Hint Extern 2 (_ ⊥ <[_:=_]>_) => apply map_disjoint_insert_r_2 : map_disjoint.
Hint Extern 2 (delete _ _ ⊥ _) => apply map_disjoint_delete_l : map_disjoint.
Hint Extern 2 (_ ⊥ delete _ _) => apply map_disjoint_delete_r : map_disjoint.
Hint Extern 2 (map_of_list _ ⊥ _) =>
  apply map_disjoint_of_list_zip_l_2 : mem_disjoint.
Hint Extern 2 (_ ⊥ map_of_list _) =>
  apply map_disjoint_of_list_zip_r_2 : mem_disjoint.
Hint Extern 2 (⋃ _ ⊥ _) => apply map_disjoint_union_list_l_2 : mem_disjoint.
Hint Extern 2 (_ ⊥ ⋃ _) => apply map_disjoint_union_list_r_2 : mem_disjoint.
Hint Extern 2 (delete_list _ _ ⊥ _) =>
  apply map_disjoint_delete_list_l : map_disjoint.
Hint Extern 2 (_ ⊥ delete_list _ _) =>
  apply map_disjoint_delete_list_r : map_disjoint.

(** The tactic [simpl_map by tac] simplifies occurrences of finite map look
ups. It uses [tac] to discharge generated inequalities. Look ups in unions do
not have nice equational properties, hence it invokes [tac] to prove that such
look ups yield [Some]. *)
Tactic Notation "simpl_map" "by" tactic3(tac) := repeat
  match goal with
  | H : context[ ∅ !! _ ] |- _ => rewrite lookup_empty in H
  | H : context[ (<[_:=_]>_) !! _ ] |- _ => rewrite lookup_insert in H
  | H : context[ (<[_:=_]>_) !! _ ] |- _ =>
   rewrite lookup_insert_ne in H by tac
  | H : context[ (delete _ _) !! _] |- _ => rewrite lookup_delete in H
  | H : context[ (delete _ _) !! _] |- _ =>
    rewrite lookup_delete_ne in H by tac
  | H : context[ {[ _ ]} !! _ ] |- _ => rewrite lookup_singleton in H
  | H : context[ {[ _ ]} !! _ ] |- _ =>
    rewrite lookup_singleton_ne in H by tac
  | H : context[ lookup (A:=?A) ?i (?m1 ∪ ?m2) ] |- _ =>
    let x := fresh in evar (x:A);
    let x' := eval unfold x in x in clear x;
    let E := fresh in
    assert ((m1 ∪ m2) !! i = Some x') as E by (clear H; by tac);
    rewrite E in H; clear E
  | |- context[ ∅ !! _ ] => rewrite lookup_empty
  | |- context[ (<[_:=_]>_) !! _ ] => rewrite lookup_insert
  | |- context[ (<[_:=_]>_) !! _ ] => rewrite lookup_insert_ne by tac
  | |- context[ (delete _ _) !! _ ] => rewrite lookup_delete
  | |- context[ (delete _ _) !! _ ] => rewrite lookup_delete_ne by tac
  | |- context[ {[ _ ]} !! _ ] => rewrite lookup_singleton
  | |- context[ {[ _ ]} !! _ ] => rewrite lookup_singleton_ne by tac
  | |- context [ lookup (A:=?A) ?i ?m ] =>
    let x := fresh in evar (x:A);
    let x' := eval unfold x in x in clear x;
    let E := fresh in
    assert (m !! i = Some x') as E by tac;
    rewrite E; clear E
  end.

Create HintDb simpl_map.
Tactic Notation "simpl_map" := simpl_map by eauto with simpl_map map_disjoint.

Hint Extern 80 ((_ ∪ _) !! _ = Some _) => apply lookup_union_Some_l : simpl_map.
Hint Extern 81 ((_ ∪ _) !! _ = Some _) => apply lookup_union_Some_r : simpl_map.
Hint Extern 80 ({[ _ ]} !! _ = Some _) => apply lookup_singleton : simpl_map.
Hint Extern 80 (<[_:=_]> _ !! _ = Some _) => apply lookup_insert : simpl_map.

(** Now we take everything together and also discharge conflicting look ups,
simplify overlapping look ups, and perform cancellations of equalities
involving unions. *)
Tactic Notation "simplify_map_equality" "by" tactic3(tac) :=
  decompose_map_disjoint;
  repeat
  match goal with
  | _ => progress simpl_map by tac
  | _ => progress simplify_equality
  | H : {[ _ ]} !! _ = None |- _ => rewrite lookup_singleton_None in H
  | H : {[ _ ]} !! _ = Some _ |- _ =>
    rewrite lookup_singleton_Some in H; destruct H
  | H1 : ?m1 !! ?i = Some ?x, H2 : ?m2 !! ?i = Some ?y |- _ =>
    let H3 := fresh in
    feed pose proof (lookup_weaken_inv m1 m2 i x y) as H3;
      [done | by tac | done | ];
    clear H2; symmetry in H3
  | H1 : ?m1 !! ?i = Some ?x, H2 : ?m2 !! ?i = None |- _ =>
    let H3 := fresh in
    assert (m1 ⊆ m2) as H3 by tac;
    apply H3 in H1; congruence
  | H : ?m ∪ _ = ?m ∪ _ |- _ =>
    apply map_union_cancel_l in H; [| solve[tac] | solve [tac]]
  | H : _ ∪ ?m = _ ∪ ?m |- _ =>
    apply map_union_cancel_r in H; [| solve[tac] | solve [tac]]
  end.
Tactic Notation "simplify_map_equality" :=
  simplify_map_equality by eauto with simpl_map map_disjoint.
