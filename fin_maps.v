(* Copyright (c) 2012, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** Finite maps associate data to keys. This file defines an interface for
finite maps and collects some theory on it. Most importantly, it proves useful
induction principles for finite maps and implements the tactic [simplify_map]
to simplify goals involving finite maps. *)
Require Import Permutation.
Require Export prelude.
(** * Axiomatization of finite maps *)
(** We require Leibniz equality to be extensional on finite maps. This of
course limits the space of finite map implementations, but since we are mainly
interested in finite maps with numbers as indexes, we do not consider this to
be a serious limitation. The main application of finite maps is to implement
the memory, where extensionality of Leibniz equality is very important for a
convenient use in the assertions of our axiomatic semantics. *)

(** Finiteness is axiomatized by requiring that each map can be translated
to an association list. The translation to association lists is used to
implement the [dom] function, and for well founded recursion on finite maps. *)

(** Finite map implementations are required to implement the [merge] function
which enables us to give a generic implementation of [union_with],
[intersection_with], and [difference_with]. *)

Class FinMapToList K A M := finmap_to_list: M → list (K * A).

Class FinMap K M `{!FMap M}
    `{∀ A, Lookup K A (M A)}
    `{∀ A, Empty (M A)}
    `{∀ A, PartialAlter K A (M A)}
    `{∀ A, Merge A (M A)}
    `{∀ A, FinMapToList K A (M A)}
    `{∀ i j : K, Decision (i = j)} := {
  finmap_eq {A} (m1 m2 : M A) :
    (∀ i, m1 !! i = m2 !! i) → m1 = m2;
  lookup_empty {A} i :
    (∅ : M A) !! i = None;
  lookup_partial_alter {A} f (m : M A) i :
    partial_alter f i m !! i = f (m !! i);
  lookup_partial_alter_ne {A} f (m : M A) i j :
    i ≠ j → partial_alter f i m !! j = m !! j;
  lookup_fmap {A B} (f : A → B) (m : M A) i :
    (f <$> m) !! i = f <$> m !! i;
  finmap_to_list_nodup {A} (m : M A) :
    NoDup (finmap_to_list m);
  elem_of_finmap_to_list {A} (m : M A) i x :
    (i,x) ∈ finmap_to_list m ↔ m !! i = Some x;
  merge_spec {A} f `{!PropHolds (f None None = None)}
    (m1 m2 : M A) i : merge f m1 m2 !! i = f (m1 !! i) (m2 !! i)
}.

(** * Derived operations *)
(** All of the following functions are defined in a generic way for arbitrary
finite map implementations. These generic implementations do not cause a
significant performance loss to make including them in the finite map interface
worthwhile. *)
Instance finmap_insert `{PartialAlter K A M} : Insert K A M := λ i x,
  partial_alter (λ _, Some x) i.
Instance finmap_alter `{PartialAlter K A M} : Alter K A M := λ f,
  partial_alter (fmap f).
Instance finmap_delete `{PartialAlter K A M} : Delete K M :=
  partial_alter (λ _, None).
Instance finmap_singleton `{PartialAlter K A M}
  `{Empty M} : Singleton (K * A) M := λ p, <[fst p:=snd p]>∅.

Definition finmap_of_list `{Insert K A M} `{Empty M}
  (l : list (K * A)) : M := insert_list l ∅.
Instance finmap_dom `{FinMapToList K A M} : Dom K M := λ C _ _ _,
  foldr ((∪) ∘ singleton ∘ fst) ∅ ∘ finmap_to_list.

Instance finmap_union_with `{Merge A M} : UnionWith A M := λ f,
  merge (union_with f).
Instance finmap_intersection_with `{Merge A M} : IntersectionWith A M := λ f,
  merge (intersection_with f).
Instance finmap_difference_with `{Merge A M} : DifferenceWith A M := λ f,
  merge (difference_with f).

(** The relation [intersection_forall R] on finite maps describes that the
relation [R] holds for each pair in the intersection. *)
Definition finmap_forall `{Lookup K A M} (P : K → A → Prop) : M → Prop :=
  λ m, ∀ i x, m !! i = Some x → P i x.
Definition finmap_intersection_forall `{Lookup K A M}
    (R : relation A) : relation M := λ m1 m2,
  ∀ i x1 x2, m1 !! i = Some x1 → m2 !! i = Some x2 → R x1 x2.
Instance finmap_disjoint `{∀ A, Lookup K A (M A)} : Disjoint (M A) := λ A,
  finmap_intersection_forall (λ _ _, False).

(** The union of two finite maps only has a meaningful definition for maps
that are disjoint. However, as working with partial functions is inconvenient
in Coq, we define the union as a total function. In case both finite maps
have a value at the same index, we take the value of the first map. *)
Instance finmap_union `{Merge A M} : Union M :=
  union_with (λ x _, Some x).
Instance finmap_intersection `{Merge A M} : Intersection M :=
  union_with (λ x _, Some x).
(** The difference operation removes all values from the first map whose
index contains a value in the second map as well. *)
Instance finmap_difference `{Merge A M} : Difference M :=
  difference_with (λ _ _, None).

(** * General theorems *)
Section finmap_common.
  Context `{FinMap K M} {A : Type}.

  Global Instance finmap_subseteq: SubsetEq (M A) := λ m n,
    ∀ i x, m !! i = Some x → n !! i = Some x.
  Global Instance: BoundedPreOrder (M A).
  Proof. split; [firstorder |]. intros m i x. by rewrite lookup_empty. Qed.

  Lemma lookup_weaken (m1 m2 : M A) i x :
    m1 !! i = Some x → m1 ⊆ m2 → m2 !! i = Some x.
  Proof. auto. Qed.
  Lemma lookup_weaken_is_Some (m1 m2 : M A) i :
    is_Some (m1 !! i) → m1 ⊆ m2 → is_Some (m2 !! i).
  Proof. inversion 1. eauto using lookup_weaken. Qed.
  Lemma lookup_weaken_None (m1 m2 : M A) i :
    m2 !! i = None → m1 ⊆ m2 → m1 !! i = None.
  Proof.
    rewrite eq_None_not_Some. intros Hm2 Hm1m2.
    specialize (Hm1m2 i). destruct (m1 !! i); naive_solver.
  Qed.

  Lemma lookup_weaken_inv (m1 m2 : M A) i x y :
    m1 !! i = Some x →
    m1 ⊆ m2 →
    m2 !! i = Some y →
    x = y.
  Proof.
    intros Hm1 ? Hm2. eapply lookup_weaken in Hm1; eauto.
    congruence.
  Qed.

  Lemma lookup_ne (m : M A) i j : m !! i ≠ m !! j → i ≠ j.
  Proof. congruence. Qed.
  Lemma finmap_empty (m : M A) : (∀ i, m !! i = None) → m = ∅.
  Proof. intros Hm. apply finmap_eq. intros. by rewrite Hm, lookup_empty. Qed.
  Lemma lookup_empty_is_Some i : ¬is_Some ((∅ : M A) !! i).
  Proof. rewrite lookup_empty. by inversion 1. Qed.
  Lemma lookup_empty_Some i (x : A) : ¬∅ !! i = Some x.
  Proof. by rewrite lookup_empty. Qed.

  Lemma partial_alter_compose (m : M A) i f g :
    partial_alter (f ∘ g) i m = partial_alter f i (partial_alter g i m).
  Proof.
    intros. apply finmap_eq. intros ii. case (decide (i = ii)).
    * intros. subst. by rewrite !lookup_partial_alter.
    * intros. by rewrite !lookup_partial_alter_ne.
  Qed.
  Lemma partial_alter_comm (m : M A) i j f g :
    i ≠ j →
    partial_alter f i (partial_alter g j m) =
      partial_alter g j (partial_alter f i m).
  Proof.
    intros. apply finmap_eq. intros jj.
    destruct (decide (jj = j)).
    * subst. by rewrite lookup_partial_alter_ne,
       !lookup_partial_alter, lookup_partial_alter_ne.
    * destruct (decide (jj = i)).
      + subst. by rewrite lookup_partial_alter,
         !lookup_partial_alter_ne, lookup_partial_alter by congruence.
      + by rewrite !lookup_partial_alter_ne by congruence.
  Qed.
  Lemma partial_alter_self_alt (m : M A) i x :
    x = m !! i → partial_alter (λ _, x) i m = m.
  Proof.
    intros. apply finmap_eq. intros ii.
    destruct (decide (i = ii)).
    * subst. by rewrite lookup_partial_alter.
    * by rewrite lookup_partial_alter_ne.
  Qed.
  Lemma partial_alter_self (m : M A) i : partial_alter (λ _, m !! i) i m = m.
  Proof. by apply partial_alter_self_alt. Qed.

  Lemma lookup_insert (m : M A) i x : <[i:=x]>m !! i = Some x.
  Proof. unfold insert. apply lookup_partial_alter. Qed.
  Lemma lookup_insert_rev (m : M A) i x y : <[i:= x ]>m !! i = Some y → x = y.
  Proof. rewrite lookup_insert. congruence. Qed.
  Lemma lookup_insert_ne (m : M A) i j x : i ≠ j → <[i:=x]>m !! j = m !! j.
  Proof. unfold insert. apply lookup_partial_alter_ne. Qed.
  Lemma insert_comm (m : M A) i j x y :
    i ≠ j → <[i:=x]>(<[j:=y]>m) = <[j:=y]>(<[i:=x]>m).
  Proof. apply partial_alter_comm. Qed.

  Lemma lookup_insert_Some (m : M A) i j x y :
    <[i:=x]>m !! j = Some y ↔ (i = j ∧ x = y) ∨ (i ≠ j ∧ m !! j = Some y).
  Proof.
    split.
    * destruct (decide (i = j)); subst;
        rewrite ?lookup_insert, ?lookup_insert_ne; intuition congruence.
    * intros [[??]|[??]].
      + subst. apply lookup_insert.
      + by rewrite lookup_insert_ne.
  Qed.
  Lemma lookup_insert_None (m : M A) i j x :
    <[i:=x]>m !! j = None ↔ m !! j = None ∧ i ≠ j.
  Proof.
    split.
    * destruct (decide (i = j)); subst;
        rewrite ?lookup_insert, ?lookup_insert_ne; intuition congruence.
    * intros [??]. by rewrite lookup_insert_ne.
  Qed.

  Lemma lookup_singleton_Some i j (x y : A) :
    {[(i, x)]} !! j = Some y ↔ i = j ∧ x = y.
  Proof.
    unfold singleton, finmap_singleton.
    rewrite lookup_insert_Some, lookup_empty. simpl.
    intuition congruence.
  Qed.
  Lemma lookup_singleton_None i j (x : A) :
    {[(i, x)]} !! j = None ↔ i ≠ j.
  Proof.
    unfold singleton, finmap_singleton.
    rewrite lookup_insert_None, lookup_empty. simpl. tauto.
  Qed.
  Lemma insert_singleton i (x y : A) : <[i:=y]>{[(i, x)]} = {[(i, y)]}.
  Proof.
    unfold singleton, finmap_singleton, insert, finmap_insert.
    by rewrite <-partial_alter_compose.
  Qed.

  Lemma lookup_singleton i (x : A) : {[(i, x)]} !! i = Some x.
  Proof. by rewrite lookup_singleton_Some. Qed.
  Lemma lookup_singleton_ne i j (x : A) : i ≠ j → {[(i, x)]} !! j = None.
  Proof. by rewrite lookup_singleton_None. Qed.

  Lemma lookup_delete (m : M A) i : delete i m !! i = None.
  Proof. apply lookup_partial_alter. Qed.
  Lemma lookup_delete_ne (m : M A) i j : i ≠ j → delete i m !! j = m !! j.
  Proof. apply lookup_partial_alter_ne. Qed.

  Lemma lookup_delete_Some (m : M A) i j y :
    delete i m !! j = Some y ↔ i ≠ j ∧ m !! j = Some y.
  Proof.
    split.
    * destruct (decide (i = j)); subst;
        rewrite ?lookup_delete, ?lookup_delete_ne; intuition congruence.
    * intros [??]. by rewrite lookup_delete_ne.
  Qed.
  Lemma lookup_delete_None (m : M A) i j :
    delete i m !! j = None ↔ i = j ∨ m !! j = None.
  Proof.
    destruct (decide (i = j)).
    * subst. rewrite lookup_delete. tauto.
    * rewrite lookup_delete_ne; tauto.
  Qed.

  Lemma delete_empty i : delete i (∅ : M A) = ∅.
  Proof. rewrite <-(partial_alter_self ∅) at 2. by rewrite lookup_empty. Qed.
  Lemma delete_singleton i (x : A) : delete i {[(i, x)]} = ∅.
  Proof. setoid_rewrite <-partial_alter_compose. apply delete_empty. Qed.
  Lemma delete_comm (m : M A) i j :
    delete i (delete j m) = delete j (delete i m).
  Proof. destruct (decide (i = j)). by subst. by apply partial_alter_comm. Qed.
  Lemma delete_insert_comm (m : M A) i j x :
    i ≠ j → delete i (<[j:=x]>m) = <[j:=x]>(delete i m).
  Proof. intro. by apply partial_alter_comm. Qed.

  Lemma delete_notin (m : M A) i :
    m !! i = None → delete i m = m.
  Proof.
    intros. apply finmap_eq. intros j.
    destruct (decide (i = j)).
    * subst. by rewrite lookup_delete.
    * by apply lookup_delete_ne.
  Qed.

  Lemma delete_partial_alter (m : M A) i f :
    m !! i = None → delete i (partial_alter f i m) = m.
  Proof.
    intros. unfold delete, finmap_delete. rewrite <-partial_alter_compose.
    rapply partial_alter_self_alt. congruence.
  Qed.
  Lemma delete_insert (m : M A) i x :
    m !! i = None → delete i (<[i:=x]>m) = m.
  Proof. apply delete_partial_alter. Qed.
  Lemma insert_delete (m : M A) i x :
    m !! i = Some x → <[i:=x]>(delete i m) = m.
  Proof.
    intros Hmi. unfold delete, finmap_delete, insert, finmap_insert.
    rewrite <-partial_alter_compose. unfold compose. rewrite <-Hmi.
    by apply partial_alter_self_alt.
  Qed.

  Lemma lookup_delete_list (m : M A) is j :
    j ∈ is → delete_list is m !! j = None.
  Proof.
    induction 1 as [|i j is]; simpl.
    * by rewrite lookup_delete.
    * destruct (decide (i = j)).
      + subst. by rewrite lookup_delete.
      + rewrite lookup_delete_ne; auto.
  Qed.
  Lemma lookup_delete_list_not_elem_of (m : M A) is j :
    j ∉ is → delete_list is m !! j = m !! j.
  Proof.
    induction is; simpl; [done |].
    rewrite elem_of_cons. intros.
    intros. rewrite lookup_delete_ne; intuition.
  Qed.
  Lemma delete_list_notin (m : M A) is :
    Forall (λ i, m !! i = None) is → delete_list is m = m.
  Proof.
    induction 1; simpl; [done |].
    rewrite delete_notin; congruence.
  Qed.

  Lemma delete_list_insert_comm (m : M A) is j x :
    j ∉ is → delete_list is (<[j:=x]>m) = <[j:=x]>(delete_list is m).
  Proof.
    induction is; simpl; [done |].
    rewrite elem_of_cons. intros.
    rewrite IHis, delete_insert_comm; intuition.
  Qed.

  Lemma elem_of_dom C `{SimpleCollection K C} (m : M A) i :
    i ∈ dom C m ↔ is_Some (m !! i).
  Proof.
    unfold dom, finmap_dom. simpl. rewrite is_Some_alt.
    setoid_rewrite <-elem_of_finmap_to_list.
    induction (finmap_to_list m) as [|[j x] l IH]; simpl.
    * rewrite elem_of_empty.
      setoid_rewrite elem_of_nil. naive_solver.
    * rewrite elem_of_union, elem_of_singleton.
      setoid_rewrite elem_of_cons. naive_solver.
  Qed.
  Lemma not_elem_of_dom C `{SimpleCollection K C} (m : M A) i :
    i ∉ dom C m ↔ m !! i = None.
  Proof. by rewrite (elem_of_dom C), eq_None_not_Some. Qed.

  Lemma dom_empty C `{SimpleCollection K C} : dom C (∅ : M A) ≡ ∅.
  Proof.
    split; intro.
    * rewrite (elem_of_dom C), lookup_empty. by inversion 1.
    * solve_elem_of.
  Qed.
  Lemma dom_empty_inv C `{SimpleCollection K C} (m : M A) :
    dom C m ≡ ∅ → m = ∅.
  Proof.
    intros E. apply finmap_empty. intros. apply (not_elem_of_dom C).
    rewrite E. solve_elem_of.
  Qed.

  Lemma delete_partial_alter_dom C `{SimpleCollection K C} (m : M A) i f :
    i ∉ dom C m → delete i (partial_alter f i m) = m.
  Proof. rewrite (not_elem_of_dom C). apply delete_partial_alter. Qed.
  Lemma delete_insert_dom C `{SimpleCollection K C} (m : M A) i x :
    i ∉ dom C m → delete i (<[i:=x]>m) = m.
  Proof. rewrite (not_elem_of_dom C). apply delete_partial_alter. Qed.
  Lemma elem_of_dom_delete C `{SimpleCollection K C} (m : M A) i j :
    i ∈ dom C (delete j m) ↔ i ≠ j ∧ i ∈ dom C m.
  Proof.
    rewrite !(elem_of_dom C), <-!not_eq_None_Some.
    rewrite lookup_delete_None. intuition.
  Qed.
  Lemma not_elem_of_dom_delete C `{SimpleCollection K C} (m : M A) i :
    i ∉ dom C (delete i m).
  Proof. apply (not_elem_of_dom C), lookup_delete. Qed.

  Lemma subseteq_dom C `{SimpleCollection K C} (m1 m2 : M A) :
    m1 ⊆ m2 → dom C m1 ⊆ dom C m2.
  Proof.
    unfold subseteq, finmap_subseteq, collection_subseteq.
    intros ??. rewrite !(elem_of_dom C). inversion 1. eauto.
  Qed.
  Lemma subset_dom C `{SimpleCollection K C} (m1 m2 : M A) :
    m1 ⊂ m2 → dom C m1 ⊂ dom C m2.
  Proof.
    intros [Hss1 Hss2]. split.
    * by apply subseteq_dom.
    * intros Hdom. destruct Hss2. intros i x Hi.
      specialize (Hdom i). rewrite !(elem_of_dom C) in Hdom.
      feed inversion Hdom. eauto.
      by erewrite (Hss1 i) in Hi by eauto.
  Qed.
  Lemma finmap_wf : wf (@subset (M A) _).
  Proof.
    apply (wf_projected (⊂) (dom (listset K))).
    * by apply (subset_dom _).
    * by apply collection_wf.
  Qed.

  Lemma partial_alter_subseteq (m : M A) i f :
    m !! i = None →
    m ⊆ partial_alter f i m.
  Proof.
    intros Hi j x Hj. rewrite lookup_partial_alter_ne; congruence.
  Qed.
  Lemma partial_alter_subset (m : M A) i f :
    m !! i = None →
    is_Some (f (m !! i)) →
    m ⊂ partial_alter f i m.
  Proof.
    intros Hi Hfi. split.
    * by apply partial_alter_subseteq.
    * inversion Hfi as [x Hx]. intros Hm.
      apply (Some_ne_None x). rewrite <-(Hm i x); [done|].
      by rewrite lookup_partial_alter.
  Qed.
  Lemma insert_subseteq (m : M A) i x :
    m !! i = None →
    m ⊆ <[i:=x]>m.
  Proof. apply partial_alter_subseteq. Qed.
  Lemma insert_subset (m : M A) i x :
    m !! i = None →
    m ⊂ <[i:=x]>m.
  Proof. intro. apply partial_alter_subset; eauto. Qed.

  Lemma delete_subseteq (m : M A) i :
    delete i m ⊆ m.
  Proof. intros j x. rewrite lookup_delete_Some. tauto. Qed.
  Lemma delete_subseteq_compat (m1 m2 : M A) i :
    m1 ⊆ m2 →
    delete i m1 ⊆ delete i m2.
  Proof. intros ? j x. rewrite !lookup_delete_Some. intuition eauto. Qed.
  Lemma delete_subset_alt (m : M A) i x :
    m !! i = Some x → delete i m ⊂ m.
  Proof.
    split.
    * apply delete_subseteq.
    * intros Hi. apply (None_ne_Some x).
      by rewrite <-(lookup_delete m i), (Hi i x).
  Qed.
  Lemma delete_subset (m : M A) i :
    is_Some (m !! i) → delete i m ⊂ m.
  Proof. inversion 1. eauto using delete_subset_alt. Qed.

  (** * Induction principles *)
  (** We use the induction principle on finite collections to prove the
  following induction principle on finite maps. *)
  Lemma finmap_ind_alt C (P : M A → Prop) `{FinCollection K C} :
    P ∅ →
    (∀ i x m, i ∉ dom C m → P m → P (<[i:=x]>m)) →
    ∀ m, P m.
  Proof.
    intros Hemp Hinsert m.
    apply (collection_ind (λ X, ∀ m, dom C m ≡ X → P m)) with (dom C m).
    * solve_proper.
    * clear m. intros m Hm. rewrite finmap_empty.
      + done.
      + intros. rewrite <-(not_elem_of_dom C), Hm.
        by solve_elem_of.
    * clear m. intros i X Hi IH m Hdom.
      assert (∃ x, m !! i = Some x) as [x ?].
      { apply is_Some_alt, (elem_of_dom C).
        rewrite Hdom. clear Hdom.
        by solve_elem_of. }
      rewrite <-(insert_delete m i x) by done.
      apply Hinsert.
      { by apply (not_elem_of_dom_delete C). }
      apply IH. apply elem_of_equiv. intros.
      rewrite (elem_of_dom_delete C).
      esolve_elem_of.
    * done.
  Qed.

  (** We use the [listset] implementation to prove an induction principle that
  does not use the map's domain. *)
  Lemma finmap_ind (P : M A → Prop) :
    P ∅ →
    (∀ i x m, m !! i = None → P m → P (<[i:=x]>m)) →
    ∀ m, P m.
  Proof.
    setoid_rewrite <-(not_elem_of_dom (listset _)).
    apply (finmap_ind_alt (listset _) P).
  Qed.
End finmap_common.

(** * The finite map tactic *)
(** The tactic [simplify_map by tac] simplifies finite map expressions
occuring in the conclusion and hypotheses. It uses [tac] to discharge generated
inequalities. *)
Tactic Notation "simpl_map" "by" tactic3(tac) := repeat
  match goal with
  | H : context[ ∅ !! _ ] |- _ => rewrite lookup_empty in H
  | H : context[ (<[_:=_]>_) !! _ ] |- _ => rewrite lookup_insert in H
  | H : context[ (<[_:=_]>_) !! _ ] |- _ => rewrite lookup_insert_ne in H by tac
  | H : context[ (delete _ _) !! _] |- _ => rewrite lookup_delete in H
  | H : context[ (delete _ _) !! _] |- _ => rewrite lookup_delete_ne in H by tac
  | H : context[ {[ _ ]} !! _ ] |- _ => rewrite lookup_singleton in H
  | H : context[ {[ _ ]} !! _ ] |- _ => rewrite lookup_singleton_ne in H by tac
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
Tactic Notation "simpl_map" := simpl_map by eauto with simpl_map.
Tactic Notation "simplify_map_equality" "by" tactic3(tac) := repeat
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
  end.
Tactic Notation "simplify_map_equality" :=
  simplify_map_equality by eauto with simpl_map.

(** * More theorems on finite maps *)
Section finmap_more.
  Context `{FinMap K M} {A : Type}.

  (** ** Properties of conversion to lists *)
  Lemma finmap_to_list_unique (m : M A) i x y :
    (i,x) ∈ finmap_to_list m →
    (i,y) ∈ finmap_to_list m →
    x = y.
  Proof. rewrite !elem_of_finmap_to_list. congruence. Qed.
  Lemma finmap_to_list_key_nodup (m : M A) :
    NoDup (fst <$> finmap_to_list m).
  Proof.
    eauto using NoDup_fmap_fst, finmap_to_list_unique, finmap_to_list_nodup.
  Qed.

  Lemma elem_of_finmap_of_list_1 (l : list (K * A)) i x :
    NoDup (fst <$> l) → (i,x) ∈ l → finmap_of_list l !! i = Some x.
  Proof.
    induction l as [|[j y] l IH]; simpl.
    * by rewrite elem_of_nil.
    * rewrite NoDup_cons, elem_of_cons, elem_of_list_fmap.
      intros [Hl ?] [?|?]; simplify_map_equality; [done |].
      destruct (decide (i = j)); simplify_map_equality; [|done].
      destruct Hl. by exists (j,x).
  Qed.
  Lemma elem_of_finmap_of_list_2 (l : list (K * A)) i x :
    finmap_of_list l !! i = Some x → (i,x) ∈ l.
  Proof.
    induction l as [|[j y] l IH]; simpl.
    * by rewrite lookup_empty.
    * rewrite elem_of_cons. destruct (decide (i = j));
        simplify_map_equality; intuition congruence.
  Qed.
  Lemma elem_of_finmap_of_list (l : list (K * A)) i x :
    NoDup (fst <$> l) →
    (i,x) ∈ l ↔ finmap_of_list l !! i = Some x.
  Proof.
    split; auto using elem_of_finmap_of_list_1, elem_of_finmap_of_list_2.
  Qed.

  Lemma not_elem_of_finmap_of_list_1 (l : list (K * A)) i :
    i ∉ fst <$> l → finmap_of_list l !! i = None.
  Proof.
    rewrite elem_of_list_fmap, eq_None_not_Some, is_Some_alt.
    intros Hi [x ?]. destruct Hi. exists (i,x). simpl.
    auto using elem_of_finmap_of_list_2.
  Qed.
  Lemma not_elem_of_finmap_of_list_2 (l : list (K * A)) i :
    finmap_of_list l !! i = None → i ∉ fst <$> l.
  Proof.
    induction l as [|[j y] l IH]; simpl.
    * rewrite elem_of_nil. tauto.
    * rewrite elem_of_cons.
      destruct (decide (i = j)); simplify_map_equality; by intuition.
  Qed.
  Lemma not_elem_of_finmap_of_list (l : list (K * A)) i :
    i ∉ fst <$> l ↔ finmap_of_list l !! i = None.
  Proof.
    split; auto using not_elem_of_finmap_of_list_1,
      not_elem_of_finmap_of_list_2.
  Qed.

  Lemma finmap_of_list_proper (l1 l2 : list (K * A)) :
    NoDup (fst <$> l1) →
    Permutation l1 l2 →
    finmap_of_list l1 = finmap_of_list l2.
  Proof.
    intros ? Hperm. apply finmap_eq. intros i. apply option_eq. intros x.
    by rewrite <-!elem_of_finmap_of_list; rewrite <-?Hperm.
  Qed.
  Lemma finmap_of_list_inj (l1 l2 : list (K * A)) :
    NoDup (fst <$> l1) →
    NoDup (fst <$> l2) →
    finmap_of_list l1 = finmap_of_list l2 →
    Permutation l1 l2.
  Proof.
    intros ?? Hl1l2.
    apply NoDup_Permutation; auto using (NoDup_fmap_1 fst).
    intros [i x]. by rewrite !elem_of_finmap_of_list, Hl1l2.
  Qed.
  Lemma finmap_of_to_list (m : M A) :
    finmap_of_list (finmap_to_list m) = m.
  Proof.
    apply finmap_eq. intros i. apply option_eq. intros x.
    by rewrite <-elem_of_finmap_of_list, elem_of_finmap_to_list
      by auto using finmap_to_list_key_nodup.
  Qed.
  Lemma finmap_to_of_list (l : list (K * A)) :
    NoDup (fst <$> l) →
    Permutation (finmap_to_list (finmap_of_list l)) l.
  Proof.
    auto using finmap_of_list_inj,
      finmap_to_list_key_nodup, finmap_of_to_list.
  Qed.
  Lemma finmap_to_list_inj (m1 m2 : M A) :
    Permutation (finmap_to_list m1) (finmap_to_list m2) →
    m1 = m2.
  Proof.
    intros.
    rewrite <-(finmap_of_to_list m1), <-(finmap_of_to_list m2).
    auto using finmap_of_list_proper, finmap_to_list_key_nodup.
  Qed.

  Lemma finmap_to_list_empty :
    finmap_to_list ∅ = @nil (K * A).
  Proof.
    apply elem_of_nil_inv. intros [i x].
    rewrite elem_of_finmap_to_list. apply lookup_empty_Some.
  Qed.
  Lemma finmap_to_list_insert (m : M A) i x :
    m !! i = None →
    Permutation (finmap_to_list (<[i:=x]>m)) ((i,x) :: finmap_to_list m).
  Proof.
    intros. apply finmap_of_list_inj; simpl.
    * apply finmap_to_list_key_nodup.
    * constructor; auto using finmap_to_list_key_nodup.
      rewrite elem_of_list_fmap.
      intros [[??] [? Hlookup]]; subst; simpl in *.
      rewrite elem_of_finmap_to_list in Hlookup. congruence.
    * by rewrite !finmap_of_to_list.
  Qed.

  Lemma finmap_of_list_nil :
    finmap_of_list (@nil (K * A)) = ∅.
  Proof. done. Qed.
  Lemma finmap_of_list_cons (l : list (K * A)) i x :
    finmap_of_list ((i, x) :: l) = <[i:=x]>(finmap_of_list l).
  Proof. done. Qed.

  Lemma finmap_to_list_empty_inv (m : M A) :
    Permutation (finmap_to_list m) [] → m = ∅.
  Proof. rewrite <-finmap_to_list_empty. apply finmap_to_list_inj. Qed.
  Lemma finmap_to_list_insert_inv (m : M A) l i x :
    Permutation (finmap_to_list m) ((i,x) :: l) →
    m = <[i:=x]>(finmap_of_list l).
  Proof.
    intros Hperm. apply finmap_to_list_inj.
    assert (NoDup (fst <$> (i, x) :: l)) as Hnodup.
    { rewrite <-Hperm. auto using finmap_to_list_key_nodup. }
    simpl in Hnodup. rewrite NoDup_cons in Hnodup.
    destruct Hnodup.
    rewrite Hperm, finmap_to_list_insert, finmap_to_of_list;
      auto using not_elem_of_finmap_of_list_1.
  Qed.

  (** ** Properties of the forall predicate *)
  Section finmap_forall.
    Context (P : K → A → Prop).

    Lemma finmap_forall_to_list m :
      finmap_forall P m ↔ Forall (curry P) (finmap_to_list m).
    Proof.
      rewrite Forall_forall. split.
      * intros Hforall [i x].
        rewrite elem_of_finmap_to_list. by apply (Hforall i x).
      * intros Hforall i x.
        rewrite <-elem_of_finmap_to_list. by apply (Hforall (i,x)).
    Qed.

    Global Instance finmap_forall_dec
      `{∀ i x, Decision (P i x)} m : Decision (finmap_forall P m).
    Proof.
      refine (cast_if (decide (Forall (curry P) (finmap_to_list m))));
        by rewrite finmap_forall_to_list.
    Defined.
  End finmap_forall.

  (** ** Properties of the merge operation *)
  Section merge_with.
    Context (f : option A → option A → option A).

    Global Instance: LeftId (=) None f → LeftId (=) ∅ (merge f).
    Proof.
      intros ??. apply finmap_eq. intros.
      by rewrite !(merge_spec f), lookup_empty, (left_id None f).
    Qed.
    Global Instance: RightId (=) None f → RightId (=) ∅ (merge f).
    Proof.
      intros ??. apply finmap_eq. intros.
      by rewrite !(merge_spec f), lookup_empty, (right_id None f).
    Qed.

    Context `{!PropHolds (f None None = None)}.

    Lemma merge_spec_alt m1 m2 m :
      (∀ i, m !! i = f (m1 !! i) (m2 !! i)) ↔ merge f m1 m2 = m.
    Proof.
      split; [| intro; subst; apply (merge_spec _) ].
      intros Hlookup. apply finmap_eq. intros. rewrite Hlookup.
      apply (merge_spec _).
    Qed.

    Lemma merge_commutative m1 m2 :
      (∀ i, f (m1 !! i) (m2 !! i) = f (m2 !! i) (m1 !! i)) →
      merge f m1 m2 = merge f m2 m1.
    Proof. intros. apply finmap_eq. intros. by rewrite !(merge_spec f). Qed.
    Global Instance: Commutative (=) f → Commutative (=) (merge f).
    Proof.
      intros ???. apply merge_commutative. intros. by apply (commutative f).
    Qed.

    Lemma merge_associative m1 m2 m3 :
      (∀ i, f (m1 !! i) (f (m2 !! i) (m3 !! i)) =
            f (f (m1 !! i) (m2 !! i)) (m3 !! i)) →
      merge f m1 (merge f m2 m3) = merge f (merge f m1 m2) m3.
    Proof. intros. apply finmap_eq. intros. by rewrite !(merge_spec f). Qed.
    Global Instance: Associative (=) f → Associative (=) (merge f).
    Proof.
      intros ????. apply merge_associative. intros. by apply (associative f).
    Qed.

    Lemma merge_idempotent m1 :
      (∀ i, f (m1 !! i) (m1 !! i) = m1 !! i) →
      merge f m1 m1 = m1.
    Proof. intros. apply finmap_eq. intros. by rewrite !(merge_spec f). Qed.
    Global Instance: Idempotent (=) f → Idempotent (=) (merge f).
    Proof.
      intros ??. apply merge_idempotent. intros. by apply (idempotent f).
    Qed.
  End merge_with.

  (** ** Properties on the intersection forall relation *)
  Section intersection_forall.
    Context (R : relation A).

    Global Instance finmap_intersection_forall_sym:
      Symmetric R → Symmetric (finmap_intersection_forall R).
    Proof. firstorder auto. Qed.
    Lemma finmap_intersection_forall_empty_l (m : M A) :
      finmap_intersection_forall R ∅ m.
    Proof. intros ???. by simpl_map. Qed.
    Lemma finmap_intersection_forall_empty_r (m : M A) :
      finmap_intersection_forall R m ∅.
    Proof. intros ???. by simpl_map. Qed.

    (** Due to the finiteness of finite maps, we can extract a witness are
    property does not hold for the intersection. *)
    Lemma finmap_not_intersection_forall `{∀ x y, Decision (R x y)} (m1 m2 : M A) :
      ¬finmap_intersection_forall R m1 m2
        ↔ ∃ i x1 x2, m1 !! i = Some x1 ∧ m2 !! i = Some x2 ∧ ¬R x1 x2.
    Proof.
      split.
      * intros Hdisjoint.
        set (Pi i := ∀ x1 x2, m1 !! i = Some x1 → m2 !! i = Some x2 → ¬R x1 x2).
        assert (∀ i, Decision (Pi i)).
        { intros i. unfold Decision, Pi.
          destruct (m1 !! i) as [x1|], (m2 !! i) as [x2|]; try (by left).
          destruct (decide (R x1 x2)).
          * naive_solver.
          * intuition congruence. }
        destruct (decide (cexists Pi (dom (listset _) m1 ∩ dom (listset _) m2)))
          as [[i [Hdom Hi]] | Hi].
        + rewrite elem_of_intersection in Hdom.
          rewrite !(elem_of_dom (listset _)), !is_Some_alt in Hdom.
          destruct Hdom as [[x1 ?] [x2 ?]]. exists i x1 x2; auto.
        + destruct Hdisjoint. intros i x1 x2 Hx1 Hx2.
          apply dec_stable. intros HP.
          destruct Hi. exists i.
          rewrite elem_of_intersection, !(elem_of_dom (listset _)).
          intuition eauto; congruence.
      * intros (i & x1 & x2 & Hx1 & Hx2 & Hx1x2) Hdisjoint.
        by apply Hx1x2, (Hdisjoint i x1 x2).
    Qed.
  End intersection_forall.

  (** ** Properties on the disjoint maps *)
  Lemma finmap_disjoint_alt (m1 m2 : M A) :
    m1 ⊥ m2 ↔ ∀ i, m1 !! i = None ∨ m2 !! i = None.
  Proof.
    split; intros Hm1m2 i; specialize (Hm1m2 i);
      destruct (m1 !! i), (m2 !! i); naive_solver.
  Qed.    
  Lemma finmap_not_disjoint (m1 m2 : M A) :
    ¬m1 ⊥ m2 ↔ ∃ i x1 x2, m1 !! i = Some x1 ∧ m2 !! i = Some x2.
  Proof.
    unfold disjoint, finmap_disjoint.
    rewrite finmap_not_intersection_forall.
    * naive_solver.
    * right. auto.
  Qed.

  Global Instance: Symmetric (@disjoint (M A) _).
  Proof. apply finmap_intersection_forall_sym. auto. Qed.
  Lemma finmap_disjoint_empty_l (m : M A) : ∅ ⊥ m.
  Proof. apply finmap_intersection_forall_empty_l. Qed.
  Lemma finmap_disjoint_empty_r (m : M A) : m ⊥ ∅.
  Proof. apply finmap_intersection_forall_empty_r. Qed.

  Lemma finmap_disjoint_weaken (m1 m1' m2 m2' : M A) :
    m1' ⊥ m2' →
    m1 ⊆ m1' → m2 ⊆ m2' →
    m1 ⊥ m2.
  Proof.
    intros Hdisjoint Hm1 Hm2 i x1 x2 Hx1 Hx2.
    destruct (Hdisjoint i x1 x2); auto.
  Qed.
  Lemma finmap_disjoint_weaken_l (m1 m1' m2  : M A) :
    m1' ⊥ m2 → m1 ⊆ m1' → m1 ⊥ m2.
  Proof. eauto using finmap_disjoint_weaken. Qed.
  Lemma finmap_disjoint_weaken_r (m1 m2 m2' : M A) :
    m1 ⊥ m2' → m2 ⊆ m2' → m1 ⊥ m2.
  Proof. eauto using finmap_disjoint_weaken. Qed.

  Lemma finmap_disjoint_Some_l (m1 m2 : M A) i x:
    m1 ⊥ m2 →
    m1 !! i = Some x →
    m2 !! i = None.
  Proof.
    intros Hdisjoint ?. rewrite eq_None_not_Some, is_Some_alt.
    intros [x2 ?]. by apply (Hdisjoint i x x2).
  Qed.
  Lemma finmap_disjoint_Some_r (m1 m2 : M A) i x:
    m1 ⊥ m2 →
    m2 !! i = Some x →
    m1 !! i = None.
  Proof. rewrite (symmetry_iff (⊥)). apply finmap_disjoint_Some_l. Qed.

  Lemma finmap_disjoint_singleton_l (m : M A) i x :
    {[(i, x)]} ⊥ m ↔ m !! i = None.
  Proof.
    split.
    * intro. apply (finmap_disjoint_Some_l {[(i, x)]} _ _ x); by simpl_map.
    * intros ? j y1 y2 ??.
      destruct (decide (i = j)); simplify_map_equality; congruence.
  Qed.
  Lemma finmap_disjoint_singleton_r (m : M A) i x :
    m ⊥ {[(i, x)]} ↔ m !! i = None.
  Proof. by rewrite (symmetry_iff (⊥)), finmap_disjoint_singleton_l. Qed.

  Lemma finmap_disjoint_singleton_l_2 (m : M A) i x :
    m !! i = None → {[(i, x)]} ⊥ m.
  Proof. by rewrite finmap_disjoint_singleton_l. Qed.
  Lemma finmap_disjoint_singleton_r_2 (m : M A) i x :
    m !! i = None → m ⊥ {[(i, x)]}.
  Proof. by rewrite finmap_disjoint_singleton_r. Qed.

  (** ** Properties of the union and intersection operation *)
  Section union_intersection_with.
    Context (f : A → A → option A).

    Lemma finmap_union_with_Some m1 m2 i x y :
      m1 !! i = Some x →
      m2 !! i = Some y →
      union_with f m1 m2 !! i = f x y.
    Proof.
      intros Hx Hy. unfold union_with, finmap_union_with.
      by rewrite (merge_spec _), Hx, Hy.
    Qed.
    Lemma finmap_union_with_Some_l m1 m2 i x :
      m1 !! i = Some x →
      m2 !! i = None →
      union_with f m1 m2 !! i = Some x.
    Proof.
      intros Hx Hy. unfold union_with, finmap_union_with.
      by rewrite (merge_spec _), Hx, Hy.
    Qed.
    Lemma finmap_union_with_Some_r m1 m2 i y :
      m1 !! i = None →
      m2 !! i = Some y →
      union_with f m1 m2 !! i = Some y.
    Proof.
      intros Hx Hy. unfold union_with, finmap_union_with.
      by rewrite (merge_spec _), Hx, Hy.
    Qed.

    Global Instance: LeftId (=) ∅ (@union_with _ (M A) _ f).
    Proof. unfold union_with, finmap_union_with. apply _. Qed.
    Global Instance: RightId (=) ∅ (@union_with _ (M A) _ f).
    Proof. unfold union_with, finmap_union_with. apply _. Qed.
    Global Instance:
      Commutative (=) f → Commutative (=) (@union_with _ (M A) _ f).
    Proof. unfold union_with, finmap_union_with. apply _. Qed.
  End union_intersection_with.

  Global Instance: LeftId (=) ∅ (@union (M A) _) := _.
  Global Instance: RightId (=) ∅ (@union (M A) _) := _.
  Global Instance: Associative (=) (@union (M A) _).
  Proof.
    intros m1 m2 m3. unfold union, finmap_union, union_with, finmap_union_with.
    apply (merge_associative _). intros i.
    by destruct (m1 !! i), (m2 !! i), (m3 !! i).
  Qed.
  Global Instance: Idempotent (=) (@union (M A) _).
    intros m. unfold union, finmap_union, union_with, finmap_union_with.
    apply (merge_idempotent _). intros i. by destruct (m !! i).
  Qed.

  Lemma lookup_union_Some_raw (m1 m2 : M A) i x :
    (m1 ∪ m2) !! i = Some x ↔
      m1 !! i = Some x ∨ (m1 !! i = None ∧ m2 !! i = Some x).
  Proof.
    unfold union, finmap_union, union_with, finmap_union_with.
    rewrite (merge_spec _).
    destruct (m1 !! i), (m2 !! i); compute; intuition congruence.
  Qed.
  Lemma lookup_union_None (m1 m2 : M A) i :
    (m1 ∪ m2) !! i = None ↔ m1 !! i = None ∧ m2 !! i = None.
  Proof.
    unfold union, finmap_union, union_with, finmap_union_with.
    rewrite (merge_spec _).
    destruct (m1 !! i), (m2 !! i); compute; intuition congruence.
  Qed.

  Lemma lookup_union_Some (m1 m2 : M A) i x :
    m1 ⊥ m2 →
    (m1 ∪ m2) !! i = Some x ↔ m1 !! i = Some x ∨ m2 !! i = Some x.
  Proof.
    intros Hdisjoint. rewrite lookup_union_Some_raw.
    intuition eauto using finmap_disjoint_Some_r.
  Qed.

  Lemma lookup_union_Some_l (m1 m2 : M A) i x :
    m1 !! i = Some x →
    (m1 ∪ m2) !! i = Some x.
  Proof. intro. rewrite lookup_union_Some_raw; intuition. Qed.
  Lemma lookup_union_Some_r (m1 m2 : M A) i x :
    m1 ⊥ m2 →
    m2 !! i = Some x →
    (m1 ∪ m2) !! i = Some x.
  Proof. intro. rewrite lookup_union_Some; intuition. Qed.

  Lemma finmap_union_comm (m1 m2 : M A) :
    m1 ⊥ m2 →
    m1 ∪ m2 = m2 ∪ m1.
  Proof.
    intros Hdisjoint. apply (merge_commutative (union_with (λ x _, Some x))).
    intros i. specialize (Hdisjoint i).
    destruct (m1 !! i), (m2 !! i); compute; naive_solver.
  Qed.

  Lemma finmap_subseteq_union (m1 m2 : M A) :
    m1 ⊆ m2 →
    m1 ∪ m2 = m2.
  Proof.
    intros Hm1m2.
    apply finmap_eq. intros i. apply option_eq. intros x.
    rewrite lookup_union_Some_raw. split; [by intuition |].
    intros Hm2. specialize (Hm1m2 i).
    destruct (m1 !! i) as [y|]; [| by auto].
    rewrite (Hm1m2 y eq_refl) in Hm2. intuition congruence.
  Qed.
  Lemma finmap_subseteq_union_l (m1 m2 : M A) :
    m1 ⊆ m1 ∪ m2.
  Proof. intros ? i x. rewrite lookup_union_Some_raw. intuition. Qed.
  Lemma finmap_subseteq_union_r (m1 m2 : M A) :
    m1 ⊥ m2 →
    m2 ⊆ m1 ∪ m2.
  Proof.
    intros. rewrite finmap_union_comm by done.
    by apply finmap_subseteq_union_l.
  Qed.

  Lemma finmap_disjoint_union_l (m1 m2 m3 : M A) :
    m1 ∪ m2 ⊥ m3 ↔ m1 ⊥ m3 ∧ m2 ⊥ m3.
  Proof.
    rewrite !finmap_disjoint_alt.
    setoid_rewrite lookup_union_None. naive_solver.
  Qed.
  Lemma finmap_disjoint_union_r (m1 m2 m3 : M A) :
    m1 ⊥ m2 ∪ m3 ↔ m1 ⊥ m2 ∧ m1 ⊥ m3.
  Proof.
    rewrite !finmap_disjoint_alt.
    setoid_rewrite lookup_union_None. naive_solver.
  Qed.
  Lemma finmap_disjoint_union_l_2 (m1 m2 m3 : M A) :
    m1 ⊥ m3 → m2 ⊥ m3 → m1 ∪ m2 ⊥ m3.
  Proof. by rewrite finmap_disjoint_union_l. Qed.
  Lemma finmap_disjoint_union_r_2 (m1 m2 m3 : M A) :
    m1 ⊥ m2 → m1 ⊥ m3 → m1 ⊥ m2 ∪ m3.
  Proof. by rewrite finmap_disjoint_union_r. Qed.
  Lemma finmap_union_cancel_l (m1 m2 m3 : M A) :
    m1 ⊥ m3 →
    m2 ⊥ m3 →
    m1 ∪ m3 = m2 ∪ m3 →
    m1 = m2.
  Proof.
    revert m1 m2 m3.
    cut (∀ (m1 m2 m3 : M A) i x,
      m1 ⊥ m3 →
      m2 ⊥ m3 →
      m1 ∪ m3 = m2 ∪ m3 →
      m1 !! i = Some x → m2 !! i = Some x).
    { intros. apply finmap_eq. intros i.
      apply option_eq. naive_solver. }
    intros m1 m2 m3 b v Hm1m3 Hm2m3 E ?.
    destruct (proj1 (lookup_union_Some m2 m3 b v Hm2m3)) as [E2|E2].
    * rewrite <-E. by apply lookup_union_Some_l.
    * done.
    * contradict E2. by apply eq_None_ne_Some, finmap_disjoint_Some_l with m1 v.
  Qed.
  Lemma finmap_union_cancel_r (m1 m2 m3 : M A) :
    m1 ⊥ m3 →
    m2 ⊥ m3 →
    m3 ∪ m1 = m3 ∪ m2 →
    m1 = m2.
  Proof.
    intros ??. rewrite !(finmap_union_comm m3) by done.
    by apply finmap_union_cancel_l.
  Qed.

  Lemma insert_union_singleton_l (m : M A) i x :
    <[i:=x]>m = {[(i,x)]} ∪ m.
  Proof.
    apply finmap_eq. intros j. apply option_eq. intros y.
    rewrite lookup_union_Some_raw.
    destruct (decide (i = j)); simplify_map_equality; intuition congruence.
  Qed.
  Lemma insert_union_singleton_r (m : M A) i x :
    m !! i = None →
    <[i:=x]>m = m ∪ {[(i,x)]}.
  Proof.
    intro. rewrite insert_union_singleton_l, finmap_union_comm; [done |].
    by apply finmap_disjoint_singleton_l.
  Qed.

  Lemma finmap_disjoint_insert_l (m1 m2 : M A) i x :
    <[i:=x]>m1 ⊥ m2 ↔ m2 !! i = None ∧ m1 ⊥ m2.
  Proof.
    rewrite insert_union_singleton_l.
    by rewrite finmap_disjoint_union_l, finmap_disjoint_singleton_l.
  Qed.
  Lemma finmap_disjoint_insert_r (m1 m2 : M A) i x :
    m1 ⊥ <[i:=x]>m2 ↔ m1 !! i = None ∧ m1 ⊥ m2.
  Proof.
    rewrite insert_union_singleton_l.
    by rewrite finmap_disjoint_union_r, finmap_disjoint_singleton_r.
  Qed.

  Lemma finmap_disjoint_insert_l_2 (m1 m2 : M A) i x :
    m2 !! i = None → m1 ⊥ m2 → <[i:=x]>m1 ⊥ m2.
  Proof. by rewrite finmap_disjoint_insert_l. Qed.
  Lemma finmap_disjoint_insert_r_2 (m1 m2 : M A) i x :
    m1 !! i = None → m1 ⊥ m2 → m1 ⊥ <[i:=x]>m2.
  Proof. by rewrite finmap_disjoint_insert_r. Qed.

  Lemma insert_union_l (m1 m2 : M A) i x :
    <[i:=x]>(m1 ∪ m2) = <[i:=x]>m1 ∪ m2.
  Proof. by rewrite !insert_union_singleton_l, (associative (∪)). Qed.
  Lemma insert_union_r (m1 m2 : M A) i x :
    m1 !! i = None →
    <[i:=x]>(m1 ∪ m2) = m1 ∪ <[i:=x]>m2.
  Proof.
    intro. rewrite !insert_union_singleton_l, !(associative (∪)).
    rewrite (finmap_union_comm m1); [done |].
    by apply finmap_disjoint_singleton_r.
  Qed.

  Lemma insert_list_union l (m : M A) :
    insert_list l m = finmap_of_list l ∪ m.
  Proof.
    induction l; simpl.
    * by rewrite (left_id _ _).
    * by rewrite IHl, insert_union_l.
  Qed.

  Lemma insert_subseteq_r (m1 m2 : M A) i x :
    m1 !! i = None → m1 ⊆ m2 → m1 ⊆ <[i:=x]>m2.
  Proof.
    intros ?? j. by destruct (decide (j = i)); intros; simplify_map_equality.
  Qed.

  (** ** Properties of the delete operation *)
  Lemma finmap_disjoint_delete_l (m1 m2 : M A) i :
    m1 ⊥ m2 → delete i m1 ⊥ m2.
  Proof.
    rewrite !finmap_disjoint_alt.
    intros Hdisjoint j. destruct (Hdisjoint j); auto.
    rewrite lookup_delete_None. tauto.
  Qed.
  Lemma finmap_disjoint_delete_r (m1 m2 : M A) i :
    m1 ⊥ m2 → m1 ⊥ delete i m2.
  Proof. symmetry. by apply finmap_disjoint_delete_l. Qed.

  Lemma finmap_disjoint_delete_list_l (m1 m2 : M A) is :
    m1 ⊥ m2 → delete_list is m1 ⊥ m2.
  Proof. induction is; simpl; auto using finmap_disjoint_delete_l. Qed.
  Lemma finmap_disjoint_delete_list_r (m1 m2 : M A) is :
    m1 ⊥ m2 → m1 ⊥ delete_list is m2.
  Proof. induction is; simpl; auto using finmap_disjoint_delete_r. Qed.

  Lemma finmap_union_delete (m1 m2 : M A) i :
    delete i (m1 ∪ m2) = delete i m1 ∪ delete i m2.
  Proof.
    intros. apply finmap_eq. intros j. apply option_eq. intros y.
    destruct (decide (i = j)); simplify_map_equality;
     rewrite ?lookup_union_Some_raw; simpl_map; intuition congruence.
  Qed.
  Lemma finmap_union_delete_list (m1 m2 : M A) is :
    delete_list is (m1 ∪ m2) = delete_list is m1 ∪ delete_list is m2.
  Proof.
    induction is; simpl; [done |].
    by rewrite IHis, finmap_union_delete.
  Qed.

  Lemma finmap_disjoint_union_list_l (ms : list (M A)) (m : M A) :
    ⋃ ms ⊥ m ↔ Forall (⊥ m) ms.
  Proof.
    split.
    * induction ms; simpl; rewrite ?finmap_disjoint_union_l; intuition.
    * induction 1; simpl.
      + apply finmap_disjoint_empty_l.
      + by rewrite finmap_disjoint_union_l.
  Qed.
  Lemma finmap_disjoint_union_list_r (ms : list (M A)) (m : M A) :
    m ⊥ ⋃ ms ↔ Forall (⊥ m) ms.
  Proof. by rewrite (symmetry_iff (⊥)), finmap_disjoint_union_list_l. Qed.

  Lemma finmap_disjoint_union_list_l_2 (ms : list (M A)) (m : M A) :
    Forall (⊥ m) ms → ⋃ ms ⊥ m.
  Proof. by rewrite finmap_disjoint_union_list_l. Qed.
  Lemma finmap_disjoint_union_list_r_2 (ms : list (M A)) (m : M A) :
    Forall (⊥ m) ms → m ⊥ ⋃ ms.
  Proof. by rewrite finmap_disjoint_union_list_r. Qed.

  (** ** Properties of the conversion from lists to maps *)
  Lemma finmap_disjoint_of_list_l (m : M A) ixs :
    finmap_of_list ixs ⊥ m ↔ Forall (λ ix, m !! fst ix = None) ixs.
  Proof.
    split.
    * induction ixs; simpl; rewrite ?finmap_disjoint_insert_l in *; intuition.
    * induction 1; simpl.
      + apply finmap_disjoint_empty_l.
      + rewrite finmap_disjoint_insert_l. auto.
  Qed.
  Lemma finmap_disjoint_of_list_r (m : M A) ixs :
    m ⊥ finmap_of_list ixs ↔ Forall (λ ix, m !! fst ix = None) ixs.
  Proof. by rewrite (symmetry_iff (⊥)), finmap_disjoint_of_list_l. Qed.

  Lemma finmap_disjoint_of_list_zip_l (m : M A) is xs :
    same_length is xs →
    finmap_of_list (zip is xs) ⊥ m ↔ Forall (λ i, m !! i = None) is.
  Proof.
    intro. rewrite finmap_disjoint_of_list_l.
    rewrite <-(zip_fst is xs) at 2 by done.
    by rewrite Forall_fmap.
  Qed.
  Lemma finmap_disjoint_of_list_zip_r (m : M A) is xs :
    same_length is xs →
    m ⊥ finmap_of_list (zip is xs) ↔ Forall (λ i, m !! i = None) is.
  Proof.
    intro. by rewrite (symmetry_iff (⊥)), finmap_disjoint_of_list_zip_l.
  Qed.
  Lemma finmap_disjoint_of_list_zip_l_2 (m : M A) is xs :
    same_length is xs →
    Forall (λ i, m !! i = None) is →
    finmap_of_list (zip is xs) ⊥ m.
  Proof. intro. by rewrite finmap_disjoint_of_list_zip_l. Qed.
  Lemma finmap_disjoint_of_list_zip_r_2 (m : M A) is xs :
    same_length is xs →
    Forall (λ i, m !! i = None) is →
    m ⊥ finmap_of_list (zip is xs).
  Proof. intro. by rewrite finmap_disjoint_of_list_zip_r. Qed.

  (** ** Properties with respect to vectors *)
  Lemma union_delete_vec {n} (ms : vec (M A) n) (i : fin n) :
    list_disjoint ms →
    ms !!! i ∪ ⋃ delete (fin_to_nat i) (vec_to_list ms) = ⋃ ms.
  Proof.
    induction ms as [|m ? ms]; inversion_clear 1;
      inv_fin i; simpl; [done | intros i].
    rewrite (finmap_union_comm m), (associative_eq _ _), IHms.
    * by apply finmap_union_comm, finmap_disjoint_union_list_l.
    * done.
    * by apply finmap_disjoint_union_list_r, Forall_delete.
  Qed.

  Lemma union_insert_vec {n} (ms : vec (M A) n) (i : fin n) m :
    m ⊥ ⋃ delete (fin_to_nat i) (vec_to_list ms) →
    ⋃ vinsert i m ms = m ∪ ⋃ delete (fin_to_nat i) (vec_to_list ms).
  Proof.
    induction ms as [|m' ? ms IH];
      inv_fin i; simpl; [done | intros i Hdisjoint].
    rewrite finmap_disjoint_union_r in Hdisjoint.
    rewrite IH, !(associative_eq (∪)), (finmap_union_comm m); intuition.
  Qed.

  Lemma finmap_list_disjoint_delete_vec {n} (ms : vec (M A) n) (i : fin n) :
    list_disjoint ms →
    Forall (⊥ ms !!! i) (delete (fin_to_nat i) (vec_to_list ms)).
  Proof.
    induction ms; inversion_clear 1; inv_fin i; simpl.
    * done.
    * constructor. symmetry. by apply Forall_vlookup. auto.
  Qed.

  Lemma finmap_list_disjoint_insert_vec {n} (ms : vec (M A) n) (i : fin n) m :
    list_disjoint ms →
    Forall (⊥ m) (delete (fin_to_nat i) (vec_to_list ms)) →
    list_disjoint (vinsert i m ms).
  Proof.
    induction ms as [|m' ? ms]; inversion_clear 1; inv_fin i; simpl.
    { constructor; auto. }
    intros i. inversion_clear 1. constructor; [| by auto].
    apply Forall_vlookup_2. intros j.
    destruct (decide (i = j)); subst;
      rewrite ?vlookup_insert, ?vlookup_insert_ne by done.
    * done.
    * by apply Forall_vlookup.
  Qed.

  (** ** Properties of the difference operation *)
  Lemma finmap_difference_Some (m1 m2 : M A) i x :
    (m1 ∖ m2) !! i = Some x ↔ m1 !! i = Some x ∧ m2 !! i = None.
  Proof.
    unfold difference, finmap_difference,
      difference_with, finmap_difference_with.
    rewrite (merge_spec _).
    destruct (m1 !! i), (m2 !! i); compute; intuition congruence.
  Qed.

  Lemma finmap_disjoint_difference_l (m1 m2 m3 : M A) :
    m2 ⊆ m3 → m1 ∖ m3 ⊥ m2.
  Proof.
    intros E i. specialize (E i).
    unfold difference, finmap_difference,
      difference_with, finmap_difference_with.
    rewrite (merge_spec _).
    destruct (m1 !! i), (m2 !! i), (m3 !! i); compute;
      try intuition congruence.
    ediscriminate E; eauto.
  Qed.
  Lemma finmap_disjoint_difference_r (m1 m2 m3 : M A) :
    m2 ⊆ m3 → m2 ⊥ m1 ∖ m3.
  Proof. intros. symmetry. by apply finmap_disjoint_difference_l. Qed.

  Lemma finmap_union_difference (m1 m2 : M A) :
    m1 ⊆ m2 → m2 = m1 ∪ m2 ∖ m1.
  Proof.
    intro Hm1m2. apply finmap_eq. intros i.
    apply option_eq. intros v. specialize (Hm1m2 i).
    unfold difference, finmap_difference,
      difference_with, finmap_difference_with.
    rewrite lookup_union_Some_raw, (merge_spec _).
    destruct (m1 !! i) as [v'|], (m2 !! i);
      try specialize (Hm1m2 v'); compute; intuition congruence.
  Qed.
End finmap_more.

Hint Extern 80 ((_ ∪ _) !! _ = Some _) =>
  apply lookup_union_Some_l : simpl_map.
Hint Extern 81 ((_ ∪ _) !! _ = Some _) =>
  apply lookup_union_Some_r : simpl_map.
Hint Extern 80 ({[ _ ]} !! _ = Some _) =>
  apply lookup_singleton : simpl_map.
Hint Extern 80 (<[_:=_]> _ !! _ = Some _) =>
  apply lookup_insert : simpl_map.

(** * Tactic to decompose disjoint assumptions *)
(** The tactic [decompose_map_disjoint] simplifies occurences of [disjoint]
in the conclusion and hypotheses that involve the union, insert, or singleton
operation. *)
Ltac decompose_map_disjoint := repeat
  match goal with
  | H : _ ∪ _ ⊥ _ |- _ =>
    apply finmap_disjoint_union_l in H; destruct H
  | H : _ ⊥ _ ∪ _ |- _ =>
    apply finmap_disjoint_union_r in H; destruct H
  | H : {[ _ ]} ⊥ _ |- _ => apply finmap_disjoint_singleton_l in H
  | H : _ ⊥ {[ _ ]} |- _ =>  apply finmap_disjoint_singleton_r in H
  | H : <[_:=_]>_ ⊥ _ |- _ =>
    apply finmap_disjoint_insert_l in H; destruct H
  | H : _ ⊥ <[_:=_]>_ |- _ =>
    apply finmap_disjoint_insert_r in H; destruct H
  | H : ⋃ _ ⊥ _ |- _ => apply finmap_disjoint_union_list_l in H
  | H : _ ⊥ ⋃ _ |- _ => apply finmap_disjoint_union_list_r in H
  | H : ∅ ⊥_ |- _ => clear H
  | H : _ ⊥ ∅ |- _ => clear H
  | H : list_disjoint [] |- _ => clear H
  | H : list_disjoint [_] |- _ => clear H
  | H : list_disjoint (_ :: _) |- _ =>
    apply list_disjoint_cons_inv in H; destruct H
  | H : Forall (⊥ _) _ |- _ => rewrite Forall_vlookup in H
  | H : Forall (⊥ _) [] |- _ => clear H
  | H : Forall (⊥ _) (_ :: _) |- _ =>
    rewrite Forall_cons in H; destruct H
  | H : Forall (⊥ _) (_ :: _) |- _ =>
    rewrite Forall_app in H; destruct H
  end.
