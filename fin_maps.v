(* Copyright (c) 2012, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** Finite maps associate data to keys. This file defines an interface for
finite maps and collects some theory on it. Most importantly, it proves useful
induction principles for finite maps and implements the tactic [simplify_map]
to simplify goals involving finite maps. *)
Require Export prelude.

(** * Axiomatization of finite maps *)
(** We require Leibniz equality to be extensional on finite maps. This of
course limits the class of finite map implementations, but since we are mainly
interested in finite maps with numbers or paths as indexes, we do not consider
this a serious limitation. The main application of finite maps is to implement
the memory, where extensionality of Leibniz equality becomes very important for
a convenient use in assertions of our axiomatic semantics. *)
(** Finiteness is axiomatized by requiring each map to have a finite domain.
Since we may have multiple implementations of finite sets, the [dom] function is
parametrized by an implementation of finite sets over the map's key type. *)
(** Finite map implementations are required to implement the [merge] function
which enables us to give a generic implementation of [union_with],
[intersection_with], and [difference_with]. *)
Class FinMap K M `{∀ A, Empty (M A)} `{Lookup K M} `{FMap M}
    `{PartialAlter K M} `{∀ A, Dom K (M A)} `{Merge M} := {
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
  elem_of_dom C {A} `{Collection K C} (m : M A) i :
    i ∈ dom C m ↔ is_Some (m !! i);
  merge_spec {A} f `{!PropHolds (f None None = None)}
    (m1 m2 : M A) i : merge f m1 m2 !! i = f (m1 !! i) (m2 !! i)
}.

(** * Derived operations *)
(** All of the following functions are defined in a generic way for arbitrary
finite map implementations. These generic implementations do not cause a
significant enough performance loss to make including them in the finite map
axiomatization worthwhile. *)
Instance finmap_alter `{PartialAlter K M} : Alter K M := λ A f,
  partial_alter (fmap f).
Instance finmap_insert `{PartialAlter K M} : Insert K M := λ A k x,
  partial_alter (λ _, Some x) k.
Instance finmap_delete `{PartialAlter K M} {A} : Delete K (M A) :=
  partial_alter (λ _, None).
Instance finmap_singleton `{PartialAlter K M} {A}
  `{Empty (M A)} : Singleton (K * A) (M A) := λ p, <[fst p:=snd p]>∅.

Definition list_to_map `{Insert K M} {A} `{Empty (M A)}
  (l : list (K * A)) : M A := insert_list l ∅.

Instance finmap_union `{Merge M} : UnionWith M := λ A f,
  merge (union_with f).
Instance finmap_intersection `{Merge M} : IntersectionWith M := λ A f,
  merge (intersection_with f).
Instance finmap_difference `{Merge M} : DifferenceWith M := λ A f,
  merge (difference_with f).

(** * General theorems *)
Section finmap.
Context `{FinMap K M} `{∀ i j : K, Decision (i = j)} {A : Type}.

Global Instance finmap_subseteq: SubsetEq (M A) := λ m n,
  ∀ i x, m !! i = Some x → n !! i = Some x.
Global Instance: BoundedPreOrder (M A).
Proof. split. firstorder. intros m i x. rewrite lookup_empty. discriminate. Qed.

Lemma lookup_subseteq_Some (m1 m2 : M A) i x :
  m1 ⊆ m2 → m1 !! i = Some x → m2 !! i = Some x.
Proof. auto. Qed.
Lemma lookup_subseteq_None (m1 m2 : M A) i :
  m1 ⊆ m2 → m2 !! i = None → m1 !! i = None.
Proof. rewrite !eq_None_not_Some. firstorder. Qed.
Lemma lookup_ne (m : M A) i j : m !! i ≠ m !! j → i ≠ j.
Proof. congruence. Qed.

Lemma not_elem_of_dom C `{Collection K C} (m : M A) i :
  i ∉ dom C m ↔ m !! i = None.
Proof. now rewrite (elem_of_dom C), eq_None_not_Some. Qed.

Lemma finmap_empty (m : M A) : (∀ i, m !! i = None) → m = ∅.
Proof. intros Hm. apply finmap_eq. intros. now rewrite Hm, lookup_empty. Qed.
Lemma dom_empty C `{Collection K C} : dom C (∅ : M A) ≡ ∅.
Proof.
  split; intro.
  * rewrite (elem_of_dom C), lookup_empty. simplify_is_Some.
  * solve_elem_of.
Qed.
Lemma dom_empty_inv C `{Collection K C} (m : M A) : dom C m ≡ ∅ → m = ∅.
Proof.
  intros E. apply finmap_empty. intros. apply (not_elem_of_dom C).
  rewrite E. solve_elem_of.
Qed.

Lemma lookup_empty_not i : ¬is_Some ((∅ : M A) !! i).
Proof. rewrite lookup_empty. simplify_is_Some. Qed.
Lemma lookup_empty_Some i (x : A) : ¬∅ !! i = Some x.
Proof. rewrite lookup_empty. discriminate. Qed.

Lemma partial_alter_compose (m : M A) i f g :
  partial_alter (f ∘ g) i m = partial_alter f i (partial_alter g i m).
Proof.
  intros. apply finmap_eq. intros ii. case (decide (i = ii)).
  * intros. subst. now rewrite !lookup_partial_alter.
  * intros. now rewrite !lookup_partial_alter_ne.
Qed.
Lemma partial_alter_comm (m : M A) i j f g :
  i ≠ j →
 partial_alter f i (partial_alter g j m) = partial_alter g j (partial_alter f i m).
Proof.
  intros. apply finmap_eq. intros jj.
  destruct (decide (jj = j)).
  * subst. now rewrite lookup_partial_alter_ne,
     !lookup_partial_alter, lookup_partial_alter_ne.
  * destruct (decide (jj = i)).
    + subst. now rewrite lookup_partial_alter,
       !lookup_partial_alter_ne, lookup_partial_alter by congruence.
    + now rewrite !lookup_partial_alter_ne by congruence.
Qed.
Lemma partial_alter_self_alt (m : M A) i x :
  x = m !! i → partial_alter (λ _, x) i m = m.
Proof.
  intros. apply finmap_eq. intros ii.
  destruct (decide (i = ii)).
  * subst. now rewrite lookup_partial_alter.
  * now rewrite lookup_partial_alter_ne.
Qed.
Lemma partial_alter_self (m : M A) i : partial_alter (λ _, m !! i) i m = m.
Proof. now apply partial_alter_self_alt. Qed.

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
    + now rewrite lookup_insert_ne.
Qed.
Lemma lookup_insert_None (m : M A) i j x :
  <[i:=x]>m !! j = None ↔ m !! j = None ∧ i ≠ j.
Proof.
  split.
  * destruct (decide (i = j)); subst;
      rewrite ?lookup_insert, ?lookup_insert_ne; intuition congruence.
  * intros [??]. now rewrite lookup_insert_ne.
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

Lemma lookup_singleton i (x : A) : {[(i, x)]} !! i = Some x.
Proof. rewrite lookup_singleton_Some. tauto. Qed.
Lemma lookup_singleton_ne i j (x : A) : i ≠ j → {[(i, x)]} !! j = None.
Proof. now rewrite lookup_singleton_None. Qed.

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
  * intros [??]. now rewrite lookup_delete_ne.
Qed.
Lemma lookup_delete_None (m : M A) i j :
  delete i m !! j = None ↔ i = j ∨ m !! j = None.
Proof.
  destruct (decide (i = j)).
  * subst. rewrite lookup_delete. tauto.
  * rewrite lookup_delete_ne; tauto.
Qed.

Lemma delete_empty i : delete i (∅ : M A) = ∅.
Proof. rewrite <-(partial_alter_self ∅) at 2. now rewrite lookup_empty. Qed.
Lemma delete_singleton i (x : A) : delete i {[(i, x)]} = ∅.
Proof. setoid_rewrite <-partial_alter_compose. apply delete_empty. Qed.
Lemma delete_comm (m : M A) i j : delete i (delete j m) = delete j (delete i m).
Proof. destruct (decide (i = j)). now subst. now apply partial_alter_comm. Qed.
Lemma delete_insert_comm (m : M A) i j x :
  i ≠ j → delete i (<[j:=x]>m) = <[j:=x]>(delete i m).
Proof. intro. now apply partial_alter_comm. Qed.

Lemma delete_notin (m : M A) i : m !! i = None → delete i m = m.
Proof.
  intros. apply finmap_eq. intros j.
  destruct (decide (i = j)).
  * subst. now rewrite lookup_delete.
  * now apply lookup_delete_ne.
Qed.

Lemma delete_partial_alter (m : M A) i f :
  m !! i = None → delete i (partial_alter f i m) = m.
Proof.
  intros. unfold delete, finmap_delete. rewrite <-partial_alter_compose.
  rapply partial_alter_self_alt. congruence.
Qed.
Lemma delete_partial_alter_dom C `{Collection K C} (m : M A) i f :
  i ∉ dom C m → delete i (partial_alter f i m) = m.
Proof. rewrite (not_elem_of_dom C). apply delete_partial_alter. Qed.
Lemma delete_insert (m : M A) i x : m !! i = None → delete i (<[i:=x]>m) = m.
Proof. apply delete_partial_alter. Qed.
Lemma delete_insert_dom C `{Collection K C} (m : M A) i x :
  i ∉ dom C m → delete i (<[i:=x]>m) = m.
Proof. rewrite (not_elem_of_dom C). apply delete_partial_alter. Qed.
Lemma insert_delete (m : M A) i x : m !! i = Some x → <[i:=x]>(delete i m) = m.
Proof.
  intros Hmi. unfold delete, finmap_delete, insert, finmap_insert.
  rewrite <-partial_alter_compose. unfold compose. rewrite <-Hmi.
  now apply partial_alter_self_alt.
Qed.

Lemma elem_of_dom_delete C `{Collection K C} (m : M A) i j :
  i ∈ dom C (delete j m) ↔ i ≠ j ∧ i ∈ dom C m.
Proof.
  rewrite !(elem_of_dom C). unfold is_Some.
  setoid_rewrite lookup_delete_Some. firstorder auto.
Qed.
Lemma not_elem_of_dom_delete C `{Collection K C} (m : M A) i :
  i ∉ dom C (delete i m).
Proof. apply (not_elem_of_dom C), lookup_delete. Qed.

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
    + easy.
    + intros. rewrite <-(not_elem_of_dom C), Hm.
      now solve_elem_of.
  * clear m. intros i X Hi IH m Hdom.
    assert (is_Some (m !! i)) as [x Hx].
    { apply (elem_of_dom C).
      rewrite Hdom. clear Hdom.
      now solve_elem_of. }
    rewrite <-(insert_delete m i x) by easy.
    apply Hinsert.
    { now apply (not_elem_of_dom_delete C). }
    apply IH. apply elem_of_equiv. intros.
    rewrite (elem_of_dom_delete C).
    esolve_elem_of.
  * easy.
Qed.

(** We use the [listset] implementation to prove an induction principle that
does not mention the map's domain. *)
Lemma finmap_ind (P : M A → Prop) :
  P ∅ →
  (∀ i x m, m !! i = None → P m → P (<[i:=x]>m)) →
  ∀ m, P m.
Proof.
  setoid_rewrite <-(not_elem_of_dom (listset _)).
  apply (finmap_ind_alt (listset _) P).
Qed.

(** * Deleting and inserting multiple elements *)
Lemma lookup_delete_list (m : M A) is j :
  In j is → delete_list is m !! j = None.
Proof.
  induction is as [|i is]; simpl; [easy |].
  intros [?|?].
  * subst. now rewrite lookup_delete.
  * destruct (decide (i = j)).
    + subst. now rewrite lookup_delete.
    + rewrite lookup_delete_ne; auto.
Qed.
Lemma lookup_delete_list_notin (m : M A) is j :
  ¬In j is → delete_list is m !! j = m !! j.
Proof.
  induction is; simpl; [easy |].
  intros. rewrite lookup_delete_ne; tauto.
Qed.

Lemma delete_list_notin (m : M A) is :
  Forall (λ i, m !! i = None) is → delete_list is m = m.
Proof.
  induction 1; simpl; [easy |].
  rewrite delete_notin; congruence.
Qed.
Lemma delete_list_insert_comm (m : M A) is j x :
  ¬In j is → delete_list is (<[j:=x]>m) = <[j:=x]>(delete_list is m).
Proof.
  induction is; simpl; [easy |].
  intros. rewrite IHis, delete_insert_comm; tauto.
Qed.

Lemma lookup_insert_list (m : M A) l1 l2 i x :
  (∀y, ¬In (i,y) l1) → insert_list (l1 ++ (i,x) :: l2) m !! i = Some x.
Proof.
  induction l1 as [|[j y] l1 IH]; simpl.
  * intros. now rewrite lookup_insert.
  * intros Hy. rewrite lookup_insert_ne; naive_solver.
Qed.

Lemma lookup_insert_list_not_in (m : M A) l i :
  (∀y, ¬In (i,y) l) → insert_list l m !! i = m !! i.
Proof.
  induction l as [|[j y] l IH]; simpl.
  * easy.
  * intros Hy. rewrite lookup_insert_ne; naive_solver.
Qed.

(** * Properties of the merge operation *)
Section merge.
  Context (f : option A → option A → option A).

  Global Instance: LeftId (=) None f → LeftId (=) ∅ (merge f).
  Proof.
    intros ??. apply finmap_eq. intros.
    now rewrite !(merge_spec f), lookup_empty, (left_id None f).
  Qed.
  Global Instance: RightId (=) None f → RightId (=) ∅ (merge f).
  Proof.
    intros ??. apply finmap_eq. intros.
    now rewrite !(merge_spec f), lookup_empty, (right_id None f).
  Qed.
  Global Instance: Idempotent (=) f → Idempotent (=) (merge f).
  Proof. intros ??. apply finmap_eq. intros. now rewrite !(merge_spec f). Qed.

  Context `{!PropHolds (f None None = None)}.

  Lemma merge_spec_alt m1 m2 m :
    (∀ i, m !! i = f (m1 !! i) (m2 !! i)) ↔ merge f m1 m2 = m.
  Proof.
    split; [| intro; subst; apply (merge_spec _) ].
    intros Hlookup. apply finmap_eq. intros. rewrite Hlookup.
    apply (merge_spec _).
  Qed.

  Lemma merge_comm m1 m2 :
    (∀ i, f (m1 !! i) (m2 !! i) = f (m2 !! i) (m1 !! i)) →
    merge f m1 m2 = merge f m2 m1.
  Proof. intros. apply finmap_eq. intros. now rewrite !(merge_spec f). Qed.
  Global Instance: Commutative (=) f → Commutative (=) (merge f).
  Proof. intros ???. apply merge_comm. intros. now apply (commutative f). Qed.

  Lemma merge_assoc m1 m2 m3 :
    (∀ i, f (m1 !! i) (f (m2 !! i) (m3 !! i)) =
          f (f (m1 !! i) (m2 !! i)) (m3 !! i)) →
    merge f m1 (merge f m2 m3) = merge f (merge f m1 m2) m3.
  Proof. intros. apply finmap_eq. intros. now rewrite !(merge_spec f). Qed.
  Global Instance: Associative (=) f → Associative (=) (merge f).
  Proof. intros ????. apply merge_assoc. intros. now apply (associative f). Qed.
End merge.

(** * Properties of the union and intersection operation *)
Section union_intersection.
  Context (f : A → A → A).

  Lemma finmap_union_merge m1 m2 i x y :
    m1 !! i = Some x →
    m2 !! i = Some y →
    union_with f m1 m2 !! i = Some (f x y).
  Proof.
    intros Hx Hy. unfold union_with, finmap_union.
    now rewrite (merge_spec _), Hx, Hy.
  Qed.
  Lemma finmap_union_l m1 m2 i x :
    m1 !! i = Some x → m2 !! i = None → union_with f m1 m2 !! i = Some x.
  Proof.
    intros Hx Hy. unfold union_with, finmap_union.
    now rewrite (merge_spec _), Hx, Hy.
  Qed.
  Lemma finmap_union_r m1 m2 i y :
    m1 !! i = None → m2 !! i = Some y → union_with f m1 m2 !! i = Some y.
  Proof.
    intros Hx Hy. unfold union_with, finmap_union.
    now rewrite (merge_spec _), Hx, Hy.
  Qed.
  Lemma finmap_union_None m1 m2 i :
    union_with f m1 m2 !! i = None ↔ m1 !! i = None ∧ m2 !! i = None.
  Proof.
    unfold union_with, finmap_union. rewrite (merge_spec _).
    destruct (m1 !! i), (m2 !! i); compute; intuition congruence.
  Qed.

  Global Instance: LeftId (=) ∅ (union_with f : M A → M A → M A) := _.
  Global Instance: RightId (=) ∅ (union_with f : M A → M A → M A) := _.
  Global Instance:
    Commutative (=) f → Commutative (=) (union_with f : M A → M A → M A) := _.
  Global Instance:
    Associative (=) f → Associative (=) (union_with f : M A → M A → M A) := _.
  Global Instance:
    Idempotent (=) f → Idempotent (=) (union_with f : M A → M A → M A) := _.
End union_intersection.
End finmap.

(** * The finite map tactic *)
(** The tactic [simplify_map by tac] simplifies finite map expressions
occuring in the conclusion and assumptions. It uses [tac] to discharge generated
inequalities. *)
Tactic Notation "simplify_map" "by" tactic(T) := repeat
  match goal with
  | _ => progress simplify_equality
  | H : context[ ∅ !! _ ] |- _ => rewrite lookup_empty in H
  | H : context[ (<[_:=_]>_) !! _ ] |- _ => rewrite lookup_insert in H
  | H : context[ (<[_:=_]>_) !! _ ] |- _ => rewrite lookup_insert_ne in H by T
  | H : context[ (delete _ _) !! _ ] |- _ => rewrite lookup_delete in H
  | H : context[ (delete _ _) !! _ ] |- _ => rewrite lookup_delete_ne in H by T
  | H : context[ {[ _ ]} !! _ ] |- _ => rewrite lookup_singleton in H
  | H : context[ {[ _ ]} !! _ ] |- _ => rewrite lookup_singleton_ne in H by T
  | |- context[ ∅ !! _ ] => rewrite lookup_empty
  | |- context[ (<[_:=_]>_) !! _ ] => rewrite lookup_insert
  | |- context[ (<[_:=_]>_) !! _ ] => rewrite lookup_insert_ne by T
  | |- context[ (delete _ _) !! _ ] => rewrite lookup_delete
  | |- context[ (delete _ _) !! _ ] => rewrite lookup_delete_ne by T
  | |- context[ {[ _ ]} !! _ ] => rewrite lookup_singleton
  | |- context[ {[ _ ]} !! _ ] => rewrite lookup_singleton_ne by T
  end.
Tactic Notation "simplify_map" := simplify_map by auto.
