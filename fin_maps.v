(* Copyright (c) 2012, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** Finite maps associate data to keys. This file defines an interface for
finite maps and collects some theory on it. Most importantly, it proves useful
induction principles for finite maps and implements the tactic [simplify_map]
to simplify goals involving finite maps. *)
Require Export prelude.
(** * Axiomatization of finite maps *)
(** We require Leibniz equality to be extensional on finite maps. This of
course limits the space of finite map implementations, but since we are mainly
interested in finite maps with numbers as indexes, we do not consider this to
be a serious limitation. The main application of finite maps is to implement
the memory, where extensionality of Leibniz equality is very important for a
convenient use in the assertions of our axiomatic semantics. *)

(** Finiteness is axiomatized by requiring each map to have a finite domain.
Since we may have multiple implementations of finite sets, the [dom] function is
parametrized by an implementation of finite sets over the map's key type. *)

(** Finite map implementations are required to implement the [merge] function
which enables us to give a generic implementation of [union_with],
[intersection_with], and [difference_with]. *)

Class FinMap K M `{!FMap M}
    `{∀ A, Lookup K (M A) A} `{∀ A, Empty (M A)}
    `{∀ A, PartialAlter K (M A) A} `{∀ A, Dom K (M A)} `{!Merge M}
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
  elem_of_dom C {A} `{Collection K C} (m : M A) i :
    i ∈ dom C m ↔ is_Some (m !! i);
  merge_spec {A} f `{!PropHolds (f None None = None)}
    (m1 m2 : M A) i : merge f m1 m2 !! i = f (m1 !! i) (m2 !! i)
}.

(** * Derived operations *)
(** All of the following functions are defined in a generic way for arbitrary
finite map implementations. These generic implementations do not cause a
significant performance loss to make including them in the finite map interface
worthwhile. *)
Instance finmap_insert `{PartialAlter K M A} : Insert K M A := λ i x,
  partial_alter (λ _, Some x) i.
Instance finmap_alter `{PartialAlter K M A} : Alter K M A := λ f,
  partial_alter (fmap f).
Instance finmap_delete `{PartialAlter K M A} : Delete K M :=
  partial_alter (λ _, None).

Instance finmap_singleton `{PartialAlter K M A}
  `{Empty M} : Singleton (K * A) M := λ p, <[fst p:=snd p]>∅.
Definition list_to_map `{Insert K M A} `{Empty M}
  (l : list (K * A)) : M := insert_list l ∅.

Instance finmap_union_with `{Merge M} : UnionWith M := λ A f,
  merge (union_with f).
Instance finmap_intersection_with `{Merge M} : IntersectionWith M := λ A f,
  merge (intersection_with f).
Instance finmap_difference_with `{Merge M} : DifferenceWith M := λ A f,
  merge (difference_with f).

(** The relation [intersection_forall R] on finite maps describes that the
relation [R] holds for each pair in the intersection. *)
Definition intersection_forall `{Lookup K M A} (R : relation A) : relation M :=
  λ m1 m2, ∀ i x1 x2, m1 !! i = Some x1 → m2 !! i = Some x2 → R x1 x2.
Instance finmap_disjoint `{∀ A, Lookup K (M A) A} : Disjoint (M A) := λ A,
  intersection_forall (λ _ _, False).

(** The union of two finite maps only has a meaningful definition for maps
that are disjoint. However, as working with partial functions is inconvenient
in Coq, we define the union as a total function. In case both finite maps
have a value at the same index, we take the value of the first map. *)
Instance finmap_union `{Merge M} {A} : Union (M A) :=
  union_with (λ x _, x).
Instance finmap_intersection `{Merge M} {A} : Intersection (M A) :=
  union_with (λ x _, x).
(** The difference operation removes all values from the first map whose
index contains a value in the second map as well. *)
Instance finmap_difference `{Merge M} {A} : Difference (M A) :=
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

  Lemma not_elem_of_dom C `{Collection K C} (m : M A) i :
    i ∉ dom C m ↔ m !! i = None.
  Proof. by rewrite (elem_of_dom C), eq_None_not_Some. Qed.

  Lemma finmap_empty (m : M A) : (∀ i, m !! i = None) → m = ∅.
  Proof. intros Hm. apply finmap_eq. intros. by rewrite Hm, lookup_empty. Qed.
  Lemma dom_empty C `{Collection K C} : dom C (∅ : M A) ≡ ∅.
  Proof.
    split; intro.
    * rewrite (elem_of_dom C), lookup_empty. by inversion 1.
    * solve_elem_of.
  Qed.
  Lemma dom_empty_inv C `{Collection K C} (m : M A) : dom C m ≡ ∅ → m = ∅.
  Proof.
    intros E. apply finmap_empty. intros. apply (not_elem_of_dom C).
    rewrite E. solve_elem_of.
  Qed.

  Lemma lookup_empty_not i : ¬is_Some ((∅ : M A) !! i).
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
      partial_alter f i (partial_alter g j m)
    = partial_alter g j (partial_alter f i m).
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
  Lemma delete_partial_alter_dom C `{Collection K C} (m : M A) i f :
    i ∉ dom C m → delete i (partial_alter f i m) = m.
  Proof. rewrite (not_elem_of_dom C). apply delete_partial_alter. Qed.
  Lemma delete_insert (m : M A) i x :
    m !! i = None → delete i (<[i:=x]>m) = m.
  Proof. apply delete_partial_alter. Qed.
  Lemma delete_insert_dom C `{Collection K C} (m : M A) i x :
    i ∉ dom C m → delete i (<[i:=x]>m) = m.
  Proof. rewrite (not_elem_of_dom C). apply delete_partial_alter. Qed.
  Lemma insert_delete (m : M A) i x :
    m !! i = Some x → <[i:=x]>(delete i m) = m.
  Proof.
    intros Hmi. unfold delete, finmap_delete, insert, finmap_insert.
    rewrite <-partial_alter_compose. unfold compose. rewrite <-Hmi.
    by apply partial_alter_self_alt.
  Qed.

  Lemma elem_of_dom_delete C `{Collection K C} (m : M A) i j :
    i ∈ dom C (delete j m) ↔ i ≠ j ∧ i ∈ dom C m.
  Proof.
    rewrite !(elem_of_dom C), <-!not_eq_None_Some.
    rewrite lookup_delete_None. intuition.
  Qed.
  Lemma not_elem_of_dom_delete C `{Collection K C} (m : M A) i :
    i ∉ dom C (delete i m).
  Proof. apply (not_elem_of_dom C), lookup_delete. Qed.

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

  (** * Properties of the merge operation *)
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
    Global Instance: Idempotent (=) f → Idempotent (=) (merge f).
    Proof. intros ??. apply finmap_eq. intros. by rewrite !(merge_spec f). Qed.

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
    Proof. intros. apply finmap_eq. intros. by rewrite !(merge_spec f). Qed.
    Global Instance: Commutative (=) f → Commutative (=) (merge f).
    Proof. intros ???. apply merge_comm. intros. by apply (commutative f). Qed.

    Lemma merge_assoc m1 m2 m3 :
      (∀ i, f (m1 !! i) (f (m2 !! i) (m3 !! i)) =
            f (f (m1 !! i) (m2 !! i)) (m3 !! i)) →
      merge f m1 (merge f m2 m3) = merge f (merge f m1 m2) m3.
    Proof. intros. apply finmap_eq. intros. by rewrite !(merge_spec f). Qed.
    Global Instance: Associative (=) f → Associative (=) (merge f).
    Proof. intros ????. apply merge_assoc. intros. by apply (associative f). Qed.
  End merge_with.
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
  end.
Tactic Notation "simpl_map" := simpl_map by auto.

Tactic Notation "simplify_map_equality" "by" tactic3(tac) := repeat
  match goal with
  | _ => progress simpl_map by tac
  | _ => progress simplify_equality
  | H1 : ?m1 !! ?i = Some ?x, H2 : ?m2 !! ?i = Some ?y |- _ =>
    let H3 := fresh in
    feed pose proof (lookup_weaken_inv m1 m2 i x y) as H3;
      [done | by tac | done | ];
    clear H2; symmetry in H3
  end.
Tactic Notation "simplify_map_equality" := simplify_map_equality by auto.

Section finmap_more.
  Context `{FinMap K M} {A : Type}.

  (** * Properties on the relation [intersection_forall] *)
  Section intersection_forall.
    Context (R : relation A).

    Global Instance intersection_forall_sym:
      Symmetric R → Symmetric (intersection_forall R).
    Proof. firstorder auto. Qed.
    Lemma intersection_forall_empty_l (m : M A) : intersection_forall R ∅ m.
    Proof. intros ???. by simpl_map. Qed.
    Lemma intersection_forall_empty_r (m : M A) : intersection_forall R m ∅.
    Proof. intros ???. by simpl_map. Qed.

    (** Due to the finiteness of finite maps, we can extract a witness are
    property does not hold for the intersection. *)
    Lemma not_intersection_forall `{∀ x y, Decision (R x y)} (m1 m2 : M A) :
      ¬intersection_forall R m1 m2
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

  (** * Properties on the disjoint maps *)
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
    rewrite not_intersection_forall.
    * firstorder auto.
    * right. auto.
  Qed.

  Global Instance: Symmetric (@disjoint (M A) _).
  Proof. apply intersection_forall_sym. auto. Qed.
  Lemma finmap_disjoint_empty_l (m : M A) : ∅ ⊥ m.
  Proof. apply intersection_forall_empty_l. Qed.
  Lemma finmap_disjoint_empty_r (m : M A) : m ⊥ ∅.
  Proof. apply intersection_forall_empty_r. Qed.

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

  (** * Properties of the union and intersection operation *)
  Section union_intersection_with.
    Context (f : A → A → A).

    Lemma finmap_union_with_Some m1 m2 i x y :
      m1 !! i = Some x →
      m2 !! i = Some y →
      union_with f m1 m2 !! i = Some (f x y).
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
    Lemma finmap_union_with_None m1 m2 i :
      union_with f m1 m2 !! i = None ↔ m1 !! i = None ∧ m2 !! i = None.
    Proof.
      unfold union_with, finmap_union_with. rewrite (merge_spec _).
      destruct (m1 !! i), (m2 !! i); compute; intuition congruence.
    Qed.

    Global Instance: LeftId (=) ∅ (@union_with M _ _ f).
    Proof. unfold union_with, finmap_union_with. apply _. Qed.
    Global Instance: RightId (=) ∅ (@union_with M _ _ f).
    Proof. unfold union_with, finmap_union_with. apply _. Qed.
    Global Instance: Commutative (=) f → Commutative (=) (@union_with M _ _ f).
    Proof. unfold union_with, finmap_union_with. apply _. Qed.
    Global Instance: Associative (=) f → Associative (=) (@union_with M _ _ f).
    Proof. unfold union_with, finmap_union_with. apply _. Qed.
    Global Instance: Idempotent (=) f → Idempotent (=) (@union_with M _ _ f).
    Proof. unfold union_with, finmap_union_with. apply _. Qed.
  End union_intersection_with.

  Global Instance: LeftId (=) ∅ (@union (M A) _) := _.
  Global Instance: RightId (=) ∅ (@union (M A) _) := _.
  Global Instance: Associative (=) (@union (M A) _) := _.
  Global Instance: Idempotent (=) (@union (M A) _) := _.

  Lemma finmap_union_Some_raw (m1 m2 : M A) i x :
    (m1 ∪ m2) !! i = Some x ↔
      m1 !! i = Some x ∨ (m1 !! i = None ∧ m2 !! i = Some x).
  Proof.
    unfold union, finmap_union, union_with, finmap_union_with.
    rewrite (merge_spec _).
    destruct (m1 !! i), (m2 !! i); compute; try intuition congruence.
  Qed.
  Lemma finmap_union_None (m1 m2 : M A) i :
    (m1 ∪ m2) !! i = None ↔ m1 !! i = None ∧ m2 !! i = None.
  Proof. apply finmap_union_with_None. Qed.

  Lemma finmap_union_Some (m1 m2 : M A) i x :
    m1 ⊥ m2 →
    (m1 ∪ m2) !! i = Some x ↔ m1 !! i = Some x ∨ m2 !! i = Some x.
  Proof.
    intros Hdisjoint. rewrite finmap_union_Some_raw.
    intuition eauto using finmap_disjoint_Some_r.
  Qed.

  Lemma finmap_union_Some_l (m1 m2 : M A) i x :
    m1 ⊥ m2 →
    m1 !! i = Some x →
    (m1 ∪ m2) !! i = Some x.
  Proof. intro. rewrite finmap_union_Some; intuition. Qed.
  Lemma finmap_union_Some_r (m1 m2 : M A) i x :
    m1 ⊥ m2 →
    m2 !! i = Some x →
    (m1 ∪ m2) !! i = Some x.
  Proof. intro. rewrite finmap_union_Some; intuition. Qed.

  Lemma finmap_union_comm (m1 m2 : M A) :
    m1 ⊥ m2 →
    m1 ∪ m2 = m2 ∪ m1.
  Proof.
    intros Hdisjoint. apply (merge_comm (union_with (λ x _, x))).
    intros i. specialize (Hdisjoint i).
    destruct (m1 !! i), (m2 !! i); compute; naive_solver.
  Qed.

  Lemma finmap_subseteq_union (m1 m2 : M A) :
    m1 ⊆ m2 →
    m1 ∪ m2 = m2.
  Proof.
    intros Hm1m2.
    apply finmap_eq. intros i. apply option_eq. intros x.
    rewrite finmap_union_Some_raw. split; [by intuition |].
    intros Hm2. specialize (Hm1m2 i).
    destruct (m1 !! i) as [y|]; [| by auto].
    rewrite (Hm1m2 y eq_refl) in Hm2. intuition congruence.
  Qed.
  Lemma finmap_subseteq_union_l (m1 m2 : M A) :
    m1 ⊥ m2 →
    m1 ⊆ m1 ∪ m2.
  Proof. intros ? i x. rewrite finmap_union_Some_raw. intuition. Qed.
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
    setoid_rewrite finmap_union_None. naive_solver.
  Qed.
  Lemma finmap_disjoint_union_r (m1 m2 m3 : M A) :
    m1 ⊥ m2 ∪ m3 ↔ m1 ⊥ m2 ∧ m1 ⊥ m3.
  Proof.
    rewrite !finmap_disjoint_alt.
    setoid_rewrite finmap_union_None. naive_solver.
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
    destruct (proj1 (finmap_union_Some m2 m3 b v Hm2m3)) as [E2|E2].
    * rewrite <-E. by apply finmap_union_Some_l.
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

  Lemma finmap_union_singleton_l (m : M A) i x :
    <[i:=x]>m = {[(i,x)]} ∪ m.
  Proof.
    apply finmap_eq. intros j. apply option_eq. intros y.
    rewrite finmap_union_Some_raw.
    destruct (decide (i = j)); simplify_map_equality; intuition congruence.
  Qed.
  Lemma finmap_union_singleton_r (m : M A) i x :
    m !! i = None →
    <[i:=x]>m = m ∪ {[(i,x)]}.
  Proof.
    intro. rewrite finmap_union_singleton_l, finmap_union_comm; [done |].
    by apply finmap_disjoint_singleton_l.
  Qed.

  Lemma finmap_disjoint_insert_l (m1 m2 : M A) i x :
    <[i:=x]>m1 ⊥ m2 ↔ m2 !! i = None ∧ m1 ⊥ m2.
  Proof.
    rewrite finmap_union_singleton_l.
    by rewrite finmap_disjoint_union_l, finmap_disjoint_singleton_l.
  Qed.
  Lemma finmap_disjoint_insert_r (m1 m2 : M A) i x :
    m1 ⊥ <[i:=x]>m2 ↔ m1 !! i = None ∧ m1 ⊥ m2.
  Proof.
    rewrite finmap_union_singleton_l.
    by rewrite finmap_disjoint_union_r, finmap_disjoint_singleton_r.
  Qed.

  Lemma finmap_disjoint_insert_l_2 (m1 m2 : M A) i x :
    m2 !! i = None → m1 ⊥ m2 → <[i:=x]>m1 ⊥ m2.
  Proof. by rewrite finmap_disjoint_insert_l. Qed.
  Lemma finmap_disjoint_insert_r_2 (m1 m2 : M A) i x :
    m1 !! i = None → m1 ⊥ m2 → m1 ⊥ <[i:=x]>m2.
  Proof. by rewrite finmap_disjoint_insert_r. Qed.

  Lemma finmap_union_insert_l (m1 m2 : M A) i x :
    <[i:=x]>(m1 ∪ m2) = <[i:=x]>m1 ∪ m2.
  Proof. by rewrite !finmap_union_singleton_l, (associative (∪)). Qed.
  Lemma finmap_union_insert_r (m1 m2 : M A) i x :
    m1 !! i = None →
    <[i:=x]>(m1 ∪ m2) = m1 ∪ <[i:=x]>m2.
  Proof.
    intro. rewrite !finmap_union_singleton_l, !(associative (∪)).
    rewrite (finmap_union_comm m1); [done |].
    by apply finmap_disjoint_singleton_r.
  Qed.

  Lemma finmap_insert_list_union l (m : M A) :
    insert_list l m = list_to_map l ∪ m.
  Proof.
    induction l; simpl.
    * by rewrite (left_id _ _).
    * by rewrite IHl, finmap_union_insert_l.
  Qed.

  Lemma finmap_subseteq_insert (m1 m2 : M A) i x :
    m1 !! i = None → m1 ⊆ m2 → m1 ⊆ <[i:=x]>m2.
  Proof.
    intros ?? j. destruct (decide (j = i)).
    * intros y ?. congruence.
    * intros. simpl_map. auto.
  Qed.

  (** * Properties of the delete operation *)
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
     rewrite ?finmap_union_Some_raw; simpl_map; intuition congruence.
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

  (** * Properties of the conversion from lists to maps *)
  Lemma finmap_disjoint_list_to_map_l (m : M A) ixs :
    list_to_map ixs ⊥ m ↔ Forall (λ ix, m !! fst ix = None) ixs.
  Proof.
    split.
    * induction ixs; simpl; rewrite ?finmap_disjoint_insert_l in *; intuition.
    * induction 1; simpl.
      + apply finmap_disjoint_empty_l.
      + rewrite finmap_disjoint_insert_l. auto.
  Qed.
  Lemma finmap_disjoint_list_to_map_r (m : M A) ixs :
    m ⊥ list_to_map ixs ↔ Forall (λ ix, m !! fst ix = None) ixs.
  Proof. by rewrite (symmetry_iff (⊥)), finmap_disjoint_list_to_map_l. Qed.

  Lemma finmap_disjoint_list_to_map_zip_l (m : M A) is xs :
    same_length is xs →
    list_to_map (zip is xs) ⊥ m ↔ Forall (λ i, m !! i = None) is.
  Proof.
    intro. rewrite finmap_disjoint_list_to_map_l.
    rewrite <-(zip_fst is xs) at 2 by done.
    by rewrite Forall_fmap.
  Qed.
  Lemma finmap_disjoint_list_to_map_zip_r (m : M A) is xs :
    same_length is xs →
    m ⊥ list_to_map (zip is xs) ↔ Forall (λ i, m !! i = None) is.
  Proof.
    intro. by rewrite (symmetry_iff (⊥)), finmap_disjoint_list_to_map_zip_l.
  Qed.
  Lemma finmap_disjoint_list_to_map_zip_l_2 (m : M A) is xs :
    same_length is xs →
    Forall (λ i, m !! i = None) is →
    list_to_map (zip is xs) ⊥ m.
  Proof. intro. by rewrite finmap_disjoint_list_to_map_zip_l. Qed.
  Lemma finmap_disjoint_list_to_map_zip_r_2 (m : M A) is xs :
    same_length is xs →
    Forall (λ i, m !! i = None) is →
    m ⊥ list_to_map (zip is xs).
  Proof. intro. by rewrite finmap_disjoint_list_to_map_zip_r. Qed.

  (** * Properties with respect to vectors of elements *)
  Lemma finmap_union_delete_vec {n} (ms : vec (M A) n) (i : fin n) :
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

  Lemma finmap_union_insert_vec {n} (ms : vec (M A) n) (i : fin n) m :
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

  (** * Properties of the difference operation *)
  Lemma finmap_difference_Some (m1 m2 : M A) i x :
    (m1 ∖ m2) !! i = Some x ↔ m1 !! i = Some x ∧ m2 !! i = None.
  Proof.
    unfold difference, finmap_difference, difference_with, finmap_difference_with.
    rewrite (merge_spec _).
    destruct (m1 !! i), (m2 !! i); compute; intuition congruence.
  Qed.

  Lemma finmap_disjoint_difference_l (m1 m2 m3 : M A) :
    m2 ⊆ m3 → m1 ∖ m3 ⊥ m2.
  Proof.
    intros E i. specialize (E i).
    unfold difference, finmap_difference, difference_with, finmap_difference_with.
    rewrite (merge_spec _).
    destruct (m1 !! i), (m2 !! i), (m3 !! i); compute; try intuition congruence.
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
    unfold difference, finmap_difference, difference_with, finmap_difference_with.
    rewrite finmap_union_Some_raw, (merge_spec _).
    destruct (m1 !! i) as [v'|], (m2 !! i);
      try specialize (Hm1m2 v'); compute; intuition congruence.
  Qed.
End finmap_more.

(** The tactic [simplify_finmap_disjoint] simplifies occurences of [disjoint]
in the conclusion and hypotheses that involve the union, insert, or singleton
operation. *)
Ltac decompose_finmap_disjoint := repeat
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
    apply Forall_inv in H; destruct H
  end.
