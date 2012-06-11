Require Export prelude.

Class FinMap K M `{∀ A, Empty (M A)} `{Lookup K M} `{FMap M} 
    `{PartialAlter K M} `{∀ A, Dom K (M A)} `{Merge M} := {
  finmap_eq {A} (m1 m2 : M A) : (∀ i, m1 !! i = m2 !! i) → m1 = m2;
  lookup_empty {A} i : (∅ : M A) !! i = None;
  lookup_partial_alter {A} f (m : M A) i : partial_alter f i m !! i = f (m !! i);
  lookup_partial_alter_ne {A} f (m : M A) i j : i ≠ j → partial_alter f i m !! j = m !! j;
  lookup_fmap {A B} (f : A → B) (m : M A) i : (f <$> m) !! i = f <$> m !! i;
  elem_of_dom C {A} `{Collection K C} (m : M A) i : i ∈ dom C m ↔ is_Some (m !! i);
  merge_spec {A} f `{!PropHolds (f None None = None)} 
    (m1 m2 : M A) i : merge f m1 m2 !! i = f (m1 !! i) (m2 !! i)
}.

Instance finmap_alter `{PartialAlter K M} : Alter K M := λ A f, partial_alter (fmap f).
Instance finmap_insert `{PartialAlter K M} : Insert K M := λ A k x, partial_alter (λ _, Some x) k.
Instance finmap_delete `{PartialAlter K M} {A} : Delete K (M A) := partial_alter (λ _, None).
Instance finmap_singleton `{PartialAlter K M} {A} `{Empty (M A)} : Singleton (K * A) (M A) := λ p,
  partial_alter (λ _, Some (snd p)) (fst p) ∅.

Definition insert_list `{Insert K M} {A} (l : list (K * A)) (m : M A) : M A := fold_right (λ p, <[ fst p := snd p ]>) m l.

Instance finmap_union `{Merge M} : UnionWith M := λ A f, merge (union_with f).
Instance finmap_intersect `{Merge M} : IntersectWith M := λ A f, merge (intersect_with f).

Section finmap.
  Context `{FinMap K M} `{∀ i j : K, Decision (i = j)} {A : Type}.

  Global Instance finmap_subseteq: SubsetEq (M A) := λ m n, ∀ i x, m !! i = Some x → n !! i = Some x.
  Global Instance: BoundedPreOrder (M A).
  Proof. split. firstorder. intros m i x. rewrite lookup_empty. discriminate. Qed.

  Lemma not_elem_of_dom C `{Collection K C} (m : M A) i : i ∉ dom C m ↔ m !! i = None.
  Proof. now rewrite (elem_of_dom C), eq_None_not_Some. Qed.

  Lemma finmap_empty (m : M A) : (∀ i, m !! i = None) → m = ∅.
  Proof. intros Hm. apply finmap_eq. intros. now rewrite Hm, lookup_empty. Qed.
  Lemma dom_empty C `{Collection K C} : dom C (∅ : M A) ≡ ∅.
  Proof. split; intro. rewrite (elem_of_dom C), lookup_empty. simplify_is_Some. simplify_elem_of. Qed.
  Lemma dom_empty_inv C `{Collection K C} (m : M A) : dom C m ≡ ∅ → m = ∅.
  Proof. intros E. apply finmap_empty. intros. apply (not_elem_of_dom C). rewrite E. simplify_elem_of. Qed.

  Lemma lookup_empty_not i : ¬is_Some ((∅ : M A) !! i).
  Proof. rewrite lookup_empty. simplify_is_Some. Qed.
  Lemma lookup_empty_Some i (x : A) : ¬∅ !! i = Some x.
  Proof. rewrite lookup_empty. discriminate. Qed.

  Lemma lookup_singleton i (x : A) : {{ (i, x) }} !! i = Some x.
  Proof. unfold singleton, finmap_singleton. apply lookup_partial_alter. Qed.
  Lemma lookup_singleton_ne i j (x : A) : i ≠ j → {{ (i, x) }} !! j = None.
  Proof.
    unfold singleton, finmap_singleton.
    intros. rewrite <-(lookup_empty j). now apply lookup_partial_alter_ne.
  Qed.
  Lemma lookup_ne (m : M A) i j : m !! i ≠ m !! j → i ≠ j.
  Proof. congruence. Qed.

  Lemma partial_alter_compose (m : M A) i f g :
    partial_alter (f ∘ g) i m = partial_alter f i (partial_alter g i m).
  Proof.
    intros. apply finmap_eq. intros ii. case (decide (i = ii)).
     intros. subst. now rewrite !lookup_partial_alter.
    intros. now rewrite !lookup_partial_alter_ne.
  Qed.
  Lemma partial_alter_comm (m : M A) i j f g :
    i ≠ j → partial_alter f i (partial_alter g j m) = partial_alter g j (partial_alter f i m).
  Proof.
    intros. apply finmap_eq. intros jj. case (decide (jj = j)).
     intros. subst. now rewrite lookup_partial_alter_ne, !lookup_partial_alter, lookup_partial_alter_ne.
    intros. case (decide (jj = i)).
     intros. subst. now rewrite lookup_partial_alter, !lookup_partial_alter_ne, lookup_partial_alter by congruence.
    intros. now rewrite !lookup_partial_alter_ne by congruence.
  Qed.
  Lemma partial_alter_self_alt (m : M A) i x :
    x = m !! i → partial_alter (λ _, x) i m = m.
  Proof.
    intros. apply finmap_eq. intros ii. case (decide (i = ii)).
     intros. subst. now rewrite lookup_partial_alter.
    intros. now rewrite lookup_partial_alter_ne.
  Qed.
  Lemma partial_alter_self (m : M A) i : partial_alter (λ _, m !! i) i m = m.
  Proof. now apply partial_alter_self_alt. Qed.

  Lemma lookup_insert (m : M A) i x : <[ i := x ]> m !! i = Some x.
  Proof. unfold insert. apply lookup_partial_alter. Qed.
  Lemma lookup_insert_rev (m : M A) i x y : <[ i := x ]> m !! i = Some y → x = y.
  Proof. rewrite lookup_insert. congruence. Qed.
  Lemma lookup_insert_ne (m : M A) i j x : i ≠ j → <[ i := x ]> m !! j = m !! j.
  Proof. unfold insert. apply lookup_partial_alter_ne. Qed.
  Lemma insert_comm (m : M A) i j x y : i ≠ j → <[ i := x ]>(<[ j := y ]>m) = <[ j := y ]>(<[ i := x ]>m).
  Proof. apply partial_alter_comm. Qed.

  Lemma lookup_delete (m : M A) i : delete i m !! i = None.
  Proof. apply lookup_partial_alter. Qed.
  Lemma lookup_delete_Some (m : M A) i j : is_Some (delete i m !! j) → i ≠ j.
  Proof. intros Hm ?. subst. rewrite lookup_delete in Hm. now apply None_not_is_Some in Hm. Qed.
  Lemma lookup_delete_ne (m : M A) i j : i ≠ j → delete i m !! j = m !! j.
  Proof. apply lookup_partial_alter_ne. Qed.
  Lemma delete_empty i : delete i (∅ : M A) = ∅.
  Proof. rewrite <-(partial_alter_self ∅) at 2. now rewrite lookup_empty. Qed.
  Lemma delete_singleton i (x : A) : delete i {{ (i, x) }} = ∅.
  Proof. setoid_rewrite <-partial_alter_compose. apply delete_empty. Qed.
  Lemma delete_comm (m : M A) i j : delete i (delete j m) = delete j (delete i m).
  Proof. destruct (decide (i = j)). now subst. now apply partial_alter_comm. Qed.
  Lemma delete_partial_alter (m : M A) i f : m !! i = None → delete i (partial_alter f i m) = m.
  Proof.
    intros. unfold delete, finmap_delete. rewrite <-partial_alter_compose. 
    rapply partial_alter_self_alt. congruence.
  Qed.
  Lemma delete_partial_alter_dom C `{Collection K C} (m : M A) i f : 
    i ∉ dom C m → delete i (partial_alter f i m) = m.
  Proof. rewrite (not_elem_of_dom C). apply delete_partial_alter. Qed.
  Lemma delete_insert (m : M A) i x : m !! i = None → delete i (<[i := x]>m) = m.
  Proof. apply delete_partial_alter. Qed.
  Lemma delete_insert_dom C `{Collection K C} (m : M A) i x : i ∉ dom C m → delete i (<[i := x]>m) = m.
  Proof. rewrite (not_elem_of_dom C). apply delete_partial_alter. Qed.
  Lemma insert_delete (m : M A) i x : m !! i = Some x → <[i := x]>(delete i m) = m.
  Proof.
    intros Hmi. unfold delete, finmap_delete, insert, finmap_insert.
    rewrite <-partial_alter_compose. unfold compose. rewrite <-Hmi.
    now apply partial_alter_self_alt.
  Qed.

  Lemma elem_of_dom_delete C `{Collection K C} (m : M A) i j : i ∈ dom C (delete j m) ↔ i ≠ j ∧ i ∈ dom C m.
  Proof.
    rewrite !(elem_of_dom C). split.
     intros. assert (j ≠ i) by (eapply lookup_delete_Some; eauto).
     erewrite <-lookup_delete_ne; eauto.
    intros [??]. now rewrite lookup_delete_ne by congruence.
  Qed.
  Lemma not_elem_of_dom_delete C `{Collection K C} (m : M A) i : i ∉ dom C (delete i m).
  Proof. apply (not_elem_of_dom C), lookup_delete. Qed.

  Lemma finmap_ind C (P : M A → Prop) `{FinCollection K C} :
    P ∅ → (∀ i x m, i ∉ dom C m → P m → P (<[ i := x ]>m)) → ∀ m, P m.
  Proof.
    intros Hemp Hinsert.
    intros m. apply (collection_ind (λ X, ∀ m, dom C m ≡ X → P m)) with (dom C m).
       solve_proper.
      clear m. intros m Hm. rewrite finmap_empty. easy.
      intros. rewrite <-(not_elem_of_dom C), Hm. now simplify_elem_of.
     clear m. intros i X Hi IH m Hdom.
     assert (is_Some (m !! i)) as [x Hx].
      apply (elem_of_dom C). rewrite Hdom. clear Hdom. now simplify_elem_of.
     rewrite <-(insert_delete m i x) by easy. apply Hinsert.
      now apply (not_elem_of_dom_delete C).
     apply IH. apply elem_of_equiv. intros.
     rewrite (elem_of_dom_delete C). rewrite Hdom.
     clear Hdom. simplify_elem_of.
    easy.
  Qed.

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
      (∀ i, f (m1 !! i) (m2 !! i) = f (m2 !! i) (m1 !! i)) → merge f m1 m2 = merge f m2 m1.
    Proof. intros. apply finmap_eq. intros. now rewrite !(merge_spec f). Qed.
    Global Instance: Commutative (=) f → Commutative (=) (merge f).
    Proof. intros ???. apply merge_comm. intros. now apply (commutative f). Qed.

    Lemma merge_assoc m1 m2 m3 :
      (∀ i, f (m1 !! i) (f (m2 !! i) (m3 !! i)) = f (f (m1 !! i) (m2 !! i)) (m3 !! i)) → 
      merge f m1 (merge f m2 m3) = merge f (merge f m1 m2) m3.
    Proof. intros. apply finmap_eq. intros. now rewrite !(merge_spec f). Qed.
    Global Instance: Associative (=) f → Associative (=) (merge f).
    Proof. intros ????. apply merge_assoc. intros. now apply (associative f). Qed.
  End merge.

  Section union_intersect.
    Context (f : A → A → A).

    Lemma finmap_union_merge m1 m2 i x y :
      m1 !! i = Some x → m2 !! i = Some y → union_with f m1 m2 !! i = Some (f x y).
    Proof. intros Hx Hy. unfold union_with, finmap_union. now rewrite (merge_spec _), Hx, Hy. Qed.   
    Lemma finmap_union_l m1 m2 i x :
      m1 !! i = Some x → m2 !! i = None → union_with f m1 m2 !! i = Some x.
    Proof. intros Hx Hy. unfold union_with, finmap_union. now rewrite (merge_spec _), Hx, Hy. Qed.
    Lemma finmap_union_r m1 m2 i y :
      m1 !! i = None → m2 !! i = Some y → union_with f m1 m2 !! i = Some y.
    Proof. intros Hx Hy. unfold union_with, finmap_union. now rewrite (merge_spec _), Hx, Hy. Qed.
    Lemma finmap_union_None m1 m2 i :
      union_with f m1 m2 !! i = None ↔ m1 !! i = None ∧ m2 !! i = None.
    Proof.
      unfold union_with, finmap_union. rewrite (merge_spec _).
      destruct (m1 !! i), (m2 !! i); compute; intuition congruence.
    Qed.

    Global Instance: LeftId (=) ∅ (union_with f : M A → M A → M A) := _.
    Global Instance: RightId (=) ∅ (union_with f : M A → M A → M A) := _.
    Global Instance: Commutative (=) f → Commutative (=) (union_with f : M A → M A → M A) := _.
    Global Instance: Associative (=) f → Associative (=) (union_with f : M A → M A → M A) := _.
    Global Instance: Idempotent (=) f → Idempotent (=) (union_with f : M A → M A → M A) := _.
  End union_intersect.
End finmap.
