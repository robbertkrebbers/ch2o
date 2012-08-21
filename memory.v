Require Export nmap list.
Open Scope N_scope.

Notation mem := (Nmap N) (only parsing).

(* Disjoint *)
Definition mem_disjoint (m1 m2 : mem) := ∀ b, m1 !! b = None ∨ m2 !! b = None.

Instance: Symmetric mem_disjoint.
Proof. intros ?? H b. destruct (H b); intuition. Qed.
Lemma mem_disjoint_empty_l m : mem_disjoint ∅ m.
Proof. intros ?. simplify_map. auto. Qed.
Lemma mem_disjoint_empty_r m : mem_disjoint m ∅.
Proof. intros ?. simplify_map. auto. Qed.
Hint Resolve mem_disjoint_empty_l mem_disjoint_empty_r : mem.

Lemma mem_disjoint_Some_l m1 m2 b x:
  mem_disjoint m1 m2 → m1 !! b = Some x → m2 !! b = None.
Proof. intros H ?. specialize (H b). intuition congruence. Qed.
Lemma mem_disjoint_Some_r m1 m2 b x:
  mem_disjoint m1 m2 → m2 !! b = Some x → m1 !! b = None.
Proof. intros H ?. specialize (H b). intuition congruence. Qed.

Lemma mem_disjoint_singleton_l m b v :
  mem_disjoint {[(b, v)]} m ↔ m !! b = None.
Proof.
  split.
  * intros H. now destruct (H b); simplify_map.
  * intros ? b'. destruct (decide (b = b')); simplify_map; auto.
Qed.
Lemma mem_disjoint_singleton_r m b v :
  mem_disjoint m {[(b, v)]} ↔ m !! b = None.
Proof. now rewrite (symmetry_iff mem_disjoint), mem_disjoint_singleton_l. Qed.

(* Union *)
Instance mem_union: Union mem := union_with (λ x _ , x).

Lemma mem_union_Some m1 m2 i x : 
  (m1 ∪ m2) !! i = Some x ↔ m1 !! i = Some x ∨ (m1 !! i = None ∧ m2 !! i = Some x).
Proof.
  unfold union, mem_union, union_with, finmap_union. rewrite (merge_spec _).
  destruct (m1 !! i), (m2 !! i); compute; try intuition congruence.
Qed.
Lemma mem_union_None m1 m2 b : 
  (m1 ∪ m2) !! b = None ↔ m1 !! b = None ∧ m2 !! b = None.
Proof. apply finmap_union_None. Qed.

Lemma mem_union_Some_l m1 m2 b x :
  m1 !! b = Some x → (m1 ∪ m2) !! b = Some x.
Proof. rewrite mem_union_Some. intuition congruence. Qed.
Lemma mem_union_Some_r m1 m2 b x :
  m1 !! b = None → m2 !! b = Some x → (m1 ∪ m2) !! b = Some x.
Proof. rewrite mem_union_Some. intuition congruence. Qed.

Lemma mem_union_Some_inv_l m1 m2 b x :
  (m1 ∪ m2) !! b = Some x → m2 !! b = None → m1 !! b = Some x.
Proof. rewrite mem_union_Some. intuition congruence. Qed.
Lemma mem_union_Some_inv_r m1 m2 b x : 
  (m1 ∪ m2) !! b = Some x → m1 !! b = None → m2 !! b = Some x.
Proof. rewrite mem_union_Some. intuition congruence. Qed.

Lemma mem_union_None_None m1 m2 b :
  m1 !! b = None → m2 !! b = None → (m1 ∪ m2) !! b = None.
Proof. rewrite mem_union_None. intuition. Qed.
Lemma mem_union_None_inv_l m1 m2 b :
  (m1 ∪ m2) !! b = None → m1 !! b = None.
Proof. rewrite mem_union_None. intuition. Qed.
Lemma mem_union_None_inv_r m1 m2 b :
  (m1 ∪ m2) !! b = None → m2 !! b = None.
Proof. rewrite mem_union_None. intuition. Qed.

Hint Resolve
  mem_union_Some_l mem_union_Some_r
  mem_union_Some_inv_l mem_union_Some_inv_r 
  mem_union_None_None : mem.

Instance: LeftId (=) ∅ ((∪) : mem → mem → mem) := _.
Instance: RightId (=) ∅ ((∪) : mem → mem → mem) := _.
Instance: Associative (=) ((∪) : mem → mem → mem) := _.
Instance: Idempotent (=) ((∪) : mem → mem → mem) := _.

Lemma mem_union_comm m1 m2 :
  mem_disjoint m1 m2 → m1 ∪ m2 = m2 ∪ m1.
Proof.
  intros H. apply (merge_comm (union_with (λ x _, x))).
  intros b. generalize (H b).
  destruct (m1 !! b), (m2 !! b); compute; intuition congruence.
Qed.

Lemma mem_subseteq_union (m1 m2 : mem) :
  m1 ⊆ m2 → m1 ∪ m2 = m2.
Proof.
  intros E. apply finmap_eq. intros b. apply option_eq. intros v.
  specialize (E b). rewrite mem_union_Some.
  destruct (m1 !! b), (m2 !! b);
    try (einjection E; [| reflexivity ]); intuition (auto; congruence).
Qed.
Lemma mem_subseteq_union_l (m1 m2 : mem) :
  m1 ⊆ m1 ∪ m2.
Proof.
  intros b v. rewrite mem_union_Some.
  destruct (m1 !! b), (m2 !! b); intuition congruence.
Qed.
Lemma mem_subseteq_union_r (m1 m2 : mem) :
  mem_disjoint m1 m2 → m2 ⊆ m1 ∪ m2.
Proof.
  intros. rewrite mem_union_comm by auto.
  apply mem_subseteq_union_l.
Qed.
Hint Resolve mem_subseteq_union_l mem_subseteq_union_r : mem.

Lemma mem_disjoint_union_l m1 m2 m3 :
  mem_disjoint (m1 ∪ m2) m3 ↔ mem_disjoint m1 m3 ∧ mem_disjoint m2 m3.
Proof. unfold mem_disjoint. setoid_rewrite mem_union_None. firstorder auto. Qed.
Lemma mem_disjoint_union_r m1 m2 m3 :
  mem_disjoint m1 (m2 ∪ m3) ↔ mem_disjoint m1 m2 ∧ mem_disjoint m1 m3.
Proof. unfold mem_disjoint. setoid_rewrite mem_union_None. firstorder auto. Qed.

Lemma mem_union_cancel_l m1 m2 m3 :
  mem_disjoint m1 m3 →
  mem_disjoint m2 m3 →
  m1 ∪ m3 = m2 ∪ m3 →
  m1 = m2.
Proof.
  revert m1 m2 m3.
  cut (∀ m1 m2 m3 b v, 
    mem_disjoint m1 m3 → m1 ∪ m3 = m2 ∪ m3 →
    m1 !! b = Some v → m2 !! b = Some v).
  { intros help ??????. apply finmap_eq. intros i.
    apply option_eq. split; eapply help; eauto with mem. }
  intros m1 m2 m3 b v ? E ?.
  apply mem_union_Some_inv_l with m3.
  * rewrite <-E. eauto with mem.
  * now apply mem_disjoint_Some_l with m1 v.
Qed.
Lemma mem_union_cancel_r m1 m2 m3 :
  mem_disjoint m1 m3 →
  mem_disjoint m2 m3 →
  m3 ∪ m1 = m3 ∪ m2 →
  m1 = m2.
Proof.
  intros ??. rewrite !(mem_union_comm m3) by (symmetry; auto).
  now apply mem_union_cancel_l.
Qed.

Lemma mem_union_insert_l m1 m2 b v :
  <[b:=v]>(m1 ∪ m2) = <[b:=v]>m1 ∪ m2.
Proof.
  apply finmap_eq. intros b'. apply option_eq. intros v'.
  destruct (decide (b = b')); simplify_map;
   rewrite ?mem_union_Some; simplify_map; intuition congruence.
Qed.
Lemma mem_union_insert_r m1 m2 b v :
  m1 !! b = None →
  <[b:=v]>(m1 ∪ m2) = m1 ∪ <[b:=v]>m2.
Proof.
  intros. apply finmap_eq. intros b'. apply option_eq. intros v'.
  destruct (decide (b = b')); simplify_map;
   rewrite ?mem_union_Some; simplify_map; intuition congruence.
Qed.

Lemma mem_union_singleton_l m b v :
  <[b:=v]>m = {[(b,v)]} ∪ m.
Proof. rewrite <-(left_id ∅ (∪) m) at 1. now rewrite mem_union_insert_l. Qed.
Lemma mem_union_singleton_r m b v :
  m !! b = None →
  <[b:=v]>m = m ∪ {[(b,v)]}.
Proof. intros. rewrite <-(right_id ∅ (∪) m) at 1. now rewrite mem_union_insert_r. Qed.

Lemma mem_insert_list_union l m :
  insert_list l m = list_to_map l ∪ m.
Proof.
  induction l; simpl.
  * now rewrite (left_id _ _).
  * now rewrite IHl, mem_union_insert_l.
Qed.

Lemma mem_subseteq_insert (m1 m2 : mem) b v :
  m1 !! b = None → m1 ⊆ m2 → m1 ⊆ <[b:=v]>m2.
Proof.
  intros ?? b'. destruct (decide (b' = b)).
  * intros v' ?. congruence.
  * intros. simplify_map. auto.
Qed.
Hint Resolve mem_subseteq_insert : mem.

Lemma mem_disjoint_insert_l m1 m2 b v :
  mem_disjoint (<[b:=v]>m1) m2 ↔ m2 !! b = None ∧ mem_disjoint m1 m2. 
Proof.
  rewrite mem_union_singleton_l.
  now rewrite mem_disjoint_union_l, mem_disjoint_singleton_l.
Qed.
Lemma mem_disjoint_insert_r m1 m2 b v :
  mem_disjoint m1 (<[b:=v]>m2) ↔ m1 !! b = None ∧ mem_disjoint m1 m2. 
Proof.
  rewrite mem_union_singleton_l.
  now rewrite mem_disjoint_union_r, mem_disjoint_singleton_r.
Qed.

Lemma mem_disjoint_delete_l m1 m2 b :
  mem_disjoint m1 m2 → mem_disjoint (delete b m1) m2.
Proof.
  intros H b'. destruct (H b'); auto.
  rewrite lookup_delete_None. tauto.
Qed.
Lemma mem_disjoint_delete_r m1 m2 b :
  mem_disjoint m1 m2 → mem_disjoint m1 (delete b m2).
Proof. symmetry. apply mem_disjoint_delete_l. now symmetry. Qed.
Hint Resolve mem_disjoint_delete_l mem_disjoint_delete_r : mem.

Lemma mem_disjoint_delete_list_l m1 m2 bs :
  mem_disjoint m1 m2 → mem_disjoint (delete_list bs m1) m2.
Proof. induction bs; simpl; auto with mem. Qed.
Lemma mem_disjoint_delete_list_r m1 m2 bs :
  mem_disjoint m1 m2 → mem_disjoint m1 (delete_list bs m2).
Proof. induction bs; simpl; auto with mem. Qed.
Hint Resolve mem_disjoint_delete_list_l mem_disjoint_delete_list_r : mem.

Lemma mem_union_delete m1 m2 b :
  delete b (m1 ∪ m2) = delete b m1 ∪ delete b m2.
Proof.
  intros. apply finmap_eq. intros b'. apply option_eq. intros v'.
  destruct (decide (b = b')); simplify_map;
   rewrite ?mem_union_Some; simplify_map; intuition congruence.
Qed.
Lemma mem_union_delete_list m1 m2 bs :
  delete_list bs (m1 ∪ m2) = delete_list bs m1 ∪ delete_list bs m2.
Proof.
  induction bs; simpl; [easy |].
  now rewrite IHbs, mem_union_delete.
Qed.

Lemma mem_disjoint_list_to_map_l l m :
  mem_disjoint (list_to_map l) m ↔ Forall (λ bv, m !! fst bv = None) l.
Proof.
  split.
  * induction l; simpl; rewrite ?mem_disjoint_insert_l in *;
      constructor; intuition auto.
  * induction 1; simpl; rewrite ?mem_disjoint_insert_l; auto with mem.
Qed.
Lemma mem_disjoint_list_to_map_r l m :
  mem_disjoint m (list_to_map l) ↔ Forall (λ bv, m !! fst bv = None) l.
Proof. now rewrite (symmetry_iff mem_disjoint), mem_disjoint_list_to_map_l. Qed.

Lemma mem_disjoint_list_to_map_zip_l bs vs m :
  same_length bs vs →
  mem_disjoint (list_to_map (zip bs vs)) m ↔ Forall (λ b, m !! b = None) bs.
Proof.
  intro. rewrite mem_disjoint_list_to_map_l.
  rewrite <-(zip_fst bs vs) at 2 by easy.
  now rewrite <-Forall_fst.
Qed.
Lemma mem_disjoint_list_to_map_zip_r bs vs m :
  same_length bs vs →
  mem_disjoint m (list_to_map (zip bs vs)) ↔ Forall (λ b, m !! b = None) bs.
Proof.
  intro. now rewrite (symmetry_iff mem_disjoint), mem_disjoint_list_to_map_zip_l.
Qed.

Ltac simplify_mem_disjoint := repeat
  match goal with
  | H : mem_disjoint (_ ∪ _) _ |- _ => apply mem_disjoint_union_l in H; destruct H
  | H : mem_disjoint _ (_ ∪ _) |- _ => apply mem_disjoint_union_r in H; destruct H
  | H : mem_disjoint {[ _ ]} _ |- _ => apply mem_disjoint_singleton_l in H
  | H : mem_disjoint _ {[ _ ]} |- _ =>  apply mem_disjoint_singleton_r in H
  | H : mem_disjoint (<[_:=_]>_) _ |- _ => apply mem_disjoint_insert_l in H; destruct H
  | H : mem_disjoint _ (<[_:=_]>_) |- _ => apply mem_disjoint_insert_r in H; destruct H
  | |- mem_disjoint (_ ∪ _) _ => apply mem_disjoint_union_l; split
  | |- mem_disjoint _ (_ ∪ _) => apply mem_disjoint_union_r; split
  | |- mem_disjoint {[ _ ]} _ => apply mem_disjoint_singleton_l
  | |- mem_disjoint _ {[ _ ]} => apply mem_disjoint_singleton_r
  | |- mem_disjoint (<[_:=_]>_) _ =>  apply mem_disjoint_insert_l; split
  | |- mem_disjoint _ (<[_:=_]>_) => apply mem_disjoint_insert_r; split
  end; try solve [intuition auto with mem].

(* Free blocks *)
Definition is_free (m : mem) (b : N) : Prop := m !! b = None.

Lemma is_free_lookup_None m b :
  is_free m b → m !! b = None.
Proof. easy. Qed.
Hint Resolve is_free_lookup_None : mem.

Lemma is_free_Forall_lookup_None m bs :
  Forall (is_free m) bs → Forall (λ b, m !! b = None) bs.
Proof. easy. Qed.
Hint Resolve is_free_Forall_lookup_None : mem.

Lemma is_free_lookup_Some m b v :
  is_free m b → ¬(m !! b = Some v).
Proof. unfold is_free. congruence. Qed.

Lemma is_free_dom `{Collection N C} m b :
  b ∉ dom C m ↔ is_free m b.
Proof. apply (not_elem_of_dom _). Qed.

Lemma is_free_subseteq (m1 m2 : mem) b :
  m1 ⊆ m2 → is_free m2 b → is_free m1 b.
Proof. apply lookup_subseteq_None. Qed.
Hint Resolve is_free_subseteq : mem.

Lemma is_free_union m1 m2 b :
  is_free (m1 ∪ m2) b ↔ is_free m1 b ∧ is_free m2 b.
Proof. apply mem_union_None. Qed.

Lemma is_free_insert m b b' v :
  is_free (<[b':=v]>m) b ↔ is_free m b ∧ b' ≠ b.
Proof. apply lookup_insert_None. Qed.
Lemma is_free_insert_1 b b' v m :
  is_free m b → b' ≠ b → is_free (<[b':=v]>m) b.
Proof. rewrite is_free_insert. auto. Qed.
Hint Resolve is_free_insert_1 : mem.

Inductive is_free_list (m : mem) : list N → Prop :=
  | is_free_nil :
     is_free_list m []
  | is_free_cons b bs :
     ¬In b bs → is_free m b → is_free_list m bs → is_free_list m (b :: bs).

Lemma is_free_list_nodup m bs : is_free_list m bs → NoDup bs.
Proof. induction 1; now constructor. Qed.
Lemma is_free_list_free m bs : is_free_list m bs → Forall (is_free m) bs.
Proof. induction 1; firstorder. Qed.
Hint Resolve is_free_list_nodup is_free_list_free : mem.

Lemma is_free_list_make m bs :
  NoDup bs → Forall (is_free m) bs → is_free_list m bs.
Proof. induction 1; inversion 1; constructor; auto. Qed.

Lemma is_free_list_subseteq m1 m2 bs :
  m1 ⊆ m2 → is_free_list m2 bs → is_free_list m1 bs.
Proof. induction 2; constructor; eauto with mem. Qed.

Lemma is_free_insert_list m b l :
  ¬In b (fst <$> l) → is_free m b → is_free (insert_list l m) b.
Proof. induction l; simpl; intuition auto with mem. Qed.
Hint Resolve is_free_insert_list : mem.

Definition is_writable (m : mem) (b : N) : Prop := is_Some (m !! b).

Definition fresh_block (m : mem) : N := fresh (dom (listset N) m).
Definition fresh_blocks (m : mem) (n : nat) : list N :=
  fresh_list n (dom (listset N) m).

Lemma is_free_fresh_block m : is_free m (fresh_block m).
Proof. unfold fresh_block. apply is_free_dom, is_fresh. Qed.
Hint Resolve is_free_fresh_block : mem.

Lemma fresh_blocks_length m n : length (fresh_blocks m n) = n.
Proof. apply fresh_list_length. Qed.
Lemma is_free_list_fresh_blocks n m : is_free_list m (fresh_blocks m n).
Proof.
  apply is_free_list_make.
  * apply fresh_list_nodup.
  * apply Forall_forall. intro.
    rewrite <-is_free_dom. apply fresh_list_is_fresh.
Qed.
Hint Resolve is_free_list_fresh_blocks : mem.

Lemma is_free_list_union m1 m2 bs :
  is_free_list (m1 ∪ m2) bs ↔ is_free_list m1 bs ∧ is_free_list m2 bs.
Proof.
  induction bs.
  * intuition constructor.
  * split.
    + inversion_clear 1. rewrite is_free_union in *.
      repeat constructor; intuition auto.
    + intros []. do 2 inversion_clear 1.
      constructor; rewrite ?is_free_union; intuition auto.
Qed.

Ltac simplify_is_free := repeat
  match goal with
  | H : is_free (_ ∪ _) _ |- _ => apply is_free_union in H; destruct H
  | H : is_free (<[_:=_]>_) _ |- _ => apply is_free_insert in H; destruct H
  | H : is_free_list (_ ∪ _) _ |- _ => apply is_free_list_union in H; destruct H
  | |- is_free (_ ∪ _) _ => apply is_free_union; split
  | |- is_free (<[_:=_]>_) _ => apply is_free_insert; split
  | |- is_free_list (_ ∪ _) _ => apply is_free_list_union; split
  end; try solve [intuition auto with mem].

(* Difference *)
Instance mem_difference: Difference mem := difference_with (λ _ _ , None).

Lemma mem_difference_Some m1 m2 i x : 
  (m1 ∖ m2) !! i = Some x ↔ m1 !! i = Some x ∧ m2 !! i = None.
Proof.
  unfold difference, mem_difference, difference_with, finmap_difference.
  rewrite (merge_spec _).
  destruct (m1 !! i), (m2 !! i); compute; intuition congruence.
Qed.

Lemma mem_disjoint_difference_l m1 m2 m3 : m2 ⊆ m3 → mem_disjoint (m1 ∖ m3) m2.
Proof.
  intros E b. specialize (E b).
  unfold difference, mem_difference, difference_with, finmap_difference.
  rewrite (merge_spec _).
  destruct (m1 !! b), (m2 !! b), (m3 !! b); compute; try intuition congruence.
  ediscriminate E; eauto.
Qed.
Lemma mem_disjoint_difference_r m1 m2 m3 : m2 ⊆ m3 → mem_disjoint m2 (m1 ∖ m3).
Proof. intros. symmetry. now apply mem_disjoint_difference_l. Qed.

Lemma mem_union_difference m1 m2 : m1 ∪ m2 = m1 ∪ m2 ∖ m1.
Proof.
  apply finmap_eq. intros b. apply option_eq. intros x.
  rewrite !mem_union_Some, mem_difference_Some.
  destruct (m1 !! b), (m2 !! b); intuition congruence.
Qed.

(* Alloc parameters *)
Inductive alloc_params (m : mem) : list N → list N → mem → Prop :=
  | alloc_params_nil : alloc_params m [] [] m
  | alloc_params_cons b bs v vs m2 :
     is_free m2 b →
     alloc_params m bs vs m2 →
     alloc_params m (b :: bs) (v :: vs) (<[b:=v]>m2).

Lemma alloc_params_same_length m1 bs m2 vs :
  alloc_params m1 bs vs m2 → same_length bs vs.
Proof. induction 1; simpl; now constructor. Qed.

Lemma alloc_params_lookup m1 bs vs m2 b v i :
  alloc_params m1 bs vs m2 →
  bs !! i = Some b → vs !! i = Some v → m2 !! b = Some v.
Proof.
  intros Halloc. revert i.
  induction Halloc; intros [|i] ??; simplify_list_lookup; simplify_map.
  feed pose proof (IHHalloc i); auto.
  rewrite lookup_insert_ne; auto.
  intro. subst. edestruct is_free_lookup_Some; eauto.
Qed.

Lemma alloc_params_subseteq m1 bs vs m2 :
  alloc_params m1 bs vs m2 → m1 ⊆ m2.
Proof. induction 1; eauto with mem. Qed.

Lemma alloc_params_free m1 bs vs m2 :
  alloc_params m1 bs vs m2 → is_free_list m1 bs.
Proof.
  induction 1; constructor; simpl; auto with mem.
  * rewrite list_lookup_In. intros [i ?].
    destruct (same_length_lookup bs vs i) as [v' ?];
     eauto using alloc_params_same_length.
    destruct (is_free_lookup_Some m2 b v');
      eauto using alloc_params_lookup.
  * eauto using alloc_params_subseteq with mem.
Qed.

Lemma alloc_params_insert_list_1 m bs vs :
  same_length bs vs →
  is_free_list m bs →
  alloc_params m bs vs (insert_list (zip bs vs) m).
Proof.
  induction 1; inversion_clear 1; simpl; constructor; auto.
  apply is_free_insert_list; auto.
  now rewrite zip_fst.
Qed.
Lemma alloc_params_insert_list_2 m1 bs vs m2 :
  alloc_params m1 bs vs m2 → m2 = insert_list (zip bs vs) m1.
Proof. induction 1; simpl; now f_equal. Qed.

Lemma alloc_params_insert_list m1 bs vs m2 :
  alloc_params m1 bs vs m2
   ↔ m2 = insert_list (zip bs vs) m1 ∧ is_free_list m1 bs ∧ same_length bs vs.
Proof.
  split.
  * intuition eauto using alloc_params_insert_list_2,
     alloc_params_free, alloc_params_same_length.
  * intros [?[??]]. subst. now apply alloc_params_insert_list_1.
Qed.

Lemma alloc_params_weaken m1 bs vs m2 m3 :
  mem_disjoint m1 m3 →
  mem_disjoint m2 m3 →
  alloc_params (m1 ∪ m3) bs vs (m2 ∪ m3) →
  alloc_params m1 bs vs m2.
Proof.
  rewrite !alloc_params_insert_list, !mem_insert_list_union.
  intuition idtac.
  * apply mem_union_cancel_l with m3.
    + easy.
    + simplify_is_free. simplify_mem_disjoint.
      apply mem_disjoint_list_to_map_zip_l; eauto with mem.
    + now rewrite <-(associative_eq (∪)).
  * now simplify_is_free.
Qed.
