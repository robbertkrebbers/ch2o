Require Export nmap list.
Open Scope N_scope.

(*
We use notation to avoid problems with unfolding. 
However, this is a bit strange, because an (Nmap N) is not
necessarily a memory. Later we will replace this definition
anyway, so currently, we just don't care.
*)
Notation mem := (Nmap N).

Definition is_free (b : N) (m : mem) : Prop := m !! b = None.
Definition is_writable (b : N) (m : mem) : Prop := is_Some (m !! b).

Definition fresh_block (m : mem) := fresh (dom (listset N) m).

Lemma fresh_block_is_free m : is_free (fresh_block m) m.
Proof. unfold is_free, fresh_block. apply (not_elem_of_dom _). apply is_fresh. Qed.
Hint Resolve fresh_block_is_free : mem.

Definition mem_disjoint (m1 m2 : mem) := ∀ b, m1 !! b = None ∨ m2 !! b = None.

Instance: Symmetric mem_disjoint.
Proof. intros ?? H b. destruct (H b); intuition. Qed.
Lemma mem_disjoint_empty_l m : mem_disjoint ∅ m.
Proof. intros ?. left. apply lookup_empty. Qed.
Lemma mem_disjoint_empty_r m : mem_disjoint m ∅.
Proof. intros ?. right. apply lookup_empty. Qed.
Hint Resolve mem_disjoint_empty_l mem_disjoint_empty_r : mem.

Lemma mem_disjoint_Some_l m1 m2 b x:
  m1 !! b = Some x → mem_disjoint m1 m2 → m2 !! b = None.
Proof. intros ? H. specialize (H b). intuition congruence. Qed.
Lemma mem_disjoint_Some_r m1 m2 b x:
  m2 !! b = Some x → mem_disjoint m1 m2 → m1 !! b = None.
Proof. intros ? H. specialize (H b). intuition congruence. Qed.
Hint Resolve mem_disjoint_Some_l mem_disjoint_Some_r : mem.

Lemma mem_disjoint_singleton_1 m b v :
  m !! b = None → mem_disjoint m {{(b, v)}}.
Proof.
  unfold is_free. intros ? b'. destruct (decide (b = b')).
   left. congruence.
  right. now apply lookup_singleton_ne.
Qed.
Lemma mem_disjoint_singleton_2 m b v :
  mem_disjoint m {{(b, v)}} → m !! b = None.
Proof.
  intros H. destruct (H b) as [H2 | H2].
   easy.
  rewrite lookup_singleton in H2. congruence.
Qed.
Hint Resolve mem_disjoint_singleton_1 : mem.

Instance mem_union: Union mem := union_with (λ x _ , x).

Lemma mem_union_Some_iff m1 m2 i x : 
  (m1 ∪ m2) !! i = Some x ↔ m1 !! i = Some x ∨ (m1 !! i = None ∧ m2 !! i = Some x).
Proof.
  unfold union, mem_union, union_with, finmap_union. rewrite (merge_spec _).
  destruct (m1 !! i), (m2 !! i); compute; try intuition congruence.
Qed.
Lemma mem_union_None_iff m1 m2 b : 
  (m1 ∪ m2) !! b = None ↔ m1 !! b = None ∧ m2 !! b = None.
Proof. apply finmap_union_None. Qed.

Lemma mem_union_Some_l m1 m2 b x :
  m1 !! b = Some x → (m1 ∪ m2) !! b = Some x.
Proof. rewrite mem_union_Some_iff. intuition congruence. Qed.
Lemma mem_union_Some_r m1 m2 b x :
  m1 !! b = None → m2 !! b = Some x → (m1 ∪ m2) !! b = Some x.
Proof. rewrite mem_union_Some_iff. intuition congruence. Qed.
Lemma mem_union_Some_inv_l m1 m2 b x :
  (m1 ∪ m2) !! b = Some x → m2 !! b = None → m1 !! b = Some x.
Proof. rewrite mem_union_Some_iff. intuition congruence. Qed.
Lemma mem_union_Some_inv_r m1 m2 b x : 
  (m1 ∪ m2) !! b = Some x → m1 !! b = None → m2 !! b = Some x.
Proof. rewrite mem_union_Some_iff. intuition congruence. Qed.

Lemma mem_union_None m1 m2 b :
  m1 !! b = None → m2 !! b = None → (m1 ∪ m2) !! b = None.
Proof. rewrite mem_union_None_iff. intuition. Qed.
Lemma mem_union_None_inv_l m1 m2 b :
  (m1 ∪ m2) !! b = None → m1 !! b = None.
Proof. rewrite mem_union_None_iff. intuition. Qed.
Lemma mem_union_None_inv_r m1 m2 b :
  (m1 ∪ m2) !! b = None → m2 !! b = None.
Proof. rewrite mem_union_None_iff. intuition. Qed.

Hint Resolve
  mem_union_Some_l mem_union_Some_r
  mem_union_Some_inv_l mem_union_Some_inv_r 
  mem_union_None : mem.

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

Lemma mem_disjoint_cancel_l m1 m2 m3 :
  mem_disjoint (m1 ∪ m2) m3 → mem_disjoint m1 m3.
Proof. intros H b. specialize (H b). rewrite mem_union_None_iff in H. tauto. Qed.
Lemma mem_disjoint_cancel_r m1 m2 m3 :
  mem_disjoint (m1 ∪ m2) m3 → mem_disjoint m2 m3.
Proof. intros H b. specialize (H b). rewrite mem_union_None_iff in H. tauto. Qed.
Lemma mem_disjoint_union m1 m2 m3 :
  mem_disjoint m1 m3 → mem_disjoint m2 m3 → mem_disjoint (m1 ∪ m2) m3.
Proof.
  intros H1 H2 b. specialize (H1 b). specialize (H2 b).
  rewrite mem_union_None_iff. tauto.
Qed.
Hint Resolve
  mem_disjoint_cancel_l mem_disjoint_cancel_r
  mem_disjoint_union : mem.

Lemma mem_disjoint_insert m1 m2 b v :
  m1!!b = None → mem_disjoint m1 m2 → mem_disjoint m1 (<[b:=v]> m2).
Proof.
  intros ? H b'. destruct (decide (b = b')); subst; auto.
  destruct (H b'); auto.
  right. now rewrite lookup_insert_ne.
Qed.
Hint Resolve mem_disjoint_insert : mem.

Lemma mem_subseteq_union_l (m1 m2 : mem) :
  m1 ⊆ m1 ∪ m2.
Proof.
  unfold union, mem_union. intros i x ?. case_eq (m2 !! i); intros.
   erewrite finmap_union_merge; eauto.
  erewrite finmap_union_l; eauto.
Qed.
Lemma mem_subseteq_union_r (m1 m2 : mem) :
  mem_disjoint m1 m2 → m2 ⊆ m1 ∪ m2.
Proof.
  intros. rewrite mem_union_comm by auto.
  apply mem_subseteq_union_l.
Qed.
Hint Resolve mem_subseteq_union_l mem_subseteq_union_r : mem.

Lemma mem_union_cancel_l m1 m2 m3 :
  mem_disjoint m1 m3 → mem_disjoint m2 m3 → m1 ∪ m3 = m2 ∪ m3 → m1 = m2.
Proof.
  revert m1 m2 m3.
  assert (∀ m1 m2 m3 b v, 
   mem_disjoint m1 m3 → m1 ∪ m3 = m2 ∪ m3 →
   m1 !! b = Some v → m2 !! b = Some v) as help.
   intros m1 m2 m3 b v ? E ?.
   apply mem_union_Some_inv_l with m3.
    rewrite <-E. eauto with mem.
   eauto with mem.
  intros. apply finmap_eq. intros i. apply option_eq.
  split; eapply help; eauto with mem.
Qed.
Lemma mem_union_cancel_r m1 m2 m3 :
  mem_disjoint m1 m3 → mem_disjoint m2 m3 → m3 ∪ m1 = m3 ∪ m2 → m1 = m2.
Proof.
  intros ??. rewrite !(mem_union_comm m3) by (symmetry; auto).
  now apply mem_union_cancel_l.
Qed.

Lemma mem_union_insert_l m1 m2 b v :
  <[b:=v]>m1 ∪ m2 = <[b:=v]>(m1 ∪ m2).
Proof.
  apply finmap_eq. intros b'. apply option_eq. intros v'.
  destruct (decide (b = b')); subst.
   rewrite mem_union_Some_iff, !lookup_insert. intuition congruence.
  rewrite mem_union_Some_iff, !lookup_insert_ne,
    mem_union_Some_iff by easy. intuition easy.
Qed.
Lemma mem_union_insert_r m1 m2 b v :
  m1!!b = None → m1 ∪ <[b:=v]>m2 = <[b:=v]>(m1 ∪ m2).
Proof.
  intros. apply finmap_eq. intros b'. apply option_eq. intros v'.
  destruct (decide (b = b')); subst.
   rewrite mem_union_Some_iff, !lookup_insert. intuition congruence.
  rewrite mem_union_Some_iff, !lookup_insert_ne,
    mem_union_Some_iff by easy. intuition easy.
Qed.

Lemma mem_union_singleton_l m b v :
  {{ (b,v) }} ∪ m = <[b:=v]>m.
Proof. rewrite <-(left_id ∅ (∪) m) at 2. now rewrite <-mem_union_insert_l. Qed.
Lemma mem_union_singleton_r m b v :
  m!!b = None → m ∪ {{ (b,v) }} = <[b:=v]>m.
Proof. intros. rewrite <-(right_id ∅ (∪) m) at 2. now rewrite <-mem_union_insert_r. Qed.
