(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file defines the permission system for our concrete memory. We
consider three variants of permissions:
- [Freeable]. This permission is used for dynamically allocated memory. As
  it can be used for writes, it can get sequenced, and therefore contains
  a fractional permission that can be locked.
- [Writable]. This permission is used for automatically allocated memory. As
  it can be used for writes, it can get sequenced, and therefore contains a
  fractional permission that can be locked.
- [ReadOnly]. Currently not used, but is supposed to be used for memory with
  read only permissions. As writing is not possible, the permission cannot be
  locked. *)
Require Export seqfrac.

Inductive memperm :=
  | Freeable_ : seqfrac → memperm
  | Writable_ : seqfrac → memperm
  | ReadOnly_ : frac → memperm.
Notation Freeable := (Freeable_ (UnSeq frac1)).
Notation Writable := (Writable_ (UnSeq frac1)).
Notation ReadOnly := (ReadOnly_ frac1).

Inductive memperm_subseteq: SubsetEq memperm :=
  | Freeable_subseteq_Freeable f1 f2 :
     f1 ⊆ f2 →
     Freeable_ f1 ⊆ Freeable_ f2
  | Writable_subseteq_Writable_ f1 f2 :
     f1 ⊆ f2 →
     Writable_ f1 ⊆ Writable_ f2
  | ReadOnly_subseteq_ReadOnly f1 f2 :
     f1 ⊆ f2 →
     ReadOnly_ f1 ⊆ ReadOnly_ f2.
Inductive memperm_disjoint: Disjoint memperm :=
  | Freeable_disjoint f1 f2 :
     f1 ⊥ f2 → Freeable_ f1 ⊥ Freeable_ f2
  | Writable_disjoint f1 f2 :
     f1 ⊥ f2 → Writable_ f1 ⊥ Writable_ f2
  | ReadOnly_disjoint f1 f2 :
     f1 ⊥ f2 → ReadOnly_ f1 ⊥ ReadOnly_ f2.

Instance memperm_ops: PermissionsOps memperm := {
  perm_kind := λ γ,
    match γ with
    | Freeable_ f => seqfrac_gen_kind Free f
    | Writable_ f => seqfrac_gen_kind Write f
    | ReadOnly_ f => frac_gen_kind Read f
    end;
  perm_lock_ := λ l γ,
    match γ with
    | Freeable_ f => Freeable_ (perm_lock_ l f)
    | Writable_ f => Writable_ (perm_lock_ l f)
    | ReadOnly_ f => ReadOnly_ (perm_lock_ l f)
    end;
  perm_subseteq := memperm_subseteq;
  perm_disjoint := memperm_disjoint;
  perm_union := λ γ1 γ2,
    match γ1, γ2 with
    | Freeable_ f1, Freeable_ f2 => Freeable_ (f1 ∪ f2)
    | Writable_ f1, Writable_ f2 => Writable_ (f1 ∪ f2)
    | ReadOnly_ f1, ReadOnly_ f2 => ReadOnly_ (f1 ∪ f2)
    | _, _ => Freeable_ Seq (**i dummy *)
    end;
  perm_difference := λ γ1 γ2,
    match γ1, γ2 with
    | Freeable_ f1, Freeable_ f2 => Freeable_ (f1 ∖ f2)
    | Writable_ f1, Writable_ f2 => Writable_ (f1 ∖ f2)
    | ReadOnly_ f1, ReadOnly_ f2 => ReadOnly_ (f1 ∖ f2)
    | _, _ => Freeable_ Seq (**i dummy *)
    end;
  perm_disjoint_dec := λ γ1 γ2, _;
  perm_eq_dec := λ γ1 γ2, _;
  perm_subseteq_dec := λ γ1 γ2, _
}.
Proof.
 refine
  match γ1, γ2 with
  | Freeable_ f1, Freeable_ f2 => cast_if (decide (f1 ⊥ f2))
  | Writable_ f1, Writable_ f2 => cast_if (decide (f1 ⊥ f2))
  | ReadOnly_ f1, ReadOnly_ f2 => cast_if (decide (f1 ⊥ f2))
  | _, _ => right _
  end; first [by constructor | by inversion 1].
 solve_decision.
 refine
  match γ1, γ2 with
  | Freeable_ f1, Freeable_ f2 => cast_if (decide (f1 ⊆ f2))
  | Writable_ f1, Writable_ f2 => cast_if (decide (f1 ⊆ f2))
  | ReadOnly_ f1, ReadOnly_ f2 => cast_if (decide (f1 ⊆ f2))
  | _, _ => right _
  end; first [by subst; constructor | by inversion 1; subst].
Defined.

Lemma Freeable_subset_Freeable f1 f2 :
  f1 ⊂ f2 → Freeable_ f1 ⊂ Freeable_ f2.
Proof. intros [? H]. by split; [constructor|contradict H; inversion H]. Qed.
Lemma Writable_subset_Writable f1 f2 :
  f1 ⊂ f2 → Writable_ f1 ⊂ Writable_ f2.
Proof. intros [? H]. by split; [constructor|contradict H; inversion H]. Qed.
Lemma ReadOnly_subset_ReadOnly f1 f2 :
  f1 ⊂ f2 → ReadOnly_ f1 ⊂ ReadOnly_ f2.
Proof. intros [? H]. by split; [constructor|contradict H; inversion H]. Qed.

Lemma seqfrac_subset_alt γ1 γ2 :
  γ1 ⊂ γ2 ↔
    (∃ f1 f2, γ1 = Freeable_ f1 ∧ γ2 = Freeable_ f2 ∧ f1 ⊂ f2) ∨
    (∃ f1 f2, γ1 = Writable_ f1 ∧ γ2 = Writable_ f2 ∧ f1 ⊂ f2) ∨
    (∃ f1 f2, γ1 = ReadOnly_ f1 ∧ γ2 = ReadOnly_ f2 ∧ f1 ⊂ f2).
Proof.
  split.
  * intros [H1 H2]. destruct H1; [left | right;left | right;right];
      (eexists _, _; split_ands; eauto; split; eauto);
      contradict H2; by constructor.
  * naive_solver eauto using Freeable_subset_Freeable,
      Writable_subset_Writable, ReadOnly_subset_ReadOnly.
Qed.

Instance: Permissions memperm.
Proof.
  split.
  * repeat split.
    + by intros []; constructor.
    + destruct 1; inversion_clear 1; constructor; etransitivity; eauto.
    + destruct 1; inversion_clear 1; f_equal; by apply (anti_symmetric _).
  * by destruct 1; constructor.
  * unfold perm_kind, perm_kind; simpl. destruct 1.
    + apply seqfrac_gen_kind_preserving. constructor. done.
    + apply seqfrac_gen_kind_preserving. constructor. done.
    + apply frac_gen_kind_preserving. constructor. done.
  * unfold perm_kind, perm_kind; simpl. intros ? [? []].
    + intros. apply seqfrac_fragment_gen_kind. red. eauto.
    + intros. apply seqfrac_fragment_gen_kind. red. eauto.
    + intros. apply frac_fragment_gen_kind. red. eauto.
  * destruct 1; inversion_clear 1;
      constructor; eapply perm_disjoint_weaken_l; eauto.
  * unfold perm_kind, perm_kind, perm_lock_; simpl.
    intros [?|?|?] ?; simpl in *; f_equal; eauto using seqfrac_unlock_lock.
  * unfold perm_kind, perm_kind, perm_lock_; simpl.
    intros [?|?|?]; simpl; intros; f_equal; eauto using seqfrac_unlock_other.
  * unfold perm_kind, perm_kind, perm_lock_; simpl.
    intros [?|?|?]; simpl; intros; f_equal.
    + by apply seqfrac_unlock_kind.
    + by apply seqfrac_unlock_kind.
    + by apply frac_unlock_kind.
  * red. unfold union, perm_union; simpl.
    by intros [?|?|?] [?|?|?] [?|?|?]; simpl; f_equal;
      rewrite ?(left_absorb Seq _), ?(right_absorb Seq _), ?(associative (∪)).
  * red. unfold union, perm_union; simpl.
    intros [?|?|?] [?|?|?]; simpl; f_equal; apply (commutative _).
  * unfold union, perm_union; simpl.
    intros [?|?|?] [?|?|?]; inversion_clear 1;
      try match goal with
      | H : Seq ⊥ _ |- _ => inversion H
      end; constructor; eapply perm_disjoint_union_ll; eauto.
  * intros [?|?|?] [?|?|?]; inversion_clear 1;
      try match goal with
      | H : Seq ⊥ _ |- _ => inversion H
      end; constructor; eapply perm_disjoint_union_move_l; eauto.
  * intros γ1 γ2. unfold union, perm_union; simpl. destruct 1; simpl.
    + apply Freeable_subset_Freeable. by apply perm_union_subset_l.
    + apply Writable_subset_Writable. by apply perm_union_subset_l.
    + apply ReadOnly_subset_ReadOnly. by apply perm_union_subset_l.
  * unfold union, perm_union; simpl.
    intros ?? []; destruct 1; constructor; try reflexivity;
      by apply perm_union_preserving_l.
  * destruct 1; inversion 1; inversion 1;
      constructor; eapply perm_union_reflecting_l; eauto.
  * unfold union, difference, perm_union, perm_difference; simpl.
    intros ??. rewrite seqfrac_subset_alt.
    intros [(?&?&?&?&?)|[(?&?&?&?&?)|(?&?&?&?&?)]]; subst;
      constructor; by apply perm_difference_disjoint.
  * unfold union, difference, perm_union, perm_difference; simpl.
    intros ??. rewrite seqfrac_subset_alt.
    intros [(?&?&?&?&?)|[(?&?&?&?&?)|(?&?&?&?&?)]]; subst;
      f_equal; by apply perm_union_difference.
Qed.

Lemma ReadOnly_fragment_ f : perm_fragment (ReadOnly_ f) ↔ perm_fragment f.
Proof.
  split.
  * intros [? Hf]. inversion Hf. red. eauto.
  * intros [??]. eexists (ReadOnly_ _). constructor. eauto.
Qed.
Lemma Writable_fragment_ f : perm_fragment (Writable_ f) ↔ perm_fragment f.
Proof.
  split.
  * intros [? Hf]. inversion Hf. red. eauto.
  * intros [? []]. intros.
    eexists (Writable_ (UnSeq _)). do 2 constructor. eauto.
Qed.
Lemma Freeable_fragment_ f : perm_fragment (Freeable_ f) ↔ perm_fragment f.
Proof.
  split.
  * intros [? Hf]. inversion Hf. red. eauto.
  * intros [? []]. intros.
    eexists (Freeable_ (UnSeq _)). do 2 constructor. eauto.
Qed.

Lemma ReadOnly_fragment : ¬perm_fragment ReadOnly.
Proof. rewrite ReadOnly_fragment_. by apply perm_fragment_not_read. Qed.
Lemma Writable_fragment : ¬perm_fragment Writable.
Proof. by apply perm_fragment_not_read. Qed.
Lemma Freeable_fragment : ¬perm_fragment Freeable.
Proof. by apply perm_fragment_not_read. Qed.

Lemma memperm_kind_lock (γ : memperm) :
  Write ⊆ perm_kind γ →
  perm_kind (perm_lock γ) = Locked.
Proof.
  destruct γ; try done.
  unfold perm_kind, perm_kind, perm_lock_; simpl.
  unfold frac_gen_kind. case_decide; inversion 1.
Qed.

Instance memperm_half: Half memperm := λ γ,
  match γ with
  | Freeable_ f => Freeable_ (f.½)
  | Writable_ f => Writable_ (f.½)
  | ReadOnly_ f => ReadOnly_ (f.½)
  end.
Instance: FracPermissions memperm.
Proof.
  split.
  * apply _.
  * unfold perm_kind; simpl. intros [] ?; constructor;
      eauto using seqfrac_disjoint_half, frac_disjoint_half.
  * unfold union, perm_union; simpl; intros [?|?|?]; simpl;
      f_equal; apply perm_union_half.
Qed.
