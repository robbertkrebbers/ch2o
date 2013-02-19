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
  | Freeable : seqfrac → memperm
  | Writable : seqfrac → memperm
  | ReadOnly : frac → memperm.
Notation Freeable_ := (Freeable (UnSeq 1)).
Notation Writable_ := (Writable (UnSeq 1)).
Notation ReadOnly_ := (ReadOnly 1).

Instance memperm_kind: PermKind memperm := λ γ,
  match γ with
  | Freeable f => seqfrac_gen_kind Free f
  | Writable f => seqfrac_gen_kind Write f
  | ReadOnly f => frac_gen_kind Read f
  end.
Instance memperm_lock: PermLock memperm := λ l γ,
  match γ with
  | Freeable f => Freeable (perm_lock_ l f)
  | Writable f => Writable (perm_lock_ l f)
  | ReadOnly f => ReadOnly (perm_lock_ l f)
  end.
Inductive memperm_subseteq: SubsetEq memperm :=
  | Freeable_subseteq_Freeable f1 f2 :
     f1 ⊆ f2 →
     Freeable f1 ⊆ Freeable f2
  | Writable_subseteq_Writable f1 f2 :
     f1 ⊆ f2 →
     Writable f1 ⊆ Writable f2
  | ReadOnly_subseteq_ReadOnly f1 f2 :
     f1 ⊆ f2 →
     ReadOnly f1 ⊆ ReadOnly f2.
Existing Instance memperm_subseteq.

Lemma Freeable_subset_Freeable f1 f2 : f1 ⊂ f2 → Freeable f1 ⊂ Freeable f2.
Proof. intros [? H]. by split; [constructor|contradict H; inversion H]. Qed.
Lemma Writable_subset_Writable f1 f2 : f1 ⊂ f2 → Writable f1 ⊂ Writable f2.
Proof. intros [? H]. by split; [constructor|contradict H; inversion H]. Qed.
Lemma ReadOnly_subset_ReadOnly f1 f2 : f1 ⊂ f2 → ReadOnly f1 ⊂ ReadOnly f2.
Proof. intros [? H]. by split; [constructor|contradict H; inversion H]. Qed.

Lemma seqfrac_subset_alt γ1 γ2 :
  γ1 ⊂ γ2 ↔
    (∃ f1 f2, γ1 = Freeable f1 ∧ γ2 = Freeable f2 ∧ f1 ⊂ f2) ∨
    (∃ f1 f2, γ1 = Writable f1 ∧ γ2 = Writable f2 ∧ f1 ⊂ f2) ∨
    (∃ f1 f2, γ1 = ReadOnly f1 ∧ γ2 = ReadOnly f2 ∧ f1 ⊂ f2).
Proof.
  split.
  * intros [H1 H2]. destruct H1; [left | right;left | right;right];
      (eexists _, _; split_ands; eauto; split; eauto);
      contradict H2; by constructor.
  * naive_solver eauto using Freeable_subset_Freeable,
      Writable_subset_Writable, ReadOnly_subset_ReadOnly.
Qed.

Inductive memperm_disjoint: Disjoint memperm :=
  | Freeable_disjoint f1 f2 :
     f1 ⊥ f2 → Freeable f1 ⊥ Freeable f2
  | Writable_disjoint f1 f2 :
     f1 ⊥ f2 → Writable f1 ⊥ Writable f2
  | ReadOnly_disjoint f1 f2 :
     f1 ⊥ f2 → ReadOnly f1 ⊥ ReadOnly f2.
Existing Instance memperm_disjoint.

Instance memperm_union: Union memperm := λ γ1 γ2,
  match γ1, γ2 with
  | Freeable f1, Freeable f2 => Freeable (f1 ∪ f2)
  | Writable f1, Writable f2 => Writable (f1 ∪ f2)
  | ReadOnly f1, ReadOnly f2 => ReadOnly (f1 ∪ f2)
  | _, _ => Freeable Seq (* dummy *)
  end.

Instance memperm_difference: Difference memperm := λ γ1 γ2,
  match γ1, γ2 with
  | Freeable f1, Freeable f2 => Freeable (f1 ∖ f2)
  | Writable f1, Writable f2 => Writable (f1 ∖ f2)
  | ReadOnly f1, ReadOnly f2 => ReadOnly (f1 ∖ f2)
  | _, _ => Freeable Seq (* dummy *)
  end.

Instance memperm_eq_dec (γ1 γ2 : memperm) : Decision (γ1 = γ2).
Proof. solve_decision. Defined.
Instance memperm_subseteq_dec (γ1 γ2 : memperm) : Decision (γ1 ⊆ γ2).
Proof.
 refine
  match γ1, γ2 with
  | Freeable f1, Freeable f2 => cast_if (decide (f1 ⊆ f2))
  | Writable f1, Writable f2 => cast_if (decide (f1 ⊆ f2))
  | ReadOnly f1, ReadOnly f2 => cast_if (decide (f1 ⊆ f2))
  | _, _ => right _
  end; first [by subst; constructor | by inversion 1; subst].
Defined.
Instance memperm_disjoint_dec (γ1 γ2 : memperm) : Decision (γ1 ⊥ γ2).
Proof.
 refine
  match γ1, γ2 with
  | Freeable f1, Freeable f2 => cast_if (decide (f1 ⊥ f2))
  | Writable f1, Writable f2 => cast_if (decide (f1 ⊥ f2))
  | ReadOnly f1, ReadOnly f2 => cast_if (decide (f1 ⊥ f2))
  | _, _ => right _
  end; first [by constructor | by inversion 1].
Defined.

Instance: Permissions memperm.
Proof.
  split.
  * repeat split.
    + by intros []; constructor.
    + destruct 1; inversion_clear 1; constructor; etransitivity; eauto.
    + destruct 1; inversion_clear 1; f_equal; by apply (anti_symmetric _).
  * by destruct 1; constructor.
  * unfold perm_kind, memperm_kind. destruct 1.
    + apply seqfrac_gen_kind_preserving. constructor. done.
    + apply seqfrac_gen_kind_preserving. constructor. done.
    + apply frac_gen_kind_preserving. constructor. done.
  * unfold perm_kind, memperm_kind. intros ? [? []].
    + intros. apply seqfrac_fragment_gen_kind. red. eauto.
    + intros. apply seqfrac_fragment_gen_kind. red. eauto.
    + intros. apply frac_fragment_gen_kind. red. eauto.
  * destruct 1; inversion_clear 1;
      constructor; eapply perm_disjoint_weaken_l; eauto.
  * unfold perm_kind, memperm_kind, perm_lock_, memperm_lock.
    intros [?|?|?] ?; simpl in *; f_equal; eauto using seqfrac_unlock_lock.
  * unfold perm_kind, memperm_kind, perm_lock_, memperm_lock.
    intros [?|?|?]; simpl; intros; f_equal; eauto using seqfrac_unlock_other.
  * unfold perm_kind, memperm_kind, perm_lock_, memperm_lock.
    intros [?|?|?]; simpl; intros; f_equal.
    + by apply seqfrac_unlock_kind.
    + by apply seqfrac_unlock_kind.
    + by apply frac_unlock_kind.
  * red. unfold union, seqfrac_union.
    by intros [?|?|?] [?|?|?] [?|?|?]; simpl; f_equal;
      rewrite ?(left_absorb Seq _), ?(right_absorb Seq _), ?(associative (∪)).
  * red. unfold union, seqfrac_union.
    intros [?|?|?] [?|?|?]; simpl; f_equal; apply (commutative _).
  * unfold union, seqfrac_union.
    intros [?|?|?] [?|?|?]; inversion_clear 1;
      try match goal with
      | H : Seq ⊥ _ |- _ => inversion H
      end; constructor; eapply perm_disjoint_union_ll; eauto.
  * intros [?|?|?] [?|?|?]; inversion_clear 1;
      try match goal with
      | H : Seq ⊥ _ |- _ => inversion H
      end; constructor; eapply perm_disjoint_union_move_l; eauto.
  * intros γ1 γ2. unfold union, seqfrac_union. destruct 1; simpl.
    + apply Freeable_subset_Freeable. by apply perm_union_subset_l.
    + apply Writable_subset_Writable. by apply perm_union_subset_l.
    + apply ReadOnly_subset_ReadOnly. by apply perm_union_subset_l.
  * unfold union, memperm_union.
    intros ?? []; destruct 1; constructor; try reflexivity;
      by apply perm_union_preserving_l.
  * destruct 1; inversion 1; inversion 1;
      constructor; eapply perm_union_reflecting_l; eauto.
  * unfold union, difference, memperm_union, memperm_difference.
    intros ??. rewrite seqfrac_subset_alt.
    intros [(?&?&?&?&?)|[(?&?&?&?&?)|(?&?&?&?&?)]]; subst;
      constructor; by apply perm_difference_disjoint.
  * unfold union, difference, memperm_union, memperm_difference.
    intros ??. rewrite seqfrac_subset_alt.
    intros [(?&?&?&?&?)|[(?&?&?&?&?)|(?&?&?&?&?)]]; subst;
      f_equal; by apply perm_union_difference.
Qed.

Lemma ReadOnly_fragment f : perm_fragment (ReadOnly f) ↔ perm_fragment f.
Proof.
  split.
  * intros [? Hf]. inversion Hf. red. eauto.
  * intros [??]. eexists (ReadOnly _). constructor. eauto.
Qed.
Lemma Writable_fragment f : perm_fragment (Writable f) ↔ perm_fragment f.
Proof.
  split.
  * intros [? Hf]. inversion Hf. red. eauto.
  * intros [? []]. intros.
    eexists (Writable (UnSeq _)). do 2 constructor. eauto.
Qed.
Lemma Freeable_fragment f : perm_fragment (Freeable f) ↔ perm_fragment f.
Proof.
  split.
  * intros [? Hf]. inversion Hf. red. eauto.
  * intros [? []]. intros.
    eexists (Freeable (UnSeq _)). do 2 constructor. eauto.
Qed.

Lemma ReadOnly__fragment : ¬perm_fragment ReadOnly_.
Proof. rewrite ReadOnly_fragment. by apply perm_fragment_not_read. Qed.
Lemma Writable__fragment : ¬perm_fragment Writable_.
Proof. by apply perm_fragment_not_read. Qed.
Lemma Freeable__fragment : ¬perm_fragment Freeable_.
Proof. by apply perm_fragment_not_read. Qed.

Lemma memperm_kind_lock (γ : memperm) :
  Write ⊆ perm_kind γ →
  perm_kind (perm_lock γ) = Locked.
Proof.
  destruct γ; try done.
  unfold perm_kind, memperm_kind, perm_lock_, memperm_lock, frac_gen_kind.
  case_decide; inversion 1.
Qed.
