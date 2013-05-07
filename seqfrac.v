(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file extends fractional permissions with an the permission of being
locked. We show that the permissions obtained form an instance of our
abstract interface. *)
Require Export frac.

Inductive seqfrac : Set := Seq | UnSeq (f : frac).

Definition seqfrac_gen_kind (k : pkind) (f : seqfrac) : pkind :=
  match f with
  | Seq => Locked
  | UnSeq f => frac_gen_kind k f
  end.

Inductive seqfrac_subseteq: SubsetEq seqfrac :=
  | Seq_subseteq_Seq : Seq ⊆ Seq
  | UnSeq_subseteq_UnSeq f1 f2 : f1 ⊆ f2 → UnSeq f1 ⊆ UnSeq f2.
Inductive seqfrac_disjoint: Disjoint seqfrac :=
  | UnSeq_disjoint f1 f2 : f1 ⊥ f2 → UnSeq f1 ⊥ UnSeq f2.

Instance seqfrac_ops: PermissionsOps seqfrac := {
  perm_kind := seqfrac_gen_kind Write;
  perm_lock_ := λ l f,
    match l, f with
    | true, _ => Seq
    | false, Seq => UnSeq frac1
    | false, UnSeq f => UnSeq f
    end;
  perm_subseteq := seqfrac_subseteq;
  perm_disjoint := seqfrac_disjoint;
  perm_union := λ f1 f2,
    match f1, f2 with
    | UnSeq f1, UnSeq f2 => UnSeq (f1 ∪ f2)
    | _, _ => Seq (**i dummy *)
    end;
  perm_difference := λ f1 f2,
    match f1, f2 with
    | UnSeq f1, UnSeq f2 => UnSeq (f1 ∖ f2)
    | _, _ => Seq (**i dummy *)
    end;
  perm_disjoint_dec := λ f1 f2, _;
  perm_eq_dec := λ f1 f2, _;
  perm_subseteq_dec := λ f1 f2, _
}.
Proof.
 refine
  match f1, f2 with
  | UnSeq f1, UnSeq f2 => cast_if (decide (f1 ⊥ f2))
  | _, _ => right _
  end; first [by constructor | by inversion 1].
 solve_decision.
 refine
  match f1, f2 with
  | Seq, Seq => left _
  | UnSeq f1, UnSeq f2 => cast_if (decide (f1 ⊆ f2))
  | _, _ => right _
  end; first [by subst; constructor | by inversion 1; subst].
Defined.

Lemma UnSeq_subset_UnSeq f1 f2 : f1 ⊂ f2 → UnSeq f1 ⊂ UnSeq f2.
Proof. intros [? H]. by split; [constructor|contradict H; inversion H]. Qed.

Lemma seqfrac_subset_alt f1 f2 :
  f1 ⊂ f2 ↔ ∃ f1' f2', f1 = UnSeq f1' ∧ f2 = UnSeq f2' ∧ f1' ⊂ f2'.
Proof.
  split.
  * intros [H1 H2]. destruct H1.
    + destruct H2. constructor.
    + repeat esplit; eauto. contradict H2. by constructor.
  * naive_solver eauto using UnSeq_subset_UnSeq.
Qed.

Lemma seqfrac_gen_kind_preserving k f1 f2 :
  Read ⊆ k → f1 ⊆ f2 → seqfrac_gen_kind k f1 ⊆ seqfrac_gen_kind k f2.
Proof.
  destruct 2; simpl.
  * done.
  * by apply frac_gen_kind_preserving.
Qed.
Lemma seqfrac_fragment_gen_kind k f :
  perm_fragment f → seqfrac_gen_kind k f = Read.
Proof.
  intros [? [???]]; simpl.
  apply frac_fragment_gen_kind. by exists f2.
Qed.
Lemma seqfrac_lock_unlock k f :
  Read ⊆ k → seqfrac_gen_kind k f = Locked → perm_lock (perm_unlock f) = f.
Proof.
  unfold perm_lock_; destruct f; simpl.
  * done.
  * unfold frac_gen_kind. case_decide. by inversion 1; subst. done.
Qed.
Lemma seqfrac_unlock_lock k f :
  Write ⊆ seqfrac_gen_kind k f → perm_unlock (perm_lock f) = f.
Proof.
  unfold perm_lock_; destruct f; simpl.
  * inversion 1.
  * unfold frac_gen_kind. case_decide. by subst. inversion 1.
Qed.
Lemma seqfrac_unlock_other k f :
  seqfrac_gen_kind k f ≠ Locked → perm_unlock f = f.
Proof. by destruct f. Qed.
Lemma seqfrac_unlock_kind k f :
  k ≠ Locked → seqfrac_gen_kind k (perm_unlock f) ≠ Locked.
Proof. destruct f. done. apply frac_unlock_kind. Qed.

Instance: Permissions seqfrac.
Proof.
  split.
  * repeat split.
    + by intros [|?]; constructor.
    + destruct 1; inversion_clear 1.
      - constructor.
      - constructor. etransitivity; eauto.
    + destruct 1; inversion_clear 1.
      - done.
      - f_equal. by apply (anti_symmetric _).
  * destruct 1. by constructor.
  * intros ??. apply seqfrac_gen_kind_preserving. constructor.
  * apply seqfrac_fragment_gen_kind.
  * destruct 1; inversion 1; subst.
    constructor. eauto using perm_disjoint_weaken_l.
  * apply seqfrac_unlock_lock.
  * apply seqfrac_unlock_other.
  * intros. by apply seqfrac_unlock_kind.
  * red. unfold union, perm_union. simpl.
    intros [|?] [|?] [|?]; try reflexivity. f_equal. apply (associative_L (∪)).
  * red. unfold union, perm_union; simpl.
    intros [|?] [|?]; try reflexivity. f_equal. apply (commutative_L (∪)).
  * unfold union, perm_union; simpl.
    intros [|?] [|?]; inversion_clear 1.
    constructor. eapply perm_disjoint_union_ll; eauto.
  * unfold union, perm_union; simpl.
    intros [|?] [|?]; inversion_clear 1.
    constructor. by apply perm_disjoint_union_move_l.
  * unfold union, perm_union; simpl. destruct 1.
    by apply UnSeq_subset_UnSeq, perm_union_subset_l.
  * unfold union, perm_union; simpl.
    intros ?? [|?]; destruct 1; try constructor.
    by apply perm_union_preserving_l.
  * destruct 1; inversion 1; inversion 1.
    constructor. eapply perm_union_reflecting_l; eauto.
  * unfold union, difference, perm_union, perm_difference; simpl.
    intros ??. rewrite seqfrac_subset_alt. intros (?&?&?&?&?); subst.
    constructor; by apply perm_disjoint_difference.
  * unfold union, difference, perm_union, perm_difference; simpl.
    intros ??. rewrite seqfrac_subset_alt. intros (?&?&?&?&?); subst.
    f_equal. by apply perm_union_difference.
Qed.

Instance: LeftAbsorb (=) Seq (∪).
Proof. by intros []. Qed.
Instance: RightAbsorb (=) Seq (∪).
Proof. by intros []. Qed.

Lemma UnSeq_fragment f : perm_fragment (UnSeq f) ↔ perm_fragment f.
Proof.
  split.
  * intros [? Hf]. inversion Hf. red. eauto.
  * intros [??]. eexists (UnSeq _). constructor. eauto.
Qed.
Lemma Seq_fragment : ¬perm_fragment Seq.
Proof. intros [? H]. inversion H. Qed.

Definition to_frac (f : seqfrac) : frac :=
  match f with
  | Seq => frac1
  | UnSeq f => f
  end.
Instance seqfrac_half: Half seqfrac := λ f,
  match f with
  | Seq => Seq
  | UnSeq f => UnSeq (f.½)
  end.
Lemma seqfrac_disjoint_half k f : seqfrac_gen_kind k f ≠ Locked → f.½ ⊥ f.½.
Proof. destruct f; [done |]. constructor. apply frac_disjoint_half. Qed.

Instance: FracPermissions seqfrac.
Proof.
  split.
  * apply _.
  * apply seqfrac_disjoint_half.
  * intros [|f]; [done |].
    unfold union, perm_union; simpl. f_equal. apply perm_union_half.
Qed.
