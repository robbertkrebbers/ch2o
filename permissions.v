(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Import Qcanon.
Require Export orders separation_instances.
Local Open Scope Qc_scope.

(**
Concrete permissions are built from more primitive combinators:
- [lockable]: [Locked] describes that the object has been locked due to
  a sequenced write, and [Unlocked] means that it is not locked
- [counter] is to account for tokens to keep track of parts of the memory
  that are addresseble.
*)
Definition perm := (lockable (counter Qcanon.Qc) + Qcanon.Qc)%type.
Instance perm_sep_ops : SeparationOps perm := _.
Instance perm_sep : Separation perm := _.
Typeclasses Opaque perm.

Definition perm_readonly : perm := inr 1.
Definition perm_full : perm := inl (LUnlocked (Counter 0 1)).
Definition perm_token : perm := inl (LUnlocked (Counter (-1) ∅)).

Inductive pkind :=
  Writable | Readable | Locked | Existing.
Instance pkind_dec (k1 k2 : pkind) : Decision (k1 = k2).
Proof. solve_decision. Defined.
Instance pkind_subseteq : SubsetEq pkind := λ k1 k2,
  match k1, k2 with
  | _, Writable => True
  | (Existing | Readable), Readable => True
  | Existing, Existing => True
  | (Existing | Locked), Locked => True
  | _, _ => False
  end.
Instance pkind_subseteq_dec : ∀ k1 k2 : pkind, Decision (k1 ⊆ k2).
Proof. intros [] []; apply _. Defined.
Instance: PartialOrder (@subseteq pkind _).
Proof. by repeat split; repeat intros []. Qed.
Instance option_pkind_subseteq : SubsetEq (option pkind) := λ k1 k2,
  match k1, k2 with
  | Some k1, Some k2 => k1 ⊆ k2 | None, _ => True | Some _, None => False
  end.
Instance option_pkind_subseteq_dec : ∀ k1 k2 : option pkind, Decision (k1 ⊆ k2).
Proof. intros [] []; apply _. Defined.
Instance: PartialOrder (@subseteq (option pkind) _).
Proof. by repeat split; repeat intros []. Qed.

Definition perm_kind (x : perm) : option pkind :=
  match x with
  | inl (LUnlocked (Counter x' y')) =>
     if decide (y' = ∅) then
       if decide (x' = 0) then None else Some Existing
     else if decide (y' = 1) then Some Writable else Some Readable
  | inl (LLocked _) => Some Locked
  | inr x' => Some Readable
  end.
Definition perm_locked (x : perm) : bool :=
  match x with inl (LLocked _) => true | _ => false end.
Definition perm_lock (x : perm) : perm :=
  match x with inl (LUnlocked x') => inl (LLocked x') | _ => x end.
Definition perm_unlock (x : perm) : perm :=
  match x with inl (LLocked x') => inl (LUnlocked x') | _ => x end.

Inductive perm_kind_view : perm → option pkind → Prop :=
  | perm_kind_None : perm_kind_view (inl (LUnlocked (Counter ∅ 0))) None
  | perm_kind_Locked x' : perm_kind_view (inl (LLocked x')) (Some Locked)
  | perm_kind_Existing x' :
     x' ≠ 0 → perm_kind_view (inl (LUnlocked (Counter x' ∅))) (Some Existing)
  | perm_kind_Readable x' y' :
     y' ≠ ∅ → y' ≠ 1 →
     perm_kind_view (inl (LUnlocked (Counter x' y'))) (Some Readable)
  | perm_kind_Writable x' :
     perm_kind_view (inl (LUnlocked (Counter x' 1))) (Some Writable)
  | perm_kind_Writable' x' :
     x' ≠ 0 → perm_kind_view (inl (LUnlocked (Counter x' 1))) (Some Writable)
  | perm_kind_ro_Readable x' : perm_kind_view (inr x') (Some Readable).
Lemma perm_kind_spec x : perm_kind_view x (perm_kind x).
Proof.
  destruct x as [[[]|[]]|]; simpl; repeat case_decide;
    intuition; simplify_equality'; constructor; auto.
Qed.
Arguments perm_kind _ : simpl never.

Lemma perm_full_valid : sep_valid perm_full.
Proof. done. Qed.
Lemma perm_full_mapped : ¬sep_unmapped perm_full.
Proof. by apply (bool_decide_unpack _). Qed.
Lemma perm_full_unshared : sep_unshared perm_full.
Proof. by apply (bool_decide_unpack _). Qed.
Lemma perm_readonly_valid : sep_valid perm_readonly.
Proof. done. Qed.
Lemma perm_readonly_mapped : ¬sep_unmapped perm_readonly.
Proof. by apply (bool_decide_unpack _). Qed.
Lemma perm_token_valid : sep_valid perm_token.
Proof. done. Qed.
Lemma perm_locked_mapped x : perm_locked x = true → ¬sep_unmapped x.
Proof. destruct x as [[[]|]|[]]; repeat sep_unfold; naive_solver. Qed.
Lemma perm_Readable_locked x : Some Readable ⊆ perm_kind x → perm_locked x = false.
Proof. by destruct (perm_kind_spec x). Qed.
Lemma perm_locked_lock x :
  Some Writable ⊆ perm_kind x → perm_locked (perm_lock x) = true.
Proof. by destruct (perm_kind_spec x). Qed.
Lemma perm_locked_unlock x : perm_locked (perm_unlock x) = false.
Proof. by destruct x as [[]|[]]. Qed.
Lemma perm_lock_valid x :
  sep_valid x → Some Writable ⊆ perm_kind x → sep_valid (perm_lock x).
Proof. destruct (perm_kind_spec x); repeat sep_unfold; intuition. Qed.
Lemma perm_lock_unmapped x :
  Some Writable ⊆ perm_kind x → sep_unmapped x → sep_unmapped (perm_lock x).
Proof. destruct (perm_kind_spec x); repeat sep_unfold; intuition. Qed.
Lemma perm_lock_mapped x : sep_unmapped (perm_lock x) → sep_unmapped x.
Proof. destruct x as [[]|[]]; repeat sep_unfold; intuition. Qed.
Lemma perm_lock_unshared x : sep_unshared x → sep_unshared (perm_lock x).
Proof. destruct x as [[]|[]]; repeat sep_unfold; intuition. Qed.
Lemma perm_unlock_lock x :
  sep_valid x → Some Writable ⊆ perm_kind x → perm_unlock (perm_lock x) = x.
Proof. by destruct (perm_kind_spec x). Qed.
Lemma perm_unlock_unlock x : perm_unlock (perm_unlock x) = perm_unlock x.
Proof. by destruct x as [[]|]. Qed.
Lemma perm_unlock_valid x : sep_valid x → sep_valid (perm_unlock x).
Proof. destruct x as [[[]|[]]|]; repeat sep_unfold; naive_solver. Qed.
Lemma perm_unlock_unmapped x : sep_unmapped x → sep_unmapped (perm_unlock x).
Proof. destruct x as [[[]|[]]|]; repeat sep_unfold; intuition. Qed.
Lemma perm_unlock_mapped x :
  sep_valid x → sep_unmapped (perm_unlock x) → sep_unmapped x.
Proof. destruct x as [[]|[]]; repeat sep_unfold; intuition. Qed.
Lemma perm_unlock_unshared x : sep_unshared x → sep_unshared (perm_unlock x).
Proof. destruct x as [[]|[]]; repeat sep_unfold; intuition. Qed.
Lemma perm_unlock_shared x :
  sep_valid x → sep_unshared (perm_unlock x) → sep_unshared x.
Proof. destruct x as [[]|[]]; repeat sep_unfold; intuition. Qed.
Lemma perm_unshared x :
  sep_valid x → Some Locked ⊆ perm_kind x → sep_unshared x.
Proof. destruct (perm_kind_spec x); repeat sep_unfold; intuition. Qed.
Lemma perm_mapped x : Some Readable ⊆ perm_kind x → ¬sep_unmapped x.
Proof. destruct (perm_kind_spec x); repeat sep_unfold; naive_solver. Qed.
Lemma perm_unmapped x :
  sep_valid x → perm_kind x = Some Existing → sep_unmapped x.
Proof. destruct (perm_kind_spec x); repeat sep_unfold; naive_solver. Qed.
Lemma perm_None_unmapped x : sep_valid x → perm_kind x = None → sep_unmapped x.
Proof. destruct (perm_kind_spec x); repeat sep_unfold; naive_solver. Qed.
Lemma perm_token_subseteq x :
  sep_valid x → Some Writable ⊆ perm_kind x → perm_token ⊂ x.
Proof.
  assert (∀ x', x' - 0 = 0 → x' = 0).
  { intros x'. change (x' - 0) with (x' + 0). by rewrite Qcplus_0_r. }
  rewrite strict_spec_alt. unfold perm_token.
  destruct (perm_kind_spec x); repeat sep_unfold; (split; [|intro]);
    simplify_equality'; intuition; exfalso; auto.
Qed.
Lemma perm_splittable x :
  sep_valid x → Some Readable ⊆ perm_kind x → sep_splittable x.
Proof. destruct (perm_kind_spec x); repeat sep_unfold; intuition. Qed.
Lemma perm_splittable_existing x :
  sep_valid x → perm_kind x = Some Existing → sep_splittable x.
Proof. by destruct (perm_kind_spec x); repeat sep_unfold. Qed.

Lemma perm_kind_full : perm_kind perm_full = Some Writable.
Proof. done. Qed.
Lemma perm_kind_lock x :
  sep_valid x → Some Writable ⊆ perm_kind x →
  perm_kind (perm_lock x) = Some Locked.
Proof. by destruct (perm_kind_spec x). Qed.
Lemma perm_kind_half x :
  sep_valid x → perm_kind (½ x) =
    match perm_kind x with 
    | Some Writable => Some Readable | _ => perm_kind x
    end.
Proof.
  assert (∀ x', x' / 2 = 0 → x' = 0).
  { intros. by apply Qcmult_integral_l with (/2); rewrite 1?Qcmult_comm. }
  assert (∀ x', x' / 2 = 1 → x' ≤ 1 → False).
  { intros x'. rewrite (Qcmult_le_mono_pos_r _ _ (/2)) by done.
    by intros -> []. }
  repeat sep_unfold; destruct (perm_kind_spec x); unfold perm_kind; simpl;
    intros; by rewrite ?decide_False by intuition eauto.
Qed.
Lemma perm_kind_token : perm_kind perm_token = Some Existing.
Proof. done. Qed.
Lemma perm_kind_difference_token x :
  perm_token ⊂ x → perm_kind (x ∖ perm_token) = perm_kind x.
Proof.
  rewrite strict_spec_alt.
  destruct (perm_kind_spec x) as [| |y| | |y|]; repeat sep_unfold;
    unfold perm_kind; simpl; intros [? Hneq]; auto.
  * assert (¬0 ≤ -1) by (by intros []); intuition.
  * assert (y ≤ -1 → y ≤ 0) by (by intros; transitivity (-1)).
    assert (y --1 ≠ 0).
    { change 0 with (-1 + 1); rewrite Qcopp_involutive,
        (injective_iff (λ x, x + 1)); contradict Hneq.
      symmetry. unfold perm_token; repeat f_equal; intuition. }
    by rewrite decide_False by done.
  * by change (-0) with 0; rewrite Qcplus_0_r, !decide_False by done.
Qed.
Lemma perm_kind_subseteq x1 x2 : x1 ⊆ x2 → perm_kind x1 ⊆ perm_kind x2.
Proof.
  destruct x1 as [[[x1 y1]|[x1 y1]]|x1], x2 as [[[x2 y2]|[x2 y2]]|x2];
    unfold perm_kind; repeat sep_unfold;
    repeat case_decide; naive_solver eauto using Qcle_antisym.
Qed.
Lemma perm_lock_disjoint x1 x2 :
  Some Writable ⊆ perm_kind x1 → x1 ⊥ x2 → perm_lock x1 ⊥ x2.
Proof.
  assert (¬2 ≤ 1) by (by intros []).
  assert (∀ x, 0 ≤ x → 1 + x ≤ 1 → x = 0).
  { intros x ? Hx. apply (Qcplus_le_mono_l x 0 1) in Hx.
    auto using Qcle_antisym. }
  destruct (perm_kind_spec x1), x2 as [[[x2 y2]|[x2 y2]]|];
    repeat sep_unfold; intuition; simplify_equality'; try done.
  * assert (y2 = 0) as -> by auto.
    rewrite (Qcplus_le_mono_r _ _ x2), Qcplus_0_l. eauto using Qcle_trans.
  * assert (y2 = 0) as -> by auto.
    rewrite (Qcplus_le_mono_r _ _ x2), Qcplus_0_l. eauto using Qcle_trans.
Qed.
Lemma perm_lock_union x1 x2 : perm_lock (x1 ∪ x2) = perm_lock x1 ∪ x2.
Proof. by destruct x1 as [[]|], x2 as [[]|]. Qed.
Lemma perm_unlock_disjoint x1 x2 : x1 ⊥ x2 → perm_unlock x1 ⊥ x2.
Proof. destruct x1 as [[]|], x2 as [[]|]; repeat sep_unfold; naive_solver. Qed.
Lemma perm_unlock_union x1 x2 :
  x1 ⊥ x2 → perm_locked x1 → perm_unlock (x1 ∪ x2) = perm_unlock x1 ∪ x2.
Proof. by destruct x1 as [[]|], x2 as [[]|]. Qed.
Lemma perm_disjoint_full x : perm_full ⊥ x → x = ∅.
Proof.
  destruct x as [[[x y]|[x y]]|];
    repeat sep_unfold; intuition; simplify_equality'.
  assert (y = 0) as ->.
  { apply Qcle_antisym; auto. by apply (Qcplus_le_mono_l y 0 1). }
  repeat f_equal; apply Qcle_antisym; auto; rewrite <-(Qcplus_0_l x); auto.
Qed.
