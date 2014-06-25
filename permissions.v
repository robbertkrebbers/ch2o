(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Import Qcanon.
Require Export orders separation_instances.
Local Open Scope Qc_scope.

(**
Concrete permissions are built from more primitive combinators:
- [freeable]: [Available] describes that the object is alive, and [Freed]
  describes that the object has been freed.
- [lockable]: [Locked] describes that the object has been locked due to
  a sequenced write, and [Unlocked] means that it is not locked
- [tagged]: [Tagged true] describes that the object has been obtained
  using [alloc], and [Tagged false] describes that the object is a block
  scoped variable.
- [counter] is to account for tokens to keep track of parts of the memory
  that are addresseble.
*)
Definition perm := freeable (lockable (tagged (counter Qcanon.Qc) false)).
Instance perm_sep_ops : SeparationOps perm := _.
Instance perm_sep : Separation perm := _.
Typeclasses Opaque perm.

Definition perm_freed : perm := Freed.
Definition perm_full (alloc : bool) : perm :=
  Available (LUnlocked (Tagged (Counter 0 1) alloc)).
Definition perm_token : perm :=
  Available (LUnlocked (Tagged (Counter (-1) ∅) false)).

Inductive pkind :=
  Freeable | Writable | Readable | Locked | Existing.
Instance pkind_dec (k1 k2 : pkind) : Decision (k1 = k2).
Proof. solve_decision. Defined.
Instance pkind_subseteq : SubsetEq pkind := λ k1 k2,
  match k1, k2 with
  | _, Freeable => True
  | (Existing | Readable | Writable | Locked), Writable => True
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
  | Freed => None
  | Available (LUnlocked (Tagged (Counter x' y') alloc)) =>
     if decide (y' = ∅) then
       if decide (x' = 0) then None else Some Existing
     else if decide (y' = 1) then
       if decide (x' = 0 ∧ alloc = true) then Some Freeable else Some Writable
     else Some Readable
  | Available (LLocked _) => Some Locked
  end.
Definition perm_locked (x : perm) : bool :=
  match x with Available (LLocked _) => true | _ => false end.
Definition perm_lock (x : perm) : perm :=
  match x with
  | Available (LUnlocked x') => Available (LLocked x') | _ => x
  end.
Definition perm_unlock (x : perm) : perm :=
  match x with
  | Available (LLocked x') => Available (LUnlocked x') | _ => x
  end.

Inductive perm_kind_view : perm → option pkind → Prop :=
  | perm_kind_None : perm_kind_view Freed None
  | perm_kind_None' alloc :
     perm_kind_view (Available (LUnlocked (Tagged (Counter ∅ 0) alloc))) None
  | perm_kind_Locked x' alloc :
     perm_kind_view (Available (LLocked (Tagged x' alloc))) (Some Locked)
  | perm_kind_Existing alloc x' :
     x' ≠ 0 → perm_kind_view
      (Available (LUnlocked (Tagged (Counter x' ∅) alloc))) (Some Existing)
  | perm_kind_Readable alloc x' y' :
     y' ≠ ∅ → y' ≠ 1 → perm_kind_view
      (Available (LUnlocked (Tagged (Counter x' y') alloc))) (Some Readable)
  | perm_kind_Freeable :
     perm_kind_view
      (Available (LUnlocked (Tagged (Counter 0 1) true))) (Some Freeable)
  | perm_kind_Writable x' :
     perm_kind_view
      (Available (LUnlocked (Tagged (Counter x' 1) false))) (Some Writable)
  | perm_kind_Writable' x' :
     x' ≠ 0 → perm_kind_view
      (Available (LUnlocked (Tagged (Counter x' 1) true))) (Some Writable).
Lemma perm_kind_spec x : perm_kind_view x (perm_kind x).
Proof.
  destruct x as [[[]|[[][]]]|]; simpl; repeat case_decide;
    intuition; simplify_equality'; constructor; auto.
Qed.
Arguments perm_kind _ : simpl never.

Lemma perm_freed_valid : sep_valid perm_freed.
Proof. done. Qed.
Lemma perm_full_valid alloc : sep_valid (perm_full alloc).
Proof. by compute; intuition. Qed.
Lemma perm_token_valid : sep_valid perm_token.
Proof. done. Qed.
Lemma perm_lock_valid x :
  sep_valid x → Some Writable ⊆ perm_kind x → sep_valid (perm_lock x).
Proof. destruct (perm_kind_spec x); repeat sep_unfold; intuition. Qed.
Lemma perm_lock_unmapped_inv x :
  sep_unmapped (perm_lock x) → sep_unmapped x.
Proof. destruct x as [[[]|[[][]]]|]; repeat sep_unfold; intuition. Qed.
Lemma perm_lock_unshared x : sep_unshared x → sep_unshared (perm_lock x).
Proof. destruct x as [[[[][]]|[[][]]]|]; repeat sep_unfold; intuition. Qed.
Lemma perm_unlock_lock x :
  sep_valid x → Some Writable ⊆ perm_kind x → perm_unlock (perm_lock x) = x.
Proof. by destruct (perm_kind_spec x). Qed.
Lemma perm_unlock_valid x : sep_valid x → sep_valid (perm_unlock x).
Proof. destruct x as [[[[][]]|[[][]]]|]; repeat sep_unfold; naive_solver. Qed.
Lemma perm_unlock_unmapped x : sep_unmapped x → sep_unmapped (perm_unlock x).
Proof. destruct x as [[[[][]]|[[][]]]|]; repeat sep_unfold; intuition. Qed.
Lemma perm_unlock_unmapped_inv x :
  sep_valid x → sep_unmapped (perm_unlock x) → sep_unmapped x.
Proof. destruct x as [[[[][]]|[[][]]]|]; repeat sep_unfold; intuition. Qed.
Lemma perm_unlock_unshared x : sep_unshared x → sep_unshared (perm_unlock x).
Proof. destruct x as [[[[][]]|[[][]]]|]; repeat sep_unfold; intuition. Qed.
Lemma perm_unlock_unshared_inv x :
  sep_valid x → sep_unshared (perm_unlock x) → sep_unshared x.
Proof. destruct x as [[[[][]]|[[][]]]|]; repeat sep_unfold; intuition. Qed.
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
  sep_valid x → Some Readable ⊆ perm_kind x → perm_token ⊂ x.
Proof.
  assert (∀ x', x' - 0 = 0 → x' = 0).
  { intros x'. change (x' - 0) with (x' + 0). by rewrite Qcplus_0_r. }
  rewrite strict_spec_alt.
  destruct (perm_kind_spec x); repeat sep_unfold; (split; [|intro]);
    simplify_equality'; intuition; exfalso; auto.
Qed.
Lemma perm_splittable x :
  sep_valid x → Some Readable ⊆ perm_kind x → sep_splittable x.
Proof. destruct (perm_kind_spec x); repeat sep_unfold; intuition. Qed.
Lemma perm_splittable_existing x :
  sep_valid x → perm_kind x = Some Existing → sep_splittable x.
Proof. by destruct (perm_kind_spec x); repeat sep_unfold. Qed.

Lemma perm_kind_full alloc :
  perm_kind (perm_full alloc) = Some (if alloc then Freeable else Writable).
Proof. by destruct alloc. Qed.
Lemma perm_kind_lock x :
  sep_valid x → Some Writable ⊆ perm_kind x →
  perm_kind (perm_lock x) = Some Locked.
Proof. by destruct (perm_kind_spec x). Qed.
Lemma perm_kind_half x :
  sep_valid x →
  perm_kind (½ x) = match perm_kind x with
                    | Some (Writable | Freeable) => Some Readable
                    | _ => perm_kind x
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
  perm_token ⊂ x →
  perm_kind (x ∖ perm_token) = match perm_kind x with
                               | Some Freeable => Some Writable
                               | _ => perm_kind x
                               end.
Proof.
  rewrite strict_spec_alt.
  destruct (perm_kind_spec x) as [| | |? y| | | |y]; repeat sep_unfold;
    unfold perm_kind; simpl; intros [? Hneq]; auto.
  * assert (¬0 ≤ -1) by (by intros []); intuition.
  * assert (y ≤ -1 → y ≤ 0) by (by intros; transitivity (-1)). 
    assert (y --1 ≠ 0).
    { change 0 with (-1 + 1); rewrite Qcopp_involutive,
        (injective_iff (λ x, x + 1)); contradict Hneq.
      symmetry. unfold perm_token; repeat f_equal; intuition. }
    by rewrite decide_False by done.
  * by change (-0) with 0; rewrite Qcplus_0_r, !decide_False by done.
  * by rewrite decide_False by (by intros []).
  * assert (y --1 = 0 → 0 ≤ y → False).
    { rewrite (Qcplus_le_mono_r _ _ (--1)). by intros -> []. }
    by rewrite decide_False by intuition eauto.
Qed.
