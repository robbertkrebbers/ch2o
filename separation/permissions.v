(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Import Qcanon.
Require Export base orders separation_instances.
Local Open Scope Qc_scope.

(**
Concrete permissions are built from more primitive combinators:
- [lockable]: [Locked] describes that the object has been locked due to
  a sequenced write, and [Unlocked] means that it is not locked
- [counter] is to account for tokens to keep track of parts of the memory
  that are addresseble.
*)
Definition perm := (lockable (counter Qcanon.Qc) + Qcanon.Qc)%type.
#[global] Instance perm_sep_ops : SeparationOps perm := _.
#[global] Instance perm_sep : Separation perm := _.
Typeclasses Opaque perm.
Global Hint Extern 0 (Separation _) => apply (_ : Separation perm): core.

Definition perm_readonly : perm := inr 1.
Definition perm_full : perm := inl (LUnlocked (Counter 0 1)).
Definition perm_token : perm := inl (LUnlocked (Counter (-1) ∅)).

Inductive pkind :=
  Writable | Readable | Locked | Existing.
#[global] Instance pkind_dec (k1 k2 : pkind) : Decision (k1 = k2).
Proof. solve_decision. Defined.
#[global] Instance pkind_subseteq : SubsetEq pkind := λ k1 k2,
  match k1, k2 with
  | _, Writable => True
  | (Existing | Readable), Readable => True
  | Existing, Existing => True
  | (Existing | Locked), Locked => True
  | _, _ => False
  end.
#[global] Instance pkind_subseteq_dec : ∀ k1 k2 : pkind, Decision (k1 ⊆ k2).
Proof. intros [] []; apply _. Defined.
#[global] Instance: PartialOrder (@subseteq pkind _).
Proof. by repeat split; repeat intros []. Qed.
#[global] Instance option_pkind_subseteq : SubsetEq (option pkind) := λ k1 k2,
  match k1, k2 with
  | Some k1, Some k2 => k1 ⊆ k2 | None, _ => True | Some _, None => False
  end.
#[global] Instance option_pkind_subseteq_dec : ∀ k1 k2 : option pkind, Decision (k1 ⊆ k2).
Proof. intros [] []; apply _. Defined.
#[global] Instance: PartialOrder (@subseteq (option pkind) _).
Proof. by repeat split; repeat intros []; try destruct p; try destruct p0; try destruct p1. Qed.

Definition perm_kind (γ : perm) : option pkind :=
  match γ with
  | inl (LUnlocked (Counter x' y')) =>
     if decide (y' = ∅) then
       if decide (x' = 0) then None else Some Existing
     else if decide (y' = 1) then Some Writable else Some Readable
  | inl (LLocked _) => Some Locked
  | inr x' => Some Readable
  end.
Definition perm_locked (γ : perm) : bool :=
  match γ with inl (LLocked _) => true | _ => false end.
Definition perm_lock (γ : perm) : perm :=
  match γ with inl (LUnlocked x') => inl (LLocked x') | _ => γ end.
Definition perm_unlock (γ : perm) : perm :=
  match γ with inl (LLocked x') => inl (LUnlocked x') | _ => γ end.

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
Lemma perm_kind_spec γ : perm_kind_view γ (perm_kind γ).
Proof.
  destruct γ as [[[]|[]]|]; simpl; repeat case_decide;
    intuition; simplify_equality'; constructor; auto.
Qed.
Arguments perm_kind _ : simpl never.

Lemma perm_full_valid : sep_valid perm_full.
Proof. done. Qed.
Lemma perm_full_mapped : ¬sep_unmapped perm_full.
Proof. by apply (bool_decide_unpack _). Qed.
Lemma perm_full_unshared : sep_unshared perm_full.
Proof. by apply (bool_decide_unpack _). Qed.
Lemma perm_subseteq_full γ1 γ2 : γ1 = perm_full → γ1 ⊆ γ2 → γ2 = perm_full.
Proof.
  intros ->; destruct γ2 as [[[??]|[c x]]|?];
    repeat sep_unfold; unfold perm_full; intuition; simplify_equality.
  assert (x = 1) as -> by eauto using Qcle_antisym.
  by assert (c = 0) as -> by eauto using Qcle_antisym.
Qed.
Lemma perm_readonly_valid : sep_valid perm_readonly.
Proof. done. Qed.
Lemma perm_readonly_mapped : ¬sep_unmapped perm_readonly.
Proof. by apply (bool_decide_unpack _). Qed.
Lemma perm_token_valid : sep_valid perm_token.
Proof. done. Qed.
Lemma perm_locked_mapped γ : perm_locked γ = true → ¬sep_unmapped γ.
Proof. destruct γ as [[[]|]|[]]; repeat sep_unfold; naive_solver. Qed.
Lemma perm_Readable_locked γ :
  Some Readable ⊆ perm_kind γ → perm_locked γ = false.
Proof. by destruct (perm_kind_spec γ). Qed.
Lemma perm_locked_lock γ :
  Some Writable ⊆ perm_kind γ → perm_locked (perm_lock γ) = true.
Proof. by destruct (perm_kind_spec γ). Qed.
Lemma perm_locked_unlock γ : perm_locked (perm_unlock γ) = false.
Proof. by destruct γ as [[]|[]]. Qed.
Lemma perm_lock_valid γ :
  sep_valid γ → Some Writable ⊆ perm_kind γ → sep_valid (perm_lock γ).
Proof. destruct (perm_kind_spec γ); repeat sep_unfold; intuition. Qed.
Lemma perm_lock_empty γ : perm_lock γ = ∅ → γ = ∅.
Proof. by destruct γ as [[]|?]. Qed.
Lemma perm_lock_unmapped γ :
  Some Writable ⊆ perm_kind γ → sep_unmapped γ → sep_unmapped (perm_lock γ).
Proof. destruct (perm_kind_spec γ); repeat sep_unfold; naive_solver. Qed.
Lemma perm_lock_mapped γ : sep_unmapped (perm_lock γ) → sep_unmapped γ.
Proof. destruct γ as [[]|[]]; repeat sep_unfold; intuition. Qed.
Lemma perm_lock_unshared γ : sep_unshared γ → sep_unshared (perm_lock γ).
Proof. destruct γ as [[]|[]]; repeat sep_unfold; intuition. Qed.
Lemma perm_unlock_lock γ :
  sep_valid γ → Some Writable ⊆ perm_kind γ → perm_unlock (perm_lock γ) = γ.
Proof. by destruct (perm_kind_spec γ). Qed.
Lemma perm_unlock_unlock γ : perm_unlock (perm_unlock γ) = perm_unlock γ.
Proof. by destruct γ as [[]|]. Qed.
Lemma perm_unlock_valid γ : sep_valid γ → sep_valid (perm_unlock γ).
Proof. destruct γ as [[[]|[]]|]; repeat sep_unfold; naive_solver. Qed.
Lemma perm_unlock_empty γ : sep_valid γ → perm_unlock γ = ∅ → γ = ∅.
Proof. destruct γ as [[]|?]; repeat sep_unfold; naive_solver. Qed.
Lemma perm_unlock_unmapped γ : sep_unmapped γ → sep_unmapped (perm_unlock γ).
Proof. destruct γ as [[[]|[]]|]; repeat sep_unfold; intuition. Qed.
Lemma perm_unlock_mapped γ :
  sep_valid γ → sep_unmapped (perm_unlock γ) → sep_unmapped γ.
Proof. destruct γ as [[[]|[]]|[]]; repeat sep_unfold; naive_solver. Qed.
Lemma perm_unlock_unshared γ : sep_unshared γ → sep_unshared (perm_unlock γ).
Proof. destruct γ as [[]|[]]; repeat sep_unfold; intuition. Qed.
Lemma perm_unlock_shared γ :
  sep_valid γ → sep_unshared (perm_unlock γ) → sep_unshared γ.
Proof. destruct γ as [[]|[]]; repeat sep_unfold; intuition. Qed.
Lemma perm_unshared γ :
  sep_valid γ → Some Locked ⊆ perm_kind γ → sep_unshared γ.
Proof. destruct (perm_kind_spec γ); repeat sep_unfold; intuition. Qed.
Lemma perm_mapped γ : Some Readable ⊆ perm_kind γ → ¬sep_unmapped γ.
Proof. destruct (perm_kind_spec γ); repeat sep_unfold; naive_solver. Qed.
Lemma perm_unmapped γ :
  sep_valid γ → perm_kind γ = Some Existing → sep_unmapped γ.
Proof. destruct (perm_kind_spec γ); repeat sep_unfold; naive_solver. Qed.
Lemma perm_None_unmapped γ : sep_valid γ → perm_kind γ = None → sep_unmapped γ.
Proof. destruct (perm_kind_spec γ); repeat sep_unfold; naive_solver. Qed.
Lemma perm_token_subseteq γ :
  sep_valid γ → Some Writable ⊆ perm_kind γ → perm_token ⊂ γ.
Proof.
  assert (∀ x', x' - 0 = 0 → x' = 0).
  { intros x'. change (x' - 0) with (x' + 0). by rewrite Qcplus_0_r. }
  rewrite strict_spec_alt. unfold perm_token.
  destruct (perm_kind_spec γ); repeat sep_unfold; (split; [|intro]);
    simplify_equality'; intuition; exfalso; auto.
Qed.
Lemma perm_splittable γ :
  sep_valid γ → Some Readable ⊆ perm_kind γ → sep_splittable γ.
Proof. destruct (perm_kind_spec γ); repeat sep_unfold; intuition. Qed.
Lemma perm_splittable_existing γ :
  sep_valid γ → perm_kind γ = Some Existing → sep_splittable γ.
Proof. by destruct (perm_kind_spec γ); repeat sep_unfold. Qed.

Lemma perm_kind_full : perm_kind perm_full = Some Writable.
Proof. done. Qed.
Lemma perm_kind_lock γ :
  Some Writable ⊆ perm_kind γ → perm_kind (perm_lock γ) = Some Locked.
Proof. by destruct (perm_kind_spec γ). Qed.
Lemma perm_kind_half γ :
  sep_valid γ → perm_kind (½ γ) =
    match perm_kind γ with 
    | Some Writable => Some Readable | _ => perm_kind γ
    end.
Proof.
  assert (∀ x', x' * /2 = 0 → x' = 0).
  { intros. by apply Qcmult_integral_l with (/2); rewrite 1?Qcmult_comm. }
  assert (∀ x', x' * /2 = 1 → x' ≤ 1 → False).
  { intros x'. rewrite (Qcmult_le_mono_pos_r _ _ (/2)) by done.
    by intros -> []. }
  repeat sep_unfold; destruct (perm_kind_spec γ); unfold perm_kind; simpl;
    intros; by rewrite ?decide_False by intuition eauto.
Qed.
Lemma perm_kind_token : perm_kind perm_token = Some Existing.
Proof. done. Qed.
Lemma perm_kind_difference_token γ :
  perm_token ⊂ γ → perm_kind (γ ∖ perm_token) = perm_kind γ.
Proof.
  rewrite strict_spec_alt.
  destruct (perm_kind_spec γ) as [| |y| | |y|]; repeat sep_unfold;
    unfold perm_kind; simpl; intros [? Hneq]; auto.
  * assert (¬0 ≤ -1) by (by intros []); intuition.
  * assert (y ≤ -1 → y ≤ 0) by (by intros; transitivity (-1)).
    assert (y + 1 ≠ 0).
    { change 0 with (-1 + 1); rewrite (inj_iff (λ x, x + 1)); contradict Hneq.
      symmetry. unfold perm_token; repeat f_equal; intuition. }
    by rewrite decide_False by done.
  * by change (-0) with 0; rewrite Qcplus_0_r, !decide_False by done.
Qed.
Lemma perm_kind_subseteq γ1 γ2 : γ1 ⊆ γ2 → perm_kind γ1 ⊆ perm_kind γ2.
Proof.
  destruct γ1 as [[[x1 y1]|[x1 y1]]|x1], γ2 as [[[x2 y2]|[x2 y2]]|x2];
    unfold perm_kind; repeat sep_unfold;
    repeat case_decide; naive_solver eauto using Qcle_antisym.
Qed.
Lemma perm_lock_disjoint γ1 γ2 :
  Some Writable ⊆ perm_kind γ1 → γ1 ## γ2 → perm_lock γ1 ## γ2.
Proof.
  assert (¬2 ≤ 1) by (by intros []).
  assert (∀ x, 0 ≤ x → 1 + x ≤ 1 → x = 0).
  { intros x ? Hx. apply (Qcplus_le_mono_l x 0 1) in Hx.
    auto using Qcle_antisym. }
  destruct (perm_kind_spec γ1), γ2 as [[[x2 y2]|[x2 y2]]|];
    repeat sep_unfold; intuition; simplify_equality'; try done.
  * assert (y2 = 0) as -> by auto.
    rewrite (Qcplus_le_mono_r _ _ x2), Qcplus_0_l. eauto using Qcle_trans.
  * assert (y2 = 0) as -> by auto.
    rewrite (Qcplus_le_mono_r _ _ x2), Qcplus_0_l. eauto using Qcle_trans.
Qed.
Lemma perm_lock_union γ1 γ2 : perm_lock (γ1 ∪ γ2) = perm_lock γ1 ∪ γ2.
Proof. by destruct γ1 as [[]|], γ2 as [[]|]. Qed.
Lemma perm_unlock_disjoint γ1 γ2 : γ1 ## γ2 → perm_unlock γ1 ## γ2.
Proof. destruct γ1 as [[]|], γ2 as [[]|]; repeat sep_unfold; naive_solver. Qed.
Lemma perm_unlock_union γ1 γ2 :
  γ1 ## γ2 → perm_locked γ1 → perm_unlock (γ1 ∪ γ2) = perm_unlock γ1 ∪ γ2.
Proof. by destruct γ1 as [[]|], γ2 as [[]|]. Qed.
Lemma perm_disjoint_full γ : perm_full ## γ → γ = ∅.
Proof.
  destruct γ as [[[x y]|[x y]]|];
    repeat sep_unfold; intuition; simplify_equality'.
  assert (y = 0) as ->.
  { apply Qcle_antisym; auto. by apply (Qcplus_le_mono_l y 0 1). }
  repeat f_equal; apply Qcle_antisym; auto; rewrite <-(Qcplus_0_l x); auto.
Qed.
