(* Copyright (c) 2012, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects general purpose definitions and theorems on lists that
are not in the Coq standard library. *)
Require Import Permutation.
Require Export base decidable option numbers.

Arguments length {_} _.
Arguments cons {_} _ _.
Arguments app {_} _ _.
Arguments Permutation {_} _ _.
Arguments Forall_cons {_} _ _ _ _ _.

Notation tail := tl.
Notation take := firstn.
Notation drop := skipn.
Notation take_drop := firstn_skipn.
Arguments take {_} !_ !_ /.
Arguments drop {_} !_ !_ /.

Notation "(::)" := cons (only parsing) : C_scope.
Notation "( x ::)" := (cons x) (only parsing) : C_scope.
Notation "(:: l )" := (λ x, cons x l) (only parsing) : C_scope.
Notation "(++)" := app (only parsing) : C_scope.
Notation "( l ++)" := (app l) (only parsing) : C_scope.
Notation "(++ k )" := (λ l, app l k) (only parsing) : C_scope.

(** * General definitions *)
(** Looking up elements and updating elements in a list. *)
Instance list_lookup {A} : Lookup nat (list A) A :=
  fix go (i : nat) (l : list A) {struct l} : option A :=
  match l with
  | [] => None
  | x :: l =>
    match i with
    | 0 => Some x
    | S i => @lookup _ _ _ go i l
    end
  end.
Instance list_alter {A} (f : A → A) : AlterD nat (list A) A f :=
  fix go (i : nat) (l : list A) {struct l} :=
  match l with
  | [] => []
  | x :: l =>
    match i with
    | 0 => f x :: l
    | S i => x :: @alter _ _ _ f go i l
    end
  end.
Instance list_delete {A} : Delete nat (list A) :=
  fix go (i : nat) (l : list A) {struct l} : list A :=
  match l with
  | [] => []
  | x :: l =>
    match i with
    | 0 => l
    | S i => x :: @delete _ _ go i l
    end
  end.
Instance list_insert {A} : Insert nat (list A) A := λ i x,
  alter (λ _, x) i.

Tactic Notation "discriminate_list_equality" hyp(H) :=
  apply (f_equal length) in H;
  repeat (simpl in H || rewrite app_length in H);
  exfalso; lia.
Tactic Notation "discriminate_list_equality" :=
  repeat_on_hyps (fun H => discriminate_list_equality H).

Ltac simplify_list_equality := repeat
  match goal with
  | _ => progress simplify_equality
  | H : _ ++ _ = _ ++ _ |- _ => first
     [ apply app_inv_head in H
     | apply app_inv_tail in H ]
  | H : _ |- _ => discriminate_list_equality H
  end.

(** The function [option_list] converts an element of the option type into
a list. *)
Definition option_list {A} : option A → list A := option_rect _ (λ x, [x]) [].

(** The predicate [prefix_of] holds if the first list is a prefix of the second.
The predicate [suffix_of] holds if the first list is a suffix of the second. *)
Definition prefix_of {A} (l1 l2 : list A) : Prop := ∃ k, l2 = l1 ++ k.
Definition suffix_of {A} (l1 l2 : list A) : Prop := ∃ k, l2 = k ++ l1.

(** The function [replicate n x] generates a list with length [n] of elements
[x]. *)
Fixpoint replicate {A} (n : nat) (x : A) : list A :=
  match n with
  | 0 => []
  | S n => x :: replicate n x
  end.
Definition reverse {A} (l : list A) : list A := rev_append l [].

(** * General theorems *)
Section general_properties.
Context {A : Type}.

Global Instance: ∀ k : list A, Injective (=) (=) (k ++).
Proof. intros ???. apply app_inv_head. Qed.
Global Instance: ∀ k : list A, Injective (=) (=) (++ k).
Proof. intros ???. apply app_inv_tail. Qed.

Lemma list_eq (l1 l2 : list A) : (∀ i, l1 !! i = l2 !! i) → l1 = l2.
Proof.
  revert l2. induction l1; intros [|??] H.
  * done.
  * discriminate (H 0).
  * discriminate (H 0).
  * f_equal; [by injection (H 0) |].
    apply IHl1. intro. apply (H (S _)).
Qed.
Lemma list_eq_nil (l : list A) : (∀ i, l !! i = None) → l = nil.
Proof. intros. by apply list_eq. Qed.

Global Instance list_eq_dec {dec : ∀ x y : A, Decision (x = y)} : ∀ l k,
  Decision (l = k) := list_eq_dec dec.

Lemma nil_or_length_pos (l : list A) : l = [] ∨ length l ≠ 0.
Proof. destruct l; simpl; auto with lia. Qed.
Lemma nil_length (l : list A) : length l = 0 → l = [].
Proof. by destruct l. Qed.
Lemma lookup_nil i : @nil A !! i = None.
Proof. by destruct i. Qed.
Lemma lookup_tail (l : list A) i : tail l !! i = l !! S i.
Proof. by destruct l. Qed.

Lemma lookup_lt_length (l : list A) i :
  is_Some (l !! i) ↔ i < length l.
Proof.
  revert i. induction l.
  * split; by inversion 1.
  * intros [|?]; simpl.
    + split; eauto with arith.
    + by rewrite <-NPeano.Nat.succ_lt_mono.
Qed.
Lemma lookup_lt_length_1 (l : list A) i :
  is_Some (l !! i) → i < length l.
Proof. apply lookup_lt_length. Qed.
Lemma lookup_lt_length_alt (l : list A) i x :
  l !! i = Some x → i < length l.
Proof. intros Hl. by rewrite <-lookup_lt_length, Hl. Qed.
Lemma lookup_lt_length_2 (l : list A) i :
  i < length l → is_Some (l !! i).
Proof. apply lookup_lt_length. Qed.

Lemma lookup_ge_length (l : list A) i :
  l !! i = None ↔ length l ≤ i.
Proof. rewrite eq_None_not_Some, lookup_lt_length. lia. Qed.
Lemma lookup_ge_length_1 (l : list A) i :
  l !! i = None → length l ≤ i.
Proof. by rewrite lookup_ge_length. Qed.
Lemma lookup_ge_length_2 (l : list A) i :
  length l ≤ i → l !! i = None.
Proof. by rewrite lookup_ge_length. Qed.

Lemma lookup_app_l (l1 l2 : list A) i :
  i < length l1 →
  (l1 ++ l2) !! i = l1 !! i.
Proof. revert i. induction l1; intros [|?]; simpl; auto with lia. Qed.
Lemma lookup_app_l_Some (l1 l2 : list A) i x :
  l1 !! i = Some x →
  (l1 ++ l2) !! i = Some x.
Proof. intros. rewrite lookup_app_l; eauto using lookup_lt_length_alt. Qed.

Lemma lookup_app_r (l1 l2 : list A) i :
  (l1 ++ l2) !! (length l1 + i) = l2 !! i.
Proof.
  revert i.
  induction l1; intros [|i]; simpl in *; simplify_equality; auto.
Qed.
Lemma lookup_app_r_alt (l1 l2 : list A) i :
  length l1 ≤ i →
  (l1 ++ l2) !! i = l2 !! (i - length l1).
Proof.
  intros. assert (i = length l1 + (i - length l1)) as Hi by lia.
  rewrite Hi at 1. by apply lookup_app_r.
Qed.
Lemma lookup_app_r_Some (l1 l2 : list A) i x :
  l2 !! i = Some x →
  (l1 ++ l2) !! (length l1 + i) = Some x.
Proof. by rewrite lookup_app_r. Qed.
Lemma lookup_app_r_Some_alt (l1 l2 : list A) i x :
  length l1 ≤ i →
  l2 !! (i - length l1) = Some x →
  (l1 ++ l2) !! i = Some x.
Proof. intro. by rewrite lookup_app_r_alt. Qed.

Lemma lookup_app_inv (l1 l2 : list A) i x :
  (l1 ++ l2) !! i = Some x →
  l1 !! i = Some x ∨ l2 !! (i - length l1) = Some x.
Proof.
  revert i.
  induction l1; intros [|i] ?; simpl in *; simplify_equality; auto.
Qed.

Lemma list_lookup_middle (l1 l2 : list A) (x : A) :
  (l1 ++ x :: l2) !! length l1 = Some x.
Proof. by induction l1; simpl. Qed.

Lemma lookup_take i j (l : list A) :
  j < i → take i l !! j = l !! j.
Proof.
  revert i j. induction l; intros [|i] j ?; trivial.
  * by destruct (le_Sn_0 j).
  * destruct j; simpl; auto with arith.
Qed.

Lemma lookup_take_le i j (l : list A) :
  i ≤ j → take i l !! j = None.
Proof.
  revert i j. induction l; intros [|i] [|j] ?; trivial.
  * by destruct (le_Sn_0 i).
  * simpl; auto with arith.
Qed.

Lemma lookup_drop i j (l : list A) :
  drop i l !! j = l !! (i + j).
Proof. revert i j. induction l; intros [|i] ?; simpl; auto. Qed.

Lemma alter_length (f : A → A) l i :
  length (alter f i l) = length l.
Proof. revert i. induction l; intros [|?]; simpl; auto with lia. Qed.
Lemma insert_length (l : list A) i x :
  length (<[i:=x]>l) = length l.
Proof. apply alter_length. Qed.

Lemma list_lookup_alter (f : A → A) l i :
  alter f i l !! i = f <$> l !! i.
Proof. revert i. induction l. done. intros [|i]. done. apply (IHl i). Qed.
Lemma list_lookup_alter_ne (f : A → A) l i j :
  i ≠ j → alter f i l !! j = l !! j.
Proof.
  revert i j. induction l; [done|].
  intros [|i] [|j] ?; try done. apply (IHl i). congruence.
Qed.
Lemma list_lookup_insert (l : list A) i x :
  i < length l →
  <[i:=x]>l !! i = Some x.
Proof.
  intros Hi. unfold insert, list_insert.
  rewrite list_lookup_alter.
  by feed inversion (lookup_lt_length_2 l i).
Qed.
Lemma list_lookup_insert_ne (l : list A) i j x :
  i ≠ j → <[i:=x]>l !! j = l !! j.
Proof. apply list_lookup_alter_ne. Qed.

Lemma alter_app_l (f : A → A) (l1 l2 : list A) i :
  i < length l1 →
  alter f i (l1 ++ l2) = alter f i l1 ++ l2.
Proof.
  revert i.
  induction l1; intros [|?] ?; simpl in *; f_equal; auto with lia.
Qed.
Lemma alter_app_r (f : A → A) (l1 l2 : list A) i :
  alter f (length l1 + i) (l1 ++ l2) = l1 ++ alter f i l2.
Proof.
  revert i.
  induction l1; intros [|?]; simpl in *; f_equal; auto.
Qed.
Lemma alter_app_r_alt (f : A → A) (l1 l2 : list A) i :
  length l1 ≤ i →
  alter f i (l1 ++ l2) = l1 ++ alter f (i - length l1) l2.
Proof.
  intros. assert (i = length l1 + (i - length l1)) as Hi by lia.
  rewrite Hi at 1. by apply alter_app_r.
Qed.

Lemma insert_app_l (l1 l2 : list A) i x :
  i < length l1 →
  <[i:=x]>(l1 ++ l2) = <[i:=x]>l1 ++ l2.
Proof. apply alter_app_l. Qed.
Lemma insert_app_r (l1 l2 : list A) i x :
  <[length l1 + i:=x]>(l1 ++ l2) = l1 ++ <[i:=x]>l2.
Proof. apply alter_app_r. Qed.
Lemma insert_app_r_alt (l1 l2 : list A) i x :
  length l1 ≤ i →
  <[i:=x]>(l1 ++ l2) = l1 ++ <[i - length l1:=x]>l2.
Proof. apply alter_app_r_alt. Qed.

Lemma take_nil i :
  take i (@nil A) = [].
Proof. by destruct i. Qed.
Lemma take_alter (f : A → A) i j l :
  i ≤ j → take i (alter f j l) = take i l.
Proof.
  intros. apply list_eq. intros jj. destruct (le_lt_dec i jj).
  * by rewrite !lookup_take_le.
  * by rewrite !lookup_take, !list_lookup_alter_ne by lia.
Qed.
Lemma take_insert i j (x : A) l :
  i ≤ j → take i (<[j:=x]>l) = take i l.
Proof take_alter _ _ _ _.

Lemma drop_alter (f : A → A) i j l :
  j < i → drop i (alter f j l) = drop i l.
Proof.
  intros. apply list_eq. intros jj.
  by rewrite !lookup_drop, !list_lookup_alter_ne by lia.
Qed.
Lemma drop_insert i j (x : A) l :
  j < i → drop i (<[j:=x]>l) = drop i l.
Proof drop_alter _ _ _ _.

Lemma insert_consecutive_length (l : list A) i k :
  length (insert_consecutive i k l) = length l.
Proof. revert i. by induction k; intros; simpl; rewrite ?insert_length. Qed.

Lemma not_elem_of_nil (x : A) : x ∉ [].
Proof. by inversion 1. Qed.
Lemma elem_of_nil (x : A) : x ∈ [] ↔ False.
Proof. intuition. by destruct (not_elem_of_nil x). Qed.
Lemma elem_of_nil_inv (l : list A) : (∀ x, x ∉ l) → l = [].
Proof. destruct l. done. by edestruct 1; constructor. Qed.
Lemma elem_of_cons (x y : A) l :
  x ∈ y :: l ↔ x = y ∨ x ∈ l.
Proof.
  split.
  * inversion 1; subst. by left. by right.
  * intros [?|?]; subst. by left. by right.
Qed.
Lemma elem_of_app (x : A) l1 l2 :
  x ∈ l1 ++ l2 ↔ x ∈ l1 ∨ x ∈ l2.
Proof.
  induction l1.
  * split; [by right|]. intros [Hx|]; [|done].
    by destruct (elem_of_nil x).
  * simpl. rewrite !elem_of_cons, IHl1. tauto.
Qed.
Lemma elem_of_list_singleton (x y : A) : x ∈ [y] ↔ x = y.
Proof. rewrite elem_of_cons, elem_of_nil. tauto. Qed.

Global Instance elem_of_list_permutation_proper (x : A) :
  Proper (Permutation ==> iff) (x ∈).
Proof. induction 1; rewrite ?elem_of_nil, ?elem_of_cons; intuition. Qed.

Lemma elem_of_list_split (x : A) l :
  x ∈ l → ∃ l1 l2, l = l1 ++ x :: l2.
Proof.
  induction 1 as [x l|x y l ? [l1 [l2 ?]]].
  * by eexists [], l.
  * subst. by exists (y :: l1) l2.
Qed.

Global Instance elem_of_list_dec {dec : ∀ x y : A, Decision (x = y)} :
  ∀ (x : A) l, Decision (x ∈ l).
Proof.
 intros x. refine (
  fix go l :=
  match l return Decision (x ∈ l) with
  | [] => right (not_elem_of_nil _)
  | y :: l => cast_if_or (decide_rel (=) x y) (go l)
  end); clear go dec; subst; try (by constructor); by inversion 1.
Defined.

Lemma elem_of_list_lookup_1 (l : list A) x :
  x ∈ l → ∃ i, l !! i = Some x.
Proof.
  induction 1 as [|???? IH].
  * by exists 0.
  * destruct IH as [i ?]; auto. by exists (S i).
Qed.
Lemma elem_of_list_lookup_2 (l : list A) i x :
  l !! i = Some x → x ∈ l.
Proof.
  revert i. induction l; intros [|i] ?;
    simpl; simplify_equality; constructor; eauto.
Qed.
Lemma elem_of_list_lookup (l : list A) x :
  x ∈ l ↔ ∃ i, l !! i = Some x.
Proof.
  firstorder eauto using
    elem_of_list_lookup_1, elem_of_list_lookup_2.
Qed.

Lemma NoDup_nil : NoDup (@nil A) ↔ True.
Proof. split; constructor. Qed.
Lemma NoDup_cons (x : A) l : NoDup (x :: l) ↔ x ∉ l ∧ NoDup l.
Proof. split. by inversion 1. intros [??]. by constructor. Qed.
Lemma NoDup_cons_11 (x : A) l : NoDup (x :: l) → x ∉ l.
Proof. rewrite NoDup_cons. by intros [??]. Qed.
Lemma NoDup_cons_12 (x : A) l : NoDup (x :: l) → NoDup l.
Proof. rewrite NoDup_cons. by intros [??]. Qed.
Lemma NoDup_singleton (x : A) : NoDup [x].
Proof. constructor. apply not_elem_of_nil. constructor. Qed.

Lemma NoDup_app (l k : list A) :
  NoDup (l ++ k) ↔ NoDup l ∧ (∀ x, x ∈ l → x ∉ k) ∧ NoDup k.
Proof.
  induction l; simpl.
  * rewrite NoDup_nil.
    setoid_rewrite elem_of_nil. naive_solver.
  * rewrite !NoDup_cons.
    setoid_rewrite elem_of_cons. setoid_rewrite elem_of_app.
    naive_solver.
Qed.

Global Instance NoDup_permutation_proper:
  Proper (Permutation ==> iff) (@NoDup A).
Proof.
  induction 1 as [|x l k Hlk IH | |].
  * by rewrite !NoDup_nil.
  * by rewrite !NoDup_cons, IH, Hlk.
  * rewrite !NoDup_cons, !elem_of_cons. intuition.
  * intuition.
Qed.

Lemma NoDup_Permutation (l k : list A) :
  NoDup l → NoDup k → (∀ x, x ∈ l ↔ x ∈ k) → Permutation l k.
Proof.
  intros Hl. revert k. induction Hl as [|x l Hin ? IH].
  * intros k _ Hk.
    rewrite (elem_of_nil_inv k); [done |].
    intros x. rewrite <-Hk, elem_of_nil. intros [].
  * intros k Hk Hlk.
    destruct (elem_of_list_split x k) as [l1 [l2 ?]]; subst.
    { rewrite <-Hlk. by constructor. }
    rewrite <-Permutation_middle, NoDup_cons in Hk.
    destruct Hk as [??].
    apply Permutation_cons_app, IH; [done |].
    intros y. specialize (Hlk y).
    rewrite <-Permutation_middle, !elem_of_cons in Hlk.
    naive_solver.
Qed.

Global Instance NoDup_dec {dec : ∀ x y : A, Decision (x = y)} :
    ∀ (l : list A), Decision (NoDup l) :=
  fix NoDup_dec l :=
  match l return Decision (NoDup l) with
  | [] => left NoDup_nil_2
  | x :: l =>
    match decide_rel (∈) x l with
    | left Hin => right (λ H, NoDup_cons_11 _ _ H Hin)
    | right Hin =>
      match NoDup_dec l with
      | left H => left (NoDup_cons_2 _ _ Hin H)
      | right H => right (H ∘ NoDup_cons_12 _ _)
      end
    end
  end.

Section remove_dups.
  Context `{!∀ x y : A, Decision (x = y)}.

  Fixpoint remove_dups (l : list A) : list A :=
    match l with
    | [] => []
    | x :: l =>
      if decide_rel (∈) x l then remove_dups l else x :: remove_dups l
    end.

  Lemma elem_of_remove_dups l x :
    x ∈ remove_dups l ↔ x ∈ l.
  Proof.
    split; induction l; simpl; repeat case_decide;
      rewrite ?elem_of_cons; intuition (simplify_equality; auto).
  Qed.

  Lemma remove_dups_nodup l : NoDup (remove_dups l).
  Proof.
    induction l; simpl; repeat case_decide; try constructor; auto.
    by rewrite elem_of_remove_dups.
  Qed.
End remove_dups.

Lemma reverse_nil : reverse [] = @nil A.
Proof. done. Qed.
Lemma reverse_cons (l : list A) x : reverse (x :: l) = reverse l ++ [x].
Proof. unfold reverse. by rewrite <-!rev_alt. Qed.
Lemma reverse_snoc (l : list A) x : reverse (l ++ [x]) = x :: reverse l.
Proof. unfold reverse. by rewrite <-!rev_alt, rev_unit. Qed.
Lemma reverse_app (l1 l2 : list A) :
  reverse (l1 ++ l2) = reverse l2 ++ reverse l1.
Proof. unfold reverse. rewrite <-!rev_alt. apply rev_app_distr. Qed.
Lemma reverse_length (l : list A) : length (reverse l) = length l.
Proof. unfold reverse. rewrite <-!rev_alt. apply rev_length. Qed.
Lemma reverse_involutive (l : list A) : reverse (reverse l) = l.
Proof. unfold reverse. rewrite <-!rev_alt. apply rev_involutive. Qed. 

Lemma replicate_length n (x : A) : length (replicate n x) = n.
Proof. induction n; simpl; auto. Qed.
Lemma lookup_replicate n (x : A) i :
  i < n →
  replicate n x !! i = Some x.
Proof.
  revert i.
  induction n; intros [|?]; naive_solver auto with lia.
Qed.
Lemma lookup_replicate_inv n (x y : A) i :
  replicate n x !! i = Some y → y = x ∧ i < n.
Proof.
  revert i.
  induction n; intros [|?]; naive_solver auto with lia.
Qed.

Section Forall_Exists.
  Context (P : A → Prop).

  Lemma Forall_forall l :
    Forall P l ↔ ∀ x, x ∈ l → P x.
  Proof.
    split.
    * induction 1; inversion 1; subst; auto.
    * intros Hin. induction l; constructor.
      + apply Hin. constructor.
      + apply IHl. intros ??. apply Hin. by constructor.
  Qed.
  Lemma Forall_inv x l : Forall P (x :: l) → P x ∧ Forall P l.
  Proof. by inversion 1. Qed.
  Lemma Forall_inv_1 x l : Forall P (x :: l) → P x.
  Proof. by inversion 1. Qed.
  Lemma Forall_inv_2 x l : Forall P (x :: l) → Forall P l.
  Proof. by inversion 1. Qed.

  Lemma Forall_app l1 l2 : Forall P (l1 ++ l2) ↔ Forall P l1 ∧ Forall P l2.
  Proof.
    split.
    * induction l1; inversion 1; intuition.
    * intros [H ?]. induction H; simpl; intuition.
  Qed.
  Lemma Forall_true l : (∀ x, P x) → Forall P l.
  Proof. induction l; auto. Qed.
  Lemma Forall_impl l (Q : A → Prop) :
    Forall P l → (∀ x, P x → Q x) → Forall Q l.
  Proof. intros H ?. induction H; auto. Defined.
  Lemma Forall_delete l i : Forall P l → Forall P (delete i l).
  Proof.
    intros H. revert i.
    by induction H; intros [|i]; try constructor.
  Qed.
  Lemma Forall_lookup l :
    Forall P l ↔ ∀ i x, l !! i = Some x → P x.
  Proof.
    rewrite Forall_forall.
    setoid_rewrite elem_of_list_lookup.
    naive_solver.
  Qed.
  Lemma Forall_alter f l i :
    Forall P l →
    (∀ x, l !! i = Some x → P x → P (f x)) →
    Forall P (alter f i l).
  Proof.
    intros Hl. revert i.
    induction Hl; simpl; intros [|i]; constructor; auto.
  Qed.

  Lemma Exists_exists l :
    Exists P l ↔ ∃ x, x ∈ l ∧ P x.
  Proof.
    split.
    * induction 1 as [x|y ?? IH].
      + exists x. split. constructor. done.
      + destruct IH as [x [??]]. exists x. split. by constructor. done. 
    * intros [x [Hin ?]]. induction l.
      + by destruct (not_elem_of_nil x).
      + inversion Hin; subst. by left. right; auto.
  Qed.
  Lemma Exists_inv x l : Exists P (x :: l) → P x ∨ Exists P l.
  Proof. inversion 1; intuition trivial. Qed.
  Lemma Exists_app l1 l2 : Exists P (l1 ++ l2) ↔ Exists P l1 ∨ Exists P l2.
  Proof.
    split.
    * induction l1; inversion 1; intuition.
    * intros [H|H].
      + induction H; simpl; intuition.
      + induction l1; simpl; intuition. 
  Qed.

  Lemma Exists_not_Forall l : Exists (not ∘ P) l → ¬Forall P l.
  Proof. induction 1; inversion_clear 1; contradiction. Qed.
  Lemma Forall_not_Exists l : Forall (not ∘ P) l → ¬Exists P l.
  Proof. induction 1; inversion_clear 1; contradiction. Qed.

  Context {dec : ∀ x, Decision (P x)}.

  Fixpoint Forall_Exists_dec l : {Forall P l} + {Exists (not ∘ P) l}.
  Proof.
   refine (
    match l with
    | [] => left _
    | x :: l => cast_if_and (dec x) (Forall_Exists_dec l)
    end); clear Forall_Exists_dec; abstract intuition.
  Defined.

  Lemma not_Forall_Exists l : ¬Forall P l → Exists (not ∘ P) l.
  Proof. intro. destruct (Forall_Exists_dec l); intuition. Qed.

  Global Instance Forall_dec l : Decision (Forall P l) :=
    match Forall_Exists_dec l with
    | left H => left H
    | right H => right (Exists_not_Forall _ H)
    end.

  Fixpoint Exists_Forall_dec l : {Exists P l} + {Forall (not ∘ P) l}.
  Proof.
   refine (
    match l with
    | [] => right _
    | x :: l => cast_if_or (dec x) (Exists_Forall_dec l)
    end); clear Exists_Forall_dec; abstract intuition.
  Defined.

  Lemma not_Exists_Forall l : ¬Exists P l → Forall (not ∘ P) l.
  Proof. intro. destruct (Exists_Forall_dec l); intuition. Qed.

  Global Instance Exists_dec l : Decision (Exists P l) :=
    match Exists_Forall_dec l with
    | left H => left H
    | right H => right (Forall_not_Exists _ H)
    end.
End Forall_Exists.

Section Forall2.
  Context {B} (P : A → B → Prop).

  Lemma Forall2_length l1 l2 :
    Forall2 P l1 l2 → length l1 = length l2.
  Proof. induction 1; simpl; auto. Qed.
  Lemma Forall2_impl (Q : A → B → Prop) l1 l2 :
    Forall2 P l1 l2 → (∀ x y, P x y → Q x y) → Forall2 Q l1 l2.
  Proof. induction 1; auto. Qed.

  Lemma Forall2_unique l k1 k2 :
    Forall2 P l k1 →
    Forall2 P l k2 →
    (∀ x y1 y2, P x y1 → P x y2 → y1 = y2) →
    k1 = k2.
  Proof.
    intros H. revert k2.
    induction H; inversion_clear 1; intros; f_equal; eauto.
  Qed.

  Lemma Forall2_Forall_1 (Q : A → Prop) l k :
    Forall2 P l k →
    Forall (λ y, ∀ x, P x y → Q x) k →
    Forall Q l.
  Proof. induction 1; inversion_clear 1; constructor; eauto. Qed.
  Lemma Forall2_Forall_2 (Q : B → Prop) l k :
    Forall2 P l k →
    Forall (λ x, ∀ y, P x y → Q y) l →
    Forall Q k.
  Proof. induction 1; inversion_clear 1; constructor; eauto. Qed.
End Forall2.

Section Forall2_order.
  Context  (R : relation A).

  Global Instance: PreOrder R → PreOrder (Forall2 R).
  Proof.
    split.
    * intros l. induction l; by constructor.
    * intros l k k' Hlk. revert k'.
      induction Hlk; inversion_clear 1; constructor.
      + etransitivity; eauto.
      + eauto.
  Qed.
End Forall2_order.
End general_properties.

Ltac decompose_elem_of_list := repeat
  match goal with
  | H : ?x ∈ [] |- _ => by destruct (not_elem_of_nil x)
  | H : _ ∈ _ :: _ |- _ => apply elem_of_cons in H; destruct H
  | H : _ ∈ _ ++ _ |- _ => apply elem_of_app in H; destruct H
  end.
Ltac decompose_Forall := repeat
  match goal with
  | H : Forall _ [] |- _ => clear H
  | H : Forall _ (_ :: _) |- _ => apply Forall_inv in H; destruct H
  | H : Forall _ (_ ++ _) |- _ => apply Forall_app in H; destruct H
  end.

(** * Theorems on the prefix and suffix predicates *)
Section prefix_postfix.
  Context {A : Type}.

  Global Instance: PreOrder (@prefix_of A).
  Proof.
    split.
    * intros ?. eexists []. by rewrite app_nil_r.
    * intros ??? [k1 ?] [k2 ?].
      exists (k1 ++ k2). subst. by rewrite app_assoc.
  Qed.

  Lemma prefix_of_nil (l : list A) : prefix_of [] l.
  Proof. by exists l. Qed.
  Lemma prefix_of_nil_not x (l : list A) : ¬prefix_of (x :: l) [].
  Proof. by intros [k E]. Qed.
  Lemma prefix_of_cons x y (l1 l2 : list A) :
    x = y → prefix_of l1 l2 → prefix_of (x :: l1) (y :: l2).
  Proof. intros ? [k E]. exists k. by subst. Qed.
  Lemma prefix_of_cons_inv_1 x y (l1 l2 : list A) :
    prefix_of (x :: l1) (y :: l2) → x = y.
  Proof. intros [k E]. by injection E. Qed.
  Lemma prefix_of_cons_inv_2 x y (l1 l2 : list A) :
    prefix_of (x :: l1) (y :: l2) → prefix_of l1 l2.
  Proof. intros [k E]. exists k. by injection E. Qed.

  Lemma prefix_of_app_l (l1 l2 l3 : list A) :
    prefix_of (l1 ++ l3) l2 → prefix_of l1 l2.
  Proof. intros [k ?]. red. exists (l3 ++ k). subst. by rewrite <-app_assoc. Qed.
  Lemma prefix_of_app_r (l1 l2 l3 : list A) :
    prefix_of l1 l2 → prefix_of l1 (l2 ++ l3).
  Proof. intros [k ?]. exists (k ++ l3). subst. by rewrite app_assoc. Qed.

  Global Instance: PreOrder (@suffix_of A).
  Proof.
    split.
    * intros ?. by eexists [].
    * intros ??? [k1 ?] [k2 ?].
      exists (k2 ++ k1). subst. by rewrite app_assoc.
  Qed.

  Lemma prefix_suffix_reverse (l1 l2 : list A) :
    prefix_of l1 l2 ↔ suffix_of (reverse l1) (reverse l2).
  Proof.
    split; intros [k E]; exists (reverse k).
    * by rewrite E, reverse_app.
    * by rewrite <-(reverse_involutive l2), E, reverse_app, reverse_involutive.
  Qed.
  Lemma suffix_prefix_reverse (l1 l2 : list A) :
    suffix_of l1 l2 ↔ prefix_of (reverse l1) (reverse l2).
  Proof. by rewrite prefix_suffix_reverse, !reverse_involutive. Qed.

  Lemma suffix_of_nil (l : list A) : suffix_of [] l.
  Proof. exists l. by rewrite app_nil_r. Qed.
  Lemma suffix_of_nil_inv (l : list A) : suffix_of l [] → l = [].
  Proof. by intros [[|?] ?]; simplify_list_equality. Qed.
  Lemma suffix_of_cons_nil_inv x (l : list A) : ¬suffix_of (x :: l) [].
  Proof. by intros [[] ?]. Qed.

  Lemma suffix_of_app (l1 l2 k : list A) :
    suffix_of l1 l2 → suffix_of (l1 ++ k) (l2 ++ k).
  Proof. intros [k' E]. exists k'. subst. by rewrite app_assoc. Qed.

  Lemma suffix_of_snoc_inv_1 x y (l1 l2 : list A) :
    suffix_of (l1 ++ [x]) (l2 ++ [y]) → x = y.
  Proof.
    rewrite suffix_prefix_reverse, !reverse_snoc.
    by apply prefix_of_cons_inv_1.
  Qed.
  Lemma suffix_of_snoc_inv_2 x y (l1 l2 : list A) :
    suffix_of (l1 ++ [x]) (l2 ++ [y]) → suffix_of l1 l2.
  Proof.
    rewrite !suffix_prefix_reverse, !reverse_snoc.
    by apply prefix_of_cons_inv_2.
  Qed.

  Lemma suffix_of_cons_l (l1 l2 : list A) x :
    suffix_of (x :: l1) l2 → suffix_of l1 l2.
  Proof. intros [k ?]. exists (k ++ [x]). subst. by rewrite <-app_assoc. Qed.
  Lemma suffix_of_app_l (l1 l2 l3 : list A) :

  suffix_of (l3 ++ l1) l2 → suffix_of l1 l2.
  Proof. intros [k ?]. exists (k ++ l3). subst. by rewrite <-app_assoc. Qed.
  Lemma suffix_of_cons_r (l1 l2 : list A) x :
    suffix_of l1 l2 → suffix_of l1 (x :: l2).
  Proof. intros [k ?]. exists (x :: k). by subst. Qed.
  Lemma suffix_of_app_r (l1 l2 l3 : list A) :
    suffix_of l1 l2 → suffix_of l1 (l3 ++ l2).
  Proof. intros [k ?]. exists (l3 ++ k). subst. by rewrite app_assoc. Qed.

  Lemma suffix_of_cons_inv (l1 l2 : list A) x y :
    suffix_of (x :: l1) (y :: l2) →
      x :: l1 = y :: l2 ∨ suffix_of (x :: l1) l2.
  Proof.
    intros [[|? k] E].
    * by left.
    * right. simplify_equality. by apply suffix_of_app_r.
  Qed.

  Lemma suffix_of_cons_not x (l : list A) : ¬suffix_of (x :: l) l.
  Proof. intros [??]. discriminate_list_equality. Qed.

  Context `{∀ x y : A, Decision (x = y)}.

  Fixpoint strip_prefix (l1 l2 : list A) : list A * (list A * list A) :=
    match l1, l2 with
    | [], l2 => ([], ([], l2))
    | l1, [] => ([], (l1, []))
    | x :: l1, y :: l2 =>
      if decide_rel (=) x y
      then fst_map (x ::) (strip_prefix l1 l2)
      else ([], (x :: l1, y :: l2))
    end.

  Global Instance prefix_of_dec: ∀ l1 l2 : list A,
      Decision (prefix_of l1 l2) :=
    fix go l1 l2 :=
    match l1, l2 return { prefix_of l1 l2 } + { ¬prefix_of l1 l2 } with
    | [], _ => left (prefix_of_nil _)
    | _, [] => right (prefix_of_nil_not _ _)
    | x :: l1, y :: l2 =>
      match decide_rel (=) x y with
      | left Exy =>
        match go l1 l2 with
        | left Hl1l2 => left (prefix_of_cons _ _ _ _ Exy Hl1l2)
        | right Hl1l2 => right (Hl1l2 ∘ prefix_of_cons_inv_2 _ _ _ _)
        end
      | right Exy => right (Exy ∘ prefix_of_cons_inv_1 _ _ _ _)
      end
    end.

  Global Instance suffix_of_dec (l1 l2 : list A) :
    Decision (suffix_of l1 l2).
  Proof.
    refine (cast_if (decide_rel prefix_of (reverse l1) (reverse l2)));
     abstract (by rewrite suffix_prefix_reverse).
  Defined.
End prefix_postfix.

(** The [simplify_suffix_of] tactic removes [suffix_of] hypotheses that are
tautologies, and simplifies [suffix_of] hypotheses involving [(::)] and
[(++)]. *)
Ltac simplify_suffix_of := repeat
  match goal with
  | H : suffix_of (_ :: _) _ |- _ =>
    destruct (suffix_of_cons_not _ _ H)
  | H : suffix_of (_ :: _) [] |- _ =>
    apply suffix_of_nil_inv in H
  | H : suffix_of (_ :: _) (_ :: _) |- _ =>
    destruct (suffix_of_cons_inv _ _ _ _ H); clear H
  | H : suffix_of ?x ?x |- _ => clear H
  | H : suffix_of ?x (_ :: ?x) |- _ => clear H
  | H : suffix_of ?x (_ ++ ?x) |- _ => clear H
  | _ => progress simplify_equality
  end.

(** The [solve_suffix_of] tactic tries to solve goals involving [suffix_of]. It
uses [simplify_suffix_of] to simplify hypotheses and tries to solve [suffix_of]
conclusions. This tactic either fails or proves the goal. *)
Ltac solve_suffix_of := solve [intuition (repeat
  match goal with
  | _ => done
  | _ => progress simplify_suffix_of
  | |- suffix_of [] _ => apply suffix_of_nil
  | |- suffix_of _ _ => reflexivity
  | |- suffix_of _ (_ :: _) => apply suffix_of_cons_r
  | |- suffix_of _ (_ ++ _) => apply suffix_of_app_r
  | H : suffix_of _ _ → False |- _ => destruct H
  end)].
Hint Extern 0 (PropHolds (suffix_of _ _)) =>
  unfold PropHolds; solve_suffix_of : typeclass_instances.

(** * Folding lists *)
Notation foldr := fold_right.
Notation foldr_app := fold_right_app.

Lemma foldr_permutation {A B} (R : relation B)
   `{!Equivalence R}
   (f : A → B → B) (b : B)
   `{!Proper ((=) ==> R ==> R) f}
   (Hf : ∀ a1 a2 b, R (f a1 (f a2 b)) (f a2 (f a1 b))) :
  Proper (Permutation ==> R) (foldr f b).
Proof.
  induction 1; simpl.
  * done.
  * by f_equiv.
  * apply Hf.
  * etransitivity; eauto.
Qed.

(** We redefine [foldl] with the arguments in the same order as in Haskell. *)
Definition foldl {A B} (f : A → B → A) : A → list B → A :=
  fix go a l :=
  match l with
  | [] => a
  | x :: l => go (f a x) l
  end.

Lemma foldl_app {A B} (f : A → B → A) (l k : list B) (a : A) :
  foldl f a (l ++ k) = foldl f (foldl f a l) k.
Proof. revert a. induction l; simpl; auto. Qed.

(** * Monadic operations *)
Instance list_ret: MRet list := λ A x, x :: @nil A.
Instance list_fmap {A B} (f : A → B) : FMapD list f :=
  fix go (l : list A) :=
  match l with
  | [] => []
  | x :: l => f x :: @fmap _ _ _ f go l
  end.
Instance list_bind {A B} (f : A → list B) : MBindD list f :=
  fix go (l : list A) :=
  match l with
  | [] => []
  | x :: l => f x ++ @mbind _ _ _ f go l
  end.
Instance list_join: MJoin list := λ A, mbind id.

Definition mapM `{!MBind M} `{!MRet M} {A B}
    (f : A → M B) : list A → M (list B) :=
  fix go l :=
  match l with
  | [] => mret []
  | x :: l => y ← f x; k ← go l; mret (y :: k)
  end.

Section list_fmap.
  Context {A B : Type} (f : A → B).

  Global Instance: Injective (=) (=) f → Injective (=) (=) (fmap f).
  Proof.
    intros ? l1. induction l1 as [|x l1 IH].
    * by intros [|??].
    * intros [|??]; [done |]; simpl; intros; simplify_equality.
      by f_equal; [apply (injective f) | auto].
  Qed.
  Lemma fmap_app l1 l2 : f <$> l1 ++ l2 = (f <$> l1) ++ (f <$> l2).
  Proof. induction l1; simpl; by f_equal. Qed.
  Lemma fmap_cons_inv y l k :
    f <$> l = y :: k → ∃ x l', y = f x ∧ l = x :: l'.
  Proof. intros. destruct l; simpl; simplify_equality; eauto. Qed.
  Lemma fmap_app_inv l k1 k2 :
    f <$> l = k1 ++ k2 → ∃ l1 l2, k1 = f <$> l1 ∧ k2 = f <$> l2 ∧ l = l1 ++ l2.
  Proof.
    revert l. induction k1 as [|y k1 IH]; simpl.
    * intros l ?. by eexists [], l.
    * intros [|x l] ?; simpl; simplify_equality.
      destruct (IH l) as [l1 [l2 [? [??]]]]; subst; [done |].
      by exists (x :: l1) l2.
  Qed.

  Lemma fmap_length l : length (f <$> l) = length l.
  Proof. induction l; simpl; by f_equal. Qed.
  Lemma fmap_reverse l : f <$> reverse l = reverse (f <$> l).
  Proof.
    induction l; simpl; [done |].
    by rewrite !reverse_cons, fmap_app, IHl.
  Qed.

  Lemma list_lookup_fmap l i : (f <$> l) !! i = f <$> (l !! i).
  Proof. revert i. induction l; by intros [|]. Qed.
  Lemma list_alter_fmap (g : A → A) (h : B → B) l i :
    Forall (λ x, f (g x) = h (f x)) l →
    f <$> alter g i l = alter h i (f <$> l).
  Proof.
    intros Hl. revert i.
    induction Hl; intros [|i]; simpl; f_equal; auto.
  Qed.
  Lemma elem_of_list_fmap_1 l x : x ∈ l → f x ∈ f <$> l.
  Proof. induction 1; simpl; rewrite elem_of_cons; intuition. Qed.
  Lemma elem_of_list_fmap_1_alt l x y : x ∈ l → y = f x → y ∈ f <$> l.
  Proof. intros. subst. by apply elem_of_list_fmap_1. Qed.
  Lemma elem_of_list_fmap_2 l x : x ∈ f <$> l → ∃ y, x = f y ∧ y ∈ l.
  Proof.
    induction l as [|y l IH]; simpl; intros; decompose_elem_of_list.
    + exists y. split; [done | by left].
    + destruct IH as [z [??]]. done. exists z. split; [done | by right].
  Qed.
  Lemma elem_of_list_fmap l x : x ∈ f <$> l ↔ ∃ y, x = f y ∧ y ∈  l.
  Proof. firstorder eauto using elem_of_list_fmap_1_alt, elem_of_list_fmap_2. Qed.

  Lemma Forall_fmap (l : list A) (P : B → Prop) :
    Forall P (f <$> l) ↔ Forall (P ∘ f) l.
  Proof.
    induction l; split; inversion_clear 1; constructor; firstorder auto.
  Qed.

  Lemma mapM_fmap (g : B → option A) (l : list A) :
    (∀ x, g (f x) = Some x) →
    mapM g (f <$> l) = Some l.
  Proof.
    intros E. induction l; simpl.
    * done.
    * by rewrite E, IHl.
  Qed.
  Lemma mapM_fmap_inv (g : B → option A) (l : list A) (k : list B) :
    (∀ x y, g y = Some x → y = f x) →
    mapM g k = Some l →
    k = f <$> l.
  Proof.
    intros Hgf. revert l; induction k as [|y k]; intros [|x l] ?;
      simplify_option_equality; f_equiv; eauto.
  Qed.
End list_fmap.

Section list_bind.
  Context {A B : Type} (f : A → list B).

  Lemma bind_app (l1 l2 : list A) :
    (l1 ++ l2) ≫= f = (l1 ≫= f) ++ (l2 ≫= f).
  Proof.
    induction l1; simpl; [done|].
    by rewrite <-app_assoc, IHl1.
  Qed.
  Lemma elem_of_list_bind (x : B) (l : list A) :
    x ∈ l ≫= f ↔ ∃ y, x ∈ f y ∧ y ∈ l.
  Proof.
    split.
    * induction l as [|y l IH]; simpl; intros; decompose_elem_of_list.
      + exists y. split; [done | by left].
      + destruct IH as [z [??]]. done.
        exists z. split; [done | by right].
    * intros [y [Hx Hy]].
      induction Hy; simpl; rewrite elem_of_app; intuition.
  Qed.
End list_bind.

Section list_ret_join.
  Context {A : Type}.

  Lemma elem_of_list_ret (x y : A) :
    x ∈ @mret list _ A y ↔ x = y.
  Proof. apply elem_of_list_singleton. Qed.
  Lemma elem_of_list_join (x : A) (ll : list (list A)) :
    x ∈ mjoin ll ↔ ∃ l, x ∈ l ∧ l ∈ ll.
  Proof. unfold mjoin, list_join. by rewrite elem_of_list_bind. Qed.

  Lemma join_nil (ls : list (list A)) :
    mjoin ls = [] ↔ Forall (= nil) ls.
  Proof.
    unfold mjoin, list_join. split.
    * by induction ls as [|[|??] ?]; constructor; auto.
    * by induction 1 as [|[|??] ?].
  Qed.
  Lemma join_nil_1 (ls : list (list A)) :
    mjoin ls = [] → Forall (= nil) ls.
  Proof. by rewrite join_nil. Qed.
  Lemma join_nil_2 (ls : list (list A)) :
    Forall (= nil) ls → mjoin ls = [].
  Proof. by rewrite join_nil. Qed.

  Lemma join_length (ls : list (list A)) :
    length (mjoin ls) = foldr (plus ∘ length) 0 ls.
  Proof.
    unfold mjoin, list_join.
    by induction ls; simpl; rewrite ?app_length; f_equal.
  Qed.
  Lemma join_length_same (ls : list (list A)) n :
    Forall (λ l, length l = n) ls →
    length (mjoin ls) = length ls * n.
  Proof. rewrite join_length. by induction 1; simpl; f_equal. Qed.

  Lemma lookup_join_same_length (ls : list (list A)) n i :
    n ≠ 0 →
    Forall (λ l, length l = n) ls →
    mjoin ls !! i = ls !! (i `div` n) ≫= (!! (i `mod` n)).
  Proof.
    intros Hn Hls. revert i. unfold mjoin, list_join.
    induction Hls as [|l ls ? Hls IH]; simpl; [done |]. intros i.
    destruct (decide (i < n)) as [Hin|Hin].
    * rewrite <-(NPeano.Nat.div_unique i n 0 i) by lia.
      rewrite <-(NPeano.Nat.mod_unique i n 0 i) by lia.
      simpl. rewrite lookup_app_l; auto with lia.
    * replace i with ((i - n) + 1 * n) by lia.
      rewrite NPeano.Nat.div_add, NPeano.Nat.mod_add by done.
      replace (i - n + 1 * n) with i by lia.
      rewrite (plus_comm _ 1), lookup_app_r_alt, IH by lia.
      by subst.
  Qed.

  (* This should be provable using the previous lemma in a shorter way *)
  Lemma alter_join_same_length f (ls : list (list A)) n i :
    n ≠ 0 →
    Forall (λ l, length l = n) ls →
    alter f i (mjoin ls) = mjoin (alter (alter f (i `mod` n)) (i `div` n) ls).
  Proof.
    intros Hn Hls. revert i. unfold mjoin, list_join.
    induction Hls as [|l ls ? Hls IH]; simpl; [done |]. intros i.
    destruct (decide (i < n)) as [Hin|Hin].
    * rewrite <-(NPeano.Nat.div_unique i n 0 i) by lia.
      rewrite <-(NPeano.Nat.mod_unique i n 0 i) by lia.
      simpl. rewrite alter_app_l; auto with lia.
    * replace i with ((i - n) + 1 * n) by lia.
      rewrite NPeano.Nat.div_add, NPeano.Nat.mod_add by done.
      replace (i - n + 1 * n) with i by lia.
      rewrite (plus_comm _ 1), alter_app_r_alt, IH by lia.
      by subst.
  Qed.
  Lemma insert_join_same_length (ls : list (list A)) n i x :
    n ≠ 0 →
    Forall (λ l, length l = n) ls →
    <[i:=x]>(mjoin ls) = mjoin (alter <[i `mod` n:=x]> (i `div` n) ls).
  Proof. apply alter_join_same_length. Qed.
End list_ret_join.

Ltac simplify_list_fmap_equality := repeat
  match goal with
  | _ => progress simplify_equality
  | H : _ <$> _ = _ :: _ |- _ =>
    apply fmap_cons_inv in H; destruct H as [? [? [??]]]
  | H : _ :: _ = _ <$> _ |- _ => symmetry in H
  | H : _ <$> _ = _ ++ _ |- _ =>
    apply fmap_app_inv in H; destruct H as [? [? [? [??]]]]
  | H : _ ++ _ = _ <$> _ |- _ => symmetry in H
  end.

(** * Indexed folds and maps *)
(** We define stronger variants of map and fold that also take the index of the
element into account. *)
Definition imap_go {A B} (f : nat → A → B) : nat → list A → list B :=
  fix go (n : nat) (l : list A) :=
  match l with
  | [] => []
  | x :: l => f n x :: go (S n) l
  end.
Definition imap {A B} (f : nat → A → B) : list A → list B := imap_go f 0.

Definition ifoldr {A B} (f : nat → B → A → A)
    (a : nat → A) : nat → list B → A :=
  fix go (n : nat) (l : list B) : A :=
  match l with
  | nil => a n
  | b :: l => f n b (go (S n) l)
  end.

Lemma ifoldr_app {A B} (f : nat → B → A → A) (a : nat → A)
    (l1 l2 : list B) n :
  ifoldr f a n (l1 ++ l2) = ifoldr f (λ n, ifoldr f a n l2) n l1.
Proof.
  revert n a. induction l1 as [| b l1 IH ]; intros; simpl; f_equal; auto.
Qed.

(** * Lists of the same length *)
(** The [same_length] view allows convenient induction over two lists with the
same length. *)
Section same_length.
  Context {A B : Type}.

  Inductive same_length : list A → list B → Prop :=
    | same_length_nil : same_length [] []
    | same_length_cons x y l k :
      same_length l k → same_length (x :: l) (y :: k).

  Lemma same_length_length l k :
    same_length l k ↔ length l = length k.
  Proof.
    split.
    * induction 1; simpl; auto.
    * revert k. induction l; intros [|??]; try discriminate;
      constructor; auto with arith.
  Qed.

  Lemma same_length_lookup l k i :
    same_length l k → is_Some (l !! i) → is_Some (k !! i).
  Proof.
    rewrite same_length_length.
    setoid_rewrite lookup_lt_length.
    intros E. by rewrite E.
  Qed.

  Lemma Forall2_app_inv (P : A → B → Prop) l1 l2 k1 k2 :
    same_length l1 k1 →
    Forall2 P (l1 ++ l2) (k1 ++ k2) → Forall2 P l2 k2.
  Proof. induction 1. done. inversion 1; subst; auto. Qed.
End same_length.

Instance: ∀ A, Reflexive (@same_length A A).
Proof. intros A l. induction l; try constructor; auto. Qed.

(** * Zipping lists *)
Definition zip_with {A B C} (f : A → B → C) : list A → list B → list C :=
  fix go l1 l2 :=
  match l1, l2 with
  | x1 :: l1, x2 :: l2 => f x1 x2 :: go l1 l2
  | _ , _ => []
  end.

Section zip_with.
  Context {A B C : Type} (f : A → B → C).

  Lemma zip_with_length l1 l2 :
    length l1 ≤ length l2 →
    length (zip_with f l1 l2) = length l1.
  Proof.
    revert l2.
    induction l1; intros [|??]; simpl; auto with lia.
  Qed.

  Lemma zip_with_fmap_fst_le (g : C → A) l1 l2 :
    (∀ x y, g (f x y) = x) →
    length l1 ≤ length l2 →
    g <$> zip_with f l1 l2 = l1.
  Proof.
    revert l2.
    induction l1; intros [|??] ??; simpl in *; f_equal; auto with lia.
  Qed.
  Lemma zip_with_fmap_snd_le (g : C → B) l1 l2 :
    (∀ x y, g (f x y) = y) →
    length l2 ≤ length l1 →
    g <$> zip_with f l1 l2 = l2.
  Proof.
    revert l1.
    induction l2; intros [|??] ??; simpl in *; f_equal; auto with lia.
  Qed.
  Lemma zip_with_fmap_fst (g : C → A) l1 l2 :
    (∀ x y, g (f x y) = x) →
    same_length l1 l2 →
    g <$> zip_with f l1 l2 = l1.
  Proof. induction 2; simpl; f_equal; auto. Qed.
  Lemma zip_with_fmap_snd (g : C → B) l1 l2 :
    (∀ x y, g (f x y) = y) →
    same_length l1 l2 →
    g <$> zip_with f l1 l2 = l2.
  Proof. induction 2; simpl; f_equal; auto. Qed.

  Lemma zip_with_Forall_fst (P : A → Prop) (Q : C → Prop) l1 l2 :
    Forall P l1 →
    Forall (λ y, ∀ x, P x → Q (f x y)) l2 →
    Forall Q (zip_with f l1 l2).
  Proof.
    intros Hl1. revert l2.
    induction Hl1; destruct 1; simpl in *; auto.
  Qed.

  Lemma zip_with_Forall_snd (P : B → Prop) (Q : C → Prop) l1 l2 :
    Forall (λ x, ∀ y, P y → Q (f x y)) l1 →
    Forall P l2 →
    Forall Q (zip_with f l1 l2).
  Proof.
    intros Hl1. revert l2.
    induction Hl1; destruct 1; simpl in *; auto.
  Qed.
End zip_with.

Notation zip := (zip_with pair).

Section zip.
  Context {A B : Type}.

  Lemma zip_length (l1 : list A) (l2 : list B) :
    length l1 ≤ length l2 →
    length (zip l1 l2) = length l1.
  Proof. by apply zip_with_length. Qed.

  Lemma zip_fmap_fst_le (l1 : list A) (l2 : list B) :
    length l1 ≤ length l2 →
    fst <$> zip l1 l2 = l1.
  Proof. by apply zip_with_fmap_fst_le. Qed.
  Lemma zip_fmap_snd (l1 : list A) (l2 : list B) :
    length l2 ≤ length l1 →
    snd <$> zip l1 l2 = l2.
  Proof. by apply zip_with_fmap_snd_le. Qed.

  Lemma zip_fst (l1 : list A) (l2 : list B) :
    same_length l1 l2 →
    fst <$> zip l1 l2 = l1.
  Proof. by apply zip_with_fmap_fst. Qed.
  Lemma zip_snd (l1 : list A) (l2 : list B) :
    same_length l1 l2 → snd <$> zip l1 l2 = l2.
  Proof. by apply zip_with_fmap_snd. Qed.
End zip.

Definition zipped_map {A B} (f : list A → list A → A → B) :
    list A → list A → list B :=
  fix go l k :=
  match k with
  | [] => []
  | x :: k => f l k x :: go (x :: l) k
  end.

Lemma elem_of_zipped_map {A B} (f : list A → list A → A → B) l k x :
  x ∈ zipped_map f l k ↔
    ∃ k' k'' y, k = k' ++ [y] ++ k'' ∧ x = f (reverse k' ++ l) k'' y.
Proof.
  split.
  * revert l. induction k as [|z k IH]; simpl;
      intros l ?; decompose_elem_of_list.
    + by eexists [], k, z.
    + destruct (IH (z :: l)) as [k' [k'' [y [??]]]]; [done |]; subst.
      eexists (z :: k'), k'', y. split; [done |].
      by rewrite reverse_cons, <-app_assoc.
  * intros [k' [k'' [y [??]]]]; subst.
    revert l. induction k' as [|z k' IH]; intros l.
    + by left.
    + right. by rewrite reverse_cons, <-!app_assoc.
Qed.

Section zipped_list_ind.
  Context {A} (P : list A → list A → Prop).
  Context (Pnil : ∀ l, P l []).
  Context (Pcons : ∀ l k x, P (x :: l) k → P l (x :: k)).

  Fixpoint zipped_list_ind l k : P l k :=
    match k with
    | [] => Pnil _
    | x :: k => Pcons _ _ _ (zipped_list_ind (x :: l) k)
    end.
End zipped_list_ind.

Inductive zipped_Forall {A} (P : list A → list A → A → Prop) :
    list A → list A → Prop :=
  | zipped_Forall_nil l : zipped_Forall P l []
  | zipped_Forall_cons l k x :
     P l k x →
     zipped_Forall P (x :: l) k →
     zipped_Forall P l (x :: k).
Arguments zipped_Forall_nil {_ _} _.
Arguments zipped_Forall_cons {_ _} _ _ _ _ _.

Lemma zipped_Forall_app {A} (P : list A → list A → A → Prop) l k k' :
  zipped_Forall P l (k ++ k') → zipped_Forall P (reverse k ++ l) k'.
Proof.
  revert l. induction k as [|x k IH]; simpl; [done |].
  inversion_clear 1. rewrite reverse_cons, <-app_assoc.
  by apply IH.
Qed.

(** * Set operations on lists *)
Section list_set_operations.
  Context {A} {dec : ∀ x y : A, Decision (x = y)}.

  Fixpoint list_difference (l k : list A) : list A :=
    match l with
    | [] => []
    | x :: l =>
      if decide_rel (∈) x k
      then list_difference l k
      else x :: list_difference l k
    end.
  Lemma elem_of_list_difference l k x :
    x ∈ list_difference l k ↔ x ∈ l ∧ x ∉ k.
  Proof.
    split; induction l; simpl; try case_decide;
      rewrite ?elem_of_nil, ?elem_of_cons; intuition congruence.
  Qed.
  Lemma list_difference_nodup l k :
    NoDup l → NoDup (list_difference l k).
  Proof.
    induction 1; simpl; try case_decide.
    * constructor.
    * done.
    * constructor. rewrite elem_of_list_difference; intuition. done.
  Qed.

  Fixpoint list_intersection (l k : list A) : list A :=
    match l with
    | [] => []
    | x :: l =>
      if decide_rel (∈) x k
      then x :: list_intersection l k
      else list_intersection l k
    end.
  Lemma elem_of_list_intersection l k x :
    x ∈ list_intersection l k ↔ x ∈ l ∧ x ∈ k.
  Proof.
    split; induction l; simpl; repeat case_decide;
      rewrite ?elem_of_nil, ?elem_of_cons; intuition congruence.
  Qed.
  Lemma list_intersection_nodup l k :
    NoDup l → NoDup (list_intersection l k).
  Proof.
    induction 1; simpl; try case_decide.
    * constructor.
    * constructor. rewrite elem_of_list_intersection; intuition. done.
    * done.
  Qed.
End list_set_operations.
