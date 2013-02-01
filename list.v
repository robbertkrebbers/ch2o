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

Notation Forall_nil_2 := Forall_nil.
Notation Forall_cons_2 := Forall_cons.

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
(** Looking up, updating, and deleting elements of a list. *)
Instance list_lookup {A} : Lookup nat A (list A) :=
  fix go (i : nat) (l : list A) {struct l} : option A :=
  match l with
  | [] => None
  | x :: l =>
    match i with
    | 0 => Some x
    | S i => @lookup _ _ _ go i l
    end
  end.
Instance list_alter {A} (f : A → A) : AlterD nat A (list A) f :=
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
Instance list_insert {A} : Insert nat A (list A) := λ i x,
  alter (λ _, x) i.

(** The function [option_list] converts an element of the option type into
a list. *)
Definition option_list {A} : option A → list A := option_rect _ (λ x, [x]) [].

(** The function [filter P l] returns the list of elements of [l] that
satisfies [P]. The order remains unchanged. *)
Instance list_filter {A} : Filter A (list A) :=
  fix go P _ l :=
  match l with
  | [] => []
  | x :: l =>
     if decide (P x)
     then x :: @filter _ _ (@go) _ _ l
     else @filter _ _ (@go) _ _ l
  end.

(** The function [replicate n x] generates a list with length [n] of elements
with value [x]. *)
Fixpoint replicate {A} (n : nat) (x : A) : list A :=
  match n with
  | 0 => []
  | S n => x :: replicate n x
  end.

(** The function [reverse l] returns the elements of [l] in reverse order. *)
Definition reverse {A} (l : list A) : list A := rev_append l [].

(** The function [resize n y l] takes the first [n] elements of [l] in case
[length l ≤ n], and otherwise appends elements with value [x] to [l] to obtain
a list of length [n]. *)
Fixpoint resize {A} (n : nat) (y : A) (l : list A) : list A :=
  match l with
  | [] => replicate n y
  | x :: l =>
    match n with
    | 0 => []
    | S n => x :: resize n y l
    end
  end.
Arguments resize {_} !_ _ !_.

(** The predicate [suffix_of] holds if the first list is a suffix of the second.
The predicate [prefix_of] holds if the first list is a prefix of the second. *)
Definition suffix_of {A} (l1 l2 : list A) : Prop := ∃ k, l2 = k ++ l1.
Definition prefix_of {A} (l1 l2 : list A) : Prop := ∃ k, l2 = l1 ++ k.
Definition max_prefix_of `{∀ x y : A, Decision (x = y)} :
    list A → list A → list A * list A * list A :=
  fix go l1 l2 :=
  match l1, l2 with
  | [], l2 => ([], l2, [])
  | l1, [] => (l1, [], [])
  | x1 :: l1, x2 :: l2 =>
     if decide_rel (=) x1 x2
     then snd_map (x1 ::) (go l1 l2)
     else (x1 :: l1, x2 :: l2, [])
  end.
Definition max_suffix_of `{∀ x y : A, Decision (x = y)} (l1 l2 : list A) :
    list A * list A * list A :=
  match max_prefix_of (reverse l1) (reverse l2) with
  | (k1, k2, k3) => (reverse k1, reverse k2, reverse k3)
  end.

(** * Tactics on lists *)
Lemma cons_inv {A} (l1 l2 : list A) x1 x2 :
  x1 :: l1 = x2 :: l2 → x1 = x2 ∧ l1 = l2.
Proof. by injection 1. Qed.

(** The tactic [discriminate_list_equality] discharges goals containing
invalid list equalities as an assumption. *)
Tactic Notation "discriminate_list_equality" hyp(H) :=
  apply (f_equal length) in H;
  repeat (simpl in H || rewrite app_length in H);
  exfalso; lia.
Tactic Notation "discriminate_list_equality" :=
  solve [repeat_on_hyps (fun H => discriminate_list_equality H)].

(** The tactic [simplify_list_equality] simplifies assumptions involving
equalities on lists. *)
Ltac simplify_list_equality := repeat
  match goal with
  | H : _ :: _ = _ :: _ |- _ =>
     apply cons_inv in H; destruct H
     (* to circumvent bug #2939 in some situations *)
  | H : _ ++ _ = _ ++ _ |- _ => first
     [ apply app_inj_tail in H; destruct H
     | apply app_inv_head in H
     | apply app_inv_tail in H ]
  | H : [?x] !! ?i = Some ?y |- _ =>
     destruct i; [change (Some x = Some y) in H|discriminate]
  | _ => progress simplify_equality
  | H : _ |- _ => discriminate_list_equality H
  end.

(** * General theorems *)
Section general_properties.
Context {A : Type}.

Global Instance: ∀ x : A, Injective (=) (=) (x ::).
Proof. by injection 1. Qed.
Global Instance: ∀ l : list A, Injective (=) (=) (:: l).
Proof. by injection 1. Qed.
Global Instance: ∀ k : list A, Injective (=) (=) (k ++).
Proof. intros ???. apply app_inv_head. Qed.
Global Instance: ∀ k : list A, Injective (=) (=) (++ k).
Proof. intros ???. apply app_inv_tail. Qed.
Global Instance: Associative (=) (@app A).
Proof. intros ???. apply app_assoc. Qed.
Global Instance: LeftId (=) [] (@app A).
Proof. done. Qed.
Global Instance: RightId (=) [] (@app A).
Proof. intro. apply app_nil_r. Qed.

Lemma app_inj (l1 k1 l2 k2 : list A) :
  length l1 = length k1 →
  l1 ++ l2 = k1 ++ k2 → l1 = k1 ∧ l2 = k2.
Proof. revert k1. induction l1; intros [|??]; naive_solver. Qed.

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
Definition list_singleton_dec (l : list A) : { x | l = [x] } + { length l ≠ 1 }.
Proof.
 by refine (
  match l with
  | [x] => inleft (x ↾ _)
  | _ => inright _
  end).
Defined.

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

Lemma list_eq_length_eq (l1 l2 : list A) :
  length l2 = length l1 →
  (∀ i x y, l1 !! i = Some x → l2 !! i = Some y → x = y) →
  l1 = l2.
Proof.
  intros Hlength Hlookup. apply list_eq. intros i.
  destruct (l2 !! i) as [x|] eqn:E.
  * feed inversion (lookup_lt_length_2 l1 i) as [y].
    { pose proof (lookup_lt_length_alt l2 i x E). lia. }
    f_equal. eauto.
  * rewrite lookup_ge_length in E |- *. lia.
Qed.

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

Lemma list_lookup_other (l : list A) i x :
  length l ≠ 1 →
  l !! i = Some x →
  ∃ j y, j ≠ i ∧ l !! j = Some y.
Proof.
  intros Hl Hi.
  destruct i; destruct l as [|x0 [|x1 l]]; simpl in *; simplify_equality.
  * by exists 1 x1.
  * by exists 0 x0.
Qed.

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

Lemma insert_consecutive_length (l : list A) i k :
  length (insert_consecutive i k l) = length l.
Proof. revert i. by induction k; intros; simpl; rewrite ?insert_length. Qed.

Lemma not_elem_of_nil (x : A) : x ∉ [].
Proof. by inversion 1. Qed.
Lemma elem_of_nil (x : A) : x ∈ [] ↔ False.
Proof. intuition. by destruct (not_elem_of_nil x). Qed.
Lemma elem_of_nil_inv (l : list A) : (∀ x, x ∉ l) → l = [].
Proof. destruct l. done. by edestruct 1; constructor. Qed.
Lemma elem_of_cons (l : list A) x y :
  x ∈ y :: l ↔ x = y ∨ x ∈ l.
Proof.
  split.
  * inversion 1; subst. by left. by right.
  * intros [?|?]; subst. by left. by right.
Qed.
Lemma not_elem_of_cons (l : list A) x y :
  x ∉ y :: l ↔ x ≠ y ∧ x ∉ l.
Proof. rewrite elem_of_cons. tauto. Qed.
Lemma elem_of_app (l1 l2 : list A) x :
  x ∈ l1 ++ l2 ↔ x ∈ l1 ∨ x ∈ l2.
Proof.
  induction l1.
  * split; [by right|]. intros [Hx|]; [|done].
    by destruct (elem_of_nil x).
  * simpl. rewrite !elem_of_cons, IHl1. tauto.
Qed.
Lemma not_elem_of_app (l1 l2 : list A) x :
  x ∉ l1 ++ l2 ↔ x ∉ l1 ∧ x ∉ l2.
Proof. rewrite elem_of_app. tauto. Qed.

Lemma elem_of_list_singleton (x y : A) : x ∈ [y] ↔ x = y.
Proof. rewrite elem_of_cons, elem_of_nil. tauto. Qed.

Global Instance elem_of_list_permutation_proper (x : A) :
  Proper (Permutation ==> iff) (x ∈).
Proof. induction 1; rewrite ?elem_of_nil, ?elem_of_cons; intuition. Qed.

Lemma elem_of_list_split (l : list A) x :
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

Global Instance NoDup_proper:
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
    destruct (elem_of_list_split k x) as [l1 [l2 ?]]; subst.
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

Lemma elem_of_list_filter `{∀ x : A, Decision (P x)} l x :
  x ∈ filter P l ↔ P x ∧ x ∈ l.
Proof.
  unfold filter. induction l; simpl; repeat case_decide;
     rewrite ?elem_of_nil, ?elem_of_cons; naive_solver.
Qed.
Lemma filter_nodup P `{∀ x : A, Decision (P x)} l :
  NoDup l → NoDup (filter P l).
Proof.
  unfold filter. induction 1; simpl; repeat case_decide;
    rewrite ?NoDup_nil, ?NoDup_cons, ?elem_of_list_filter; tauto.
Qed.

Lemma reverse_nil : reverse [] = @nil A.
Proof. done. Qed.
Lemma reverse_singleton (x : A) : reverse [x] = [x].
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

Lemma take_nil n :
  take n (@nil A) = [].
Proof. by destruct n. Qed.
Lemma take_app (l k : list A) :
  take (length l) (l ++ k) = l.
Proof. induction l; simpl; f_equal; auto. Qed.
Lemma take_app_alt (l k : list A) n :
  n = length l →
  take n (l ++ k) = l.
Proof. intros Hn. by rewrite Hn, take_app. Qed.
Lemma take_app_le (l k : list A) n :
  n ≤ length l →
  take n (l ++ k) = take n l.
Proof.
  revert n;
  induction l; intros [|?] ?; simpl in *; f_equal; auto with lia.
Qed.
Lemma take_app_ge (l k : list A) n :
  length l ≤ n →
  take n (l ++ k) = l ++ take (n - length l) k.
Proof.
  revert n;
  induction l; intros [|?] ?; simpl in *; f_equal; auto with lia.
Qed.
Lemma take_ge (l : list A) n :
  length l ≤ n →
  take n l = l.
Proof.
  revert n.
  induction l; intros [|?] ?; simpl in *; f_equal; auto with lia.
Qed.

Lemma take_take (l : list A) n m :
  take n (take m l) = take (min n m) l.
Proof. revert n m. induction l; intros [|?] [|?]; simpl; f_equal; auto. Qed.
Lemma take_idempotent (l : list A) n :
  take n (take n l) = take n l.
Proof. by rewrite take_take, Min.min_idempotent. Qed.

Lemma take_length (l : list A) n :
  length (take n l) = min n (length l).
Proof. revert n. induction l; intros [|?]; simpl; f_equal; done. Qed.
Lemma take_length_alt (l : list A) n :
  n ≤ length l →
  length (take n l) = n.
Proof. rewrite take_length. apply Min.min_l. Qed.

Lemma lookup_take (l : list A) n i :
  i < n → take n l !! i = l !! i.
Proof.
  revert n i. induction l; intros [|n] i ?; trivial.
  * auto with lia.
  * destruct i; simpl; auto with arith.
Qed.
Lemma lookup_take_ge (l : list A) n i :
  n ≤ i → take n l !! i = None.
Proof.
  revert n i.
  induction l; intros [|?] [|?] ?; simpl; auto with lia.
Qed.
Lemma take_alter (f : A → A) l n i :
  n ≤ i → take n (alter f i l) = take n l.
Proof.
  intros. apply list_eq. intros j. destruct (le_lt_dec n j).
  * by rewrite !lookup_take_ge.
  * by rewrite !lookup_take, !list_lookup_alter_ne by lia.
Qed.
Lemma take_insert (l : list A) n i x :
  n ≤ i → take n (<[i:=x]>l) = take n l.
Proof take_alter _ _ _ _.

Lemma drop_nil n :
  drop n (@nil A) = [].
Proof. by destruct n. Qed.
Lemma drop_app (l k : list A) :
  drop (length l) (l ++ k) = k.
Proof. induction l; simpl; f_equal; auto. Qed.
Lemma drop_app_alt (l k : list A) n :
  n = length l →
  drop n (l ++ k) = k.
Proof. intros Hn. by rewrite Hn, drop_app. Qed.
Lemma drop_length (l : list A) n :
  length (drop n l) = length l - n.
Proof.
  revert n. by induction l; intros [|i]; simpl; f_equal.
Qed.
Lemma drop_all (l : list A) :
  drop (length l) l = [].
Proof. induction l; simpl; auto. Qed.
Lemma drop_all_alt (l : list A) n :
  n = length l →
  drop n l = [].
Proof. intros. subst. by rewrite drop_all. Qed.

Lemma lookup_drop (l : list A) n i :
  drop n l !! i = l !! (n + i).
Proof. revert n i. induction l; intros [|i] ?; simpl; auto. Qed.
Lemma drop_alter (f : A → A) l n i  :
  i < n → drop n (alter f i l) = drop n l.
Proof.
  intros. apply list_eq. intros j.
  by rewrite !lookup_drop, !list_lookup_alter_ne by lia.
Qed.
Lemma drop_insert (l : list A) n i x :
  i < n → drop n (<[i:=x]>l) = drop n l.
Proof drop_alter _ _ _ _.

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
Lemma replicate_plus n m (x : A) :
  replicate (n + m) x = replicate n x ++ replicate m x.
Proof. induction n; simpl; f_equal; auto. Qed.

Lemma take_replicate n m (x : A) :
  take n (replicate m x) = replicate (min n m) x.
Proof. revert m. by induction n; intros [|?]; simpl; f_equal. Qed.
Lemma take_replicate_plus n m (x : A) :
  take n (replicate (n + m) x) = replicate n x.
Proof. by rewrite take_replicate, min_l by lia. Qed.
Lemma drop_replicate n m (x : A) :
  drop n (replicate m x) = replicate (m - n) x.
Proof. revert m. by induction n; intros [|?]; simpl; f_equal. Qed.
Lemma drop_replicate_plus n m (x : A) :
  drop n (replicate (n + m) x) = replicate m x.
Proof. rewrite drop_replicate. f_equal. lia. Qed.

Lemma resize_spec (l : list A) n x :
  resize n x l = take n l ++ replicate (n - length l) x.
Proof.
  revert n.
  induction l; intros [|?]; simpl; f_equal; auto.
Qed.
Lemma resize_0 (l : list A) x :
  resize 0 x l = [].
Proof. by destruct l. Qed.
Lemma resize_nil n (x : A) :
  resize n x [] = replicate n x.
Proof. rewrite resize_spec. rewrite take_nil. simpl. f_equal. lia. Qed.
Lemma resize_ge (l : list A) n x :
  length l ≤ n →
  resize n x l = l ++ replicate (n - length l) x.
Proof. intros. by rewrite resize_spec, take_ge. Qed.
Lemma resize_le (l : list A) n x :
  n ≤ length l →
  resize n x l = take n l.
Proof.
  intros. rewrite resize_spec, (proj2 (NPeano.Nat.sub_0_le _ _)) by done.
  simpl. by rewrite (right_id [] (++)).
Qed.

Lemma resize_all (l : list A) x :
  resize (length l) x l = l.
Proof. intros. by rewrite resize_le, take_ge. Qed.
Lemma resize_all_alt (l : list A) n x :
  n = length l →
  resize n x l = l.
Proof. intros. subst. by rewrite resize_all. Qed.

Lemma resize_plus (l : list A) n m x :
  resize (n + m) x l = resize n x l ++ resize m x (drop n l).
Proof.
  revert n m.
  induction l; intros [|?] [|?]; simpl; f_equal; auto.
  * by rewrite plus_0_r, (right_id [] (++)).
  * by rewrite replicate_plus.
Qed.
Lemma resize_plus_eq (l : list A) n m x :
  length l = n →
  resize (n + m) x l = l ++ replicate m x.
Proof.
  intros. subst.
  by rewrite resize_plus, resize_all, drop_all, resize_nil.
Qed.

Lemma resize_app_le (l1 l2 : list A) n x :
  n ≤ length l1 →
  resize n x (l1 ++ l2) = resize n x l1.
Proof.
  intros.
  by rewrite !resize_le, take_app_le by (rewrite ?app_length; lia).
Qed.
Lemma resize_app_ge (l1 l2 : list A) n x :
  length l1 ≤ n →
  resize n x (l1 ++ l2) = l1 ++ resize (n - length l1) x l2.
Proof.
  intros.
  rewrite !resize_spec, take_app_ge, (associative (++)) by done.
  do 2 f_equal. rewrite app_length. lia.
Qed.

Lemma resize_length (l : list A) n x : length (resize n x l) = n.
Proof.
  rewrite resize_spec, app_length, replicate_length, take_length. lia.
Qed.
Lemma resize_replicate (x : A) n m :
  resize n x (replicate m x) = replicate n x.
Proof. revert m. induction n; intros [|?]; simpl; f_equal; auto. Qed.

Lemma resize_resize (l : list A) n m x :
  n ≤ m →
  resize n x (resize m x l) = resize n x l.
Proof.
  revert n m. induction l; simpl.
  * intros. by rewrite !resize_nil, resize_replicate.
  * intros [|?] [|?] ?; simpl; f_equal; auto with lia.
Qed.
Lemma resize_idempotent (l : list A) n x :
  resize n x (resize n x l) = resize n x l.
Proof. by rewrite resize_resize. Qed.

Lemma resize_take_le (l : list A) n m x :
  n ≤ m →
  resize n x (take m l) = resize n x l.
Proof.
  revert n m.
  induction l; intros [|?] [|?] ?; simpl; f_equal; auto with lia.
Qed.
Lemma resize_take_eq (l : list A) n x :
  resize n x (take n l) = resize n x l.
Proof. by rewrite resize_take_le. Qed.

Lemma take_resize (l : list A) n m x :
  take n (resize m x l) = resize (min n m) x l.
Proof.
  revert n m.
  induction l; intros [|?] [|?]; simpl; f_equal; auto using take_replicate.
Qed.
Lemma take_resize_le (l : list A) n m x :
  n ≤ m →
  take n (resize m x l) = resize n x l.
Proof. intros. by rewrite take_resize, Min.min_l. Qed.
Lemma take_resize_eq (l : list A) n x :
  take n (resize n x l) = resize n x l.
Proof. intros. by rewrite take_resize, Min.min_l. Qed.
Lemma take_length_resize (l : list A) n x :
  length l ≤ n →
  take (length l) (resize n x l) = l.
Proof. intros. by rewrite take_resize_le, resize_all. Qed.
Lemma take_length_resize_alt (l : list A) n m x :
  m = length l →
  m ≤ n →
  take m (resize n x l) = l.
Proof. intros. subst. by apply take_length_resize. Qed.
Lemma take_resize_plus (l : list A) n m x :
  take n (resize (n + m) x l) = resize n x l.
Proof. by rewrite take_resize, min_l by lia. Qed.

Lemma drop_resize_le (l : list A) n m x :
  n ≤ m →
  drop n (resize m x l) = resize (m - n) x (drop n l).
Proof.
  revert n m. induction l; simpl.
  * intros. by rewrite drop_nil, !resize_nil, drop_replicate.
  * intros [|?] [|?] ?; simpl; try case_match; auto with lia.
Qed.
Lemma drop_resize_plus (l : list A) n m x :
  drop n (resize (n + m) x l) = resize m x (drop n l).
Proof. rewrite drop_resize_le by lia. f_equal. lia. Qed.

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

  Lemma Forall_nil : Forall P [] ↔ True.
  Proof. done. Qed.
  Lemma Forall_cons_1 x l : Forall P (x :: l) → P x ∧ Forall P l.
  Proof. by inversion 1. Qed.
  Lemma Forall_cons x l : Forall P (x :: l) ↔ P x ∧ Forall P l.
  Proof. split. by inversion 1. intros [??]. by constructor. Qed.
  Lemma Forall_singleton x : Forall P [x] ↔ P x.
  Proof. rewrite Forall_cons, Forall_nil; tauto. Qed.
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
  Lemma Forall_lookup_1 l i x :
    Forall P l → l !! i = Some x → P x.
  Proof. rewrite Forall_lookup. eauto. Qed.
  Lemma Forall_alter f l i :
    Forall P l →
    (∀ x, l !! i = Some x → P x → P (f x)) →
    Forall P (alter f i l).
  Proof.
    intros Hl. revert i.
    induction Hl; simpl; intros [|i]; constructor; auto.
  Qed.

  Lemma Forall_replicate n x :
    P x → Forall P (replicate n x).
  Proof. induction n; simpl; constructor; auto. Qed.
  Lemma Forall_replicate_eq n (x : A) :
    Forall (=x) (replicate n x).
  Proof. induction n; simpl; constructor; auto. Qed.

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
End general_properties.

Section Forall2.
  Context {A B} (P : A → B → Prop).

  Lemma Forall2_nil_inv_l k :
    Forall2 P [] k → k = [].
  Proof. by inversion 1. Qed.
  Lemma Forall2_nil_inv_r k :
    Forall2 P k [] → k = [].
  Proof. by inversion 1. Qed.

  Lemma Forall2_cons_inv l1 l2 x1 x2 :
    Forall2 P (x1 :: l1) (x2 :: l2) → P x1 x2 ∧ Forall2 P l1 l2.
  Proof. by inversion 1. Qed.
  Lemma Forall2_cons_inv_l l1 k x1 :
    Forall2 P (x1 :: l1) k → ∃ x2 l2,
      P x1 x2 ∧ Forall2 P l1 l2 ∧ k = x2 :: l2.
  Proof. inversion 1; subst; eauto. Qed.
  Lemma Forall2_cons_inv_r k l2 x2 :
    Forall2 P k (x2 :: l2) → ∃ x1 l1,
      P x1 x2 ∧ Forall2 P l1 l2 ∧ k = x1 :: l1.
  Proof. inversion 1; subst; eauto. Qed.
  Lemma Forall2_cons_nil_inv l1 x1 :
    Forall2 P (x1 :: l1) [] → False.
  Proof. by inversion 1. Qed.
  Lemma Forall2_nil_cons_inv l2 x2 :
    Forall2 P [] (x2 :: l2) → False.
  Proof. by inversion 1. Qed.

  Lemma Forall2_flip l1 l2 :
    Forall2 P l1 l2 ↔ Forall2 (flip P) l2 l1.
  Proof. split; induction 1; constructor; auto. Qed.

  Lemma Forall2_length l1 l2 :
    Forall2 P l1 l2 → length l1 = length l2.
  Proof. induction 1; simpl; auto. Qed.

  Lemma Forall2_impl (Q : A → B → Prop) l1 l2 :
    Forall2 P l1 l2 → (∀ x y, P x y → Q x y) → Forall2 Q l1 l2.
  Proof. intros H ?. induction H; auto. Defined.

  Lemma Forall2_unique l k1 k2 :
    Forall2 P l k1 →
    Forall2 P l k2 →
    (∀ x y1 y2, P x y1 → P x y2 → y1 = y2) →
    k1 = k2.
  Proof.
    intros H. revert k2.
    induction H; inversion_clear 1; intros; f_equal; eauto.
  Qed.

  Lemma Forall2_Forall_l (Q : A → Prop) l k :
    Forall2 P l k →
    Forall (λ y, ∀ x, P x y → Q x) k →
    Forall Q l.
  Proof. induction 1; inversion_clear 1; eauto. Qed.
  Lemma Forall2_Forall_r (Q : B → Prop) l k :
    Forall2 P l k →
    Forall (λ x, ∀ y, P x y → Q y) l →
    Forall Q k.
  Proof. induction 1; inversion_clear 1; eauto. Qed.

  Lemma Forall2_lookup l1 l2 i x y :
    Forall2 P l1 l2 →
      l1 !! i = Some x → l2 !! i = Some y → P x y.
  Proof.
    intros H. revert i. induction H.
    * discriminate.
    * intros [|?] ??; simpl in *; simplify_equality; eauto.
  Qed.
  Lemma Forall2_lookup_l l1 l2 i x :
    Forall2 P l1 l2 → l1 !! i = Some x → ∃ y,
      l2 !! i = Some y ∧ P x y.
  Proof.
    intros H. revert i. induction H.
    * discriminate.
    * intros [|?] ?; simpl in *; simplify_equality; eauto.
  Qed.
  Lemma Forall2_lookup_r l1 l2 i y :
    Forall2 P l1 l2 → l2 !! i = Some y → ∃ x,
      l1 !! i = Some x ∧ P x y.
  Proof.
    intros H. revert i. induction H.
    * discriminate.
    * intros [|?] ?; simpl in *; simplify_equality; eauto.
  Qed.

  Lemma Forall2_alter_l f l1 l2 i :
    Forall2 P l1 l2 →
    (∀ x1 x2,
      l1 !! i = Some x1 → l2 !! i = Some x2 → P x1 x2 → P (f x1) x2) →
    Forall2 P (alter f i l1) l2.
  Proof.
    intros Hl. revert i.
    induction Hl; simpl; intros [|i]; constructor; auto.
  Qed.
  Lemma Forall2_alter_r f l1 l2 i :
    Forall2 P l1 l2 →
    (∀ x1 x2,
      l1 !! i = Some x1 → l2 !! i = Some x2 → P x1 x2 → P x1 (f x2)) →
    Forall2 P l1 (alter f i l2).
  Proof.
    intros Hl. revert i.
    induction Hl; simpl; intros [|i]; constructor; auto.
  Qed.
  Lemma Forall2_alter f g l1 l2 i :
    Forall2 P l1 l2 →
    (∀ x1 x2,
      l1 !! i = Some x1 → l2 !! i = Some x2 → P x1 x2 → P (f x1) (g x2)) →
    Forall2 P (alter f i l1) (alter g i l2).
  Proof.
    intros Hl. revert i.
    induction Hl; simpl; intros [|i]; constructor; auto.
  Qed.

  Lemma Forall2_replicate_l l n x :
    Forall (P x) l →
    length l = n →
    Forall2 P (replicate n x) l.
  Proof.
    intros Hl. revert n.
    induction Hl; intros [|?] ?; simplify_equality; constructor; auto.
  Qed.
  Lemma Forall2_replicate_r l n x :
    Forall (flip P x) l →
    length l = n →
    Forall2 P l (replicate n x).
  Proof.
    intros Hl. revert n.
    induction Hl; intros [|?] ?; simplify_equality; constructor; auto.
  Qed.
  Lemma Forall2_replicate n x1 x2 :
    P x1 x2 →
    Forall2 P (replicate n x1) (replicate n x2).
  Proof. induction n; simpl; constructor; auto. Qed.

  Lemma Forall2_take l1 l2 n :
    Forall2 P l1 l2 →
    Forall2 P (take n l1) (take n l2).
  Proof.
    intros Hl1l2. revert n.
    induction Hl1l2; intros [|?]; simpl; auto.
  Qed.
  Lemma Forall2_drop l1 l2 n :
    Forall2 P l1 l2 →
    Forall2 P (drop n l1) (drop n l2).
  Proof.
    intros Hl1l2. revert n.
    induction Hl1l2; intros [|?]; simpl; auto.
  Qed.
  Lemma Forall2_resize l1 l2 x1 x2 n :
    P x1 x2 →
    Forall2 P l1 l2 →
    Forall2 P (resize n x1 l1) (resize n x2 l2).
  Proof.
    intros. rewrite !resize_spec, (Forall2_length l1 l2) by done.
    auto using Forall2_app, Forall2_take, Forall2_replicate.
  Qed.

  Lemma Forall2_resize_ge_l l1 l2 x1 x2 n m :
    (∀ x, P x x2) →
    n ≤ m →
    Forall2 P (resize n x1 l1) l2 →
    Forall2 P (resize m x1 l1) (resize m x2 l2).
  Proof.
    intros. assert (n = length l2).
    { by rewrite <-(Forall2_length (resize n x1 l1) l2), resize_length. }
    rewrite (le_plus_minus n m) by done. subst.
    rewrite !resize_plus, resize_all, drop_all, resize_nil.
    apply Forall2_app; [done |].
    apply Forall2_replicate_r; [| by rewrite resize_length].
    by apply Forall_true.
  Qed.
  Lemma Forall2_resize_ge_r l1 l2 x1 x2 n m :
    (∀ x3, P x1 x3) →
    n ≤ m →
    Forall2 P l1 (resize n x2 l2) →
    Forall2 P (resize m x1 l1) (resize m x2 l2).
  Proof.
    intros. assert (n = length l1).
    { by rewrite (Forall2_length l1 (resize n x2 l2)), resize_length. }
    rewrite (le_plus_minus n m) by done. subst.
    rewrite !resize_plus, resize_all, drop_all, resize_nil.
    apply Forall2_app; [done |].
    apply Forall2_replicate_l; [| by rewrite resize_length].
    by apply Forall_true.
  Qed.

  Lemma Forall2_trans {C} (Q : B → C → Prop) (R : A → C → Prop) l1 l2 l3 :
    (∀ x1 x2 x3, P x1 x2 → Q x2 x3 → R x1 x3) →
    Forall2 P l1 l2 →
    Forall2 Q l2 l3 →
    Forall2 R l1 l3.
  Proof.
    intros ? Hl1l2. revert l3.
    induction Hl1l2; inversion_clear 1; eauto.
  Qed.

  Lemma Forall2_Forall (Q : A → A → Prop) l :
    Forall (λ x, Q x x) l → Forall2 Q l l.
  Proof. induction 1; constructor; auto. Qed.

  Global Instance Forall2_dec `{∀ x1 x2, Decision (P x1 x2)} :
    ∀ l1 l2, Decision (Forall2 P l1 l2).
  Proof.
   refine (
    fix go l1 l2 : Decision (Forall2 P l1 l2) :=
    match l1, l2 with
    | [], [] => left _
    | x1 :: l1, x2 :: l2 => cast_if_and (decide (P x1 x2)) (go l1 l2)
    | _, _ => right _
    end); clear go; abstract first [by constructor | by inversion 1].
  Defined.
End Forall2.

Section Forall2_order.
  Context  {A} (R : relation A).

  Global Instance: PreOrder R → PreOrder (Forall2 R).
  Proof.
    split.
    * intros l. induction l; by constructor.
    * intros ???. apply Forall2_trans. apply transitivity.
  Qed.
  Global Instance: AntiSymmetric R → AntiSymmetric (Forall2 R).
  Proof. induction 2; inversion_clear 1; f_equal; auto. Qed.
End Forall2_order.

Ltac decompose_elem_of_list := repeat
  match goal with
  | H : ?x ∈ [] |- _ => by destruct (not_elem_of_nil x)
  | H : _ ∈ _ :: _ |- _ => apply elem_of_cons in H; destruct H
  | H : _ ∈ _ ++ _ |- _ => apply elem_of_app in H; destruct H
  end.
Ltac decompose_Forall := repeat
  match goal with
  | H : Forall _ [] |- _ => clear H
  | H : Forall _ (_ :: _) |- _ => rewrite Forall_cons in H; destruct H
  | H : Forall _ (_ ++ _) |- _ => rewrite Forall_app in H; destruct H
  | H : Forall2 _ [] [] |- _ => clear H
  | H : Forall2 _ (_ :: _) [] |- _ => destruct (Forall2_cons_nil_inv _ _ _ H)
  | H : Forall2 _ [] (_ :: _) |- _ => destruct (Forall2_nil_cons_inv _ _ _ H)
  | H : Forall2 _ [] ?l |- _ => apply Forall2_nil_inv_l in H; subst l
  | H : Forall2 _ ?l [] |- _ => apply Forall2_nil_inv_r in H; subst l
  | H : Forall2 _ (_ :: _) (_ :: _) |- _ =>
     apply Forall2_cons_inv in H; destruct H
  | H : Forall2 _ (_ :: _) ?l |- _ =>
     apply Forall2_cons_inv_l in H; destruct H as (? & ? & ? & ? & ?); subst l
  | H : Forall2 _ ?l (_ :: _) |- _ =>
     apply Forall2_cons_inv_r in H; destruct H as (? & ? & ? & ? & ?); subst l
  end.

(** * Theorems on the prefix and suffix predicates *)
Section prefix_postfix.
  Context {A : Type}.

  Global Instance: PreOrder (@prefix_of A).
  Proof.
    split.
    * intros ?. eexists []. by rewrite (right_id [] (++)).
    * intros ??? [k1 ?] [k2 ?].
      exists (k1 ++ k2). subst. by rewrite (associative (++)).
  Qed.

  Lemma prefix_of_nil (l : list A) : prefix_of [] l.
  Proof. by exists l. Qed.
  Lemma prefix_of_nil_not x (l : list A) : ¬prefix_of (x :: l) [].
  Proof. by intros [k E]. Qed.
  Lemma prefix_of_cons x (l1 l2 : list A) :
    prefix_of l1 l2 → prefix_of (x :: l1) (x :: l2).
  Proof. intros [k E]. exists k. by subst. Qed.
  Lemma prefix_of_cons_alt x y (l1 l2 : list A) :
    x = y → prefix_of l1 l2 → prefix_of (x :: l1) (y :: l2).
  Proof. intro. subst. apply prefix_of_cons. Qed.
  Lemma prefix_of_cons_inv_1 x y (l1 l2 : list A) :
    prefix_of (x :: l1) (y :: l2) → x = y.
  Proof. intros [k E]. by injection E. Qed.
  Lemma prefix_of_cons_inv_2 x y (l1 l2 : list A) :
    prefix_of (x :: l1) (y :: l2) → prefix_of l1 l2.
  Proof. intros [k E]. exists k. by injection E. Qed.

  Lemma prefix_of_app k (l1 l2 : list A) :
    prefix_of l1 l2 → prefix_of (k ++ l1) (k ++ l2).
  Proof. intros [k' ?]. subst. exists k'. by rewrite (associative (++)). Qed.
  Lemma prefix_of_app_alt k1 k2 (l1 l2 : list A) :
    k1 = k2 → prefix_of l1 l2 → prefix_of (k1 ++ l1) (k2 ++ l2).
  Proof. intro. subst. apply prefix_of_app. Qed.
  Lemma prefix_of_app_l (l1 l2 l3 : list A) :
    prefix_of (l1 ++ l3) l2 → prefix_of l1 l2.
  Proof.
    intros [k ?]. red. exists (l3 ++ k). subst.
    by rewrite <-(associative (++)).
  Qed.
  Lemma prefix_of_app_r (l1 l2 l3 : list A) :
    prefix_of l1 l2 → prefix_of l1 (l2 ++ l3).
  Proof.
    intros [k ?]. exists (k ++ l3). subst.
    by rewrite (associative (++)).
  Qed.

  Lemma prefix_of_length (l1 l2 : list A) :
    prefix_of l1 l2 → length l1 ≤ length l2.
  Proof. intros [??]. subst. rewrite app_length. lia. Qed.
  Lemma prefix_of_snoc_not (l : list A) x : ¬prefix_of (l ++ [x]) l.
  Proof. intros [??]. discriminate_list_equality. Qed.

  Global Instance: PreOrder (@suffix_of A).
  Proof.
    split.
    * intros ?. by eexists [].
    * intros ??? [k1 ?] [k2 ?].
      exists (k2 ++ k1). subst. by rewrite (associative (++)).
  Qed.

  Global Instance prefix_of_dec `{∀ x y : A, Decision (x = y)} :
      ∀ l1 l2 : list A, Decision (prefix_of l1 l2) :=
    fix go l1 l2 :=
    match l1, l2 return { prefix_of l1 l2 } + { ¬prefix_of l1 l2 } with
    | [], _ => left (prefix_of_nil _)
    | _, [] => right (prefix_of_nil_not _ _)
    | x :: l1, y :: l2 =>
      match decide_rel (=) x y with
      | left Exy =>
        match go l1 l2 with
        | left Hl1l2 => left (prefix_of_cons_alt _ _ _ _ Exy Hl1l2)
        | right Hl1l2 => right (Hl1l2 ∘ prefix_of_cons_inv_2 _ _ _ _)
        end
      | right Exy => right (Exy ∘ prefix_of_cons_inv_1 _ _ _ _)
      end
    end.

  Section max_prefix_of.
    Context `{∀ x y : A, Decision (x = y)}.

    Lemma max_prefix_of_fst (l1 l2 : list A) :
      l1 = snd (max_prefix_of l1 l2) ++ fst (fst (max_prefix_of l1 l2)).
    Proof.
      revert l2. induction l1; intros [|??]; simpl;
        repeat case_decide; simpl; f_equal; auto.
    Qed.
    Lemma max_prefix_of_fst_alt (l1 l2 : list A) k1 k2 k3 :
      max_prefix_of l1 l2 = (k1,k2,k3) → l1 = k3 ++ k1.
    Proof.
      intro. pose proof (max_prefix_of_fst l1 l2).
      by destruct (max_prefix_of l1 l2) as [[]?]; simplify_equality.
    Qed.
    Lemma max_prefix_of_fst_prefix (l1 l2 : list A) :
      prefix_of (snd (max_prefix_of l1 l2)) l1.
    Proof. eexists. apply max_prefix_of_fst. Qed.
    Lemma max_prefix_of_fst_prefix_alt (l1 l2 : list A) k1 k2 k3 :
      max_prefix_of l1 l2 = (k1,k2,k3) → prefix_of k3 l1.
    Proof. eexists. eauto using max_prefix_of_fst_alt. Qed.

    Lemma max_prefix_of_snd (l1 l2 : list A) :
      l2 = snd (max_prefix_of l1 l2) ++ snd (fst (max_prefix_of l1 l2)).
    Proof.
      revert l2. induction l1; intros [|??]; simpl;
        repeat case_decide; simpl; f_equal; auto.
    Qed.
    Lemma max_prefix_of_snd_alt (l1 l2 : list A) k1 k2 k3 :
      max_prefix_of l1 l2 = (k1,k2,k3) → l2 = k3 ++ k2.
    Proof.
      intro. pose proof (max_prefix_of_snd l1 l2).
      by destruct (max_prefix_of l1 l2) as [[]?]; simplify_equality.
    Qed.
    Lemma max_prefix_of_snd_prefix (l1 l2 : list A) :
      prefix_of (snd (max_prefix_of l1 l2)) l2.
    Proof. eexists. apply max_prefix_of_snd. Qed.
    Lemma max_prefix_of_snd_prefix_alt (l1 l2 : list A) k1 k2 k3 :
      max_prefix_of l1 l2 = (k1,k2,k3) → prefix_of k3 l2.
    Proof. eexists. eauto using max_prefix_of_snd_alt. Qed.

    Lemma max_prefix_of_max (l1 l2 : list A) k :
      prefix_of k l1 →
      prefix_of k l2 →
      prefix_of k (snd (max_prefix_of l1 l2)).
    Proof.
      intros [l1' ?] [l2' ?]. subst.
      by induction k; simpl; repeat case_decide; simpl;
        auto using prefix_of_nil, prefix_of_cons.
    Qed.
    Lemma max_prefix_of_max_alt (l1 l2 : list A) k1 k2 k3 k :
      max_prefix_of l1 l2 = (k1,k2,k3) →
      prefix_of k l1 →
      prefix_of k l2 →
      prefix_of k k3.
    Proof.
      intro. pose proof (max_prefix_of_max l1 l2 k).
      by destruct (max_prefix_of l1 l2) as [[]?]; simplify_equality.
    Qed.

    Lemma max_prefix_of_max_snoc (l1 l2 : list A) k1 k2 k3 x1 x2 :
      max_prefix_of l1 l2 = (x1 :: k1, x2 :: k2, k3) →
      x1 ≠ x2.
    Proof.
      intros Hl ?. subst. destruct (prefix_of_snoc_not k3 x2).
      eapply max_prefix_of_max_alt; eauto.
      * rewrite (max_prefix_of_fst_alt _ _ _ _ _ Hl).
        apply prefix_of_app, prefix_of_cons, prefix_of_nil.
      * rewrite (max_prefix_of_snd_alt _ _ _ _ _ Hl).
        apply prefix_of_app, prefix_of_cons, prefix_of_nil.
    Qed.
  End max_prefix_of.

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
  Proof. exists l. by rewrite (right_id [] (++)). Qed.
  Lemma suffix_of_nil_inv (l : list A) : suffix_of l [] → l = [].
  Proof. by intros [[|?] ?]; simplify_list_equality. Qed.
  Lemma suffix_of_cons_nil_inv x (l : list A) : ¬suffix_of (x :: l) [].
  Proof. by intros [[] ?]. Qed.
  Lemma suffix_of_snoc (l1 l2 : list A) x :
    suffix_of l1 l2 → suffix_of (l1 ++ [x]) (l2 ++ [x]).
  Proof. intros [k E]. exists k. subst. by rewrite (associative (++)). Qed.
  Lemma suffix_of_snoc_alt x y (l1 l2 : list A) :
    x = y → suffix_of l1 l2 → suffix_of (l1 ++ [x]) (l2 ++ [y]).
  Proof. intro. subst. apply suffix_of_snoc. Qed.
 
  Lemma suffix_of_app (l1 l2 k : list A) :
    suffix_of l1 l2 → suffix_of (l1 ++ k) (l2 ++ k).
  Proof. intros [k' E]. exists k'. subst. by rewrite (associative (++)). Qed.
  Lemma suffix_of_app_alt (l1 l2 k1 k2 : list A) :
    k1 = k2 → suffix_of l1 l2 → suffix_of (l1 ++ k1) (l2 ++ k2).
  Proof. intro. subst. apply suffix_of_app. Qed.

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
  Proof.
    intros [k ?]. exists (k ++ [x]). subst.
    by rewrite <-(associative (++)).
  Qed.
  Lemma suffix_of_app_l (l1 l2 l3 : list A) :
    suffix_of (l3 ++ l1) l2 → suffix_of l1 l2.
  Proof.
    intros [k ?]. exists (k ++ l3). subst.
    by rewrite <-(associative (++)).
  Qed.
  Lemma suffix_of_cons_r (l1 l2 : list A) x :
    suffix_of l1 l2 → suffix_of l1 (x :: l2).
  Proof. intros [k ?]. exists (x :: k). by subst. Qed.
  Lemma suffix_of_app_r (l1 l2 l3 : list A) :
    suffix_of l1 l2 → suffix_of l1 (l3 ++ l2).
  Proof.
    intros [k ?]. exists (l3 ++ k). subst.
    by rewrite (associative (++)).
  Qed.

  Lemma suffix_of_cons_inv (l1 l2 : list A) x y :
    suffix_of (x :: l1) (y :: l2) →
      x :: l1 = y :: l2 ∨ suffix_of (x :: l1) l2.
  Proof.
    intros [[|? k] E].
    * by left.
    * right. simplify_equality. by apply suffix_of_app_r.
  Qed.

  Lemma suffix_of_length (l1 l2 : list A) :
    suffix_of l1 l2 → length l1 ≤ length l2.
  Proof. intros [??]. subst. rewrite app_length. lia. Qed.
  Lemma suffix_of_cons_not x (l : list A) : ¬suffix_of (x :: l) l.
  Proof. intros [??]. discriminate_list_equality. Qed.

  Global Instance suffix_of_dec `{∀ x y : A, Decision (x = y)}
    (l1 l2 : list A) : Decision (suffix_of l1 l2).
  Proof.
    refine (cast_if (decide_rel prefix_of (reverse l1) (reverse l2)));
     abstract (by rewrite suffix_prefix_reverse).
  Defined.

  Section max_suffix_of.
    Context `{∀ x y : A, Decision (x = y)}.

    Lemma max_suffix_of_fst (l1 l2 : list A) :
      l1 = fst (fst (max_suffix_of l1 l2)) ++ snd (max_suffix_of l1 l2).
    Proof.
      rewrite <-(reverse_involutive l1) at 1.
      rewrite (max_prefix_of_fst (reverse l1) (reverse l2)).
      unfold max_suffix_of.
      destruct (max_prefix_of (reverse l1) (reverse l2)) as ((?&?)&?); simpl.
      by rewrite reverse_app.
    Qed.
    Lemma max_suffix_of_fst_alt (l1 l2 : list A) k1 k2 k3 :
      max_suffix_of l1 l2 = (k1,k2,k3) → l1 = k1 ++ k3.
    Proof.
      intro. pose proof (max_suffix_of_fst l1 l2).
      by destruct (max_suffix_of l1 l2) as [[]?]; simplify_equality.
    Qed.
    Lemma max_suffix_of_fst_suffix (l1 l2 : list A) :
      suffix_of (snd (max_suffix_of l1 l2)) l1.
    Proof. eexists. apply max_suffix_of_fst. Qed.
    Lemma max_suffix_of_fst_suffix_alt (l1 l2 : list A) k1 k2 k3 :
      max_suffix_of l1 l2 = (k1,k2,k3) → suffix_of k3 l1.
    Proof. eexists. eauto using max_suffix_of_fst_alt. Qed.

    Lemma max_suffix_of_snd (l1 l2 : list A) :
      l2 = snd (fst (max_suffix_of l1 l2)) ++ snd (max_suffix_of l1 l2).
    Proof.
      rewrite <-(reverse_involutive l2) at 1.
      rewrite (max_prefix_of_snd (reverse l1) (reverse l2)).
      unfold max_suffix_of.
      destruct (max_prefix_of (reverse l1) (reverse l2)) as ((?&?)&?); simpl.
      by rewrite reverse_app.
    Qed.
    Lemma max_suffix_of_snd_alt (l1 l2 : list A) k1 k2 k3 :
      max_suffix_of l1 l2 = (k1,k2,k3) → l2 = k2 ++ k3.
    Proof.
      intro. pose proof (max_suffix_of_snd l1 l2).
      by destruct (max_suffix_of l1 l2) as [[]?]; simplify_equality.
    Qed.
    Lemma max_suffix_of_snd_suffix (l1 l2 : list A) :
      suffix_of (snd (max_suffix_of l1 l2)) l2.
    Proof. eexists. apply max_suffix_of_snd. Qed.
    Lemma max_suffix_of_snd_suffix_alt (l1 l2 : list A) k1 k2 k3 :
      max_suffix_of l1 l2 = (k1,k2,k3) → suffix_of k3 l2.
    Proof. eexists. eauto using max_suffix_of_snd_alt. Qed.

    Lemma max_suffix_of_max (l1 l2 : list A) k :
      suffix_of k l1 →
      suffix_of k l2 →
      suffix_of k (snd (max_suffix_of l1 l2)).
    Proof.
      generalize (max_prefix_of_max (reverse l1) (reverse l2)).
      rewrite !suffix_prefix_reverse. unfold max_suffix_of.
      destruct (max_prefix_of (reverse l1) (reverse l2)) as ((?&?)&?); simpl.
      rewrite reverse_involutive. auto.
    Qed.
    Lemma max_suffix_of_max_alt (l1 l2 : list A) k1 k2 k3 k :
      max_suffix_of l1 l2 = (k1,k2,k3) →
      suffix_of k l1 →
      suffix_of k l2 →
      suffix_of k k3.
    Proof.
      intro. pose proof (max_suffix_of_max l1 l2 k).
      by destruct (max_suffix_of l1 l2) as [[]?]; simplify_equality.
    Qed.

    Lemma max_suffix_of_max_snoc (l1 l2 : list A) k1 k2 k3 x1 x2 :
      max_suffix_of l1 l2 = (k1 ++ [x1], k2 ++ [x2], k3) →
      x1 ≠ x2.
    Proof.
      intros Hl ?. subst. destruct (suffix_of_cons_not x2 k3).
      eapply max_suffix_of_max_alt; eauto.
      * rewrite (max_suffix_of_fst_alt _ _ _ _ _ Hl).
        by apply (suffix_of_app [x2]), suffix_of_app_r.
      * rewrite (max_suffix_of_snd_alt _ _ _ _ _ Hl).
        by apply (suffix_of_app [x2]), suffix_of_app_r.
    Qed.
  End max_suffix_of.
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
Instance list_join: MJoin list :=
  fix go A (ls : list (list A)) : list A :=
  match ls with
  | [] => []
  | l :: ls => l ++ @mjoin _ go _ ls
  end.

Definition mapM `{!MBind M} `{!MRet M} {A B}
    (f : A → M B) : list A → M (list B) :=
  fix go l :=
  match l with
  | [] => mret []
  | x :: l => y ← f x; k ← go l; mret (y :: k)
  end.

Section list_fmap.
  Context {A B : Type} (f : A → B).

  Lemma list_fmap_compose {C} (g : B → C) l :
    g ∘ f <$> l = g <$> f <$> l.
  Proof. induction l; simpl; f_equal; auto. Qed.

  Lemma list_fmap_ext (g : A → B) (l : list A) :
    (∀ x, f x = g x) → fmap f l = fmap g l.
  Proof. intro. induction l; simpl; f_equal; auto. Qed.
  Lemma list_fmap_ext_alt (g : A → B) (l : list A) :
    Forall (λ x, f x = g x) l ↔ fmap f l = fmap g l.
  Proof.
    split.
    * induction 1; simpl; f_equal; auto.
    * induction l; simpl; constructor; simplify_equality; auto.
  Qed.

  Global Instance: Injective (=) (=) f → Injective (=) (=) (fmap f).
  Proof.
    intros ? l1. induction l1 as [|x l1 IH].
    * by intros [|??].
    * intros [|??]; simpl; intros; f_equal; simplify_equality; auto.
  Qed.
  Lemma fmap_app l1 l2 : f <$> l1 ++ l2 = (f <$> l1) ++ (f <$> l2).
  Proof. induction l1; simpl; by f_equal. Qed.

  Lemma fmap_nil_inv k :
    f <$> k = [] → k = [].
  Proof. by destruct k. Qed.
  Lemma fmap_cons_inv y l k :
    f <$> l = y :: k → ∃ x l',
      y = f x ∧ k = f <$> l' ∧ l = x :: l'.
  Proof. intros. destruct l; simpl; simplify_equality; eauto. Qed.
  Lemma fmap_app_inv l k1 k2 :
    f <$> l = k1 ++ k2 → ∃ l1 l2,
      k1 = f <$> l1 ∧ k2 = f <$> l2 ∧ l = l1 ++ l2.
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
  Lemma fmap_replicate n x :
    f <$> replicate n x = replicate n (f x).
  Proof. induction n; simpl; f_equal; auto. Qed.

  Lemma list_lookup_fmap l i : (f <$> l) !! i = f <$> (l !! i).
  Proof. revert i. induction l; by intros [|]. Qed.
  Lemma list_lookup_fmap_inv l i x :
    (f <$> l) !! i = Some x → ∃ y, x = f y ∧ l !! i = Some y.
  Proof.
    intros Hi. rewrite list_lookup_fmap in Hi.
    destruct (l !! i) eqn:?; simplify_equality; eauto.
  Qed.
   
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
  Proof.
    firstorder eauto using elem_of_list_fmap_1_alt, elem_of_list_fmap_2.
  Qed.

  Lemma NoDup_fmap_1 (l : list A) :
    NoDup (f <$> l) → NoDup l.
  Proof.
    induction l; simpl; inversion_clear 1; constructor; auto.
    rewrite elem_of_list_fmap in *. naive_solver.
  Qed.
  Lemma NoDup_fmap_2 `{!Injective (=) (=) f} (l : list A) :
    NoDup l → NoDup (f <$> l).
  Proof.
    induction 1; simpl; constructor; trivial.
    rewrite elem_of_list_fmap. intros [y [Hxy ?]].
    apply (injective f) in Hxy. by subst.
  Qed.
  Lemma NoDup_fmap `{!Injective (=) (=) f} (l : list A) :
    NoDup (f <$> l) ↔ NoDup l.
  Proof. split; auto using NoDup_fmap_1, NoDup_fmap_2. Qed.

  Global Instance fmap_Permutation_proper:
    Proper (Permutation ==> Permutation) (fmap f).
  Proof. induction 1; simpl; econstructor; eauto. Qed.

  Lemma Forall_fmap (l : list A) (P : B → Prop) :
    Forall P (f <$> l) ↔ Forall (P ∘ f) l.
  Proof.
    split; induction l; inversion_clear 1; constructor; auto.
  Qed.

  Lemma Forall2_fmap_l {C} (P : B → C → Prop) l1 l2 :
    Forall2 P (f <$> l1) l2 ↔ Forall2 (P ∘ f) l1 l2.
  Proof.
    split; revert l2; induction l1; inversion_clear 1; constructor; auto.
  Qed.
  Lemma Forall2_fmap_r {C} (P : C → B → Prop) l1 l2 :
    Forall2 P l1 (f <$> l2) ↔ Forall2 (λ x, P x ∘ f) l1 l2.
  Proof.
    split; revert l1; induction l2; inversion_clear 1; constructor; auto.
  Qed.
  Lemma Forall2_fmap_1 {C D} (g : C → D) (P : B → D → Prop) l1 l2 :
    Forall2 P (f <$> l1) (g <$> l2) →
    Forall2 (λ x1 x2, P (f x1) (g x2)) l1 l2.
  Proof. revert l2; induction l1; intros [|??]; inversion_clear 1; auto. Qed.
  Lemma Forall2_fmap_2 {C D} (g : C → D) (P : B → D → Prop) l1 l2 :
    Forall2 (λ x1 x2, P (f x1) (g x2)) l1 l2 →
    Forall2 P (f <$> l1) (g <$> l2).
  Proof. induction 1; simpl; auto. Qed.
  Lemma Forall2_fmap {C D} (g : C → D) (P : B → D → Prop) l1 l2 :
    Forall2 P (f <$> l1) (g <$> l2) ↔
    Forall2 (λ x1 x2, P (f x1) (g x2)) l1 l2.
  Proof. split; auto using Forall2_fmap_1, Forall2_fmap_2. Qed.

  Lemma mapM_fmap_Some (g : B → option A) (l : list A) :
    (∀ x, g (f x) = Some x) →
    mapM g (f <$> l) = Some l.
  Proof. intros. by induction l; simpl; simplify_option_equality. Qed.
  Lemma mapM_fmap_Some_inv (g : B → option A) (l : list A) (k : list B) :
    (∀ x y, g y = Some x → y = f x) →
    mapM g k = Some l →
    k = f <$> l.
  Proof.
    intros Hgf. revert l; induction k as [|y k]; intros [|x l] ?;
      simplify_option_equality; f_equiv; eauto.
  Qed.

  Lemma mapM_Some (g : B → option A) l k :
    Forall2 (λ x y, g x = Some y) l k →
    mapM g l = Some k.
  Proof. by induction 1; simplify_option_equality. Qed.

  Lemma Forall2_impl_mapM (P : B → A → Prop) (g : B → option A) l k :
    Forall (λ x, ∀ y, g x = Some y → P x y) l →
    mapM g l = Some k →
    Forall2 P l k.
  Proof.
    intros Hl. revert k. induction Hl; intros [|??] ?;
      simplify_option_equality; eauto.
  Qed.
End list_fmap.

Lemma NoDup_fmap_fst {A B} (l : list (A * B)) :
  (∀ x y1 y2, (x,y1) ∈ l → (x,y2) ∈ l → y1 = y2) →
  NoDup l →
  NoDup (fst <$> l).
Proof.
  intros Hunique.
  induction 1 as [|[x1 y1] l Hin Hnodup IH]; simpl; constructor.
  * rewrite elem_of_list_fmap.
    intros [[x2 y2] [??]]; simpl in *; subst. destruct Hin.
    rewrite (Hunique x2 y1 y2); rewrite ?elem_of_cons; auto.
  * apply IH. intros.
    eapply Hunique; rewrite ?elem_of_cons; eauto.
Qed.

Section list_bind.
  Context {A B : Type} (f : A → list B).

  Lemma bind_app (l1 l2 : list A) :
    (l1 ++ l2) ≫= f = (l1 ≫= f) ++ (l2 ≫= f).
  Proof.
    induction l1; simpl; [done|].
    by rewrite <-(associative (++)), IHl1.
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

  Lemma Forall2_bind {C D} (g : C → list D) (P : B → D → Prop) l1 l2 :
    Forall2 (λ x1 x2, Forall2 P (f x1) (g x2)) l1 l2 →
    Forall2 P (l1 ≫= f) (l2 ≫= g).
  Proof. induction 1; simpl; auto using Forall2_app. Qed.
End list_bind.

Section list_ret_join.
  Context {A : Type}.

  Lemma list_join_bind (ls : list (list A)) :
    mjoin ls = ls ≫= id.
  Proof. induction ls; simpl; f_equal; auto. Qed.

  Lemma elem_of_list_ret (x y : A) :
    x ∈ @mret list _ A y ↔ x = y.
  Proof. apply elem_of_list_singleton. Qed.
  Lemma elem_of_list_join (x : A) (ls : list (list A)) :
    x ∈ mjoin ls ↔ ∃ l, x ∈ l ∧ l ∈ ls.
  Proof. by rewrite list_join_bind, elem_of_list_bind. Qed.

  Lemma join_nil (ls : list (list A)) :
    mjoin ls = [] ↔ Forall (= []) ls.
  Proof.
    split.
    * by induction ls as [|[|??] ?]; constructor; auto.
    * by induction 1 as [|[|??] ?].
  Qed.
  Lemma join_nil_1 (ls : list (list A)) :
    mjoin ls = [] → Forall (= []) ls.
  Proof. by rewrite join_nil. Qed.
  Lemma join_nil_2 (ls : list (list A)) :
    Forall (= []) ls → mjoin ls = [].
  Proof. by rewrite join_nil. Qed.

  Lemma join_length (ls : list (list A)) :
    length (mjoin ls) = foldr (plus ∘ length) 0 ls.
  Proof. by induction ls; simpl; rewrite ?app_length; f_equal. Qed.
  Lemma join_length_same (ls : list (list A)) n :
    Forall (λ l, length l = n) ls →
    length (mjoin ls) = length ls * n.
  Proof. rewrite join_length. by induction 1; simpl; f_equal. Qed.

  Lemma lookup_join_same_length (ls : list (list A)) n i :
    n ≠ 0 →
    Forall (λ l, length l = n) ls →
    mjoin ls !! i = ls !! (i `div` n) ≫= (!! (i `mod` n)).
  Proof.
    intros Hn Hls. revert i.
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
    intros Hn Hls. revert i.
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

  Lemma Forall2_join {B} (P : A → B → Prop) ls1 ls2 :
    Forall2 (Forall2 P) ls1 ls2 →
    Forall2 P (mjoin ls1) (mjoin ls2).
  Proof. induction 1; simpl; auto using Forall2_app. Qed.
End list_ret_join.

Ltac simplify_list_fmap_equality := repeat
  match goal with
  | _ => progress simplify_equality
  | H : _ <$> _ = [] |- _ => apply fmap_nil_inv in H
  | H : [] = _ <$> _ |- _ => symmetry in H; apply fmap_nil_inv in H
  | H : _ <$> _ = _ :: _ |- _ =>
    apply fmap_cons_inv in H; destruct H as (?&?&?&?&?)
  | H : _ :: _ = _ <$> _ |- _ => symmetry in H
  | H : _ <$> _ = _ ++ _ |- _ =>
    apply fmap_app_inv in H; destruct H as (?&?&?&?&?)
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

  Lemma same_length_length_1 l k :
    same_length l k → length l = length k.
  Proof. induction 1; simpl; auto. Qed.
  Lemma same_length_length_2 l k :
    length l = length k → same_length l k.
  Proof.
    revert k. induction l; intros [|??]; try discriminate;
      constructor; auto with arith.
  Qed.
  Lemma same_length_length l k :
    same_length l k ↔ length l = length k.
  Proof. split; auto using same_length_length_1, same_length_length_2. Qed.

  Lemma same_length_lookup l k i :
    same_length l k → is_Some (l !! i) → is_Some (k !! i).
  Proof.
    rewrite same_length_length.
    setoid_rewrite lookup_lt_length.
    intros E. by rewrite E.
  Qed.

  Lemma Forall2_same_length (P : A → B → Prop) l1 l2 :
    Forall2 P l1 l2 →
    same_length l1 l2.
  Proof. intro. eapply same_length_length, Forall2_length; eauto. Qed.
  Lemma Forall2_app_inv (P : A → B → Prop) l1 l2 k1 k2 :
    same_length l1 k1 →
    Forall2 P (l1 ++ l2) (k1 ++ k2) → Forall2 P l2 k2.
  Proof. induction 1. done. inversion 1; subst; auto. Qed.

  Lemma same_length_Forall2 l1 l2 :
    same_length l1 l2 ↔ Forall2 (λ _ _, True) l1 l2.
  Proof. split; induction 1; constructor; auto. Qed.

  Lemma same_length_take l1 l2 n :
    same_length l1 l2 →
    same_length (take n l1) (take n l2).
  Proof. rewrite !same_length_Forall2. apply Forall2_take. Qed.
  Lemma same_length_drop l1 l2 n :
    same_length l1 l2 →
    same_length (drop n l1) (drop n l2).
  Proof. rewrite !same_length_Forall2. apply Forall2_drop. Qed.
  Lemma same_length_resize l1 l2 x1 x2 n :
    same_length (resize n x1 l1) (resize n x2 l2).
  Proof. apply same_length_length. by rewrite !resize_length. Qed.
End same_length.

Instance: ∀ A, Reflexive (@same_length A A).
Proof. intros A l. induction l; constructor; auto. Qed.

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

  Lemma Forall_zip_with_fst (P : A → Prop) (Q : C → Prop) l1 l2 :
    Forall P l1 →
    Forall (λ y, ∀ x, P x → Q (f x y)) l2 →
    Forall Q (zip_with f l1 l2).
  Proof.
    intros Hl1. revert l2.
    induction Hl1; destruct 1; simpl in *; auto.
  Qed.
  Lemma Forall_zip_with_snd (P : B → Prop) (Q : C → Prop) l1 l2 :
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
      by rewrite reverse_cons, <-(associative (++)).
  * intros [k' [k'' [y [??]]]]; subst.
    revert l. induction k' as [|z k' IH]; intros l.
    + by left.
    + right. by rewrite reverse_cons, <-!(associative (++)).
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
  inversion_clear 1. rewrite reverse_cons, <-(associative (++)).
  by apply IH.
Qed.

(** * Permutations *)
Fixpoint interleave {A} (x : A) (l : list A) : list (list A) :=
  match l with
  | [] => [ [x] ]
  | y :: l => (x :: y :: l) :: ((y ::) <$> interleave x l)
  end.
Fixpoint permutations {A} (l : list A) : list (list A) :=
  match l with
  | [] => [ [] ]
  | x :: l => permutations l ≫= interleave x
  end.

Section permutations.
  Context {A : Type}.

  Lemma interleave_cons (x : A) (l : list A) :
    x :: l ∈ interleave x l.
  Proof. destruct l; simpl; rewrite elem_of_cons; auto. Qed.
  Lemma interleave_Permutation (x : A) (l l' : list A) :
    l' ∈ interleave x l → Permutation l' (x :: l).
  Proof.
    revert l'. induction l as [|y l IH]; intros l'; simpl.
    * rewrite elem_of_list_singleton. intros. by subst.
    * rewrite elem_of_cons, elem_of_list_fmap.
      intros [?|[? [? H]]]; subst.
      + by constructor.
      + rewrite (IH _ H). constructor.
  Qed.

  Lemma permutations_refl (l : list A) :
    l ∈ permutations l.
  Proof.
    induction l; simpl.
    * by apply elem_of_list_singleton.
    * apply elem_of_list_bind. eauto using interleave_cons.
  Qed.
  Lemma permutations_skip (x : A) (l l' : list A) : 
    l ∈ permutations l' →
    x :: l ∈ permutations (x :: l').
  Proof.
    intros Hl. simpl. apply elem_of_list_bind.
    eauto using interleave_cons.
  Qed.
  Lemma permutations_swap (x y : A) (l : list A) : 
    y :: x :: l ∈ permutations (x :: y :: l).
  Proof.
    simpl. apply elem_of_list_bind.
    exists (y :: l). split; simpl.
    * destruct l; simpl; rewrite !elem_of_cons; auto.
    * apply elem_of_list_bind. simpl.
      eauto using interleave_cons, permutations_refl.
  Qed.
  Lemma permutations_nil (l : list A) :
    l ∈ permutations [] ↔ l = [].
  Proof. simpl. by rewrite elem_of_list_singleton. Qed.

  Lemma interleave_interleave_toggle (x1 x2 : A) (l1 l2 l3 : list A) :
    l1 ∈ interleave x1 l2 →
    l2 ∈ interleave x2 l3 → ∃ l4,
      l1 ∈ interleave x2 l4 ∧ l4 ∈ interleave x1 l3.
  Proof.
    revert l1 l2. induction l3 as [|y l3 IH]; intros l1 l2; simpl.
    { intros Hl1 Hl2.
      rewrite elem_of_list_singleton in Hl2. subst. simpl in Hl1.
      rewrite elem_of_cons, elem_of_list_singleton in Hl1.
      exists [x1]. simpl.
      rewrite elem_of_cons, !elem_of_list_singleton. tauto. }
    rewrite elem_of_cons, elem_of_list_fmap.
    intros Hl1 [? | [l2' [??]]]; subst; simpl in *.
    * rewrite !elem_of_cons, elem_of_list_fmap in Hl1.
      destruct Hl1 as [? | [? | [l4 [??]]]]; subst.
      + exists (x1 :: y :: l3). simpl. rewrite !elem_of_cons. tauto.
      + exists (x1 :: y :: l3). simpl. rewrite !elem_of_cons. tauto.
      + exists l4. simpl. rewrite elem_of_cons. auto using interleave_cons.
    * rewrite elem_of_cons, elem_of_list_fmap in Hl1.
      destruct Hl1 as [? | [l1' [??]]]; subst.
      + exists (x1 :: y :: l3). simpl.
        rewrite !elem_of_cons, !elem_of_list_fmap.
        split; [| by auto]. right. right. exists (y :: l2').
        rewrite elem_of_list_fmap. naive_solver.
      + destruct (IH l1' l2') as [l4 [??]]; auto.
        exists (y :: l4). simpl.
        rewrite !elem_of_cons, !elem_of_list_fmap. naive_solver.
  Qed.
  Lemma permutations_interleave_toggle (x : A) (l1 l2 l3 : list A) :
    l1 ∈ permutations l2 →
    l2 ∈ interleave x l3 → ∃ l4,
      l1 ∈ interleave x l4 ∧ l4 ∈ permutations l3.
  Proof.
    revert l1 l2. induction l3 as [|y l3 IH]; intros l1 l2; simpl.
    { intros Hl1 Hl2. eexists []. simpl.
      split; [| by rewrite elem_of_list_singleton].
      rewrite elem_of_list_singleton in Hl2.
      by rewrite Hl2 in Hl1. }
    rewrite elem_of_cons, elem_of_list_fmap.
    intros Hl1 [? | [l2' [? Hl2']]]; subst; simpl in *.
    * rewrite elem_of_list_bind in Hl1.
      destruct Hl1 as [l1' [??]]. by exists l1'.
    * rewrite elem_of_list_bind in Hl1.
      setoid_rewrite elem_of_list_bind.
      destruct Hl1 as [l1' [??]].
      destruct (IH l1' l2') as [l1'' [??]]; auto.
      destruct (interleave_interleave_toggle y x l1 l1' l1'') as [? [??]]; eauto.
  Qed.
  Lemma permutations_trans (l1 l2 l3 : list A) :
    l1 ∈ permutations l2 →
    l2 ∈ permutations l3 →
    l1 ∈ permutations l3.
  Proof.
    revert l1 l2. induction l3 as [|x l3 IH]; intros l1 l2; simpl.
    * intros Hl1 Hl2. rewrite elem_of_list_singleton in Hl2.
      by rewrite Hl2 in Hl1.
    * rewrite !elem_of_list_bind. intros Hl1 [l2' [Hl2 Hl2']].
      destruct (permutations_interleave_toggle x l1 l2 l2') as [? [??]]; eauto.
  Qed.

  Lemma permutations_Permutation (l l' : list A) :
    l' ∈ permutations l ↔ Permutation l l'.
  Proof.
    split.
    * revert l'. induction l; simpl; intros l''.
      + rewrite elem_of_list_singleton.
        intros. subst. constructor.
      + rewrite elem_of_list_bind. intros [l' [Hl'' ?]].
        rewrite (interleave_Permutation _ _ _ Hl'').
        constructor; auto.
    * induction 1; eauto using permutations_refl,
        permutations_skip, permutations_swap, permutations_trans.
  Qed.

  Global Instance Permutation_dec `{∀ x y : A, Decision (x = y)}
    (l1 l2 : list A) : Decision (Permutation l1 l2).
  Proof.
    refine (cast_if (decide (l2 ∈ permutations l1)));
      by rewrite <-permutations_Permutation.
  Defined.
End permutations.

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

  Definition list_intersection_with (f : A → A → option A) :
      list A → list A → list A :=
    fix go l k :=
    match l with
    | [] => []
    | x :: l => foldr (λ y,
       match f x y with None => id | Some z => (z ::) end) (go l k) k
    end.
  Lemma elem_of_list_intersection_with f l k x :
    x ∈ list_intersection_with f l k ↔ ∃ x1 x2,
      x1 ∈ l ∧ x2 ∈ k ∧ f x1 x2 = Some x.
  Proof.
    split.
    * induction l as [|x1 l IH]; simpl.
      + by rewrite elem_of_nil.
      + intros Hx. setoid_rewrite elem_of_cons.
        cut ((∃ x2, x2 ∈ k ∧ f x1 x2 = Some x)
          ∨ x ∈ list_intersection_with f l k).
        { naive_solver. }
        clear IH. revert Hx. generalize (list_intersection_with f l k).
        induction k; simpl; [by auto|].
        case_match; setoid_rewrite elem_of_cons; naive_solver.
    * intros (x1 & x2 & Hx1 & Hx2 & Hx).
      induction Hx1 as [x1 | x1 ? l ? IH]; simpl.
      + generalize (list_intersection_with f l k).
        induction Hx2; simpl; [by rewrite Hx; left |].
        case_match; simpl; try setoid_rewrite elem_of_cons; auto.
      + generalize (IH Hx). clear Hx IH Hx2.
        generalize (list_intersection_with f l k).
        induction k; simpl; intros; [done |].
        case_match; simpl; rewrite ?elem_of_cons; auto.
  Qed.
End list_set_operations.
