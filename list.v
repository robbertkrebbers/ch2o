(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects general purpose definitions and theorems on lists that
are not in the Coq standard library. *)
Require Export Permutation.
Require Export numbers base decidable option.

Arguments length {_} _.
Arguments cons {_} _ _.
Arguments app {_} _ _.
Arguments Permutation {_} _ _.
Arguments Forall_cons {_} _ _ _ _ _.

Notation tail := tl.
Notation take := firstn.
Notation drop := skipn.

Arguments take {_} !_ !_ /.
Arguments drop {_} !_ !_ /.

Notation "(::)" := cons (only parsing) : C_scope.
Notation "( x ::)" := (cons x) (only parsing) : C_scope.
Notation "(:: l )" := (λ x, cons x l) (only parsing) : C_scope.
Notation "(++)" := app (only parsing) : C_scope.
Notation "( l ++)" := (app l) (only parsing) : C_scope.
Notation "(++ k )" := (λ l, app l k) (only parsing) : C_scope.

Infix "≡ₚ" := Permutation (at level 70, no associativity) : C_scope.
Notation "(≡ₚ)" := Permutation (only parsing) : C_scope.
Notation "( x ≡ₚ)" := (Permutation x) (only parsing) : C_scope.
Notation "(≡ₚ x )" := (λ y, y ≡ₚ x) (only parsing) : C_scope.
Notation "(≢ₚ)" := (λ x y, ¬x ≡ₚ y) (only parsing) : C_scope.
Notation "x ≢ₚ y":= (¬x ≡ₚ y) (at level 70, no associativity) : C_scope.
Notation "( x ≢ₚ)" := (λ y, x ≢ₚ y) (only parsing) : C_scope.
Notation "(≢ₚ x )" := (λ y, y ≢ₚ x) (only parsing) : C_scope.

(** * Definitions *)
(** The operation [l !! i] gives the [i]th element of the list [l], or [None]
in case [i] is out of bounds. *)
Instance list_lookup {A} : Lookup nat A (list A) :=
  fix go (i : nat) (l : list A) {struct l} : option A :=
  match l with
  | [] => None
  | x :: l => match i with 0 => Some x | S i => @lookup _ _ _ go i l end
  end.

(** The operation [alter f i l] applies the function [f] to the [i]th element
of [l]. In case [i] is out of bounds, the list is returned unchanged. *)
Instance list_alter {A} (f : A → A) : AlterD nat A (list A) f :=
  fix go (i : nat) (l : list A) {struct l} :=
  match l with
  | [] => []
  | x :: l => match i with 0 => f x :: l | S i => x :: @alter _ _ _ f go i l end
  end.

(** The operation [delete i l] removes the [i]th element of [l] and moves
all consecutive elements one position ahead. In case [i] is out of bounds,
the list is returned unchanged. *)
Instance list_delete {A} : Delete nat (list A) :=
  fix go (i : nat) (l : list A) {struct l} : list A :=
  match l with
  | [] => []
  | x :: l => match i with 0 => l | S i => x :: @delete _ _ go i l end
  end.

(** The operation [<[i:=x]> l] overwrites the element at position [i] with the
value [x]. In case [i] is out of bounds, the list is returned unchanged. *)
Instance list_insert {A} : Insert nat A (list A) := λ i x, alter (λ _, x) i.

(** The function [option_list o] converts an element [Some x] into the
singleton list [[x]], and [None] into the empty list [[]]. *)
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
  match n with 0 => [] | S n => x :: replicate n x end.

(** The function [reverse l] returns the elements of [l] in reverse order. *)
Definition reverse {A} (l : list A) : list A := rev_append l [].

Fixpoint last' {A} (x : A) (l : list A) : A :=
  match l with [] => x | x :: l => last' x l end.
Definition last {A} (l : list A) : option A :=
  match l with [] => None | x :: l => Some (last' x l) end.

(** The function [resize n y l] takes the first [n] elements of [l] in case
[length l ≤ n], and otherwise appends elements with value [x] to [l] to obtain
a list of length [n]. *)
Fixpoint resize {A} (n : nat) (y : A) (l : list A) : list A :=
  match l with
  | [] => replicate n y
  | x :: l => match n with 0 => [] | S n => x :: resize n y l end
  end.
Arguments resize {_} !_ _ !_.

(** Functions to fold over a list. We redefine [foldl] with the arguments in
the same order as in Haskell. *)
Notation foldr := fold_right.

Definition foldl {A B} (f : A → B → A) : A → list B → A :=
  fix go a l :=
  match l with
  | [] => a
  | x :: l => go (f a x) l
  end.

(** The monadic operations. *)
Instance list_ret: MRet list := λ A x, x :: @nil A.
Instance list_fmap {A B} (f : A → B) : FMapD list f :=
  fix go (l : list A) :=
  match l with [] => [] | x :: l => f x :: @fmap _ _ _ f go l end.
Instance list_bind {A B} (f : A → list B) : MBindD list f :=
  fix go (l : list A) :=
  match l with [] => [] | x :: l => f x ++ @mbind _ _ _ f go l end.
Instance list_join: MJoin list :=
  fix go A (ls : list (list A)) : list A :=
  match ls with [] => [] | l :: ls => l ++ @mjoin _ go _ ls end.

(** We define stronger variants of map and fold that allow the mapped
function to use the index of the elements. *)
Definition imap_go {A B} (f : nat → A → B) : nat → list A → list B :=
  fix go (n : nat) (l : list A) :=
  match l with [] => [] | x :: l => f n x :: go (S n) l end.
Definition imap {A B} (f : nat → A → B) : list A → list B := imap_go f 0.

Definition ifoldr {A B} (f : nat → B → A → A) (a : nat → A) :
  nat → list B → A := fix go n l :=
  match l with [] => a n | b :: l => f n b (go (S n) l) end.

Definition zipped_map {A B} (f : list A → list A → A → B) :
  list A → list A → list B := fix go l k :=
  match k with [] => [] | x :: k => f l k x :: go (x :: l) k end.

Inductive zipped_Forall {A} (P : list A → list A → A → Prop) :
    list A → list A → Prop :=
  | zipped_Forall_nil l : zipped_Forall P l []
  | zipped_Forall_cons l k x :
     P l k x → zipped_Forall P (x :: l) k → zipped_Forall P l (x :: k).
Arguments zipped_Forall_nil {_ _} _.
Arguments zipped_Forall_cons {_ _} _ _ _ _ _.

(** Zipping lists. *)
Definition zip_with {A B C} (f : A → B → C) : list A → list B → list C :=
  fix go l1 l2 :=
  match l1, l2 with x1 :: l1, x2 :: l2 => f x1 x2 :: go l1 l2 | _ , _ => [] end.
Notation zip := (zip_with pair).

(** The function [permutations l] yields all permutations of [l]. *)
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

(** The predicate [suffix_of] holds if the first list is a suffix of the second.
The predicate [prefix_of] holds if the first list is a prefix of the second. *)
Definition suffix_of {A} : relation (list A) := λ l1 l2, ∃ k, l2 = k ++ l1.
Definition prefix_of {A} : relation (list A) := λ l1 l2, ∃ k, l2 = l1 ++ k.
Infix "`suffix_of`" := suffix_of (at level 70) : C_scope.
Infix "`prefix_of`" := prefix_of (at level 70) : C_scope.

Section prefix_suffix_ops.
  Context `{∀ x y : A, Decision (x = y)}.

  Definition max_prefix_of : list A → list A → list A * list A * list A :=
    fix go l1 l2 :=
    match l1, l2 with
    | [], l2 => ([], l2, [])
    | l1, [] => (l1, [], [])
    | x1 :: l1, x2 :: l2 =>
      if decide_rel (=) x1 x2
      then snd_map (x1 ::) (go l1 l2)
      else (x1 :: l1, x2 :: l2, [])
    end.
  Definition max_suffix_of (l1 l2 : list A) : list A * list A * list A :=
    match max_prefix_of (reverse l1) (reverse l2) with
    | (k1, k2, k3) => (reverse k1, reverse k2, reverse k3)
    end.

  Definition strip_prefix (l1 l2 : list A) := snd $ fst $ max_prefix_of l1 l2.
  Definition strip_suffix (l1 l2 : list A) := snd $ fst $ max_suffix_of l1 l2.
End prefix_suffix_ops.

(** A list [l1] is a sub list of [l2] if [l2] is obtained by removing elements
from [l1] without changing the order. *)
Inductive sublist {A} : relation (list A) :=
  | sublist_nil : sublist [] []
  | sublist_skip x l1 l2 : sublist l1 l2 → sublist (x :: l1) (x :: l2)
  | sublist_insert x l1 l2 : sublist l1 l2 → sublist l1 (x :: l2).
Infix "`sublist`" := sublist (at level 70) : C_scope.

(** A list [l2] contains a list [l1] if [l2] is obtained by removing elements
from [l1] without changing the order. *)
Inductive contains {A} : relation (list A) :=
  | contains_nil : contains [] []
  | contains_skip x l1 l2 : contains l1 l2 → contains (x :: l1) (x :: l2)
  | contains_swap x y l : contains (y :: x :: l) (x :: y :: l)
  | contains_insert x l1 l2 : contains l1 l2 → contains l1 (x :: l2)
  | contains_trans l1 l2 l3 : contains l1 l2 → contains l2 l3 → contains l1 l3.
Infix "`contains`" := contains (at level 70) : C_scope.

Section contains_dec_help.
  Context {A} {dec : ∀ x y : A, Decision (x = y)}.

  Fixpoint list_remove (x : A) (l : list A) : option (list A) :=
    match l with
    | [] => None
    | y :: l => if decide (x = y) then Some l else (y ::) <$> list_remove x l
    end.
  Fixpoint list_remove_list (k : list A) (l : list A) : option (list A) :=
    match k with
    | [] => Some l
    | x :: k => list_remove x l ≫= list_remove_list k
    end.
End contains_dec_help.

(** The [same_length] view allows convenient induction over two lists with the
same length. *)
Inductive same_length {A B} : list A → list B → Prop :=
  | same_length_nil : same_length [] []
  | same_length_cons x1 x2 l1 l2 :
     same_length l1 l2 → same_length (x1 :: l1) (x2 :: l2).
Infix "`same_length`" := same_length (at level 70) : C_scope.

(** Set operations on lists *)
Section list_set.
  Context {A} {dec : ∀ x y : A, Decision (x = y)}.

  Global Instance elem_of_list_dec {dec : ∀ x y : A, Decision (x = y)}
    (x : A) : ∀ l, Decision (x ∈ l).
  Proof.
   refine (
    fix go l :=
    match l return Decision (x ∈ l) with
    | [] => right _
    | y :: l => cast_if_or (decide (x = y)) (go l)
    end); clear go dec; subst; try (by constructor); abstract by inversion 1.
  Defined.

  Fixpoint remove_dups (l : list A) : list A :=
    match l with
    | [] => []
    | x :: l =>
      if decide_rel (∈) x l then remove_dups l else x :: remove_dups l
    end.

  Fixpoint list_difference (l k : list A) : list A :=
    match l with
    | [] => []
    | x :: l =>
      if decide_rel (∈) x k
      then list_difference l k
      else x :: list_difference l k
    end.
  Fixpoint list_intersection (l k : list A) : list A :=
    match l with
    | [] => []
    | x :: l =>
      if decide_rel (∈) x k
      then x :: list_intersection l k
      else list_intersection l k
    end.
  Definition list_intersection_with (f : A → A → option A) :
    list A → list A → list A := fix go l k :=
    match l with
    | [] => []
    | x :: l => foldr (λ y,
        match f x y with None => id | Some z => (z ::) end) (go l k) k
    end.
End list_set.

(** * Basic tactics on lists *)
(** The tactic [discriminate_list_equality] discharges a goal if it contains
a list equality involving [(::)] and [(++)] of two lists that have a different
length as one of its hypotheses. *)
Tactic Notation "discriminate_list_equality" hyp(H) :=
  apply (f_equal length) in H;
  repeat (simpl in H || rewrite app_length in H); exfalso; lia.
Tactic Notation "discriminate_list_equality" :=
  match goal with
  | H : @eq (list _) _ _ |- _ => discriminate_list_equality H
  end.

(** The tactic [simplify_list_equality] simplifies hypotheses involving
equalities on lists using injectivity of [(::)] and [(++)]. Also, it simplifies
lookups in singleton lists. *)
Ltac simplify_list_equality :=
  repeat match goal with
  | _ => progress simplify_equality
  | H : _ ++ _ = _ ++ _ |- _ => first
    [ apply app_inj_tail in H; destruct H
    | apply app_inv_head in H | apply app_inv_tail in H ]
  | H : [?x] !! ?i = Some ?y |- _ =>
    destruct i; [change (Some x = Some y) in H | discriminate]
  end;
  try discriminate_list_equality.

(** * General theorems *)
Section general_properties.
Context {A : Type}.
Implicit Types x y z : A.
Implicit Types l k : list A.

Global Instance: Injective2 (=) (=) (=) (@cons A).
Proof. by injection 1. Qed.
Global Instance: ∀ x, Injective (=) (=) (x ::).
Proof. by injection 1. Qed.
Global Instance: ∀ l, Injective (=) (=) (:: l).
Proof. by injection 1. Qed.
Global Instance: ∀ k, Injective (=) (=) (k ++).
Proof. intros ???. apply app_inv_head. Qed.
Global Instance: ∀ k, Injective (=) (=) (++ k).
Proof. intros ???. apply app_inv_tail. Qed.
Global Instance: Associative (=) (@app A).
Proof. intros ???. apply app_assoc. Qed.
Global Instance: LeftId (=) [] (@app A).
Proof. done. Qed.
Global Instance: RightId (=) [] (@app A).
Proof. intro. apply app_nil_r. Qed.

Lemma app_nil l1 l2 : l1 ++ l2 = [] ↔ l1 = [] ∧ l2 = [].
Proof. split. apply app_eq_nil. by intros [??]; subst. Qed.
Lemma app_singleton l1 l2 x :
  l1 ++ l2 = [x] ↔ l1 = [] ∧ l2 = [x] ∨ l1 = [x] ∧ l2 = [].
Proof. split. apply app_eq_unit. by intros [[??]|[??]]; subst. Qed.

Lemma cons_middle x l1 l2 : l1 ++ x :: l2 = l1 ++ [x] ++ l2.
Proof. done. Qed.
Lemma app_inj l1 k1 l2 k2 :
  length l1 = length k1 → l1 ++ l2 = k1 ++ k2 → l1 = k1 ∧ l2 = k2.
Proof. revert k1. induction l1; intros [|??]; naive_solver. Qed.

Lemma list_eq l1 l2 : (∀ i, l1 !! i = l2 !! i) → l1 = l2.
Proof.
  revert l2. induction l1; intros [|??] H.
  * done.
  * discriminate (H 0).
  * discriminate (H 0).
  * f_equal; [by injection (H 0) |]. apply IHl1. intro. apply (H (S _)).
Qed.
Lemma list_eq_nil l : (∀ i, l !! i = None) → l = nil.
Proof. intros. by apply list_eq. Qed.

Global Instance list_eq_dec {dec : ∀ x y, Decision (x = y)} : ∀ l k,
  Decision (l = k) := list_eq_dec dec.
Definition list_singleton_dec l : { x | l = [x] } + { length l ≠ 1 }.
Proof. by refine match l with [x] => inleft (x↾_) | _ => inright _ end. Defined.

Lemma nil_or_length_pos l : l = [] ∨ length l ≠ 0.
Proof. destruct l; simpl; auto with lia. Qed.
Lemma nil_length l : length l = 0 → l = [].
Proof. by destruct l. Qed.
Lemma lookup_nil i : @nil A !! i = None.
Proof. by destruct i. Qed.
Lemma lookup_tail l i : tail l !! i = l !! S i.
Proof. by destruct l. Qed.

Lemma lookup_lt_Some l i x : l !! i = Some x → i < length l.
Proof.
  revert i. induction l; intros [|?] ?;
    simpl in *; simplify_equality; simpl; auto with arith.
Qed.
Lemma lookup_lt_is_Some_1 l i : is_Some (l !! i) → i < length l.
Proof. intros [??]; eauto using lookup_lt_Some. Qed.
Lemma lookup_lt_is_Some_2 l i : i < length l → is_Some (l !! i).
Proof.
  revert i. induction l; intros [|?] ?;
    simpl in *; simplify_equality; simpl; eauto with lia.
Qed.
Lemma lookup_lt_is_Some l i : is_Some (l !! i) ↔ i < length l.
Proof. split; auto using lookup_lt_is_Some_1, lookup_lt_is_Some_2. Qed.

Lemma lookup_ge_None l i : l !! i = None ↔ length l ≤ i.
Proof. rewrite eq_None_not_Some, lookup_lt_is_Some. lia. Qed.
Lemma lookup_ge_None_1 l i : l !! i = None → length l ≤ i.
Proof. by rewrite lookup_ge_None. Qed.
Lemma lookup_ge_None_2 l i : length l ≤ i → l !! i = None.
Proof. by rewrite lookup_ge_None. Qed.

Lemma list_eq_length l1 l2 :
  length l2 = length l1 →
  (∀ i x y, l1 !! i = Some x → l2 !! i = Some y → x = y) → l1 = l2.
Proof.
  intros Hl ?. apply list_eq. intros i. destruct (l2 !! i) as [x|] eqn:Hx.
  * destruct (lookup_lt_is_Some_2 l1 i) as [y ?]; subst.
    + rewrite <-Hl. eauto using lookup_lt_Some.
    + naive_solver.
  * by rewrite lookup_ge_None, <-Hl, <-lookup_ge_None.
Qed.

Lemma lookup_app_l l1 l2 i : i < length l1 → (l1 ++ l2) !! i = l1 !! i.
Proof. revert i. induction l1; intros [|?]; simpl; auto with lia. Qed.
Lemma lookup_app_l_Some l1 l2 i x : l1 !! i = Some x → (l1 ++ l2) !! i = Some x.
Proof. intros. rewrite lookup_app_l; eauto using lookup_lt_Some. Qed.
Lemma lookup_app_r l1 l2 i : (l1 ++ l2) !! (length l1 + i) = l2 !! i.
Proof.
  revert i. induction l1; intros [|i]; simpl in *; simplify_equality; auto.
Qed.
Lemma lookup_app_r_alt l1 l2 i :
  length l1 ≤ i → (l1 ++ l2) !! i = l2 !! (i - length l1).
Proof.
  intros. assert (i = length l1 + (i - length l1)) as Hi by lia.
  rewrite Hi at 1. by apply lookup_app_r.
Qed.
Lemma lookup_app_r_Some l1 l2 i x :
  l2 !! i = Some x → (l1 ++ l2) !! (length l1 + i) = Some x.
Proof. by rewrite lookup_app_r. Qed.
Lemma lookup_app_r_Some_alt l1 l2 i x :
  length l1 ≤ i → l2 !! (i - length l1) = Some x → (l1 ++ l2) !! i = Some x.
Proof. intro. by rewrite lookup_app_r_alt. Qed.
Lemma lookup_app_inv l1 l2 i x :
  (l1 ++ l2) !! i = Some x → l1 !! i = Some x ∨ l2 !! (i - length l1) = Some x.
Proof.
  revert i. induction l1; intros [|i] ?; simpl in *; simplify_equality; auto.
Qed.
Lemma list_lookup_middle l1 l2 x : (l1 ++ x :: l2) !! length l1 = Some x.
Proof. by induction l1; simpl. Qed.

Lemma alter_length f l i : length (alter f i l) = length l.
Proof. revert i. induction l; intros [|?]; simpl; auto with lia. Qed.
Lemma insert_length l i x : length (<[i:=x]>l) = length l.
Proof. apply alter_length. Qed.

Lemma list_lookup_alter f l i : alter f i l !! i = f <$> l !! i.
Proof. revert i. induction l. done. intros [|i]. done. apply (IHl i). Qed.
Lemma list_lookup_alter_ne f l i j : i ≠ j → alter f i l !! j = l !! j.
Proof.
  revert i j. induction l; [done|].
  intros [|i] [|j] ?; try done. apply (IHl i). congruence.
Qed.
Lemma list_lookup_insert l i x : i < length l → <[i:=x]>l !! i = Some x.
Proof.
  intros Hi. unfold insert, list_insert. rewrite list_lookup_alter.
  by destruct (lookup_lt_is_Some_2 l i); simplify_option_equality.
Qed.
Lemma list_lookup_insert_ne l i j x : i ≠ j → <[i:=x]>l !! j = l !! j.
Proof. apply list_lookup_alter_ne. Qed.

Lemma list_lookup_other l i x :
  length l ≠ 1 → l !! i = Some x → ∃ j y, j ≠ i ∧ l !! j = Some y.
Proof.
  intros. destruct i, l as [|x0 [|x1 l]]; simpl in *; simplify_equality.
  * by exists 1 x1.
  * by exists 0 x0.
Qed.

Lemma alter_app_l f l1 l2 i :
  i < length l1 → alter f i (l1 ++ l2) = alter f i l1 ++ l2.
Proof.
  revert i. induction l1; intros [|?] ?; simpl in *; f_equal; auto with lia.
Qed.
Lemma alter_app_r f l1 l2 i :
  alter f (length l1 + i) (l1 ++ l2) = l1 ++ alter f i l2.
Proof. revert i. induction l1; intros [|?]; simpl in *; f_equal; auto. Qed.
Lemma alter_app_r_alt f l1 l2 i :
  length l1 ≤ i → alter f i (l1 ++ l2) = l1 ++ alter f (i - length l1) l2.
Proof.
  intros. assert (i = length l1 + (i - length l1)) as Hi by lia.
  rewrite Hi at 1. by apply alter_app_r.
Qed.

Lemma insert_app_l l1 l2 i x :
  i < length l1 → <[i:=x]>(l1 ++ l2) = <[i:=x]>l1 ++ l2.
Proof. apply alter_app_l. Qed.
Lemma insert_app_r l1 l2 i x : <[length l1+i:=x]>(l1 ++ l2) = l1 ++ <[i:=x]>l2.
Proof. apply alter_app_r. Qed.
Lemma insert_app_r_alt l1 l2 i x :
  length l1 ≤ i → <[i:=x]>(l1 ++ l2) = l1 ++ <[i - length l1:=x]>l2.
Proof. apply alter_app_r_alt. Qed.

Lemma insert_consecutive_length l i k :
  length (insert_consecutive i k l) = length l.
Proof. revert i. by induction k; intros; simpl; rewrite ?insert_length. Qed.

Lemma delete_middle l1 l2 x : delete (length l1) (l1 ++ x :: l2) = l1 ++ l2.
Proof. induction l1; simpl; f_equal; auto. Qed.

(** ** Properties of the [elem_of] predicate *)
Lemma not_elem_of_nil x : x ∉ [].
Proof. by inversion 1. Qed.
Lemma elem_of_nil x : x ∈ [] ↔ False.
Proof. intuition. by destruct (not_elem_of_nil x). Qed.
Lemma elem_of_nil_inv l : (∀ x, x ∉ l) → l = [].
Proof. destruct l. done. by edestruct 1; constructor. Qed.
Lemma elem_of_cons l x y : x ∈ y :: l ↔ x = y ∨ x ∈ l.
Proof.
  split.
  * inversion 1; subst. by left. by right.
  * intros [?|?]; subst. by left. by right.
Qed.
Lemma not_elem_of_cons l x y : x ∉ y :: l ↔ x ≠ y ∧ x ∉ l.
Proof. rewrite elem_of_cons. tauto. Qed.
Lemma elem_of_app l1 l2 x : x ∈ l1 ++ l2 ↔ x ∈ l1 ∨ x ∈ l2.
Proof.
  induction l1.
  * split; [by right|]. intros [Hx|]; [|done]. by destruct (elem_of_nil x).
  * simpl. rewrite !elem_of_cons, IHl1. tauto.
Qed.
Lemma not_elem_of_app l1 l2 x : x ∉ l1 ++ l2 ↔ x ∉ l1 ∧ x ∉ l2.
Proof. rewrite elem_of_app. tauto. Qed.
Lemma elem_of_list_singleton x y : x ∈ [y] ↔ x = y.
Proof. rewrite elem_of_cons, elem_of_nil. tauto. Qed.

Global Instance elem_of_list_permutation_proper x : Proper ((≡ₚ) ==> iff) (x ∈).
Proof. induction 1; rewrite ?elem_of_nil, ?elem_of_cons; intuition. Qed.

Lemma elem_of_list_split l x : x ∈ l → ∃ l1 l2, l = l1 ++ x :: l2.
Proof.
  induction 1 as [x l|x y l ? [l1 [l2 ?]]].
  * by eexists [], l.
  * subst. by exists (y :: l1) l2.
Qed.

Lemma elem_of_list_lookup_1 l x : x ∈ l → ∃ i, l !! i = Some x.
Proof.
  induction 1 as [|???? IH]; [by exists 0 |].
  destruct IH as [i ?]; auto. by exists (S i).
Qed.
Lemma elem_of_list_lookup_2 l i x : l !! i = Some x → x ∈ l.
Proof.
  revert i. induction l; intros [|i] ?;
    simpl; simplify_equality; constructor; eauto.
Qed.
Lemma elem_of_list_lookup l x : x ∈ l ↔ ∃ i, l !! i = Some x.
Proof. firstorder eauto using elem_of_list_lookup_1, elem_of_list_lookup_2. Qed.

(** ** Set operations on lists *)
Section list_set.
  Context {dec : ∀ x y, Decision (x = y)}.

  Lemma elem_of_list_difference l k x :
    x ∈ list_difference l k ↔ x ∈ l ∧ x ∉ k.
  Proof.
    split; induction l; simpl; try case_decide;
      rewrite ?elem_of_nil, ?elem_of_cons; intuition congruence.
  Qed.
  Lemma list_difference_nodup l k : NoDup l → NoDup (list_difference l k).
  Proof.
    induction 1; simpl; try case_decide.
    * constructor.
    * done.
    * constructor. rewrite elem_of_list_difference; intuition. done.
  Qed.

  Lemma elem_of_list_intersection l k x :
    x ∈ list_intersection l k ↔ x ∈ l ∧ x ∈ k.
  Proof.
    split; induction l; simpl; repeat case_decide;
      rewrite ?elem_of_nil, ?elem_of_cons; intuition congruence.
  Qed.
  Lemma list_intersection_nodup l k : NoDup l → NoDup (list_intersection l k).
  Proof.
    induction 1; simpl; try case_decide.
    * constructor.
    * constructor. rewrite elem_of_list_intersection; intuition. done.
    * done.
  Qed.

  Lemma elem_of_list_intersection_with f l k x :
    x ∈ list_intersection_with f l k ↔ ∃ x1 x2,
      x1 ∈ l ∧ x2 ∈ k ∧ f x1 x2 = Some x.
  Proof.
    split.
    * induction l as [|x1 l IH]; simpl.
      + by rewrite elem_of_nil.
      + intros Hx. setoid_rewrite elem_of_cons.
        cut ((∃ x2, x2 ∈ k ∧ f x1 x2 = Some x)
          ∨ x ∈ list_intersection_with f l k); [naive_solver|].
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
End list_set.

(** ** Properties of the [NoDup] predicate *)
Lemma NoDup_nil : NoDup (@nil A) ↔ True.
Proof. split; constructor. Qed.
Lemma NoDup_cons x l : NoDup (x :: l) ↔ x ∉ l ∧ NoDup l.
Proof. split. by inversion 1. intros [??]. by constructor. Qed.
Lemma NoDup_cons_11 x l : NoDup (x :: l) → x ∉ l.
Proof. rewrite NoDup_cons. by intros [??]. Qed.
Lemma NoDup_cons_12 x l : NoDup (x :: l) → NoDup l.
Proof. rewrite NoDup_cons. by intros [??]. Qed.
Lemma NoDup_singleton x : NoDup [x].
Proof. constructor. apply not_elem_of_nil. constructor. Qed.

Lemma NoDup_app l k : NoDup (l ++ k) ↔ NoDup l ∧ (∀ x, x ∈ l → x ∉ k) ∧ NoDup k.
Proof.
  induction l; simpl.
  * rewrite NoDup_nil. setoid_rewrite elem_of_nil. naive_solver.
  * rewrite !NoDup_cons.
    setoid_rewrite elem_of_cons. setoid_rewrite elem_of_app. naive_solver.
Qed.

Global Instance NoDup_proper: Proper ((≡ₚ) ==> iff) (@NoDup A).
Proof.
  induction 1 as [|x l k Hlk IH | |].
  * by rewrite !NoDup_nil.
  * by rewrite !NoDup_cons, IH, Hlk.
  * rewrite !NoDup_cons, !elem_of_cons. intuition.
  * intuition.
Qed.

Lemma NoDup_Permutation l k : NoDup l → NoDup k → (∀ x, x ∈ l ↔ x ∈ k) → l ≡ₚ k.
Proof.
  intros Hl. revert k. induction Hl as [|x l Hin ? IH].
  * intros k _ Hk. rewrite (elem_of_nil_inv k); [done |].
    intros x. rewrite <-Hk, elem_of_nil. intros [].
  * intros k Hk Hlk. destruct (elem_of_list_split k x) as [l1 [l2 ?]]; subst.
    { rewrite <-Hlk. by constructor. }
    rewrite <-Permutation_middle, NoDup_cons in Hk.
    destruct Hk as [??]. apply Permutation_cons_app, IH; [done |].
    intros y. specialize (Hlk y).
    rewrite <-Permutation_middle, !elem_of_cons in Hlk. naive_solver.
Qed.

Section no_dup_dec.
  Context `{!∀ x y, Decision (x = y)}.

  Global Instance NoDup_dec: ∀ l, Decision (NoDup l) :=
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

  Lemma elem_of_remove_dups l x : x ∈ remove_dups l ↔ x ∈ l.
  Proof.
    split; induction l; simpl; repeat case_decide;
      rewrite ?elem_of_cons; intuition (simplify_equality; auto).
  Qed.
  Lemma remove_dups_nodup l : NoDup (remove_dups l).
  Proof.
    induction l; simpl; repeat case_decide; try constructor; auto.
    by rewrite elem_of_remove_dups.
  Qed.
End no_dup_dec.

(** ** Properties of the [filter] function *)
Section filter.
  Context (P : A → Prop) `{∀ x, Decision (P x)}.

  Lemma elem_of_list_filter l x : x ∈ filter P l ↔ P x ∧ x ∈ l.
  Proof.
    unfold filter. induction l; simpl; repeat case_decide;
       rewrite ?elem_of_nil, ?elem_of_cons; naive_solver.
  Qed.
  Lemma filter_nodup l : NoDup l → NoDup (filter P l).
  Proof.
    unfold filter. induction 1; simpl; repeat case_decide;
      rewrite ?NoDup_nil, ?NoDup_cons, ?elem_of_list_filter; tauto.
  Qed.
End filter.

(** ** Properties of the [reverse] function *)
Lemma reverse_nil : reverse [] = @nil A.
Proof. done. Qed.
Lemma reverse_singleton x : reverse [x] = [x].
Proof. done. Qed.
Lemma reverse_cons l x : reverse (x :: l) = reverse l ++ [x].
Proof. unfold reverse. by rewrite <-!rev_alt. Qed.
Lemma reverse_snoc l x : reverse (l ++ [x]) = x :: reverse l.
Proof. unfold reverse. by rewrite <-!rev_alt, rev_unit. Qed.
Lemma reverse_app l1 l2 : reverse (l1 ++ l2) = reverse l2 ++ reverse l1.
Proof. unfold reverse. rewrite <-!rev_alt. apply rev_app_distr. Qed.
Lemma reverse_length l : length (reverse l) = length l.
Proof. unfold reverse. rewrite <-!rev_alt. apply rev_length. Qed.
Lemma reverse_involutive l : reverse (reverse l) = l.
Proof. unfold reverse. rewrite <-!rev_alt. apply rev_involutive. Qed.

(** ** Properties of the [take] function *)
Definition take_drop := @firstn_skipn A.

Lemma take_nil n : take n (@nil A) = [].
Proof. by destruct n. Qed.
Lemma take_app l k : take (length l) (l ++ k) = l.
Proof. induction l; simpl; f_equal; auto. Qed.
Lemma take_app_alt l k n : n = length l → take n (l ++ k) = l.
Proof. intros Hn. by rewrite Hn, take_app. Qed.
Lemma take_app_le l k n : n ≤ length l → take n (l ++ k) = take n l.
Proof.
  revert n. induction l; intros [|?] ?; simpl in *; f_equal; auto with lia.
Qed.
Lemma take_app_ge l k n :
  length l ≤ n → take n (l ++ k) = l ++ take (n - length l) k.
Proof.
  revert n. induction l; intros [|?] ?; simpl in *; f_equal; auto with lia.
Qed.
Lemma take_ge l n : length l ≤ n → take n l = l.
Proof.
  revert n. induction l; intros [|?] ?; simpl in *; f_equal; auto with lia.
Qed.

Lemma take_take l n m : take n (take m l) = take (min n m) l.
Proof. revert n m. induction l; intros [|?] [|?]; simpl; f_equal; auto. Qed.
Lemma take_idempotent l n : take n (take n l) = take n l.
Proof. by rewrite take_take, Min.min_idempotent. Qed.

Lemma take_length l n : length (take n l) = min n (length l).
Proof. revert n. induction l; intros [|?]; simpl; f_equal; done. Qed.
Lemma take_length_alt l n : n ≤ length l → length (take n l) = n.
Proof. rewrite take_length. apply Min.min_l. Qed.

Lemma lookup_take l n i : i < n → take n l !! i = l !! i.
Proof.
  revert n i. induction l; intros [|n] i ?; trivial.
  * auto with lia.
  * destruct i; simpl; auto with arith.
Qed.
Lemma lookup_take_ge l n i : n ≤ i → take n l !! i = None.
Proof. revert n i. induction l; intros [|?] [|?] ?; simpl; auto with lia. Qed.
Lemma take_alter f l n i : n ≤ i → take n (alter f i l) = take n l.
Proof.
  intros. apply list_eq. intros j. destruct (le_lt_dec n j).
  * by rewrite !lookup_take_ge.
  * by rewrite !lookup_take, !list_lookup_alter_ne by lia.
Qed.
Lemma take_insert l n i x : n ≤ i → take n (<[i:=x]>l) = take n l.
Proof. apply take_alter. Qed.

(** ** Properties of the [drop] function *)
Lemma drop_nil n : drop n (@nil A) = [].
Proof. by destruct n. Qed.
Lemma drop_app l k : drop (length l) (l ++ k) = k.
Proof. induction l; simpl; f_equal; auto. Qed.
Lemma drop_app_alt l k n : n = length l → drop n (l ++ k) = k.
Proof. intros Hn. by rewrite Hn, drop_app. Qed.
Lemma drop_length l n : length (drop n l) = length l - n.
Proof. revert n. by induction l; intros [|i]; simpl; f_equal. Qed.
Lemma drop_all l : drop (length l) l = [].
Proof. induction l; simpl; auto. Qed.
Lemma drop_all_alt l n : n = length l → drop n l = [].
Proof. intros. subst. by rewrite drop_all. Qed.

Lemma lookup_drop l n i : drop n l !! i = l !! (n + i).
Proof. revert n i. induction l; intros [|i] ?; simpl; auto. Qed.
Lemma drop_alter f l n i : i < n → drop n (alter f i l) = drop n l.
Proof.
  intros. apply list_eq. intros j.
  by rewrite !lookup_drop, !list_lookup_alter_ne by lia.
Qed.
Lemma drop_insert l n i x : i < n → drop n (<[i:=x]>l) = drop n l.
Proof. apply drop_alter. Qed.

Lemma delete_take_drop l i : delete i l = take i l ++ drop (S i) l.
Proof. revert i. induction l; intros [|?]; simpl; auto using f_equal. Qed.

(** ** Properties of the [replicate] function *)
Lemma replicate_length n x : length (replicate n x) = n.
Proof. induction n; simpl; auto. Qed.
Lemma lookup_replicate n x i : i < n → replicate n x !! i = Some x.
Proof. revert i. induction n; intros [|?]; naive_solver auto with lia. Qed.
Lemma lookup_replicate_inv n x y i :
  replicate n x !! i = Some y → y = x ∧ i < n.
Proof. revert i. induction n; intros [|?]; naive_solver auto with lia. Qed.
Lemma replicate_S n x : replicate (S n) x = x :: replicate  n x.
Proof. done. Qed.
Lemma replicate_plus n m x :
  replicate (n + m) x = replicate n x ++ replicate m x.
Proof. induction n; simpl; f_equal; auto. Qed.

Lemma take_replicate n m x : take n (replicate m x) = replicate (min n m) x.
Proof. revert m. by induction n; intros [|?]; simpl; f_equal. Qed.
Lemma take_replicate_plus n m x : take n (replicate (n + m) x) = replicate n x.
Proof. by rewrite take_replicate, min_l by lia. Qed.
Lemma drop_replicate n m x : drop n (replicate m x) = replicate (m - n) x.
Proof. revert m. by induction n; intros [|?]; simpl; f_equal. Qed.
Lemma drop_replicate_plus n m x : drop n (replicate (n + m) x) = replicate m x.
Proof. rewrite drop_replicate. f_equal. lia. Qed.

Lemma reverse_replicate n x : reverse (replicate n x) = replicate n x.
Proof.
  induction n as [|n IH]; [done|]. simpl. rewrite reverse_cons, IH.
  change [x] with (replicate 1 x). by rewrite <-replicate_plus, plus_comm.
Qed.

(** ** Properties of the [resize] function *)
Lemma resize_spec l n x : resize n x l = take n l ++ replicate (n - length l) x.
Proof. revert n. induction l; intros [|?]; simpl; f_equal; auto. Qed.
Lemma resize_0 l x : resize 0 x l = [].
Proof. by destruct l. Qed.
Lemma resize_nil n x : resize n x [] = replicate n x.
Proof. rewrite resize_spec. rewrite take_nil. simpl. f_equal. lia. Qed.
Lemma resize_ge l n x :
  length l ≤ n → resize n x l = l ++ replicate (n - length l) x.
Proof. intros. by rewrite resize_spec, take_ge. Qed.
Lemma resize_le l n x : n ≤ length l → resize n x l = take n l.
Proof.
  intros. rewrite resize_spec, (proj2 (NPeano.Nat.sub_0_le _ _)) by done.
  simpl. by rewrite (right_id_L [] (++)).
Qed.

Lemma resize_all l x : resize (length l) x l = l.
Proof. intros. by rewrite resize_le, take_ge. Qed.
Lemma resize_all_alt l n x : n = length l → resize n x l = l.
Proof. intros. subst. by rewrite resize_all. Qed.

Lemma resize_plus l n m x :
  resize (n + m) x l = resize n x l ++ resize m x (drop n l).
Proof.
  revert n m. induction l; intros [|?] [|?]; simpl; f_equal; auto.
  * by rewrite plus_0_r, (right_id_L [] (++)).
  * by rewrite replicate_plus.
Qed.
Lemma resize_plus_eq l n m x :
  length l = n → resize (n + m) x l = l ++ replicate m x.
Proof.
  intros. subst. by rewrite resize_plus, resize_all, drop_all, resize_nil.
Qed.

Lemma resize_app_le l1 l2 n x :
  n ≤ length l1 → resize n x (l1 ++ l2) = resize n x l1.
Proof.
  intros. by rewrite !resize_le, take_app_le by (rewrite ?app_length; lia).
Qed.
Lemma resize_app_ge l1 l2 n x :
  length l1 ≤ n → resize n x (l1 ++ l2) = l1 ++ resize (n - length l1) x l2.
Proof.
  intros. rewrite !resize_spec, take_app_ge, (associative_L (++)) by done.
  do 2 f_equal. rewrite app_length. lia.
Qed.

Lemma resize_length l n x : length (resize n x l) = n.
Proof. rewrite resize_spec, app_length, replicate_length, take_length. lia. Qed.
Lemma resize_replicate x n m : resize n x (replicate m x) = replicate n x.
Proof. revert m. induction n; intros [|?]; simpl; f_equal; auto. Qed.

Lemma resize_resize l n m x : n ≤ m → resize n x (resize m x l) = resize n x l.
Proof.
  revert n m. induction l; simpl.
  * intros. by rewrite !resize_nil, resize_replicate.
  * intros [|?] [|?] ?; simpl; f_equal; auto with lia.
Qed.
Lemma resize_idempotent l n x : resize n x (resize n x l) = resize n x l.
Proof. by rewrite resize_resize. Qed.

Lemma resize_take_le l n m x : n ≤ m → resize n x (take m l) = resize n x l.
Proof.
  revert n m. induction l; intros [|?] [|?] ?; simpl; f_equal; auto with lia.
Qed.
Lemma resize_take_eq l n x : resize n x (take n l) = resize n x l.
Proof. by rewrite resize_take_le. Qed.

Lemma take_resize l n m x : take n (resize m x l) = resize (min n m) x l.
Proof.
  revert n m.
  induction l; intros [|?] [|?]; simpl; f_equal; auto using take_replicate.
Qed.
Lemma take_resize_le l n m x : n ≤ m → take n (resize m x l) = resize n x l.
Proof. intros. by rewrite take_resize, Min.min_l. Qed.
Lemma take_resize_eq l n x : take n (resize n x l) = resize n x l.
Proof. intros. by rewrite take_resize, Min.min_l. Qed.
Lemma take_length_resize l n x :
  length l ≤ n → take (length l) (resize n x l) = l.
Proof. intros. by rewrite take_resize_le, resize_all. Qed.
Lemma take_length_resize_alt l n m x :
  m = length l → m ≤ n → take m (resize n x l) = l.
Proof. intros. subst. by apply take_length_resize. Qed.
Lemma take_resize_plus l n m x : take n (resize (n + m) x l) = resize n x l.
Proof. by rewrite take_resize, min_l by lia. Qed.

Lemma drop_resize_le l n m x :
  n ≤ m → drop n (resize m x l) = resize (m - n) x (drop n l).
Proof.
  revert n m. induction l; simpl.
  * intros. by rewrite drop_nil, !resize_nil, drop_replicate.
  * intros [|?] [|?] ?; simpl; try case_match; auto with lia.
Qed.
Lemma drop_resize_plus l n m x :
  drop n (resize (n + m) x l) = resize m x (drop n l).
Proof. rewrite drop_resize_le by lia. f_equal. lia. Qed.

(** ** Properties of the [Permutation] predicate *)
Lemma Permutation_nil l : l ≡ₚ [] ↔ l = [].
Proof. split. by intro; apply Permutation_nil. by intro; subst. Qed.
Lemma Permutation_singleton l x : l ≡ₚ [x] ↔ l = [x].
Proof. split. by intro; apply Permutation_length_1_inv. by intro; subst. Qed.
Definition Permutation_skip := @perm_skip A.
Definition Permutation_swap := @perm_swap A.
Definition Permutation_singleton_inj := @Permutation_length_1 A.

Global Existing Instance Permutation_app'_Proper.
Global Instance: Proper ((≡ₚ) ==> (=)) (@length A).
Proof. induction 1; simpl; auto with lia. Qed.
Global Instance: Commutative (≡ₚ) (@app A).
Proof.
  intros l1. induction l1 as [|x l1 IH]; intros l2; simpl.
  * by rewrite (right_id_L [] (++)).
  * rewrite Permutation_middle, IH. simpl. by rewrite Permutation_middle.
Qed.
Global Instance: ∀ x : A, Injective (≡ₚ) (≡ₚ) (x ::).
Proof. red. eauto using Permutation_cons_inv. Qed.
Global Instance: ∀ k : list A, Injective (≡ₚ) (≡ₚ) (k ++).
Proof.
  red. induction k as [|x k IH]; intros l1 l2; simpl; auto.
  intros. by apply IH, (injective (x ::)).
Qed.
Global Instance: ∀ k : list A, Injective (≡ₚ) (≡ₚ) (++ k).
Proof.
  intros k l1 l2. rewrite !(commutative (++) _ k). by apply (injective (k ++)).
Qed.

(** ** Properties of the [prefix_of] and [suffix_of] predicates *)
Global Instance: PreOrder (@prefix_of A).
Proof.
  split.
  * intros ?. eexists []. by rewrite (right_id_L [] (++)).
  * intros ??? [k1 ?] [k2 ?].
    exists (k1 ++ k2). subst. by rewrite (associative_L (++)).
Qed.

Lemma prefix_of_nil l : [] `prefix_of` l.
Proof. by exists l. Qed.
Lemma prefix_of_nil_not x l : ¬x :: l `prefix_of` [].
Proof. by intros [k E]. Qed.
Lemma prefix_of_cons x l1 l2 : l1 `prefix_of` l2 → x :: l1 `prefix_of` x :: l2.
Proof. intros [k E]. exists k. by subst. Qed.
Lemma prefix_of_cons_alt x y l1 l2 :
  x = y → l1 `prefix_of` l2 → x :: l1 `prefix_of` y :: l2.
Proof. intro. subst. apply prefix_of_cons. Qed.
Lemma prefix_of_cons_inv_1 x y l1 l2 : x :: l1 `prefix_of` y :: l2 → x = y.
Proof. intros [k E]. by injection E. Qed.
Lemma prefix_of_cons_inv_2 x y l1 l2 :
  x :: l1 `prefix_of` y :: l2 → l1 `prefix_of` l2.
Proof. intros [k E]. exists k. by injection E. Qed.

Lemma prefix_of_app k l1 l2 : l1 `prefix_of` l2 → k ++ l1 `prefix_of` k ++ l2.
Proof. intros [k' ?]. subst. exists k'. by rewrite (associative_L (++)). Qed.
Lemma prefix_of_app_alt k1 k2 l1 l2 :
  k1 = k2 → l1 `prefix_of` l2 → k1 ++ l1 `prefix_of` k2 ++ l2.
Proof. intro. subst. apply prefix_of_app. Qed.
Lemma prefix_of_app_l l1 l2 l3 : l1 ++ l3 `prefix_of` l2 → l1 `prefix_of` l2.
Proof.
  intros [k ?]. red. exists (l3 ++ k). subst. by rewrite <-(associative_L (++)).
Qed.
Lemma prefix_of_app_r l1 l2 l3 : l1 `prefix_of` l2 → l1 `prefix_of` l2 ++ l3.
Proof.
  intros [k ?]. exists (k ++ l3). subst. by rewrite (associative_L (++)).
Qed.

Lemma prefix_of_length l1 l2 : l1 `prefix_of` l2 → length l1 ≤ length l2.
Proof. intros [??]. subst. rewrite app_length. lia. Qed.
Lemma prefix_of_snoc_not l x : ¬l ++ [x] `prefix_of` l.
Proof. intros [??]. discriminate_list_equality. Qed.

Global Instance: PreOrder (@suffix_of A).
Proof.
  split.
  * intros ?. by eexists [].
  * intros ??? [k1 ?] [k2 ?].
    exists (k2 ++ k1). subst. by rewrite (associative_L (++)).
Qed.

Global Instance prefix_of_dec `{∀ x y, Decision (x = y)} : ∀ l1 l2,
  Decision (l1 `prefix_of` l2) := fix go l1 l2 :=
  match l1, l2 return { l1 `prefix_of` l2 } + { ¬l1 `prefix_of` l2 } with
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

Section prefix_ops.
  Context `{∀ x y, Decision (x = y)}.

  Lemma max_prefix_of_fst l1 l2 :
    l1 = snd (max_prefix_of l1 l2) ++ fst (fst (max_prefix_of l1 l2)).
  Proof.
    revert l2. induction l1; intros [|??]; simpl;
      repeat case_decide; simpl; f_equal; auto.
  Qed.
  Lemma max_prefix_of_fst_alt l1 l2 k1 k2 k3 :
    max_prefix_of l1 l2 = (k1, k2, k3) → l1 = k3 ++ k1.
  Proof.
    intro. pose proof (max_prefix_of_fst l1 l2).
    by destruct (max_prefix_of l1 l2) as [[]?]; simplify_equality.
  Qed.
  Lemma max_prefix_of_fst_prefix l1 l2 :
    snd (max_prefix_of l1 l2) `prefix_of` l1.
  Proof. eexists. apply max_prefix_of_fst. Qed.
  Lemma max_prefix_of_fst_prefix_alt l1 l2 k1 k2 k3 :
    max_prefix_of l1 l2 = (k1, k2, k3) → k3 `prefix_of` l1.
  Proof. eexists. eauto using max_prefix_of_fst_alt. Qed.

  Lemma max_prefix_of_snd l1 l2 :
    l2 = snd (max_prefix_of l1 l2) ++ snd (fst (max_prefix_of l1 l2)).
  Proof.
    revert l2. induction l1; intros [|??]; simpl;
      repeat case_decide; simpl; f_equal; auto.
  Qed.
  Lemma max_prefix_of_snd_alt l1 l2 k1 k2 k3 :
    max_prefix_of l1 l2 = (k1, k2, k3) → l2 = k3 ++ k2.
  Proof.
    intro. pose proof (max_prefix_of_snd l1 l2).
    by destruct (max_prefix_of l1 l2) as [[]?]; simplify_equality.
  Qed.
  Lemma max_prefix_of_snd_prefix l1 l2 :
    snd (max_prefix_of l1 l2) `prefix_of` l2.
  Proof. eexists. apply max_prefix_of_snd. Qed.
  Lemma max_prefix_of_snd_prefix_alt l1 l2 k1 k2 k3 :
    max_prefix_of l1 l2 = (k1,k2,k3) → k3 `prefix_of` l2.
  Proof. eexists. eauto using max_prefix_of_snd_alt. Qed.

  Lemma max_prefix_of_max l1 l2 k :
    k `prefix_of` l1 → k `prefix_of` l2 →
    k `prefix_of` snd (max_prefix_of l1 l2).
  Proof.
    intros [l1' ?] [l2' ?]. subst.
    by induction k; simpl; repeat case_decide; simpl;
      auto using prefix_of_nil, prefix_of_cons.
  Qed.
  Lemma max_prefix_of_max_alt l1 l2 k1 k2 k3 k :
    max_prefix_of l1 l2 = (k1,k2,k3) →
    k `prefix_of` l1 → k `prefix_of` l2 → k `prefix_of` k3.
  Proof.
    intro. pose proof (max_prefix_of_max l1 l2 k).
    by destruct (max_prefix_of l1 l2) as [[]?]; simplify_equality.
  Qed.

  Lemma max_prefix_of_max_snoc l1 l2 k1 k2 k3 x1 x2 :
    max_prefix_of l1 l2 = (x1 :: k1, x2 :: k2, k3) → x1 ≠ x2.
  Proof.
    intros Hl ?. subst. destruct (prefix_of_snoc_not k3 x2).
    eapply max_prefix_of_max_alt; eauto.
    * rewrite (max_prefix_of_fst_alt _ _ _ _ _ Hl).
      apply prefix_of_app, prefix_of_cons, prefix_of_nil.
    * rewrite (max_prefix_of_snd_alt _ _ _ _ _ Hl).
      apply prefix_of_app, prefix_of_cons, prefix_of_nil.
  Qed.
End prefix_ops.

Lemma prefix_suffix_reverse l1 l2 :
  l1 `prefix_of` l2 ↔ reverse l1 `suffix_of` reverse l2.
Proof.
  split; intros [k E]; exists (reverse k).
  * by rewrite E, reverse_app.
  * by rewrite <-(reverse_involutive l2), E, reverse_app, reverse_involutive.
Qed.
Lemma suffix_prefix_reverse l1 l2 :
  l1 `suffix_of` l2 ↔ reverse l1 `prefix_of` reverse l2.
Proof. by rewrite prefix_suffix_reverse, !reverse_involutive. Qed.

Lemma suffix_of_nil l : [] `suffix_of` l.
Proof. exists l. by rewrite (right_id_L [] (++)). Qed.
Lemma suffix_of_nil_inv l : l `suffix_of` [] → l = [].
Proof. by intros [[|?] ?]; simplify_list_equality. Qed.
Lemma suffix_of_cons_nil_inv x l : ¬x :: l `suffix_of` [].
Proof. by intros [[] ?]. Qed.
Lemma suffix_of_snoc l1 l2 x :
  l1 `suffix_of` l2 → l1 ++ [x] `suffix_of` l2 ++ [x].
Proof. intros [k E]. exists k. subst. by rewrite (associative_L (++)). Qed.
Lemma suffix_of_snoc_alt x y l1 l2 :
  x = y → l1 `suffix_of` l2 → l1 ++ [x] `suffix_of` l2 ++ [y].
Proof. intro. subst. apply suffix_of_snoc. Qed.

Lemma suffix_of_app l1 l2 k : l1 `suffix_of` l2 → l1 ++ k `suffix_of` l2 ++ k.
Proof. intros [k' E]. exists k'. subst. by rewrite (associative_L (++)). Qed.
Lemma suffix_of_app_alt l1 l2 k1 k2 :
  k1 = k2 → l1 `suffix_of` l2 → l1 ++ k1 `suffix_of` l2 ++ k2.
Proof. intro. subst. apply suffix_of_app. Qed.

Lemma suffix_of_snoc_inv_1 x y l1 l2 :
  l1 ++ [x] `suffix_of` l2 ++ [y] → x = y.
Proof.
  intros [k' E]. rewrite (associative_L (++)) in E. by simplify_list_equality.
Qed.
Lemma suffix_of_snoc_inv_2 x y l1 l2 :
  l1 ++ [x] `suffix_of` l2 ++ [y] → l1 `suffix_of` l2.
Proof.
  intros [k' E]. exists k'. rewrite (associative_L (++)) in E.
  by simplify_list_equality.
Qed.
Lemma suffix_of_app_inv l1 l2 k :
  l1 ++ k `suffix_of` l2 ++ k → l1 `suffix_of` l2.
Proof.
  intros [k' E]. exists k'. rewrite (associative_L (++)) in E.
  by simplify_list_equality.
Qed.

Lemma suffix_of_cons_l l1 l2 x : x :: l1 `suffix_of` l2 → l1 `suffix_of` l2.
Proof.
  intros [k ?]. exists (k ++ [x]). subst. by rewrite <-(associative_L (++)).
Qed.
Lemma suffix_of_app_l l1 l2 l3 : l3 ++ l1 `suffix_of` l2 → l1 `suffix_of` l2.
Proof.
  intros [k ?]. exists (k ++ l3). subst. by rewrite <-(associative_L (++)).
Qed.
Lemma suffix_of_cons_r l1 l2 x : l1 `suffix_of` l2 → l1 `suffix_of` x :: l2.
Proof. intros [k ?]. exists (x :: k). by subst. Qed.
Lemma suffix_of_app_r l1 l2 l3 : l1 `suffix_of` l2 → l1 `suffix_of` l3 ++ l2.
Proof. intros [k ?]. exists (l3 ++ k). subst. by rewrite (associative_L _). Qed.

Lemma suffix_of_cons_inv l1 l2 x y :
  x :: l1 `suffix_of` y :: l2 → x :: l1 = y :: l2 ∨ x :: l1 `suffix_of` l2.
Proof.
  intros [[|? k] E]; [by left |].
  right. simplify_equality. by apply suffix_of_app_r.
Qed.

Lemma suffix_of_length l1 l2 : l1 `suffix_of` l2 → length l1 ≤ length l2.
Proof. intros [??]. subst. rewrite app_length. lia. Qed.
Lemma suffix_of_cons_not x l : ¬x :: l `suffix_of` l.
Proof. intros [??]. discriminate_list_equality. Qed.

Global Instance suffix_of_dec `{∀ x y, Decision (x = y)} l1 l2 :
  Decision (l1 `suffix_of` l2).
Proof.
  refine (cast_if (decide_rel prefix_of (reverse l1) (reverse l2)));
   abstract (by rewrite suffix_prefix_reverse).
Defined.

Section max_suffix_of.
  Context `{∀ x y, Decision (x = y)}.

  Lemma max_suffix_of_fst l1 l2 :
    l1 = fst (fst (max_suffix_of l1 l2)) ++ snd (max_suffix_of l1 l2).
  Proof.
    rewrite <-(reverse_involutive l1) at 1.
    rewrite (max_prefix_of_fst (reverse l1) (reverse l2)). unfold max_suffix_of.
    destruct (max_prefix_of (reverse l1) (reverse l2)) as ((?&?)&?); simpl.
    by rewrite reverse_app.
  Qed.
  Lemma max_suffix_of_fst_alt l1 l2 k1 k2 k3 :
    max_suffix_of l1 l2 = (k1, k2, k3) → l1 = k1 ++ k3.
  Proof.
    intro. pose proof (max_suffix_of_fst l1 l2).
    by destruct (max_suffix_of l1 l2) as [[]?]; simplify_equality.
  Qed.
  Lemma max_suffix_of_fst_suffix l1 l2 :
    snd (max_suffix_of l1 l2) `suffix_of` l1.
  Proof. eexists. apply max_suffix_of_fst. Qed.
  Lemma max_suffix_of_fst_suffix_alt l1 l2 k1 k2 k3 :
    max_suffix_of l1 l2 = (k1, k2, k3) → k3 `suffix_of` l1.
  Proof. eexists. eauto using max_suffix_of_fst_alt. Qed.

  Lemma max_suffix_of_snd l1 l2 :
    l2 = snd (fst (max_suffix_of l1 l2)) ++ snd (max_suffix_of l1 l2).
  Proof.
    rewrite <-(reverse_involutive l2) at 1.
    rewrite (max_prefix_of_snd (reverse l1) (reverse l2)).
    unfold max_suffix_of.
    destruct (max_prefix_of (reverse l1) (reverse l2)) as ((?&?)&?); simpl.
    by rewrite reverse_app.
  Qed.
  Lemma max_suffix_of_snd_alt l1 l2 k1 k2 k3 :
    max_suffix_of l1 l2 = (k1,k2,k3) → l2 = k2 ++ k3.
  Proof.
    intro. pose proof (max_suffix_of_snd l1 l2).
    by destruct (max_suffix_of l1 l2) as [[]?]; simplify_equality.
  Qed.
  Lemma max_suffix_of_snd_suffix l1 l2 :
    snd (max_suffix_of l1 l2) `suffix_of` l2.
  Proof. eexists. apply max_suffix_of_snd. Qed.
  Lemma max_suffix_of_snd_suffix_alt l1 l2 k1 k2 k3 :
    max_suffix_of l1 l2 = (k1,k2,k3) → k3 `suffix_of` l2.
  Proof. eexists. eauto using max_suffix_of_snd_alt. Qed.

  Lemma max_suffix_of_max l1 l2 k :
    k `suffix_of` l1 → k `suffix_of` l2 →
     k `suffix_of` snd (max_suffix_of l1 l2).
  Proof.
    generalize (max_prefix_of_max (reverse l1) (reverse l2)).
    rewrite !suffix_prefix_reverse. unfold max_suffix_of.
    destruct (max_prefix_of (reverse l1) (reverse l2)) as ((?&?)&?); simpl.
    rewrite reverse_involutive. auto.
  Qed.
  Lemma max_suffix_of_max_alt l1 l2 k1 k2 k3 k :
    max_suffix_of l1 l2 = (k1, k2, k3) →
    k `suffix_of` l1 → k `suffix_of` l2 → k `suffix_of` k3.
  Proof.
    intro. pose proof (max_suffix_of_max l1 l2 k).
    by destruct (max_suffix_of l1 l2) as [[]?]; simplify_equality.
  Qed.

  Lemma max_suffix_of_max_snoc l1 l2 k1 k2 k3 x1 x2 :
    max_suffix_of l1 l2 = (k1 ++ [x1], k2 ++ [x2], k3) → x1 ≠ x2.
  Proof.
    intros Hl ?. subst. destruct (suffix_of_cons_not x2 k3).
    eapply max_suffix_of_max_alt; eauto.
    * rewrite (max_suffix_of_fst_alt _ _ _ _ _ Hl).
      by apply (suffix_of_app [x2]), suffix_of_app_r.
    * rewrite (max_suffix_of_snd_alt _ _ _ _ _ Hl).
      by apply (suffix_of_app [x2]), suffix_of_app_r.
  Qed.
End max_suffix_of.

(** ** Properties of the [sublist] predicate *)
Lemma sublist_length l1 l2 : l1 `sublist` l2 → length l1 ≤ length l2.
Proof. induction 1; simpl; auto with arith. Qed.

Lemma sublist_nil_l l : [] `sublist` l.
Proof. induction l; try constructor; auto. Qed.
Lemma sublist_nil_r l : l `sublist` [] ↔ l = [].
Proof. split. by inversion 1. intros. subst. constructor. Qed.

Lemma sublist_app l1 l2 k1 k2 :
  l1 `sublist` l2 → k1 `sublist` k2 → l1 ++ k1 `sublist` l2 ++ k2.
Proof. induction 1; simpl; try constructor; auto. Qed.
Lemma sublist_inserts_l k l1 l2 : l1 `sublist` l2 → l1 `sublist` k ++ l2.
Proof. induction k; try constructor; auto. Qed.
Lemma sublist_inserts_r k l1 l2 : l1 `sublist` l2 → l1 `sublist` l2 ++ k.
Proof. induction 1; simpl; try constructor; auto using sublist_nil_l. Qed.

Lemma sublist_cons_r x l k :
  l `sublist` x :: k ↔ l `sublist` k ∨ ∃ l', l = x :: l' ∧ l' `sublist` k.
Proof.
  split. inversion 1; eauto. intros [?|(?&?&?)]; subst; constructor; auto.
Qed.
Lemma sublist_cons_l x l k :
  x :: l `sublist` k ↔ ∃ k1 k2, k = k1 ++ x :: k2 ∧ l `sublist` k2.
Proof.
  split.
  * intros Hlk. induction k as [|y k IH]; inversion Hlk.
    + eexists [], k. by repeat constructor.
    + destruct IH as (k1&k2&?&?); subst; auto. by exists (y :: k1) k2.
  * intros (k1&k2&?&?). subst. by apply sublist_inserts_l, sublist_skip.
Qed.

Lemma sublist_app_r l k1 k2 :
  l `sublist` k1 ++ k2 ↔
    ∃ l1 l2, l = l1 ++ l2 ∧ l1 `sublist` k1 ∧ l2 `sublist` k2.
Proof.
  split.
  * revert l k2. induction k1 as [|y k1 IH]; intros l k2; simpl.
    { eexists [], l. by repeat constructor. }
    rewrite sublist_cons_r. intros [?|(l' & ? &?)]; subst.
    + destruct (IH l k2) as (l1&l2&?&?&?); trivial; subst.
      exists l1 l2. auto using sublist_insert.
    + destruct (IH l' k2) as (l1&l2&?&?&?); trivial; subst.
      exists (y :: l1) l2. auto using sublist_skip.
  * intros (?&?&?&?&?); subst. auto using sublist_app.
Qed.
Lemma sublist_app_l l1 l2 k :
  l1 ++ l2 `sublist` k ↔
    ∃ k1 k2, k = k1 ++ k2 ∧ l1 `sublist` k1 ∧ l2 `sublist` k2.
Proof.
  split.
  * revert l2 k. induction l1 as [|x l1 IH]; intros l2 k; simpl.
    { eexists [], k. by repeat constructor. }
    rewrite sublist_cons_l. intros (k1 & k2 &?&?); subst.
    destruct (IH l2 k2) as (h1 & h2 &?&?&?); trivial; subst.
    exists (k1 ++ x :: h1) h2. rewrite <-(associative_L (++)).
    auto using sublist_inserts_l, sublist_skip.
  * intros (?&?&?&?&?); subst. auto using sublist_app.
Qed.
Lemma sublist_app_inv_l k l1 l2 : k ++ l1 `sublist` k ++ l2 → l1 `sublist` l2.
Proof.
  induction k as [|y k IH]; simpl; [done |].
  rewrite sublist_cons_r. intros [Hl12|(?&?&?)]; [|simplify_equality; eauto].
  rewrite sublist_cons_l in Hl12. destruct Hl12 as (k1&k2&Hk&?).
  apply IH. rewrite Hk. eauto using sublist_inserts_l, sublist_insert.
Qed.
Lemma sublist_app_inv_r k l1 l2 : l1 ++ k `sublist` l2 ++ k → l1 `sublist` l2.
Proof.
  revert l1 l2. induction k as [|y k IH]; intros l1 l2.
  { by rewrite !(right_id_L [] (++)). }
  intros. feed pose proof (IH (l1 ++ [y]) (l2 ++ [y])) as Hl12.
  { by rewrite <-!(associative_L (++)). }
  rewrite sublist_app_l in Hl12. destruct Hl12 as (k1&k2&E&?&Hk2).
  destruct k2 as [|z k2] using rev_ind; [inversion Hk2|].
  rewrite (associative_L (++)) in E. simplify_list_equality.
  eauto using sublist_inserts_r.
Qed.

Global Instance: PartialOrder (@sublist A).
Proof.
  split; [split|].
  * intros l. induction l; constructor; auto.
  * intros l1 l2 l3 Hl12. revert l3. induction Hl12.
    + auto using sublist_nil_l.
    + intros ?. rewrite sublist_cons_l. intros (?&?&?&?); subst.
      eauto using sublist_inserts_l, sublist_skip.
    + intros ?. rewrite sublist_cons_l. intros (?&?&?&?); subst.
      eauto using sublist_inserts_l, sublist_insert.
  * intros l1 l2 Hl12 Hl21. apply sublist_length in Hl21.
    induction Hl12; simpl in *; f_equal; auto with arith.
    apply sublist_length in Hl12. lia.
Qed.

Lemma sublist_take l i : take i l `sublist` l.
Proof. rewrite <-(take_drop i l) at 2. by apply sublist_inserts_r. Qed.
Lemma sublist_drop l i : drop i l `sublist` l.
Proof. rewrite <-(take_drop i l) at 2. by apply sublist_inserts_l. Qed.
Lemma sublist_delete l i : delete i l `sublist` l.
Proof. revert i. by induction l; intros [|?]; simpl; constructor. Qed.
Lemma sublist_delete_list l is : delete_list is l `sublist` l.
Proof.
  induction is as [|i is IH]; simpl; [done |].
  transitivity (delete_list is l); auto using sublist_delete.
Qed.

Lemma sublist_alt l1 l2 : l1 `sublist` l2 ↔ ∃ is, l1 = delete_list is l2.
Proof.
  split.
  * intros Hl12. cut (∀ k, ∃ is, k ++ l1 = delete_list is (k ++ l2)).
    { intros help. apply (help []). }
    induction Hl12 as [|x l1 l2 _ IH|x l1 l2 _ IH]; intros k.
    + by eexists [].
    + destruct (IH (k ++ [x])) as [is His]. exists is.
      by rewrite <-!(associative_L (++)) in His.
    + destruct (IH k) as [is His]. exists (is ++ [length k]).
      unfold delete_list. rewrite fold_right_app. simpl.
      by rewrite delete_middle.
  * intros [is ?]. subst. apply sublist_delete_list.
Qed.

Lemma Permutation_sublist l1 l2 l3 :
  l1 ≡ₚ l2 → l2 `sublist` l3 → ∃ l4, l1 `sublist` l4 ∧ l4 ≡ₚ l3.
Proof.
  intros Hl1l2. revert l3.
  induction Hl1l2 as [|x l1 l2 ? IH|x y l1|l1 l1' l2 ? IH1 ? IH2].
  * intros l3. by exists l3.
  * intros l3. rewrite sublist_cons_l. intros (l3'&l3''&?&?); subst.
    destruct (IH l3'') as (l4&?&Hl4); auto. exists (l3' ++ x :: l4).
    split. by apply sublist_inserts_l, sublist_skip. by rewrite Hl4.
  * intros l3. rewrite sublist_cons_l. intros (l3'&l3''&?& Hl3); subst.
    rewrite sublist_cons_l in Hl3. destruct Hl3 as (l5'&l5''&?& Hl5); subst.
    exists (l3' ++ y :: l5' ++ x :: l5''). split.
    - by do 2 apply sublist_inserts_l, sublist_skip.
    - by rewrite !Permutation_middle, Permutation_swap.
  * intros l3 ?. destruct (IH2 l3) as (l3'&?&?); trivial.
    destruct (IH1 l3') as (l3'' &?&?); trivial. exists l3''.
    split. done. etransitivity; eauto.
Qed.
Lemma sublist_Permutation l1 l2 l3 :
  l1 `sublist` l2 → l2 ≡ₚ l3 → ∃ l4, l1 ≡ₚ l4 ∧ l4 `sublist` l3.
Proof.
  intros Hl1l2 Hl2l3. revert l1 Hl1l2.
  induction Hl2l3 as [|x l2 l3 ? IH|x y l2|l2 l2' l3 ? IH1 ? IH2].
  * intros l1. by exists l1.
  * intros l1. rewrite sublist_cons_r. intros [?|(l1'&l1''&?)]; subst.
    { destruct (IH l1) as (l4&?&?); trivial.
      exists l4. split. done. by constructor. }
    destruct (IH l1') as (l4&?&Hl4); auto. exists (x :: l4).
    split. by constructor. by constructor.
  * intros l1. rewrite sublist_cons_r. intros [Hl1|(l1'&l1''&Hl1)]; subst.
    { exists l1. split; [done|]. rewrite sublist_cons_r in Hl1.
      destruct Hl1 as [?|(l1'&?&?)]; subst; by repeat constructor. }
    rewrite sublist_cons_r in Hl1. destruct Hl1 as [?|(l1''&?&?)]; subst.
    + exists (y :: l1'). by repeat constructor.
    + exists (x :: y :: l1''). by repeat constructor.
  * intros l1 ?. destruct (IH1 l1) as (l3'&?&?); trivial.
    destruct (IH2 l3') as (l3'' &?&?); trivial. exists l3''.
    split; [|done]. etransitivity; eauto.
Qed.

(** Properties of the [contains] predicate *)
Lemma contains_length l1 l2 : l1 `contains` l2 → length l1 ≤ length l2.
Proof. induction 1; simpl; auto with lia. Qed.
Lemma contains_nil_l l : [] `contains` l.
Proof. induction l; constructor; auto. Qed.
Lemma contains_nil_r l : l `contains` [] ↔ l = [].
Proof.
  split; [|intros; subst; constructor].
  intros Hl. apply contains_length in Hl. destruct l; simpl in *; auto with lia.
Qed.

Global Instance: PreOrder (@contains A).
Proof.
  split.
  * intros l. induction l; constructor; auto.
  * red. apply contains_trans.
Qed.

Lemma Permutation_contains l1 l2 : l1 ≡ₚ l2 → l1 `contains` l2.
Proof. induction 1; econstructor; eauto. Qed.
Lemma sublist_contains l1 l2 : l1 `sublist` l2 → l1 `contains` l2.
Proof. induction 1; constructor; auto. Qed.
Lemma contains_Permutation_alt l1 l2 :
  length l2 ≤ length l1 → l1 `contains` l2 → l1 ≡ₚ l2.
Proof.
  intros Hl21 Hl12. revert Hl21. elim Hl12; clear l1 l2 Hl12; simpl.
  * constructor.
  * constructor; auto with lia.
  * constructor; auto with lia.
  * intros x l1 l2 ? IH ?. feed specialize IH; [lia|].
    apply Permutation_length in IH. lia.
  * intros l1 l2 l3 Hl12 ? Hl23 ?.
    apply contains_length in Hl12. apply contains_length in Hl23.
    transitivity l2; auto with lia.
Qed.
Lemma contains_Permutation l1 l2 :
  length l2 = length l1 → l1 `contains` l2 → l1 ≡ₚ l2.
Proof. intro. apply contains_Permutation_alt. lia. Qed.

Global Instance: Proper ((≡ₚ) ==> (≡ₚ) ==> iff) (@contains A).
Proof.
  intros l1 l2 ? k1 k2 ?. split; intros.
  * transitivity l1. by apply Permutation_contains.
    transitivity k1. done. by apply Permutation_contains.
  * transitivity l2. by apply Permutation_contains.
    transitivity k2. done. by apply Permutation_contains.
Qed.
Global Instance: AntiSymmetric (≡ₚ) (@contains A).
Proof. red. auto using contains_Permutation_alt, contains_length. Qed.

Lemma contains_take l i : take i l `contains` l.
Proof. auto using sublist_take, sublist_contains. Qed.
Lemma contains_drop l i : drop i l `contains` l.
Proof. auto using sublist_drop, sublist_contains. Qed.
Lemma contains_delete l i : delete i l `contains` l.
Proof. auto using sublist_delete, sublist_contains. Qed.
Lemma contains_delete_list l is : delete_list is l `sublist` l.
Proof. auto using sublist_delete_list, sublist_contains. Qed.

Lemma contains_sublist_l l1 l3 :
  l1 `contains` l3 ↔ ∃ l2, l1 `sublist` l2 ∧ l2 ≡ₚ l3.
Proof.
  split.
  { intros Hl13. elim Hl13; clear l1 l3 Hl13.
    * by eexists [].
    * intros x l1 l3 ? (l2&?&?). exists (x :: l2). by repeat constructor.
    * intros x y l. exists (y :: x :: l). by repeat constructor.
    * intros x l1 l3 ? (l2&?&?). exists (x :: l2). by repeat constructor.
    * intros l1 l3 l5 ? (l2&?&?) ? (l4&?&?).
      destruct (Permutation_sublist l2 l3 l4) as (l3'&?&?); trivial.
      exists l3'. split; etransitivity; eauto. }
  intros (l2&?&?).
  transitivity l2; auto using sublist_contains, Permutation_contains.
Qed.
Lemma contains_sublist_r l1 l3 :
  l1 `contains` l3 ↔ ∃ l2, l1 ≡ₚ l2 ∧ l2 `sublist` l3.
Proof.
  rewrite contains_sublist_l.
  split; intros (l2&?&?); eauto using sublist_Permutation, Permutation_sublist.
Qed.

Lemma contains_inserts_l k l1 l2 : l1 `contains` l2 → l1 `contains` k ++ l2.
Proof. induction k; try constructor; auto. Qed.
Lemma contains_inserts_r k l1 l2 : l1 `contains` l2 → l1 `contains` l2 ++ k.
Proof. rewrite (commutative (++)). apply contains_inserts_l. Qed.
Lemma contains_skips_l k l1 l2 : l1 `contains` l2 → k ++ l1 `contains` k ++ l2.
Proof. induction k; try constructor; auto. Qed.
Lemma contains_skips_r k l1 l2 : l1 `contains` l2 → l1 ++ k `contains` l2 ++ k.
Proof. rewrite !(commutative (++) _ k). apply contains_skips_l. Qed.
Lemma contains_app l1 l2 k1 k2 :
  l1 `contains` l2 → k1 `contains` k2 → l1 ++ k1 `contains` l2 ++ k2.
Proof.
  transitivity (l1 ++ k2); auto using contains_skips_l, contains_skips_r.
Qed.

Lemma contains_cons_r x l k :
  l `contains` x :: k ↔ l `contains` k ∨ ∃ l', l ≡ₚ x :: l' ∧ l' `contains` k.
Proof.
  split.
  * rewrite contains_sublist_r. intros (l'&E&Hl').
    rewrite sublist_cons_r in Hl'. destruct Hl' as [?|(?&?&?)]; subst.
    + left. rewrite E. eauto using sublist_contains.
    + right. eauto using sublist_contains.
  * intros [?|(?&E&?)]; [|rewrite E]; by constructor.
Qed.
Lemma contains_cons_l x l k :
  x :: l `contains` k ↔ ∃ k', k ≡ₚ x :: k' ∧ l `contains` k'.
Proof.
  split.
  * rewrite contains_sublist_l. intros (l'&Hl'&E).
    rewrite sublist_cons_l in Hl'. destruct Hl' as (k1&k2&?&?); subst.
    exists (k1 ++ k2). split; eauto using contains_inserts_l, sublist_contains.
    by rewrite Permutation_middle.
  * intros (?&E&?). rewrite E. by constructor.
Qed.
Lemma contains_app_r l k1 k2 :
  l `contains` k1 ++ k2 ↔ ∃ l1 l2,
    l ≡ₚ l1 ++ l2 ∧ l1 `contains` k1 ∧ l2 `contains` k2.
Proof.
  split.
  * rewrite contains_sublist_r. intros (l'&E&Hl').
    rewrite sublist_app_r in Hl'. destruct Hl' as (l1&l2&?&?&?); subst.
    exists l1 l2. eauto using sublist_contains.
  * intros (?&?&E&?&?). rewrite E. eauto using contains_app.
Qed.
Lemma contains_app_l l1 l2 k :
  l1 ++ l2 `contains` k ↔ ∃ k1 k2,
    k ≡ₚ k1 ++ k2 ∧ l1 `contains` k1 ∧ l2 `contains` k2.
Proof.
  split.
  * rewrite contains_sublist_l. intros (l'&Hl'&E).
    rewrite sublist_app_l in Hl'. destruct Hl' as (k1&k2&?&?&?); subst.
    exists k1 k2. split. done. eauto using sublist_contains.
  * intros (?&?&E&?&?). rewrite E. eauto using contains_app.
Qed.
Lemma contains_app_inv_l l1 l2 k :
  k ++ l1 `contains` k ++ l2 → l1 `contains` l2.
Proof.
  induction k as [|y k IH]; simpl; [done |]. rewrite contains_cons_l.
  intros (?&E&?). apply Permutation_cons_inv in E. apply IH. by rewrite E.
Qed.
Lemma contains_app_inv_r l1 l2 k :
  l1 ++ k `contains` l2 ++ k → l1 `contains` l2.
Proof.
  revert l1 l2. induction k as [|y k IH]; intros l1 l2.
  { by rewrite !(right_id_L [] (++)). }
  intros. feed pose proof (IH (l1 ++ [y]) (l2 ++ [y])) as Hl12.
  { by rewrite <-!(associative_L (++)). }
  rewrite contains_app_l in Hl12. destruct Hl12 as (k1&k2&E1&?&Hk2).
  rewrite contains_cons_l in Hk2. destruct Hk2 as (k2'&E2&?).
  rewrite E2, (Permutation_cons_append k2'), (associative_L (++)) in E1.
  apply Permutation_app_inv_r in E1. rewrite E1. eauto using contains_inserts_r.
Qed.
Lemma contains_cons_middle x l k1 k2 :
  l `contains` k1 ++ k2 → x :: l `contains` k1 ++ x :: k2.
Proof. rewrite <-Permutation_middle. by apply contains_skip. Qed.
Lemma contains_app_middle l1 l2 k1 k2 :
  l2 `contains` k1 ++ k2 → l1 ++ l2 `contains` k1 ++ l1 ++ k2.
Proof.
  rewrite !(associative (++)), (commutative (++) k1 l1), <-(associative_L (++)).
  by apply contains_skips_l.
Qed.
Lemma contains_middle l k1 k2 : l `contains` k1 ++ l ++ k2.
Proof. by apply contains_inserts_l, contains_inserts_r. Qed.

Lemma Permutation_alt l1 l2 :
  l1 ≡ₚ l2 ↔ length l1 = length l2 ∧ l1 `contains` l2.
Proof.
  split. by intros Hl; rewrite Hl. intros [??]; auto using contains_Permutation.
Qed.

Section contains_dec.
  Context `{∀ x y, Decision (x = y)}.

  Lemma list_remove_Permutation l1 l2 k1 x :
    l1 ≡ₚ l2 → list_remove x l1 = Some k1 →
    ∃ k2, list_remove x l2 = Some k2 ∧ k1 ≡ₚ k2.
  Proof.
    intros Hl. revert k1. induction Hl
      as [|y l1 l2 ? IH|y1 y2 l|l1 l2 l3 ? IH1 ? IH2]; simpl; intros k1 Hk1.
    * done.
    * case_decide; simplify_equality; eauto.
      destruct (list_remove x l1) as [l|] eqn:?; simplify_equality.
      destruct (IH l) as (?&?&?); simplify_option_equality; eauto.
    * repeat case_decide; simplify_option_equality;
        eauto using Permutation_swap.
    * destruct (IH1 k1) as (k2&?&?); trivial.
      destruct (IH2 k2) as (k3&?&?); trivial.
      exists k3. split; eauto. by transitivity k2.
  Qed.

  Lemma list_remove_Some l k x : list_remove x l = Some k → l ≡ₚ x :: k.
  Proof.
    revert k. induction l as [|y l IH]; simpl; intros k ?; [done |].
    case_decide; simplify_option_equality; [done|].
    by rewrite Permutation_swap, <-IH.
  Qed.
  Lemma list_remove_Some_inv l k x :
    l ≡ₚ x :: k → ∃ k', list_remove x l = Some k' ∧ k ≡ₚ k'.
  Proof.
    intros. destruct (list_remove_Permutation (x :: k) l k x) as (k'&?&?).
    * done.
    * simpl; by case_decide.
    * by exists k'.
  Qed.

  Lemma list_remove_list_contains l1 l2 :
    l1 `contains` l2 ↔ is_Some (list_remove_list l1 l2).
  Proof.
    split.
    * revert l2. induction l1 as [|x l1 IH]; simpl.
      { intros l2 _. by exists l2. }
      intros l2. rewrite contains_cons_l. intros (k&Hk&?).
      destruct (list_remove_Some_inv l2 k x) as (k2&?&Hk2); trivial.
      simplify_option_equality. apply IH. by rewrite <-Hk2.
    * intros [k Hk]. revert l2 k Hk.
      induction l1 as [|x l1 IH]; simpl; intros l2 k.
      { intros. apply contains_nil_l. }
      destruct (list_remove x l2) as [k'|] eqn:?; intros; simplify_equality.
      rewrite contains_cons_l. eauto using list_remove_Some.
  Qed.

  Global Instance contains_dec l1 l2 : Decision (l1 `contains` l2).
  Proof.
   refine (cast_if (decide (is_Some (list_remove_list l1 l2))));
    abstract (rewrite list_remove_list_contains; tauto).
  Defined.
  Global Instance Permutation_dec l1 l2 : Decision (l1 ≡ₚ l2).
  Proof.
   refine (cast_if_and
    (decide (length l1 = length l2)) (decide (l1 `contains` l2)));
    abstract (rewrite Permutation_alt; tauto).
  Defined.
End contains_dec.
End general_properties.

(** ** Properties of the [same_length] predicate *)
Instance: ∀ A, Reflexive (@same_length A A).
Proof. intros A l. induction l; constructor; auto. Qed.
Instance: ∀ A, Symmetric (@same_length A A).
Proof. induction 1; constructor; auto. Qed.

Section same_length.
  Context {A B : Type}.
  Implicit Types l : list A. Implicit Types k : list B.

  Lemma same_length_length_1 l k : l `same_length` k → length l = length k.
  Proof. induction 1; simpl; auto. Qed.
  Lemma same_length_length_2 l k : length l = length k → l `same_length` k.
  Proof.
    revert k. induction l; intros [|??]; try discriminate;
      constructor; auto with arith.
  Qed.
  Lemma same_length_length l k : l `same_length` k ↔ length l = length k.
  Proof. split; auto using same_length_length_1, same_length_length_2. Qed.

  Lemma same_length_lookup l k i :
    l `same_length` k → is_Some (l !! i) → is_Some (k !! i).
  Proof. rewrite same_length_length. rewrite !lookup_lt_is_Some. lia. Qed.

  Lemma same_length_take l k n :
    l `same_length` k → take n l `same_length` take n k.
  Proof. intros Hl. revert n; induction Hl; intros [|n]; constructor; auto. Qed.
  Lemma same_length_drop l k n :
    l `same_length` k → drop n l `same_length` drop n k.
  Proof.
    intros Hl. revert n; induction Hl; intros [|]; simpl; try constructor; auto.
  Qed.
  Lemma same_length_resize l k x y n : resize n x l `same_length` resize n y k.
  Proof. apply same_length_length. by rewrite !resize_length. Qed.
End same_length.

(** ** Properties of the [Forall] and [Exists] predicate *)
Section Forall_Exists.
  Context {A} (P : A → Prop).

  Definition Forall_nil_2 := @Forall_nil A.
  Definition Forall_cons_2 := @Forall_cons A.

  Lemma Forall_forall l : Forall P l ↔ ∀ x, x ∈ l → P x.
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

  Global Instance Forall_proper:
    Proper (pointwise_relation _ (↔) ==> (=) ==> (↔)) (@Forall A).
  Proof. split; subst; induction 1; constructor; firstorder. Qed.

  Lemma Forall_iff l (Q : A → Prop) :
    (∀ x, P x ↔ Q x) → Forall P l ↔ Forall Q l.
  Proof. intros H. apply Forall_proper. red. apply H. done. Qed.

  Lemma Forall_delete l i : Forall P l → Forall P (delete i l).
  Proof. intros H. revert i. by induction H; intros [|i]; try constructor. Qed.
  Lemma Forall_lookup l : Forall P l ↔ ∀ i x, l !! i = Some x → P x.
  Proof.
    rewrite Forall_forall. setoid_rewrite elem_of_list_lookup. naive_solver.
  Qed.
  Lemma Forall_lookup_1 l i x : Forall P l → l !! i = Some x → P x.
  Proof. rewrite Forall_lookup. eauto. Qed.
  Lemma Forall_lookup_2 l : (∀ i x, l !! i = Some x → P x) → Forall P l.
  Proof. by rewrite Forall_lookup. Qed.

  Lemma Forall_alter f l i :
    Forall P l → (∀ x, l !! i = Some x → P x → P (f x)) →
    Forall P (alter f i l).
  Proof.
    intros Hl. revert i. induction Hl; simpl; intros [|i]; constructor; auto.
  Qed.

  Lemma Forall_replicate n x : P x → Forall P (replicate n x).
  Proof. induction n; simpl; constructor; auto. Qed.
  Lemma Forall_replicate_eq n (x : A) : Forall (=x) (replicate n x).
  Proof. induction n; simpl; constructor; auto. Qed.

  Lemma Forall_take n l : Forall P l → Forall P (take n l).
  Proof. intros Hl. revert n. induction Hl; intros [|?]; simpl; auto. Qed.
  Lemma Forall_drop n l : Forall P l → Forall P (drop n l).
  Proof. intros Hl. revert n. induction Hl; intros [|?]; simpl; auto. Qed.
  Lemma Forall_resize n x l : P x → Forall P l → Forall P (resize n x l).
  Proof.
    intros ? Hl. revert n.
    induction Hl; intros [|?]; simpl; auto using Forall_replicate.
  Qed.
  Lemma Exists_exists l : Exists P l ↔ ∃ x, x ∈ l ∧ P x.
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
    * intros [H|H]; [induction H | induction l1]; simpl; intuition.
  Qed.

  Global Instance Exists_proper:
    Proper (pointwise_relation _ (↔) ==> (=) ==> (↔)) (@Exists A).
  Proof. split; subst; (induction 1; [left|right]; firstorder auto). Qed.

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

Lemma Forall_swap {A B} (Q : A → B → Prop) l1 l2 :
  Forall (λ y, Forall (Q y) l1) l2 ↔ Forall (λ x, Forall (flip Q x) l2) l1.
Proof. repeat setoid_rewrite Forall_forall. simpl. split; eauto. Qed.

(** ** Properties of the [Forall2] predicate *)
Section Forall2.
  Context {A B} (P : A → B → Prop).

  Lemma Forall2_nil_inv_l k : Forall2 P [] k → k = [].
  Proof. by inversion 1. Qed.
  Lemma Forall2_nil_inv_r k : Forall2 P k [] → k = [].
  Proof. by inversion 1. Qed.
  Lemma Forall2_cons_inv l1 l2 x1 x2 :
    Forall2 P (x1 :: l1) (x2 :: l2) → P x1 x2 ∧ Forall2 P l1 l2.
  Proof. by inversion 1. Qed.
  Lemma Forall2_cons_inv_l l1 k x1 :
    Forall2 P (x1 :: l1) k → ∃ x2 l2, P x1 x2 ∧ Forall2 P l1 l2 ∧ k = x2 :: l2.
  Proof. inversion 1; subst; eauto. Qed.
  Lemma Forall2_cons_inv_r k l2 x2 :
    Forall2 P k (x2 :: l2) → ∃ x1 l1, P x1 x2 ∧ Forall2 P l1 l2 ∧ k = x1 :: l1.
  Proof. inversion 1; subst; eauto. Qed.
  Lemma Forall2_cons_nil_inv l1 x1 : Forall2 P (x1 :: l1) [] → False.
  Proof. by inversion 1. Qed.
  Lemma Forall2_nil_cons_inv l2 x2 : Forall2 P [] (x2 :: l2) → False.
  Proof. by inversion 1. Qed.
  Lemma Forall2_app_inv l1 l2 k1 k2 :
    l1 `same_length` k1 →
    Forall2 P (l1 ++ l2) (k1 ++ k2) → Forall2 P l1 k1 ∧ Forall2 P l2 k2.
  Proof. induction 1. done. inversion 1; naive_solver. Qed.
  Lemma Forall2_app_inv_l l1 l2 k :
    Forall2 P (l1 ++ l2) k →
      ∃ k1 k2, Forall2 P l1 k1 ∧ Forall2 P l2 k2 ∧ k = k1 ++ k2.
  Proof. revert k. induction l1; simpl; inversion 1; naive_solver. Qed.
  Lemma Forall2_app_inv_r l k1 k2 :
    Forall2 P l (k1 ++ k2) →
      ∃ l1 l2, Forall2 P l1 k1 ∧ Forall2 P l2 k2 ∧ l = l1 ++ l2.
  Proof. revert l. induction k1; simpl; inversion 1; naive_solver. Qed.

  Lemma Forall2_length l1 l2 : Forall2 P l1 l2 → length l1 = length l2.
  Proof. induction 1; simpl; auto. Qed.
  Lemma Forall2_same_length l1 l2 : Forall2 P l1 l2 → l1 `same_length` l2.
  Proof. induction 1; constructor; auto. Qed.

  Lemma Forall2_flip l1 l2 : Forall2 P l1 l2 ↔ Forall2 (flip P) l2 l1.
  Proof. split; induction 1; constructor; auto. Qed.
  Lemma Forall2_impl (Q : A → B → Prop) l1 l2 :
    Forall2 P l1 l2 → (∀ x y, P x y → Q x y) → Forall2 Q l1 l2.
  Proof. intros H ?. induction H; auto. Defined.
  Lemma Forall2_unique l k1 k2 :
    Forall2 P l k1 →  Forall2 P l k2 →
    (∀ x y1 y2, P x y1 → P x y2 → y1 = y2) → k1 = k2.
  Proof.
    intros H. revert k2. induction H; inversion_clear 1; intros; f_equal; eauto.
  Qed.

  Lemma Forall2_Forall_l (Q : A → Prop) l k :
    Forall2 P l k → Forall (λ y, ∀ x, P x y → Q x) k → Forall Q l.
  Proof. induction 1; inversion_clear 1; eauto. Qed.
  Lemma Forall2_Forall_r (Q : B → Prop) l k :
    Forall2 P l k → Forall (λ x, ∀ y, P x y → Q y) l → Forall Q k.
  Proof. induction 1; inversion_clear 1; eauto. Qed.

  Lemma Forall2_lookup_lr l1 l2 i x y :
    Forall2 P l1 l2 → l1 !! i = Some x → l2 !! i = Some y → P x y.
  Proof.
    intros H. revert i. induction H; [done|].
    intros [|?] ??; simpl in *; simplify_equality; eauto.
  Qed.
  Lemma Forall2_lookup_l l1 l2 i x :
    Forall2 P l1 l2 → l1 !! i = Some x → ∃ y, l2 !! i = Some y ∧ P x y.
  Proof.
    intros H. revert i. induction H; [done|].
    intros [|?] ?; simpl in *; simplify_equality; eauto.
  Qed.
  Lemma Forall2_lookup_r l1 l2 i y :
    Forall2 P l1 l2 → l2 !! i = Some y → ∃ x, l1 !! i = Some x ∧ P x y.
  Proof.
    intros H. revert i. induction H; [done|].
    intros [|?] ?; simpl in *; simplify_equality; eauto.
  Qed.
  Lemma Forall2_lookup_2 l1 l2 :
    l1 `same_length` l2 →
    (∀ i x y, l1 !! i = Some x → l2 !! i = Some y → P x y) → Forall2 P l1 l2.
  Proof.
    eauto using Forall2_same_length, Forall2_lookup_lr.
    intros Hl Hlookup. induction Hl as [|????? IH]; constructor.
    * by apply (Hlookup 0).
    * apply IH. intros i. apply (Hlookup (S i)).
  Qed.
  Lemma Forall2_lookup l1 l2 :
    Forall2 P l1 l2 ↔ l1 `same_length` l2 ∧
      (∀ i x y, l1 !! i = Some x → l2 !! i = Some y → P x y).
  Proof.
    split.
    * eauto using Forall2_same_length, Forall2_lookup_lr.
    * intros [??]; eauto using Forall2_lookup_2.
  Qed.
  Lemma Forall2_alter_l f l1 l2 i :
    Forall2 P l1 l2 → (∀ x1 x2,
      l1 !! i = Some x1 → l2 !! i = Some x2 → P x1 x2 → P (f x1) x2) →
    Forall2 P (alter f i l1) l2.
  Proof.
    intros Hl. revert i. induction Hl; simpl; intros [|i]; constructor; auto.
  Qed.
  Lemma Forall2_alter_r f l1 l2 i :
    Forall2 P l1 l2 → (∀ x1 x2,
      l1 !! i = Some x1 → l2 !! i = Some x2 → P x1 x2 → P x1 (f x2)) →
    Forall2 P l1 (alter f i l2).
  Proof.
    intros Hl. revert i. induction Hl; simpl; intros [|i]; constructor; auto.
  Qed.
  Lemma Forall2_alter f g l1 l2 i :
    Forall2 P l1 l2 → (∀ x1 x2,
      l1 !! i = Some x1 → l2 !! i = Some x2 → P x1 x2 → P (f x1) (g x2)) →
    Forall2 P (alter f i l1) (alter g i l2).
  Proof.
    intros Hl. revert i. induction Hl; simpl; intros [|i]; constructor; auto.
  Qed.
  Lemma Forall2_delete l1 l2 i :
    Forall2 P l1 l2 → Forall2 P (delete i l1) (delete i l2).
  Proof.
    intros Hl12. revert i. induction Hl12; intros [|i]; simpl; intuition.
  Qed.
  Lemma Forall2_replicate_l l n x :
    Forall (P x) l → length l = n → Forall2 P (replicate n x) l.
  Proof.
    intros Hl. revert n.
    induction Hl; intros [|?] ?; simplify_equality; constructor; auto.
  Qed.
  Lemma Forall2_replicate_r l n x :
    Forall (flip P x) l → length l = n → Forall2 P l (replicate n x).
  Proof.
    intros Hl. revert n.
    induction Hl; intros [|?] ?; simplify_equality; constructor; auto.
  Qed.
  Lemma Forall2_replicate n x1 x2 :
    P x1 x2 → Forall2 P (replicate n x1) (replicate n x2).
  Proof. induction n; simpl; constructor; auto. Qed.
  Lemma Forall2_take l1 l2 n :
    Forall2 P l1 l2 → Forall2 P (take n l1) (take n l2).
  Proof. intros Hl1l2. revert n. induction Hl1l2; intros [|?]; simpl; auto. Qed.
  Lemma Forall2_drop l1 l2 n :
    Forall2 P l1 l2 → Forall2 P (drop n l1) (drop n l2).
  Proof. intros Hl1l2. revert n. induction Hl1l2; intros [|?]; simpl; auto. Qed.
  Lemma Forall2_resize l1 l2 x1 x2 n :
    P x1 x2 → Forall2 P l1 l2 → Forall2 P (resize n x1 l1) (resize n x2 l2).
  Proof.
    intros. rewrite !resize_spec, (Forall2_length l1 l2) by done.
    auto using Forall2_app, Forall2_take, Forall2_replicate.
  Qed.

  Lemma Forall2_resize_ge_l l1 l2 x1 x2 n m :
    P x1 x2 → Forall (flip P x2) l1 → n ≤ m →
    Forall2 P (resize n x1 l1) l2 → Forall2 P (resize m x1 l1) (resize m x2 l2).
  Proof.
    intros. assert (n = length l2).
    { by rewrite <-(Forall2_length (resize n x1 l1) l2), resize_length. }
    rewrite (le_plus_minus n m) by done. subst.
    rewrite !resize_plus, resize_all, drop_all, resize_nil.
    apply Forall2_app; [done |].
    apply Forall2_replicate_r; [| by rewrite resize_length].
    eauto using Forall_resize, Forall_drop.
  Qed.
  Lemma Forall2_resize_ge_r l1 l2 x1 x2 n m :
    P x1 x2 → Forall (P x1) l2 → n ≤ m →
    Forall2 P l1 (resize n x2 l2) → Forall2 P (resize m x1 l1) (resize m x2 l2).
  Proof.
    intros. assert (n = length l1).
    { by rewrite (Forall2_length l1 (resize n x2 l2)), resize_length. }
    rewrite (le_plus_minus n m) by done. subst.
    rewrite !resize_plus, resize_all, drop_all, resize_nil.
    apply Forall2_app; [done |].
    apply Forall2_replicate_l; [| by rewrite resize_length].
    eauto using Forall_resize, Forall_drop.
  Qed.

  Lemma Forall2_transitive {C} (Q : B → C → Prop) (R : A → C → Prop) l1 l2 l3 :
    (∀ x1 x2 x3, P x1 x2 → Q x2 x3 → R x1 x3) →
    Forall2 P l1 l2 → Forall2 Q l2 l3 → Forall2 R l1 l3.
  Proof.
    intros ? Hl1l2. revert l3. induction Hl1l2; inversion_clear 1; eauto.
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

  Global Instance: Reflexive R → Reflexive (Forall2 R).
  Proof. intros ? l. induction l; by constructor. Qed.
  Global Instance: Symmetric R → Symmetric (Forall2 R).
  Proof. intros. induction 1; constructor; auto. Qed.
  Global Instance: Transitive R → Transitive (Forall2 R).
  Proof. intros ????. apply Forall2_transitive. apply transitivity. Qed.
  Global Instance: Equivalence R → Equivalence (Forall2 R).
  Proof. split; apply _. Qed.
  Global Instance: PreOrder R → PreOrder (Forall2 R).
  Proof. split; apply _. Qed.
  Global Instance: AntiSymmetric (=) R → AntiSymmetric (=) (Forall2 R).
  Proof. induction 2; inversion_clear 1; f_equal; auto. Qed.

  Global Instance: Proper (R ==> Forall2 R ==> Forall2 R) (::).
  Proof. by constructor. Qed.
  Global Instance: Proper (Forall2 R ==> Forall2 R ==> Forall2 R) (++).
  Proof. repeat intro. eauto using Forall2_app. Qed.
  Global Instance: Proper (Forall2 R ==> Forall2 R) (delete i).
  Proof. repeat intro. eauto using Forall2_delete. Qed.
  Global Instance: Proper (R ==> Forall2 R) (replicate n).
  Proof. repeat intro. eauto using Forall2_replicate. Qed.
  Global Instance: Proper (Forall2 R ==> Forall2 R) (take n).
  Proof. repeat intro. eauto using Forall2_take. Qed.
  Global Instance: Proper (Forall2 R ==> Forall2 R) (drop n).
  Proof. repeat intro. eauto using Forall2_drop. Qed.
  Global Instance: Proper (R ==> Forall2 R ==> Forall2 R) (resize n).
  Proof. repeat intro. eauto using Forall2_resize. Qed.
  Global Instance: Proper ((=) ==> R ==> Forall2 R ==> Forall2 R) insert.
  Proof. repeat intro. subst. apply Forall2_alter; auto. Qed.
End Forall2_order.

(** * Properties of the monadic operations *)
Section fmap.
  Context {A B : Type} (f : A → B).

  Lemma list_fmap_compose {C} (g : B → C) l : g ∘ f <$> l = g <$> f <$> l.
  Proof. induction l; simpl; f_equal; auto. Qed.

  Lemma list_fmap_ext (g : A → B) (l : list A) :
    (∀ x, f x = g x) → fmap f l = fmap g l.
  Proof. intro. induction l; simpl; f_equal; auto. Qed.

  Global Instance: Injective (=) (=) f → Injective (=) (=) (fmap f).
  Proof.
    intros ? l1. induction l1 as [|x l1 IH].
    * by intros [|??].
    * intros [|??]; simpl; intros; f_equal; simplify_equality; auto.
  Qed.
  Lemma fmap_app l1 l2 : f <$> l1 ++ l2 = (f <$> l1) ++ (f <$> l2).
  Proof. induction l1; simpl; by f_equal. Qed.

  Lemma fmap_nil_inv k :  f <$> k = [] → k = [].
  Proof. by destruct k. Qed.
  Lemma fmap_cons_inv y l k :
    f <$> l = y :: k → ∃ x l', y = f x ∧ k = f <$> l' ∧ l = x :: l'.
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
    induction l; simpl; [done |]. by rewrite !reverse_cons, fmap_app, IHl.
  Qed.
  Lemma fmap_replicate n x :  f <$> replicate n x = replicate n (f x).
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
    Forall (λ x, f (g x) = h (f x)) l → f <$> alter g i l = alter h i (f <$> l).
  Proof.
    intros Hl. revert i. induction Hl; intros [|i]; simpl; f_equal; auto.
  Qed.
  Lemma elem_of_list_fmap_1 l x : x ∈ l → f x ∈ f <$> l.
  Proof. induction 1; simpl; rewrite elem_of_cons; intuition. Qed.
  Lemma elem_of_list_fmap_1_alt l x y : x ∈ l → y = f x → y ∈ f <$> l.
  Proof. intros. subst. by apply elem_of_list_fmap_1. Qed.
  Lemma elem_of_list_fmap_2 l x : x ∈ f <$> l → ∃ y, x = f y ∧ y ∈ l.
  Proof.
    induction l as [|y l IH]; simpl; inversion_clear 1.
    + exists y. split; [done | by left].
    + destruct IH as [z [??]]. done. exists z. split; [done | by right].
  Qed.
  Lemma elem_of_list_fmap l x : x ∈ f <$> l ↔ ∃ y, x = f y ∧ y ∈  l.
  Proof.
    firstorder eauto using elem_of_list_fmap_1_alt, elem_of_list_fmap_2.
  Qed.

  Lemma NoDup_fmap_1 l : NoDup (f <$> l) → NoDup l.
  Proof.
    induction l; simpl; inversion_clear 1; constructor; auto.
    rewrite elem_of_list_fmap in *. naive_solver.
  Qed.
  Lemma NoDup_fmap_2 `{!Injective (=) (=) f} l : NoDup l → NoDup (f <$> l).
  Proof.
    induction 1; simpl; constructor; trivial. rewrite elem_of_list_fmap.
    intros [y [Hxy ?]]. apply (injective f) in Hxy. by subst.
  Qed.
  Lemma NoDup_fmap `{!Injective (=) (=) f} l : NoDup (f <$> l) ↔ NoDup l.
  Proof. split; auto using NoDup_fmap_1, NoDup_fmap_2. Qed.

  Global Instance fmap_sublist: Proper (sublist ==> sublist) (fmap f).
  Proof. induction 1; simpl; econstructor; eauto. Qed.
  Global Instance fmap_contains: Proper (contains ==> contains) (fmap f).
  Proof. induction 1; simpl; econstructor; eauto. Qed.
  Global Instance fmap_Permutation: Proper ((≡ₚ) ==> (≡ₚ)) (fmap f).
  Proof. induction 1; simpl; econstructor; eauto. Qed.

  Lemma Forall_fmap_ext (g : A → B) (l : list A) :
    Forall (λ x, f x = g x) l ↔ fmap f l = fmap g l.
  Proof.
    split.
    * induction 1; simpl; f_equal; auto.
    * induction l; simpl; constructor; simplify_equality; auto.
  Qed.
  Lemma Forall_fmap (P : B → Prop) l : Forall P (f <$> l) ↔ Forall (P ∘ f) l.
  Proof. split; induction l; inversion_clear 1; constructor; auto. Qed.

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
    Forall2 P (f <$> l1) (g <$> l2) → Forall2 (λ x1 x2, P (f x1) (g x2)) l1 l2.
  Proof. revert l2; induction l1; intros [|??]; inversion_clear 1; auto. Qed.
  Lemma Forall2_fmap_2 {C D} (g : C → D) (P : B → D → Prop) l1 l2 :
    Forall2 (λ x1 x2, P (f x1) (g x2)) l1 l2 → Forall2 P (f <$> l1) (g <$> l2).
  Proof. induction 1; simpl; auto. Qed.
  Lemma Forall2_fmap {C D} (g : C → D) (P : B → D → Prop) l1 l2 :
    Forall2 P (f <$> l1) (g <$> l2) ↔ Forall2 (λ x1 x2, P (f x1) (g x2)) l1 l2.
  Proof. split; auto using Forall2_fmap_1, Forall2_fmap_2. Qed.

  Lemma mapM_fmap_Some (g : B → option A) (l : list A) :
    (∀ x, g (f x) = Some x) → mapM g (f <$> l) = Some l.
  Proof. intros. by induction l; simpl; simplify_option_equality. Qed.
  Lemma mapM_fmap_Some_inv (g : B → option A) (l : list A) (k : list B) :
    (∀ x y, g y = Some x → y = f x) → mapM g k = Some l → k = f <$> l.
  Proof.
    intros Hgf. revert l; induction k as [|??]; intros [|??] ?;
      simplify_option_equality; f_equiv; eauto.
  Qed.
End fmap.

Lemma NoDup_fmap_fst {A B} (l : list (A * B)) :
  (∀ x y1 y2, (x,y1) ∈ l → (x,y2) ∈ l → y1 = y2) → NoDup l → NoDup (fst <$> l).
Proof.
  intros Hunique. induction 1 as [|[x1 y1] l Hin Hnodup IH]; simpl; constructor.
  * rewrite elem_of_list_fmap.
    intros [[x2 y2] [??]]; simpl in *; subst. destruct Hin.
    rewrite (Hunique x2 y1 y2); rewrite ?elem_of_cons; auto.
  * apply IH. intros.
    eapply Hunique; rewrite ?elem_of_cons; eauto.
Qed.

Section bind.
  Context {A B : Type} (f : A → list B).

  Global Instance mbind_sublist: Proper (sublist ==> sublist) (mbind f).
  Proof.
    induction 1; simpl; auto.
    * done.
    * by apply sublist_app.
    * by apply sublist_inserts_l.
  Qed.
  Global Instance mbind_contains: Proper (contains ==> contains) (mbind f).
  Proof.
    induction 1; simpl; auto.
    * done.
    * by apply contains_app.
    * by rewrite !(associative_L (++)), (commutative (++) (f _)).
    * by apply contains_inserts_l.
    * etransitivity; eauto.
  Qed.
  Global Instance mbind_Permutation: Proper ((≡ₚ) ==> (≡ₚ)) (mbind f).
  Proof.
    induction 1; simpl; auto.
    * by f_equiv.
    * by rewrite !(associative_L (++)), (commutative (++) (f _)).
    * etransitivity; eauto.
  Qed.

  Lemma bind_app (l1 l2 : list A) : (l1 ++ l2) ≫= f = (l1 ≫= f) ++ (l2 ≫= f).
  Proof.
    induction l1; simpl; [done|]. by rewrite <-(associative_L (++)), IHl1.
  Qed.
  Lemma elem_of_list_bind (x : B) (l : list A) :
    x ∈ l ≫= f ↔ ∃ y, x ∈ f y ∧ y ∈ l.
  Proof.
    split.
    * induction l as [|y l IH]; simpl; [inversion 1|].
      rewrite elem_of_app. intros [?|?].
      + exists y. split; [done | by left].
      + destruct IH as [z [??]]. done. exists z. split; [done | by right].
    * intros [y [Hx Hy]]. induction Hy; simpl; rewrite elem_of_app; intuition.
  Qed.

  Lemma Forall2_bind {C D} (g : C → list D) (P : B → D → Prop) l1 l2 :
    Forall2 (λ x1 x2, Forall2 P (f x1) (g x2)) l1 l2 →
    Forall2 P (l1 ≫= f) (l2 ≫= g).
  Proof. induction 1; simpl; auto using Forall2_app. Qed.
End bind.

Section ret_join.
  Context {A : Type}.

  Lemma list_join_bind (ls : list (list A)) : mjoin ls = ls ≫= id.
  Proof. induction ls; simpl; f_equal; auto. Qed.

  Global Instance mjoin_Permutation:
    Proper (@Permutation (list A) ==> (≡ₚ)) mjoin.
  Proof. intros ?? E. by rewrite !list_join_bind, E. Qed.

  Lemma elem_of_list_ret (x y : A) : x ∈ @mret list _ A y ↔ x = y.
  Proof. apply elem_of_list_singleton. Qed.
  Lemma elem_of_list_join (x : A) (ls : list (list A)) :
    x ∈ mjoin ls ↔ ∃ l, x ∈ l ∧ l ∈ ls.
  Proof. by rewrite list_join_bind, elem_of_list_bind. Qed.

  Lemma join_nil (ls : list (list A)) : mjoin ls = [] ↔ Forall (= []) ls.
  Proof.
    split.
    * by induction ls as [|[|??] ?]; constructor; auto.
    * by induction 1 as [|[|??] ?].
  Qed.
  Lemma join_nil_1 (ls : list (list A)) : mjoin ls = [] → Forall (= []) ls.
  Proof. by rewrite join_nil. Qed.
  Lemma join_nil_2 (ls : list (list A)) : Forall (= []) ls → mjoin ls = [].
  Proof. by rewrite join_nil. Qed.

  Lemma join_length (ls : list (list A)) :
    length (mjoin ls) = foldr (plus ∘ length) 0 ls.
  Proof. by induction ls; simpl; rewrite ?app_length; f_equal. Qed.
  Lemma join_length_same (ls : list (list A)) n :
    Forall (λ l, length l = n) ls → length (mjoin ls) = length ls * n.
  Proof. rewrite join_length. by induction 1; simpl; f_equal. Qed.

  Lemma lookup_join_same_length (ls : list (list A)) n i :
    n ≠ 0 → Forall (λ l, length l = n) ls →
    mjoin ls !! i = ls !! (i `div` n) ≫= (!! (i `mod` n)).
  Proof.
    intros Hn Hls. revert i. induction Hls as [|l ls ? Hls IH]; simpl; [done |].
    intros i. destruct (decide (i < n)) as [Hin|Hin].
    * rewrite <-(NPeano.Nat.div_unique i n 0 i) by lia.
      rewrite <-(NPeano.Nat.mod_unique i n 0 i) by lia.
      simpl. rewrite lookup_app_l; auto with lia.
    * replace i with ((i - n) + 1 * n) by lia.
      rewrite NPeano.Nat.div_add, NPeano.Nat.mod_add by done.
      replace (i - n + 1 * n) with i by lia.
      rewrite (plus_comm _ 1), lookup_app_r_alt, IH by lia. by subst.
  Qed.

  (* This should be provable using the previous lemma in a shorter way *)
  Lemma alter_join_same_length f (ls : list (list A)) n i :
    n ≠ 0 → Forall (λ l, length l = n) ls →
    alter f i (mjoin ls) = mjoin (alter (alter f (i `mod` n)) (i `div` n) ls).
  Proof.
    intros Hn Hls. revert i. induction Hls as [|l ls ? Hls IH]; simpl; [done |].
    intros i. destruct (decide (i < n)) as [Hin|Hin].
    * rewrite <-(NPeano.Nat.div_unique i n 0 i) by lia.
      rewrite <-(NPeano.Nat.mod_unique i n 0 i) by lia.
      simpl. rewrite alter_app_l; auto with lia.
    * replace i with ((i - n) + 1 * n) by lia.
      rewrite NPeano.Nat.div_add, NPeano.Nat.mod_add by done.
      replace (i - n + 1 * n) with i by lia.
      rewrite (plus_comm _ 1), alter_app_r_alt, IH by lia. by subst.
  Qed.
  Lemma insert_join_same_length (ls : list (list A)) n i x :
    n ≠ 0 → Forall (λ l, length l = n) ls →
    <[i:=x]>(mjoin ls) = mjoin (alter <[i `mod` n:=x]> (i `div` n) ls).
  Proof. apply alter_join_same_length. Qed.

  Lemma Forall2_join {B} (P : A → B → Prop) ls1 ls2 :
    Forall2 (Forall2 P) ls1 ls2 → Forall2 P (mjoin ls1) (mjoin ls2).
  Proof. induction 1; simpl; auto using Forall2_app. Qed.
End ret_join.

(** ** Properties of the [permutations] function *)
Section permutations.
  Context {A : Type}.
  Implicit Types x y z : A.
  Implicit Types l : list A.

  Lemma interleave_cons x l : x :: l ∈ interleave x l.
  Proof. destruct l; simpl; rewrite elem_of_cons; auto. Qed.
  Lemma interleave_Permutation x l l' : l' ∈ interleave x l → l' ≡ₚ x :: l.
  Proof.
    revert l'. induction l as [|y l IH]; intros l'; simpl.
    * rewrite elem_of_list_singleton. intros. by subst.
    * rewrite elem_of_cons, elem_of_list_fmap. intros [?|[? [? H]]]; subst.
      + by constructor.
      + rewrite (IH _ H). constructor.
  Qed.

  Lemma permutations_refl l : l ∈ permutations l.
  Proof.
    induction l; simpl.
    * by apply elem_of_list_singleton.
    * apply elem_of_list_bind. eauto using interleave_cons.
  Qed.
  Lemma permutations_skip x l l' :
    l ∈ permutations l' → x :: l ∈ permutations (x :: l').
  Proof.
    intros Hl. simpl. apply elem_of_list_bind. eauto using interleave_cons.
  Qed.
  Lemma permutations_swap x y l : y :: x :: l ∈ permutations (x :: y :: l).
  Proof.
    simpl. apply elem_of_list_bind. exists (y :: l). split; simpl.
    * destruct l; simpl; rewrite !elem_of_cons; auto.
    * apply elem_of_list_bind. simpl.
      eauto using interleave_cons, permutations_refl.
  Qed.
  Lemma permutations_nil l : l ∈ permutations [] ↔ l = [].
  Proof. simpl. by rewrite elem_of_list_singleton. Qed.

  Lemma interleave_interleave_toggle x1 x2 l1 l2 l3 :
    l1 ∈ interleave x1 l2 → l2 ∈ interleave x2 l3 → ∃ l4,
      l1 ∈ interleave x2 l4 ∧ l4 ∈ interleave x1 l3.
  Proof.
    revert l1 l2. induction l3 as [|y l3 IH]; intros l1 l2; simpl.
    { intros Hl1 Hl2.
      rewrite elem_of_list_singleton in Hl2. subst. simpl in Hl1.
      rewrite elem_of_cons, elem_of_list_singleton in Hl1. exists [x1]. simpl.
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
      + destruct (IH l1' l2') as [l4 [??]]; auto. exists (y :: l4). simpl.
        rewrite !elem_of_cons, !elem_of_list_fmap. naive_solver.
  Qed.
  Lemma permutations_interleave_toggle x l1 l2 l3 :
    l1 ∈ permutations l2 → l2 ∈ interleave x l3 → ∃ l4,
      l1 ∈ interleave x l4 ∧ l4 ∈ permutations l3.
  Proof.
    revert l1 l2. induction l3 as [|y l3 IH]; intros l1 l2; simpl.
    { intros Hl1 Hl2. eexists []. simpl.
      split; [| by rewrite elem_of_list_singleton].
      rewrite elem_of_list_singleton in Hl2. by rewrite Hl2 in Hl1. }
    rewrite elem_of_cons, elem_of_list_fmap.
    intros Hl1 [? | [l2' [? Hl2']]]; subst; simpl in *.
    * rewrite elem_of_list_bind in Hl1.
      destruct Hl1 as [l1' [??]]. by exists l1'.
    * rewrite elem_of_list_bind in Hl1. setoid_rewrite elem_of_list_bind.
      destruct Hl1 as [l1' [??]]. destruct (IH l1' l2') as (l1''&?&?); auto.
      destruct (interleave_interleave_toggle y x l1 l1' l1'') as (?&?&?); eauto.
  Qed.
  Lemma permutations_trans l1 l2 l3 :
    l1 ∈ permutations l2 → l2 ∈ permutations l3 → l1 ∈ permutations l3.
  Proof.
    revert l1 l2. induction l3 as [|x l3 IH]; intros l1 l2; simpl.
    * intros Hl1 Hl2. rewrite elem_of_list_singleton in Hl2.
      by rewrite Hl2 in Hl1.
    * rewrite !elem_of_list_bind. intros Hl1 [l2' [Hl2 Hl2']].
      destruct (permutations_interleave_toggle x l1 l2 l2') as [? [??]]; eauto.
  Qed.

  Lemma permutations_Permutation l l' : l' ∈ permutations l ↔ l ≡ₚ l'.
  Proof.
    split.
    * revert l'. induction l; simpl; intros l''.
      + rewrite elem_of_list_singleton. intros. subst. constructor.
      + rewrite elem_of_list_bind. intros [l' [Hl'' ?]].
        rewrite (interleave_Permutation _ _ _ Hl''). constructor; auto.
    * induction 1; eauto using permutations_refl,
        permutations_skip, permutations_swap, permutations_trans.
  Qed.
End permutations.

(** ** Properties of the folding functions *)
Definition foldr_app := @fold_right_app.

Lemma foldl_app {A B} (f : A → B → A) (l k : list B) (a : A) :
  foldl f a (l ++ k) = foldl f (foldl f a l) k.
Proof. revert a. induction l; simpl; auto. Qed.

Lemma foldr_permutation {A B} (R : relation B) `{!Equivalence R}
    (f : A → B → B) (b : B) `{!Proper ((=) ==> R ==> R) f}
    (Hf : ∀ a1 a2 b, R (f a1 (f a2 b)) (f a2 (f a1 b))) :
  Proper ((≡ₚ) ==> R) (foldr f b).
Proof.
  induction 1; simpl.
  * done.
  * by f_equiv.
  * apply Hf.
  * etransitivity; eauto.
Qed.

Lemma ifoldr_app {A B} (f : nat → B → A → A) (a : nat → A) (l1 l2 : list B) n :
  ifoldr f a n (l1 ++ l2) = ifoldr f (λ n, ifoldr f a n l2) n l1.
Proof. revert n a. induction l1; intros; simpl; f_equal; auto. Qed.

(** ** Properties of the [zip_with] and [zip] functions *)
Section zip_with.
  Context {A B C : Type} (f : A → B → C).

  Lemma zip_with_nil_inv l1 l2 :
    zip_with f l1 l2 = [] → l1 = [] ∨ l2 = [].
  Proof. destruct l1, l2; simpl; auto with congruence. Qed.
  Lemma zip_with_cons_inv y l1 l2 k :
    zip_with f l1 l2 = y :: k →
    ∃ x1 x2 l1' l2', y = f x1 x2 ∧ k = zip_with f l1' l2' ∧
      l1 = x1 :: l1' ∧ l2 = x2 :: l2'.
  Proof. intros. destruct l1, l2; simpl; simplify_equality; repeat eexists. Qed.
  Lemma zip_with_app_inv l1 l2 k' k'' :
    zip_with f l1 l2 = k' ++ k'' →
    ∃ l1' l1'' l2' l2'', k' = zip_with f l1' l2' ∧ k'' = zip_with f l1'' l2'' ∧
      l1 = l1' ++ l1'' ∧ l2 = l2' ++ l2''.
  Proof.
    revert l1 l2. induction k' as [|y k' IH]; simpl.
    * intros l1 l2 ?. by eexists [], l1, [], l2.
    * intros [|x1 l1] [|x2 l2] ?; simpl; simplify_equality.
      destruct (IH l1 l2) as (l1'&l1''&l2'&l2''&?&?&?&?); subst; [done |].
      by exists (x1 :: l1') l1'' (x2 :: l2') l2''.
  Qed.

  Lemma zip_with_inj l1 l2 k1 k2 :
    (∀ x1 x2 y1 y2, f x1 x2 = f y1 y2 → x1 = y1 ∧ x2 = y2) →
    l1 `same_length` l2 → k1 `same_length` k2 →
    zip_with f l1 l2 = zip_with f k1 k2 → l1 = k1 ∧ l2 = k2.
  Proof.
    intros ? Hl. revert k1 k2. induction Hl; intros ?? [] ?; simpl;
      simplify_equality; f_equal; naive_solver.
  Qed.

  Lemma zip_with_length l1 l2 :
    length l1 ≤ length l2 → length (zip_with f l1 l2) = length l1.
  Proof. revert l2. induction l1; intros [|??]; simpl; auto with lia. Qed.

  Lemma zip_with_fmap_fst_le (g : C → A) l1 l2 :
    (∀ x y, g (f x y) = x) → length l1 ≤ length l2 →
    g <$> zip_with f l1 l2 = l1.
  Proof.
    revert l2.
    induction l1; intros [|??] ??; simpl in *; f_equal; auto with lia.
  Qed.
  Lemma zip_with_fmap_snd_le (g : C → B) l1 l2 :
    (∀ x y, g (f x y) = y) → length l2 ≤ length l1 →
    g <$> zip_with f l1 l2 = l2.
  Proof.
    revert l1.
    induction l2; intros [|??] ??; simpl in *; f_equal; auto with lia.
  Qed.
  Lemma zip_with_fmap_fst (g : C → A) l1 l2 :
    (∀ x y, g (f x y) = x) → l1 `same_length` l2 → g <$> zip_with f l1 l2 = l1.
  Proof. induction 2; simpl; f_equal; auto. Qed.
  Lemma zip_with_fmap_snd (g : C → B) l1 l2 :
    (∀ x y, g (f x y) = y) → l1 `same_length` l2 → g <$> zip_with f l1 l2 = l2.
  Proof. induction 2; simpl; f_equal; auto. Qed.

  Lemma Forall_zip_with_fst (P : A → Prop) (Q : C → Prop) l1 l2 :
    Forall P l1 → Forall (λ y, ∀ x, P x → Q (f x y)) l2 →
    Forall Q (zip_with f l1 l2).
  Proof. intros Hl. revert l2. induction Hl; destruct 1; simpl in *; auto. Qed.
  Lemma Forall_zip_with_snd (P : B → Prop) (Q : C → Prop) l1 l2 :
    Forall (λ x, ∀ y, P y → Q (f x y)) l1 → Forall P l2 →
    Forall Q (zip_with f l1 l2).
  Proof. intros Hl. revert l2. induction Hl; destruct 1; simpl in *; auto. Qed.
End zip_with.

Section zip.
  Context {A B : Type}.
  Implicit Types l : list A.
  Implicit Types k : list B.

  Lemma zip_length l k : length l ≤ length k → length (zip l k) = length l.
  Proof. by apply zip_with_length. Qed.
  Lemma zip_fmap_fst_le l k : length l ≤ length k → fst <$> zip l k = l.
  Proof. by apply zip_with_fmap_fst_le. Qed.
  Lemma zip_fmap_snd l k : length k ≤ length l → snd <$> zip l k = k.
  Proof. by apply zip_with_fmap_snd_le. Qed.
  Lemma zip_fst l k : l `same_length` k → fst <$> zip l k = l.
  Proof. by apply zip_with_fmap_fst. Qed.
  Lemma zip_snd l k : l `same_length` k → snd <$> zip l k = k.
  Proof. by apply zip_with_fmap_snd. Qed.
End zip.

Lemma elem_of_zipped_map {A B} (f : list A → list A → A → B) l k x :
  x ∈ zipped_map f l k ↔
    ∃ k' k'' y, k = k' ++ [y] ++ k'' ∧ x = f (reverse k' ++ l) k'' y.
Proof.
  split.
  * revert l. induction k as [|z k IH]; simpl; intros l; inversion_clear 1.
    + by eexists [], k, z.
    + destruct (IH (z :: l)) as [k' [k'' [y [??]]]]; [done |]; subst.
      eexists (z :: k'), k'', y. split; [done |].
      by rewrite reverse_cons, <-(associative_L (++)).
  * intros [k' [k'' [y [??]]]]; subst.
    revert l. induction k' as [|z k' IH]; intros l; [by left|].
    right. by rewrite reverse_cons, <-!(associative_L (++)).
Qed.

Section zipped_list_ind.
  Context {A} (P : list A → list A → Prop).
  Context (Pnil : ∀ l, P l []) (Pcons : ∀ l k x, P (x :: l) k → P l (x :: k)).

  Fixpoint zipped_list_ind l k : P l k :=
    match k with
    | [] => Pnil _
    | x :: k => Pcons _ _ _ (zipped_list_ind (x :: l) k)
    end.
End zipped_list_ind.

Lemma zipped_Forall_app {A} (P : list A → list A → A → Prop) l k k' :
  zipped_Forall P l (k ++ k') → zipped_Forall P (reverse k ++ l) k'.
Proof.
  revert l. induction k as [|x k IH]; simpl; [done |].
  inversion_clear 1. rewrite reverse_cons, <-(associative_L (++)). by apply IH.
Qed.

(** * Relection over lists *)
(** We define a simple data structure [rlist] to capture a syntactic
representation of lists consisting of constants, applications and the nil list.
Note that we represent [(x ::)] as [rapp (rnode [x])]. For now, we abstract
over the type of constants, but later we use [nat]s and a list representing
a corresponding environment. *)
Inductive rlist (A : Type) :=
  | rnil : rlist A
  | rnode : A → rlist A
  | rapp : rlist A → rlist A → rlist A.
Arguments rnil {_}.
Arguments rnode {_} _.
Arguments rapp {_} _ _.

Module rlist.
Fixpoint to_list {A} (t : rlist A) : list A :=
  match t with
  | rnil => []
  | rnode l => [l]
  | rapp t1 t2 => to_list t1 ++ to_list t2
  end.

Notation env A := (list (list A)) (only parsing).
Definition eval {A} (E : env A) : rlist nat → list A :=
  fix go t :=
  match t with
  | rnil => []
  | rnode i => from_option [] (E !! i)
  | rapp t1 t2 => go t1 ++ go t2
  end.

(** A simple quoting mechanism using type classes. [QuoteLookup E1 E2 x i]
means: starting in environment [E1], look up the index [i] corresponding to the
constant [x]. In case [x] has a corresponding index [i] in [E1], the original
environment is given back as [E2]. Otherwise, the environment [E2] is extended
with a binding [i] for [x]. *)
Section quote_lookup.
  Context {A : Type}.
  Class QuoteLookup (E1 E2 : list A) (x : A) (i : nat) := {}.
  Global Instance quote_lookup_here E x : QuoteLookup (x :: E) (x :: E) x 0.
  Global Instance quote_lookup_end x : QuoteLookup [] [x] x 0.
  Global Instance quote_lookup_further E1 E2 x i y :
    QuoteLookup E1 E2 x i → QuoteLookup (y :: E1) (y :: E2) x (S i) | 1000.
End quote_lookup.

Section quote.
  Context {A : Type}.
  Class Quote (E1 E2 : env A) (l : list A) (t : rlist nat) := {}.
  Global Instance quote_nil: Quote E1 E1 [] rnil.
  Global Instance quote_node E1 E2 l i:
    QuoteLookup E1 E2 l i → Quote E1 E2 l (rnode i) | 1000.
  Global Instance quote_cons E1 E2 E3 x l i t :
    QuoteLookup E1 E2 [x] i →
    Quote E2 E3 l t → Quote E1 E3 (x :: l) (rapp (rnode i) t).
  Global Instance quote_app E1 E2 E3 l1 l2 t1 t2 :
    Quote E1 E2 l1 t1 → Quote E2 E3 l2 t2 → Quote E1 E3 (l1 ++ l2) (rapp t1 t2).
End quote.

Section eval.
  Context {A} (E : env A).

  Lemma eval_alt t : eval E t = to_list t ≫= from_option [] ∘ (E !!).
  Proof.
    induction t; simpl.
    * done.
    * by rewrite (right_id_L [] (++)).
    * rewrite bind_app. by f_equal.
  Qed.
  Lemma eval_eq t1 t2 : to_list t1 = to_list t2 → eval E t1 = eval E t2.
  Proof. intros Ht. by rewrite !eval_alt, Ht. Qed.
  Lemma eval_Permutation t1 t2 :
    to_list t1 ≡ₚ to_list t2 → eval E t1 ≡ₚ eval E t2.
  Proof. intros Ht. by rewrite !eval_alt, Ht. Qed.
  Lemma eval_contains t1 t2 :
    to_list t1 `contains` to_list t2 → eval E t1 `contains` eval E t2.
  Proof. intros Ht. by rewrite !eval_alt, Ht. Qed.
End eval.
End rlist.

(** * Tactics *)
Ltac quote_Permutation :=
  match goal with
  | |- ?l1 ≡ₚ ?l2 =>
    match type of (_ : rlist.Quote [] _ l1 _) with rlist.Quote _ ?E2 _ ?t1 =>
    match type of (_ : rlist.Quote E2 _ l2 _) with rlist.Quote _ ?E3 _ ?t2 =>
      change (rlist.eval E3 t1 ≡ₚ rlist.eval E3 t2)
    end end
  end.
Ltac solve_Permutation :=
  quote_Permutation; apply rlist.eval_Permutation;
  apply (bool_decide_unpack _); by vm_compute.

Ltac quote_contains :=
  match goal with
  | |- ?l1 `contains` ?l2 =>
    match type of (_ : rlist.Quote [] _ l1 _) with rlist.Quote _ ?E2 _ ?t1 =>
    match type of (_ : rlist.Quote E2 _ l2 _) with rlist.Quote _ ?E3 _ ?t2 =>
      change (rlist.eval E3 t1 `contains` rlist.eval E3 t2)
    end end
  end.
Ltac solve_contains :=
  quote_contains; apply rlist.eval_contains;
  apply (bool_decide_unpack _); by vm_compute.

Ltac decompose_elem_of_list := repeat
  match goal with
  | H : ?x ∈ [] |- _ => by destruct (not_elem_of_nil x)
  | H : _ ∈ _ :: _ |- _ => apply elem_of_cons in H; destruct H
  | H : _ ∈ _ ++ _ |- _ => apply elem_of_app in H; destruct H
  end.

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
Ltac simplify_zip_equality := repeat
  match goal with
  | _ => progress simplify_equality
  | H : zip_with _ _ _ = [] |- _ => apply zip_with_nil_inv in H; destruct H
  | H : [] = zip_with _ _ _ |- _ => symmetry in H
  | H : zip_with _ _ _ = _ :: _ |- _ =>
    apply zip_with_cons_inv in H; destruct H as (?&?&?&?&?&?&?&?)
  | H : _ :: _ = zip_with _ _ _ |- _ => symmetry in H
  | H : zip_with _ _ _ = _ ++ _ |- _ =>
    apply zip_with_app_inv in H; destruct H as (?&?&?&?&?&?&?&?)
  | H : _ ++ _ = zip_with _ _ _ |- _ => symmetry in H
  end.

Ltac decompose_Forall_hyps := repeat
  match goal with
  | H : Forall _ [] |- _ => clear H
  | H : Forall _ (_ :: _) |- _ => rewrite Forall_cons in H; destruct H
  | H : Forall _ (_ ++ _) |- _ => rewrite Forall_app in H; destruct H
  | H : Forall _ (_ <$> _) |- _ => rewrite Forall_fmap in H
  | H : Forall _ ?l, H' : length ?l ≠ 0 |- _ => is_var l; destruct H; [done|]
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
  | H : Forall2 _ (_ ++ _) (_ ++ _) |- _ =>
    destruct (Forall2_app_inv _ _ _ _ _ H); [eauto using Forall2_same_length |]
  | H : Forall2 _ (_ ++ _) ?l |- _ =>
    apply Forall2_app_inv_l in H; destruct H as (? & ? & ? & ? & ?); subst l
  | H : Forall2 _ ?l (_ ++ _) |- _ =>
    apply Forall2_app_inv_r in H; destruct H as (? & ? & ? & ? & ?); subst l
  | H : Forall ?P ?l, H1 : ?l !! _ = Some ?x |- _ =>
    unless (P x) by done;
    let E := fresh in
    assert (P x) as E by (apply (Forall_lookup_1 P _ _ _ H H1)); lazy beta in E
  | H : Forall2 ?P ?l1 ?l2 |- _ =>
    lazymatch goal with
    | H1 : l1 !! ?i = Some ?x, H2 : l2 !! ?i = Some ?y |- _ =>
      unless (P x y) by done;
      let E := fresh in
      assert (P x y) as E by (apply (Forall2_lookup_lr P _ _ _ _ _ H H1 H2));
      lazy beta in E
    | H1 : l1 !! _ = Some ?x |- _ =>
      destruct (Forall2_lookup_l P _ _ _ _ H H1) as (?&?&?)
    | H2 : l2 !! _ = Some ?y |- _ =>
      destruct (Forall2_lookup_r P _ _ _ _ H H2) as (?&?&?)
    end
  end.
Ltac decompose_Forall := repeat
  match goal with
  | |- Forall _ _ => by apply Forall_true
  | |- Forall _ [] => constructor
  | |- Forall _ (_ :: _) => constructor
  | |- Forall _ (_ ++ _) => apply Forall_app
  | |- Forall _ (_ <$> _) => apply Forall_fmap
  | |- Forall2 _ _ _ => apply Forall2_Forall
  | |- Forall2 _ [] [] => constructor
  | |- Forall2 _ (_ :: _) (_ :: _) => constructor
  | |- Forall2 _ (_ ++ _) (_ ++ _) => first
    [ apply Forall2_app; [by decompose_Forall |]
    | apply Forall2_app; [| by decompose_Forall]]
  | |- Forall2 _ (_ <$> _) _ => apply Forall2_fmap_l
  | |- Forall2 _ _ (_ <$> _) => apply Forall2_fmap_r
  | _ => progress decompose_Forall_hyps
  | |- Forall _ _ =>
    apply Forall_lookup_2; intros ???; progress decompose_Forall_hyps
  | |- Forall2 _ _ _ =>
    apply Forall2_lookup_2; [by eauto using Forall2_same_length|];
    intros ?????; progress decompose_Forall_hyps
  end.

(** The [simplify_suffix_of] tactic removes [suffix_of] hypotheses that are
tautologies, and simplifies [suffix_of] hypotheses involving [(::)] and
[(++)]. *)
Ltac simplify_suffix_of := repeat
  match goal with
  | H : suffix_of (_ :: _) _ |- _ => destruct (suffix_of_cons_not _ _ H)
  | H : suffix_of (_ :: _) [] |- _ => apply suffix_of_nil_inv in H
  | H : suffix_of (_ ++ _) (_ ++ _) |- _ => apply suffix_of_app_inv in H
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
Ltac solve_suffix_of := by intuition (repeat
  match goal with
  | _ => done
  | _ => progress simplify_suffix_of
  | |- suffix_of [] _ => apply suffix_of_nil
  | |- suffix_of _ _ => reflexivity
  | |- suffix_of _ (_ :: _) => apply suffix_of_cons_r
  | |- suffix_of _ (_ ++ _) => apply suffix_of_app_r
  | H : suffix_of _ _ → False |- _ => destruct H
  end).
Hint Extern 0 (PropHolds (suffix_of _ _)) =>
  unfold PropHolds; solve_suffix_of : typeclass_instances.
