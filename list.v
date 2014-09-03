(* Copyright (c) 2012-2014, Robbert Krebbers. *)
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
  fix go i l {struct l} : option A := let _ : Lookup _ _ _ := @go in
  match l with
  | [] => None | x :: l => match i with 0 => Some x | S i => l !! i end
  end.

(** The operation [alter f i l] applies the function [f] to the [i]th element
of [l]. In case [i] is out of bounds, the list is returned unchanged. *)
Instance list_alter {A} : Alter nat A (list A) := λ f,
  fix go i l {struct l} :=
  match l with
  | [] => []
  | x :: l => match i with 0 => f x :: l | S i => x :: go i l end
  end.

(** The operation [<[i:=x]> l] overwrites the element at position [i] with the
value [x]. In case [i] is out of bounds, the list is returned unchanged. *)
Instance list_insert {A} : Insert nat A (list A) :=
  fix go i y l {struct l} := let _ : Insert _ _ _ := @go in
  match l with
  | [] => []
  | x :: l => match i with 0 => y :: l | S i => x :: <[i:=y]>l end
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

(** The function [option_list o] converts an element [Some x] into the
singleton list [[x]], and [None] into the empty list [[]]. *)
Definition option_list {A} : option A → list A := option_rect _ (λ x, [x]) [].
Definition list_singleton {A} (l : list A) : option A :=
  match l with [x] => Some x | _ => None end.

(** The function [filter P l] returns the list of elements of [l] that
satisfies [P]. The order remains unchanged. *)
Instance list_filter {A} : Filter A (list A) :=
  fix go P _ l := let _ : Filter _ _ := @go in
  match l with
  | [] => []
  | x :: l => if decide (P x) then x :: filter P l else filter P l
  end.

(** The function [list_find P l] returns the first index [i] whose element
satisfies the predicate [P]. *)
Definition list_find {A} P `{∀ x, Decision (P x)} : list A → option nat :=
  fix go l :=
  match l with
  | [] => None | x :: l => if decide (P x) then Some 0 else S <$> go l
  end.

(** The function [replicate n x] generates a list with length [n] of elements
with value [x]. *)
Fixpoint replicate {A} (n : nat) (x : A) : list A :=
  match n with 0 => [] | S n => x :: replicate n x end.

(** The function [reverse l] returns the elements of [l] in reverse order. *)
Definition reverse {A} (l : list A) : list A := rev_append l [].

(** The function [last l] returns the last element of the list [l], or [None]
if the list [l] is empty. *)
Fixpoint last {A} (l : list A) : option A :=
  match l with [] => None | [x] => Some x | _ :: l => last l end.

(** The function [resize n y l] takes the first [n] elements of [l] in case
[length l ≤ n], and otherwise appends elements with value [x] to [l] to obtain
a list of length [n]. *)
Fixpoint resize {A} (n : nat) (y : A) (l : list A) : list A :=
  match l with
  | [] => replicate n y
  | x :: l => match n with 0 => [] | S n => x :: resize n y l end
  end.
Arguments resize {_} !_ _ !_.

(** The function [reshape k l] transforms [l] into a list of lists whose sizes
are specified by [k]. In case [l] is too short, the resulting list will be
padded with empty lists. In case [l] is too long, it will be truncated. *)
Fixpoint reshape {A} (szs : list nat) (l : list A) : list (list A) :=
  match szs with
  | [] => [] | sz :: szs => take sz l :: reshape szs (drop sz l)
  end.

Definition sublist_lookup {A} (i n : nat) (l : list A) : option (list A) :=
  guard (i + n ≤ length l); Some (take n (drop i l)).
Definition sublist_alter {A} (f : list A → list A)
    (i n : nat) (l : list A) : list A :=
  take i l ++ f (take n (drop i l)) ++ drop (i + n) l.

(** Functions to fold over a list. We redefine [foldl] with the arguments in
the same order as in Haskell. *)
Notation foldr := fold_right.
Definition foldl {A B} (f : A → B → A) : A → list B → A :=
  fix go a l := match l with [] => a | x :: l => go (f a x) l end.

(** The monadic operations. *)
Instance list_ret: MRet list := λ A x, x :: @nil A.
Instance list_fmap : FMap list := λ A B f,
  fix go (l : list A) := match l with [] => [] | x :: l => f x :: go l end.
Instance list_omap : OMap list := λ A B f,
  fix go (l : list A) :=
  match l with
  | [] => []
  | x :: l => match f x with Some y => y :: go l | None => go l end
  end.
Instance list_bind : MBind list := λ A B f,
  fix go (l : list A) := match l with [] => [] | x :: l => f x ++ go l end.
Instance list_join: MJoin list :=
  fix go A (ls : list (list A)) : list A :=
  match ls with [] => [] | l :: ls => l ++ @mjoin _ go _ ls end.
Definition mapM `{MBind M, MRet M} {A B} (f : A → M B) : list A → M (list B) :=
  fix go l :=
  match l with [] => mret [] | x :: l => y ← f x; k ← go l; mret (y :: k) end.

(** We define stronger variants of map and fold that allow the mapped
function to use the index of the elements. *)
Definition imap_go {A B} (f : nat → A → B) : nat → list A → list B :=
  fix go (n : nat) (l : list A) :=
  match l with [] => [] | x :: l => f n x :: go (S n) l end.
Definition imap {A B} (f : nat → A → B) : list A → list B := imap_go f 0.
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

(** The function [mask f βs l] applies the function [f] to elements in [l] at
positions that are [true] in [βs]. *)
Fixpoint mask {A} (f : A → A) (βs : list bool) (l : list A) : list A :=
  match βs, l with
  | β :: βs, x :: l => (if β then f x else x) :: mask f βs l
  | _, _ => l
  end.

(** The function [permutations l] yields all permutations of [l]. *)
Fixpoint interleave {A} (x : A) (l : list A) : list (list A) :=
  match l with
  | [] => [[x]]| y :: l => (x :: y :: l) :: ((y ::) <$> interleave x l)
  end.
Fixpoint permutations {A} (l : list A) : list (list A) :=
  match l with [] => [[]] | x :: l => permutations l ≫= interleave x end.

(** The predicate [suffix_of] holds if the first list is a suffix of the second.
The predicate [prefix_of] holds if the first list is a prefix of the second. *)
Definition suffix_of {A} : relation (list A) := λ l1 l2, ∃ k, l2 = k ++ l1.
Definition prefix_of {A} : relation (list A) := λ l1 l2, ∃ k, l2 = l1 ++ k.
Infix "`suffix_of`" := suffix_of (at level 70) : C_scope.
Infix "`prefix_of`" := prefix_of (at level 70) : C_scope.
Hint Extern 0 (?x `prefix_of` ?y) => reflexivity.
Hint Extern 0 (?x `suffix_of` ?y) => reflexivity.

Section prefix_suffix_ops.
  Context `{∀ x y : A, Decision (x = y)}.
  Definition max_prefix_of : list A → list A → list A * list A * list A :=
    fix go l1 l2 :=
    match l1, l2 with
    | [], l2 => ([], l2, [])
    | l1, [] => (l1, [], [])
    | x1 :: l1, x2 :: l2 =>
      if decide_rel (=) x1 x2
      then prod_map id (x1 ::) (go l1 l2) else (x1 :: l1, x2 :: l2, [])
    end.
  Definition max_suffix_of (l1 l2 : list A) : list A * list A * list A :=
    match max_prefix_of (reverse l1) (reverse l2) with
    | (k1, k2, k3) => (reverse k1, reverse k2, reverse k3)
    end.
  Definition strip_prefix (l1 l2 : list A) := (max_prefix_of l1 l2).1.2.
  Definition strip_suffix (l1 l2 : list A) := (max_suffix_of l1 l2).1.2.
End prefix_suffix_ops.

(** A list [l1] is a sublist of [l2] if [l2] is obtained by removing elements
from [l1] without changing the order. *)
Inductive sublist {A} : relation (list A) :=
  | sublist_nil : sublist [] []
  | sublist_skip x l1 l2 : sublist l1 l2 → sublist (x :: l1) (x :: l2)
  | sublist_cons x l1 l2 : sublist l1 l2 → sublist l1 (x :: l2).
Infix "`sublist`" := sublist (at level 70) : C_scope.
Hint Extern 0 (?x `sublist` ?y) => reflexivity.

(** A list [l2] contains a list [l1] if [l2] is obtained by removing elements
from [l1] while possiblity changing the order. *)
Inductive contains {A} : relation (list A) :=
  | contains_nil : contains [] []
  | contains_skip x l1 l2 : contains l1 l2 → contains (x :: l1) (x :: l2)
  | contains_swap x y l : contains (y :: x :: l) (x :: y :: l)
  | contains_cons x l1 l2 : contains l1 l2 → contains l1 (x :: l2)
  | contains_trans l1 l2 l3 : contains l1 l2 → contains l2 l3 → contains l1 l3.
Infix "`contains`" := contains (at level 70) : C_scope.
Hint Extern 0 (?x `contains` ?y) => reflexivity.

Section contains_dec_help.
  Context {A} {dec : ∀ x y : A, Decision (x = y)}.
  Fixpoint list_remove (x : A) (l : list A) : option (list A) :=
    match l with
    | [] => None
    | y :: l => if decide (x = y) then Some l else (y ::) <$> list_remove x l
    end.
  Fixpoint list_remove_list (k : list A) (l : list A) : option (list A) :=
    match k with
    | [] => Some l | x :: k => list_remove x l ≫= list_remove_list k
    end.
End contains_dec_help.

Inductive Forall3 {A B C} (P : A → B → C → Prop) :
     list A → list B → list C → Prop :=
  | Forall3_nil : Forall3 P [] [] []
  | Forall3_cons x y z l k k' :
     P x y z → Forall3 P l k k' → Forall3 P (x :: l) (y :: k) (z :: k').

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
      then list_difference l k else x :: list_difference l k
    end.
  Definition list_union (l k : list A) : list A := list_difference l k ++ k.
  Fixpoint list_intersection (l k : list A) : list A :=
    match l with
    | [] => []
    | x :: l =>
      if decide_rel (∈) x k
      then x :: list_intersection l k else list_intersection l k
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
Lemma app_injective_1 {A} (l1 k1 l2 k2 : list A) :
  length l1 = length k1 → l1 ++ l2 = k1 ++ k2 → l1 = k1 ∧ l2 = k2.
Proof. revert k1. induction l1; intros [|??]; naive_solver. Qed.
Lemma app_injective_2 {A} (l1 k1 l2 k2 : list A) :
  length l2 = length k2 → l1 ++ l2 = k1 ++ k2 → l1 = k1 ∧ l2 = k2.
Proof.
  intros ? Hl. apply app_injective_1; auto.
  apply (f_equal length) in Hl. rewrite !app_length in Hl. lia.
Qed.
Ltac simplify_list_equality :=
  repeat match goal with
  | _ => progress simplify_equality
  | H : _ ++ _ = _ ++ _ |- _ => first
    [ apply app_inv_head in H | apply app_inv_tail in H
    | apply app_injective_1 in H; [destruct H|done]
    | apply app_injective_2 in H; [destruct H|done] ]
  | H : [?x] !! ?i = Some ?y |- _ =>
    destruct i; [change (Some x = Some y) in H | discriminate]
  end;
  try discriminate_list_equality.
Ltac simplify_list_equality' :=
  repeat (progress simpl in * || simplify_list_equality).

(** * General theorems *)
Section general_properties.
Context {A : Type}.
Implicit Types x y z : A.
Implicit Types l k : list A.

Global Instance: Injective2 (=) (=) (=) (@cons A).
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
Proof. split. apply app_eq_nil. by intros [-> ->]. Qed.
Lemma app_singleton l1 l2 x :
  l1 ++ l2 = [x] ↔ l1 = [] ∧ l2 = [x] ∨ l1 = [x] ∧ l2 = [].
Proof. split. apply app_eq_unit. by intros [[-> ->]|[-> ->]]. Qed.
Lemma cons_middle x l1 l2 : l1 ++ x :: l2 = l1 ++ [x] ++ l2.
Proof. done. Qed.
Lemma list_eq l1 l2 : (∀ i, l1 !! i = l2 !! i) → l1 = l2.
Proof.
  revert l2. induction l1; intros [|??] H.
  * done.
  * discriminate (H 0).
  * discriminate (H 0).
  * f_equal; [by injection (H 0)|]. apply (IHl1 _ $ λ i, H (S i)).
Qed.
Global Instance list_eq_dec {dec : ∀ x y, Decision (x = y)} : ∀ l k,
  Decision (l = k) := list_eq_dec dec.
Global Instance list_eq_nil_dec l : Decision (l = []).
Proof. by refine match l with [] => left _ | _ => right _ end. Defined.
Lemma list_singleton_reflect l :
  option_reflect (λ x, l = [x]) (length l ≠ 1) (list_singleton l).
Proof. by destruct l as [|? []]; constructor. Defined.

Definition nil_length : length (@nil A) = 0 := eq_refl.
Definition cons_length x l : length (x :: l) = S (length l) := eq_refl.
Lemma nil_or_length_pos l : l = [] ∨ length l ≠ 0.
Proof. destruct l; simpl; auto with lia. Qed.
Lemma nil_length_inv l : length l = 0 → l = [].
Proof. by destruct l. Qed.
Lemma lookup_nil i : @nil A !! i = None.
Proof. by destruct i. Qed.
Lemma lookup_tail l i : tail l !! i = l !! S i.
Proof. by destruct l. Qed.
Lemma lookup_lt_Some l i x : l !! i = Some x → i < length l.
Proof.
  revert i. induction l; intros [|?] ?; simplify_equality'; auto with arith.
Qed.
Lemma lookup_lt_is_Some_1 l i : is_Some (l !! i) → i < length l.
Proof. intros [??]; eauto using lookup_lt_Some. Qed.
Lemma lookup_lt_is_Some_2 l i : i < length l → is_Some (l !! i).
Proof.
  revert i. induction l; intros [|?] ?; simplify_equality'; eauto with lia.
Qed.
Lemma lookup_lt_is_Some l i : is_Some (l !! i) ↔ i < length l.
Proof. split; auto using lookup_lt_is_Some_1, lookup_lt_is_Some_2. Qed.
Lemma lookup_ge_None l i : l !! i = None ↔ length l ≤ i.
Proof. rewrite eq_None_not_Some, lookup_lt_is_Some. lia. Qed.
Lemma lookup_ge_None_1 l i : l !! i = None → length l ≤ i.
Proof. by rewrite lookup_ge_None. Qed.
Lemma lookup_ge_None_2 l i : length l ≤ i → l !! i = None.
Proof. by rewrite lookup_ge_None. Qed.
Lemma list_eq_same_length l1 l2 n :
  length l2 = n → length l1 = n →
  (∀ i x y, i < n → l1 !! i = Some x → l2 !! i = Some y → x = y) → l1 = l2.
Proof.
  intros <- Hlen Hl; apply list_eq; intros i. destruct (l2 !! i) as [x|] eqn:Hx.
  * destruct (lookup_lt_is_Some_2 l1 i) as [y Hy].
    { rewrite Hlen; eauto using lookup_lt_Some. }
    rewrite Hy; f_equal; apply (Hl i); eauto using lookup_lt_Some.
  * by rewrite lookup_ge_None, Hlen, <-lookup_ge_None.
Qed.
Lemma lookup_app_l l1 l2 i : i < length l1 → (l1 ++ l2) !! i = l1 !! i.
Proof. revert i. induction l1; intros [|?]; simpl; auto with lia. Qed.
Lemma lookup_app_l_Some l1 l2 i x : l1 !! i = Some x → (l1 ++ l2) !! i = Some x.
Proof. intros. rewrite lookup_app_l; eauto using lookup_lt_Some. Qed.
Lemma lookup_app_r l1 l2 i : (l1 ++ l2) !! (length l1 + i) = l2 !! i.
Proof. revert i. induction l1; intros [|i]; simplify_equality'; auto. Qed.
Lemma lookup_app_r_alt l1 l2 i j :
  j = length l1 → (l1 ++ l2) !! (j + i) = l2 !! i.
Proof. intros ->. by apply lookup_app_r. Qed.
Lemma lookup_app_r_Some l1 l2 i x :
  l2 !! i = Some x → (l1 ++ l2) !! (length l1 + i) = Some x.
Proof. by rewrite lookup_app_r. Qed.
Lemma lookup_app_minus_r l1 l2 i :
  length l1 ≤ i → (l1 ++ l2) !! i = l2 !! (i - length l1).
Proof. intros. rewrite <-(lookup_app_r l1 l2). f_equal. lia. Qed.
Lemma lookup_app_inv l1 l2 i x :
  (l1 ++ l2) !! i = Some x → l1 !! i = Some x ∨ l2 !! (i - length l1) = Some x.
Proof. revert i. induction l1; intros [|i] ?; simplify_equality'; auto. Qed.
Lemma list_lookup_middle l1 l2 x n :
  n = length l1 → (l1 ++ x :: l2) !! n = Some x.
Proof. intros ->. by induction l1. Qed.

Lemma alter_length f l i : length (alter f i l) = length l.
Proof. revert i. by induction l; intros [|?]; f_equal'. Qed.
Lemma insert_length l i x : length (<[i:=x]>l) = length l.
Proof. revert i. by induction l; intros [|?]; f_equal'. Qed.
Lemma list_lookup_alter f l i : alter f i l !! i = f <$> l !! i.
Proof. revert i. induction l. done. intros [|i]. done. apply (IHl i). Qed.
Lemma list_lookup_alter_ne f l i j : i ≠ j → alter f i l !! j = l !! j.
Proof.
  revert i j. induction l; [done|]. intros [][] ?; csimpl; auto with congruence.
Qed.
Lemma list_lookup_insert l i x : i < length l → <[i:=x]>l !! i = Some x.
Proof. revert i. induction l; intros [|?] ?; f_equal'; auto with lia. Qed.
Lemma list_lookup_insert_ne l i j x : i ≠ j → <[i:=x]>l !! j = l !! j.
Proof.
  revert i j. induction l; [done|]. intros [] [] ?; simpl; auto with congruence.
Qed.
Lemma list_lookup_other l i x :
  length l ≠ 1 → l !! i = Some x → ∃ j y, j ≠ i ∧ l !! j = Some y.
Proof.
  intros. destruct i, l as [|x0 [|x1 l]]; simplify_equality'.
  * by exists 1 x1.
  * by exists 0 x0.
Qed.
Lemma alter_app_l f l1 l2 i :
  i < length l1 → alter f i (l1 ++ l2) = alter f i l1 ++ l2.
Proof. revert i. induction l1; intros [|?] ?; f_equal'; auto with lia. Qed.
Lemma alter_app_r f l1 l2 i :
  alter f (length l1 + i) (l1 ++ l2) = l1 ++ alter f i l2.
Proof. revert i. induction l1; intros [|?]; f_equal'; auto. Qed.
Lemma alter_app_r_alt f l1 l2 i :
  length l1 ≤ i → alter f i (l1 ++ l2) = l1 ++ alter f (i - length l1) l2.
Proof.
  intros. assert (i = length l1 + (i - length l1)) as Hi by lia.
  rewrite Hi at 1. by apply alter_app_r.
Qed.
Lemma list_alter_ext f g l k i :
  (∀ x, l !! i = Some x → f x = g x) → l = k → alter f i l = alter g i k.
Proof. intros H ->. revert i H. induction k; intros [|?] ?; f_equal'; auto. Qed.
Lemma list_alter_compose f g l i :
  alter (f ∘ g) i l = alter f i (alter g i l).
Proof. revert i. induction l; intros [|?]; f_equal'; auto. Qed.
Lemma list_alter_commute f g l i j :
  i ≠ j → alter f i (alter g j l) = alter g j (alter f i l).
Proof. revert i j. induction l; intros [|?][|?] ?; f_equal'; auto with lia. Qed.
Lemma insert_app_l l1 l2 i x :
  i < length l1 → <[i:=x]>(l1 ++ l2) = <[i:=x]>l1 ++ l2.
Proof. revert i. induction l1; intros [|?] ?; f_equal'; auto with lia. Qed.
Lemma insert_app_r l1 l2 i x : <[length l1+i:=x]>(l1 ++ l2) = l1 ++ <[i:=x]>l2.
Proof. revert i. induction l1; intros [|?]; f_equal'; auto. Qed.
Lemma insert_app_r_alt l1 l2 i x :
  length l1 ≤ i → <[i:=x]>(l1 ++ l2) = l1 ++ <[i - length l1:=x]>l2.
Proof.
  intros. assert (i = length l1 + (i - length l1)) as Hi by lia.
  rewrite Hi at 1. by apply insert_app_r.
Qed.
Lemma delete_middle l1 l2 x : delete (length l1) (l1 ++ x :: l2) = l1 ++ l2.
Proof. induction l1; f_equal'; auto. Qed.

(** ** Properties of the [elem_of] predicate *)
Lemma not_elem_of_nil x : x ∉ [].
Proof. by inversion 1. Qed.
Lemma elem_of_nil x : x ∈ [] ↔ False.
Proof. intuition. by destruct (not_elem_of_nil x). Qed.
Lemma elem_of_nil_inv l : (∀ x, x ∉ l) → l = [].
Proof. destruct l. done. by edestruct 1; constructor. Qed.
Lemma elem_of_not_nil x l : x ∈ l → l ≠ [].
Proof. intros ? ->. by apply (elem_of_nil x). Qed.
Lemma elem_of_cons l x y : x ∈ y :: l ↔ x = y ∨ x ∈ l.
Proof. split; [inversion 1; subst|intros [->|?]]; constructor (done). Qed.
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
  induction 1 as [x l|x y l ? [l1 [l2 ->]]]; [by eexists [], l|].
  by exists (y :: l1) l2.
Qed.
Lemma elem_of_list_lookup_1 l x : x ∈ l → ∃ i, l !! i = Some x.
Proof.
  induction 1 as [|???? IH]; [by exists 0 |].
  destruct IH as [i ?]; auto. by exists (S i).
Qed.
Lemma elem_of_list_lookup_2 l i x : l !! i = Some x → x ∈ l.
Proof.
  revert i. induction l; intros [|i] ?; simplify_equality'; constructor; eauto.
Qed.
Lemma elem_of_list_lookup l x : x ∈ l ↔ ∃ i, l !! i = Some x.
Proof. firstorder eauto using elem_of_list_lookup_1, elem_of_list_lookup_2. Qed.
Lemma elem_of_list_omap {B} (f : A → option B) l (y : B) :
  y ∈ omap f l ↔ ∃ x, x ∈ l ∧ f x = Some y.
Proof.
  split.
  * induction l as [|x l]; csimpl; repeat case_match; inversion 1; subst;
      setoid_rewrite elem_of_cons; naive_solver.
  * intros (x&Hx&?). induction Hx; csimpl; repeat case_match;
      simplify_equality; auto; constructor (by auto).
Qed.

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
Lemma NoDup_lookup l i j x :
  NoDup l → l !! i = Some x → l !! j = Some x → i = j.
Proof.
  intros Hl. revert i j. induction Hl as [|x' l Hx Hl IH].
  { intros; simplify_equality. }
  intros [|i] [|j] ??; simplify_equality'; eauto with f_equal;
    exfalso; eauto using elem_of_list_lookup_2.
Qed.
Lemma NoDup_alt l :
  NoDup l ↔ ∀ i j x, l !! i = Some x → l !! j = Some x → i = j.
Proof.
  split; eauto using NoDup_lookup.
  induction l as [|x l IH]; intros Hl; constructor.
  * rewrite elem_of_list_lookup. intros [i ?].
    by feed pose proof (Hl (S i) 0 x); auto.
  * apply IH. intros i j x' ??. by apply (injective S), (Hl (S i) (S j) x').
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
  Lemma NoDup_remove_dups l : NoDup (remove_dups l).
  Proof.
    induction l; simpl; repeat case_decide; try constructor; auto.
    by rewrite elem_of_remove_dups.
  Qed.
End no_dup_dec.

(** ** Set operations on lists *)
Section list_set.
  Context {dec : ∀ x y, Decision (x = y)}.
  Lemma elem_of_list_difference l k x : x ∈ list_difference l k ↔ x ∈ l ∧ x ∉ k.
  Proof.
    split; induction l; simpl; try case_decide;
      rewrite ?elem_of_nil, ?elem_of_cons; intuition congruence.
  Qed.
  Lemma NoDup_list_difference l k : NoDup l → NoDup (list_difference l k).
  Proof.
    induction 1; simpl; try case_decide.
    * constructor.
    * done.
    * constructor. rewrite elem_of_list_difference; intuition. done.
  Qed.
  Lemma elem_of_list_union l k x : x ∈ list_union l k ↔ x ∈ l ∨ x ∈ k.
  Proof.
    unfold list_union. rewrite elem_of_app, elem_of_list_difference.
    intuition. case (decide (x ∈ k)); intuition.
  Qed.
  Lemma NoDup_list_union l k : NoDup l → NoDup k → NoDup (list_union l k).
  Proof.
    intros. apply NoDup_app. repeat split.
    * by apply NoDup_list_difference.
    * intro. rewrite elem_of_list_difference. intuition.
    * done.
  Qed.
  Lemma elem_of_list_intersection l k x :
    x ∈ list_intersection l k ↔ x ∈ l ∧ x ∈ k.
  Proof.
    split; induction l; simpl; repeat case_decide;
      rewrite ?elem_of_nil, ?elem_of_cons; intuition congruence.
  Qed.
  Lemma NoDup_list_intersection l k : NoDup l → NoDup (list_intersection l k).
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
    * induction l as [|x1 l IH]; simpl; [by rewrite elem_of_nil|].
      intros Hx. setoid_rewrite elem_of_cons.
      cut ((∃ x2, x2 ∈ k ∧ f x1 x2 = Some x)
        ∨ x ∈ list_intersection_with f l k); [naive_solver|].
      clear IH. revert Hx. generalize (list_intersection_with f l k).
      induction k; simpl; [by auto|].
      case_match; setoid_rewrite elem_of_cons; naive_solver.
    * intros (x1&x2&Hx1&Hx2&Hx). induction Hx1 as [x1|x1 ? l ? IH]; simpl.
      + generalize (list_intersection_with f l k).
        induction Hx2; simpl; [by rewrite Hx; left |].
        case_match; simpl; try setoid_rewrite elem_of_cons; auto.
      + generalize (IH Hx). clear Hx IH Hx2.
        generalize (list_intersection_with f l k).
        induction k; simpl; intros; [done|].
        case_match; simpl; rewrite ?elem_of_cons; auto.
  Qed.
End list_set.

(** ** Properties of the [filter] function *)
Section filter.
  Context (P : A → Prop) `{∀ x, Decision (P x)}.
  Lemma elem_of_list_filter l x : x ∈ filter P l ↔ P x ∧ x ∈ l.
  Proof.
    unfold filter. induction l; simpl; repeat case_decide;
       rewrite ?elem_of_nil, ?elem_of_cons; naive_solver.
  Qed.
  Lemma NoDup_filter l : NoDup l → NoDup (filter P l).
  Proof.
    unfold filter. induction 1; simpl; repeat case_decide;
      rewrite ?NoDup_nil, ?NoDup_cons, ?elem_of_list_filter; tauto.
  Qed.
End filter.

(** ** Properties of the [find] function *)
Section find.
  Context (P : A → Prop) `{∀ x, Decision (P x)}.
  Lemma list_find_Some l i :
    list_find P l = Some i → ∃ x, l !! i = Some x ∧ P x.
  Proof.
    revert i. induction l; intros [] ?; simplify_option_equality; eauto.
  Qed.
  Lemma list_find_elem_of l x : x ∈ l → P x → ∃ i, list_find P l = Some i.
  Proof.
    induction 1 as [|x y l ? IH]; intros; simplify_option_equality; eauto.
    by destruct IH as [i ->]; [|exists (S i)].
  Qed.
End find.

Section find_eq.
  Context `{∀ x y, Decision (x = y)}.
  Lemma list_find_eq_Some l i x : list_find (x =) l = Some i → l !! i = Some x.
  Proof.
    intros.
    destruct (list_find_Some (x =) l i) as (?&?&?); auto with congruence.
  Qed.
  Lemma list_find_eq_elem_of l x : x ∈ l → ∃ i, list_find (x=) l = Some i.
  Proof. eauto using list_find_elem_of. Qed.
End find_eq.

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
Lemma elem_of_reverse_2 x l : x ∈ l → x ∈ reverse l.
Proof.
  induction 1; rewrite reverse_cons, elem_of_app,
    ?elem_of_list_singleton; intuition.
Qed.
Lemma elem_of_reverse x l : x ∈ reverse l ↔ x ∈ l.
Proof.
  split; auto using elem_of_reverse_2.
  intros. rewrite <-(reverse_involutive l). by apply elem_of_reverse_2.
Qed.
Global Instance: Injective (=) (=) (@reverse A).
Proof.
  intros l1 l2 Hl.
  by rewrite <-(reverse_involutive l1), <-(reverse_involutive l2), Hl.
Qed.

(** ** Properties of the [last] function *)
Lemma last_snoc x l : last (l ++ [x]) = Some x.
Proof. induction l as [|? []]; simpl; auto. Qed.
Lemma last_reverse l : last (reverse l) = head l.
Proof. by destruct l as [|x l]; rewrite ?reverse_cons, ?last_snoc. Qed.
Lemma head_reverse l : head (reverse l) = last l.
Proof. by rewrite <-last_reverse, reverse_involutive. Qed.

(** ** Properties of the [take] function *)
Definition take_drop i l : take i l ++ drop i l = l := firstn_skipn i l.
Lemma take_drop_middle l i x :
  l !! i = Some x → take i l ++ x :: drop (S i) l = l.
Proof.
  revert i x. induction l; intros [|?] ??; simplify_equality'; f_equal; auto.
Qed.
Lemma take_nil n : take n (@nil A) = [].
Proof. by destruct n. Qed.
Lemma take_app l k : take (length l) (l ++ k) = l.
Proof. induction l; f_equal'; auto. Qed.
Lemma take_app_alt l k n : n = length l → take n (l ++ k) = l.
Proof. intros Hn. by rewrite Hn, take_app. Qed.
Lemma take_app_le l k n : n ≤ length l → take n (l ++ k) = take n l.
Proof. revert n. induction l; intros [|?] ?; f_equal'; auto with lia. Qed.
Lemma take_plus_app l k n m :
  length l = n → take (n + m) (l ++ k) = l ++ take m k.
Proof. intros <-. induction l; f_equal'; auto. Qed.
Lemma take_app_ge l k n :
  length l ≤ n → take n (l ++ k) = l ++ take (n - length l) k.
Proof. revert n. induction l; intros [|?] ?; f_equal'; auto with lia. Qed.
Lemma take_ge l n : length l ≤ n → take n l = l.
Proof. revert n. induction l; intros [|?] ?; f_equal'; auto with lia. Qed.
Lemma take_take l n m : take n (take m l) = take (min n m) l.
Proof. revert n m. induction l; intros [|?] [|?]; f_equal'; auto. Qed.
Lemma take_idempotent l n : take n (take n l) = take n l.
Proof. by rewrite take_take, Min.min_idempotent. Qed.
Lemma take_length l n : length (take n l) = min n (length l).
Proof. revert n. induction l; intros [|?]; f_equal'; done. Qed.
Lemma take_length_le l n : n ≤ length l → length (take n l) = n.
Proof. rewrite take_length. apply Min.min_l. Qed.
Lemma take_length_ge l n : length l ≤ n → length (take n l) = length l.
Proof. rewrite take_length. apply Min.min_r. Qed.
Lemma take_drop_commute l n m : take n (drop m l) = drop m (take (m + n) l).
Proof.
  revert n m. induction l; intros [|?][|?]; simpl; auto using take_nil with lia.
Qed.
Lemma lookup_take l n i : i < n → take n l !! i = l !! i.
Proof. revert n i. induction l; intros [|n] [|i] ?; simpl; auto with lia. Qed.
Lemma lookup_take_ge l n i : n ≤ i → take n l !! i = None.
Proof. revert n i. induction l; intros [|?] [|?] ?; simpl; auto with lia. Qed.
Lemma take_alter f l n i : n ≤ i → take n (alter f i l) = take n l.
Proof.
  intros. apply list_eq. intros j. destruct (le_lt_dec n j).
  * by rewrite !lookup_take_ge.
  * by rewrite !lookup_take, !list_lookup_alter_ne by lia.
Qed.
Lemma take_insert l n i x : n ≤ i → take n (<[i:=x]>l) = take n l.
Proof.
  intros. apply list_eq. intros j. destruct (le_lt_dec n j).
  * by rewrite !lookup_take_ge.
  * by rewrite !lookup_take, !list_lookup_insert_ne by lia.
Qed.

(** ** Properties of the [drop] function *)
Lemma drop_0 l : drop 0 l = l.
Proof. done. Qed.
Lemma drop_nil n : drop n (@nil A) = [].
Proof. by destruct n. Qed.
Lemma drop_length l n : length (drop n l) = length l - n.
Proof. revert n. by induction l; intros [|i]; f_equal'. Qed.
Lemma drop_ge l n : length l ≤ n → drop n l = [].
Proof. revert n. induction l; intros [|??]; simpl in *; auto with lia. Qed.
Lemma drop_all l : drop (length l) l = [].
Proof. by apply drop_ge. Qed.
Lemma drop_drop l n1 n2 : drop n1 (drop n2 l) = drop (n2 + n1) l.
Proof. revert n2. induction l; intros [|?]; simpl; rewrite ?drop_nil; auto. Qed.
Lemma drop_app_le l k n :
  n ≤ length l → drop n (l ++ k) = drop n l ++ k.
Proof. revert n. induction l; intros [|?]; simpl; auto with lia. Qed.
Lemma drop_app l k : drop (length l) (l ++ k) = k.
Proof. by rewrite drop_app_le, drop_all. Qed.
Lemma drop_app_alt l k n : n = length l → drop n (l ++ k) = k.
Proof. intros ->. by apply drop_app. Qed.
Lemma drop_app_ge l k n :
  length l ≤ n → drop n (l ++ k) = drop (n - length l) k.
Proof.
  intros. rewrite <-(Nat.sub_add (length l) n) at 1 by done.
  by rewrite Nat.add_comm, <-drop_drop, drop_app.
Qed.
Lemma lookup_drop l n i : drop n l !! i = l !! (n + i).
Proof. revert n i. induction l; intros [|i] ?; simpl; auto. Qed.
Lemma drop_alter f l n i : i < n → drop n (alter f i l) = drop n l.
Proof.
  intros. apply list_eq. intros j.
  by rewrite !lookup_drop, !list_lookup_alter_ne by lia.
Qed.
Lemma drop_insert l n i x : i < n → drop n (<[i:=x]>l) = drop n l.
Proof.
  intros. apply list_eq. intros j.
  by rewrite !lookup_drop, !list_lookup_insert_ne by lia.
Qed.
Lemma delete_take_drop l i : delete i l = take i l ++ drop (S i) l.
Proof. revert i. induction l; intros [|?]; f_equal'; auto. Qed.

(** ** Properties of the [replicate] function *)
Lemma replicate_length n x : length (replicate n x) = n.
Proof. induction n; simpl; auto. Qed.
Lemma lookup_replicate n x i : i < n → replicate n x !! i = Some x.
Proof. revert i. induction n; intros [|?]; naive_solver auto with lia. Qed.
Lemma lookup_replicate_inv n x y i :
  replicate n x !! i = Some y → y = x ∧ i < n.
Proof. revert i. induction n; intros [|?]; naive_solver auto with lia. Qed.
Lemma lookup_replicate_None n x i : n ≤ i ↔ replicate n x !! i = None.
Proof.
  rewrite eq_None_not_Some, Nat.le_ngt. split.
  * intros Hin [x' Hx']; destruct Hin.
    by destruct (lookup_replicate_inv n x x' i).
  * intros Hx ?. destruct Hx. exists x; auto using lookup_replicate.
Qed.
Lemma elem_of_replicate_inv x n y : x ∈ replicate n y → x = y.
Proof. induction n; simpl; rewrite ?elem_of_nil, ?elem_of_cons; intuition. Qed.
Lemma replicate_S n x : replicate (S n) x = x :: replicate  n x.
Proof. done. Qed.
Lemma replicate_plus n m x :
  replicate (n + m) x = replicate n x ++ replicate m x.
Proof. induction n; f_equal'; auto. Qed.
Lemma take_replicate n m x : take n (replicate m x) = replicate (min n m) x.
Proof. revert m. by induction n; intros [|?]; f_equal'. Qed.
Lemma take_replicate_plus n m x : take n (replicate (n + m) x) = replicate n x.
Proof. by rewrite take_replicate, min_l by lia. Qed.
Lemma drop_replicate n m x : drop n (replicate m x) = replicate (m - n) x.
Proof. revert m. by induction n; intros [|?]; f_equal'. Qed.
Lemma drop_replicate_plus n m x : drop n (replicate (n + m) x) = replicate m x.
Proof. rewrite drop_replicate. f_equal. lia. Qed.
Lemma replicate_as_elem_of x n l :
  replicate n x = l ↔ length l = n ∧ ∀ y, y ∈ l → y = x.
Proof.
  split; [intros <-; eauto using elem_of_replicate_inv, replicate_length|].
  intros [<- Hl]. symmetry. induction l as [|y l IH]; f_equal'.
  * apply Hl. by left.
  * apply IH. intros ??. apply Hl. by right.
Qed.
Lemma reverse_replicate n x : reverse (replicate n x) = replicate n x.
Proof.
  symmetry. apply replicate_as_elem_of.
  rewrite reverse_length, replicate_length. split; auto.
  intros y. rewrite elem_of_reverse. by apply elem_of_replicate_inv.
Qed.
Lemma replicate_false βs n : length βs = n → replicate n false =.>* βs.
Proof. intros <-. by induction βs; simpl; constructor. Qed.

(** ** Properties of the [resize] function *)
Lemma resize_spec l n x : resize n x l = take n l ++ replicate (n - length l) x.
Proof. revert n. induction l; intros [|?]; f_equal'; auto. Qed.
Lemma resize_0 l x : resize 0 x l = [].
Proof. by destruct l. Qed.
Lemma resize_nil n x : resize n x [] = replicate n x.
Proof. rewrite resize_spec. rewrite take_nil. f_equal'. lia. Qed.
Lemma resize_ge l n x :
  length l ≤ n → resize n x l = l ++ replicate (n - length l) x.
Proof. intros. by rewrite resize_spec, take_ge. Qed.
Lemma resize_le l n x : n ≤ length l → resize n x l = take n l.
Proof.
  intros. rewrite resize_spec, (proj2 (Nat.sub_0_le _ _)) by done.
  simpl. by rewrite (right_id_L [] (++)).
Qed.
Lemma resize_all l x : resize (length l) x l = l.
Proof. intros. by rewrite resize_le, take_ge. Qed.
Lemma resize_all_alt l n x : n = length l → resize n x l = l.
Proof. intros ->. by rewrite resize_all. Qed.
Lemma resize_plus l n m x :
  resize (n + m) x l = resize n x l ++ resize m x (drop n l).
Proof.
  revert n m. induction l; intros [|?] [|?]; f_equal'; auto.
  * by rewrite Nat.add_0_r, (right_id_L [] (++)).
  * by rewrite replicate_plus.
Qed.
Lemma resize_plus_eq l n m x :
  length l = n → resize (n + m) x l = l ++ replicate m x.
Proof. intros <-. by rewrite resize_plus, resize_all, drop_all, resize_nil. Qed.
Lemma resize_app_le l1 l2 n x :
  n ≤ length l1 → resize n x (l1 ++ l2) = resize n x l1.
Proof.
  intros. by rewrite !resize_le, take_app_le by (rewrite ?app_length; lia).
Qed.
Lemma resize_app l1 l2 n x : n = length l1 → resize n x (l1 ++ l2) = l1.
Proof. intros ->. by rewrite resize_app_le, resize_all. Qed.
Lemma resize_app_ge l1 l2 n x :
  length l1 ≤ n → resize n x (l1 ++ l2) = l1 ++ resize (n - length l1) x l2.
Proof.
  intros. rewrite !resize_spec, take_app_ge, (associative_L (++)) by done.
  do 2 f_equal. rewrite app_length. lia.
Qed.
Lemma resize_length l n x : length (resize n x l) = n.
Proof. rewrite resize_spec, app_length, replicate_length, take_length. lia. Qed.
Lemma resize_replicate x n m : resize n x (replicate m x) = replicate n x.
Proof. revert m. induction n; intros [|?]; f_equal'; auto. Qed.
Lemma resize_resize l n m x : n ≤ m → resize n x (resize m x l) = resize n x l.
Proof.
  revert n m. induction l; simpl.
  * intros. by rewrite !resize_nil, resize_replicate.
  * intros [|?] [|?] ?; f_equal'; auto with lia.
Qed.
Lemma resize_idempotent l n x : resize n x (resize n x l) = resize n x l.
Proof. by rewrite resize_resize. Qed.
Lemma resize_take_le l n m x : n ≤ m → resize n x (take m l) = resize n x l.
Proof. revert n m. induction l; intros [|?][|?] ?; f_equal'; auto with lia. Qed.
Lemma resize_take_eq l n x : resize n x (take n l) = resize n x l.
Proof. by rewrite resize_take_le. Qed.
Lemma take_resize l n m x : take n (resize m x l) = resize (min n m) x l.
Proof.
  revert n m. induction l; intros [|?][|?]; f_equal'; auto using take_replicate.
Qed.
Lemma take_resize_le l n m x : n ≤ m → take n (resize m x l) = resize n x l.
Proof. intros. by rewrite take_resize, Min.min_l. Qed.
Lemma take_resize_eq l n x : take n (resize n x l) = resize n x l.
Proof. intros. by rewrite take_resize, Min.min_l. Qed.
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
Lemma lookup_resize l n x i : i < n → i < length l → resize n x l !! i = l !! i.
Proof.
  intros ??. destruct (decide (n < length l)).
  * by rewrite resize_le, lookup_take by lia.
  * by rewrite resize_ge, lookup_app_l by lia.
Qed.
Lemma lookup_resize_new l n x i :
  length l ≤ i → i < n → resize n x l !! i = Some x.
Proof.
  intros ??. rewrite resize_ge by lia.
  replace i with (length l + (i - length l)) by lia.
  by rewrite lookup_app_r, lookup_replicate by lia.
Qed.
Lemma lookup_resize_old l n x i : n ≤ i → resize n x l !! i = None.
Proof. intros ?. apply lookup_ge_None_2. by rewrite resize_length. Qed.
End general_properties.

Section more_general_properties.
Context {A : Type}.
Implicit Types x y z : A.
Implicit Types l k : list A.

(** ** Properties of the [reshape] function *)
Lemma reshape_length szs l : length (reshape szs l) = length szs.
Proof. revert l. by induction szs; intros; f_equal'. Qed.
Lemma join_reshape szs l :
  sum_list szs = length l → mjoin (reshape szs l) = l.
Proof.
  revert l. induction szs as [|sz szs IH]; simpl; intros l Hl; [by destruct l|].
  by rewrite IH, take_drop by (rewrite drop_length; lia).
Qed.
Lemma sum_list_replicate n m : sum_list (replicate m n) = m * n.
Proof. induction m; simpl; auto. Qed.

(** ** Properties of [sublist_lookup] and [sublist_alter] *)
Lemma sublist_lookup_length l i n k :
  sublist_lookup i n l = Some k → length k = n.
Proof.
  unfold sublist_lookup; intros; simplify_option_equality.
  rewrite take_length, drop_length; lia.
Qed.
Lemma sublist_lookup_all l n : length l = n → sublist_lookup 0 n l = Some l.
Proof.
  intros. unfold sublist_lookup; case_option_guard; [|lia].
  by rewrite take_ge by (rewrite drop_length; lia).
Qed.
Lemma sublist_lookup_Some l i n :
  i + n ≤ length l → sublist_lookup i n l = Some (take n (drop i l)).
Proof. by unfold sublist_lookup; intros; simplify_option_equality. Qed.
Lemma sublist_lookup_None l i n :
  length l < i + n → sublist_lookup i n l = None.
Proof. by unfold sublist_lookup; intros; simplify_option_equality by lia. Qed.
Lemma sublist_eq l k n :
  (n | length l) → (n | length k) →
  (∀ i, sublist_lookup (i * n) n l = sublist_lookup (i * n) n k) → l = k.
Proof.
  revert l k. assert (∀ l i,
    n ≠ 0 → (n | length l) → ¬n * i `div` n + n ≤ length l → length l ≤ i).
  { intros l i ? [j ->] Hjn. apply Nat.nlt_ge; contradict Hjn.
    rewrite <-Nat.mul_succ_r, (Nat.mul_comm n).
    apply Nat.mul_le_mono_r, Nat.le_succ_l, Nat.div_lt_upper_bound; lia. }
  intros l k Hl Hk Hlookup. destruct (decide (n = 0)) as [->|].
  { by rewrite (nil_length_inv l),
      (nil_length_inv k) by eauto using Nat.divide_0_l. }
  apply list_eq; intros i. specialize (Hlookup (i `div` n)).
  rewrite (Nat.mul_comm _ n) in Hlookup.
  unfold sublist_lookup in *; simplify_option_equality;
    [|by rewrite !lookup_ge_None_2 by auto].
  apply (f_equal (!! i `mod` n)) in Hlookup.
  by rewrite !lookup_take, !lookup_drop, <-!Nat.div_mod in Hlookup
    by (auto using Nat.mod_upper_bound with lia).
Qed.
Lemma sublist_eq_same_length l k j n :
  length l = j * n → length k = j * n →
  (∀ i,i < j → sublist_lookup (i * n) n l = sublist_lookup (i * n) n k) → l = k.
Proof.
  intros Hl Hk ?. destruct (decide (n = 0)) as [->|].
  { by rewrite (nil_length_inv l), (nil_length_inv k) by lia. }
  apply sublist_eq with n; [by exists j|by exists j|].
  intros i. destruct (decide (i < j)); [by auto|].
  assert (∀ m, m = j * n → m < i * n + n).
  { intros ? ->. replace (i * n + n) with (S i * n) by lia.
    apply Nat.mul_lt_mono_pos_r; lia. }
  by rewrite !sublist_lookup_None by auto.
Qed.
Lemma sublist_lookup_reshape l i n m :
  0 < n → length l = m * n →
  reshape (replicate m n) l !! i = sublist_lookup (i * n) n l.
Proof.
  intros Hn Hl. unfold sublist_lookup.  apply option_eq; intros x; split.
  * intros Hx. case_option_guard as Hi.
    { f_equal. clear Hi. revert i l Hl Hx.
      induction m as [|m IH]; intros [|i] l ??; simplify_equality'; auto.
      rewrite <-drop_drop. apply IH; rewrite ?drop_length; auto with lia. }
    destruct Hi. rewrite Hl, <-Nat.mul_succ_l.
    apply Nat.mul_le_mono_r, Nat.le_succ_l. apply lookup_lt_Some in Hx.
    by rewrite reshape_length, replicate_length in Hx.
  * intros Hx. case_option_guard as Hi; simplify_equality'.
    revert i l Hl Hi. induction m as [|m IH]; [auto with lia|].
    intros [|i] l ??; simpl; [done|]. rewrite <-drop_drop.
    rewrite IH; rewrite ?drop_length; auto with lia.
Qed.
Lemma sublist_lookup_compose l1 l2 l3 i n j m :
  sublist_lookup i n l1 = Some l2 → sublist_lookup j m l2 = Some l3 →
  sublist_lookup (i + j) m l1 = Some l3.
Proof.
  unfold sublist_lookup; intros; simplify_option_equality;
    repeat match goal with
    | H : _ ≤ length _ |- _ => rewrite take_length, drop_length in H
    end; rewrite ?take_drop_commute, ?drop_drop, ?take_take,
      ?Min.min_l, Nat.add_assoc by lia; auto with lia.
Qed.
Lemma sublist_alter_length f l i n k :
  sublist_lookup i n l = Some k → length (f k) = n →
  length (sublist_alter f i n l) = length l.
Proof.
  unfold sublist_alter, sublist_lookup. intros Hk ?; simplify_option_equality.
  rewrite !app_length, Hk, !take_length, !drop_length; lia.
Qed.
Lemma sublist_lookup_alter f l i n k :
  sublist_lookup i n l = Some k → length (f k) = n →
  sublist_lookup i n (sublist_alter f i n l) = f <$> sublist_lookup i n l.
Proof.
  unfold sublist_lookup. intros Hk ?. erewrite sublist_alter_length by eauto.
  unfold sublist_alter; simplify_option_equality.
  by rewrite Hk, drop_app_alt, take_app_alt by (rewrite ?take_length; lia).
Qed.
Lemma sublist_lookup_alter_ne f l i j n k :
  sublist_lookup j n l = Some k → length (f k) = n → i + n ≤ j ∨ j + n ≤ i →
  sublist_lookup i n (sublist_alter f j n l) = sublist_lookup i n l.
Proof.
  unfold sublist_lookup. intros Hk Hi ?. erewrite sublist_alter_length by eauto.
  unfold sublist_alter; simplify_option_equality; f_equal; rewrite Hk.
  apply list_eq; intros ii.
  destruct (decide (ii < length (f k))); [|by rewrite !lookup_take_ge by lia].
  rewrite !lookup_take, !lookup_drop by done. destruct (decide (i + ii < j)).
  { by rewrite lookup_app_l, lookup_take by (rewrite ?take_length; lia). }
  rewrite lookup_app_minus_r by (rewrite take_length; lia).
  rewrite take_length_le, lookup_app_minus_r, lookup_drop by lia. f_equal; lia.
Qed.
Lemma sublist_alter_all f l n : length l = n → sublist_alter f 0 n l = f l.
Proof.
  intros <-. unfold sublist_alter; simpl.
  by rewrite drop_all, (right_id_L [] (++)), take_ge.
Qed.
Lemma sublist_alter_compose f g l i n k :
  sublist_lookup i n l = Some k → length (f k) = n → length (g k) = n →
  sublist_alter (f ∘ g) i n l = sublist_alter f i n (sublist_alter g i n l).
Proof.
  unfold sublist_alter, sublist_lookup. intros Hk ??; simplify_option_equality.
  by rewrite !take_app_alt, drop_app_alt, !(associative_L (++)), drop_app_alt,
    take_app_alt by (rewrite ?app_length, ?take_length, ?Hk; lia).
Qed.

(** ** Properties of the [mask] function *)
Lemma mask_nil f βs : mask f βs (@nil A) = [].
Proof. by destruct βs. Qed.
Lemma mask_length f βs l : length (mask f βs l) = length l.
Proof. revert βs. induction l; intros [|??]; f_equal'; auto. Qed.
Lemma mask_true f l n : length l ≤ n → mask f (replicate n true) l = f <$> l.
Proof. revert n. induction l; intros [|?] ?; f_equal'; auto with lia. Qed.
Lemma mask_false f l n : mask f (replicate n false) l = l.
Proof. revert l. induction n; intros [|??]; f_equal'; auto. Qed.
Lemma mask_app f βs1 βs2 l :
  mask f (βs1 ++ βs2) l
  = mask f βs1 (take (length βs1) l) ++ mask f βs2 (drop (length βs1) l).
Proof. revert l. induction βs1;intros [|??]; f_equal'; auto using mask_nil. Qed.
Lemma take_mask f βs l n : take n (mask f βs l) = mask f (take n βs) (take n l).
Proof. revert n βs. induction l; intros [|?] [|[] ?]; f_equal'; auto. Qed.
Lemma drop_mask f βs l n : drop n (mask f βs l) = mask f (drop n βs) (drop n l).
Proof.
  revert n βs. induction l; intros [|?] [|[] ?]; f_equal'; auto using mask_nil.
Qed.
Lemma sublist_lookup_mask f βs l i n :
  sublist_lookup i n (mask f βs l)
  = mask f (take n (drop i βs)) <$> sublist_lookup i n l.
Proof.
  unfold sublist_lookup; rewrite mask_length; simplify_option_equality; auto.
  by rewrite drop_mask, take_mask.
Qed.
Lemma mask_mask f g βs1 βs2 l :
  (∀ x, f (g x) = f x) → βs1 =.>* βs2 →
  mask f βs2 (mask g βs1 l) = mask f βs2 l.
Proof.
  intros ? Hβs. revert l. by induction Hβs as [|[] []]; intros [|??]; f_equal'.
Qed.

(** ** Properties of the [seq] function *)
Lemma fmap_seq j n : S <$> seq j n = seq (S j) n.
Proof. revert j. induction n; intros; f_equal'; auto. Qed.
Lemma lookup_seq j n i : i < n → seq j n !! i = Some (j + i).
Proof.
  revert j i. induction n as [|n IH]; intros j [|i] ?; simpl; auto with lia.
  rewrite IH; auto with lia.
Qed.
Lemma lookup_seq_ge j n i : n ≤ i → seq j n !! i = None.
Proof. revert j i. induction n; intros j [|i] ?; simpl; auto with lia. Qed.
Lemma lookup_seq_inv j n i j' : seq j n !! i = Some j' → j' = j + i ∧ i < n.
Proof.
  destruct (le_lt_dec n i); [by rewrite lookup_seq_ge|].
  rewrite lookup_seq by done. intuition congruence.
Qed.

(** ** Properties of the [Permutation] predicate *)
Lemma Permutation_nil l : l ≡ₚ [] ↔ l = [].
Proof. split. by intro; apply Permutation_nil. by intros ->. Qed.
Lemma Permutation_singleton l x : l ≡ₚ [x] ↔ l = [x].
Proof. split. by intro; apply Permutation_length_1_inv. by intros ->. Qed.
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
Lemma replicate_Permutation n x l : replicate n x ≡ₚ l → replicate n x = l.
Proof.
  intros Hl. apply replicate_as_elem_of. split.
  * by rewrite <-Hl, replicate_length.
  * intros y. rewrite <-Hl. by apply elem_of_replicate_inv.
Qed.
Lemma reverse_Permutation l : reverse l ≡ₚ l.
Proof.
  induction l as [|x l IH]; [done|].
  by rewrite reverse_cons, (commutative (++)), IH.
Qed.

(** ** Properties of the [prefix_of] and [suffix_of] predicates *)
Global Instance: PreOrder (@prefix_of A).
Proof.
  split.
  * intros ?. eexists []. by rewrite (right_id_L [] (++)).
  * intros ???[k1->] [k2->]. exists (k1 ++ k2). by rewrite (associative_L (++)).
Qed.
Lemma prefix_of_nil l : [] `prefix_of` l.
Proof. by exists l. Qed.
Lemma prefix_of_nil_not x l : ¬x :: l `prefix_of` [].
Proof. by intros [k ?]. Qed.
Lemma prefix_of_cons x l1 l2 : l1 `prefix_of` l2 → x :: l1 `prefix_of` x :: l2.
Proof. intros [k ->]. by exists k. Qed.
Lemma prefix_of_cons_alt x y l1 l2 :
  x = y → l1 `prefix_of` l2 → x :: l1 `prefix_of` y :: l2.
Proof. intros ->. apply prefix_of_cons. Qed.
Lemma prefix_of_cons_inv_1 x y l1 l2 : x :: l1 `prefix_of` y :: l2 → x = y.
Proof. by intros [k ?]; simplify_equality'. Qed.
Lemma prefix_of_cons_inv_2 x y l1 l2 :
  x :: l1 `prefix_of` y :: l2 → l1 `prefix_of` l2.
Proof. intros [k ?]; simplify_equality. by exists k. Qed.
Lemma prefix_of_app k l1 l2 : l1 `prefix_of` l2 → k ++ l1 `prefix_of` k ++ l2.
Proof. intros [k' ->]. exists k'. by rewrite (associative_L (++)). Qed.
Lemma prefix_of_app_alt k1 k2 l1 l2 :
  k1 = k2 → l1 `prefix_of` l2 → k1 ++ l1 `prefix_of` k2 ++ l2.
Proof. intros ->. apply prefix_of_app. Qed.
Lemma prefix_of_app_l l1 l2 l3 : l1 ++ l3 `prefix_of` l2 → l1 `prefix_of` l2.
Proof. intros [k ->]. exists (l3 ++ k). by rewrite (associative_L (++)). Qed.
Lemma prefix_of_app_r l1 l2 l3 : l1 `prefix_of` l2 → l1 `prefix_of` l2 ++ l3.
Proof. intros [k ->]. exists (k ++ l3). by rewrite (associative_L (++)). Qed.
Lemma prefix_of_length l1 l2 : l1 `prefix_of` l2 → length l1 ≤ length l2.
Proof. intros [? ->]. rewrite app_length. lia. Qed.
Lemma prefix_of_snoc_not l x : ¬l ++ [x] `prefix_of` l.
Proof. intros [??]. discriminate_list_equality. Qed.
Global Instance: PreOrder (@suffix_of A).
Proof.
  split.
  * intros ?. by eexists [].
  * intros ???[k1->] [k2->]. exists (k2 ++ k1). by rewrite (associative_L (++)).
Qed.
Global Instance prefix_of_dec `{∀ x y, Decision (x = y)} : ∀ l1 l2,
    Decision (l1 `prefix_of` l2) := fix go l1 l2 :=
  match l1, l2 return { l1 `prefix_of` l2 } + { ¬l1 `prefix_of` l2 } with
  | [], _ => left (prefix_of_nil _)
  | _, [] => right (prefix_of_nil_not _ _)
  | x :: l1, y :: l2 =>
    match decide_rel (=) x y with
    | left Hxy =>
      match go l1 l2 with
      | left Hl1l2 => left (prefix_of_cons_alt _ _ _ _ Hxy Hl1l2)
      | right Hl1l2 => right (Hl1l2 ∘ prefix_of_cons_inv_2 _ _ _ _)
      end
    | right Hxy => right (Hxy ∘ prefix_of_cons_inv_1 _ _ _ _)
    end
  end.

Section prefix_ops.
  Context `{∀ x y, Decision (x = y)}.
  Lemma max_prefix_of_fst l1 l2 :
    l1 = (max_prefix_of l1 l2).2 ++ (max_prefix_of l1 l2).1.1.
  Proof.
    revert l2. induction l1; intros [|??]; simpl;
      repeat case_decide; f_equal'; auto.
  Qed.
  Lemma max_prefix_of_fst_alt l1 l2 k1 k2 k3 :
    max_prefix_of l1 l2 = (k1, k2, k3) → l1 = k3 ++ k1.
  Proof.
    intros. pose proof (max_prefix_of_fst l1 l2).
    by destruct (max_prefix_of l1 l2) as [[]?]; simplify_equality.
  Qed.
  Lemma max_prefix_of_fst_prefix l1 l2 : (max_prefix_of l1 l2).2 `prefix_of` l1.
  Proof. eexists. apply max_prefix_of_fst. Qed.
  Lemma max_prefix_of_fst_prefix_alt l1 l2 k1 k2 k3 :
    max_prefix_of l1 l2 = (k1, k2, k3) → k3 `prefix_of` l1.
  Proof. eexists. eauto using max_prefix_of_fst_alt. Qed.
  Lemma max_prefix_of_snd l1 l2 :
    l2 = (max_prefix_of l1 l2).2 ++ (max_prefix_of l1 l2).1.2.
  Proof.
    revert l2. induction l1; intros [|??]; simpl;
      repeat case_decide; f_equal'; auto.
  Qed.
  Lemma max_prefix_of_snd_alt l1 l2 k1 k2 k3 :
    max_prefix_of l1 l2 = (k1, k2, k3) → l2 = k3 ++ k2.
  Proof.
    intro. pose proof (max_prefix_of_snd l1 l2).
    by destruct (max_prefix_of l1 l2) as [[]?]; simplify_equality.
  Qed.
  Lemma max_prefix_of_snd_prefix l1 l2 : (max_prefix_of l1 l2).2 `prefix_of` l2.
  Proof. eexists. apply max_prefix_of_snd. Qed.
  Lemma max_prefix_of_snd_prefix_alt l1 l2 k1 k2 k3 :
    max_prefix_of l1 l2 = (k1,k2,k3) → k3 `prefix_of` l2.
  Proof. eexists. eauto using max_prefix_of_snd_alt. Qed.
  Lemma max_prefix_of_max l1 l2 k :
    k `prefix_of` l1 → k `prefix_of` l2 → k `prefix_of` (max_prefix_of l1 l2).2.
  Proof.
    intros [l1' ->] [l2' ->]. by induction k; simpl; repeat case_decide;
      simpl; auto using prefix_of_nil, prefix_of_cons.
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
    intros Hl ->. destruct (prefix_of_snoc_not k3 x2).
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
Proof. intros [k ->]. exists k. by rewrite (associative_L (++)). Qed.
Lemma suffix_of_snoc_alt x y l1 l2 :
  x = y → l1 `suffix_of` l2 → l1 ++ [x] `suffix_of` l2 ++ [y].
Proof. intros ->. apply suffix_of_snoc. Qed.
Lemma suffix_of_app l1 l2 k : l1 `suffix_of` l2 → l1 ++ k `suffix_of` l2 ++ k.
Proof. intros [k' ->]. exists k'. by rewrite (associative_L (++)). Qed.
Lemma suffix_of_app_alt l1 l2 k1 k2 :
  k1 = k2 → l1 `suffix_of` l2 → l1 ++ k1 `suffix_of` l2 ++ k2.
Proof. intros ->. apply suffix_of_app. Qed.
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
Proof. intros [k ->]. exists (k ++ [x]). by rewrite <-(associative_L (++)). Qed.
Lemma suffix_of_app_l l1 l2 l3 : l3 ++ l1 `suffix_of` l2 → l1 `suffix_of` l2.
Proof. intros [k ->]. exists (k ++ l3). by rewrite <-(associative_L (++)). Qed.
Lemma suffix_of_cons_r l1 l2 x : l1 `suffix_of` l2 → l1 `suffix_of` x :: l2.
Proof. intros [k ->]. by exists (x :: k). Qed.
Lemma suffix_of_app_r l1 l2 l3 : l1 `suffix_of` l2 → l1 `suffix_of` l3 ++ l2.
Proof. intros [k ->]. exists (l3 ++ k). by rewrite (associative_L (++)). Qed.
Lemma suffix_of_cons_inv l1 l2 x y :
  x :: l1 `suffix_of` y :: l2 → x :: l1 = y :: l2 ∨ x :: l1 `suffix_of` l2.
Proof.
  intros [[|? k] E]; [by left|].
  right. simplify_equality. by apply suffix_of_app_r.
Qed.
Lemma suffix_of_length l1 l2 : l1 `suffix_of` l2 → length l1 ≤ length l2.
Proof. intros [? ->]. rewrite app_length. lia. Qed.
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
    l1 = (max_suffix_of l1 l2).1.1 ++ (max_suffix_of l1 l2).2.
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
  Lemma max_suffix_of_fst_suffix l1 l2 : (max_suffix_of l1 l2).2 `suffix_of` l1.
  Proof. eexists. apply max_suffix_of_fst. Qed.
  Lemma max_suffix_of_fst_suffix_alt l1 l2 k1 k2 k3 :
    max_suffix_of l1 l2 = (k1, k2, k3) → k3 `suffix_of` l1.
  Proof. eexists. eauto using max_suffix_of_fst_alt. Qed.
  Lemma max_suffix_of_snd l1 l2 :
    l2 = (max_suffix_of l1 l2).1.2 ++ (max_suffix_of l1 l2).2.
  Proof.
    rewrite <-(reverse_involutive l2) at 1.
    rewrite (max_prefix_of_snd (reverse l1) (reverse l2)). unfold max_suffix_of.
    destruct (max_prefix_of (reverse l1) (reverse l2)) as ((?&?)&?); simpl.
    by rewrite reverse_app.
  Qed.
  Lemma max_suffix_of_snd_alt l1 l2 k1 k2 k3 :
    max_suffix_of l1 l2 = (k1,k2,k3) → l2 = k2 ++ k3.
  Proof.
    intro. pose proof (max_suffix_of_snd l1 l2).
    by destruct (max_suffix_of l1 l2) as [[]?]; simplify_equality.
  Qed.
  Lemma max_suffix_of_snd_suffix l1 l2 : (max_suffix_of l1 l2).2 `suffix_of` l2.
  Proof. eexists. apply max_suffix_of_snd. Qed.
  Lemma max_suffix_of_snd_suffix_alt l1 l2 k1 k2 k3 :
    max_suffix_of l1 l2 = (k1,k2,k3) → k3 `suffix_of` l2.
  Proof. eexists. eauto using max_suffix_of_snd_alt. Qed.
  Lemma max_suffix_of_max l1 l2 k :
    k `suffix_of` l1 → k `suffix_of` l2 → k `suffix_of` (max_suffix_of l1 l2).2.
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
    intros Hl ->. destruct (suffix_of_cons_not x2 k3).
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
Proof. split. by inversion 1. intros ->. constructor. Qed.
Lemma sublist_app l1 l2 k1 k2 :
  l1 `sublist` l2 → k1 `sublist` k2 → l1 ++ k1 `sublist` l2 ++ k2.
Proof. induction 1; simpl; try constructor; auto. Qed.
Lemma sublist_inserts_l k l1 l2 : l1 `sublist` l2 → l1 `sublist` k ++ l2.
Proof. induction k; try constructor; auto. Qed.
Lemma sublist_inserts_r k l1 l2 : l1 `sublist` l2 → l1 `sublist` l2 ++ k.
Proof. induction 1; simpl; try constructor; auto using sublist_nil_l. Qed.
Lemma sublist_cons_r x l k :
  l `sublist` x :: k ↔ l `sublist` k ∨ ∃ l', l = x :: l' ∧ l' `sublist` k.
Proof. split. inversion 1; eauto. intros [?|(?&->&?)]; constructor; auto. Qed.
Lemma sublist_cons_l x l k :
  x :: l `sublist` k ↔ ∃ k1 k2, k = k1 ++ x :: k2 ∧ l `sublist` k2.
Proof.
  split.
  * intros Hlk. induction k as [|y k IH]; inversion Hlk.
    + eexists [], k. by repeat constructor.
    + destruct IH as (k1&k2&->&?); auto. by exists (y :: k1) k2.
  * intros (k1&k2&->&?). by apply sublist_inserts_l, sublist_skip.
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
      exists l1 l2. auto using sublist_cons.
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
  apply IH. rewrite Hk. eauto using sublist_inserts_l, sublist_cons.
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
      eauto using sublist_inserts_l, sublist_cons.
  * intros l1 l2 Hl12 Hl21. apply sublist_length in Hl21.
    induction Hl12; f_equal'; auto with arith.
    apply sublist_length in Hl12. lia.
Qed.
Lemma sublist_take l i : take i l `sublist` l.
Proof. rewrite <-(take_drop i l) at 2. by apply sublist_inserts_r. Qed.
Lemma sublist_drop l i : drop i l `sublist` l.
Proof. rewrite <-(take_drop i l) at 2. by apply sublist_inserts_l. Qed.
Lemma sublist_delete l i : delete i l `sublist` l.
Proof. revert i. by induction l; intros [|?]; simpl; constructor. Qed.
Lemma sublist_foldr_delete l is : foldr delete l is `sublist` l.
Proof.
  induction is as [|i is IH]; simpl; [done |].
  transitivity (foldr delete l is); auto using sublist_delete.
Qed.
Lemma sublist_alt l1 l2 : l1 `sublist` l2 ↔ ∃ is, l1 = foldr delete l2 is.
Proof.
  split; [|intros [is ->]; apply sublist_foldr_delete].
  intros Hl12. cut (∀ k, ∃ is, k ++ l1 = foldr delete (k ++ l2) is).
  { intros help. apply (help []). }
  induction Hl12 as [|x l1 l2 _ IH|x l1 l2 _ IH]; intros k.
  * by eexists [].
  * destruct (IH (k ++ [x])) as [is His]. exists is.
    by rewrite <-!(associative_L (++)) in His.
  * destruct (IH k) as [is His]. exists (is ++ [length k]).
    rewrite fold_right_app. simpl. by rewrite delete_middle.
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
  split; [|intros ->; constructor].
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
Lemma contains_Permutation l1 l2 : l1 `contains` l2 → ∃ k, l2 ≡ₚ l1 ++ k.
Proof.
  induction 1 as
    [|x y l ? [k Hk]| |x l1 l2 ? [k Hk]|l1 l2 l3 ? [k Hk] ? [k' Hk']].
  * by eexists [].
  * exists k. by rewrite Hk.
  * eexists []. rewrite (right_id_L [] (++)). by constructor.
  * exists (x :: k). by rewrite Hk, Permutation_middle.
  * exists (k ++ k'). by rewrite Hk', Hk, (associative_L (++)).
Qed.
Lemma contains_Permutation_length_le l1 l2 :
  length l2 ≤ length l1 → l1 `contains` l2 → l1 ≡ₚ l2.
Proof.
  intros Hl21 Hl12. destruct (contains_Permutation l1 l2) as [[|??] Hk]; auto.
  * by rewrite Hk, (right_id_L [] (++)).
  * rewrite Hk, app_length in Hl21; simpl in Hl21; lia.
Qed.
Lemma contains_Permutation_length_eq l1 l2 :
  length l2 = length l1 → l1 `contains` l2 → l1 ≡ₚ l2.
Proof. intro. apply contains_Permutation_length_le. lia. Qed.
Global Instance: Proper ((≡ₚ) ==> (≡ₚ) ==> iff) (@contains A).
Proof.
  intros l1 l2 ? k1 k2 ?. split; intros.
  * transitivity l1. by apply Permutation_contains.
    transitivity k1. done. by apply Permutation_contains.
  * transitivity l2. by apply Permutation_contains.
    transitivity k2. done. by apply Permutation_contains.
Qed.
Global Instance: AntiSymmetric (≡ₚ) (@contains A).
Proof. red. auto using contains_Permutation_length_le, contains_length. Qed.
Lemma contains_take l i : take i l `contains` l.
Proof. auto using sublist_take, sublist_contains. Qed.
Lemma contains_drop l i : drop i l `contains` l.
Proof. auto using sublist_drop, sublist_contains. Qed.
Lemma contains_delete l i : delete i l `contains` l.
Proof. auto using sublist_delete, sublist_contains. Qed.
Lemma contains_foldr_delete l is : foldr delete l is `sublist` l.
Proof. auto using sublist_foldr_delete, sublist_contains. Qed.
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
  split.
  * by intros Hl; rewrite Hl.
  * intros [??]; auto using contains_Permutation_length_eq.
Qed.

Lemma NoDup_contains l k : NoDup l → (∀ x, x ∈ l → x ∈ k) → l `contains` k.
Proof.
  intros Hl. revert k. induction Hl as [|x l Hx ? IH].
  { intros k Hk. by apply contains_nil_l. }
  intros k Hlk. destruct (elem_of_list_split k x) as (l1&l2&?); subst.
  { apply Hlk. by constructor. }
  rewrite <-Permutation_middle. apply contains_skip, IH.
  intros y Hy. rewrite elem_of_app.
  specialize (Hlk y). rewrite elem_of_app, !elem_of_cons in Hlk.
  by destruct Hlk as [?|[?|?]]; subst; eauto.
Qed.
Lemma NoDup_Permutation l k : NoDup l → NoDup k → (∀ x, x ∈ l ↔ x ∈ k) → l ≡ₚ k.
Proof.
  intros. apply (anti_symmetric contains); apply NoDup_contains; naive_solver.
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
    * simplify_option_equality; eauto using Permutation_swap.
    * destruct (IH1 k1) as (k2&?&?); trivial.
      destruct (IH2 k2) as (k3&?&?); trivial.
      exists k3. split; eauto. by transitivity k2.
  Qed.
  Lemma list_remove_Some l k x : list_remove x l = Some k → l ≡ₚ x :: k.
  Proof.
    revert k. induction l as [|y l IH]; simpl; intros k ?; [done |].
    simplify_option_equality; auto. by rewrite Permutation_swap, <-IH.
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
End more_general_properties.

(** ** Properties of the [Forall] and [Exists] predicate *)
Lemma Forall_Exists_dec {A} {P Q : A → Prop} (dec : ∀ x, {P x} + {Q x}) :
  ∀ l, {Forall P l} + {Exists Q l}.
Proof.
 refine (
  fix go l :=
  match l return {Forall P l} + {Exists Q l} with
  | [] => left _
  | x :: l => cast_if_and (dec x) (go l)
  end); clear go; intuition.
Defined.

Section Forall_Exists.
  Context {A} (P : A → Prop).

  Definition Forall_nil_2 := @Forall_nil A.
  Definition Forall_cons_2 := @Forall_cons A.
  Lemma Forall_forall l : Forall P l ↔ ∀ x, x ∈ l → P x.
  Proof.
    split; [induction 1; inversion 1; subst; auto|].
    intros Hin; induction l as [|x l IH]; constructor; [apply Hin; constructor|].
    apply IH. intros ??. apply Hin. by constructor.
  Qed.
  Lemma Forall_nil : Forall P [] ↔ True.
  Proof. done. Qed.
  Lemma Forall_cons_1 x l : Forall P (x :: l) → P x ∧ Forall P l.
  Proof. by inversion 1. Qed.
  Lemma Forall_cons x l : Forall P (x :: l) ↔ P x ∧ Forall P l.
  Proof. split. by inversion 1. intros [??]. by constructor. Qed.
  Lemma Forall_singleton x : Forall P [x] ↔ P x.
  Proof. rewrite Forall_cons, Forall_nil; tauto. Qed.
  Lemma Forall_app_2 l1 l2 : Forall P l1 → Forall P l2 → Forall P (l1 ++ l2).
  Proof. induction 1; simpl; auto. Qed.
  Lemma Forall_app l1 l2 : Forall P (l1 ++ l2) ↔ Forall P l1 ∧ Forall P l2.
  Proof.
    split; [induction l1; inversion 1; intuition|].
    intros [??]; auto using Forall_app_2.
  Qed.
  Lemma Forall_true l : (∀ x, P x) → Forall P l.
  Proof. induction l; auto. Qed.
  Lemma Forall_impl (Q : A → Prop) l :
    Forall P l → (∀ x, P x → Q x) → Forall Q l.
  Proof. intros H ?. induction H; auto. Defined.
  Global Instance Forall_proper:
    Proper (pointwise_relation _ (↔) ==> (=) ==> (↔)) (@Forall A).
  Proof. split; subst; induction 1; constructor (by firstorder auto). Qed.
  Lemma Forall_iff l (Q : A → Prop) :
    (∀ x, P x ↔ Q x) → Forall P l ↔ Forall Q l.
  Proof. intros H. apply Forall_proper. red; apply H. done. Qed.
  Lemma Forall_not l : length l ≠ 0 → Forall (not ∘ P) l → ¬Forall P l.
  Proof. by destruct 2; inversion 1. Qed.
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
    Forall P l → (∀ x, l!!i = Some x → P x → P (f x)) → Forall P (alter f i l).
  Proof.
    intros Hl. revert i. induction Hl; simpl; intros [|i]; constructor; auto.
  Qed.
  Lemma Forall_alter_inv f l i :
    Forall P (alter f i l) → (∀ x, l!!i = Some x → P (f x) → P x) → Forall P l.
  Proof. 
    revert i. induction l; intros [|?]; simpl;
      inversion_clear 1; constructor; eauto.
  Qed.
  Lemma Forall_replicate n x : P x → Forall P (replicate n x).
  Proof. induction n; simpl; constructor; auto. Qed.
  Lemma Forall_replicate_eq n (x : A) : Forall (x =) (replicate n x).
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
  Lemma Forall_resize_inv n x l :
    length l ≤ n → Forall P (resize n x l) → Forall P l.
  Proof. intros ?. rewrite resize_ge, Forall_app by done. by intros []. Qed.
  Lemma Forall_sublist_lookup l i n k :
    sublist_lookup i n l = Some k → Forall P l → Forall P k.
  Proof.
    unfold sublist_lookup. intros; simplify_option_equality.
    auto using Forall_take, Forall_drop.
  Qed.
  Lemma Forall_sublist_alter f l i n k :
    Forall P l → sublist_lookup i n l = Some k → Forall P (f k) →
    Forall P (sublist_alter f i n l).
  Proof.
    unfold sublist_alter, sublist_lookup. intros; simplify_option_equality.
    auto using Forall_app_2, Forall_drop, Forall_take.
  Qed.
  Lemma Forall_sublist_alter_inv f l i n k :
    sublist_lookup i n l = Some k →
    Forall P (sublist_alter f i n l) → Forall P (f k).
  Proof.
    unfold sublist_alter, sublist_lookup. intros ?; simplify_option_equality.
    rewrite !Forall_app; tauto.
  Qed.
  Lemma Forall_reshape l szs : Forall P l → Forall (Forall P) (reshape szs l).
  Proof.
    revert l. induction szs; simpl; auto using Forall_take, Forall_drop.
  Qed.
  Lemma Forall_rev_ind (Q : list A → Prop) :
    Q [] → (∀ x l, P x → Forall P l → Q l → Q (l ++ [x])) →
    ∀ l, Forall P l → Q l.
  Proof.
    intros ?? l. induction l using rev_ind; auto.
    rewrite Forall_app, Forall_singleton; intros [??]; auto.
  Qed.
  Lemma Exists_exists l : Exists P l ↔ ∃ x, x ∈ l ∧ P x.
  Proof.
    split.
    * induction 1 as [x|y ?? [x [??]]]; exists x; by repeat constructor.
    * intros [x [Hin ?]]. induction l; [by destruct (not_elem_of_nil x)|].
      inversion Hin; subst. by left. right; auto.
  Qed.
  Lemma Exists_inv x l : Exists P (x :: l) → P x ∨ Exists P l.
  Proof. inversion 1; intuition trivial. Qed.
  Lemma Exists_app l1 l2 : Exists P (l1 ++ l2) ↔ Exists P l1 ∨ Exists P l2.
  Proof.
    split.
    * induction l1; inversion 1; intuition.
    * intros [H|H]; [induction H | induction l1]; simpl; intuition.
  Qed.
  Lemma Exists_impl (Q : A → Prop) l :
    Exists P l → (∀ x, P x → Q x) → Exists Q l.
  Proof. intros H ?. induction H; auto. Defined.
  Global Instance Exists_proper:
    Proper (pointwise_relation _ (↔) ==> (=) ==> (↔)) (@Exists A).
  Proof. split; subst; induction 1; constructor (by firstorder auto). Qed.
  Lemma Exists_not_Forall l : Exists (not ∘ P) l → ¬Forall P l.
  Proof. induction 1; inversion_clear 1; contradiction. Qed.
  Lemma Forall_not_Exists l : Forall (not ∘ P) l → ¬Exists P l.
  Proof. induction 1; inversion_clear 1; contradiction. Qed.

  Lemma Forall_list_difference `{∀ x y : A, Decision (x = y)} l k :
    Forall P l → Forall P (list_difference l k).
  Proof.
    rewrite !Forall_forall.
    intros ? x; rewrite elem_of_list_difference; naive_solver.
  Qed.
  Lemma Forall_list_union `{∀ x y : A, Decision (x = y)} l k :
    Forall P l → Forall P k → Forall P (list_union l k).
  Proof. intros. apply Forall_app; auto using Forall_list_difference. Qed.
  Lemma Forall_list_intersection `{∀ x y : A, Decision (x = y)} l k :
    Forall P l → Forall P (list_intersection l k).
  Proof.
    rewrite !Forall_forall.
    intros ? x; rewrite elem_of_list_intersection; naive_solver.
  Qed.

  Context {dec : ∀ x, Decision (P x)}.
  Lemma not_Forall_Exists l : ¬Forall P l → Exists (not ∘ P) l.
  Proof. intro. destruct (Forall_Exists_dec dec l); intuition. Qed.
  Lemma not_Exists_Forall l : ¬Exists P l → Forall (not ∘ P) l.
  Proof. by destruct (Forall_Exists_dec (λ x, swap_if (decide (P x))) l). Qed.
  Global Instance Forall_dec l : Decision (Forall P l) :=
    match Forall_Exists_dec dec l with
    | left H => left H
    | right H => right (Exists_not_Forall _ H)
    end.
  Global Instance Exists_dec l : Decision (Exists P l) :=
    match Forall_Exists_dec (λ x, swap_if (decide (P x))) l with
    | left H => right (Forall_not_Exists _ H)
    | right H => left H
    end.
End Forall_Exists.

Lemma replicate_as_Forall {A} (x : A) n l :
  replicate n x = l ↔ length l = n ∧ Forall (x =) l.
Proof. rewrite replicate_as_elem_of, Forall_forall. naive_solver. Qed.
Lemma replicate_as_Forall_2 {A} (x : A) n l :
  length l = n → Forall (x =) l → replicate n x = l.
Proof. by rewrite replicate_as_Forall. Qed.

Lemma Forall_swap {A B} (Q : A → B → Prop) l1 l2 :
  Forall (λ y, Forall (Q y) l1) l2 ↔ Forall (λ x, Forall (flip Q x) l2) l1.
Proof. repeat setoid_rewrite Forall_forall. simpl. split; eauto. Qed.
Lemma Forall_seq (P : nat → Prop) i n :
  Forall P (seq i n) ↔ ∀ j, i ≤ j < i + n → P j.
Proof.
  rewrite Forall_lookup. split.
  * intros H j [??]. apply (H (j - i)).
    rewrite lookup_seq; auto with f_equal lia.
  * intros H j x Hj. apply lookup_seq_inv in Hj.
    destruct Hj; subst. auto with lia.
Qed.

(** ** Properties of the [Forall2] predicate *)
Section Forall2.
  Context {A B} (P : A → B → Prop).
  Implicit Types x : A.
  Implicit Types y : B.
  Implicit Types l : list A.
  Implicit Types k : list B.

  Lemma Forall2_true l k :
    (∀ x y, P x y) → length l = length k → Forall2 P l k.
  Proof.
    intro. revert k. induction l; intros [|??] ?; simplify_equality'; auto.
  Qed.
  Lemma Forall2_same_length l k :
    Forall2 (λ _ _, True) l k ↔ length l = length k.
  Proof.
    split; [by induction 1; f_equal'|].
    revert k. induction l; intros [|??] ?; simplify_equality'; auto.
  Qed.
  Lemma Forall2_length l k : Forall2 P l k → length l = length k.
  Proof. by induction 1; f_equal'. Qed.
  Lemma Forall2_length_l l k n : Forall2 P l k → length l = n → length k = n.
  Proof. intros ? <-; symmetry. by apply Forall2_length. Qed.
  Lemma Forall2_length_r l k n : Forall2 P l k → length k = n → length l = n.
  Proof. intros ? <-. by apply Forall2_length. Qed.
  Lemma Forall2_nil_inv_l k : Forall2 P [] k → k = [].
  Proof. by inversion 1. Qed.
  Lemma Forall2_nil_inv_r l : Forall2 P l [] → l = [].
  Proof. by inversion 1. Qed.
  Lemma Forall2_cons_inv x l y k :
    Forall2 P (x :: l) (y :: k) → P x y ∧ Forall2 P l k.
  Proof. by inversion 1. Qed.
  Lemma Forall2_cons_inv_l x l k :
    Forall2 P (x :: l) k → ∃ y k', P x y ∧ Forall2 P l k' ∧ k = y :: k'.
  Proof. inversion 1; subst; eauto. Qed.
  Lemma Forall2_cons_inv_r l k y :
    Forall2 P l (y :: k) → ∃ x l', P x y ∧ Forall2 P l' k ∧ l = x :: l'.
  Proof. inversion 1; subst; eauto. Qed.
  Lemma Forall2_cons_nil_inv x l : Forall2 P (x :: l) [] → False.
  Proof. by inversion 1. Qed.
  Lemma Forall2_nil_cons_inv y k : Forall2 P [] (y :: k) → False.
  Proof. by inversion 1. Qed.
  Lemma Forall2_app_l l1 l2 k :
    Forall2 P l1 (take (length l1) k) → Forall2 P l2 (drop (length l1) k) →
    Forall2 P (l1 ++ l2) k.
  Proof. intros. rewrite <-(take_drop (length l1) k). by apply Forall2_app. Qed.
  Lemma Forall2_app_r l k1 k2 :
    Forall2 P (take (length k1) l) k1 → Forall2 P (drop (length k1) l) k2 →
    Forall2 P l (k1 ++ k2).
  Proof. intros. rewrite <-(take_drop (length k1) l). by apply Forall2_app. Qed.
  Lemma Forall2_app_inv l1 l2 k1 k2 :
    length l1 = length k1 →
    Forall2 P (l1 ++ l2) (k1 ++ k2) → Forall2 P l1 k1 ∧ Forall2 P l2 k2.
  Proof.
    rewrite <-Forall2_same_length. induction 1; inversion 1; naive_solver.
  Qed.
  Lemma Forall2_app_inv_l l1 l2 k :
    Forall2 P (l1 ++ l2) k ↔
      ∃ k1 k2, Forall2 P l1 k1 ∧ Forall2 P l2 k2 ∧ k = k1 ++ k2.
  Proof.
    split; [|intros (?&?&?&?&->); by apply Forall2_app].
    revert k. induction l1; inversion 1; naive_solver.
  Qed.
  Lemma Forall2_app_inv_r l k1 k2 :
    Forall2 P l (k1 ++ k2) ↔
      ∃ l1 l2, Forall2 P l1 k1 ∧ Forall2 P l2 k2 ∧ l = l1 ++ l2.
  Proof.
    split; [|intros (?&?&?&?&->); by apply Forall2_app].
    revert l. induction k1; inversion 1; naive_solver.
  Qed.
  Lemma Forall2_flip l k : Forall2 (flip P) k l ↔ Forall2 P l k.
  Proof. split; induction 1; constructor; auto. Qed.
  Lemma Forall2_impl (Q : A → B → Prop) l k :
    Forall2 P l k → (∀ x y, P x y → Q x y) → Forall2 Q l k.
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
  Lemma Forall2_lookup_lr l k i x y :
    Forall2 P l k → l !! i = Some x → k !! i = Some y → P x y.
  Proof.
    intros H. revert i. induction H; intros [|?] ??; simplify_equality'; eauto.
  Qed.
  Lemma Forall2_lookup_l l k i x :
    Forall2 P l k → l !! i = Some x → ∃ y, k !! i = Some y ∧ P x y.
  Proof.
    intros H. revert i. induction H; intros [|?] ?; simplify_equality'; eauto.
  Qed.
  Lemma Forall2_lookup_r l k i y :
    Forall2 P l k → k !! i = Some y → ∃ x, l !! i = Some x ∧ P x y.
  Proof.
    intros H. revert i. induction H; intros [|?] ?; simplify_equality'; eauto.
  Qed.
  Lemma Forall2_lookup_2 l k :
    length l = length k →
    (∀ i x y, l !! i = Some x → k !! i = Some y → P x y) → Forall2 P l k.
  Proof.
    rewrite <-Forall2_same_length. intros Hl Hlookup.
    induction Hl as [|?????? IH]; constructor; [by apply (Hlookup 0)|].
    apply IH. apply (λ i, Hlookup (S i)).
  Qed.
  Lemma Forall2_lookup l k :
    Forall2 P l k ↔ length l = length k ∧
      (∀ i x y, l !! i = Some x → k !! i = Some y → P x y).
  Proof.
    naive_solver eauto using Forall2_length, Forall2_lookup_lr,Forall2_lookup_2.
  Qed.
  Lemma Forall2_alter_l f l k i :
    Forall2 P l k →
    (∀ x y, l !! i = Some x → k !! i = Some y → P x y → P (f x) y) →
    Forall2 P (alter f i l) k.
  Proof. intros Hl. revert i. induction Hl; intros [|]; constructor; auto. Qed.
  Lemma Forall2_alter_r f l k i :
    Forall2 P l k →
    (∀ x y, l !! i = Some x → k !! i = Some y → P x y → P x (f y)) →
    Forall2 P l (alter f i k).
  Proof. intros Hl. revert i. induction Hl; intros [|]; constructor; auto. Qed.
  Lemma Forall2_alter f g l k i :
    Forall2 P l k →
    (∀ x y, l !! i = Some x → k !! i = Some y → P x y → P (f x) (g y)) →
    Forall2 P (alter f i l) (alter g i k).
  Proof. intros Hl. revert i. induction Hl; intros [|]; constructor; auto. Qed.
  Lemma Forall2_insert l k x y i :
    Forall2 P l k → P x y → Forall2 P (<[i:=x]> l) (<[i:=y]> k).
  Proof. intros Hl. revert i. induction Hl; intros [|]; constructor; auto. Qed.
  Lemma Forall2_delete l k i :
    Forall2 P l k → Forall2 P (delete i l) (delete i k).
  Proof. intros Hl. revert i. induction Hl; intros [|]; simpl; intuition. Qed.
  Lemma Forall2_replicate_l k n x :
    length k = n → Forall (P x) k → Forall2 P (replicate n x) k.
  Proof. intros <-. induction 1; simpl; auto. Qed.
  Lemma Forall2_replicate_r l n y :
    length l = n → Forall (flip P y) l → Forall2 P l (replicate n y).
  Proof. intros <-. induction 1; simpl; auto. Qed.
  Lemma Forall2_replicate n x y :
    P x y → Forall2 P (replicate n x) (replicate n y).
  Proof. induction n; simpl; constructor; auto. Qed.
  Lemma Forall2_take l k n : Forall2 P l k → Forall2 P (take n l) (take n k).
  Proof. intros Hl. revert n. induction Hl; intros [|?]; simpl; auto. Qed.
  Lemma Forall2_drop l k n : Forall2 P l k → Forall2 P (drop n l) (drop n k).
  Proof. intros Hl. revert n. induction Hl; intros [|?]; simpl; auto. Qed.
  Lemma Forall2_resize l k x y n :
    P x y → Forall2 P l k → Forall2 P (resize n x l) (resize n y k).
  Proof.
    intros. rewrite !resize_spec, (Forall2_length l k) by done.
    auto using Forall2_app, Forall2_take, Forall2_replicate.
  Qed.
  Lemma Forall2_resize_ge_l l k x y n m :
    P x y → Forall (flip P y) l → n ≤ m →
    Forall2 P (resize n x l) k → Forall2 P (resize m x l) (resize m y k).
  Proof.
    intros. assert (n = length k) as ->.
    { by rewrite <-(Forall2_length (resize n x l) k), resize_length. }
    rewrite (le_plus_minus (length k) m), !resize_plus, resize_all,
      drop_all, resize_nil by done; auto using Forall2_app, Forall2_replicate_r,
      Forall_resize, Forall_drop, resize_length.
  Qed.
  Lemma Forall2_resize_ge_r l k x y n m :
    P x y → Forall (P x) k → n ≤ m →
    Forall2 P l (resize n y k) → Forall2 P (resize m x l) (resize m y k).
  Proof.
    intros. assert (n = length l) as ->.
    { by rewrite (Forall2_length l (resize n y k)), resize_length. }
    rewrite (le_plus_minus (length l) m), !resize_plus, resize_all,
      drop_all, resize_nil by done; auto using Forall2_app, Forall2_replicate_l,
      Forall_resize, Forall_drop, resize_length.
  Qed.
  Lemma Forall2_sublist_lookup_l l k n i l' :
    Forall2 P l k → sublist_lookup n i l = Some l' →
    ∃ k', sublist_lookup n i k = Some k' ∧ Forall2 P l' k'.
  Proof.
    unfold sublist_lookup. intros Hlk Hl.
    exists (take i (drop n k)); simplify_option_equality.
    * auto using Forall2_take, Forall2_drop.
    * apply Forall2_length in Hlk; lia.
  Qed.
  Lemma Forall2_sublist_lookup_r l k n i k' :
    Forall2 P l k → sublist_lookup n i k = Some k' →
    ∃ l', sublist_lookup n i l = Some l' ∧ Forall2 P l' k'.
  Proof.
    intro. unfold sublist_lookup.
    erewrite Forall2_length by eauto; intros; simplify_option_equality.
    eauto using Forall2_take, Forall2_drop.
  Qed.
  Lemma Forall2_sublist_alter f g l k i n l' k' :
    Forall2 P l k → sublist_lookup i n l = Some l' →
    sublist_lookup i n k = Some k' → Forall2 P (f l') (g k') →
    Forall2 P (sublist_alter f i n l) (sublist_alter g i n k).
  Proof.
    intro. unfold sublist_alter, sublist_lookup.
    erewrite Forall2_length by eauto; intros; simplify_option_equality.
    auto using Forall2_app, Forall2_drop, Forall2_take.
  Qed.
  Lemma Forall2_sublist_alter_l f l k i n l' k' :
    Forall2 P l k → sublist_lookup i n l = Some l' →
    sublist_lookup i n k = Some k' → Forall2 P (f l') k' →
    Forall2 P (sublist_alter f i n l) k.
  Proof.
    intro. unfold sublist_lookup, sublist_alter.
    erewrite <-Forall2_length by eauto; intros; simplify_option_equality.
    apply Forall2_app_l;
      rewrite ?take_length_le by lia; auto using Forall2_take.
    apply Forall2_app_l; erewrite Forall2_length, take_length,
      drop_length, <-Forall2_length, Min.min_l by eauto with lia; [done|].
    rewrite drop_drop; auto using Forall2_drop.
  Qed.
  Lemma Forall2_transitive {C} (Q : B → C → Prop) (R : A → C → Prop) l k lC :
    (∀ x y z, P x y → Q y z → R x z) →
    Forall2 P l k → Forall2 Q k lC → Forall2 R l lC.
  Proof. intros ? Hl. revert lC. induction Hl; inversion_clear 1; eauto. Qed.
  Lemma Forall2_Forall (Q : A → A → Prop) l :
    Forall (λ x, Q x x) l → Forall2 Q l l.
  Proof. induction 1; constructor; auto. Qed.
  Global Instance Forall2_dec `{dec : ∀ x y, Decision (P x y)} :
    ∀ l k, Decision (Forall2 P l k).
  Proof.
   refine (
    fix go l k : Decision (Forall2 P l k) :=
    match l, k with
    | [], [] => left _
    | x :: l, y :: k => cast_if_and (decide (P x y)) (go l k)
    | _, _ => right _
    end); clear dec go; abstract first [by constructor | by inversion 1].
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
End Forall2_order.

Section Forall3.
  Context {A B C} (P : A → B → C → Prop).
  Lemma Forall3_app l1 k1 k1' l2 k2 k2' :
    Forall3 P l1 k1 k1' → Forall3 P l2 k2 k2' →
    Forall3 P (l1 ++ l2) (k1 ++ k2) (k1' ++ k2').
  Proof. induction 1; simpl; [done|constructor]; auto. Qed.
  Lemma Forall3_impl (Q : A → B → C → Prop) l l' k :
    Forall3 P l l' k → (∀ x y z, P x y z → Q x y z) → Forall3 Q l l' k.
  Proof. intros Hl ?. induction Hl; constructor; auto. Defined.
  Lemma Forall3_length_lm l l' k : Forall3 P l l' k → length l = length l'.
  Proof. by induction 1; f_equal'. Qed.
  Lemma Forall3_lookup_lmr l l' k i x y z :
    Forall3 P l l' k →
    l !! i = Some x → l' !! i = Some y → k !! i = Some z → P x y z.
  Proof.
    intros H. revert i. induction H; intros [|?] ???; simplify_equality'; eauto.
  Qed.
  Lemma Forall3_lookup_l l l' k i x :
    Forall3 P l l' k → l !! i = Some x →
    ∃ y z, l' !! i = Some y ∧ k !! i = Some z ∧ P x y z.
  Proof.
    intros H. revert i. induction H; intros [|?] ?; simplify_equality'; eauto.
  Qed.
  Lemma Forall3_lookup_m l l' k i y :
    Forall3 P l l' k → l' !! i = Some y →
    ∃ x z, l !! i = Some x ∧ k !! i = Some z ∧ P x y z.
  Proof.
    intros H. revert i. induction H; intros [|?] ?; simplify_equality'; eauto.
  Qed.
  Lemma Forall3_lookup_r l l' k i z :
    Forall3 P l l' k → k !! i = Some z →
    ∃ x y, l !! i = Some x ∧ l' !! i = Some y ∧ P x y z.
  Proof.
    intros H. revert i. induction H; intros [|?] ?; simplify_equality'; eauto.
  Qed.
  Lemma Forall3_alter_lm f g l l' k i :
    Forall3 P l l' k →
    (∀ x y z, l !! i = Some x → l' !! i = Some y → k !! i = Some z →
      P x y z → P (f x) (g y) z) →
    Forall3 P (alter f i l) (alter g i l') k.
  Proof. intros Hl. revert i. induction Hl; intros [|]; constructor; auto. Qed.
End Forall3.

(** * Properties of the monadic operations *)
Section fmap.
  Context {A B : Type} (f : A → B).

  Lemma list_fmap_id (l : list A) : id <$> l = l.
  Proof. induction l; f_equal'; auto. Qed.
  Lemma list_fmap_compose {C} (g : B → C) l : g ∘ f <$> l = g <$> f <$> l.
  Proof. induction l; f_equal'; auto. Qed.
  Lemma list_fmap_ext (g : A → B) (l1 l2 : list A) :
    (∀ x, f x = g x) → l1 = l2 → fmap f l1 = fmap g l2.
  Proof. intros ? <-. induction l1; f_equal'; auto. Qed.
  Global Instance: Injective (=) (=) f → Injective (=) (=) (fmap f).
  Proof.
    intros ? l1. induction l1 as [|x l1 IH]; [by intros [|??]|].
    intros [|??]; intros; f_equal'; simplify_equality; auto.
  Qed.
  Definition fmap_nil : f <$> [] = [] := eq_refl.
  Definition fmap_cons x l : f <$> x :: l = f x :: f <$> l := eq_refl.
  Lemma fmap_app l1 l2 : f <$> l1 ++ l2 = (f <$> l1) ++ (f <$> l2).
  Proof. by induction l1; f_equal'. Qed.
  Lemma fmap_nil_inv k :  f <$> k = [] → k = [].
  Proof. by destruct k. Qed.
  Lemma fmap_cons_inv y l k :
    f <$> l = y :: k → ∃ x l', y = f x ∧ k = f <$> l' ∧ l = x :: l'.
  Proof. intros. destruct l; simplify_equality'; eauto. Qed.
  Lemma fmap_app_inv l k1 k2 :
    f <$> l = k1 ++ k2 → ∃ l1 l2, k1 = f <$> l1 ∧ k2 = f <$> l2 ∧ l = l1 ++ l2.
  Proof.
    revert l. induction k1 as [|y k1 IH]; simpl; [intros l ?; by eexists [],l|].
    intros [|x l] ?; simplify_equality'.
    destruct (IH l) as (l1&l2&->&->&->); [done|]. by exists (x :: l1) l2.
  Qed.
  Lemma fmap_length l : length (f <$> l) = length l.
  Proof. by induction l; f_equal'. Qed.
  Lemma fmap_reverse l : f <$> reverse l = reverse (f <$> l).
  Proof.
    induction l as [|?? IH]; csimpl; by rewrite ?reverse_cons, ?fmap_app, ?IH.
  Qed.
  Lemma fmap_last l : last (f <$> l) = f <$> last l.
  Proof. induction l as [|? []]; simpl; auto. Qed.
  Lemma fmap_replicate n x :  f <$> replicate n x = replicate n (f x).
  Proof. by induction n; f_equal'. Qed.
  Lemma fmap_take n l : f <$> take n l = take n (f <$> l).
  Proof. revert n. by induction l; intros [|?]; f_equal'. Qed.
  Lemma fmap_drop n l : f <$> drop n l = drop n (f <$> l).
  Proof. revert n. by induction l; intros [|?]; f_equal'. Qed.
  Lemma fmap_resize n x l : f <$> resize n x l = resize n (f x) (f <$> l).
  Proof.
    revert n. induction l; intros [|?]; f_equal'; auto using fmap_replicate.
  Qed.
  Lemma replicate_const_fmap (x : A) (l : list A) :
    const x <$> l = replicate (length l) x.
  Proof. by induction l; f_equal'. Qed.
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
  Proof. intros Hl. revert i. by induction Hl; intros [|i]; f_equal'. Qed.
  Lemma elem_of_list_fmap_1 l x : x ∈ l → f x ∈ f <$> l.
  Proof. induction 1; csimpl; rewrite elem_of_cons; intuition. Qed.
  Lemma elem_of_list_fmap_1_alt l x y : x ∈ l → y = f x → y ∈ f <$> l.
  Proof. intros. subst. by apply elem_of_list_fmap_1. Qed.
  Lemma elem_of_list_fmap_2 l x : x ∈ f <$> l → ∃ y, x = f y ∧ y ∈ l.
  Proof.
    induction l as [|y l IH]; simpl; inversion_clear 1.
    * exists y. split; [done | by left].
    * destruct IH as [z [??]]. done. exists z. split; [done | by right].
  Qed.
  Lemma elem_of_list_fmap l x : x ∈ f <$> l ↔ ∃ y, x = f y ∧ y ∈  l.
  Proof.
    naive_solver eauto using elem_of_list_fmap_1_alt, elem_of_list_fmap_2.
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
  Lemma Forall_fmap_ext_1 (g : A → B) (l : list A) :
    Forall (λ x, f x = g x) l → fmap f l = fmap g l.
  Proof. by induction 1; f_equal'. Qed.
  Lemma Forall_fmap_ext (g : A → B) (l : list A) :
    Forall (λ x, f x = g x) l ↔ fmap f l = fmap g l.
  Proof.
    split; [auto using Forall_fmap_ext_1|].
    induction l; simpl; constructor; simplify_equality; auto.
  Qed.
  Lemma Forall_fmap (P : B → Prop) l : Forall P (f <$> l) ↔ Forall (P ∘ f) l.
  Proof. split; induction l; inversion_clear 1; constructor; auto. Qed.
  Lemma Exists_fmap (P : B → Prop) l : Exists P (f <$> l) ↔ Exists (P ∘ f) l.
  Proof. split; induction l; inversion 1; constructor (by auto). Qed.
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
  Proof. induction 1; csimpl; auto. Qed.
  Lemma Forall2_fmap {C D} (g : C → D) (P : B → D → Prop) l1 l2 :
    Forall2 P (f <$> l1) (g <$> l2) ↔ Forall2 (λ x1 x2, P (f x1) (g x2)) l1 l2.
  Proof. split; auto using Forall2_fmap_1, Forall2_fmap_2. Qed.
  Lemma list_fmap_bind {C} (g : B → list C) l : (f <$> l) ≫= g = l ≫= g ∘ f.
  Proof. by induction l; f_equal'. Qed.
End fmap.

Lemma list_alter_fmap_mono {A} (f : A → A) (g : A → A) l i :
  Forall (λ x, f (g x) = g (f x)) l → f <$> alter g i l = alter g i (f <$> l).
Proof. auto using list_alter_fmap. Qed.
Lemma NoDup_fmap_fst {A B} (l : list (A * B)) :
  (∀ x y1 y2, (x,y1) ∈ l → (x,y2) ∈ l → y1 = y2) → NoDup l → NoDup (fst <$> l).
Proof.
  intros Hunique. induction 1 as [|[x1 y1] l Hin Hnodup IH]; csimpl; constructor.
  * rewrite elem_of_list_fmap.
    intros [[x2 y2] [??]]; simpl in *; subst. destruct Hin.
    rewrite (Hunique x2 y1 y2); rewrite ?elem_of_cons; auto.
  * apply IH. intros. eapply Hunique; rewrite ?elem_of_cons; eauto.
Qed.

Section bind.
  Context {A B : Type} (f : A → list B).

  Lemma list_bind_ext (g : A → list B) l1 l2 :
    (∀ x, f x = g x) → l1 = l2 → l1 ≫= f = l2 ≫= g.
  Proof. intros ? <-. by induction l1; f_equal'. Qed.
  Lemma Forall_bind_ext (g : A → list B) (l : list A) :
    Forall (λ x, f x = g x) l → l ≫= f = l ≫= g.
  Proof. by induction 1; f_equal'. Qed.
  Global Instance bind_sublist: Proper (sublist ==> sublist) (mbind f).
  Proof.
    induction 1; simpl; auto;
      [by apply sublist_app|by apply sublist_inserts_l].
  Qed.
  Global Instance bind_contains: Proper (contains ==> contains) (mbind f).
  Proof.
    induction 1; csimpl; auto.
    * by apply contains_app.
    * by rewrite !(associative_L (++)), (commutative (++) (f _)).
    * by apply contains_inserts_l.
    * etransitivity; eauto.
  Qed.
  Global Instance bind_Permutation: Proper ((≡ₚ) ==> (≡ₚ)) (mbind f).
  Proof.
    induction 1; csimpl; auto.
    * by f_equiv.
    * by rewrite !(associative_L (++)), (commutative (++) (f _)).
    * etransitivity; eauto.
  Qed.
  Lemma bind_cons x l : (x :: l) ≫= f = f x ++ l ≫= f.
  Proof. done. Qed.
  Lemma bind_singleton x : [x] ≫= f = f x.
  Proof. csimpl. by rewrite (right_id_L _ (++)). Qed.
  Lemma bind_app l1 l2 : (l1 ++ l2) ≫= f = (l1 ≫= f) ++ (l2 ≫= f).
  Proof. by induction l1; csimpl; rewrite <-?(associative_L (++)); f_equal. Qed.
  Lemma elem_of_list_bind (x : B) (l : list A) :
    x ∈ l ≫= f ↔ ∃ y, x ∈ f y ∧ y ∈ l.
  Proof.
    split.
    * induction l as [|y l IH]; csimpl; [inversion 1|].
      rewrite elem_of_app. intros [?|?].
      + exists y. split; [done | by left].
      + destruct IH as [z [??]]. done. exists z. split; [done | by right].
    * intros [y [Hx Hy]]. induction Hy; csimpl; rewrite elem_of_app; intuition.
  Qed.
  Lemma Forall_bind (P : B → Prop) l :
    Forall P (l ≫= f) ↔ Forall (Forall P ∘ f) l.
  Proof.
    split.
    * induction l; csimpl; rewrite ?Forall_app; constructor; csimpl; intuition.
    * induction 1; csimpl; rewrite ?Forall_app; auto.
  Qed.
  Lemma Forall2_bind {C D} (g : C → list D) (P : B → D → Prop) l1 l2 :
    Forall2 (λ x1 x2, Forall2 P (f x1) (g x2)) l1 l2 →
    Forall2 P (l1 ≫= f) (l2 ≫= g).
  Proof. induction 1; csimpl; auto using Forall2_app. Qed.
End bind.

Section ret_join.
  Context {A : Type}.

  Lemma list_join_bind (ls : list (list A)) : mjoin ls = ls ≫= id.
  Proof. by induction ls; f_equal'. Qed.
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
    split; [|by induction 1 as [|[|??] ?]].
    by induction ls as [|[|??] ?]; constructor; auto.
  Qed.
  Lemma join_nil_1 (ls : list (list A)) : mjoin ls = [] → Forall (= []) ls.
  Proof. by rewrite join_nil. Qed.
  Lemma join_nil_2 (ls : list (list A)) : Forall (= []) ls → mjoin ls = [].
  Proof. by rewrite join_nil. Qed.
  Lemma Forall_join (P : A → Prop) (ls: list (list A)) :
    Forall (Forall P) ls → Forall P (mjoin ls).
  Proof. induction 1; simpl; auto using Forall_app_2. Qed.
  Lemma Forall2_join {B} (P : A → B → Prop) ls1 ls2 :
    Forall2 (Forall2 P) ls1 ls2 → Forall2 P (mjoin ls1) (mjoin ls2).
  Proof. induction 1; simpl; auto using Forall2_app. Qed.
End ret_join.

Section mapM.
  Context {A B : Type} (f : A → option B).

  Lemma mapM_ext (g : A → option B) l : (∀ x, f x = g x) → mapM f l = mapM g l.
  Proof. intros Hfg. by induction l; simpl; rewrite ?Hfg, ?IHl. Qed.
  Lemma Forall2_mapM_ext (g : A → option B) l k :
    Forall2 (λ x y, f x = g y) l k → mapM f l = mapM g k.
  Proof. induction 1 as [|???? Hfg ? IH]; simpl. done. by rewrite Hfg, IH. Qed.
  Lemma Forall_mapM_ext (g : A → option B) l :
    Forall (λ x, f x = g x) l → mapM f l = mapM g l.
  Proof. induction 1 as [|?? Hfg ? IH]; simpl. done. by rewrite Hfg, IH. Qed.
  Lemma mapM_Some_1 l k : mapM f l = Some k → Forall2 (λ x y, f x = Some y) l k.
  Proof.
    revert k. induction l as [|x l]; intros [|y k]; simpl; try done.
    * destruct (f x); simpl; [|discriminate]. by destruct (mapM f l).
    * destruct (f x) eqn:?; simpl; [|discriminate].
      destruct (mapM f l); intros; simplify_equality. constructor; auto.
  Qed.
  Lemma mapM_Some_2 l k : Forall2 (λ x y, f x = Some y) l k → mapM f l = Some k.
  Proof.
    induction 1 as [|???? Hf ? IH]; simpl; [done |].
    rewrite Hf. simpl. by rewrite IH.
  Qed.
  Lemma mapM_Some l k : mapM f l = Some k ↔ Forall2 (λ x y, f x = Some y) l k.
  Proof. split; auto using mapM_Some_1, mapM_Some_2. Qed.
  Lemma mapM_length l k : mapM f l = Some k → length l = length k.
  Proof. intros. by eapply Forall2_length, mapM_Some_1. Qed.
  Lemma mapM_None_1 l : mapM f l = None → Exists (λ x, f x = None) l.
  Proof.
    induction l as [|x l IH]; simpl; [done|].
    destruct (f x) eqn:?; simpl; eauto. by destruct (mapM f l); eauto.
  Qed.
  Lemma mapM_None_2 l : Exists (λ x, f x = None) l → mapM f l = None.
  Proof.
    induction 1 as [x l Hx|x l ? IH]; simpl; [by rewrite Hx|].
    by destruct (f x); simpl; rewrite ?IH.
  Qed.
  Lemma mapM_None l : mapM f l = None ↔ Exists (λ x, f x = None) l.
  Proof. split; auto using mapM_None_1, mapM_None_2. Qed.
  Lemma mapM_is_Some_1 l : is_Some (mapM f l) → Forall (is_Some ∘ f) l.
  Proof.
    unfold compose. setoid_rewrite <-not_eq_None_Some.
    rewrite mapM_None. apply (not_Exists_Forall _).
  Qed.
  Lemma mapM_is_Some_2 l : Forall (is_Some ∘ f) l → is_Some (mapM f l).
  Proof.
    unfold compose. setoid_rewrite <-not_eq_None_Some.
    rewrite mapM_None. apply (Forall_not_Exists _).
  Qed.
  Lemma mapM_is_Some l : is_Some (mapM f l) ↔ Forall (is_Some ∘ f) l.
  Proof. split; auto using mapM_is_Some_1, mapM_is_Some_2. Qed.
  Lemma mapM_fmap_Some (g : B → A) (l : list B) :
    (∀ x, f (g x) = Some x) → mapM f (g <$> l) = Some l.
  Proof. intros. by induction l; simpl; simplify_option_equality. Qed.
  Lemma mapM_fmap_Some_inv (g : B → A) (l : list B) (k : list A) :
    (∀ x y, f y = Some x → y = g x) → mapM f k = Some l → k = g <$> l.
  Proof.
    intros Hgf. revert l; induction k as [|??]; intros [|??] ?;
      simplify_option_equality; f_equiv; eauto.
  Qed.
End mapM.

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
    * rewrite elem_of_list_singleton. by intros ->.
    * rewrite elem_of_cons, elem_of_list_fmap. intros [->|[? [-> H]]]; [done|].
      rewrite (IH _ H). constructor.
  Qed.
  Lemma permutations_refl l : l ∈ permutations l.
  Proof.
    induction l; simpl; [by apply elem_of_list_singleton|].
    apply elem_of_list_bind. eauto using interleave_cons.
  Qed.
  Lemma permutations_skip x l l' :
    l ∈ permutations l' → x :: l ∈ permutations (x :: l').
  Proof. intro. apply elem_of_list_bind; eauto using interleave_cons. Qed.
  Lemma permutations_swap x y l : y :: x :: l ∈ permutations (x :: y :: l).
  Proof.
    simpl. apply elem_of_list_bind. exists (y :: l). split; simpl.
    * destruct l; csimpl; rewrite !elem_of_cons; auto.
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
    { rewrite !elem_of_list_singleton. intros ? ->. exists [x1].
      change (interleave x2 [x1]) with ([[x2; x1]] ++ [[x1; x2]]).
      by rewrite (commutative (++)), elem_of_list_singleton. }
    rewrite elem_of_cons, elem_of_list_fmap.
    intros Hl1 [? | [l2' [??]]]; simplify_equality'.
    * rewrite !elem_of_cons, elem_of_list_fmap in Hl1.
      destruct Hl1 as [? | [? | [l4 [??]]]]; subst.
      + exists (x1 :: y :: l3). csimpl. rewrite !elem_of_cons. tauto.
      + exists (x1 :: y :: l3). csimpl. rewrite !elem_of_cons. tauto.
      + exists l4. simpl. rewrite elem_of_cons. auto using interleave_cons.
    * rewrite elem_of_cons, elem_of_list_fmap in Hl1.
      destruct Hl1 as [? | [l1' [??]]]; subst.
      + exists (x1 :: y :: l3). csimpl.
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
    { rewrite elem_of_list_singleton. intros Hl1 ->. eexists [].
      by rewrite elem_of_list_singleton. }
    rewrite elem_of_cons, elem_of_list_fmap.
    intros Hl1 [? | [l2' [? Hl2']]]; simplify_equality'.
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
    * rewrite !elem_of_list_singleton. intros Hl1 ->; simpl in *.
      by rewrite elem_of_list_singleton in Hl1.
    * rewrite !elem_of_list_bind. intros Hl1 [l2' [Hl2 Hl2']].
      destruct (permutations_interleave_toggle x l1 l2 l2') as [? [??]]; eauto.
  Qed.
  Lemma permutations_Permutation l l' : l' ∈ permutations l ↔ l ≡ₚ l'.
  Proof.
    split.
    * revert l'. induction l; simpl; intros l''.
      + rewrite elem_of_list_singleton. by intros ->.
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
Proof. induction 1; simpl; [done|by f_equiv|apply Hf|etransitivity; eauto]. Qed.

(** ** Properties of the [zip_with] and [zip] functions *)
Section zip_with.
  Context {A B C : Type} (f : A → B → C).
  Implicit Types x : A.
  Implicit Types y : B.
  Implicit Types l : list A.
  Implicit Types k : list B.

  Lemma zip_with_nil_r l : zip_with f l [] = [].
  Proof. by destruct l. Qed.
  Lemma zip_with_app l1 l2 k1 k2 :
    length l1 = length k1 →
    zip_with f (l1 ++ l2) (k1 ++ k2) = zip_with f l1 k1 ++ zip_with f l2 k2.
  Proof. rewrite <-Forall2_same_length. induction 1; f_equal'; auto. Qed.
  Lemma zip_with_app_l l1 l2 k :
    zip_with f (l1 ++ l2) k
    = zip_with f l1 (take (length l1) k) ++ zip_with f l2 (drop (length l1) k).
  Proof.
    revert k. induction l1; intros [|??]; f_equal'; auto. by destruct l2.
  Qed.
  Lemma zip_with_app_r l k1 k2 :
    zip_with f l (k1 ++ k2)
    = zip_with f (take (length k1) l) k1 ++ zip_with f (drop (length k1) l) k2.
  Proof. revert l. induction k1; intros [|??]; f_equal'; auto. Qed.
  Lemma zip_with_flip l k : zip_with (flip f) k l =  zip_with f l k.
  Proof. revert k. induction l; intros [|??]; f_equal'; auto. Qed.
  Lemma zip_with_ext (g : A → B → C) l1 l2 k1 k2 :
    (∀ x y, f x y = g x y) → l1 = l2 → k1 = k2 →
    zip_with f l1 k1 = zip_with g l2 k2.
  Proof. intros ? <-<-. revert k1. by induction l1; intros [|??]; f_equal'. Qed.
  Lemma Forall_zip_with_ext_l (g : A → B → C) l k1 k2 :
    Forall (λ x, ∀ y, f x y = g x y) l → k1 = k2 →
    zip_with f l k1 = zip_with g l k2.
  Proof. intros Hl <-. revert k1. by induction Hl; intros [|??]; f_equal'. Qed.
  Lemma Forall_zip_with_ext_r (g : A → B → C) l1 l2 k :
    l1 = l2 → Forall (λ y, ∀ x, f x y = g x y) k →
    zip_with f l1 k = zip_with g l2 k.
  Proof. intros <- Hk. revert l1. by induction Hk; intros [|??]; f_equal'. Qed.
  Lemma zip_with_fmap_l {D} (g : D → A) lD k :
    zip_with f (g <$> lD) k = zip_with (λ z, f (g z)) lD k.
  Proof. revert k. by induction lD; intros [|??]; f_equal'. Qed.
  Lemma zip_with_fmap_r {D} (g : D → B) l kD :
    zip_with f l (g <$> kD) = zip_with (λ x z, f x (g z)) l kD.
  Proof. revert kD. by induction l; intros [|??]; f_equal'. Qed.
  Lemma zip_with_nil_inv l k : zip_with f l k = [] → l = [] ∨ k = [].
  Proof. destruct l, k; intros; simplify_equality'; auto. Qed.
  Lemma zip_with_cons_inv l k z lC :
    zip_with f l k = z :: lC →
    ∃ x y l' k', z = f x y ∧ lC = zip_with f l' k' ∧ l = x :: l' ∧ k = y :: k'.
  Proof. intros. destruct l, k; simplify_equality'; repeat eexists. Qed.
  Lemma zip_with_app_inv l k lC1 lC2 :
    zip_with f l k = lC1 ++ lC2 →
    ∃ l1 k1 l2 k2, lC1 = zip_with f l1 k1 ∧ lC2 = zip_with f l2 k2 ∧
      l = l1 ++ l2 ∧ k = k1 ++ k2 ∧ length l1 = length k1.
  Proof.
    revert l k. induction lC1 as [|z lC1 IH]; simpl.
    { intros l k ?. by eexists [], [], l, k. }
    intros [|x l] [|y k] ?; simplify_equality'.
    destruct (IH l k) as (l1&k1&l2&k2&->&->&->&->&?); [done |].
    exists (x :: l1) (y :: k1) l2 k2; simpl; auto with congruence.
  Qed.
  Lemma zip_with_inj `{!Injective2 (=) (=) (=) f} l1 l2 k1 k2 :
    length l1 = length k1 → length l2 = length k2 →
    zip_with f l1 k1 = zip_with f l2 k2 → l1 = l2 ∧ k1 = k2.
  Proof.
    rewrite <-!Forall2_same_length. intros Hl. revert l2 k2.
    induction Hl; intros ?? [] ?; f_equal; naive_solver.
  Qed.
  Lemma zip_with_length l k :
    length (zip_with f l k) = min (length l) (length k).
  Proof. revert k. induction l; intros [|??]; simpl; auto with lia. Qed.
  Lemma zip_with_length_l l k :
    length l ≤ length k → length (zip_with f l k) = length l.
  Proof. rewrite zip_with_length; lia. Qed.
  Lemma zip_with_length_r l k :
    length k ≤ length l → length (zip_with f l k) = length k.
  Proof. rewrite zip_with_length; lia. Qed.
  Lemma zip_with_length_same_l P l k :
    Forall2 P l k → length (zip_with f l k) = length l.
  Proof. induction 1; simpl; auto. Qed.
  Lemma zip_with_length_same_r P l k :
    Forall2 P l k → length (zip_with f l k) = length k.
  Proof. induction 1; simpl; auto. Qed.
  Lemma lookup_zip_with l k i :
    zip_with f l k !! i = x ← l !! i; y ← k !! i; Some (f x y).
  Proof.
    revert k i. induction l; intros [|??] [|?]; f_equal'; auto.
    by destruct (_ !! _).
  Qed.
  Lemma fmap_zip_with_l (g : C → A) l k :
    (∀ x y, g (f x y) = x) → length l ≤ length k → g <$> zip_with f l k = l.
  Proof. revert k. induction l; intros [|??] ??; f_equal'; auto with lia. Qed.
  Lemma fmap_zip_with_r (g : C → B) l k :
    (∀ x y, g (f x y) = y) → length k ≤ length l → g <$> zip_with f l k = k.
  Proof. revert l. induction k; intros [|??] ??; f_equal'; auto with lia. Qed.
  Lemma zip_with_zip l k : zip_with f l k = curry f <$> zip l k.
  Proof. revert k. by induction l; intros [|??]; f_equal'. Qed.
  Lemma zip_with_fst_snd lk :
    zip_with f (fst <$> lk) (snd <$> lk) = curry f <$> lk.
  Proof. by induction lk as [|[]]; f_equal'. Qed.
  Lemma zip_with_replicate_l n x k :
    length k ≤ n → zip_with f (replicate n x) k = f x <$> k.
  Proof. revert n. induction k; intros [|?] ?; f_equal'; auto with lia. Qed.
  Lemma zip_with_replicate_r n y l :
    length l ≤ n → zip_with f l (replicate n y) = flip f y <$> l.
  Proof. revert n. induction l; intros [|?] ?; f_equal'; auto with lia. Qed.
  Lemma zip_with_take n l k :
    take n (zip_with f l k) = zip_with f (take n l) (take n k).
  Proof. revert n k. by induction l; intros [|?] [|??]; f_equal'. Qed.
  Lemma zip_with_drop n l k :
    drop n (zip_with f l k) = zip_with f (drop n l) (drop n k).
  Proof.
    revert n k. induction l; intros [] []; f_equal'; auto using zip_with_nil_r.
  Qed.
  Lemma zip_with_take_l n l k :
    length k ≤ n → zip_with f (take n l) k = zip_with f l k.
  Proof. revert n k. induction l; intros [] [] ?; f_equal'; auto with lia. Qed.
  Lemma zip_with_take_r n l k :
    length l ≤ n → zip_with f l (take n k) = zip_with f l k.
  Proof. revert n k. induction l; intros [] [] ?; f_equal'; auto with lia. Qed.
  Lemma Forall_zip_with_fst (P : A → Prop) (Q : C → Prop) l k :
    Forall P l → Forall (λ y, ∀ x, P x → Q (f x y)) k →
    Forall Q (zip_with f l k).
  Proof. intros Hl. revert k. induction Hl; destruct 1; simpl in *; auto. Qed.
  Lemma Forall_zip_with_snd (P : B → Prop) (Q : C → Prop) l k :
    Forall (λ x, ∀ y, P y → Q (f x y)) l → Forall P k →
    Forall Q (zip_with f l k).
  Proof. intros Hl. revert k. induction Hl; destruct 1; simpl in *; auto. Qed.
End zip_with.

Lemma zip_with_sublist_alter {A B} (f : A → B → A) g l k i n l' k' :
  length l = length k →
  sublist_lookup i n l = Some l' → sublist_lookup i n k = Some k' →
  length (g l') = length k' → zip_with f (g l') k' = g (zip_with f l' k') →
  zip_with f (sublist_alter g i n l) k = sublist_alter g i n (zip_with f l k).
Proof.
  unfold sublist_lookup, sublist_alter. intros Hlen; rewrite Hlen.
  intros ?? Hl' Hk'. simplify_option_equality.
  by rewrite !zip_with_app_l, !zip_with_drop, Hl', drop_drop, !zip_with_take,
    !take_length_le, Hk' by (rewrite ?drop_length; auto with lia).
Qed.

Section zip.
  Context {A B : Type}.
  Implicit Types l : list A.
  Implicit Types k : list B.
  Lemma fst_zip l k : length l ≤ length k → fst <$> zip l k = l.
  Proof. by apply fmap_zip_with_l. Qed.
  Lemma snd_zip l k : length k ≤ length l → snd <$> zip l k = k.
  Proof. by apply fmap_zip_with_r. Qed.
  Lemma zip_fst_snd (lk : list (A * B)) : zip (fst <$> lk) (snd <$> lk) = lk.
  Proof. by induction lk as [|[]]; f_equal'. Qed.
  Lemma Forall2_fst P l1 l2 k1 k2 :
    length l2 = length k2 → Forall2 P l1 k1 → 
    Forall2 (λ x y, P (x.1) (y.1)) (zip l1 l2) (zip k1 k2).
  Proof.
    rewrite <-Forall2_same_length. intros Hlk2 Hlk1. revert l2 k2 Hlk2.
    induction Hlk1; intros ?? [|??????]; simpl; auto.
  Qed.
  Lemma Forall2_snd P l1 l2 k1 k2 :
    length l1 = length k1 → Forall2 P l2 k2 → 
    Forall2 (λ x y, P (x.2) (y.2)) (zip l1 l2) (zip k1 k2).
  Proof.
    rewrite <-Forall2_same_length. intros Hlk1 Hlk2. revert l1 k1 Hlk1.
    induction Hlk2; intros ?? [|??????]; simpl; auto.
  Qed.
End zip.

Lemma elem_of_zipped_map {A B} (f : list A → list A → A → B) l k x :
  x ∈ zipped_map f l k ↔
    ∃ k' k'' y, k = k' ++ [y] ++ k'' ∧ x = f (reverse k' ++ l) k'' y.
Proof.
  split.
  * revert l. induction k as [|z k IH]; simpl; intros l; inversion_clear 1.
    { by eexists [], k, z. }
    destruct (IH (z :: l)) as (k'&k''&y&->&->); [done |].
    eexists (z :: k'), k'', y. by rewrite reverse_cons, <-(associative_L (++)).
  * intros (k'&k''&y&->&->). revert l. induction k' as [|z k' IH]; [by left|].
    intros l; right. by rewrite reverse_cons, <-!(associative_L (++)).
Qed.
Section zipped_list_ind.
  Context {A} (P : list A → list A → Prop).
  Context (Pnil : ∀ l, P l []) (Pcons : ∀ l k x, P (x :: l) k → P l (x :: k)).
  Fixpoint zipped_list_ind l k : P l k :=
    match k with
    | [] => Pnil _ | x :: k => Pcons _ _ _ (zipped_list_ind (x :: l) k)
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
  rnil : rlist A | rnode : A → rlist A | rapp : rlist A → rlist A → rlist A.
Arguments rnil {_}.
Arguments rnode {_} _.
Arguments rapp {_} _ _.

Module rlist.
Fixpoint to_list {A} (t : rlist A) : list A :=
  match t with
  | rnil => [] | rnode l => [l] | rapp t1 t2 => to_list t1 ++ to_list t2
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
    induction t; csimpl.
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
    apply zip_with_app_inv in H; destruct H as (?&?&?&?&?&?&?&?&?)
  | H : _ ++ _ = zip_with _ _ _ |- _ => symmetry in H
  end.
Ltac decompose_Forall_hyps := repeat
  match goal with
  | H : Forall _ [] |- _ => clear H
  | H : Forall _ (_ :: _) |- _ => rewrite Forall_cons in H; destruct H
  | H : Forall _ (_ ++ _) |- _ => rewrite Forall_app in H; destruct H
  | H : Forall2 _ [] [] |- _ => clear H
  | H : Forall2 _ (_ :: _) [] |- _ => destruct (Forall2_cons_nil_inv _ _ _ H)
  | H : Forall2 _ [] (_ :: _) |- _ => destruct (Forall2_nil_cons_inv _ _ _ H)
  | H : Forall2 _ [] ?k |- _ => apply Forall2_nil_inv_l in H; subst k
  | H : Forall2 _ ?l [] |- _ => apply Forall2_nil_inv_r in H; subst l
  | H : Forall2 _ (_ :: _) (_ :: _) |- _ =>
    apply Forall2_cons_inv in H; destruct H
  | _ => progress simplify_equality'
  | H : Forall2 _ (_ :: _) ?k |- _ =>
    let k_hd := fresh k "_hd" in let k_tl := fresh k "_tl" in
    apply Forall2_cons_inv_l in H; destruct H as (k_hd&k_tl&?&?&->);
    rename k_tl into k
  | H : Forall2 _ ?l (_ :: _) |- _ =>
    let l_hd := fresh l "_hd" in let l_tl := fresh l "_tl" in
    apply Forall2_cons_inv_r in H; destruct H as (l_hd&l_tl&?&?&->);
    rename l_tl into l
  | H : Forall2 _ (_ ++ _) (_ ++ _) |- _ =>
    apply Forall2_app_inv in H; [destruct H | first 
      [by eauto using Forall2_length | by symmetry; eauto using Forall2_length]]
  | H : Forall2 _ (_ ++ _) ?k |- _ => first
    [ let k1 := fresh k "_1" in let k2 := fresh k "_2" in
      apply Forall2_app_inv_l in H; destruct H as (k1&k2&?&?&->)
    | apply Forall2_app_inv_l in H; destruct H as (?&?&?&?&?)]
  | H : Forall2 _ ?l (_ ++ _) |- _ => first
    [ let l1 := fresh l "_1" in let l2 := fresh l "_2" in
      apply Forall2_app_inv_r in H; destruct H as (l1&l2&?&?&->)
    | apply Forall2_app_inv_r in H; destruct H as (?&?&?&?&?) ]
  | H : Forall ?P ?l, H1 : ?l !! _ = Some ?x |- _ =>
    (* to avoid some stupid loops, not fool proof *)
    unless (P x) by auto using Forall_app_2, Forall_nil_2;
    let E := fresh in
    assert (P x) as E by (apply (Forall_lookup_1 P _ _ _ H H1)); lazy beta in E
  | H : Forall2 ?P ?l ?k |- _ =>
    lazymatch goal with
    | H1 : l !! ?i = Some ?x, H2 : k !! ?i = Some ?y |- _ =>
      unless (P x y) by done; let E := fresh in
      assert (P x y) as E by (by apply (Forall2_lookup_lr P l k i x y));
      lazy beta in E
    | H1 : l !! _ = Some ?x |- _ =>
      destruct (Forall2_lookup_l P _ _ _ _ H H1) as (?&?&?)
    | H2 : k !! _ = Some ?y |- _ =>
      destruct (Forall2_lookup_r P _ _ _ _ H H2) as (?&?&?)
    end
  | H : Forall3 ?P ?l ?l' ?k |- _ =>
    lazymatch goal with
    | H1:l !! ?i = Some ?x, H2:l' !! ?i = Some ?y, H3:k !! ?i = Some ?z |- _ =>
      unless (P x y z) by done; let E := fresh in
      assert (P x y z) as E by (by apply (Forall3_lookup_lmr P l l' k i x y z));
      lazy beta in E
    | H1 : l !! _ = Some ?x |- _ =>
      destruct (Forall3_lookup_l P _ _ _ _ _ H H1) as (?&?&?&?&?)
    | H2 : l' !! _ = Some ?y |- _ =>
      destruct (Forall3_lookup_m P _ _ _ _ _ H H2) as (?&?&?&?&?)
    | H3 : k !! _ = Some ?z |- _ =>
      destruct (Forall3_lookup_r P _ _ _ _ _ H H3) as (?&?&?&?&?)
    end
  end.
Ltac decompose_Forall := repeat
  match goal with
  | |- Forall _ _ => by apply Forall_true
  | |- Forall _ [] => constructor
  | |- Forall _ (_ :: _) => constructor
  | |- Forall _ (_ ++ _) => apply Forall_app_2
  | |- Forall _ (_ <$> _) => apply Forall_fmap
  | |- Forall _ (_ ≫= _) => apply Forall_bind
  | |- Forall2 _ _ _ => apply Forall2_Forall
  | |- Forall2 _ [] [] => constructor
  | |- Forall2 _ (_ :: _) (_ :: _) => constructor
  | |- Forall2 _ (_ ++ _) (_ ++ _) => first
    [ apply Forall2_app; [by decompose_Forall |]
    | apply Forall2_app; [| by decompose_Forall]]
  | |- Forall2 _ (_ <$> _) _ => apply Forall2_fmap_l
  | |- Forall2 _ _ (_ <$> _) => apply Forall2_fmap_r
  | _ => progress decompose_Forall_hyps
  | H : Forall _ (_ <$> _) |- _ => rewrite Forall_fmap in H
  | H : Forall _ (_ ≫= _) |- _ => rewrite Forall_bind in H
  | |- Forall _ _ =>
    apply Forall_lookup_2; intros ???; progress decompose_Forall_hyps
  | |- Forall2 _ _ _ =>
    apply Forall2_lookup_2; [by eauto using Forall2_length|];
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
