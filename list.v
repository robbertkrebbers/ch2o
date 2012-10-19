(* Copyright (c) 2012, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects general purpose definitions and theorems on lists that
are not in the Coq standard library. *)
Require Import Omega Permutation.
Require Export base decidable option.

Arguments length {_} _.
Arguments cons {_} _ _.
Arguments app {_} _ _.

Arguments Forall_nil {_ _}.
Arguments Forall_cons {_ _} _ _ _ _.
Arguments Exists_nil {_ _}.
Arguments Exists_cons {_ _} _ _.

Arguments In {_} _ _.
Arguments NoDup_nil {_}.
Arguments Permutation {_} _ _.

Notation tail := tl.
Notation take := firstn.
Notation drop := skipn.
Notation foldr := fold_right.
Notation foldl := fold_left.

Arguments take {_} !_ !_ /.
Arguments drop {_} !_ !_ /.

Notation take_drop := firstn_skipn.
Notation foldr_app := fold_right_app.
Notation foldl_app := fold_left_app.

Notation "(::)" := cons (only parsing) : C_scope.
Notation "( x ::)" := (cons x) (only parsing) : C_scope.
Notation "(:: l )" := (λ x, cons x l) (only parsing) : C_scope.
Notation "(++)" := app (only parsing) : C_scope.
Notation "( l ++)" := (app l) (only parsing) : C_scope.
Notation "(++ k )" := (λ l, app l k) (only parsing) : C_scope.

(** * General definitions *)
(** Looking up elements and updating elements in a list. *)
Global Instance list_lookup: Lookup nat list :=
  fix go A (i : nat) (l : list A) {struct l} : option A :=
  match l with
  | [] => None
  | x :: l =>
    match i with
    | 0 => Some x
    | S i => @lookup _ _ go _ i l
    end
  end.

Global Instance list_alter: Alter nat list :=
  fix go A (f : A → A) (i : nat) (l : list A) {struct l} :=
  match l with
  | [] => []
  | x :: l =>
    match i with
    | 0 => f x :: l
    | S i => x :: @alter _ _ go _ f i l
    end
  end.

Global Instance list_insert: Insert nat list := λ _ i x,
  alter (λ _, x) i.

Global Instance list_delete: Delete nat list :=
  fix go A (i : nat) (l : list A) {struct l} : list A :=
  match l with
  | [] => []
  | x :: l =>
    match i with
    | 0 => l
    | S i => x :: @delete _ _ go _ i l
    end
  end.

Tactic Notation "discriminate_list_equality" hyp(H) :=
  apply (f_equal length) in H;
  repeat (simpl in H || rewrite app_length in H);
  exfalso; omega.
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

(** * General theorems *)
Section general_properties.
Context {A : Type}.

Lemma list_eq (l1 l2 : list A) : (∀ i, l1 !! i = l2 !! i) → l1 = l2.
Proof.
  revert l2. induction l1; intros [|??] H.
  * done.
  * discriminate (H 0).
  * discriminate (H 0).
  * f_equal. by injection (H 0). apply IHl1. intro. apply (H (S _)).
Qed.

Lemma list_lookup_nil i : @nil A !! i = None.
Proof. by destruct i. Qed.
Lemma list_lookup_tail (l : list A) i : tail l !! i = l !! S i.
Proof. by destruct l. Qed.

Lemma list_lookup_Some_In (l : list A) i x : l !! i = Some x → In x l.
Proof.
  revert i. induction l; intros [|i] ?;
    simpl; simplify_equality; constructor (solve [eauto]).
Qed.

Lemma list_lookup_In_Some (l : list A) x : In x l → ∃ i, l !! i = Some x.
Proof.
  induction l; destruct 1; subst.
  * by exists 0.
  * destruct IHl as [i ?]; auto. by exists (S i).
Qed.
Lemma list_lookup_In (l : list A) x : In x l ↔ ∃ i, l !! i = Some x.
Proof. firstorder eauto using list_lookup_Some_In, list_lookup_In_Some. Qed.

Lemma list_lookup_middle (l1 l2 : list A) (x : A) :
  (l1 ++ x :: l2) !! length l1 = Some x.
Proof. by induction l1; simpl. Qed.

Lemma list_lookup_lt_length (l : list A) i : is_Some (l !! i) ↔ i < length l.
Proof.
  revert i. induction l.
  * split; by inversion 1.
  * intros [|?]; simpl.
    + split; auto with arith.
    + by rewrite <-NPeano.Nat.succ_lt_mono.
Qed.
Lemma list_lookup_weaken (l l' : list A) i x :
  l !! i = Some x → (l ++ l') !! i = Some x.
Proof. revert i. induction l. done. by intros []. Qed.

Lemma take_lookup i j (l : list A) :
  j < i → take i l !! j = l !! j.
Proof.
  revert i j. induction l; intros [|i] j ?; trivial.
  * by destruct (le_Sn_0 j).
  * destruct j; simpl; auto with arith.
Qed.

Lemma take_lookup_le i j (l : list A) :
  i ≤ j → take i l !! j = None.
Proof.
  revert i j. induction l; intros [|i] [|j] ?; trivial.
  * by destruct (le_Sn_0 i).
  * simpl; auto with arith.
Qed.

Lemma drop_lookup i j (l : list A) :
  drop i l !! j = l !! (i + j).
Proof. revert i j. induction l; intros [|i] ?; simpl; auto. Qed.

Lemma list_lookup_alter (f : A → A) i l : alter f i l !! i = f <$> l !! i.
Proof. revert i. induction l. done. intros [|i]. done. apply (IHl i). Qed.
Lemma list_lookup_alter_ne (f : A → A) i j l :
  i ≠ j → alter f i l !! j = l !! j.
Proof.
  revert i j. induction l; [done|].
  intros [|i] [|j] ?; try done. apply (IHl i). congruence.
Qed.

Lemma take_alter (f : A → A) i j l :
  i ≤ j → take i (alter f j l) = take i l.
Proof.
  intros. apply list_eq. intros jj. destruct (le_lt_dec i jj).
  * by rewrite !take_lookup_le.
  * by rewrite !take_lookup, !list_lookup_alter_ne by omega.
Qed.
Lemma take_insert i j (x : A) l :
  i ≤ j → take i (<[j:=x]>l) = take i l.
Proof take_alter _ _ _ _.

Lemma drop_alter (f : A → A) i j l :
  j < i → drop i (alter f j l) = drop i l.
Proof.
  intros. apply list_eq. intros jj.
  by rewrite !drop_lookup, !list_lookup_alter_ne by omega.
Qed.
Lemma drop_insert i j (x : A) l :
  j < i → drop i (<[j:=x]>l) = drop i l.
Proof drop_alter _ _ _ _.

Lemma foldr_permutation {B} (f : A → B → B) (b : B) :
  (∀ a1 a2 b, f a1 (f a2 b) = f a2 (f a1 b)) →
  Proper (Permutation ==> (=)) (foldr f b).
Proof. intro. induction 1; simpl; congruence. Qed.

Lemma Forall_cons_inv (P : A → Prop) x l :
  Forall P (x :: l) → P x ∧ Forall P l.
Proof. by inversion_clear 1. Qed.

Lemma Forall_app (P : A → Prop) l1 l2 :
  Forall P (l1 ++ l2) ↔ Forall P l1 ∧ Forall P l2.
Proof.
  split.
   induction l1; inversion 1; intuition.
  intros [H ?]. induction H; simpl; intuition.
Qed.

Lemma Forall_true (P : A → Prop) l :
  (∀ x, P x) → Forall P l.
Proof. induction l; auto. Qed.
Lemma Forall_impl (P Q : A → Prop) l :
  Forall P l → (∀ x, P x → Q x) → Forall Q l.
Proof. induction 1; auto. Qed.
Lemma Forall_delete (P : A → Prop) l i :
  Forall P l → Forall P (delete i l).
Proof.
  intros H. revert i.
  by induction H; intros [|i]; try constructor.
Qed.

Lemma Forall2_length {B} (P : A → B → Prop) l1 l2 :
  Forall2 P l1 l2 → length l1 = length l2.
Proof. induction 1; simpl; auto. Qed.

Lemma Forall2_impl {B} (P Q : A → B → Prop) l1 l2 :
  Forall2 P l1 l2 → (∀ x y, P x y → Q x y) → Forall2 Q l1 l2.
Proof. induction 1; auto. Qed.

Lemma Forall2_unique {B} (P : A → B → Prop) l k1 k2 :
  Forall2 P l k1 →
  Forall2 P l k2 →
  (∀ x y1 y2, P x y1 → P x y2 → y1 = y2) →
  k1 = k2.
Proof.
  intros H. revert k2. induction H; inversion_clear 1; intros; f_equal; eauto.
Qed.

Lemma NoDup_singleton (x : A) : NoDup [x].
Proof. constructor. intros []. constructor. Qed.
Lemma NoDup_app (l k : list A) :
  NoDup l → NoDup k → (∀ x, In x l → ¬In x k) → NoDup (l ++ k).
Proof.
  induction 1; simpl.
  * done.
  * constructor; rewrite ?in_app_iff; firstorder.
Qed.

Global Instance: ∀ k : list A, Injective (=) (=) (k ++).
Proof. intros ???. apply app_inv_head. Qed.
Global Instance: ∀ k : list A, Injective (=) (=) (++ k).
Proof. intros ???. apply app_inv_tail. Qed.

Lemma in_nil_inv (l : list A) : (∀ x, ¬In x l) → l = [].
Proof. destruct l. done. by edestruct 1; constructor. Qed.
Lemma nil_length (l : list A) : length l = 0 → l = [].
Proof. by destruct l. Qed.
Lemma NoDup_inv_1 (x : A) (l : list A) : NoDup (x :: l) → ¬In x l.
Proof. by inversion_clear 1. Qed.
Lemma NoDup_inv_2 (x : A) (l : list A) : NoDup (x :: l) → NoDup l.
Proof. by inversion_clear 1. Qed.
Lemma Forall_inv_2 (P : A → Prop) x l : Forall P (x :: l) → Forall P l.
Proof. by inversion 1. Qed.
Lemma Exists_inv (P : A → Prop) x l : Exists P (x :: l) → P x ∨ Exists P l.
Proof. inversion 1; intuition trivial. Qed.

Definition reverse (l : list A) : list A := rev_append l [].

Lemma reverse_nill : reverse [] = [].
Proof. done. Qed.
Lemma reverse_cons x l : reverse (x :: l) = reverse l ++ [x].
Proof. unfold reverse. by rewrite <-!rev_alt. Qed.
Lemma reverse_snoc x l : reverse (l ++ [x]) = x :: reverse l.
Proof. unfold reverse. by rewrite <-!rev_alt, rev_unit. Qed.
Lemma reverse_app l1 l2 : reverse (l1 ++ l2) = reverse l2 ++ reverse l1.
Proof. unfold reverse. rewrite <-!rev_alt. apply rev_app_distr. Qed.
Lemma reverse_length l : length (reverse l) = length l.
Proof. unfold reverse. rewrite <-!rev_alt. apply rev_length. Qed.
Lemma reverse_involutive l : reverse (reverse l) = l.
Proof. unfold reverse. rewrite <-!rev_alt. apply rev_involutive. Qed. 

Global Instance list_eq_dec {dec : ∀ x y : A, Decision (x = y)} : ∀ l k,
  Decision (l = k) := list_eq_dec dec.
Global Instance In_dec {dec : ∀ x y : A, Decision (x = y)} : ∀ x l,
  Decision (In x l) := in_dec dec.

Global Instance NoDup_dec {dec : ∀ x y : A, Decision (x = y)} :
    ∀ (l : list A), Decision (NoDup l) :=
  fix NoDup_dec l :=
  match l return Decision (NoDup l) with
  | [] => left NoDup_nil
  | x :: l =>
    match In_dec x l with
    | left Hin => right (λ H, NoDup_inv_1 _ _ H Hin)
    | right Hin =>
      match NoDup_dec l with
      | left H => left (NoDup_cons _ Hin H)
      | right H => right (H ∘ NoDup_inv_2 _ _)
      end
    end
  end.

Section Forall_Exists.
Context (P : A → Prop).

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

Global Instance prefix_of_dec `{∀ x y : A, Decision (x = y)} :
    ∀ l1 l2, Decision (prefix_of l1 l2) :=
  fix prefix_of_dec l1 l2 :=
  match l1, l2 return { prefix_of l1 l2 } + { ¬prefix_of l1 l2 } with
  | [], _ => left (prefix_of_nil _)
  | _, [] => right (prefix_of_nil_not _ _)
  | x :: l1, y :: l2 =>
    match decide_rel (=) x y with
    | left Exy =>
      match prefix_of_dec l1 l2 with
      | left Hl1l2 => left (prefix_of_cons _ _ _ _ Exy Hl1l2)
      | right Hl1l2 => right (Hl1l2 ∘ prefix_of_cons_inv_2 _ _ _ _)
      end
    | right Exy => right (Exy ∘ prefix_of_cons_inv_1 _ _ _ _)
    end
  end.

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

Global Instance suffix_of_dec `{∀ x y : A, Decision (x = y)} (l1 l2 : list A) :
  Decision (suffix_of l1 l2).
Proof.
  refine (cast_if (decide_rel prefix_of (reverse l1) (reverse l2)));
   abstract (by rewrite suffix_prefix_reverse).
Defined.
End prefix_postfix.

(** The [simplify_suffix_of] removes [suffix_of] hypotheses that are
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

(** The [solve_suffix_of] tries to solve goals involving [suffix_of]. It uses
[simplify_suffix_of] to simplify hypotheses and tries to solve [suffix_of]
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

(** * Monadic operations *)
Global Instance list_fmap {A B} (f : A → B) : FMap list f :=
  fix go (l : list A) :=
  match l with
  | [] => []
  | x :: l => f x :: @fmap _ _ _ f go l
  end.
Global Instance list_join {A} : MJoin list :=
  fix go (l : list (list A)) : list A :=
  match l with
  | [] =>  []
  | x :: l => x ++ @mjoin _ _ go l
  end.
Global Instance list_bind {A B} (f : A → list B) : MBind list f := λ l,
  mjoin (f <$> l).

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

  Lemma in_fmap_1 l x : In x l → In (f x) (f <$> l).
  Proof. induction l; destruct 1; subst; constructor (solve [auto]). Qed.
  Lemma in_fmap_1_alt l x y : In x l → y = f x → In y (f <$> l).
  Proof. intros. subst. by apply in_fmap_1. Qed.
  Lemma in_fmap_2 l x : In x (f <$> l) → ∃ y, x = f y ∧ In y l.
  Proof.
    induction l as [|y l]; destruct 1; subst.
    * exists y; by intuition.
    * destruct IHl as [y' [??]]. done. exists y'; intuition.
  Qed.
  Lemma in_fmap l x : In x (f <$> l) ↔ ∃ y, x = f y ∧ In y l.
  Proof.
    split.
    * apply in_fmap_2.
    * intros [? [??]]. eauto using in_fmap_1_alt.
  Qed.

  Lemma Forall_fmap (l : list A) (P : B → Prop) :
    Forall (P ∘ f) l ↔ Forall P (f <$> l).
  Proof. induction l; split; inversion_clear 1; constructor; firstorder auto. Qed.
End list_fmap.

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
    setoid_rewrite list_lookup_lt_length.
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

Notation zip := (zip_with pair).

Section zip.
  Context {A B : Type}.

  Lemma zip_fst_le (l1 : list A) (l2 : list B) :
    length l1 ≤ length l2 → fst <$> zip l1 l2 = l1.
  Proof.
    revert l2.
    induction l1; intros [|??] ?; simpl; f_equal; auto with arith.
    edestruct Le.le_Sn_0; eauto.
  Qed.
  Lemma zip_fst (l1 : list A) (l2 : list B) :
    same_length l1 l2 → fst <$> zip l1 l2 = l1.
  Proof.
    rewrite same_length_length. intros H.
    apply zip_fst_le. by rewrite H.
  Qed.

  Lemma zip_snd_le (l1 : list A) (l2 : list B) :
    length l2 ≤ length l1 → snd <$> zip l1 l2 = l2.
  Proof.
    revert l2.
    induction l1; intros [|??] ?; simpl; f_equal; auto with arith.
    edestruct Le.le_Sn_0; eauto.
  Qed.
  Lemma zip_snd (l1 : list A) (l2 : list B) :
    same_length l1 l2 → snd <$> zip l1 l2 = l2.
  Proof.
    rewrite same_length_length. intros H.
    apply zip_snd_le. by rewrite H.
  Qed.
End zip.

Definition zipped_map {A B} (f : list A → list A → A → B) :
    list A → list A → list B :=
  fix go l k :=
  match k with
  | [] => []
  | x :: k => f l k x :: go (x :: l) k
  end.

Lemma In_zipped_map {A B} (f : list A → list A → A → B) l k x :
  In x (zipped_map f l k) ↔
    ∃ k' k'' y, k = k' ++ [y] ++ k'' ∧ x = f (reverse k' ++ l) k'' y.
Proof.
  split.
  * revert l. induction k as [|z k IH]; [done | intros l [?|?]]; subst.
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
