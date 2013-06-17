(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file defines a type [frag A] to represent symbolic fragments of a
data type [A]. The representation of [x : A] as a list of [n] fragments is:
"frag 0 of x", ..., "frag n of x".  We provide functions to ``split'' an
element of type [A] into fragments, and to go back. Fragments are used to
describe abstract fragments of pointers so as to encode and decode pointers as
bytes in the file [pointers]. *)
Require Export numbers list.

Record frag (A : Type) := Frag { frag_item : A; frag_index : nat }.
Add Printing Constructor frag.
Arguments Frag {_} _ _.
Arguments frag_item {_} _.
Arguments frag_index {_} _.

Section fragmented.
Context {A : Type} `{∀ x y : A, Decision (x = y)}.
Context (len : nat) {len_pos : PropHolds (len ≠ 0)}.

Global Instance frag_eq_dec (s1 s2 : frag A) : Decision (s1 = s2).
Proof. solve_decision. Defined.

Inductive fragmented (x : A) : nat → list (frag A) → Prop :=
  | fragmented_nil : fragmented x len []
  | fragmented_cons i xss :
     fragmented x (S i) xss → fragmented x i (Frag x i :: xss).

Global Instance fragmented_dec x : ∀ i xss, Decision (fragmented x i xss).
Proof.
 refine (
  fix go i xss :=
  match xss with
  | [] => cast_if (decide_rel (=) len i)
  | Frag y j :: pss =>
     cast_if_and3 (decide_rel (=) i j) (decide_rel (=) x y) (go (S j) pss)
  end); clear go len_pos; abstract (simplify_equality;
      first [by constructor | by inversion 1]).
Defined.

Lemma fragmented_length x i xss : fragmented x i xss → i + length xss = len.
Proof. induction 1; simpl; lia. Qed.
Lemma fragmented_seq x i xss :
  fragmented x i xss → Frag x <$> seq i (length xss) = xss.
Proof. induction 1; simpl; by f_equal. Qed.

Lemma fragmented_alt x i xss :
  fragmented x i xss ↔
    i + length xss = len ∧ xss = Frag x <$> seq i (length xss).
Proof.
  split; [intros Hvalid; split |].
  * by apply fragmented_length with x.
  * by rewrite fragmented_seq.
  * intros [Hi Hxss]. rewrite Hxss. clear Hxss. revert i Hi.
    induction (length xss); simpl; intros i.
    + rewrite Nat.add_0_r. intros; subst. constructor.
    + constructor. apply IHn. lia.
Qed.

Definition to_frags (x : A) : list (frag A) := Frag x <$> seq 0 len.
Definition of_frags (xss : list (frag A)) : option A :=
  match xss with
  | Frag x 0 :: xss => guard (fragmented x 1 xss); Some x
  | _ => None
  end.

Lemma to_frags_fragmented x : fragmented x 0 (to_frags x).
Proof.
  unfold to_frags. apply fragmented_alt. by rewrite fmap_length, seq_length.
Qed.
Lemma to_frags_length x : length (to_frags x) = len.
Proof.
  unfold to_frags. rewrite <-(plus_O_n (length _)).
  apply fragmented_length with x, to_frags_fragmented.
Qed.

Lemma of_to_frags x xss : of_frags xss = Some x ↔ to_frags x = xss.
Proof.
  unfold of_frags, to_frags, PropHolds in *.
  destruct len as [|n] eqn:?; simpl; [lia |]. split; intros Hss.
  * destruct xss as [|[y [|?]] xss]; simplify_option_equality.
    replace n with (length xss).
    + by rewrite fragmented_seq.
    + pose proof (fragmented_length x 1 xss). intuition lia.
  * simplify_option_equality; [done |].
    match goal with H : ¬fragmented _ _ _ |- _ => destruct H end;
      apply fragmented_alt.
    rewrite fmap_length, seq_length. intuition lia.
Qed.
Lemma of_to_frags_1 x xss : of_frags xss = Some x → to_frags x = xss.
Proof. by apply of_to_frags. Qed.
Lemma of_to_frags_2 x : of_frags (to_frags x) = Some x.
Proof. by apply of_to_frags. Qed.

Global Instance to_frags_inj: Injective (=) (=) to_frags.
Proof.
  intros x y. generalize (eq_refl (to_frags y)).
  rewrite <-!of_to_frags. congruence.
Qed.

Lemma Forall_to_frags (P : frag A → Prop) x :
  (∀ i, i < len → P (Frag x i)) → Forall P (to_frags x).
Proof.
  unfold to_frags. intros. apply Forall_fmap, Forall_seq; auto with lia.
Qed.
Lemma Forall_of_frags (P : frag A → Prop) x xss i :
  of_frags xss = Some x → i < len → Forall P xss → P (Frag x i).
Proof.
  revert xss i. assert (∀ i xss,
    S i < len → fragmented x 1 xss → Forall P xss → P (Frag x (S i))).
  { intros i xss ?. rewrite fragmented_alt. intros [? Hxss].
    rewrite Hxss. rewrite Forall_fmap, Forall_seq.
    intros Hx. apply Hx; auto with lia. }
  unfold of_frags. intros. destruct xss as [|[? [|?]]], i;
    simplify_option_equality; decompose_Forall; eauto.
Qed.
End fragmented.
