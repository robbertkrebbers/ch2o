(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file defines a type [segment A] to represent symbolic segments of a
data type [A]. The representation of [x : A] as a list of [n] segments is:
"segment 0 of x", ..., "segment n of x".  We provide functions to ``split'' an
element of type [A] into segments, and to go back. Segments are used to
describe abstract fragments of pointers so as to encode and decode pointers as
bytes in the file [pointers]. *)
Require Export numbers list.

Record segment (A : Type) := Segment { segment_item : A; segment_index : nat }.
Arguments Segment {_} _ _.
Arguments segment_item {_} _.
Arguments segment_index {_} _.

Section segmented.
Context {A : Type} `{∀ x y : A, Decision (x = y)}.
Context (len : nat) {len_pos : PropHolds (0 < len)}.

Global Instance segment_eq_dec (s1 s2 : segment A) : Decision (s1 = s2).
Proof. solve_decision. Defined.

Inductive segmented (x : A) : nat → list (segment A) → Prop :=
  | segmented_nil : segmented x len []
  | segmented_cons i xss :
     segmented x (S i) xss → segmented x i (Segment x i :: xss).

Global Instance segmented_dec x : ∀ i xss, Decision (segmented x i xss).
Proof.
 refine (
  fix go i xss :=
  match xss with
  | [] => cast_if (decide_rel (=) len i)
  | Segment y j :: pss =>
    cast_if_and3 (decide_rel (=) i j) (decide_rel (=) x y) (go (S j) pss)
  end); clear go len_pos; abstract (simplify_equality;
      first [by constructor | by inversion 1]).
Defined.

Lemma segmented_length x i xss : segmented x i xss → i + length xss = len.
Proof. induction 1; simpl; lia. Qed.
Lemma segmented_seq x i xss :
  segmented x i xss → Segment x <$> seq i (length xss) = xss.
Proof. induction 1; simpl; by f_equal. Qed.

Lemma segmented_alt x i xss :
  segmented x i xss ↔
    i + length xss = len ∧ xss = Segment x <$> seq i (length xss).
Proof.
  split; [intros Hvalid; split |].
  * revert Hvalid. by apply segmented_length.
  * by rewrite segmented_seq.
  * intros [Hi Hxss]. rewrite Hxss. clear Hxss. revert i Hi.
    induction (length xss); simpl; intros.
    + replace i with len by lia. constructor.
    + constructor. apply IHn. lia.
Qed.

Definition to_segments (x : A) : list (segment A) := Segment x <$> seq 0 len.
Definition of_segments (xss : list (segment A)) : option A :=
  match xss with
  | Segment x 0 :: xss => guard (segmented x 1 xss); Some x
  | _ => None
  end.

Lemma to_segments_segmented x : segmented x 0 (to_segments x).
Proof.
  unfold to_segments. apply segmented_alt. by rewrite fmap_length, seq_length.
Qed.
Lemma to_segments_length x : length (to_segments x) = len.
Proof.
  unfold to_segments. rewrite <-(plus_O_n (length _)).
  apply segmented_length with x, to_segments_segmented.
Qed.

Lemma of_to_segments x xss : of_segments xss = Some x ↔ to_segments x = xss.
Proof.
  unfold of_segments, to_segments, PropHolds in *.
  destruct len as [|n] eqn:?; simpl; [lia |]. split; intros Hss.
  * destruct xss as [|[y [|?]] xss]; simplify_option_equality.
    replace n with (length xss).
    + by rewrite segmented_seq.
    + pose proof (segmented_length x 1 xss). intuition lia.
  * simplify_option_equality; [done |].
    match goal with H : ¬segmented _ _ _ |- _ => destruct H end;
      apply segmented_alt.
    rewrite fmap_length, seq_length. intuition lia.
Qed.
Lemma of_to_segments_1 x xss : of_segments xss = Some x → to_segments x = xss.
Proof. by apply of_to_segments. Qed.
Lemma of_to_segments_2 x : of_segments (to_segments x) = Some x.
Proof. by apply of_to_segments. Qed.

Global Instance to_segments_inj: Injective (=) (=) to_segments.
Proof.
  intros x y. generalize (eq_refl (to_segments y)).
  rewrite <-!of_to_segments. congruence.
Qed.

Lemma Forall_to_segments (P : A → Prop) x :
  P x → Forall (P ∘ segment_item) (to_segments x).
Proof. unfold to_segments. intros. by apply Forall_fmap, Forall_true. Qed.
Lemma Forall_of_segments (P : A → Prop) x xss :
  of_segments xss = Some x → Forall (P ∘ segment_item) xss → P x.
Proof.
  unfold of_segments. intros.
  by destruct xss as [|[? [|?]]]; simplify_option_equality; decompose_Forall.
Qed.
End segmented.
