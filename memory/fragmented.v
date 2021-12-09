(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file defines a type [frag A] to represent symbolic fragments of a
data type [A]. The representation of [x : A] as a list of [n] fragments is:
"frag 0 of x", ..., "frag n of x".  We provide functions to ``split'' an
element of type [A] into fragments, and to go back. Fragments are used to
describe abstract fragments of pointers so as to encode and decode pointers as
bytes in the file [pointers]. *)
Require Export base.

Record fragment (A : Type) := Fragment { frag_item : A; frag_index : nat }.
Add Printing Constructor fragment.
Arguments Fragment {_} _ _.
Arguments frag_item {_} _.
Arguments frag_index {_} _.

#[global] Instance fragment_eq_dec `{EqDecision A}: EqDecision (fragment A).
Proof. solve_decision. Defined.

Section fragmented.
Context {A : Type} `{EqDecision A}.
Context (len : nat) {len_pos : PropHolds (len ≠ 0)}.

Definition fragmented (x : A) (i : nat) (xss : list (fragment A)) : Prop :=
  xss = Fragment x <$> seq i (len - i).
#[global] Instance fragmented_dec x : ∀ i xss, Decision (fragmented x i xss).
Proof. intros. unfold Decision, fragmented. decide equality. solve_decision. Defined.
Typeclasses Opaque fragmented.

Definition to_fragments (x : A) : list (fragment A) := Fragment x <$> seq 0 len.
Definition of_fragments (xss : list (fragment A)) : option A :=
  match xss with
  | Fragment x 0 :: xss => guard (fragmented x 1 xss); Some x
  | _ => None
  end.

Lemma to_fragments_fragmented x : fragmented x 0 (to_fragments x).
Proof. unfold fragmented, to_fragments. by rewrite Nat.sub_0_r. Qed.
Lemma to_fragments_length x : length (to_fragments x) = len.
Proof. unfold to_fragments. by rewrite fmap_length, seq_length. Qed.

Lemma of_to_fragments x xss : of_fragments xss = Some x ↔ to_fragments x = xss.
Proof.
  unfold of_fragments, to_fragments, fragmented, fragmented_dec, PropHolds in *.
  destruct len as [|n]; [lia|].
  by destruct xss as [|[y [|?]] xss]; split; intros;
    simplify_option_eq; rewrite ?Nat.sub_0_r, ?Nat.sub_0_r in *.
Qed.
Lemma of_to_fragments_1 x xss :
  of_fragments xss = Some x → to_fragments x = xss.
Proof. by apply of_to_fragments. Qed.
Lemma of_to_fragments_2 x : of_fragments (to_fragments x) = Some x.
Proof. by apply of_to_fragments. Qed.
#[global] Instance to_fragments_inj: Inj (=) (=) to_fragments.
Proof.
  intros x y. generalize (eq_refl (to_fragments y)).
  rewrite <-!of_to_fragments. congruence.
Qed.

Lemma Forall_to_fragments (P : fragment A → Prop) x :
  (∀ i, i < len → P (Fragment x i)) → Forall P (to_fragments x).
Proof.
  unfold to_fragments. intros. apply Forall_fmap, Forall_seq; auto with lia.
Qed.
Lemma Forall_of_fragments (P : fragment A → Prop) x xss i :
  of_fragments xss = Some x → i < len → Forall P xss → P (Fragment x i).
Proof.
  revert xss i. assert (∀ i xss,
    S i < len → fragmented x 1 xss → Forall P xss → P (Fragment x (S i))).
  { intros i xss ? ->. rewrite Forall_fmap, Forall_seq.
    intros Hx. apply Hx; auto with lia. }
  unfold of_fragments. intros. destruct xss as [|[? [|?]]], i;
    simplify_option_eq; decompose_Forall_hyps; eauto.
Qed.
End fragmented.
