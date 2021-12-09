(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export base tactics.

Local Unset Elimination Schemes.
Definition sType := Type.
Bind Scope type_scope with sType.
Class SeparationOps (A : sType) : sType := {
  sep_valid : A → Prop;
  sep_empty :> Empty A;
  sep_disjoint :> Disjoint A;
  sep_union :> Union A;
  sep_subseteq :> SubsetEq A;
  sep_difference :> Difference A;
  sep_splittable : A → Prop;
  sep_half :> Half A;
  sep_unmapped : A → Prop;
  sep_unshared : A → Prop;
  sep_valid_dec (x : A) :> Decision (sep_valid x);
  sep_subseteq_dec (x y : A) :> Decision (x ⊆ y);
  sep_disjoint_dec (x y : A) :> Decision (x ## y);
  sep_eq_dec :> EqDecision A;
  sep_unshared_dec (x : A) :> Decision (sep_unshared x);
  sep_splittable_dec (x : A) :> Decision (sep_splittable x);
  sep_unmapped_dec (x : A) :> Decision (sep_unmapped x)
}.
Arguments sep_valid _ _ _ : simpl never.
Arguments sep_empty _ _ : simpl never.
Arguments sep_disjoint _ _ _ _ : simpl never.
Arguments sep_union _ _ _ _ : simpl never.
Arguments sep_subseteq _ _ _ _ : simpl never.
Arguments sep_difference _ _ _ _ : simpl never.
Arguments sep_splittable _ _ _ : simpl never.
Arguments sep_half _ _ _ : simpl never.
Arguments sep_unmapped _ _ _ : simpl never.
Arguments sep_unshared _ _ _ : simpl never.
Arguments sep_valid_dec _ _ _ : simpl never.
Arguments sep_subseteq_dec _ _ _ _ : simpl never.
Arguments sep_disjoint_dec _ _ _ _ : simpl never.
Arguments sep_eq_dec _ _ _ _ : simpl never.
Arguments sep_unshared_dec _ _ _ : simpl never.
Arguments sep_splittable_dec _ _ _ : simpl never.
Arguments sep_unmapped_dec _ _ _ : simpl never.
Ltac sep_unfold :=
  unfold disjoint, sep_disjoint, sep_valid, subseteq, sep_subseteq,
  sep_unshared, sep_splittable, sep_unmapped, empty, sep_empty, union,
  sep_union, difference, sep_difference, half, sep_half; simpl.

Class Separation (A : sType) `{SeparationOps A} : Prop := {
  sep_inhabited : ∃ x : A, sep_valid x ∧ ¬sep_unmapped x;
  sep_disjoint_valid_l (x y : A) : x ## y → sep_valid x;
  sep_union_valid (x y : A) : x ## y → sep_valid (x ∪ y);
  sep_disjoint_empty_l (x : A) : sep_valid x → ∅ ## x;
  sep_left_id (x : A) : sep_valid x → ∅ ∪ x = x;
  sep_symmetric :> Symmetric (@disjoint A _);
  sep_commutative' (x y : A) : x ## y → x ∪ y = y ∪ x;
  sep_disjoint_ll (x y z : A) : x ## y → x ∪ y ## z → x ## z;
  sep_disjoint_move_l (x y z : A) : x ## y → x ∪ y ## z → x ## y ∪ z;
  sep_associative' (x y z : A) :
    y ## z → x ## y ∪ z → x ∪ (y ∪ z) = (x ∪ y) ∪ z;
  sep_positive_l' (x y : A) : x ## y → x ∪ y = ∅ → x = ∅;
  sep_cancel_l' (x y z : A) :
    z ## x → z ## y → z ∪ x = z ∪ y → x = y;
  sep_union_subseteq_l' (x y : A) : x ## y → x ⊆ x ∪ y;
  sep_disjoint_difference' (x y : A) : x ⊆ y → x ## y ∖ x;
  sep_union_difference (x y : A) : x ⊆ y → x ∪ y ∖ x = y;
  sep_splittable_union' (x : A) : x ## x → sep_splittable (x ∪ x);
  sep_splittable_weaken (x y : A) : sep_splittable y → x ⊆ y → sep_splittable x;
  sep_disjoint_half' (x : A) : sep_splittable x → ½ x ## ½ x;
  sep_union_half (x : A) : sep_splittable x → ½ x ∪ ½ x = x;
  sep_union_half_distr' (x y : A) :
    x ## y → sep_splittable (x ∪ y) → ½ (x ∪ y) = ½ x ∪ ½ y;
  sep_unmapped_valid x : sep_unmapped x → sep_valid x;
  sep_unmapped_empty : sep_unmapped ∅;
  sep_unmapped_weaken x y : sep_unmapped y → x ⊆ y → sep_unmapped x;
  sep_unmapped_union_2' (x y : A) :
    x ## y → sep_unmapped x → sep_unmapped y → sep_unmapped (x ∪ y);
  sep_unshared_spec' (x : A) :
    sep_unshared x ↔ sep_valid x ∧ ∀ y, x ## y → sep_unmapped y;
  sep_unshared_unmapped (x : A) : sep_unshared x → sep_unmapped x → False
}.
Arguments sep_inhabited _ {_ _}.

(** We define a relation [xs1 ≡## xs2] that states that lists [xs1] and [xs2]
behave equivalently with respect to disjointness. For example, we have
[∅ :: xs ≡## xs] and [x ∪ y :: xs ≡## x :: y :: xs]. Since this relation is an
equivalence relation, and is respected by the list operations, it allows us to
use Coq's setoid mechanism to conveniently reason about disjoint permissions/
memories/... Likewise, we define an order [xs1 ⊆## xs2]. *)
Definition sep_disjoint_le `{SeparationOps A} : relation (list A) :=
  λ xs1 xs2, ∀ x, ## (x :: xs1) → ## (x :: xs2).
Notation "xs ⊆## ys" := (sep_disjoint_le xs ys)
  (at level 70, format "xs  ⊆##  ys") : C_scope.
Notation "(⊆##)" := (sep_disjoint_le) (only parsing) : C_scope.

Definition sep_disjoint_equiv `{SeparationOps A} : relation (list A) :=
  λ xs1 xs2, xs1 ⊆## xs2 ∧ xs2 ⊆## xs1.
Notation "xs ≡## ys" := (sep_disjoint_equiv xs ys)
  (at level 70, format "xs  ≡##  ys") : C_scope.
Notation "(≡##)" := sep_disjoint_equiv (only parsing) : C_scope.

Section separation.
Context `{Separation A}.
Implicit Types x y z : A.
Implicit Types xs ys zs : list A.

(** ** Properties of the [(##)] relation *)
Lemma sep_disjoint_empty_r x : sep_valid x → x ## ∅.
Proof. symmetry. by apply sep_disjoint_empty_l. Qed.
Lemma sep_disjoint_valid_r x y : x ## y → sep_valid y.
Proof. rewrite (symmetry_iff (##)). apply sep_disjoint_valid_l. Qed.
Lemma sep_disjoint_lr x y z : x ## y → x ∪ y ## z → y ## z.
Proof. intro. rewrite sep_commutative' by done. by apply sep_disjoint_ll. Qed.
Lemma sep_disjoint_rl x y z : y ## z → x ## y ∪ z → x ## y.
Proof. rewrite !(symmetry_iff _ x). apply sep_disjoint_ll. Qed.
Lemma sep_disjoint_rr x y z : y ## z → x ## y ∪ z → x ## z.
Proof. intro. rewrite sep_commutative' by done. by apply sep_disjoint_rl. Qed.
Lemma sep_disjoint_move_r x y z : y ## z → x ## y ∪ z → x ∪ y ## z.
Proof.
  intros. symmetry. rewrite sep_commutative'; [|eauto using sep_disjoint_rl].
  apply sep_disjoint_move_l; [done |]. by rewrite sep_commutative'.
Qed.

(** ** Algebraic properties *)
Lemma sep_right_id x : sep_valid x → x ∪ ∅ = x.
Proof.
  intros. by rewrite sep_commutative', sep_left_id
    by auto using sep_disjoint_empty_r.
Qed.
Lemma sep_empty_valid : sep_valid ∅.
Proof.
  destruct (sep_inhabited A) as (x&Hx&_).
  by apply sep_disjoint_valid_l with x, sep_disjoint_empty_l.
Qed.
Lemma sep_positive_r' x y : x ## y → x ∪ y = ∅ → y = ∅.
Proof. intro. rewrite sep_commutative' by done. by apply sep_positive_l'. Qed.
Lemma sep_union_empty' x y : x ## y → x ∪ y = ∅ ↔ x = ∅ ∧ y = ∅.
Proof.
  split; [eauto using sep_positive_l', sep_positive_r'|].
  intros [-> ->]; eauto using sep_left_id, sep_disjoint_valid_l.
Qed.
Lemma sep_cancel_r' x y z : x ## z → y ## z → x ∪ z = y ∪ z → x = y.
Proof.
  intros ??. rewrite !(sep_commutative' _ z) by done. by apply sep_cancel_l'.
Qed.
Lemma sep_cancel_empty_l x y : x ## y → x ∪ y = y → x = ∅.
Proof.
  intros. apply sep_cancel_r' with y;
    rewrite ?sep_left_id by eauto using sep_disjoint_valid_l;
    eauto using sep_disjoint_empty_l, sep_disjoint_valid_l.
Qed.
Lemma sep_cancel_empty_r x y : x ## y → x ∪ y = x → y = ∅.
Proof.
  intro. rewrite sep_commutative' by done. by apply sep_cancel_empty_l.
Qed.
Lemma sep_associative_rev x y z : x ## y → x ∪ y ## z → x ∪ y ∪ z = x ∪ (y ∪ z).
Proof.
  eauto using eq_sym, sep_associative', sep_disjoint_move_l, sep_disjoint_lr.
Qed.
Lemma sep_permute x y z : x ## y → x ∪ y ## z → x ∪ y ∪ z = x ∪ z ∪ y.
Proof.
  intros. assert (x ## z) by eauto using sep_disjoint_ll.
  assert (x ∪ z ## y).
  { rewrite sep_commutative' by done. by apply sep_disjoint_move_r. }
  by rewrite !sep_associative_rev,
    (sep_commutative' y) by eauto using sep_disjoint_lr.
Qed.

(** ** Properties of the [(⊆)] relation *)
Lemma sep_subseteq_spec' x y : x ⊆ y ↔ ∃ z, y = x ∪ z ∧ x ## z.
Proof.
  split; [|intros (?&->&?); by apply sep_union_subseteq_l']. exists (y ∖ x).
  eauto using sep_disjoint_difference', sep_union_difference, eq_sym.
Qed.
Lemma sep_subseteq_valid_r x y : x ⊆ y → sep_valid y.
Proof.
  rewrite !sep_subseteq_spec'. intros (z&->&?). by apply sep_union_valid.
Qed.
Lemma sep_subseteq_valid_l x y : x ⊆ y → sep_valid x.
Proof.
  rewrite !sep_subseteq_spec'. intros (z&_&?).
  by apply sep_disjoint_valid_l with z.
Qed.
Lemma sep_reflexive x : sep_valid x → x ⊆ x.
Proof.
  rewrite sep_subseteq_spec'. eexists ∅.
  rewrite sep_right_id; auto using sep_disjoint_empty_r.
Qed.
#[global] Instance: Transitive (@subseteq A _).
Proof.
  intros x y z. rewrite !sep_subseteq_spec'. intros (z1&->&?) (z2&->&?).
  exists (z1 ∪ z2); eauto 8 using sep_associative',
    sep_disjoint_lr, sep_disjoint_move_l, eq_sym.
Qed.
#[global] Instance: AntiSymm (=) (@subseteq A _).
Proof.
  intros x y. rewrite !sep_subseteq_spec'; intros (z1&->&?) (z2&Hx&?).
  rewrite <-(sep_right_id x) in Hx at 1 by eauto using sep_disjoint_valid_l.
  rewrite <-sep_associative' in Hx by
    eauto using sep_disjoint_move_l, sep_disjoint_lr.
  apply sep_cancel_l' in Hx;
    eauto using sep_disjoint_empty_r, sep_disjoint_move_l, sep_disjoint_valid_l.
  by rewrite (sep_positive_l' z1 z2), sep_right_id by
    (by eauto 2 using sep_disjoint_lr, sep_disjoint_valid_l).
Qed.
Lemma sep_subseteq_empty x : sep_valid x → ∅ ⊆ x.
Proof.
  intros. rewrite sep_subseteq_spec'. exists x.
  rewrite sep_left_id; auto using sep_disjoint_empty_l.
Qed.
Lemma sep_union_subseteq_r' x y : x ## y → y ⊆ x ∪ y.
Proof.
  intro. rewrite sep_commutative' by done. by apply sep_union_subseteq_l'.
Qed.
Lemma sep_disjoint_weaken_l x y z : x ## y → z ⊆ x → z ## y.
Proof.
  rewrite !sep_subseteq_spec'.
  intros ? (?&->&?); eauto using sep_disjoint_ll.
Qed.
Lemma sep_disjoint_weaken_r x y z : x ## y → z ⊆ y → x ## z.
Proof.
  rewrite !sep_subseteq_spec'.
  intros ? (?&->&?); eauto using sep_disjoint_rl.
Qed.
#[global] Instance: Proper ((⊆) ==> (⊆) ==> flip impl) (@disjoint A _).
Proof.
  repeat intro; eauto using sep_disjoint_weaken_l, sep_disjoint_weaken_r.
Qed.
Lemma sep_union_difference_alt x y : x ## y → (x ∪ y) ∖ x = y.
Proof.
  intros. apply sep_cancel_l' with x;
    auto using sep_disjoint_difference', sep_union_subseteq_l'.
  by rewrite sep_union_difference by auto using sep_union_subseteq_l'.
Qed.
Lemma sep_difference_subseteq x y : x ⊆ y → y ∖ x ⊆ y.
Proof.
  rewrite sep_subseteq_spec'; intros (z&->&?).
  rewrite sep_union_difference_alt; auto using sep_union_subseteq_r'.
Qed.

(** ** Properties of the [(∖)] operation *)
Lemma sep_difference_valid x y : x ⊆ y → sep_valid (y ∖ x).
Proof. eauto using sep_disjoint_valid_r, sep_disjoint_difference'. Qed.
Lemma sep_difference_diag x : sep_valid x → x ∖ x = ∅.
Proof.
  intros. apply (sep_cancel_l' _ _ x);
    auto using sep_disjoint_difference', sep_disjoint_empty_r, sep_reflexive.
  by rewrite sep_union_difference, sep_right_id by auto using sep_reflexive.
Qed.
Lemma sep_difference_empty x : sep_valid x → x ∖ ∅ = x.
Proof.
  intros. by rewrite <-(sep_left_id (x ∖ ∅)), sep_union_difference
    by auto using sep_difference_valid, sep_subseteq_empty.
Qed.
Lemma sep_difference_empty_rev x y : x ⊆ y → y ∖ x = ∅ → x = y.
Proof.
  intros ? Hxy. by rewrite <-(sep_right_id x), <-Hxy,
    sep_union_difference by eauto using sep_subseteq_valid_l.
Qed.

(** ** Properties of the [half] operation *)
Lemma sep_splittable_valid x : sep_splittable x → sep_valid x.
Proof.
  intros. rewrite <-(sep_union_half x) by done.
  auto using sep_union_valid, sep_disjoint_half'.
Qed.
Lemma sep_half_valid x : sep_splittable x → sep_valid (½ x).
Proof. eauto using sep_disjoint_valid_l, sep_disjoint_half'. Qed.
Lemma sep_half_subseteq x : sep_splittable x → ½ x ⊆ x.
Proof.
  rewrite sep_subseteq_spec'. intros. exists (½ x).
  eauto using sep_disjoint_half', sep_union_half, eq_sym.
Qed.
Lemma sep_splittable_empty : sep_splittable ∅.
Proof.
  rewrite <-(sep_right_id ∅) by auto using sep_empty_valid.
  apply sep_splittable_union';
    auto using sep_disjoint_empty_l, sep_empty_valid.
Qed.
Lemma sep_half_empty : ½ (∅ : A) = ∅.
Proof.
  apply sep_positive_l' with (½ ∅);
    eauto using sep_union_half, sep_disjoint_half', sep_splittable_empty.
Qed.
Lemma sep_half_empty_rev x : sep_splittable x → ½ x = ∅ → x = ∅.
Proof.
  intros ? Hx. by rewrite <-(sep_union_half x), !Hx, sep_left_id
    by auto using sep_empty_valid.
Qed.
Lemma sep_splittable_half x : sep_splittable x → sep_splittable (½ x).
Proof. eauto using sep_splittable_weaken, sep_half_subseteq. Qed.

(** ** Properties of the [sep_unmapped] predicate *)
Lemma sep_unmapped_empty_alt x : x = ∅ → sep_unmapped x.
Proof. intros ->; by apply sep_unmapped_empty. Qed.
Lemma sep_unmapped_union_l' x y :
  x ## y → sep_unmapped (x ∪ y) → sep_unmapped x.
Proof. eauto using sep_unmapped_weaken, sep_union_subseteq_l'. Qed.
Lemma sep_unmapped_union_r' x y :
  x ## y → sep_unmapped (x ∪ y) → sep_unmapped y.
Proof. eauto using sep_unmapped_weaken, sep_union_subseteq_r'. Qed.
Lemma sep_unmapped_union' x y :
  x ## y → sep_unmapped (x ∪ y) ↔ sep_unmapped x ∧ sep_unmapped y.
Proof.
  naive_solver eauto using sep_unmapped_union_l',
    sep_unmapped_union_r', sep_unmapped_union_2'.
Qed.
Lemma sep_unmapped_half x :
  sep_splittable x → sep_unmapped (½ x) ↔ sep_unmapped x.
Proof.
  intros. rewrite <-(sep_union_half x) at 2 by done. rewrite
    sep_unmapped_union' by eauto using sep_disjoint_half'; tauto.
Qed.
Lemma sep_unmapped_half_1 x :
  sep_splittable x → sep_unmapped (½ x) → sep_unmapped x.
Proof. intros. by apply sep_unmapped_half. Qed.
Lemma sep_unmapped_difference x y :
  x ⊆ y → sep_unmapped x ∧ sep_unmapped (y ∖ x) ↔ sep_unmapped y.
Proof.
  intros. rewrite <-(sep_union_difference x y) at 2 by done.
  by rewrite sep_unmapped_union' by eauto using sep_disjoint_difference'.
Qed.
Lemma sep_unmapped_difference_1 x y :
  x ⊆ y → sep_unmapped x → sep_unmapped (y ∖ x) → sep_unmapped y.
Proof. intros. by apply (sep_unmapped_difference x y). Qed.
Lemma sep_unmapped_difference_2 x y :
  x ⊆ y → sep_unmapped y → sep_unmapped (y ∖ x).
Proof. intros. by apply (sep_unmapped_difference x y). Qed.

(** ** Properties of the [sep_unshared] predicate *)
Lemma sep_unshared_empty : ¬sep_unshared ∅.
Proof.
  rewrite sep_unshared_spec'; intros [??].
  destruct (sep_inhabited A) as (x&?&[]); eauto using sep_disjoint_empty_l.
Qed.
Lemma sep_unshared_ne_empty x : sep_unshared x → x ≠ ∅.
Proof. intros ? ->. by apply sep_unshared_empty. Qed.
Lemma sep_unshared_valid x : sep_unshared x → sep_valid x.
Proof. rewrite sep_unshared_spec'. by intros [??]. Qed.
Lemma sep_disjoint_unshared_unmapped x y :
  x ## y → sep_unshared x → sep_unmapped y.
Proof. rewrite sep_unshared_spec'; naive_solver. Qed.
Lemma sep_unshared_weaken x y : sep_unshared x → x ⊆ y → sep_unshared y.
Proof.
  rewrite !sep_unshared_spec'.
  naive_solver eauto using sep_disjoint_weaken_l, sep_subseteq_valid_r.
Qed.
Lemma sep_unshared_union_l' x y :
  x ## y → sep_unshared x → sep_unshared (x ∪ y).
Proof. eauto using sep_unshared_weaken, sep_union_subseteq_l'. Qed.
Lemma sep_unshared_union_r' x y :
  x ## y → sep_unshared y → sep_unshared (x ∪ y).
Proof. eauto using sep_unshared_weaken, sep_union_subseteq_r'. Qed.

(** ** Properties of disjointness of lists *)
Lemma sep_disjoint_list_valid xs : ## xs → Forall sep_valid xs.
Proof. induction 1; constructor; eauto using sep_disjoint_valid_l. Qed.
Lemma sep_disjoint_list_singleton x : ## [x] ↔ sep_valid x.
Proof.
  intros. rewrite !disjoint_list_cons, disjoint_list_nil; simpl.
  intuition eauto using sep_disjoint_empty_r, sep_disjoint_valid_l.
Qed.
Lemma sep_disjoint_list_double x y : ## [x; y] ↔ x ## y.
Proof.
  rewrite disjoint_list_cons, sep_disjoint_list_singleton; simpl. split.
  * intros [Hxy ?]. by rewrite sep_right_id in Hxy.
  * intros. rewrite sep_right_id; eauto using sep_disjoint_valid_r.
Qed.
Lemma sep_disjoint_list_double_1 x y : ## [x; y] → x ## y.
Proof. by rewrite sep_disjoint_list_double. Qed.
Lemma sep_disjoint_list_double_2 x y : x ## y → ## [x; y].
Proof. by rewrite sep_disjoint_list_double. Qed.
Lemma sep_disjoint_list_symmetric x y : ## [x; y] → ## [y; x].
Proof. by rewrite !sep_disjoint_list_double. Qed.
Hint Immediate sep_disjoint_list_double_1 sep_disjoint_list_symmetric: core.
Hint Resolve sep_disjoint_list_double_2: core.
Lemma sep_subseteq_spec x y : x ⊆ y ↔ ∃ z, y = x ∪ z ∧ ## [x; z].
Proof.
  setoid_rewrite sep_disjoint_list_double. apply sep_subseteq_spec'.
Qed.
Lemma sep_associative x y z : ## [x; y; z] → x ∪ (y ∪ z) = (x ∪ y) ∪ z.
Proof.
  rewrite !disjoint_list_cons; simpl. intros (Hxyz&Hyz&?&_).
  rewrite sep_right_id in Hxyz, Hyz by eauto using sep_disjoint_valid_l.
  by apply sep_associative'.
Qed.
Lemma sep_commutative x y : ## [x; y] → x ∪ y = y ∪ x.
Proof. rewrite sep_disjoint_list_double. apply sep_commutative'. Qed.

Lemma sep_cancel_l x y z : ## [z; x] → ## [z; y] → z ∪ x = z ∪ y → x = y.
Proof. eauto using sep_cancel_l', sep_disjoint_list_double_1. Qed.
Lemma sep_cancel_r x y z : ## [x; z] → ## [y; z] → x ∪ z = y ∪ z → x = y.
Proof.
  intros ??. rewrite !(sep_commutative _ z) by done. eauto using sep_cancel_l.
Qed.
Lemma sep_positive_l x y : ## [x; y] → x ∪ y = ∅ → x = ∅.
Proof. rewrite sep_disjoint_list_double. eauto using sep_positive_l'. Qed.
Lemma sep_positive_r x y : ## [x; y] → x ∪ y = ∅ → y = ∅.
Proof. rewrite sep_disjoint_list_double. apply sep_positive_r'. Qed.
Lemma sep_union_subseteq_l x y : ##[x; y] → x ⊆ x ∪ y.
Proof. rewrite sep_disjoint_list_double. apply sep_union_subseteq_l'. Qed.
Lemma sep_union_subseteq_r x y : ##[x; y] → y ⊆ x ∪ y.
Proof. rewrite sep_disjoint_list_double. apply sep_union_subseteq_r'. Qed.
Lemma sep_union_subseteq_l_transitive x y z : ## [y; z] → x ⊆ y → x ⊆ y ∪ z.
Proof. intros. transitivity y; auto using sep_union_subseteq_l. Qed.
Lemma sep_union_subseteq_r_transitive x y z : ## [y; z] → x ⊆ z → x ⊆ y ∪ z.
Proof. intros. transitivity z; auto using sep_union_subseteq_r. Qed.
Lemma sep_preserving_l x y z : ## [z; y] → x ⊆ y → z ∪ x ⊆ z ∪ y.
Proof.
  rewrite !sep_subseteq_spec; setoid_rewrite sep_disjoint_list_double.
  intros ? (z1&->&?). exists z1.
  rewrite sep_associative'; auto using sep_disjoint_move_r.
Qed.
Lemma sep_preserving_r x y z : ## [y; z] → x ⊆ y → x ∪ z ⊆ y ∪ z.
Proof.
  rewrite sep_disjoint_list_double; intros.
  rewrite !(sep_commutative' _ z) by eauto using sep_disjoint_weaken_l.
  apply sep_preserving_l; auto.
Qed.
Lemma sep_preserving x y z z' : ## [y; z'] → x ⊆ y → z ⊆ z' → x ∪ z ⊆ y ∪ z'.
Proof.
  rewrite sep_disjoint_list_double; intros.
  transitivity (x ∪ z'); auto using sep_preserving_r.
  apply sep_preserving_l; eauto using sep_disjoint_weaken_l.
Qed.
Lemma sep_reflecting_l x y z : ## [z; x] → ## [z; y] → z ∪ x ⊆ z ∪ y → x ⊆ y.
Proof.
  rewrite !sep_subseteq_spec; setoid_rewrite sep_disjoint_list_double.
  intros ?? (z1&?&?). exists z1. split; eauto 2 using sep_disjoint_lr.
  apply (sep_cancel_l' _ _ z); auto using sep_disjoint_move_l.
  by rewrite sep_associative' by
    eauto using sep_disjoint_lr, sep_disjoint_move_l.
Qed.
Lemma sep_reflecting_r x y z : ## [x; z] → ## [y; z] → x ∪ z ⊆ y ∪ z → x ⊆ y.
Proof.
  intros ??. rewrite !(sep_commutative _ z) by done.
  eauto using sep_reflecting_l.
Qed.
Lemma sep_disjoint_difference x y : x ⊆ y → ##[x; y ∖ x].
Proof. rewrite sep_disjoint_list_double. apply sep_disjoint_difference'. Qed.
Lemma sep_splittable_union x : ## [x; x] → sep_splittable (x ∪ x).
Proof. rewrite sep_disjoint_list_double. apply sep_splittable_union'. Qed.
Lemma sep_disjoint_half x : sep_splittable x → ## [½ x; ½ x].
Proof. rewrite sep_disjoint_list_double. apply sep_disjoint_half'. Qed.
Lemma sep_splittable_spec x : sep_splittable x ↔ ∃ y, x = y ∪ y ∧ ## [y; y].
Proof.
  split.
  * exists (½ x); eauto using sep_disjoint_half, sep_union_half, eq_sym.
  * intros (?&->&?); auto using sep_splittable_union.
Qed.
Lemma sep_union_half_distr x y :
  ## [x; y] → sep_splittable (x ∪ y) → ½ (x ∪ y) = ½ x ∪ ½ y.
Proof. rewrite sep_disjoint_list_double. apply sep_union_half_distr'. Qed.
Lemma sep_half_unique x y : ## [y; y] → x = y ∪ y → y = ½ x.
Proof.
  intros ? ->.
  assert (sep_splittable (y ∪ y)) by auto using sep_splittable_union.
  assert (sep_splittable y) by
    eauto using sep_splittable_weaken, sep_union_subseteq_l.
  by rewrite sep_union_half_distr, sep_union_half by done.
Qed.
Lemma sep_union_list_valid xs : ## xs → sep_valid (⋃ xs).
Proof. induction 1; simpl; auto using sep_empty_valid, sep_union_valid. Qed.
Lemma sep_disjoint_contains_aux xs1 xs2 :
  ## xs2 → xs1 ⊆+ xs2 → ## xs1 ∧ ⋃ xs1 ⊆ ⋃ xs2.
Proof.
  intros Hxs2 Hxs. revert Hxs2. induction Hxs as
  [|x xs1 xs2 ? IH|x1 x2 xs|x xs1 xs2 ? IH|xs1 xs2 xs3 ? IH1 ? IH2]; simpl in *.
  * auto using sep_reflexive, sep_empty_valid.
  * rewrite !disjoint_list_cons. intros [??]. destruct IH as [IH1 IH2]; auto.
    eauto 7 using sep_preserving_l, sep_disjoint_weaken_r.
  * rewrite !disjoint_list_cons; simpl. intros (?&?&?). split_and ?.
    + apply sep_disjoint_move_l.
      { symmetry. eauto using sep_disjoint_rl. }
      rewrite sep_commutative' by (symmetry; eauto using sep_disjoint_rl).
      eauto using sep_disjoint_move_r.
    + eauto using sep_disjoint_rr.
    + done.
    + rewrite (sep_associative' x1), (sep_commutative' x1 x2)
        by eauto using sep_disjoint_rl.
      assert (x2 ## x1 ∪ ⋃ xs).
      { rewrite (sep_commutative' x1) by eauto 2 using sep_disjoint_rr.
        by apply sep_disjoint_move_l. }
      rewrite <-sep_associative' by (eauto 2 using sep_disjoint_rr).
      by apply sep_reflexive, sep_union_valid.
  * rewrite !disjoint_list_cons. intros [??].
    destruct IH as [IH1 IH2]; eauto using sep_union_subseteq_r_transitive.
  * intros. destruct IH1; auto; destruct IH2; auto.
    split; auto. by transitivity (⋃ xs2).
Qed.
Lemma sep_disjoint_contains xs1 xs2 : ## xs2 → xs1 ⊆+ xs2 → ## xs1.
Proof. intros. by apply (sep_disjoint_contains_aux xs1 xs2). Qed.
Lemma sep_union_list_subseteq xs1 xs2 :
  ## xs2 → xs1 ⊆+ xs2 → ⋃ xs1 ⊆ ⋃ xs2.
Proof. intros. by apply sep_disjoint_contains_aux. Qed.
#[global] Instance: Proper (@Permutation A ==> iff) disjoint_list.
Proof.
  intros xs1 xs2 Hxs; split; intros.
  * apply (sep_disjoint_contains xs2 xs1). done. by rewrite Hxs.
  * apply (sep_disjoint_contains xs1 xs2). done. by rewrite Hxs.
Qed.
Lemma sep_list_preserving xs1 xs2 : ## xs2 → xs1 ⊆* xs2 → ⋃ xs1 ⊆ ⋃ xs2.
Proof.
  intros Hxs2. induction 1; simpl; inversion_clear Hxs2;
    auto using sep_preserving, sep_reflexive, sep_empty_valid.
Qed.
Lemma sep_disjoint_empty_alt xs : ## (∅ :: xs) ↔ ## xs.
Proof.
  rewrite disjoint_list_cons. intuition auto using sep_disjoint_empty_l.
  eauto using sep_disjoint_empty_l, sep_union_list_valid.
Qed.
Lemma sep_disjoint_alt x y xs : ## (x :: y :: xs) ↔ x ## y ∧ ## (x ∪ y :: xs).
Proof.
  rewrite !disjoint_list_cons. simpl. split; intros (?&?&?).
  * eauto using sep_disjoint_rl, sep_disjoint_move_r.
  * eauto using sep_disjoint_lr, sep_disjoint_move_l.
Qed.
Lemma sep_disjoint_list_alt xs1 xs2 :
  ## (xs1 ++ xs2) ↔ ## xs1 ∧ ## (⋃ xs1 :: xs2).
Proof.
  revert xs2. induction xs1 as [|x xs1 IH]; simpl; intros xs2.
  { rewrite sep_disjoint_empty_alt, disjoint_list_nil. naive_solver. }
  rewrite Permutation_middle, IH, Permutation_swap, sep_disjoint_alt.
  rewrite (disjoint_list_cons x). naive_solver.
Qed.
Lemma sep_unmapped_union_l x y :
  ## [x; y] → sep_unmapped (x ∪ y) → sep_unmapped x.
Proof. eauto using sep_unmapped_weaken, sep_union_subseteq_l. Qed.
Lemma sep_unmapped_union_r x y :
  ## [x; y] → sep_unmapped (x ∪ y) → sep_unmapped y.
Proof. eauto using sep_unmapped_weaken, sep_union_subseteq_r. Qed.

(** ** Properties of [(⊆##)] *)
#[global] Instance: PreOrder (⊆##).
Proof. unfold sep_disjoint_le. split; red; naive_solver. Qed.
#[global] Instance: Proper ((⊆##) ==> impl) disjoint_list.
Proof.
  intros xs1 xs2 Hxs. red. rewrite <-(sep_disjoint_empty_alt xs1),
    <-(sep_disjoint_empty_alt xs2). by apply (Hxs ∅).
Qed.
#[global] Instance: Proper ((≡ₚ) ==> (≡ₚ) ==> iff) (⊆##).
Proof.
  unfold sep_disjoint_le, impl. intros xs1 xs2 Hxs12 xs3 xs4 Hxs34.
  by setoid_rewrite Hxs12; setoid_rewrite Hxs34.
Qed.
#[global] Instance: `{Proper ((⊆##) ==> (⊆##)) (z ::.)}.
Proof.
  unfold sep_disjoint_le, impl. intros z xs1 xs2 Hxs12 y; subst.
  rewrite !sep_disjoint_alt. naive_solver.
Qed.
#[global] Instance: `{Proper (flip (⊆##) ==> flip (⊆##)) (z ::.)}.
Proof. by intros z x y Hxy; simpl in *; rewrite Hxy. Qed.
#[global] Instance: Proper ((⊆##) ==> (⊆##) ==> (⊆##)) (++).
Proof.
  unfold sep_disjoint_le. intros xs1 xs2 Hxs12 xs3 xs4 Hxs34 y.
  apply impl_transitive with ( ## (y :: xs2 ++ xs3)).
  * rewrite !(comm (++) _ xs3), !app_comm_cons.
    rewrite !sep_disjoint_list_alt. naive_solver.
  * rewrite !app_comm_cons, !sep_disjoint_list_alt. naive_solver.
Qed.
#[global] Instance: Proper (flip (⊆##) ==> flip (⊆##) ==> flip (⊆##)) (++).
Proof. by intros x1 y1 Hxy1 x2 y2 Hxy2; simpl in *; rewrite Hxy1, Hxy2. Qed.
Lemma sep_disjoint_cons_le_inj x y xs : [x] ⊆## [y] → x :: xs ⊆## y :: xs.
Proof. intros. change ([x] ++ xs ⊆## [y] ++ xs). by f_equiv. Qed.

(** ** Properties of [(≡##)] *)
Lemma sep_disjoint_equiv_alt xs1 xs2 :
  xs1 ≡## xs2 ↔  ∀ x, ## (x :: xs1) ↔ ## (x :: xs2).
Proof. unfold sep_disjoint_equiv, sep_disjoint_le. naive_solver. Qed.
#[global] Instance: Equivalence (≡##).
Proof.
  split.
  * done.
  * by intros ?? [??].
  * by intros x y z [??] [??]; split; transitivity y.
Qed.
#[global] Instance: AntiSymm (≡##) (⊆##).
Proof. by split. Qed.
#[global] Instance: Proper ((≡##) ==> iff) disjoint_list.
Proof. intros ?? [Hxs1 Hxs2]. split. by rewrite Hxs1. by rewrite Hxs2. Qed.
#[global] Instance: Proper ((≡##) ==> (≡##) ==> iff) (⊆##).
Proof.
  intros x y [??] z x4 [??]. split; intro.
  * transitivity x; auto. transitivity z; auto. 
  * transitivity y; auto. transitivity x4; auto.
Qed.
#[global] Instance: Proper ((≡ₚ) ==> (≡ₚ) ==> iff) (≡##).
Proof.
  intros xs1 xs2 Hxs12 xs3 xs4 Hxs34. rewrite !sep_disjoint_equiv_alt.
  by setoid_rewrite Hxs12; setoid_rewrite Hxs34.
Qed.
#[global] Instance: Proper ((=) ==> (≡##) ==> (≡##)) (::).
Proof.
  intros ??? ?? [Hxs1 Hxs2]; subst. split. by rewrite Hxs1. by rewrite Hxs2.
Qed.
#[global] Instance: Proper ((≡##) ==> (≡##) ==> (≡##)) (++).
Proof.
  intros ?? [Hxs1 Hxs2] ?? [Hxs3 Hxs4].
  split. by rewrite Hxs1, Hxs3. by rewrite Hxs2, Hxs4.
Qed.
Lemma sep_disjoint_cons_inj x y xs : [x] ≡## [y] → x :: xs ≡## y :: xs.
Proof. intros. change ([x] ++ xs ≡## [y] ++ xs). by f_equiv. Qed.
Lemma sep_disjoint_equiv_empty xs : ∅ :: xs ≡## xs.
Proof.
  by split; intros y; rewrite (Permutation_swap _ y), sep_disjoint_empty_alt.
Qed.
Lemma sep_disjoint_le_union x y xs : x :: y :: xs ⊆## x ∪ y :: xs.
Proof.
  intros y'. rewrite !(Permutation_swap _ y'),
    (sep_disjoint_alt x y), <-sep_disjoint_list_double. by intros [??].
Qed.
Lemma sep_disjoint_equiv_union x y xs : ##[x; y] → x ∪ y :: xs ≡## x :: y :: xs.
Proof.
  split; auto using sep_disjoint_le_union. intros y'.
  rewrite !(Permutation_swap _ y'), (sep_disjoint_alt x y),
    <-sep_disjoint_list_double; tauto.
Qed.
Lemma sep_disjoint_le_union_list xs1 xs2 : xs1 ++ xs2 ⊆## ⋃ xs1 :: xs2.
Proof.
  intros y. rewrite !(Permutation_swap _ y), Permutation_middle,
    sep_disjoint_list_alt; tauto.
Qed.
Lemma sep_disjoint_le_union_list_singleton xs : xs ⊆## [⋃ xs].
Proof. by rewrite <-sep_disjoint_le_union_list, (right_id_L [] (++)). Qed.
Lemma sep_disjoint_equiv_union_list xs1 xs2: ## xs1 → ⋃ xs1 :: xs2 ≡## xs1 ++ xs2.
Proof.
  split; auto using sep_disjoint_le_union_list.
  intros y. rewrite !(Permutation_swap _ y), Permutation_middle,
    sep_disjoint_list_alt; tauto.
Qed.
Lemma sep_disjoint_equiv_union_list_singleton xs : ## xs → [⋃ xs] ≡## xs.
Proof.
  intros. by rewrite sep_disjoint_equiv_union_list, (right_id_L [] (++)).
Qed.
Lemma sep_disjoint_equiv_difference x y xs :
  x ⊆ y → y :: xs ≡## x :: y ∖ x :: xs.
Proof.
  intros. by rewrite <-sep_disjoint_equiv_union, sep_union_difference
    by auto using sep_disjoint_difference.
Qed.
Lemma sep_subseteq_disjoint_le x y xs : x ⊆ y → y :: xs ⊆## x :: xs.
Proof.
  rewrite sep_subseteq_spec; intros (z&->&?); intros y.
  rewrite sep_disjoint_equiv_union by done; intros Hyxz.
  apply (sep_disjoint_contains _ _ Hyxz); solve_submseteq.
Qed.
Lemma sep_difference_distr_l x y z :
  z ⊆ x → ## [x; y] → (x ∪ y) ∖ z = (x ∖ z) ∪ y.
Proof.
  intros. apply (sep_cancel_l _ _ z).
  { by apply sep_disjoint_difference, sep_union_subseteq_l_transitive. }
  { by rewrite <-sep_disjoint_le_union, <-sep_disjoint_equiv_difference. }
  assert ( ## [z; x ∖ z; y]) by (by rewrite <-sep_disjoint_equiv_difference).
  by rewrite sep_associative, !sep_union_difference
    by auto using sep_union_subseteq_l_transitive.
Qed.
Lemma sep_difference_distr_r x y z :
  z ⊆ y → ## [x; y] → (x ∪ y) ∖ z = x ∪ (y ∖ z).
Proof.
  intros. assert ( ## [y ∖ z; x]).
  { apply (disjoint_list_cons z).
    rewrite <-sep_disjoint_equiv_difference; eauto. }
  by rewrite !(sep_commutative x), sep_difference_distr_l by eauto.
Qed.
Lemma sep_disjoint_equiv_half x xs :
  sep_splittable x → ½ x :: ½ x :: xs ≡## x :: xs.
Proof.
  intros. by rewrite <-sep_disjoint_equiv_union, sep_union_half
    by auto using sep_disjoint_half.
Qed.

(** ** Properties with respect to vectors *)
Lemma sep_disjoint_equiv_insert {n} (xs : vec A n) (i : fin n) x :
  vinsert i x xs ≡## x :: delete (fin_to_nat i) (vec_to_list xs).
Proof.
  induction xs as [|x' ? xs IH]; inv_fin i; simpl; [done|intros i].
  by rewrite Permutation_swap, IH.
Qed.
Lemma sep_disjoint_equiv_delete {n} (xs : vec A n) (i : fin n) :
  xs !!! i :: delete (fin_to_nat i) (vec_to_list xs) ≡## xs.
Proof. by rewrite <-sep_disjoint_equiv_insert, vlookup_insert_self. Qed.
Lemma sep_union_delete {n} (xs : vec A n) (i : fin n) :
  ## xs → xs !!! i ∪ ⋃ delete (fin_to_nat i) (vec_to_list xs) = ⋃ xs.
Proof.
  induction xs as [|x ? xs IH]; inversion_clear 1; inv_fin i; simpl; [done|].
  intros i.
  assert (## [xs !!! i; ⋃ (delete (fin_to_nat i) (vec_to_list xs)); x]) as Hxs.
  { rewrite <-sep_disjoint_le_union_list, app_comm_cons,
      sep_disjoint_equiv_delete, sep_disjoint_list_alt; auto. }
  rewrite (sep_commutative x), sep_associative
    by (apply (sep_disjoint_contains _ _ Hxs); solve_submseteq).
  by rewrite IH, sep_commutative by auto.
Qed.
Lemma sep_union_insert {n} (xs : vec A n) (i : fin n) x :
  ## (x :: delete (fin_to_nat i) (vec_to_list xs)) →
  ⋃ vinsert i x xs = x ∪ ⋃ delete (fin_to_nat i) (vec_to_list xs).
Proof.
  induction xs as [|x' ? xs IH]; inv_fin i; simpl; [done |].
  intros i; rewrite !disjoint_list_cons; simpl; intros (?&?&?).
  assert (## [x; x'; ⋃ delete (fin_to_nat i) (vec_to_list xs)]) as Hxs.
  { constructor; simpl;
      rewrite ?sep_right_id by eauto using sep_disjoint_valid_l; auto. }
  by rewrite IH, !sep_associative, (sep_commutative x') by
    (rewrite <-?(sep_disjoint_equiv_union_list_singleton (delete _ _)) by done;
     by (apply (sep_disjoint_contains _ _ Hxs); solve_submseteq)).
Qed.
Lemma sep_subseteq_lookup {n} (xs : vec A n) (i : fin n) :
  ## xs → xs !!! i ⊆ ⋃ xs.
Proof.
  intros. rewrite <-(sep_union_delete _ i) by done.
  apply sep_union_subseteq_l.
  rewrite Permutation_swap, <-sep_disjoint_le_union_list, (comm (++)).
  by simpl; rewrite sep_disjoint_equiv_delete.
Qed.

(** ** Properties lifted to lists *)
Lemma seps_subseteq_empty xs n :
  length xs = n → Forall sep_valid xs → replicate n ∅ ⊆* xs.
Proof. eauto using Forall2_replicate_l, Forall_impl, sep_subseteq_empty. Qed.
Lemma seps_left_id xs ys : xs ##* ys → Forall (∅ =.) xs → xs ∪* ys = ys.
Proof.
  induction 1; intros; decompose_Forall_hyps;
    f_equal; eauto using sep_left_id, sep_disjoint_valid_l.
Qed.
Lemma seps_right_id xs ys : xs ##* ys → Forall (∅ =.) ys → xs ∪* ys = xs.
Proof.
  induction 1; intros; decompose_Forall_hyps;
    f_equal; eauto using sep_right_id, sep_disjoint_valid_l.
Qed.
Lemma seps_disjoint_valid_l xs ys : xs ##* ys → Forall sep_valid xs.
Proof. induction 1; simpl; constructor; eauto using sep_disjoint_valid_l. Qed.
Lemma seps_union_valid xs ys : xs ##* ys → Forall sep_valid (xs ∪* ys).
Proof. induction 1; simpl; constructor; auto using sep_union_valid. Qed.
Lemma seps_positive_l xs ys :
  xs ##* ys → Forall (∅ =.) (xs ∪* ys) → Forall (∅ =.) xs.
Proof.
  induction 1; intros; decompose_Forall_hyps;
    eauto using sep_positive_l', eq_sym.
Qed.
Lemma seps_positive_r xs ys :
  xs ##* ys → Forall (∅ =.) (xs ∪* ys) → Forall (∅ =.) ys.
Proof.
  induction 1; intros; decompose_Forall_hyps;
    eauto using sep_positive_r', eq_sym.
Qed.
Lemma seps_union_empty xs ys :
  Forall (∅ =.) xs → Forall (∅ =.) ys → Forall (∅ =.) (xs ∪* ys).
Proof.
  intros Hxs. revert ys. induction Hxs; intros ? [|????];
    simplify_equality'; auto using sep_left_id, sep_empty_valid, eq_sym.
Qed.
Lemma seps_unmapped_union_l xs ys :
  xs ##* ys → Forall sep_unmapped (xs ∪* ys) → Forall sep_unmapped xs.
Proof.
  induction 1; intros; decompose_Forall_hyps;
    eauto using sep_unmapped_union_l'.
Qed.
Lemma seps_unmapped_union_r xs ys :
  xs ##* ys → Forall sep_unmapped (xs ∪* ys) → Forall sep_unmapped ys.
Proof.
  induction 1; intros; decompose_Forall_hyps;
    eauto using sep_unmapped_union_r'.
Qed.
Lemma seps_unmapped_union xs ys :
  xs ##* ys → Forall sep_unmapped xs → Forall sep_unmapped ys →
  Forall sep_unmapped (xs ∪* ys).
Proof.
  induction 1; intros; decompose_Forall_hyps;
    eauto using sep_unmapped_union_2'.
Qed.
Lemma seps_commutative xs ys : xs ##* ys → xs ∪* ys = ys ∪* xs.
Proof. induction 1; f_equal'; eauto using sep_commutative'. Qed.
Lemma seps_disjoint_ll xs ys zs : xs ##* ys → xs ∪* ys ##* zs → xs ##* zs.
Proof.
  intros Hxs. revert zs. induction Hxs; intros;
    decompose_Forall_hyps; constructor; eauto using sep_disjoint_ll.
Qed.
Lemma seps_disjoint_lr xs ys zs: xs ##* ys → xs ∪* ys ##* zs → ys ##* zs.
Proof.
  intros Hxs. revert zs. induction Hxs; intros;
    decompose_Forall_hyps; constructor; eauto using sep_disjoint_lr.
Qed.
Lemma seps_disjoint_rl xs ys zs : ys ##* zs → xs ##* ys ∪* zs → xs ##* ys.
Proof.
  intros Hys. revert xs. induction Hys; intros;
    decompose_Forall_hyps; constructor; eauto using sep_disjoint_rl.
Qed.
Lemma seps_disjoint_rr xs ys zs : ys ##* zs → xs ##* ys ∪* zs → xs ##* zs.
Proof.
  intros Hys. revert xs. induction Hys; intros;
    decompose_Forall_hyps; constructor; eauto using sep_disjoint_rr.
Qed.
Lemma seps_disjoint_move_l xs ys zs :
  xs ##* ys → xs ∪* ys ##* zs → xs ##* ys ∪* zs.
Proof.
  intros Hxs. revert zs. induction Hxs; intros;
    decompose_Forall_hyps; constructor; auto using sep_disjoint_move_l.
Qed.
Lemma seps_disjoint_move_r xs ys zs :
  ys ##* zs → xs ##* ys ∪* zs → xs ∪* ys ##* zs.
Proof.
  intros Hys. revert xs. induction Hys; intros;
    decompose_Forall_hyps; constructor; auto using sep_disjoint_move_r.
Qed.
Lemma seps_associative xs ys zs :
  ys ##* zs → xs ##* ys ∪* zs → xs ∪* (ys ∪* zs) = xs ∪* ys ∪* zs.
Proof.
  intros Hxs. revert xs. induction Hxs; intros;
    decompose_Forall_hyps; f_equal; auto using sep_associative'.
Qed.
Lemma seps_associative_rev xs ys zs :
  xs ##* ys → xs ∪* ys ##* zs → xs ∪* ys ∪* zs = xs ∪* (ys ∪* zs).
Proof.
  eauto using eq_sym, seps_associative,seps_disjoint_move_l, seps_disjoint_lr.
Qed.
Lemma seps_permute xs ys zs :
  xs ##* ys → xs ∪* ys ##* zs → xs ∪* ys ∪* zs = xs ∪* zs ∪* ys.
Proof.
  intros Hxs. revert zs. induction Hxs; intros;
    decompose_Forall_hyps; f_equal; auto using sep_permute.
Qed.
Lemma seps_cancel_l xs ys zs :
  zs ##* xs → zs ##* ys → zs ∪* xs = zs ∪* ys → xs = ys.
Proof.
  intros Hzs. revert ys. induction Hzs; intros; decompose_Forall_hyps;
    f_equal; eauto using sep_cancel_l'.
Qed.
Lemma seps_cancel_r xs ys zs :
  xs ##* zs → ys ##* zs → xs ∪* zs = ys ∪* zs → xs = ys.
Proof.
  intros Hzs. revert ys. induction Hzs; intros; decompose_Forall_hyps;
    f_equal; eauto using sep_cancel_r'.
Qed.
Lemma seps_cancel_empty_l xs ys : xs ##* ys → xs ∪* ys = ys → Forall (∅ =.) xs.
Proof. induction 1; naive_solver eauto using sep_cancel_empty_l, eq_sym. Qed.
Lemma seps_cancel_empty_r xs ys : xs ##* ys → xs ∪* ys = xs → Forall (∅ =.) ys.
Proof. induction 1; naive_solver eauto using sep_cancel_empty_r, eq_sym. Qed.
Lemma seps_reflexive xs : Forall sep_valid xs → xs ⊆* xs.
Proof. induction 1; simpl; auto using sep_reflexive. Qed.
Lemma seps_union_subseteq_l xs ys : xs ##* ys → xs ⊆* xs ∪* ys.
Proof. induction 1; simpl; auto using sep_union_subseteq_l'. Qed.
Lemma seps_union_subseteq_r xs ys : xs ##* ys → ys ⊆* xs ∪* ys.
Proof. induction 1; simpl; auto using sep_union_subseteq_r'. Qed.
Lemma seps_disjoint_difference xs1 xs2 : xs1 ⊆* xs2 → xs1 ##* xs2 ∖* xs1.
Proof. induction 1; constructor; auto using sep_disjoint_difference'. Qed.
Lemma seps_difference_valid xs ys : xs ⊆* ys → Forall sep_valid (ys ∖* xs).
Proof. induction 1; simpl; auto using sep_difference_valid. Qed.
Lemma seps_union_difference xs ys : xs ⊆* ys → xs ∪* ys ∖* xs = ys.
Proof. induction 1; f_equal'; auto using sep_union_difference. Qed.
Lemma seps_difference_empty_rev xs ys :
  xs ⊆* ys → Forall (∅ =.) (ys ∖* xs) → xs = ys.
Proof.
  induction 1; intros; decompose_Forall_hyps;
    f_equal; auto using sep_difference_empty_rev.
Qed.
Lemma seps_unmapped_difference_1 xs ys :
  xs ⊆* ys → Forall sep_unmapped xs →
  Forall sep_unmapped (ys ∖* xs) → Forall sep_unmapped ys.
Proof.
  induction 1; intros; decompose_Forall_hyps;
    eauto using sep_unmapped_difference_1.
Qed.
Lemma seps_unmapped_difference_2 xs ys :
  xs ⊆* ys → Forall sep_unmapped ys → Forall sep_unmapped (ys ∖* xs).
Proof.
  induction 1; intros; decompose_Forall_hyps;
    eauto using sep_unmapped_difference_2.
Qed.
Lemma seps_splittable_union xs : xs ##* xs → Forall sep_splittable (xs ∪* xs).
Proof.
  induction xs; intros; decompose_Forall_hyps;
    constructor; eauto using sep_splittable_union'.
Qed.
Lemma seps_splittable_weaken xs ys :
  Forall sep_splittable ys → xs ⊆* ys → Forall sep_splittable xs.
Proof.
  induction 2; decompose_Forall_hyps; eauto using sep_splittable_weaken.
Qed.
Lemma seps_disjoint_half xs : Forall sep_splittable xs → ½* xs ##* ½* xs.
Proof. induction 1; csimpl; auto using sep_disjoint_half'. Qed.
Lemma seps_union_half xs : Forall sep_splittable xs → ½* xs ∪* ½* xs = xs.
Proof. induction 1; f_equal'; auto using sep_union_half. Qed.
Lemma seps_unmapped_half_1 xs :
  Forall sep_splittable xs →
  Forall sep_unmapped (½* xs) → Forall sep_unmapped xs.
Proof. induction 1; inversion_clear 1; auto using sep_unmapped_half_1. Qed.
Lemma seps_half_empty_rev xs :
  Forall sep_splittable xs → Forall (∅ =.) (½* xs) → Forall (∅ =.) xs.
Proof.
  induction 1; inversion_clear 1; auto using sep_half_empty_rev, eq_sym.
Qed.
Lemma seps_union_half_distr xs ys :
  xs ##* ys → Forall sep_splittable (xs ∪* ys) → ½* (xs ∪* ys) = ½* xs ∪* ½* ys.
Proof.
  induction 1; intros; decompose_Forall_hyps;
    f_equal; auto using sep_union_half_distr'.
Qed.
Lemma seps_unmapped_valid xs : Forall sep_unmapped xs → Forall sep_valid xs.
Proof. induction 1; simpl; auto using sep_unmapped_valid. Qed.
Lemma seps_unshared_valid xs : Forall sep_unshared xs → Forall sep_valid xs.
Proof. induction 1; simpl; auto using sep_unshared_valid. Qed.
Lemma seps_disjoint_unshared_unmapped xs ys :
  xs ##* ys → Forall sep_unshared xs → Forall sep_unmapped ys.
Proof.
  induction 1; inversion_clear 1; eauto using sep_disjoint_unshared_unmapped.
Qed.
Lemma seps_unshared_weaken xs ys :
  Forall sep_unshared xs → xs ⊆* ys → Forall sep_unshared ys.
Proof.
  induction 2; decompose_Forall_hyps; eauto using sep_unshared_weaken.
Qed.
Lemma seps_unshared_unmapped xs :
  Forall sep_unshared xs → Forall (not ∘ sep_unmapped) xs.
Proof. induction 1; eauto using sep_unshared_unmapped. Qed.
End separation.

(** * Tactic *)
(** The tactic [solve_sep_disjoint] solves goals of the shape [## xs]. It first
eliminates all occurences of [∅], [∪], and [⋃] from the hypotheses using the
tactic [simplify_sep_disjoint_hyps]. Then it performs the same job on the
conclusion and finally tries to prove that one of assumptions implies the
conclusion. *)
Ltac solve_simple_sep_disjoint :=
  repeat first
  [ rewrite sep_disjoint_equiv_empty
  | rewrite <-sep_disjoint_le_union_list
  | rewrite <-sep_disjoint_le_union ];
  match goal with
  | _ => done
  | |- ## [] => by apply disjoint_list_nil
  | H : ## ?xs2 |- ## ?xs1 => apply (sep_disjoint_contains _ _ H); solve_submseteq
  end.
Ltac simplify_sep_disjoint_hyps := repeat
  match goal with
  | H : sep_valid _ |- _ => apply sep_disjoint_list_singleton in H
  | H : ## [] |- _ => clear H
  | H : ?x ## ?y |- _ => apply sep_disjoint_list_double in H
  | H : ## ?xs |- _ =>
    progress repeat first
    [ rewrite sep_disjoint_equiv_empty in H
    | rewrite sep_disjoint_equiv_union_list in H by solve_simple_sep_disjoint
    | rewrite sep_disjoint_equiv_union in H by solve_simple_sep_disjoint ]
  end.
Ltac solve_sep_disjoint :=
  match goal with
  | |- ## [] => by apply disjoint_list_nil
  | |- ## [_] => by apply sep_disjoint_list_singleton
  | |- ## _ => try done
  | |- sep_valid _ => done || apply sep_disjoint_list_singleton
  | |- _ ## _ => done || apply sep_disjoint_list_double
  end;
  simplify_sep_disjoint_hyps; solve_simple_sep_disjoint.
