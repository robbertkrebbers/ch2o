(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This files defines a lexicographic order on various common data structures
and proves that it is a partial order having a strong variant of trichotomy. *)
Require Import orders.

Notation cast_trichotomy T :=
  match T with
  | inleft (left _) => inleft (left _)
  | inleft (right _) => inleft (right _)
  | inright _ => inright _
  end.

Instance prod_lexico `{Lexico A} `{Lexico B} : Lexico (A * B) := λ p1 p2,
  (**i 1.) *) strict lexico (fst p1) (fst p2) ∨
  (**i 2.) *) fst p1 = fst p2 ∧ lexico (snd p1) (snd p2).

Lemma prod_lexico_strict `{Lexico A} `{Lexico B} (p1 p2 : A * B) :
  strict lexico p1 p2 ↔
    strict lexico (fst p1) (fst p2) ∨
    fst p1 = fst p2 ∧ strict lexico (snd p1) (snd p2).
Proof.
  destruct p1, p2. repeat (unfold lexico, prod_lexico, strict). naive_solver.
Qed.

Instance bool_lexico : Lexico bool := (→).
Instance nat_lexico : Lexico nat := (≤).
Instance N_lexico : Lexico N := (≤)%N.
Instance Z_lexico : Lexico Z := (≤)%Z.
Typeclasses Opaque bool_lexico nat_lexico N_lexico Z_lexico.
Instance list_lexico `{Lexico A} : Lexico (list A) :=
  fix go l1 l2 :=
  let _ : Lexico (list A) := @go in
  match l1, l2 with
  | [], _ => True
  | _ :: _, [] => False
  | x1 :: l1, x2 :: l2 => lexico (x1,l1) (x2,l2)
  end.
Instance sig_lexico `{Lexico A} (P : A → Prop) `{∀ x, ProofIrrel (P x)} :
  Lexico (sig P) := λ x1 x2, lexico (`x1) (`x2).

Lemma prod_lexico_reflexive `{Lexico A} `{!PartialOrder (@lexico A _)}
  `{Lexico B} (x : A) (y : B) : lexico y y → lexico (x,y) (x,y).
Proof. by right. Qed.
Lemma prod_lexico_transitive `{Lexico A} `{!PartialOrder (@lexico A _)}
    `{Lexico B} (x1 x2 x3 : A) (y1 y2 y3 : B) :
  lexico (x1,y1) (x2,y2) → lexico (x2,y2) (x3,y3) →
  (lexico y1 y2 → lexico y2 y3 → lexico y1 y3) → lexico (x1,y1) (x3,y3).
Proof.
  intros Hx12 Hx23 ?; revert Hx12 Hx23. unfold lexico, prod_lexico.
  intros [|[??]] [?|[??]]; simplify_equality'; auto. left. by transitivity x2.
Qed.
Lemma prod_lexico_anti_symmetric `{Lexico A} `{!PartialOrder (@lexico A _)}
    `{Lexico B} (x1 x2 : A) (y1 y2 : B) :
  lexico (x1,y1) (x2,y2) → lexico (x2,y2) (x1,y1) →
  (lexico y1 y2 → lexico y2 y1 → y1 = y2) → x1 = x2 ∧ y1 = y2.
Proof. by intros [[??]|[??]] [[??]|[??]] ?; simplify_equality'; auto. Qed.
Instance prod_lexico_po `{Lexico A} `{Lexico B} `{!PartialOrder (@lexico A _)}
  `{!PartialOrder (@lexico B _)} : PartialOrder (@lexico (A * B) _).
Proof.
  repeat split.
  * by intros [??]; apply prod_lexico_reflexive.
  * intros [??] [??] [??] ??.
    eapply prod_lexico_transitive; eauto. apply @transitivity, _.
  * intros [x1 y1] [x2 y2] ??.
    destruct (prod_lexico_anti_symmetric x1 x2 y1 y2); try intuition congruence.
    apply (anti_symmetric _).
Qed.
Instance prod_lexico_trichotomyT `{Lexico A} `{tA: !TrichotomyT (@lexico A _)}
  `{Lexico B} `{tB:!TrichotomyT (@lexico B _)}: TrichotomyT (@lexico (A * B) _).
Proof.
 red; refine (λ p1 p2,
  match trichotomyT lexico (fst p1) (fst p2) with
  | inleft (left _) => inleft (left _)
  | inleft (right _) =>
    cast_trichotomy (trichotomyT lexico (snd p1) (snd p2))
  | inright _ => inright _
  end); clear tA tB; abstract (rewrite ?prod_lexico_strict;
    intuition (auto using injective_projections with congruence)).
Defined.

Instance bool_lexico_po : PartialOrder (@lexico bool _).
Proof.
  unfold lexico, bool_lexico. repeat split.
  * intros []; simpl; tauto.
  * intros [] [] []; simpl; tauto.
  * intros [] []; simpl; tauto.
Qed.
Instance bool_lexico_trichotomy: TrichotomyT (@lexico bool _).
Proof.
 red; refine (λ b1 b2,
  match b1, b2 with
  | false, false => inleft (right _)
  | false, true => inleft (left _)
  | true, false => inright _
  | true, true => inleft (right _)
  end); abstract (unfold strict, lexico, bool_lexico; naive_solver).
Defined.

Lemma nat_lexico_strict (x1 x2 : nat) : strict lexico x1 x2 ↔ x1 < x2.
Proof. unfold strict, lexico, nat_lexico. lia. Qed.
Instance nat_lexico_po : PartialOrder (@lexico nat _).
Proof. unfold lexico, nat_lexico. apply _. Qed.
Instance nat_lexico_trichotomy: TrichotomyT (@lexico nat _).
Proof.
 red; refine (λ n1 n2,
  match Nat.compare n1 n2 as c return Nat.compare n1 n2 = c → _ with
  | Lt => λ H,
    inleft (left (proj2 (nat_lexico_strict _ _) (nat_compare_Lt_lt _ _ H)))
  | Eq => λ H, inleft (right (nat_compare_eq _ _ H))
  | Gt => λ H,
    inright (proj2 (nat_lexico_strict _ _) (nat_compare_Gt_gt _ _ H))
  end eq_refl).
Defined.

Lemma N_lexico_strict (x1 x2 : N) : strict lexico x1 x2 ↔ (x1 < x2)%N.
Proof. unfold strict, lexico, N_lexico. lia. Qed.
Instance N_lexico_po : PartialOrder (@lexico N _).
Proof. unfold lexico, N_lexico. apply _. Qed.
Instance N_lexico_trichotomy: TrichotomyT (@lexico N _).
Proof.
 red; refine (λ n1 n2,
  match N.compare n1 n2 as c return N.compare n1 n2 = c → _ with
  | Lt => λ H,
    inleft (left (proj2 (N_lexico_strict _ _) (proj2 (N.compare_lt_iff _ _) H)))
  | Eq => λ H, inleft (right (N.compare_eq _ _ H))
  | Gt => λ H,
    inright (proj2 (N_lexico_strict _ _) (proj1 (N.compare_gt_iff _ _) H))
  end eq_refl).
Defined.

Lemma Z_lexico_strict (x1 x2 : Z) : strict lexico x1 x2 ↔ (x1 < x2)%Z.
Proof. unfold strict, lexico, Z_lexico. lia. Qed.
Instance Z_lexico_po : PartialOrder (@lexico Z _).
Proof. unfold lexico, Z_lexico. apply _. Qed.
Instance Z_lexico_trichotomy: TrichotomyT (@lexico Z _).
Proof.
 red; refine (λ n1 n2,
  match Z.compare n1 n2 as c return Z.compare n1 n2 = c → _ with
  | Lt => λ H,
    inleft (left (proj2 (Z_lexico_strict _ _) (proj2 (Z.compare_lt_iff _ _) H)))
  | Eq => λ H, inleft (right (Z.compare_eq _ _ H))
  | Gt => λ H,
    inright (proj2 (Z_lexico_strict _ _) (proj1 (Z.compare_gt_iff _ _) H))
  end eq_refl).
Defined.

Instance list_lexico_po `{Lexico A} `{!PartialOrder (@lexico A _)} :
  PartialOrder (@lexico (list A) _).
Proof.
  repeat split.
  * intros l. induction l. done. by apply prod_lexico_reflexive.
  * intros l1. induction l1 as [|x1 l1]; intros [|x2 l2] [|x3 l3] ??; try done.
    eapply prod_lexico_transitive; eauto.
  * intros l1. induction l1 as [|x1 l1]; intros [|x2 l2] ??; try done.
    destruct (prod_lexico_anti_symmetric x1 x2 l1 l2); naive_solver.
Qed.
Instance list_lexico_trichotomy `{Lexico A} `{!TrichotomyT (@lexico A _)} :
  TrichotomyT (@lexico (list A) _).
Proof.
 refine (
  fix go l1 l2 :=
  let go' : TrichotomyT (@lexico (list A) _) := @go in
  match l1, l2 with
  | [], [] => inleft (right _)
  | [], _ :: _ => inleft (left _)
  | _ :: _, [] => inright _
  | x1 :: l1, x2 :: l2 => cast_trichotomy (trichotomyT lexico (x1,l1) (x2,l2))
  end); clear go go';
  abstract (repeat (done || constructor || congruence || by inversion 1)).
Defined.

Instance sig_lexico_po `{Lexico A} `{!PartialOrder (@lexico A _)}
  (P : A → Prop) `{∀ x, ProofIrrel (P x)} : PartialOrder (@lexico (sig P) _).
Proof.
  unfold lexico, sig_lexico. repeat split.
  * by intros [??].
  * intros [x1 ?] [x2 ?] [x3 ?] ??. by simplify_order.
  * intros [x1 ?] [x2 ?] ??. apply (sig_eq_pi _). by simplify_order.
Qed.
Instance sig_lexico_trichotomy `{Lexico A} `{tA: !TrichotomyT (@lexico A _)}
  (P : A → Prop) `{∀ x, ProofIrrel (P x)} : TrichotomyT (@lexico (sig P) _).
Proof.
 red; refine (λ x1 x2, cast_trichotomy (trichotomyT lexico (`x1) (`x2)));
  abstract (repeat (done || constructor || apply (sig_eq_pi P))).
Defined.
