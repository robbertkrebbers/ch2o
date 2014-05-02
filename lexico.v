(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This files defines a lexicographic order on various common data structures
and proves that it is a partial order having a strong variant of trichotomy. *)
Require Import numbers.

Notation cast_trichotomy T :=
  match T with
  | inleft (left _) => inleft (left _)
  | inleft (right _) => inleft (right _)
  | inright _ => inright _
  end.

Instance prod_lexico `{Lexico A, Lexico B} : Lexico (A * B) := λ p1 p2,
  (**i 1.) *) lexico (p1.1) (p2.1) ∨
  (**i 2.) *) p1.1 = p2.1 ∧ lexico (p1.2) (p2.2).

Instance bool_lexico : Lexico bool := λ b1 b2,
  match b1, b2 with false, true => True | _, _ => False end.
Instance nat_lexico : Lexico nat := (<).
Instance N_lexico : Lexico N := (<)%N.
Instance Z_lexico : Lexico Z := (<)%Z.
Typeclasses Opaque bool_lexico nat_lexico N_lexico Z_lexico.
Instance list_lexico `{Lexico A} : Lexico (list A) :=
  fix go l1 l2 :=
  let _ : Lexico (list A) := @go in
  match l1, l2 with
  | [], _ :: _ => True
  | x1 :: l1, x2 :: l2 => lexico (x1,l1) (x2,l2)
  | _, _ => False
  end.
Instance sig_lexico `{Lexico A} (P : A → Prop) `{∀ x, ProofIrrel (P x)} :
  Lexico (sig P) := λ x1 x2, lexico (`x1) (`x2).

Lemma prod_lexico_irreflexive `{Lexico A, Lexico B, !Irreflexive (@lexico A _)}
  (x : A) (y : B) : complement lexico y y → complement lexico (x,y) (x,y).
Proof. intros ? [?|[??]]. by apply (irreflexivity lexico x). done. Qed.
Lemma prod_lexico_transitive `{Lexico A, Lexico B, !Transitive (@lexico A _)}
    (x1 x2 x3 : A) (y1 y2 y3 : B) :
  lexico (x1,y1) (x2,y2) → lexico (x2,y2) (x3,y3) →
  (lexico y1 y2 → lexico y2 y3 → lexico y1 y3) → lexico (x1,y1) (x3,y3).
Proof.
  intros Hx12 Hx23 ?; revert Hx12 Hx23. unfold lexico, prod_lexico.
  intros [|[??]] [?|[??]]; simplify_equality'; auto.
  by left; transitivity x2.
Qed.

Instance prod_lexico_po `{Lexico A, Lexico B, !StrictOrder (@lexico A _)}
  `{!StrictOrder (@lexico B _)} : StrictOrder (@lexico (A * B) _).
Proof.
  split.
  * intros [x y]. apply prod_lexico_irreflexive.
    by apply (irreflexivity lexico y).
  * intros [??] [??] [??] ??.
    eapply prod_lexico_transitive; eauto. apply transitivity.
Qed.
Instance prod_lexico_trichotomyT `{Lexico A, tA : !TrichotomyT (@lexico A _)}
  `{Lexico B, tB : !TrichotomyT (@lexico B _)}: TrichotomyT (@lexico (A * B) _).
Proof.
 red; refine (λ p1 p2,
  match trichotomyT lexico (p1.1) (p2.1) with
  | inleft (left _) => inleft (left _)
  | inleft (right _) => cast_trichotomy (trichotomyT lexico (p1.2) (p2.2))
  | inright _ => inright _
  end); clear tA tB;
    abstract (unfold lexico, prod_lexico; auto using injective_projections).
Defined.

Instance bool_lexico_po : StrictOrder (@lexico bool _).
Proof. split. by intros [] ?. by intros [] [] [] ??. Qed.
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

Instance nat_lexico_po : StrictOrder (@lexico nat _).
Proof. unfold lexico, nat_lexico. apply _. Qed.
Instance nat_lexico_trichotomy: TrichotomyT (@lexico nat _).
Proof.
 red; refine (λ n1 n2,
  match Nat.compare n1 n2 as c return Nat.compare n1 n2 = c → _ with
  | Lt => λ H, inleft (left (nat_compare_Lt_lt _ _ H))
  | Eq => λ H, inleft (right (nat_compare_eq _ _ H))
  | Gt => λ H, inright (nat_compare_Gt_gt _ _ H)
  end eq_refl).
Defined.

Instance N_lexico_po : StrictOrder (@lexico N _).
Proof. unfold lexico, N_lexico. apply _. Qed.
Instance N_lexico_trichotomy: TrichotomyT (@lexico N _).
Proof.
 red; refine (λ n1 n2,
  match N.compare n1 n2 as c return N.compare n1 n2 = c → _ with
  | Lt => λ H, inleft (left (proj2 (N.compare_lt_iff _ _) H))
  | Eq => λ H, inleft (right (N.compare_eq _ _ H))
  | Gt => λ H, inright (proj1 (N.compare_gt_iff _ _) H)
  end eq_refl).
Defined.

Instance Z_lexico_po : StrictOrder (@lexico Z _).
Proof. unfold lexico, Z_lexico. apply _. Qed.
Instance Z_lexico_trichotomy: TrichotomyT (@lexico Z _).
Proof.
 red; refine (λ n1 n2,
  match Z.compare n1 n2 as c return Z.compare n1 n2 = c → _ with
  | Lt => λ H, inleft (left (proj2 (Z.compare_lt_iff _ _) H))
  | Eq => λ H, inleft (right (Z.compare_eq _ _ H))
  | Gt => λ H, inright (proj1 (Z.compare_gt_iff _ _) H)
  end eq_refl).
Defined.

Instance list_lexico_po `{Lexico A, !StrictOrder (@lexico A _)} :
  StrictOrder (@lexico (list A) _).
Proof.
  split.
  * intros l. induction l. by intros ?. by apply prod_lexico_irreflexive.
  * intros l1. induction l1 as [|x1 l1]; intros [|x2 l2] [|x3 l3] ??; try done.
    eapply prod_lexico_transitive; eauto.
Qed.
Instance list_lexico_trichotomy `{Lexico A, tA : !TrichotomyT (@lexico A _)} :
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
  end); clear tA go go';
    abstract (repeat (done || constructor || congruence || by inversion 1)).
Defined.

Instance sig_lexico_po `{Lexico A, !StrictOrder (@lexico A _)}
  (P : A → Prop) `{∀ x, ProofIrrel (P x)} : StrictOrder (@lexico (sig P) _).
Proof.
  unfold lexico, sig_lexico. split.
  * intros [x ?] ?. by apply (irreflexivity lexico x). 
  * intros [x1 ?] [x2 ?] [x3 ?] ??. by transitivity x2.
Qed.
Instance sig_lexico_trichotomy `{Lexico A, tA : !TrichotomyT (@lexico A _)}
  (P : A → Prop) `{∀ x, ProofIrrel (P x)} : TrichotomyT (@lexico (sig P) _).
Proof.
 red; refine (λ x1 x2, cast_trichotomy (trichotomyT lexico (`x1) (`x2)));
  abstract (repeat (done || constructor || apply (sig_eq_pi P))).
Defined.
