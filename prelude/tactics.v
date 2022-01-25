(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects general purpose tactics that are used throughout
the development. *)

From stdpp Require Import list.
Require Export base.

Ltac injection' H :=
  block_goal; injection H; clear H; intros H; intros; unblock_goal.

Ltac simplify_equality := repeat
  match goal with
  | H : _ ≠ _ |- _ => by destruct H
  | H : _ = _ → False |- _ => by destruct H
  | H : ?x = _ |- _ => subst x
  | H : _ = ?x |- _ => subst x
  | H : _ = _ |- _ => discriminate H
  | H : ?f _ = ?f _ |- _ => apply (inj f) in H
  | H : ?f _ _ = ?f _ _ |- _ => apply (inj2 f) in H; destruct H
    (* before [injection'] to circumvent bug #2939 in some situations *)
  | H : ?f _ = ?f _ |- _ => injection' H
  | H : ?f _ _ = ?f _ _ |- _ => injection' H
  | H : ?f _ _ _ = ?f _ _ _ |- _ => injection' H
  | H : ?f _ _ _ _ = ?f _ _ _ _ |- _ => injection' H
  | H : ?f _ _ _ _ _ = ?f _ _ _ _ _ |- _ => injection' H
  | H : ?f _ _ _ _ _ _ = ?f _ _ _ _ _ _ |- _ => injection' H
  | H : ?x = ?x |- _ => clear H
    (* unclear how to generalize the below *)
  | H1 : ?o = Some ?x, H2 : ?o = Some ?y |- _ =>
    assert (y = x) by congruence; clear H2
  | H1 : ?o = Some ?x, H2 : ?o = None |- _ => congruence
  end.
Ltac simplify_equality' := repeat (progress csimpl in * || simplify_equality).
Ltac f_equal' := csimpl in *; f_equal.
Ltac f_lia :=
  repeat lazymatch goal with
  | |- @eq BinNums.Z _ _ => lia
  | |- @eq nat _ _ => lia
  | |- _ => f_equal
  end.
Ltac f_lia' := csimpl in *; f_lia.

Tactic Notation "decompose_elem_of" hyp(H) :=
  let rec go H :=
  lazymatch type of H with
  | _ ∈ ∅ => apply elem_of_empty in H; destruct H
  | ?x ∈ {[ ?y ]} =>
    apply elem_of_singleton in H; try first [subst y | subst x]
  | ?x ∉ {[ ?y ]} =>
    apply not_elem_of_singleton in H
  | _ ∈ _ ∪ _ =>
    apply elem_of_union in H; destruct H as [H|H]; [go H|go H]
  | _ ∉ _ ∪ _ =>
    let H1 := fresh H in let H2 := fresh H in apply not_elem_of_union in H;
    destruct H as [H1 H2]; go H1; go H2
  | _ ∈ _ ∩ _ =>
    let H1 := fresh H in let H2 := fresh H in apply elem_of_intersection in H;
    destruct H as [H1 H2]; go H1; go H2
  | _ ∈ _ ∖ _ =>
    let H1 := fresh H in let H2 := fresh H in apply elem_of_difference in H;
    destruct H as [H1 H2]; go H1; go H2
  | ?x ∈ _ <$> _ =>
    apply elem_of_fmap in H; destruct H as [? [? H]]; try (subst x); go H
  | _ ∈ _ ≫= _ =>
    let H1 := fresh H in let H2 := fresh H in apply elem_of_bind in H;
    destruct H as [? [H1 H2]]; go H1; go H2
  | ?x ∈ mret ?y =>
    apply elem_of_ret in H; try first [subst y | subst x]
  | _ ∈ mjoin _ ≫= _ =>
    let H1 := fresh H in let H2 := fresh H in apply elem_of_join in H;
    destruct H as [? [H1 H2]]; go H1; go H2
  | _ ∈ guard _; _ =>
    let H1 := fresh H in let H2 := fresh H in apply elem_of_guard in H;
    destruct H as [H1 H2]; go H2
  | _ ∈ option_to_set _ => apply elem_of_option_to_set in H
  | _ ∈ list_to_set _ => apply elem_of_list_to_set in H
  | _ => idtac
  end in go H.
Tactic Notation "decompose_elem_of" :=
  repeat_on_hyps (fun H => decompose_elem_of H).

Ltac decompose_empty := repeat
  match goal with
  | H : ∅ ≡ ∅ |- _ => clear H
  | H : ∅ = ∅ |- _ => clear H
  | H : ∅ ≡ _ |- _ => symmetry in H
  | H : ∅ = _ |- _ => symmetry in H
  | H : _ ∪ _ ≡ ∅ |- _ => apply empty_union in H; destruct H
  | H : _ ∪ _ ≢ ∅ |- _ => apply non_empty_union in H; destruct H
  | H : {[ _ ]} ≡ ∅ |- _ => destruct (non_empty_singleton _ H)
  | H : _ ∪ _ = ∅ |- _ => apply empty_union_L in H; destruct H
  | H : _ ∪ _ ≠ ∅ |- _ => apply non_empty_union_L in H; destruct H
  | H : {[ _ ]} = ∅ |- _ => destruct (non_empty_singleton_L _ H)
  | H : guard _ ; _ ≡ ∅ |- _ => apply guard_empty in H; destruct H
  end.