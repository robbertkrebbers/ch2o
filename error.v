(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export list.

Instance error_ret {E} : MRet (sum E) := λ A, inr.
Instance error_bind {E} : MBind (sum E) := λ A B f x,
  match x with inr a => f a | inl e => inl e end.
Instance error_fmap {E} : FMap (sum E) := λ A B f x,
  match x with inr a => inr (f a) | inl e => inl e end.

Definition error_guard {E} P {dec : Decision P} {A}
    (e : E) (f : P → E + A) : E + A :=
  match decide P with left H => f H | right _ => inl e end.
Notation "'guard' P 'with' e ; o" := (error_guard P e (λ _, o))
  (at level 65, next at level 35, only parsing, right associativity) : C_scope.
Definition error_of_option {A E} (x : option A) (e : E) : sum E A :=
  match x with Some a => inr a | None => inl e end.

Tactic Notation "case_error_guard" "as" ident(Hx) :=
  match goal with
  | H : context C [@error_guard _ ?P ?dec _ ?e ?x] |- _ =>
    let X := context C [ match dec with left H => x H | _ => inl e end ] in
    change X in H; destruct_decide dec as Hx
  | |- context C [@error_guard _ ?P ?dec _ ?e ?x] =>
    let X := context C [ match dec with left H => x H | _ => inl e end ] in
    change X; destruct_decide dec as Hx
  end.
Tactic Notation "case_error_guard" :=
  let H := fresh in case_error_guard as H.

Tactic Notation "simplify_error_equality" :=
  repeat match goal with
  | _ => progress simplify_equality'
  | H : error_of_option ?o ?e = ?x |- _ =>
    match o with Some _ => fail 1 | None => fail 1 | _ => idtac end;
    match x with inr _ => idtac | inl _ => idtac | _ => fail 1 end;
    let y := fresh in destruct o as [y|] eqn:?;
      [change (inr y = x) in H|change (inl e = x) in H]
  | H : mbind (M:=sum _) ?f ?o = ?x |- _ =>
    match o with inr _ => fail 1 | inl _ => fail 1 | _ => idtac end;
    match x with inr _ => idtac | inl _ => idtac | _ => fail 1 end;
    let e := fresh in let y := fresh in destruct o as [e|y] eqn:?;
      [change (inl e = x) in H|change (f y = x) in H]
  | H : ?x = mbind (M:=sum _) ?f ?o |- _ =>
    match o with inr _ => fail 1 | inl _ => fail 1 | _ => idtac end;
    match x with inr _ => idtac | inl _ => idtac | _ => fail 1 end;
    let e := fresh in let y := fresh in destruct o as [e|y] eqn:?;
      [change (inl e = x) in H|change (f y = x) in H]
  | H : fmap (M:=sum _) ?f ?o = ?x |- _ =>
    match o with inr _ => fail 1 | inl _ => fail 1 | _ => idtac end;
    match x with inr _ => idtac | inl _ => idtac | _ => fail 1 end;
    let e := fresh in let y := fresh in destruct o as [e|y] eqn:?;
      [change (inl e = x) in H|change (inr (f y) = x) in H]
  | H : ?x = fmap (M:=sum _) ?f ?o |- _ =>
    match o with inr _ => fail 1 | inl _ => fail 1 | _ => idtac end;
    match x with inr _ => idtac | inl _ => idtac | _ => fail 1 end;
    let e := fresh in let y := fresh in destruct o as [e|y] eqn:?;
      [change (inl e = x) in H|change (inr (f y) = x) in H]
  | _ => progress case_decide
  | _ => progress case_error_guard
  end.

Section mapM.
  Context {A B E : Type} (f : A → E + B).

  Lemma error_mapM_ext (g : A → sum E B) l :
    (∀ x, f x = g x) → mapM f l = mapM g l.
  Proof. intros Hfg. by induction l; simpl; rewrite ?Hfg, ?IHl. Qed.
  Lemma error_Forall2_mapM_ext (g : A → E + B) l k :
    Forall2 (λ x y, f x = g y) l k → mapM f l = mapM g k.
  Proof. induction 1 as [|???? Hfg ? IH]; simpl. done. by rewrite Hfg, IH. Qed.
  Lemma error_Forall_mapM_ext (g : A → E + B) l :
    Forall (λ x, f x = g x) l → mapM f l = mapM g l.
  Proof. induction 1 as [|?? Hfg ? IH]; simpl. done. by rewrite Hfg, IH. Qed.
  Lemma mapM_inr_1 l k : mapM f l = inr k → Forall2 (λ x y, f x = inr y) l k.
  Proof.
    revert k. induction l as [|x l]; intros [|y k]; simpl; try done.
    * destruct (f x); simpl; [discriminate|]. by destruct (mapM f l).
    * destruct (f x) eqn:?; simpl; [discriminate|].
      destruct (mapM f l); intros; simplify_equality. constructor; auto.
  Qed.
  Lemma mapM_inr_2 l k : Forall2 (λ x y, f x = inr y) l k → mapM f l = inr k.
  Proof.
    induction 1 as [|???? Hf ? IH]; simpl; [done |].
    rewrite Hf. simpl. by rewrite IH.
  Qed.
  Lemma mapM_inr l k : mapM f l = inr k ↔ Forall2 (λ x y, f x = inr y) l k.
  Proof. split; auto using mapM_inr_1, mapM_inr_2. Qed.
  Lemma error_mapM_length l k : mapM f l = inr k → length l = length k.
  Proof. intros. by eapply Forall2_length, mapM_inr_1. Qed.
End mapM.
