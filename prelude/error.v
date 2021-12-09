(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Import tactics.
Require Export list.

Definition error (S E A : Type) : Type := S → E + (A * S).

Definition error_eval {S E A} (x : error S E A) (s : S) : E + A :=
  match x s with inl e => inl e | inr (a,_) => inr a end.

#[global] Instance error_ret {S E} : MRet (error S E) := λ A x s, inr (x,s).
#[global] Instance error_bind {S E} : MBind (error S E) := λ A B f x s,
  match x s with
  | inr (a,s') => f a s'
  | inl e => inl e
  end.
#[global] Instance error_fmap {S E} : FMap (error S E) := λ A B f x s,
  match x s with
  | inr (a,s') => inr (f a,s')
  | inl e => inl e
  end.
Definition fail {S E A} (e : E) : error S E A := λ s, inl e.

Definition modify {S E} (f : S → S) : error S E () := λ s, inr ((), f s).
Definition gets {S E A} (f : S → A) : error S E A := λ s, inr (f s, s).

Definition error_guard {E} P {dec : Decision P} {S A}
    (e : E) (f : P → error S E A) : error S E A :=
  match decide P with left H => f H | right _ => fail e end.
Notation "'guard' P 'with' e ; o" := (error_guard P e (λ _, o))
  (at level 20, o at level 200, only parsing, right associativity) : C_scope.
Definition error_of_option {S A E} (x : option A) (e : E) : error S E A :=
  match x with Some a => mret a | None => fail e end.

Lemma error_bind_ret {S E A B} (f : A → error S E B) s s'' x b :
  (x ≫= f) s = mret (M := error S E) b s'' ↔ 
  ∃ a s', x s = mret (M := error S E) a s' ∧ f a s' = mret (M := error S E) b s''.
Proof. compute; destruct (x s) as [|[??]]; naive_solver. Qed.
Lemma error_fmap_ret {S E A B} (f : A → B) s s' (x : error S E A) b :
  (f <$> x) s = mret (M := error S E) b s' ↔ ∃ a, x s = mret (M := error S E) a s' ∧ b = f a.
Proof. compute; destruct (x s) as [|[??]]; naive_solver. Qed.
Lemma error_of_option_ret {S E A} (s s' : S) (o : option A) (e : E) a :
  error_of_option o e s = mret (M := error S E) a s' ↔ o = Some a ∧ s = s'.
Proof. compute; destruct o; naive_solver. Qed.
Lemma error_guard_ret {S E A} `{dec : Decision P} s s' (x : error S E A) e a :
  (guard P with e ; x) s = mret (M := error S E) a s' ↔ P ∧ x s = mret (M := error S E) a s'.
Proof. compute; destruct dec; naive_solver. Qed.
Lemma error_fmap_bind {S E A B C} (f : A → B) (g : B → error S E C) x s :
  ((f <$> x) ≫= g) s = (x ≫= g ∘ f) s.
Proof. by compute; destruct (x s) as [|[??]]. Qed.

Lemma error_associative {S E A B C} (f : A → error S E B) (g : B → error S E C) x s :
  ((x ≫= f) ≫= g) s = (a ← x; f a ≫= g) s.
Proof. by compute; destruct (x s) as [|[??]]. Qed.
Lemma error_of_option_bind {S E A B} (f : A → option B) o e :
  error_of_option (S := S) (E:=E) (o ≫= f) e
  = a ← error_of_option o e; error_of_option (f a) e.
Proof. by destruct o. Qed.

Lemma error_gets_spec {S E A} (g : S → A) s : gets (E:=E) g s = mret (M := error S E) (g s) s.
Proof. done. Qed.
Lemma error_modify_spec {S E} (g : S → S) s : modify (E:=E) g s = mret (M := error S E) () (g s).
Proof. done. Qed.
Lemma error_left_gets {S E A B} (g : S → A) (f : A → error S E B) s :
  (gets (E:=E) g ≫= f) s = f (g s) s.
Proof. done. Qed.
Lemma error_left_modify {S E B} (g : S → S) (f : unit → error S E B) s :
  (modify (E:=E) g ≫= f) s = f () (g s).
Proof. done. Qed.
Lemma error_left_id {S E A B} (a : A) (f : A → error S E B) :
  (mret a ≫= f) = f a.
Proof. done. Qed.

Ltac generalize_errors :=
  csimpl;
  let gen_error e :=
    try (is_var e; fail 1); generalize e;
    let x := fresh "err" in intros x in
  repeat match goal with
  | |- context[ fail ?e ] => gen_error e
  | |- context[ error_guard _ ?e ] => gen_error e
  | |- context[ error_of_option _ ?e ] => gen_error e
  end.
Tactic Notation "simplify_error_equality" :=
  repeat match goal with
  | H : context [ gets _ _ _ ] |- _ => rewrite error_gets_spec in H
  | H : context [ modify _ _ _ ] |- _ => rewrite error_modify_spec in H
  | H : (mret (M:=error _ _) _ ≫= _) _ = _ |- _ => rewrite error_left_id in H
  | H : (gets _ ≫= _) _ = _ |- _ => rewrite error_left_gets in H
  | H : (modify _ ≫= _) _ = _ |- _ => rewrite error_left_modify in H
  | H : error_guard _ _ _ _ = _ |- _ => apply error_guard_ret in H; destruct H
  | _ => progress simplify_equality'
  | H : error_of_option _ _ _ = _ |- _ =>
    apply error_of_option_ret in H; destruct H
  | H : mbind (M:=error _ _) _ _ _ = _ |- _ =>
    apply error_bind_ret in H; destruct H as (?&?&?&?)
  | H : fmap (M:=error _ _) _ _ _ = _ |- _ =>
    apply error_fmap_ret in H; destruct H as (?&?&?)
  | H : mbind (M:=option) _ _ = _ |- _ =>
    apply bind_Some in H; destruct H as (?&?&?)
  | H : fmap (M:=option) _ _ = _ |- _ =>
    apply fmap_Some in H; destruct H as (?&?&?)
  | H : maybe _ ?x = Some _ |- _ => is_var x; destruct x
  | H : maybe2 _ ?x = Some _ |- _ => is_var x; destruct x
  | H : maybe3 _ ?x = Some _ |- _ => is_var x; destruct x
  | H : maybe4 _ ?x = Some _ |- _ => is_var x; destruct x
  | _ => progress case_decide
  end.

Tactic Notation "error_proceed" :=
  repeat match goal with
  | H : context [ gets _ _ ] |- _ => rewrite error_gets_spec in H
  | H : context [ modify _ _ ] |- _ => rewrite error_modify_spec in H
  | H : context [ error_of_option _ _ ] |- _ => rewrite error_of_option_bind in H
  | H : (mret (M:= _ _) _ ≫= _) _ = _ |- _ => rewrite error_left_id in H
  | H : (gets _ ≫= _) _ = _ |- _ => rewrite error_left_gets in H
  | H : (modify _ ≫= _) _ = _ |- _ => rewrite error_left_modify in H
  | H : ((_ <$> _) ≫= _) _ = _ |- _ => rewrite error_fmap_bind in H
  | H : ((_ ≫= _) ≫= _) _ = _ |- _ => rewrite error_associative in H
  | H : (error_guard _ _ _) _ = _ |- _ =>
     let H' := fresh in apply error_guard_ret in H; destruct H as [H' H]
  | _ => progress simplify_equality'
  | H : maybe _ ?x = Some _ |- _ => is_var x; destruct x
  | H : maybe2 _ ?x = Some _ |- _ => is_var x; destruct x
  | H : maybe3 _ ?x = Some _ |- _ => is_var x; destruct x
  | H : maybe4 _ ?x = Some _ |- _ => is_var x; destruct x
  end.
Tactic Notation "error_proceed"
    simple_intropattern(a) "as" simple_intropattern(s) :=
  error_proceed;
  lazymatch goal with
  | H : (error_of_option ?o _ ≫= _) _ = _ |- _ => destruct o as [a|] eqn:?
  | H : error_of_option ?o _ _ = _ |- _ => destruct o as [a|] eqn:?
  | H : (_ ≫= _) _ = _ |- _ => apply error_bind_ret in H; destruct H as (a&s&?&H)
  | H : (_ <$> _) _ = _ |- _ => apply error_fmap_ret in H; destruct H as (a&?&?)
  end;
  error_proceed.
