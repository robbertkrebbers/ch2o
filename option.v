(* Copyright (c) 2012, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects general purpose definitions and theorems on the option
data type that are not in the Coq standard library. *)
Require Export base tactics decidable.

(** * General definitions and theorems *)
(** Basic properties about equality. *)
Lemma None_ne_Some `(a : A) : None ≠ Some a.
Proof. congruence. Qed.
Lemma Some_ne_None `(a : A) : Some a ≠ None.
Proof. congruence. Qed.
Lemma eq_None_ne_Some `(x : option A) a : x = None → x ≠ Some a.
Proof. congruence. Qed.
Instance Some_inj {A} : Injective (=) (=) (@Some A).
Proof. congruence. Qed.

(** The non dependent elimination principle on the option type. *)
Definition option_case {A B} (f : A → B) (b : B) (x : option A) : B :=
  match x with
  | None => b
  | Some a => f a
  end.

(** The [maybe] function allows us to get the value out of the option type
by specifying a default value. *)
Definition maybe {A} (a : A) (x : option A) : A :=
  match x with
  | None => a
  | Some b => b
  end.

(** An alternative, but equivalent, definition of equality on the option
data type. This theorem is useful to prove that two options are the same. *)
Lemma option_eq {A} (x y : option A) :
  x = y ↔ ∀ a, x = Some a ↔ y = Some a.
Proof.
  split.
  { intros. by subst. }
  intros E. destruct x, y.
  + by apply E.
  + symmetry. by apply E.
  + by apply E.
  + done.
Qed.

(** We define [is_Some] as a [sig] instead of a [sigT] as extraction of
witnesses can be derived (see [is_Some_sigT] below). *)
Definition is_Some `(x : option A) : Prop := ∃ a, x = Some a.
Hint Extern 10 (is_Some _) => solve [eexists; eauto].

Ltac simplify_is_Some := repeat intro; repeat
  match goal with
  | _ => progress simplify_equality
  | H : is_Some _ |- _ => destruct H as [??]
  | |- is_Some _ => eauto
  end.

Lemma Some_is_Some `(a : A) : is_Some (Some a).
Proof. simplify_is_Some. Qed.
Lemma None_not_is_Some {A} : ¬is_Some (@None A).
Proof. simplify_is_Some. Qed.

Definition is_Some_sigT `(x : option A) : is_Some x → { a | x = Some a } :=
  match x with
  | None => False_rect _ ∘ ex_ind None_ne_Some
  | Some a => λ _, a↾eq_refl
  end.
Lemma eq_Some_is_Some `(x : option A) a : x = Some a → is_Some x.
Proof. simplify_is_Some. Qed.

Lemma eq_None_not_Some `(x : option A) : x = None ↔ ¬is_Some x.
Proof. destruct x; simpl; firstorder congruence. Qed.

Lemma make_eq_Some {A} (x : option A) a :
  is_Some x → (∀ b, x = Some b → b = a) → x = Some a.
Proof. intros [??] H. subst. f_equal. auto. Qed.

(** Equality on [option] is decidable. *)
Instance option_eq_dec `{dec : ∀ x y : A, Decision (x = y)}
    (x y : option A) : Decision (x = y) :=
  match x with
  | Some a =>
    match y with
    | Some b =>
      match dec a b with
      | left H => left (f_equal _ H)
      | right H => right (H ∘ injective Some _ _)
      end
    | None => right (Some_ne_None _)
    end
  | None =>
    match y with
    | Some _ => right (None_ne_Some _)
    | None => left eq_refl
    end
  end.

(** * Monadic operations *)
Instance option_bind {A B} (f : A → option B) : MBind option f := λ x,
  match x with
  | Some a => f a
  | None => None
  end.
Instance option_join {A} : MJoin option := λ x : option (option A),
  match x with
  | Some x => x
  | None => None
  end.
Instance option_fmap {A B} (f : A → B) : FMap option f := option_map f.

Lemma option_fmap_is_Some {A B} (f : A → B) (x : option A) :
  is_Some x ↔ is_Some (f <$> x).
Proof. destruct x; split; intros [??]; subst; compute; by eauto. Qed.
Lemma option_fmap_is_None {A B} (f : A → B) (x : option A) :
  x = None ↔ f <$> x = None.
Proof. unfold fmap, option_fmap. destruct x; simpl; split; congruence. Qed.

Tactic Notation "simplify_option_bind" "by" tactic3(tac) := repeat
  match goal with
  | _ => first [progress simpl in * | progress simplify_equality]
  | H : mbind (M:=option) (A:=?A) ?f ?o = ?x |- _ =>
    let x := fresh in evar (x:A);
    let x' := eval unfold x in x in clear x;
    let Hx := fresh in
    assert (o = Some x') as Hx by tac;
    rewrite Hx in H; clear Hx
  | H : mbind (M:=option) ?f ?o = ?x |- _ =>
    match o with Some _ => fail 1 | None => fail 1 | _ => idtac end;
    match x with Some _ => idtac | None => idtac | _ => fail 1 end;
    destruct o eqn:?
  | |- mbind (M:=option) (A:=?A) ?f ?o = ?x =>
    let x := fresh in evar (x:A);
    let x' := eval unfold x in x in clear x;
    let Hx := fresh in
    assert (o = Some x') as Hx by tac;
    rewrite Hx; clear Hx
  end.
Tactic Notation "simplify_option_bind" := simplify_option_bind by eauto.

(** * Union, intersection and difference *)
Instance option_union: UnionWith option := λ A f x y,
  match x, y with
  | Some a, Some b => Some (f a b)
  | Some a, None => Some a
  | None, Some b => Some b
  | None, None => None
  end.
Instance option_intersection: IntersectionWith option := λ A f x y,
  match x, y with
  | Some a, Some b => Some (f a b)
  | _, _ => None
  end.
Instance option_difference: DifferenceWith option := λ A f x y,
  match x, y with
  | Some a, Some b => f a b
  | Some a, None => Some a
  | None, _ => None
  end.

Section option_union_intersection.
  Context {A} (f : A → A → A).

  Global Instance: LeftId (=) None (union_with f).
  Proof. by intros [?|]. Qed.
  Global Instance: RightId (=) None (union_with f).
  Proof. by intros [?|]. Qed.
  Global Instance: Commutative (=) f → Commutative (=) (union_with f).
  Proof.
    intros ? [?|] [?|]; compute; try reflexivity.
    by rewrite (commutative f).
  Qed.
  Global Instance: Associative (=) f → Associative (=) (union_with f).
  Proof.
    intros ? [?|] [?|] [?|]; compute; try reflexivity.
    by rewrite (associative f).
  Qed.
  Global Instance: Idempotent (=) f → Idempotent (=) (union_with f).
  Proof.
    intros ? [?|]; compute; try reflexivity.
    by rewrite (idempotent f).
  Qed.

  Global Instance: Commutative (=) f → Commutative (=) (intersection_with f).
  Proof.
    intros ? [?|] [?|]; compute; try reflexivity.
    by rewrite (commutative f).
  Qed.
  Global Instance: Associative (=) f → Associative (=) (intersection_with f).
  Proof.
    intros ? [?|] [?|] [?|]; compute; try reflexivity.
    by rewrite (associative f).
  Qed.
  Global Instance: Idempotent (=) f → Idempotent (=) (intersection_with f).
  Proof.
    intros ? [?|]; compute; try reflexivity.
    by rewrite (idempotent f).
  Qed.
End option_union_intersection.

Section option_difference.
  Context {A} (f : A → A → option A).

  Global Instance: RightId (=) None (difference_with f).
  Proof. by intros [?|]. Qed.
End option_difference.
