(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects general purpose definitions and theorems on the option
data type that are not in the Coq standard library. *)
Require Export base tactics decidable.

Inductive option_reflect {A} (P : A → Prop) (Q : Prop) : option A → Type :=
  | ReflectSome x : P x → option_reflect P Q (Some x)
  | ReflectNone : Q → option_reflect P Q None.

(** * General definitions and theorems *)
(** Basic properties about equality. *)
Lemma None_ne_Some {A} (a : A) : None ≠ Some a.
Proof. congruence. Qed.
Lemma Some_ne_None {A} (a : A) : Some a ≠ None.
Proof. congruence. Qed.
Lemma eq_None_ne_Some {A} (x : option A) a : x = None → x ≠ Some a.
Proof. congruence. Qed.
Instance Some_inj {A} : Injective (=) (=) (@Some A).
Proof. congruence. Qed.

(** The non dependent elimination principle on the option type. *)
Definition default {A B} (b : B) (x : option A) (f : A → B)  : B :=
  match x with None => b | Some a => f a end.
Hint Extern 1000 => simpl (default _ (Some _) _) || simpl (default _ None _).

(** The [from_option] function allows us to get the value out of the option
type by specifying a default value. *)
Definition from_option {A} (a : A) (x : option A) : A :=
  match x with None => a | Some b => b end.

(** An alternative, but equivalent, definition of equality on the option
data type. This theorem is useful to prove that two options are the same. *)
Lemma option_eq {A} (x y : option A) : x = y ↔ ∀ a, x = Some a ↔ y = Some a.
Proof. split; [by intros; by subst |]. destruct x, y; naive_solver. Qed.

Definition is_Some {A} (x : option A) := ∃ y, x = Some y.
Lemma mk_is_Some {A} (x : option A) y : x = Some y → is_Some x.
Proof. intros; red; subst; eauto. Qed.
Hint Resolve mk_is_Some.
Lemma is_Some_None {A} : ¬is_Some (@None A).
Proof. by destruct 1. Qed.
Hint Resolve is_Some_None.

Instance is_Some_pi {A} (x : option A) : ProofIrrel (is_Some x).
Proof.
  set (P (y : option A) := match y with Some _ => True | _ => False end).
  set (f x := match x return P x → is_Some x with
    Some _ => λ _, ex_intro _ _ eq_refl | None => False_rect _ end).
  set (g x (H : is_Some x) :=
    match H return P x with ex_intro _ p => eq_rect _ _ I _ (eq_sym p) end).
  assert (∀ x H, f x (g x H) = H) as f_g by (by intros ? [??]; subst).
  intros p1 p2. rewrite <-(f_g _ p1), <-(f_g _ p2). by destruct x, p1.
Qed.
Instance is_Some_dec {A} (x : option A) : Decision (is_Some x) :=
  match x with
  | Some x => left (ex_intro _ x eq_refl)
  | None => right is_Some_None
  end.

Definition is_Some_proj {A} {x : option A} : is_Some x → A :=
  match x with Some a => λ _, a | None => False_rect _ ∘ is_Some_None end.
Definition Some_dec {A} (x : option A) : { a | x = Some a } + { x = None } :=
  match x return { a | x = Some a } + { x = None } with
  | Some a => inleft (a ↾ eq_refl _)
  | None => inright eq_refl
  end.
Instance None_dec {A} (x : option A) : Decision (x = None) :=
  match x with Some x => right (Some_ne_None x) | None => left eq_refl end.

Lemma eq_None_not_Some {A} (x : option A) : x = None ↔ ¬is_Some x.
Proof. destruct x; unfold is_Some; naive_solver. Qed.
Lemma not_eq_None_Some `(x : option A) : x ≠ None ↔ is_Some x.
Proof. rewrite eq_None_not_Some. split. apply dec_stable. tauto. Qed.

(** Equality on [option] is decidable. *)
Instance option_eq_None_dec {A} (x : option A) : Decision (x = None) :=
  match x with Some _ => right (Some_ne_None _) | None => left eq_refl end.
Instance option_None_eq_dec {A} (x : option A) : Decision (None = x) :=
  match x with Some _ => right (None_ne_Some _) | None => left eq_refl end.
Instance option_eq_dec `{dec : ∀ x y : A, Decision (x = y)}
  (x y : option A) : Decision (x = y).
Proof.
 refine
  match x, y with
  | Some a, Some b => cast_if (decide (a = b))
  | None, None => left _ | _, _ => right _
  end; abstract congruence.
Defined.

(** * Monadic operations *)
Instance option_ret: MRet option := @Some.
Instance option_bind: MBind option := λ A B f x,
  match x with Some a => f a | None => None end.
Instance option_join: MJoin option := λ A x,
  match x with Some x => x | None => None end.
Instance option_fmap: FMap option := @option_map.
Instance option_guard: MGuard option := λ P dec A x,
  match dec with left H => x H | _ => None end.

Lemma fmap_is_Some {A B} (f : A → B) x : is_Some (f <$> x) ↔ is_Some x.
Proof. unfold is_Some; destruct x; naive_solver. Qed.
Lemma fmap_Some {A B} (f : A → B) x y :
  f <$> x = Some y ↔ ∃ x', x = Some x' ∧ y = f x'.
Proof. destruct x; naive_solver. Qed.
Lemma fmap_None {A B} (f : A → B) x : f <$> x = None ↔ x = None.
Proof. by destruct x. Qed.
Lemma option_fmap_id {A} (x : option A) : id <$> x = x.
Proof. by destruct x. Qed.
Lemma option_fmap_compose {A B} (f : A → B) {C} (g : B → C) x :
  g ∘ f <$> x = g <$> f <$> x.
Proof. by destruct x. Qed.
Lemma option_fmap_bind {A B C} (f : A → B) (g : B → option C) x :
  (f <$> x) ≫= g = x ≫= g ∘ f.
Proof. by destruct x. Qed.
Lemma option_bind_assoc {A B C} (f : A → option B)
  (g : B → option C) (x : option A) : (x ≫= f) ≫= g = x ≫= (mbind g ∘ f).
Proof. by destruct x; simpl. Qed.
Lemma option_bind_ext {A B} (f g : A → option B) x y :
  (∀ a, f a = g a) → x = y → x ≫= f = y ≫= g.
Proof. intros. destruct x, y; simplify_equality; simpl; auto. Qed.
Lemma option_bind_ext_fun {A B} (f g : A → option B) x :
  (∀ a, f a = g a) → x ≫= f = x ≫= g.
Proof. intros. by apply option_bind_ext. Qed.
Lemma bind_Some {A B} (f : A → option B) (x : option A) b :
  x ≫= f = Some b ↔ ∃ a, x = Some a ∧ f a = Some b.
Proof. split. by destruct x as [a|]; [exists a|]. by intros (?&->&?). Qed.
Lemma bind_None {A B} (f : A → option B) (x : option A) :
  x ≫= f = None ↔ x = None ∨ ∃ a, x = Some a ∧ f a = None.
Proof.
  split; [|by intros [->|(?&->&?)]].
  destruct x; intros; simplify_equality'; eauto.
Qed.
Lemma bind_with_Some {A} (x : option A) : x ≫= Some = x.
Proof. by destruct x. Qed.

Tactic Notation "case_option_guard" "as" ident(Hx) :=
  match goal with
  | H : context C [@mguard option _ ?P ?dec _ ?x] |- _ =>
    let X := context C [ match dec with left H => x H | _ => None end ] in
    change X in H; destruct_decide dec as Hx
  | |- context C [@mguard option _ ?P ?dec _ ?x] =>
    let X := context C [ match dec with left H => x H | _ => None end ] in
    change X; destruct_decide dec as Hx
  end.
Tactic Notation "case_option_guard" :=
  let H := fresh in case_option_guard as H.

Lemma option_guard_True {A} P `{Decision P} (x : option A) :
  P → guard P; x = x.
Proof. intros. by case_option_guard. Qed.
Lemma option_guard_False {A} P `{Decision P} (x : option A) :
  ¬P → guard P; x = None.
Proof. intros. by case_option_guard. Qed.
Lemma option_guard_iff {A} P Q `{Decision P, Decision Q} (x : option A) :
  (P ↔ Q) → guard P; x = guard Q; x.
Proof. intros [??]. repeat case_option_guard; intuition. Qed.

Tactic Notation "simpl_option_monad" "by" tactic3(tac) :=
  let assert_Some_None A o H := first
    [ let x := fresh in evar (x:A); let x' := eval unfold x in x in clear x;
      assert (o = Some x') as H by tac
    | assert (o = None) as H by tac ]
  in repeat match goal with
  | H : context [mbind (M:=option) (A:=?A) ?f ?o] |- _ =>
    let Hx := fresh in assert_Some_None A o Hx; rewrite Hx in H; clear Hx
  | H : context [fmap (M:=option) (A:=?A) ?f ?o] |- _ =>
    let Hx := fresh in assert_Some_None A o Hx; rewrite Hx in H; clear Hx
  | H : context [default (A:=?A) _ ?o _] |- _ =>
    let Hx := fresh in assert_Some_None A o Hx; rewrite Hx in H; clear Hx
  | H : context [ match ?o with _ => _ end ] |- _ =>
    match type of o with
    | option ?A =>
      let Hx := fresh in assert_Some_None A o Hx; rewrite Hx in H; clear Hx
    end
  | |- context [mbind (M:=option) (A:=?A) ?f ?o] =>
    let Hx := fresh in assert_Some_None A o Hx; rewrite Hx; clear Hx
  | |- context [fmap (M:=option) (A:=?A) ?f ?o] =>
    let Hx := fresh in assert_Some_None A o Hx; rewrite Hx; clear Hx
  | |- context [default (A:=?A) _ ?o _] =>
    let Hx := fresh in assert_Some_None A o Hx; rewrite Hx; clear Hx
  | |- context [from_option (A:=?A) _ ?o] =>
    let Hx := fresh in assert_Some_None A o Hx; rewrite Hx; clear Hx
  | |- context [ match ?o with _ => _ end ] =>
    match type of o with
    | option ?A =>
      let Hx := fresh in assert_Some_None A o Hx; rewrite Hx; clear Hx
    end
  | _ => rewrite decide_True by tac
  | _ => rewrite decide_False by tac
  | _ => rewrite option_guard_True by tac
  | _ => rewrite option_guard_False by tac
  end.
Tactic Notation "simplify_option_equality" "by" tactic3(tac) :=
  let assert_Some_None A o H := first
    [ let x := fresh in evar (x:A); let x' := eval unfold x in x in clear x;
      assert (o = Some x') as H by tac
    | assert (o = None) as H by tac ]
  in repeat match goal with
  | _ => progress simplify_equality'
  | _ => progress simpl_option_monad by tac
  | H : mbind (M:=option) _ ?o = ?x |- _ =>
    match o with Some _ => fail 1 | None => fail 1 | _ => idtac end;
    match x with Some _ => idtac | None => idtac | _ => fail 1 end;
    destruct o eqn:?
  | H : ?x = mbind (M:=option) _ ?o |- _ =>
    match o with Some _ => fail 1 | None => fail 1 | _ => idtac end;
    match x with Some _ => idtac | None => idtac | _ => fail 1 end;
    destruct o eqn:?
  | H : fmap (M:=option) _ ?o = ?x |- _ =>
    match o with Some _ => fail 1 | None => fail 1 | _ => idtac end;
    match x with Some _ => idtac | None => idtac | _ => fail 1 end;
    destruct o eqn:?
  | H : ?x = fmap (M:=option) _ ?o |- _ =>
    match o with Some _ => fail 1 | None => fail 1 | _ => idtac end;
    match x with Some _ => idtac | None => idtac | _ => fail 1 end;
    destruct o eqn:?
  | _ => progress case_decide
  | _ => progress case_option_guard
  end.
Tactic Notation "simplify_option_equality" := simplify_option_equality by eauto.

(** * Union, intersection and difference *)
Instance option_union_with {A} : UnionWith A (option A) := λ f x y,
  match x, y with
  | Some a, Some b => f a b
  | Some a, None => Some a
  | None, Some b => Some b
  | None, None => None
  end.
Instance option_intersection_with {A} : IntersectionWith A (option A) :=
  λ f x y, match x, y with Some a, Some b => f a b | _, _ => None end.
Instance option_difference_with {A} : DifferenceWith A (option A) := λ f x y,
  match x, y with
  | Some a, Some b => f a b
  | Some a, None => Some a
  | None, _ => None
  end.

Section option_union_intersection_difference.
  Context {A} (f : A → A → option A).
  Global Instance: LeftId (=) None (union_with f).
  Proof. by intros [?|]. Qed.
  Global Instance: RightId (=) None (union_with f).
  Proof. by intros [?|]. Qed.
  Global Instance: Commutative (=) f → Commutative (=) (union_with f).
  Proof. by intros ? [?|] [?|]; compute; rewrite 1?(commutative f). Qed.
  Global Instance: LeftAbsorb (=) None (intersection_with f).
  Proof. by intros [?|]. Qed.
  Global Instance: RightAbsorb (=) None (intersection_with f).
  Proof. by intros [?|]. Qed.
  Global Instance: Commutative (=) f → Commutative (=) (intersection_with f).
  Proof. by intros ? [?|] [?|]; compute; rewrite 1?(commutative f). Qed.
  Global Instance: RightId (=) None (difference_with f).
  Proof. by intros [?|]. Qed.
End option_union_intersection_difference.
