Require Export base decidable orders.

Lemma None_ne_Some `(a : A) : None ≠ Some a.
Proof. congruence. Qed.
Lemma Some_ne_None `(a : A) : Some a ≠ None.
Proof. congruence. Qed.
Lemma eq_None_ne_Some `(x : option A) a : x = None → x ≠ Some a.
Proof. congruence. Qed.
Instance Some_inj {A} : Injective (=) (=) (@Some A).
Proof. congruence. Qed.

Definition option_case {A B} (f : A → B) (b : B) (x : option A) :=
  match x with
  | None => b
  | Some a => f a
  end.

Definition maybe {A} (a : A) (x : option A) :=
  match x with
  | None => a
  | Some a => a
  end.

Lemma option_eq {A} (x y : option A) :
  x = y ↔ ∀ a, x = Some a ↔ y = Some a.
Proof.
  split.
  * intros. now subst.
  * intros E. destruct x, y.
    + now apply E.
    + symmetry. now apply E.
    + now apply E.
    + easy.
Qed.

Definition is_Some `(x : option A) := ∃ a, x = Some a.
Hint Extern 10 (is_Some _) => solve [eexists; eauto].

Ltac simplify_is_Some := repeat intro; repeat
  match goal with
  | _ => progress simplify_eqs
  | H : is_Some _ |- _ => destruct H as [??]
  | |- is_Some _ => eauto
  end.

Lemma Some_is_Some `(a : A) : is_Some (Some a).
Proof. simplify_is_Some. Qed.
Lemma None_not_is_Some {A} : ¬is_Some (@None A).
Proof. simplify_is_Some. Qed.

Definition is_Some_1 `(x : option A) : is_Some x → { a | x = Some a } :=
  match x with
  | None => False_rect _ ∘ ex_ind None_ne_Some
  | Some a => λ _, a↾eq_refl
  end.
Lemma is_Some_2 `(x : option A) a : x = Some a → is_Some x.
Proof. simplify_is_Some. Qed.

Lemma eq_None_not_Some `(x : option A) : x = None ↔ ¬is_Some x.
Proof. destruct x; simpl; firstorder congruence. Qed.

Lemma make_eq_Some {A} (x : option A) a : 
  is_Some x → (∀ b, x = Some b → b = a) → x = Some a.
Proof. intros [??] H. subst. f_equal. auto. Qed.

Instance option_eq_dec `{dec : ∀ x y : A, Decision (x = y)} (x y : option A) :
    Decision (x = y) :=
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

Inductive option_lift `(P : A → Prop) : option A → Prop :=
  | option_lift_some x : P x → option_lift P (Some x)
  | option_lift_None : option_lift P None.

Ltac option_lift_inv := repeat
  match goal with
  | H : option_lift _ (Some _) |- _ => inversion H; clear H; subst
  | H : option_lift _ None |- _ => inversion H
  end.

Lemma option_lift_inv_Some `(P : A → Prop) x : option_lift P (Some x) → P x.
Proof. intros. now option_lift_inv. Qed.

Definition option_lift_sig `(P : A → Prop) (x : option A) :
    option_lift P x → option (sig P) :=
  match x with
  | Some a => λ p, Some (exist _ a (option_lift_inv_Some P a p))
  | None => λ _, None
  end.

Definition option_lift_dsig `(P : A → Prop) `{∀ x : A, Decision (P x)} 
    (x : option A) : option_lift P x → option (dsig P) :=
  match x with
  | Some a => λ p, Some (dexist a (option_lift_inv_Some P a p))
  | None => λ _, None
  end.

Lemma option_lift_dsig_Some `(P : A → Prop) `{∀ x : A, Decision (P x)} x y px py :
  option_lift_dsig P x px = Some (y↾py) ↔ x = Some y.
Proof.
  split.
  * destruct x; simpl; intros; now simplify_eqs.
  * intros. subst. simpl. f_equal. now apply dsig_eq.
Qed.

Lemma option_lift_dsig_is_Some `(P : A → Prop) `{∀ x : A, Decision (P x)} x px :
  is_Some (option_lift_dsig P x px) ↔ is_Some x.
Proof.
  split.
  * intros [[??] ?]. eapply is_Some_2, option_lift_dsig_Some; eauto.
  * intros [??]. subst. eapply is_Some_2. reflexivity.
Qed.

Instance option_ret: MRet option := @Some.
Instance option_bind: MBind option := λ A B f x,
  match x with
  | Some a => f a
  | None => None
  end.
Instance option_join: MJoin option := λ A x,
  match x with
  | Some x => x
  | None => None
  end.
Instance option_fmap: FMap option := @option_map.

Ltac simplify_options := repeat
  match goal with
  | _ => progress simplify_eqs
  | H : mbind (M:=option) ?f ?o = ?x |- _ =>
    change (option_bind _ _ f o = x) in H;
    destruct o; simpl in H; try discriminate
  | H : context [ ?o = _ ] |- mbind (M:=option) ?f ?o = ?x =>
    change (option_bind _ _ f o = x);
    erewrite H by eauto;
    simpl
  end.

Lemma option_fmap_is_Some {A B} (f : A → B) (x : option A) :
  is_Some x ↔ is_Some (f <$> x).
Proof. destruct x; split; intros [??]; subst; compute; eauto; discriminate. Qed.
Lemma option_fmap_is_None {A B} (f : A → B) (x : option A) :
  x = None ↔ f <$> x = None.
Proof. unfold fmap, option_fmap. destruct x; simpl; split; congruence. Qed.

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
  Proof. now intros [?|]. Qed.
  Global Instance: RightId (=) None (union_with f).
  Proof. now intros [?|]. Qed.
  Global Instance: Commutative (=) f → Commutative (=) (union_with f).
  Proof. intros ? [?|] [?|]; compute; try reflexivity. now rewrite (commutative f). Qed.
  Global Instance: Associative (=) f → Associative (=) (union_with f).
  Proof. intros ? [?|] [?|] [?|]; compute; try reflexivity. now rewrite (associative f). Qed.
  Global Instance: Idempotent (=) f → Idempotent (=) (union_with f).
  Proof. intros ? [?|]; compute; try reflexivity. now rewrite (idempotent f). Qed.
End option_union_intersection.

Section option_difference.
  Context {A} (f : A → A → option A).

  Global Instance: RightId (=) None (difference_with f).
  Proof. now intros [?|]. Qed.
End option_difference.
