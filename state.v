Require Export statements trs.

Inductive direction :=
  | In : direction
  | Out : direction
  | Top : option N → direction
  | Jump : label → direction.

Instance direction_eq_dec (d1 d2 : direction) : Decision (d1 = d2).
Proof. solve_decision. Defined.

Definition down (d : direction) (s : stmt) : Prop :=
  match d with
  | In => True
  | Jump l => l ∈ labels s
  | _ => False
  end.
Definition up (d : direction) (s : stmt) : Prop :=
  match d with
  | Out => True
  | Top _ => True
  | Jump l => l ∉ labels s
  | _ => False
  end.

Hint Extern 0 (down _ _) => constructor.
Hint Extern 0 (up _ _) => constructor.

Lemma not_down_up d s : ¬down d s → up d s.
Proof. destruct d; intuition. Qed.

Definition down_up_dec d s : {down d s} + {up d s} :=
  match d with
  | In => left I
  | Out => right I
  | Jump l => decide_rel (∈) l (labels s)
  | Top _ => right I
  end.

Inductive location :=
  | Stmt : direction → stmt → location
  | Call : N → list N → location
  | Return : option N → location.

Instance location_eq_dec (loc1 loc2 : location) : Decision (loc1 = loc2).
Proof. solve_decision. Defined.

Inductive state := State {
  SCtx : ctx;
  SLoc : location;
  SMem : mem
}.
Add Printing Constructor state.

Instance state_eq_dec (S1 S2 : state) : Decision (S1 = S2).
Proof. solve_decision. Defined.

Inductive simple_location :=
  | Stmt_ : stmt → simple_location
  | Call_ : N → simple_location
  | Return_ : simple_location.

Coercion to_simple_location (loc : location) :=
  match loc with
  | Stmt _ s => Stmt_ s
  | Call f _ => Call_ f
  | Return _ => Return_
  end.

Definition simple_location_related (loc1 loc2 : simple_location) : Prop :=
  match loc1, loc2 with
  | Stmt_ s1, Stmt_ s2 => s1 = s2
  | Call_ f1, Call_ f2 => f1 = f2
  | _, _ => True
  end.
Local Infix "≍" := simple_location_related (at level 80).

Arguments simple_location_related !_ !_.

Instance: Reflexive simple_location_related.
Proof. now intros []. Qed.
Instance: Injective (=) (=) Stmt_.
Proof. now injection 1. Qed.

Section ctx_wf.
Context (δ : fenv).

Inductive ctx_wf (k : ctx) (loc : simple_location) :
      ctx → simple_location → Prop :=
  | ctx_wf_start :
     ctx_wf k loc k loc
  | ctx_wf_item k' E s :
     ctx_wf k loc k' (Stmt_ (subst E s)) →
     ctx_wf k loc (CItem E :: k') (Stmt_ s)
  | ctx_wf_block k' b s :
     ctx_wf k loc k' (Stmt_ (block s)) →
     ctx_wf k loc (CBlock b :: k') (Stmt_ s)
  | ctx_wf_call k' e f es :
     ctx_wf k loc k' (Stmt_ (call e f es)) →
     ctx_wf k loc (CCall e f es :: k') (Call_ f)
  | ctx_wf_return k' f :
     ctx_wf k loc k' (Call_ f) →
     ctx_wf k loc k' Return_
  | ctx_wf_params k' f bs s :
     δ !! f = Some s →
     ctx_wf k loc k' (Call_ f) →
     ctx_wf k loc (CParams bs :: k') (Stmt_ s).

Lemma ctx_wf_suffix_of k loc k' loc' :
  ctx_wf k loc k' loc' → suffix_of k k'.
Proof. induction 1; simpl in *; auto with list. Qed.

Lemma ctx_wf_related k loc k' loc1 loc2 :
  ctx_wf k loc k' loc1 → ctx_wf k loc k' loc2 → loc1 ≍ loc2.
Proof.
  intros wf1. revert loc2.
  induction wf1; inversion 1; subst; simpl in *; trivial; try
    match goal with
    | H : ctx_wf _ _ _ _ |- _ =>
      apply ctx_wf_suffix_of in H; discriminate_suffix_of
    end.
  * easy.
  * destruct loc; simpl in *; auto.
  * eapply (injective (subst _)), (IHwf1 (Stmt_ _)); eassumption.
  * eapply (injective SBlock), (IHwf1 (Stmt_ _)); eassumption.
  * destruct loc2; simpl in *; auto.
  * efeed specialize IHwf1; eauto; simpl in *; congruence.
Qed.

Lemma ctx_wf_unique k loc k' s1 s2 :
  ctx_wf k loc k' (Stmt_ s1) → ctx_wf k loc k' (Stmt_ s2) → s1 = s2.
Proof. apply ctx_wf_related. Qed.
End ctx_wf.
