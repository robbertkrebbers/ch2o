(* Copyright (c) 2012, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file defines an axiomatic semantics using separation logic. Judgments
of our axiomatic semantics are sextuples of the shape
[Δ ; J ; R ⊢ {{ P }} s {{ Q }}] where:
- [s] is a statement, and [P] and [Q] are assertions called the pre and
  postcondition of [s], respectively.
- [Δ] is a finite map from function names to their pre and postconditions.
- [J] is a map that gives the jumping condition for each [goto]. To be able to
  execute a [goto l], the assertion [J l] should hold.
- [R] is a map that gives the current function's post condition. To be able to
  execute a [return mv], the assertion [R mv] should hold.

The axiomatic semantics is defined as a semantic definition with respect to
our operational semantics. We prove that the rules of separation logic and
novel rules for our specific features can be derived. *)
Require Export assertions smallstep.
Local Open Scope nat_scope.

Section axiomatic.
Context (δ : funenv).

(** * The Hoare judgment *)
(** The standard semantic definition of a Hoare triple [{{ P }} s {{ Q }}]
is: if [P] holds for the state before execution of [s], and execution of [s]
terminates, then [Q] will hold afterwards. For our language we have to deal
with non local control flow, mutual recursive function calls, undefined
behavior, and the framing rule, making such a definition more complicated. *)

(** Since the conditions [P], [Q], [J] and [R] of the Hoare judgment
[Δ ; J ; R ⊢ {{ P }} s {{ Q }}] correspond to the four directions [↘], [↗],
[↷] and [⇈] in which execution of statements can be performed, we
reformulate the sextuple as a triple [ax_stmt Δ s Pd] where [Pd] is a function
from directions to assertions such that [Pd ↘ = P], [Pd ↗ = Q], [Pd (↷ l) = J l]
and [Pd (⇈ mv) = R mv]. *)

(** Intuitively, the triple [ax_stmt Δ s Pd] should imply something along the
lines of: if [Pd d (get_stack k) m] and [State k (Stmt s d) m ⇒s* State k
(Stmt s d') m'], then [Pd d' (get_stack k) m']. However, a reduction path
[State k (Stmt s d) m ⇒s* State k (Stmt s d') m'] may very well pop items of
the program context [k] and restore them later on. Since [Pd] only gives
guarantees about [get_stack k], this property is too strong. Therefore, we
restrict to reduction paths [State k (Stmt s d) m ⇒s{k}* State k (Stmt s d') m']
that remain below the context [k]. *)

(** Apart from safety, we also want the Hoare judgment to guarantee that the
program cannot go wrong. Therefore, we further specialize the above property
to: if [Pd d (get_stack k) m] and [State k (Stmt s d) m ⇒s{k}* S], then [S] is
either reducible (i.e. not stuck) or it is of the shape [State k (Stmt s d') m']
with [Pd d' (get_stack k) m'] (i.e., execution is finished). *)

(** In order to derive the frame rule of separation logic, we require the
program to satisfy thread safety. That means, if before execution of [s] the
memory can be divided into two disjoint parts [m] and [mf] such before
precondition holds for [m], then execution of [s] will not modify the memory
[mf] at point during its execution. *)

(** To prove that the rules for function calls and various other constructs
are derivable we have to perform inductions on the reduction paths. Since our
paths are not informative (i.e. in [Prop]) we use paths of bounded length so we
can perform induction on that bound.  *)

(** ** General definitions *)
(** In order to make our definitions reusable for function calls, we generalize
direction indexed assertions to a predicate [stack → mem → location → Prop]. *)
Section general.
Context (Ploc : stack → mem → location → Prop).

(** The predicate [ax n loc k m mf S'] states that for each reduction
[State k loc (m ∪ mf) ⇒s{k}^n S'] the state [S'] is either reducible or
satisfies [Ploc]. We use an inductive predicate instead of logical quantifiers
so as to obtain more convenient case analyses. *)
Inductive ax_valid (k : ctx) (mf : mem) : state → Prop :=
  | ax_further m' loc' k' :
     m' ⊥ mf →
     red (δ⇒s{k}) (State k' loc' (m' ∪ mf)) →
     ax_valid k mf (State k' loc' (m' ∪ mf))
  | ax_done m' loc' :
     Ploc (get_stack k) m' loc' →
     m' ⊥ mf →
     ax_valid k mf (State k loc' (m' ∪ mf)).

Definition ax (n : nat) (loc : location)
    (k : ctx) (m mf : mem) (S' : state) : Prop :=
  m ⊥ mf →
  δ ⊢ State k loc (m ∪ mf) ⇒s{k}^n S' →
  ax_valid k mf S'.

Lemma ax_weaken n1 n2 loc k m mf S :
  n1 ≤ n2 → ax n2 loc k m mf S → ax n1 loc k m mf S.
Proof. unfold ax. eauto using bsteps_weaken. Qed.

(** The main tool to prove the structural Hoare rules for constructs like
blocks, the conditional and the while loop, is to cut reduction paths in two.
In these proofs we have reductions [State (l ++ k) loc (m ∪ mf) ⇒s{k}^n S'']
that should be split into the maximal prefix that is below [l ++ k] and the
remainder. *)
Inductive ax_splitting (n : nat) (loc : location)
      (l k : ctx) (m mf : mem) : state → Prop :=
  | ax_splitting_further k'' loc'' m'' :
     m'' ⊥ mf →
     red (δ⇒s{l ++ k}) (State k'' loc'' (m'' ∪ mf)) →
     ax_splitting n loc l k m mf (State k'' loc'' (m'' ∪ mf))
  | ax_splitting_done m' loc' S'' :
     Ploc (get_stack (l ++ k)) m' loc' →
     m' ⊥ mf →
     δ ⊢ State (l ++ k) loc (m ∪ mf) ⇒s{l ++ k}^n
         State (l ++ k) loc' (m' ∪ mf) →
     δ ⊢ State (l ++ k) loc' (m' ∪ mf) ⇒s{k}^n S'' →
     ax_splitting n loc l k m mf S''.

Lemma ax_split n loc l k m mf S'' :
  (∀ S, ax n loc (l ++ k) m mf S) →
  m ⊥ mf →
  δ ⊢ State (l ++ k) loc (m ∪ mf) ⇒s{k}^n S'' →
  ax_splitting n loc l k m mf S''.
Proof.
  intros Hax ? p1.
  destruct (cstep_subctx_cut δ n l k _ _ p1) as [p | [S' [p2 [p3 ?]]]].
  * solve_suffix_of.
  * feed destruct (Hax S'') as [m'' | m'' loc'' P]; auto.
    + now left.
    + now right with m'' loc''; intuition.
  * feed destruct (Hax S') as [m' | m' loc' P]; auto.
    + contradiction.
    + now right with m' loc'.
Qed.
End general.

(** ** Function calls *)
(** We define assertions of functions as a dependently typed record [fassert]
consisting of the function's pre and postcondition. The pre and postcondition
should be stack independent because local variables may have a different
meaning at the caller than within the called function's body. Furthermore, to
relate the postcondition to the precondition, we extend this record with a
field [fcommon] that is used in both. This approach is similar to (Appel/Blazy,
2007), but we also allow the postcondition to refer to the function's
arguments. *)
Record fassert := FAssert {
  fcommon : Type;
  fpre : fcommon → list value → assert;
  fpost : fcommon → list value → option value → assert;
  fpre_stack_indep c vs : StackIndep (fpre c vs);
  fpost_stack_indep c vs mv : StackIndep (fpost c vs mv)
}.
Add Printing Constructor fassert.
Existing Instance fpre_stack_indep.
Existing Instance fpost_stack_indep.
Notation fassert_env := (funmap fassert).

(** The predicate [ax_funs n Δ] states that function calls to functions in
[Δ] behave accordingly. Less informally, for a given reduction
[State k (Call f vs) (m ∪ mf) ⇒s{k}^n S] whose starting state satisfies the
function's precondiction, we have that [S] is either reducible, or is of the
shape [State k (Return mv) (m' ∪ mf)] satisfying the function's
postcondition. *)
Inductive ax_fun_loc (Pf : fassert) (c : fcommon Pf) (vs : list value)
    (ρ : stack) (m : mem) : location → Prop :=
  | make_lassert_fun v :
     fpost Pf c vs v ρ m →
     ax_fun_loc Pf c vs ρ m (Return v).
Definition ax_funs (n : nat) (Δ : fassert_env) : Prop :=
  ∀ f Pf c vs m mf k S',
    Δ !! f = Some Pf →
    fpre Pf c vs (get_stack k) m →
    ax (ax_fun_loc Pf c vs) n (Call f vs) k m mf S'.

Lemma ax_funs_weaken n1 n2 Δ :
  n1 ≤ n2 → ax_funs n2 Δ → ax_funs n1 Δ.
Proof. unfold ax_funs. eauto using ax_weaken. Qed.

Lemma ax_funs_empty n : ax_funs n ∅.
Proof. repeat intro. simplify_map. Qed.
Lemma ax_funs_S n Δ : ax_funs (S n) Δ → ax_funs n Δ.
Proof. apply ax_funs_weaken. auto with arith. Qed.
Hint Resolve ax_funs_empty ax_funs_S : ax.

(** ** Directed assertions *)
(** We generalize the notion of direction indexed assertions to arbitrary
types. This generalization allows us to define some operations in a more
generic way. *)
Definition directed A := direction → A.
Definition directed_pack {A} (P : A) (Q : A) (R : option value → A)
  (J : label → A) : directed A := direction_rect (λ _, A) P Q R J.
Lemma directed_pack_proper `{!@Equivalence A R} : Proper
  (R ==> R ==> pointwise_relation _ R ==> pointwise_relation _ R
     ==> (=) ==> R) (@directed_pack A).
Proof. intros ????????????? [] ?; subst; firstorder. Qed.

(** This hideous of definition of [fmap] makes [f <$> directed_pack P Q R J]
convertible with [directed_pack (f P) (f Q) (f ∘ R) (f ∘ J)]. This is used to
derive the rules [ax_stmt_frame] and [ax_block] from a more general one. *)
Instance directed_fmap : FMap directed := λ _ _ f Pd d,
  match d with
  | ↘ => f (Pd ↘)
  | ↗ => f (Pd ↗)
  | ⇈ mv => f (Pd (⇈ mv))
  | ↷ l => f (Pd (↷ l))
  end.
Lemma directed_fmap_spec {A B} (f : A → B) (P : directed A) d :
  (f <$> P) d = f (P d).
Proof. now destruct d. Qed.

Notation dassert := (directed assert).
Notation dassert_pack P Q R J := (@directed_pack assert P%A Q%A R%A J%A).
Definition dassert_pack_top (P : assert) (R : option value → assert) :
  dassert := dassert_pack P (R None) R (λ _, False%A).

(** ** The Hoare judgment for statements *)
(** Now the definition of the Hoare judgment for statements is just packing all
of the above definitions together. *)
Inductive ax_stmt_loc (Pd : dassert)
    (ρ : stack) (m : mem) : location → Prop :=
  | make_lassert_stmt d s :
     up d s →
     Pd d ρ m →
     ax_stmt_loc Pd ρ m (Stmt d s).
Definition ax_stmt (Δ : fassert_env) s (Pd : dassert) : Prop :=
  ∀ n k d m mf S',
    ax_funs n Δ →
    down d s →
    Pd d (get_stack k) m →
    ax (ax_stmt_loc Pd) n (Stmt d s) k m mf S'.

Notation "Δ ; J ; R ⊢ {{ P }} s {{ Q }}" :=
  (ax_stmt Δ s%S (dassert_pack P%A Q%A R%A J%A))
  (J at level 10, R at level 10, at level 80, Q at next level,
   format "Δ ;  J ;  R  ⊢  '[' {{  P  }} '/'  s  '/' {{  Q  }} ']'").
Notation "Δ ⊢ {{ P }} s {{ R }}" :=
  (ax_stmt Δ s%S (dassert_pack_top P%A R%A))
  (J at level 10, at level 80, Q at next level,
   format "Δ  ⊢  '[' {{  P  }} '/'  s  '/' {{  R  }} ']'").

(** * Soundness of the axiomatic semantics *)
(** We prove some consequences the Hoare judgment that do not involve the
auxiliary notions we defined above. This shows that the Hoare judgment is
sound with respect to the intended meaning. *)
Lemma ax_stmt_sound_sep P R s m mf S' :
  ∅ ⊢ {{ P }} s {{ R }} →
  m ⊥ mf →
  P [] m →
  δ ⊢ State [] (Stmt ↘ s) (m ∪ mf) ⇒s* S' →
    (∃ m', S' = State [] (Stmt ↗ s) (m' ∪ mf) ∧ R None [] m')
  ∨ (∃ m' mv, S' = State [] (Stmt (⇈ mv) s) (m' ∪ mf) ∧ R mv [] m')
  ∨ red (δ⇒s) S'.
Proof.
  intros Hax ? ? p.
  apply rtc_bsteps in p. destruct p as [n p].
  apply (bsteps_subrel (δ⇒s) (δ⇒s{ [] }) _) in p.
  feed destruct (Hax n [] ↘ m mf S')
    as [|m' ? [d ???]]; auto with mem ax.
  * right. right. now apply (red_subrel (δ⇒s{ [] }) (δ⇒s) _).
  * efeed pose proof cstep_bsteps_preserves_stmt; eauto.
    subst. destruct d; try contradiction; intuition eauto.
Qed.
Lemma ax_stmt_sound P R s m S' :
  ∅ ⊢ {{ P }} s {{ R }} →
  P [] m →
  δ ⊢ State [] (Stmt ↘ s) m ⇒s* S' →
    (∃ m', S' = State [] (Stmt ↗ s) m' ∧ R None [] m')
  ∨ (∃ m' mv, S' = State [] (Stmt (⇈ mv) s) m' ∧ R mv [] m')
  ∨ red (δ⇒s) S'.
Proof.
  intros ?? p. rewrite <-(right_id_eq ∅ (∪) m) in p.
  destruct (ax_stmt_sound_sep P R s m ∅ S') as [[?[E ?]]|[[?[?[E ?]]]|]];
    try rewrite (right_id_eq ∅ (∪)) in E; intuition eauto with mem.
Qed.

Lemma ax_stmt_looping_sep P s m mf :
  ∅ ⊢ {{ P }} s {{ λ _, False }} →
  m ⊥ mf →
  P [] m →
  looping (δ⇒s) (State [] (Stmt ↘ s) (m ∪ mf)).
Proof.
  intros Hax ??. apply looping_alt. intros S' p.
  destruct (ax_stmt_sound_sep P (λ _, False)%A s m mf S')
    as [[??]|[[?[??]]|?]]; intuition.
Qed.
Lemma ax_stmt_looping P s m :
  ∅ ⊢ {{ P }} s {{ λ _, False }} →
  P [] m →
  looping (δ⇒s) (State [] (Stmt ↘ s) m).
Proof.
  intros. rewrite <-(right_id_eq ∅ (∪) m).
  eapply ax_stmt_looping_sep; eauto with mem.
Qed.

(** * The Hoare rules *)
(** We prove that the Hoare rules can be derived from the semantic definition
of the Hoare judgment. *)
(** ** Logical rules *)
Lemma ax_stmt_weak_packed Δ Pd Pd' s :
  (∀ d, down d s → Pd' d ⊆ Pd d) →
  (∀ d, up d s → Pd d ⊆ Pd' d) →
  ax_stmt Δ s Pd →
  ax_stmt Δ s Pd'.
Proof.
  intros Hdown Hup Hax n k d m mf S' ???? p.
  feed destruct (Hax n k d m mf S') as [|m' ? [????]]; auto.
  * now apply Hdown.
  * now left.
  * apply cstep_bsteps_preserves_stmt in p; subst.
    right. constructor. easy. now apply Hup. easy.
Qed.

Lemma ax_stmt_weak_pre Δ J R P P' Q s :
  P' ⊆ P →
  Δ; J; R ⊢ {{ P }} s {{ Q }} →
  Δ; J; R ⊢ {{ P' }} s {{ Q }}.
Proof. intro. apply ax_stmt_weak_packed; intros []; solve_assert. Qed.
Lemma ax_stmt_weak_post Δ J R P Q Q' s :
  Q ⊆ Q' →
  Δ; J; R ⊢ {{ P }} s {{ Q }} →
  Δ; J; R ⊢ {{ P }} s {{ Q' }}.
Proof. intro. apply ax_stmt_weak_packed; intros []; solve_assert. Qed.

Lemma ax_stmt_frame_packed Δ A Pd s :
  ax_stmt Δ s Pd →
  ax_stmt Δ s ((λ P, P * A)%A <$> Pd).
Proof.
  intros Hax n k d m mf S' ?? Hpre ? p.
  rewrite directed_fmap_spec in Hpre.
  destruct Hpre as [m2 [m3 [? [? [??]]]]]; simplify_equality.
  feed destruct (Hax n k d m2 (m3 ∪ mf) S') as [|m2' ? []]; auto.
  * now simplify_mem_disjoint.
  * now rewrite (associative_eq _).
  * rewrite (associative_eq _). left.
    + now simplify_mem_disjoint.
    + now rewrite <-(associative_eq _).
  * rewrite (associative_eq _). right.
    + constructor; auto.
      rewrite directed_fmap_spec.
      exists m2' m3. intuition. now simplify_mem_disjoint.
    + now simplify_mem_disjoint.
Qed.

Lemma ax_stmt_frame Δ J R A P Q s :
  Δ; J; R ⊢ {{ P }} s {{ Q }} →
  Δ; (λ l, J l * A); (λ v, R v * A) ⊢ {{ P * A }} s {{ Q * A }}.
Proof. apply ax_stmt_frame_packed. Qed.

Lemma ax_stmt_and Δ J R P Q Q' s :
  Δ; J; R ⊢ {{ P }} s {{ Q }} →
  Δ; J; R ⊢ {{ P }} s {{ Q' }} →
  Δ; J; R ⊢ {{ P }} s {{ Q ∧ Q' }}.
Proof.
  intros Hax1 Hax2 n k d m mf S' ???? p.
  feed destruct (Hax1 n k d m mf S') as [|m' ? [d' s' ??]]; auto.
    now destruct d; intuition.
   now left.
  feed inversion (Hax2 n k d m mf (State k (Stmt d' s') (m' ∪ mf)))
      as [|m'' ? [d'' s'' ??]]; auto.
    now destruct d; intuition.
   now left.
  simplify_equality. right.
  * constructor; auto.
    assert (m' = m'').
    { now apply mem_union_cancel_l with mf. }
    subst. destruct d'; intuition auto. now split.
  * easy.
Qed.

Lemma ax_stmt_or Δ J R P P' Q s :
  Δ; J; R ⊢ {{ P }} s {{ Q }} →
  Δ; J; R ⊢ {{ P' }} s {{ Q }} →
  Δ; J; R ⊢ {{ P ∨ P' }} s {{ Q }}.
Proof.
  intros Hax1 Hax2 n k [] m mf S' ?? Hpre ? p; try contradiction.
  * destruct Hpre.
    + feed destruct (Hax1 n k ↘ m mf S') as [|m' ? [d' s' ??]]; auto.
      { now left. }
      right. constructor. easy. now destruct d'; try left. easy.
    + feed destruct (Hax2 n k ↘ m mf S') as [|m' ? [d' s' ??]]; auto.
      { now left. }
      right. constructor. easy. now destruct d'; try right. easy.
  * feed destruct (Hax1 n k (↷l) m mf S') as [|m' ? [d' s' ??]]; auto.
    { now left. }
    right. constructor. easy. now destruct d'; try right. easy.
Qed.

Lemma ax_stmt_ex Δ J R {A} (P Q : A → assert) s :
  inhabited A →
  (∀ x, Δ; J; R ⊢ {{ P x }} s {{ Q x }}) →
  Δ; J; R ⊢ {{ ∃ x, P x }} s {{ ∃ x, Q x }}.
Proof.
  intros HA Hax n k [] m mf S' HΔ ? Hpre ? p; try contradiction.
  * destruct Hpre as [x Hpre].
    feed destruct (Hax x n k ↘ m mf S') as [|m' ? [d' s' ??]]; auto.
    { now left. }
    right. constructor. easy. now destruct d'; try exists x. easy.
  * destruct HA as [x].
    feed destruct (Hax x n k (↷l) m mf S') as [|m' ? [d' s' ??]]; auto.
    { now left. }
    right. constructor. easy. now destruct d'; try exists x. easy.
Qed.

(** ** Rules for function calls *)
Lemma ax_call J R Δ f es Pf (c : fcommon Pf) :
  Δ !! f = Some Pf →
  Δ; J; R ⊢ {{ assert_call (fpre Pf c) es }} call None f es
            {{ ∃ vs mv, fpost Pf c vs mv }}.
Proof.
  intros Hf n k [] m mf S' HΔ ? Hpre ? p; try contradiction.

  apply assert_call_correct in Hpre.
  destruct Hpre as [vs [??]].

  inv_csteps p as [| n' ??? p1 p2].
  { left. easy. solve_cred. }
  inv_cstep p1.
  simplify_expr_eval.

  feed destruct (ax_split
    (ax_fun_loc Pf c vs)
    (S n') (Call f vs) [CCall None f es] k
    m mf S') as [m' | m' ?? [? Hpost] ? _ p3].

  * intros. apply HΔ. easy. now apply (stack_indep (get_stack k)).
  * easy.
  * now apply bsteps_S.

  * left. easy. now apply (red_subrel (δ⇒s{CCall None f es :: k}) _ _).
  * inv_csteps p3 as [| n'' ??? p3 p4 ].
    { left. easy. solve_cred. }
    inv_cstep p3. last_cstep p4.
    right.
    + constructor; auto.
      eexists _,_. apply (stack_indep []), Hpost.
    + easy.
Qed.

Lemma ax_call_Some J R Δ A f e es Pf (c : fcommon Pf) Q :
  Δ !! f = Some Pf →
  (∀ vs mv, fpost Pf c vs mv * A → ∃ a v,
    e⇓ptr a ∧ ⌜ mv = Some v ⌝ ∧ load (ptr a)⇓- ∧ <[a:=v]>Q)%A →
  Δ; J; R ⊢ {{ assert_call (fpre Pf c) es * A }} call (Some e) f es {{ Q }}.
Proof.
  intros Hf HQ n k [] m mf S' HΔ ? Hpre ? p; try contradiction.

  destruct Hpre as [m1 [m2 [? [? [Hpre ?]]]]]; subst.
  simplify_mem_disjoint.
  apply assert_call_correct in Hpre.
  destruct Hpre as [vs [??]].

  inv_csteps p as [| n' ??? p1 p2].
  { left. now simplify_mem_disjoint. solve_cred. }

  rewrite <-(associative_eq _) in p1.
  inv_cstep p1.
  simplify_expr_eval.

  feed destruct (ax_split
    (ax_fun_loc Pf c vs)
    (S n') (Call f vs) [CCall (Some e) f es] k
    m1 (m2 ∪ mf) S') as [m' ??? Hred | m' ?? [? Hpost] ? _ p3].

  * intros. apply HΔ. easy. now apply (stack_indep (get_stack k)).
  * simplify_mem_disjoint.
  * now apply bsteps_S.

  * rewrite !(associative_eq (∪)) in Hred |- *. left.
    + simplify_mem_disjoint.
    + now apply (red_subrel (δ⇒s{CCall (Some e) f es :: k}) _ _).
  * edestruct HQ as [a [v' [? [? [[v'' ?] ?]]]]].
    { exists m' m2. repeat split.
      + simplify_mem_disjoint.
      + eapply (stack_indep _). eauto.
      + eassumption. }
    unfold_assert in *; simplify_option_bind; subst.
    rewrite (associative_eq _) in p3.
    inv_csteps p3 as [| n'' ??? p3 p4 ].
    { left. simplify_mem_disjoint. solve_cred. }
    inv_cstep p3. last_cstep p4.
    simplify_expr_eval. rewrite mem_union_insert_l.
    right.
    + now constructor.
    + simplify_mem_disjoint.
      eapply mem_disjoint_Some_l; [| eassumption].
      simplify_mem_disjoint.
Qed.

Lemma ax_add_funs Δ Δ' s Pd :
  (∀ f Pf, Δ' !! f = Some Pf → is_Some (δ !! f)) →
  (∀ f Pf sf c vs,
    Δ' !! f = Some Pf →
    δ !! f = Some sf →
    Δ' ∪ Δ ⊢ {{ Π imap (λ i v, var i ↦ val v) vs * fpre Pf c vs }}
     sf
    {{ λ mv, Π imap (λ i _, var i ↦ -) vs * fpost Pf c vs mv }}) →
  ax_stmt (Δ' ∪ Δ) s Pd →
  ax_stmt Δ s Pd.
Proof.
  intros HΔ' HaxΔ'. revert s.
  cut (∀ f Pf sf n c vs m mf m' k bs S',
   Δ' !! f = Some Pf →
   δ !! f = Some sf →
   ax_funs n (Δ' ∪ Δ) →
   m ⊥ mf →
   alloc_params (m ∪ mf) bs vs m' →
   (fpre Pf c vs) (get_stack k) m →
   δ ⊢ State (CParams bs :: k) (Stmt ↘ sf) m' ⇒s{k}^n S' →
   ax_valid (ax_fun_loc Pf c vs) k mf S').

  { intros help s Hax n k d m mf S' HΔ.
    eapply Hax. clear d s Pd k m mf S' Hax.
   induction n as [n IH] using lt_wf_ind.
   intros f' Pf' c vs m mf k S' Hf' ?? p.
   rewrite finmap_union_Some in Hf'.
   destruct Hf' as [? | [_ ?]]; [| eapply HΔ; eauto ].

   destruct (HΔ' f' Pf'); trivial.
   inv_csteps p as [| n' ??? p1 p2].
   { left. easy. solve_cred. }

   inv_cstep p1.
   apply (ax_funs_weaken n') in HΔ; [| omega].
   eapply help; eauto. }

  intros f Pf sf n c vs m mf m' k bs S3 ???? Hparams Hpre p1.

  apply alloc_params_insert_list in Hparams.
  destruct Hparams as [? [??]]; subst.
  rewrite mem_insert_list_union, (associative_eq (∪)) in p1.
  simplify_is_free.

  feed destruct (ax_split
    (ax_stmt_loc (dassert_pack_top
      (Π imap (λ i v, var i ↦ val v) vs * fpre Pf c vs)
      (λ mv, Π imap (λ i _, var i ↦ -) vs * fpost Pf c vs mv)))%A
    n (Stmt ↘ sf) [CParams bs] k
    (list_to_map (zip bs vs) ∪ m)
    mf S3) as [m' | m' ? S2 [??? Hpost] ? _ p2].

  * intros. eapply HaxΔ'; eauto.
    simpl. rewrite <-mem_insert_list_union.
    apply assert_alloc_params_alt; auto.
  * simplify_mem_disjoint.
    apply mem_disjoint_list_to_map_zip_l; eauto with mem.
  * easy.

  * left. easy. now apply (red_subrel (δ⇒s{CParams bs :: k}) _ _).
  * inv_csteps p2 as [| n3 ? S3 ? p2 p3 ].
    { left. easy. solve_cred. }
    inv_cstep p2.
    + last_cstep p3.
      rewrite mem_union_delete_list, (delete_list_notin mf)
       by now apply is_free_list_free.
      right.
      - constructor. apply assert_free_params with vs; eauto with mem.
      - now auto with mem.
    + last_cstep p3.
      rewrite mem_union_delete_list, (delete_list_notin mf)
       by now apply is_free_list_free.
      right.
      - constructor. apply assert_free_params with vs; eauto with mem.
      - now auto with mem.
Qed.

(** ** Structural rules *)
Lemma ax_skip Δ J R P : Δ; J; R ⊢ {{ P }} skip {{ P }}.
Proof.
  intros n k d m mf S' ???? p.
  inv_csteps p as [| ???? p1 p2].
  { left. easy. solve_cred. }
  inv_cstep p1. last_cstep p2.
  right. now constructor. easy.
Qed.

Lemma ax_goto Δ J R Q l : Δ; J; R ⊢ {{ J l }} goto l {{ Q }}.
Proof.
  intros n k d m mf S' ???? p.
  inv_csteps p as [| ???? p1 p2].
  { left. easy. solve_cred. }
  inv_cstep p1. last_cstep p2.
  right. constructor; solve_elem_of. easy.
Qed.

Lemma ax_return_None Δ J R Q :
  Δ; J; R ⊢ {{ R None }} ret None {{ Q }}.
Proof.
  intros n k d m mf S' ???? p.
  inv_csteps p as [| ???? p1 p2 ].
  { left. easy. solve_cred. }
  inv_cstep p1. last_cstep p2.
  right. now constructor. easy.
Qed.

Lemma ax_return_Some Δ J R e Q :
  Δ; J; R ⊢ {{ ∃ v, e⇓v ∧ R (Some v) }} ret (Some e) {{ Q }}.
Proof.
  intros n k [] m mf S' ?? Hpre ? p; try contradiction.
  destruct Hpre as [v [??]]. unfold_assert in *.
  inv_csteps p as [| ???? p1 p2 ].
  { left. easy. solve_cred. }
  inv_cstep p1. last_cstep p2.
  simplify_expr_eval.
  right. now constructor. easy.
Qed.

Lemma ax_assign Δ J R e1 e2 Q :
  Δ; J; R ⊢ {{ ∃ a v, e1⇓ptr a ∧ e2⇓v
               ∧ load (ptr a)⇓- ∧ <[a:=v]>Q }} e1 ::= e2 {{ Q }}.
Proof.
  intros n k [] m mf S' ?? Hpre ? p; try contradiction.
  destruct Hpre as [a [v [?[?[[v' ?]?]]]]].
  unfold_assert in *. simplify_option_bind.
  inv_csteps p as [| ???? p1 p2 ].
  { left. easy. solve_cred. }
  inv_cstep p1. last_cstep p2.
  simplify_expr_eval. rewrite mem_union_insert_l.
  right.
  * now constructor.
  * simplify_mem_disjoint. eapply mem_disjoint_Some_l; eauto.
Qed.

Lemma ax_block_packed Δ Pd s :
  ax_stmt Δ s ((λ P, var O ↦ - * P↑)%A <$> Pd) →
  ax_stmt Δ (block s) Pd.
Proof.
  intros Hax n k d m mf S5. revert n d m.
  cut (∀ n d m b v,
   ax_funs n Δ →
   mem_disjoint m mf →
   is_free (m ∪ mf) b →
   δ ⊢ State (CBlock b :: k) (Stmt d s) (<[b:=v]>(m ∪ mf)) ⇒s{k}^n S5 →
   down d s →
   Pd d (get_stack k) m →
   ax_valid (ax_stmt_loc Pd) k mf S5).

  { intros help n d m ???? p.
    inv_csteps p as [| n' ??? p1 p2].
    { left. easy. solve_cred. }
    inv_cstep p1; eapply (help n'); eauto with ax. }

  intros n1 d1 m1 b v ??? p1 ? Hpre.
  simplify_is_free.
  rewrite mem_union_insert_l in p1.

  feed destruct (ax_split
    (ax_stmt_loc ((λ P, var O ↦ - * P↑)%A <$> Pd))
    n1 (Stmt d1 s) [CBlock b] k
    (<[b:=v]>m1) mf S5) as [m2 | m2 ? S5 [d2 s2 ? Hpost] ? p p2]; auto.

  * intros. apply Hax; auto.
    rewrite directed_fmap_spec. now apply assert_alloc.
  * simplify_mem_disjoint.

  * left. easy. solve_cred.
  * apply cstep_bsteps_preserves_stmt in p. subst s2.
    rewrite directed_fmap_spec in Hpost. simpl in Hpost.
    apply assert_free in Hpost.
    inv_csteps p2 as [| n3 ? S3 ? p2 p3].
    { left. easy. solve_cred. }

    inv_cstep p2; try solve_stmt_elem_of.
    + last_cstep p3. rewrite mem_union_delete, (delete_notin mf).
      right. now constructor. simplify_mem_disjoint. easy.
    + last_cstep p3. rewrite mem_union_delete, (delete_notin mf).
      right. now constructor. simplify_mem_disjoint. easy.
    + last_cstep p3. rewrite mem_union_delete, (delete_notin mf).
      right. now constructor. simplify_mem_disjoint. easy.
Qed.

Lemma ax_block Δ J R P Q s :
  Δ; (λ l, var O ↦ - * J l↑); (λ v, var O ↦ - * R v↑) ⊢
    {{ var O ↦ - * P↑ }} s {{ var O ↦ - * Q↑ }} →
  Δ; J; R ⊢ {{ P }} block s {{ Q }}.
Proof. intros. now apply ax_block_packed. Qed.

Lemma ax_label Δ J R l s Q :
  Δ; J; R ⊢ {{ J l }} s {{ Q }} →
  Δ; J; R ⊢ {{ J l }} l :; s {{ Q }}.
Proof.
  intros Hax n k d m mf S5. revert n d m.
  cut (∀ n d m,
   ax_funs n Δ →
   mem_disjoint m mf →
   δ ⊢ State (CItem (l :; □) :: k) (Stmt d s) (m ∪ mf) ⇒s{k}^n S5 →
   down d s →
   dassert_pack (J l) Q R J d (get_stack k) m →
   ax_valid (ax_stmt_loc (dassert_pack (J l) Q R J)) k mf S5).

  { intros help n d m ???? p.
    inv_csteps p as [| n' ??? p1 p2].
    { left. easy. solve_cred. }
    inv_cstep p1; eapply (help n'); eauto with ax. }

  induction n as [n1 IH] using lt_wf_ind.
  intros d1 m1 ?? p1 ??.

  feed destruct (ax_split
    (ax_stmt_loc (dassert_pack (J l) Q R J))
    n1 (Stmt d1 s) [CItem (l :;□)] k
    m1 mf S5) as [m2 | m2 ? S5 [d2 s2 ??] ? p p2]; auto.
  { left. easy. solve_cred. }

  apply cstep_bsteps_preserves_stmt in p. subst s2.
  inv_csteps p2 as [| n3 ? S3 ? p2 p3].
  { left. easy. solve_cred. }

  inv_cstep p2; try solve_stmt_elem_of.
  * last_cstep p3. right. now constructor. easy.
  * last_cstep p3. right. now constructor. easy.
  * match goal with
    | _ : ?l' ∉ labels s |- _ => destruct (decide (l' = l))
    end; subst.
    + inv_csteps p3 as [| n4 ? S4 ? p3 p4].
      { left. easy. solve_cred. }
      inv_cstep p3. eapply (IH n4); eauto with ax.
    + last_cstep p3. right. constructor; solve_elem_of. easy.
Qed.

Lemma ax_while Δ J R P e s :
  Δ; J; R ⊢ {{ P ∧ e⇓⊤ }} s {{ P ∧ e⇓- }} →
  Δ; J; R ⊢ {{ P ∧ e⇓- }} while (e) s {{ P ∧ e⇓⊥ }}.
Proof.
  intros Hax n k d m mf S5. revert n d m.
  cut (∀ n d m,
   ax_funs n Δ →
   mem_disjoint m mf →
   δ ⊢ State (CItem (while (e) □) :: k) (Stmt d s) (m ∪ mf) ⇒s{k}^n S5 →
   down d s →
   dassert_pack (P ∧ e⇓⊤) (P ∧ e⇓-) R J d (get_stack k) m →
   ax_valid (ax_stmt_loc (dassert_pack (P ∧ e⇓-) (P ∧ e⇓⊥) R J)) k mf S5).

  { intros help n [] m ?? Hpre ? p; try contradiction.
    * destruct Hpre as [? [v Hv]]. unfold_assert in Hv.
      inv_csteps p as [| n' ??? p1 p2].
      { left. easy. destruct (val_true_false_dec v); solve_cred. }
      inv_cstep p1; simplify_expr_eval.
      + eapply (help n'); eauto with ax. solve_assert.
      + last_cstep p2.
        right. constructor; solve_assert. easy.
    * inv_csteps p as [| n' ??? p1 p2].
      { left. easy. solve_cred. }
      inv_cstep. eapply (help n'); eauto with ax. }

  induction n as [n1 IH] using lt_wf_ind.
  intros d1 m1 ?? p1 ??.

  feed destruct (ax_split
    (ax_stmt_loc (dassert_pack (P ∧ e⇓⊤) (P ∧ e⇓-) R J))
    n1 (Stmt d1 s) [CItem (while (e) □)] k
    m1 mf S5) as [m2 | m2 ? S5 [d2 s2 ? Hpost] ? p p2]; auto.
  { left. easy. solve_cred. }

  apply cstep_bsteps_preserves_stmt in p. subst s2.
  inv_csteps p2 as [| n3 ? S3 ? p2 p3].
  { left. easy. solve_cred. }

  inv_cstep p2; try solve_stmt_elem_of.
  * destruct Hpost as [? [v Hv]]. unfold_assert in Hv.
    inv_csteps p3 as [| n4 ? S4 ? p3 p4].
    { left. easy. destruct (val_true_false_dec v); solve_cred. }
    inv_cstep p3; simplify_expr_eval.
    + eapply (IH n4); eauto with ax. solve_assert.
    + last_cstep p4.
      right. constructor; solve_assert. easy.
  * last_cstep p3. right. now constructor. easy.
  * last_cstep p3. right. now constructor. easy.
Qed.

Lemma ax_comp Δ J R sl sr P P' Q :
  Δ; J; R ⊢ {{ P }} sl {{ P' }} →
  Δ; J; R ⊢ {{ P' }} sr {{ Q }} →
  Δ; J; R ⊢ {{ P }} sl ;; sr {{ Q }}.
Proof.
  intros Haxl Haxr n k d m mf S5. revert n d m.
  cut (∀ n d m,
   ax_funs n Δ →
   mem_disjoint m mf →
   (δ ⊢ State (CItem (□ ;; sr) :: k) (Stmt d sl) (m ∪ mf) ⇒s{k}^n S5
     ∧ down d sl
     ∧ dassert_pack P P' R J d (get_stack k) m)
   ∨ (δ ⊢ State (CItem (sl ;; □) :: k) (Stmt d sr) (m ∪ mf) ⇒s{k}^n S5
     ∧ down d sr
     ∧ dassert_pack P' Q R J d (get_stack k) m) →
   ax_valid (ax_stmt_loc (dassert_pack P Q R J)) k mf S5).

  { intros help n d m ???? p.
    inv_csteps p as [| n' ??? p1 p2].
    { left. easy. solve_cred. }
    inv_cstep p1; eapply (help n'); eauto with ax. }

  induction n as [n1 IH] using lt_wf_ind.
  intros d1 m1 ?? [[p1 [??]] | [p1 [??]]].

  * feed destruct (ax_split
      (ax_stmt_loc (dassert_pack P P' R J))
      n1 (Stmt d1 sl) [CItem (□;;sr)] k
      m1 mf S5) as [m2 | m2 ? S5 [d2 s2 ??] ? p p2]; auto.
    { left. easy. solve_cred. }

    apply cstep_bsteps_preserves_stmt in p. subst s2.
    inv_csteps p2 as [| n3 ? S3 ? p2 p3].
    { left. easy. solve_cred. }

    inv_cstep p2; try solve_stmt_elem_of.
    + eapply (IH n3); intuition eauto with ax.
    + last_cstep p3. right. now constructor. easy.
    + match goal with
      | _ : ?l ∉ labels sl |- _ => destruct (decide (l ∈ labels sr))
      end; subst.
      - inv_csteps p3 as [| n4 ? S4 ? p3 p4].
        { left. easy. solve_cred. }
        inv_cstep p3. eapply (IH n4); intuition eauto with ax.
      - last_cstep p3. right. constructor; solve_elem_of. easy.

  * feed destruct (ax_split
      (ax_stmt_loc (dassert_pack P' Q R J))
      n1 (Stmt d1 sr) [CItem (sl;;□)] k
      m1 mf S5) as [m2 | m2 ? S5 [d2 s2 ??] ? p p2]; auto.
    { left. easy. solve_cred. }

    apply cstep_bsteps_preserves_stmt in p. subst s2.
    inv_csteps p2 as [| n3 ? S3 ? p2 p3].
    { left. easy. solve_cred. }

    inv_cstep p2; try solve_stmt_elem_of.
    + last_cstep p3. right. now constructor. easy.
    + last_cstep p3. right. now constructor. easy.
    + match goal with
      | _ : ?l ∉ labels sr |- _ => destruct (decide (l ∈ labels sl))
      end; subst.
      - inv_csteps p3 as [| n4 ? S4 ? p3 p4].
        { left. easy. solve_cred. }
        inv_cstep p3. eapply (IH n4); intuition eauto with ax.
      - last_cstep p3. right. constructor; solve_elem_of. easy.
Qed.

Lemma ax_if Δ J R e sl sr P Q :
  Δ; J; R ⊢ {{ P ∧ e⇓⊤ }} sl {{ Q }} →
  Δ; J; R ⊢ {{ P ∧ e⇓⊥ }} sr {{ Q }} →
  Δ; J; R ⊢ {{ P ∧ e⇓- }} IF e then sl else sr {{ Q }}.
Proof.
  intros Haxl Haxr n k d m mf S5. revert n d m.
  cut (∀ n d m,
   ax_funs n Δ →
   mem_disjoint m mf →
   (δ ⊢ State (CItem (IF e then □ else sr) :: k) (Stmt d sl) (m ∪ mf)
         ⇒s{k}^n S5
     ∧ down d sl
     ∧ dassert_pack (P ∧ e⇓⊤)%A Q R J d (get_stack k) m)
   ∨ (δ ⊢ State (CItem (IF e then sl else □) :: k) (Stmt d sr) (m ∪ mf)
           ⇒s{k}^n S5
     ∧ down d sr
     ∧ dassert_pack (P ∧ e⇓⊥)%A Q R J d (get_stack k) m) →
   ax_valid (ax_stmt_loc (dassert_pack (P ∧ e⇓-)%A Q R J)) k mf S5).

  { intros help n [] m ?? Hpre ? p; try contradiction.
    * destruct Hpre as [? [v Hv]]. unfold_assert in Hv.
      inv_csteps p as [| n' ??? p1 p2].
      { left. easy. destruct (val_true_false_dec v); solve_cred. }
      inv_cstep p1; simplify_expr_eval; eapply (help n');
        eauto with ax; solve_assert.
    * inv_csteps p as [| n' ??? p1 p2].
      { left. easy. solve_cred. }
      inv_cstep p1; eapply (help n'); eauto with ax. }

  induction n as [n1 IH] using lt_wf_ind.
  intros d1 m1 ?? [[p1 [??]] | [p1 [??]]].

  * feed destruct (ax_split
      (ax_stmt_loc (dassert_pack (P ∧ e⇓⊤)%A Q R J))
      n1 (Stmt d1 sl) [CItem (IF e then □ else sr)] k
      m1 mf S5) as [m2 | m2 ? S5 [d2 s2 ??] ? p p2]; auto.
    { left. easy. solve_cred. }

    apply cstep_bsteps_preserves_stmt in p. subst s2.
    inv_csteps p2 as [| n3 ? S3 ? p2 p3].
    { left. easy. solve_cred. }

    inv_cstep p2; try solve_stmt_elem_of.
    + last_cstep p3. right. now constructor. easy.
    + last_cstep p3. right. now constructor. easy.
    + match goal with
      | _ : ?l ∉ labels sl |- _ => destruct (decide (l ∈ labels sr))
      end; subst.
      - inv_csteps p3 as [| n4 ? S4 ? p3 p4].
        { left. easy. solve_cred. }
        inv_cstep p3. eapply (IH n4); intuition eauto with ax.
      - last_cstep p3. right. constructor; solve_elem_of. easy.

  * feed destruct (ax_split
      (ax_stmt_loc (dassert_pack (P ∧ e⇓⊥)%A Q R J))
      n1 (Stmt d1 sr) [CItem (IF e then sl else □)] k
      m1 mf S5) as [m2 | m2 ? S5 [d2 s2 ??] ? p p2]; auto.
    { left. easy. solve_cred. }

    apply cstep_bsteps_preserves_stmt in p. subst s2.
    inv_csteps p2 as [| n3 ? S3 ? p2 p3].
    { left. easy. solve_cred. }

    inv_cstep p2; try solve_stmt_elem_of.
    + last_cstep p3. right. now constructor. easy.
    + last_cstep p3. right. now constructor. easy.
    + match goal with
      | _ : ?l ∉ labels sr |- _ => destruct (decide (l ∈ labels sl))
      end; subst.
      - inv_csteps p3 as [| n4 ? S4 ? p3 p4].
        { left. easy. solve_cred. }
        inv_cstep p3. eapply (IH n4); intuition eauto with ax.
      - last_cstep p3. right. constructor; solve_elem_of. easy.
Qed.
End axiomatic.
