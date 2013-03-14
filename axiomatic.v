(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file defines an axiomatic semantics (in the form of separation logic)
for our language. This axiomatic semantics has two judgments: one for
statements and one for expressions. Statement judgment are sextuples of the
shape [Δ \ R \ J ⊨ₛ {{ P }} s {{ Q }}] where:

- [s] is a statement, and [P] and [Q] are assertions called the pre- and
  postcondition of [s], respectively.
- [Δ] is a finite function from function names to their pre- and postconditions.
  This environment is used to cope with (mutually) recursive functions.
- [R] is a function that gives the returning condition for a return value.
  Hence, [R v] has to hold to execute a [return e] where execution of [e] yields
  the value [v].
- [J] is a function that gives the jumping condition for each goto. Hence,
  [J l] has to hold to execute a [goto l].

The assertions [P], [Q], [R] and [J] correspond to the four directions [↘], [↗],
[⇈] and [↷] in which traversal through a statement can be performed. We
therefore treat the sextuple as a triple [Δ \ Pd ⊨ₚ s] where [Pd] is a function
from directions to assertions such that [Pd ↘ = P], [Pd ↗ = Q],
[Pd (⇈ v) = R v] and [P (↷ l) = J l]. *)

(** Furthermore, expression judgments are quadruples [Δ ⊨ₑ {{ P }} e {{ Q }}].
As usual, [P] and [Q] are the pre- and postcondition of [e], but whereas
the precondition is just an assertion, the postcondition is a function from
values to assertions. It ensures that if execution of [e] yields a value [v],
then [Q v] holds. *)

(** Instead of first defining the axiomatic semantics inductively as a set of
derivation rules, we directly define an interpretation, and show that the rules
of separation logic and novel rules for our specific features can be derived
from this interpretation. *)
Require Import fin_maps.
Require Export assertions expression_eval_correct.
Local Open Scope nat_scope.

Section axiomatic.
Context (δ : funenv).

(** * The Hoare judgment *)
(** We want [Δ \ R \ J ⊨ₛ {{ P }} s {{ Q }}] to ensure partial program
correctness. Intuitively, that means: if [P (get_stack k) m] and
[State k (Stmt s ↘) m ⇒* State k (Stmt s ↗) m'], then [Q (get_stack k) m'].
Due to the additional features we consider, this intuition is too simple.

- We also have to account for reductions starting or ending in the directions
  [⇈] or [↷]. The notation [Δ \ Pd ⊨ₚ s] to take [R], [J], [P] and [Q] together
  as one function [Pd] comes in handy here.
  The intuitive meaning of [Δ \ Pd ⊨ₚ s] is: if [Pd d (get_stack k) m] and
  [State k (Stmt s d) m ⇒* State k (Stmt s d') m'], then
  [Pd d' (get_stack k) m'].
- We should enforce the reduction [State k (Stmt s d) m ⇒*
  State k (Stmt s d') m'] to remain below [k] as it could otherwise take too
  many items of the program context.
- Our language has various kinds of undefined behavior (e.g. invalid pointer
  dereferences). We therefore also want [Δ \ Pd ⊨ₚ s] to guarantee that [s]
  does not exhibit any undefined behaviors.
  Hence, [Δ \ Pd ⊨ₚ s] should at least guarantee that if [P d k m] and
  [State k (Stmt s d) m ⇒* S], then [S] is either:
-- reducible (no undefined behavior has occurred), or,
-- of the shape [State k (Stmt s d') m'] with [Pd d' (get_stack k) m']
   (execution is finished).

- The program should satisfy a form of memory safety so as the make the frame
  rule derivable. Also, in order to deal with non-deterministic execution
  of expressions, we should be able to interleave executions of different
  subexpressions.
  Hence, if before execution the memory can be extended with a disjoint part
  [mf] (called the framing memory), that part should not be modified during
  the execution. Also, to allow interleaving, the framing memory [mf] should be
  allowed to be changed at any point during the execution.
- We take a step indexed approach in order to relate the assertions of
  functions in [Δ] to the statement [s].

Nearly all of the above properties apply to the expression judgment
[Δ ⊨ₑ {{ P }} e {{ Q }}] as well. Therefore, we first define a more general
notion that captures these properties for both kinds of judgments. *)

(** The intuitive meaning of the predicate [ax P l n k φ m] is that all
[cstep_in_ctx δ l]-reductions paths of at most [n] steps starting at
[State k φ (m ∪ mf)] with an arbitrary framing memory [mf]:
- do not exhibit undefined behavior,
- do not get stuck,
- always satisfy [locks φ ⊆ locks m] during the execution, and,
- if finished satisfy [P].

To allow interleaving of expressions, we need to be able to change the framing
memory [mf] during the execution. Therefore, instead of defining [ax] using
the reflexive transitive closure, we define this predicate inductively using
single steps. The condition on the annotated locks in the program with respect
to the locks in the memory is used to separate the locks. *)
Section ax.
  Context (P : stack → mem → focus → Prop).
  Context `{P_nf : PropHolds (∀ mf l m φ,
    P (get_stack l) m φ →
    nf (cstep_in_ctx δ l) (State l φ (m ∪ mf)))}.

  Inductive ax (l : ctx) : nat → ctx → focus → mem → Prop :=
    | ax_O k φ m :
       ax l 0 k φ m
    | ax_done n φ m :
       P (get_stack l) m φ →
       ax l n l φ m
    | ax_further n k φ m :
       (∀ mf,
         m ⊥ mf →
         red (cstep_in_ctx δ l) (State k φ (m ∪ mf))) →
       (∀ mf S',
         m ⊥ mf →
         δ ⊢ₛ State k φ (m ∪ mf) ⇒{l} S' →
         ax_next l n mf S') →
       ax l (S n) k φ m
  with ax_next (l : ctx) : nat → mem → state → Prop :=
    | mk_ax_next n mf k φ m :
       m ⊥ mf →
       φ ≠ Undef →
       locks φ ⊆ locks m →
       ax l n k φ m →
       ax_next l n mf (State k φ (m ∪ mf)).

  Lemma mk_ax_next_alt l n mf k φ m :
    m ⊥ mf →
    φ ≠ Undef →
    locks φ = ∅ →
    ax l n k φ m →
    ax_next l n mf (State k φ (m ∪ mf)).
  Proof. constructor; esolve_elem_of. Qed.

  Lemma ax_further_pred l n k φ m :
    (∀ mf,
      m ⊥ mf →
      red (cstep_in_ctx δ l) (State k φ (m ∪ mf))) →
    (∀ mf S',
      m ⊥ mf →
      δ ⊢ₛ State k φ (m ∪ mf) ⇒{l} S' →
      ax_next l (pred n) mf S') →
    ax l n k φ m.
  Proof. destruct n; constructor (solve [auto]). Qed.

  Lemma ax_S l n k φ m
    (Hax : ax l (S n) k φ m) : ax l n k φ m
  with ax_next_S l n mf S'
    (Hax : ax_next l (S n) mf S') : ax_next l n mf S'.
  Proof.
  { inversion Hax; subst.
    * by apply ax_done.
    * destruct n.
      + apply ax_O.
      + apply ax_further; [done |].
        intros. apply (ax_next_S). eauto. }
  { inversion Hax; subst.
    constructor; trivial. by apply ax_S. }
  Qed.

  Lemma ax_plus_l l n1 n2 k φ m :
    ax l (n1 + n2) k φ m → ax l n2 k φ m.
  Proof. induction n1; simpl; auto using ax_S. Qed.
  Lemma ax_next_plus_l l n1 n2 mf S' :
    ax_next l (n1 + n2) mf S' → ax_next l n2 mf S'.
  Proof. induction n1; simpl; auto using ax_next_S. Qed.
  Lemma ax_le l n1 n2 k φ m :
    ax l n2 k φ m → n1 ≤ n2 → ax l n1 k φ m.
  Proof.
    intros Hax ?. rewrite (Minus.le_plus_minus n1 n2), plus_comm in Hax;
     eauto using ax_plus_l.
  Qed.
  Lemma ax_next_le l n1 n2 mf S :
    ax_next l n2 mf S → n1 ≤ n2 → ax_next l n1 mf S.
  Proof.
    intros Hax ?. rewrite (Minus.le_plus_minus n1 n2), plus_comm in Hax;
     eauto using ax_next_plus_l.
  Qed.
  Lemma ax_pred l n k φ m : ax l n k φ m → ax l (pred n) k φ m.
  Proof. intros. eauto using ax_le with arith. Qed.

  Lemma ax_step n l mf k φ m S' :
    m ⊥ mf →
    ax l (S n) k φ m →
    δ ⊢ₛ State k φ (m ∪ mf) ⇒{l} S' →
    ax_next l n mf S'.
  Proof.
    intros ? Hax p.
    inversion Hax as [| | ???? _ Hnext]. simplify_equality.
    * destruct (P_nf mf k m φ). done. solve_cred.
    * eauto.
  Qed.

  Lemma ax_red n l mf k φ m :
    m ⊥ mf →
    ax l (S n) k φ m →
    ¬P (get_stack k) m φ →
    red (cstep_in_ctx δ l) (State k φ (m ∪ mf)).
  Proof. inversion 2; subst; by auto. Qed.

  Lemma ax_step_undef n l mf k φ m k' m' :
    m ⊥ mf →
    δ ⊢ₛ State k φ (m ∪ mf) ⇒{l} State k' Undef m' →
    ¬ax l (S n) k φ m.
  Proof.
    intros ? p Hax.
    by feed inversion (ax_step n l mf k φ m (State k' Undef m')); subst.
  Qed.

  Lemma ax_steps n1 n2 l mf φ k m S' :
    m ⊥ mf →
    φ ≠ Undef →
    locks φ ⊆ locks m →
    ax l (n1 + n2) k φ m →
    δ ⊢ₛ State k φ (m ∪ mf) ⇒{l}^n1 S' →
    ax_next l n2 mf S'.
  Proof.
    revert k φ m.
    induction n1 as [n1 IH] using lt_wf_ind.
    intros k φ m ??? Hax p.
    inv_csteps p as [|n' ? S'' ? p1 p2].
    * constructor; eauto using ax_plus_l.
    * feed inversion (ax_step (n' + n2) l mf k φ m S''); subst; eauto.
  Qed.
End ax.
Hint Resolve ax_pred ax_S : ax.

(** The predicate [ax] can be composed. This property is used to prove the
structural Hoare rules. *)
Lemma ax_compose P Q n φ k1 k2 k3 m :
  suffix_of k2 k1 →
  suffix_of k3 k2 →
  ax P k2 n k1 φ m →
  (∀ m' φ',
    P (get_stack k2) m' φ' →
    ax Q k3 n k2 φ' m') →
  ax Q k3 n k1 φ m.
Proof.
  revert φ k1 m. induction n as [|n IH].
  { intros. apply ax_O. }
  intros φ k1 m ?? Hax Hnext.
  inversion Hax as [| | ???? Hred Hstep]; subst.
  { by apply Hnext. }
  apply ax_further.
  { intros mf ?. apply (red_subrel (cstep_in_ctx δ k2) _ _). auto. }
  intros ??? [p _].
  feed pose proof (cred_preserves_subctx δ k2
    (State k1 φ (m ∪ mf)) S'); auto.
  feed destruct (Hstep mf S') as [? mf' k' φ' m']; trivial.
  { by split. }
  constructor; trivial. apply IH; trivial.
  intros m'' φ'' ?. by apply ax_S, Hnext.
Qed.

(** A variant of the previous lemma that is more convenient for backwards
chaining. *)
Lemma ax_compose_cons P Q n φ l E m :
  ax P (E :: l) n (E :: l) φ m →
  (∀ m' φ',
    P (get_stack (E :: l)) m' φ' →
    ax Q l n (E :: l) φ' m') →
  ax Q l n (E :: l) φ m.
Proof. apply ax_compose; solve_suffix_of. Qed.

(** The predicates [ax] satisfies an abstract version of the frame, weaken, and
conjunction rule. These abstract versions are used to prove the concrete rules
for both the expression and statement judgment. *)
Lemma ax_frame (P Q : stack → mem → focus → Prop) m2 l n k φ m :
  (∀ m φ,
    m ⊥ m2 →
    P (get_stack l) m φ →
    Q (get_stack l) (m ∪ m2) φ) →
  ax P l n k φ m →
  m ⊥ m2 →
  ax Q l n k φ (m ∪ m2).
Proof.
  intros HPQ. revert k φ m.
  induction n as [|n]; [constructor |].
  intros k φ m Hax ?.
  inversion Hax as [| |???? Hred Hstep]; subst.
  { by apply ax_done, HPQ. }
  apply ax_further.
  { intros mf ?. rewrite <-(associative_eq _).
    apply Hred. by apply mem_disjoint_union_move_l. }
  intros mf S' ? p.
  feed inversion (Hstep (m2 ∪ mf) S'); subst.
  * by apply mem_disjoint_union_move_l.
  * by rewrite (associative_eq _).
  * rewrite (associative_eq _). constructor; auto.
    + apply mem_disjoint_union_move_r; eauto using mem_disjoint_union_lr.
    + rewrite mem_locks_union by (eapply mem_disjoint_union_rl; eauto).
      esolve_elem_of.
    + apply IHn; eauto using mem_disjoint_union_rl, mem_disjoint_union_lr.
Qed.

Lemma ax_weaken (P Q : stack → mem → focus → Prop) l n k φ m :
  (∀ m φ,
    P (get_stack l) m φ →
    Q (get_stack l) m φ) →
  ax P l n k φ m →
  ax Q l n k φ m.
Proof.
  intros HPQ ?.
  rewrite <-(right_id_eq ∅ (∪) m). apply (ax_frame P Q).
  * intros. rewrite (right_id_eq ∅ (∪)). auto.
  * done.
  * by apply mem_disjoint_empty_r.
Qed.

Global Instance: Proper (((=) ==> (=) ==> (=) ==> impl) ==>
   (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> impl) ax.
Proof.
  intros ?? H ? l ?? n ?? k ?? φ ?? m ?.
  subst. red. apply ax_weaken. intros ??. by apply H.
Qed.
Global Instance: Proper (((=) ==> (=) ==> (=) ==> iff) ==>
   (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> iff) ax.
Proof.
  intros ?? H ? l ?? n ?? k ?? φ ?? m ?. subst. split; apply ax_weaken;
    intros ??; apply H; first [by eauto | by symmetry; eauto].
Qed.

Lemma ax_and (P Q R : stack → mem → focus → Prop)
  `{P_nf : PropHolds (∀ mf l m φ,
     P (get_stack l) m φ → nf (cstep_in_ctx δ l) (State l φ (m ∪ mf)))}
  `{Q_nf : PropHolds (∀ mf l m φ,
     Q (get_stack l) m φ → nf (cstep_in_ctx δ l) (State l φ (m ∪ mf)))}
    l n k φ m :
  (∀ ρ m φ, P ρ m φ → Q ρ m φ → R ρ m φ) →
  ax P l n k φ m →
  ax Q l n k φ m →
  ax R l n k φ m.
Proof.
  intros HPQ. revert k φ m.
  induction n as [|n]; [constructor |].
  intros k φ m Hax1 Hax2.
  inversion Hax1 as [| |???? Hred1 Hstep1];
    inversion Hax2 as [| |???? Hred2 Hstep2]; subst.
  * by apply ax_done, HPQ.
  * exfalso. by eapply P_nf, (Hred2 ∅), mem_disjoint_empty_r.
  * exfalso. by eapply Q_nf, (Hred1 ∅), mem_disjoint_empty_r.
  * apply ax_further; [done |]. intros mf S' ??.
    specialize (Hstep1 mf S'). specialize (Hstep2 mf S').
    feed destruct Hstep1; feed inversion Hstep2; subst; trivial.
    constructor; auto. simplify_mem_equality; eauto.
Qed.

(** ** Function calls *)
(** We consider two kinds of specifications of functions: one for functions
that are proven to be pure, and one for non-pure functions. The specification
of a pure function consists solely of its denotation [F]. Its intuitive meaning
is that when called with arguments [vs], then if it returns a value [v], we
have [F vs = Some v]. *)

(** Specifications on non-pure functions consist of the function's pre- and
postcondition. These should be stack independent as local variables may have a
different meaning at the calling function and the callee. To relate the
postcondition to the precondition, we allow quantification over an arbitrary
type [c]. This approach to specifications of non-pure functions is similar
to (Appel/Blazy, 2007). However, contrary to them, we also allow the
postcondition to refer to the function's arguments. *)
Inductive fassert :=
  | FPure: purefun → fassert
  | FImpure (c : Type)
      (fpre : c → list val → assert)
      (fpost : c → list val → vassert) :
    (∀ c vs, StackIndep (fpre c vs)) →
    (∀ c vs v, StackIndep (fpost c vs v)) →
    fassert.
Notation fassert_env := (funmap fassert).

Definition fcommon (Pf : fassert) : Type :=
  match Pf with
  | FImpure c _ _ _ _ => c
  | FPure _ => unit
  end.
Definition fpre (Pf : fassert) : fcommon Pf → list val → assert :=
  match Pf return fcommon Pf → list val → assert with
  | FImpure _ pre _ _ _ => pre
  | FPure _ => λ _ _, emp%A
  end.
Definition fpost (Pf : fassert) : fcommon Pf → list val → vassert :=
  match Pf return fcommon Pf → list val → vassert with
  | FImpure _ _ post _ _ => post
  | FPure F => λ _ vs v, (emp ∧ ⌜ F vs = Some v ⌝)%A
  end.

Global Instance fpre_stack_indep Pf c vs : StackIndep (fpre Pf c vs).
Proof. destruct Pf; apply _. Qed.
Global Instance fpost_stack_indep Pf c vs v : StackIndep (fpost Pf c vs v).
Proof. destruct Pf; apply _. Qed.

(** The operation [fpure] extracts an environment of pure functions from the
an environment of function specifications. *)
Definition fpure: fassert_env → purefuns :=
  merge (λ _ mPf,
    match mPf with
    | Some (FPure F) => Some F
    | _ => None
    end) (@empty purefuns _).

Lemma lookup_fpure_Some Δ f F :
  fpure Δ !! f = Some F ↔ Δ !! f = Some (FPure F).
Proof.
  unfold fpure. rewrite lookup_merge by done.
  destruct (Δ !! f) as [[]|]; naive_solver.
Qed.
Lemma lookup_fpure_None Δ f :
  fpure Δ !! f = None ↔
    Δ !! f = None ∨
    ∃ c pre post Hpre Hpost, Δ !! f = Some (FImpure c pre post Hpre Hpost).
Proof.
  unfold fpure. rewrite lookup_merge by done.
  destruct (Δ !! f) as [[]|]; naive_solver.
Qed.

Lemma fpure_empty : fpure ∅ = ∅.
Proof.
  apply map_empty. intros f. unfold fpure.
  by rewrite lookup_merge, lookup_empty.
Qed.
Lemma fassert_disjoint_union Δ1 Δ2 :
  Δ1 ⊥ Δ2 → fpure Δ1 ⊥ fpure Δ2.
Proof. intros ????. rewrite !lookup_fpure_Some. eauto. Qed.

Lemma fpure_union Δ1 Δ2 :
  Δ1 ⊥ Δ2 →
  fpure (Δ1 ∪ Δ2) = fpure Δ1 ∪ fpure Δ2.
Proof.
  intros. apply map_eq. intros f. apply option_eq. intros F.
  by rewrite lookup_fpure_Some, !lookup_union_Some,
    !lookup_fpure_Some by auto using fassert_disjoint_union.
Qed.

Definition fassert_fun_indep (fs : funset) (Pf : fassert) : Prop :=
  match Pf with
  | FImpure _ pre post _ _ =>
      (∀ c vs, FunIndep fs (pre c vs)) ∧
      (∀ c vs v, FunIndep fs (post c vs v))
  | FPure _ => True
  end.
Lemma fpre_fun_indep fs Pf c vs :
  fassert_fun_indep fs Pf →
  FunIndep fs (fpre Pf c vs).
Proof. destruct Pf; simpl. apply _. by intros [??]. Qed.
Lemma fpost_fun_indep fs Pf c vs v :
  fassert_fun_indep fs Pf →
  FunIndep fs (fpost Pf c vs v).
Proof. destruct Pf; simpl. apply _. by intros [??]. Qed.

Definition fassert_env_fun_indep (fs : funset) : fassert_env → Prop :=
  map_forall (λ _, fassert_fun_indep fs).

Lemma lookup_fpre_fun_indep Δ fs f Pf c vs :
  fassert_env_fun_indep fs Δ →
  Δ !! f = Some Pf →
  FunIndep fs (fpre Pf c vs).
Proof. intros HΔ ?. eapply fpre_fun_indep, HΔ; eauto. Qed.
Lemma lookup_fpost_fun_indep Δ fs f Pf c vs v :
  fassert_env_fun_indep fs Δ →
  Δ !! f = Some Pf →
  FunIndep fs (fpost Pf c vs v).
Proof. intros HΔ ?. eapply fpost_fun_indep, HΔ; eauto. Qed.

(** The predicate [ax_funs n Δ] states that the functions in [Δ] behave
accordingly. Intuitively this means that if a [Call f vs] with [vs] satisfying
the precondition of [f] terminates, then the result is a [Return v] with [v]
satisfying the postcondition of [f]. *)
Inductive ax_fun_P (δp : purefuns) (Pf : fassert) (c : fcommon Pf) (vs : list val)
    (ρ : stack) (m : mem) : focus → Prop :=
  | make_ax_fun_P v :
     locks m = ∅ →
     assert_holds δp (fpost Pf c vs v) ρ m →
     ax_fun_P δp Pf c vs ρ m (Return v).
Definition ax_funs (n : nat) (Δ : fassert_env) : Prop :=
  ∀ f Pf c vs m k,
    Δ !! f = Some Pf →
    locks m = ∅ →
    assert_holds (fpure Δ) (fpre Pf c vs) (get_stack k) m →
    ax (ax_fun_P (fpure Δ) Pf c vs) k n k (Call f vs) m.

Instance: PropHolds (∀ mf l m φ,
  ax_fun_P δp Pf c vs (get_stack l) m φ →
  nf (cstep_in_ctx δ l) (State l φ (m ∪ mf))).
Proof. destruct 1. intros [? p]. inv_cstep p. Qed.
Instance: PropHolds (∀ ρ m, ¬ax_fun_P δp Pf c vs ρ m Undef).
Proof. inversion 1. Qed.

Lemma ax_funs_weaken n1 n2 Δ :
  ax_funs n2 Δ → n1 ≤ n2 → ax_funs n1 Δ.
Proof. unfold ax_funs. eauto using ax_le. Qed.

Lemma ax_funs_empty n : ax_funs n ∅.
Proof. repeat intro. simplify_map_equality. Qed.
Lemma ax_funs_S n Δ : ax_funs (S n) Δ → ax_funs n Δ.
Proof. eauto using ax_funs_weaken with arith. Qed.
Lemma ax_funs_pred n Δ : ax_funs n Δ → ax_funs (pred n) Δ.
Proof. eauto using ax_funs_weaken with arith. Qed.
Hint Resolve ax_funs_empty ax_funs_S ax_funs_pred : ax.

Lemma ax_fun_P_union_l_pure δp Δ f Pf c vs :
  fassert_env_fun_indep (dom funset δp) Δ →
  Δ !! f = Some Pf →
  ((=) ==> (=) ==> (=) ==> iff)%signature
    (ax_fun_P (δp ∪ fpure Δ) Pf c vs) (ax_fun_P (fpure Δ) Pf c vs).
Proof.
  intros ?? ? ρ ? ? m ? ? φ ?; subst.
  split; destruct 1; constructor; eauto.
  * rewrite <-fun_indep_union_l; eauto using lookup_fpost_fun_indep.
  * rewrite fun_indep_union_l; eauto using lookup_fpost_fun_indep.
Qed.

(** ** Directed assertions *)
(** The statement judgment will be of the shape [Δ \ Pd ⊨ₚ s] where [Pd] is
a function from directions to assertions taking the pre- and post, returning,
and jumping condition together. We generalize this idea slightly, and define
the type [directed A] as functions [direction → A]. *)
Definition directed_pack {A} (P : A) (Q : A) (R : val → A)
  (J : label → A) : direction → A := direction_rect (λ _, A) P Q R J.
Global Instance directed_pack_proper `{!@Equivalence A R} : Proper
  (R ==> R ==> pointwise_relation _ R ==>
    pointwise_relation _ R ==> pointwise_relation _ R)
  (@directed_pack A).
Proof. intros ???????????? []; subst; firstorder. Qed.

(** This hideous definition of [fmap] makes [f <$> directed_pack P Q R J]
convertable with [directed_pack (f P) (f Q) (f ∘ R) (f ∘ J)]. *)
Instance directed_fmap: FMap (λ A, direction → A) := λ A B f Pd d,
  match d with
  | ↘ => f (Pd ↘)
  | ↗ => f (Pd ↗)
  | ⇈ v => f (Pd (⇈ v))
  | ↷ l => f (Pd (↷ l))
  end.
Lemma directed_fmap_spec {A B} (f : A → B) (P : direction → A) d :
  (f <$> P) d = f (P d).
Proof. by destruct d. Qed.

Notation dassert := (direction → assert).
Notation dassert_pack P Q R J := (@directed_pack assert P%A Q%A R%A J%A).
Definition dassert_pack_top (P : assert) (R : vassert) :
  dassert := dassert_pack P (R VVoid) R (λ _, False%A).

(** ** The Hoare judgment for statements *)
(** Now the interpretation of the statement Hoare judgment is just taking all
of the previously defined notions together. We require both the program and
the memory to contain no locks at the start. Also, we require all locks to be
released in the end, as each statement that contains an expression always has
a sequence point in the end. *)
Inductive ax_stmt_P (s : stmt) (δp : purefuns) (Pd : dassert)
    (ρ : stack) (m : mem) : focus → Prop :=
  make_ax_stmt_P d :
    up d s →
    locks m = ∅ →
    assert_holds δp (Pd d) ρ m →
    ax_stmt_P s δp Pd ρ m (Stmt d s).
Definition ax_stmt_packed (Δ : fassert_env) (Pd : dassert) (s : stmt) : Prop :=
  ∀ n k d m,
    ax_funs n Δ →
    down d s →
    locks s = ∅ →
    locks m = ∅ →
    assert_holds (fpure Δ) (Pd d) (get_stack k) m →
    ax (ax_stmt_P s (fpure Δ) Pd) k n k (Stmt d s) m.
Notation "Δ \ P ⊨ₚ s" :=
  (ax_stmt_packed Δ P%A s%S)
  (at level 74, P at next level, format "Δ  \  P  ⊨ₚ  '[' s ']'").

Instance: PropHolds (∀ mf l m φ,
  ax_stmt_P s δp Pd (get_stack l) m φ →
  nf (cstep_in_ctx δ l) (State l φ (m ∪ mf))).
Proof. destruct 1. intros [? p]. inv_cstep p. Qed.

Instance ax_stmt_P_proper: Proper
  (pointwise_relation _ (≡@{δp}) ==> (=) ==> (=) ==> (=) ==> iff)
  (ax_stmt_P s δp).
Proof.
  intros ???? E. repeat intro; subst.
  split; destruct 1; constructor; eauto; eapply E; eauto.
Qed.

Global Instance ax_stmt_packed_proper: Proper
  (pointwise_relation _ (≡@{fpure Δ}) ==> (=) ==> iff)
  (ax_stmt_packed Δ).
Proof.
  intros Δ Pd Qd E1 ???; subst. unfold ax_stmt_packed.
  by setoid_rewrite E1.
Qed.

Definition ax_stmt Δ R J P s Q := Δ \ dassert_pack P Q R J ⊨ₚ s.
Definition ax_stmt_top Δ P s Q := Δ \ dassert_pack_top P Q ⊨ₚ s.

(* The level is just below logical negation (whose level is 75). *)
Notation "Δ \ R \ J ⊨ₛ {{ P }} s {{ Q }}" :=
  (ax_stmt Δ R%A J%A P%A s%S Q%A)
  (at level 74, J at next level, R at next level,
   format "Δ  \  R  \  J  ⊨ₛ  '[' {{  P  }} '/'  s  '/' {{  Q  }} ']'").
Notation "Δ ⊨ₜ {{ P }} s {{ Q }}" :=
  (ax_stmt_top Δ P%A s%S Q%A)
  (at level 74, format "Δ  ⊨ₜ  '[' {{  P  }} '/'  s  '/' {{  Q  }} ']'").

Lemma ax_stmt_top_unfold Δ P s Q :
  Δ ⊨ₜ {{ P }} s {{ Q }} ↔ Δ \ Q \ (λ _, False) ⊨ₛ {{ P }} s {{ Q voidc%V }}.
Proof. done. Qed.

Global Instance ax_stmt_proper: Proper
  (pointwise_relation _ (≡@{fpure Δ}) ==> pointwise_relation _ (≡@{fpure Δ}) ==>
     (≡@{fpure Δ}) ==> (=) ==> (≡@{fpure Δ}) ==> iff)
  (ax_stmt Δ).
Proof.
  intros ??? E1 ?? E2 ?? E3 ??? ?? E4; subst.
  unfold ax_stmt. by rewrite E1, E2, E3, E4.
Qed.
Global Instance ax_stmt_top_proper: Proper
  ((≡@{fpure Δ}) ==> (=) ==> pointwise_relation _ (≡@{fpure Δ}) ==> iff)
  (ax_stmt_top Δ).
Proof.
  intros ??? E1 ??? ?? E2; subst.
  unfold ax_stmt_top, dassert_pack_top. by rewrite E1, E2.
Qed.

Lemma ax_stmt_P_union_l_pure δp Δ s Pd :
  (∀ d, FunIndep (dom funset δp) (Pd d)) →
  fassert_env_fun_indep (dom funset δp) Δ →
  ((=) ==> (=) ==> (=) ==> iff)%signature
    (ax_stmt_P s (δp ∪ fpure Δ) Pd) (ax_stmt_P s (fpure Δ) Pd).
Proof.
  intros ??? ρ ? ? m ? ? φ ?; subst.
  split; destruct 1; constructor; eauto.
  * rewrite <-fun_indep_union_l; eauto.
  * rewrite fun_indep_union_l; eauto.
Qed.

(** ** The Hoare judgment for expressions *)
(** The interpretation of the expression judgment is defined similarly as the
interpretation of the judgment for statements. At the start, we require both
the expression and the memory to be lock free. In the end, the locks in the
memory should exactly match the annotated locations in the final expression
that remain to be unlocked. The latter is important, as an unlock operation at
a sequence point thereby corresponds to unlocking everything. *)
Inductive ax_expr_P (δp : purefuns) (Q : val → assert)
    (ρ : stack) (m : mem) : focus → Prop :=
  make_ax_expr_P v Ω :
    locks m = Ω →
    assert_holds δp (Q v) ρ m →
    ax_expr_P δp Q ρ m (Expr (valc@{Ω} v)).
Definition ax_expr (Δ : fassert_env) (P : assert)
    (e : expr) (Q : val → assert) : Prop :=
  ∀ n k m,
    ax_funs n Δ →
    locks e = ∅ →
    locks m = ∅ →
    assert_holds (fpure Δ) P (get_stack k) m →
    ax (ax_expr_P (fpure Δ) Q) k n k (Expr e) m.
Notation "Δ ⊨ₑ {{ P }} e {{ Q }}" :=
  (ax_expr Δ P%A e%E Q%A)
  (at level 74, format "Δ  ⊨ₑ  '[' {{  P  }} '/'  e  '/' {{  Q  }} ']'").

Instance: PropHolds (∀ mf l m φ,
  ax_expr_P δp Q (get_stack l) m φ →
  nf (cstep_in_ctx δ l) (State l φ (m ∪ mf))).
Proof. destruct 1. apply cnf_val. Qed.

Instance ax_expr_P_impl: Proper
  (pointwise_relation _ (⊆@{δp}) ==> (=) ==> (=) ==> (=) ==> impl)
  (ax_expr_P δp).
Proof.
  intros ??? E ??? ??? ???.
  destruct 1; subst; constructor; eauto; eapply E; eauto.
Qed.
Instance ax_expr_P_proper: Proper
  (pointwise_relation _ (≡@{δp}) ==> (=) ==> (=) ==> (=) ==> iff)
  (ax_expr_P δp).
Proof.
  intros ??? E. repeat intro; subst.
  split; destruct 1; constructor; eauto; eapply E; eauto.
Qed.

Lemma ax_expr_P_is_value P δp ρ m e :
  ax_expr_P δp P ρ m (Expr e) →
  is_value e.
Proof. by inversion 1. Qed.

Lemma ax_expr_val P n δp k v Ω m :
  ax (ax_expr_P δp P) k (S n) k (Expr (valc@{Ω} v)) m →
  assert_holds δp (P v) (get_stack k) m.
Proof.
  inversion 1 as [|??? [????]|???? Hred]; subst.
  * done.
  * destruct (cnf_val δ k Ω v (m ∪ ∅)).
    apply Hred. apply mem_disjoint_empty_r.
Qed.

Lemma ax_expr_val_locks P n δp k v Ω m :
  ax (ax_expr_P δp P) k (S n) k (Expr (valc@{Ω} v)) m →
  locks m = Ω.
Proof.
  inversion 1 as [|??? [????]|???? Hred]; subst.
  * done.
  * destruct (cnf_val δ k Ω v (m ∪ ∅)).
    apply Hred. apply mem_disjoint_empty_r.
Qed.

Global Instance ax_expr_proper: Proper
  ((≡@{fpure Δ}) ==> (=) ==> pointwise_relation _ (≡@{fpure Δ}) ==> iff)
  (ax_expr Δ).
Proof.
  intros Δ P Q E1 ??? Pf Qf E2; subst. unfold ax_expr.
  by setoid_rewrite E1; setoid_rewrite E2.
Qed.

Lemma ax_expr_P_union_l_pure δp Δ Q :
  (∀ v, FunIndep (dom funset δp) (Q v)) →
  fassert_env_fun_indep (dom funset δp) Δ →
  ((=) ==> (=) ==> (=) ==> iff)%signature
    (ax_expr_P (δp ∪ fpure Δ) Q) (ax_expr_P (fpure Δ) Q).
Proof.
  intros ??? ρ ? ? m ? ? φ ?; subst.
  split; destruct 1; constructor; eauto.
  * rewrite <-fun_indep_union_l; eauto.
  * rewrite fun_indep_union_l; eauto.
Qed.

(** The lemma [ax_expr_compose] is used to prove the structural Hoare rules for
expressions. It is proven by chasing all (interleaved) reduction paths for the
compound expression. This is done step-wise by distinguishing the following
cases:

- All subexpressions are values.
- Some subexpression contains a redex that is not a function call.
- Some subexpression contains a redex that is a function call. In this case we
  use the lemma [ax_call_compose]. *)
Lemma ax_call_compose P Q (E : ectx) E' n φ l k m1 m2 :
  locks E' ⊆ locks E ∪ locks m2 →
  m1 ⊥ m2 →
  ax P l n (k ++ [CFun E] ++ l) φ m1 →
  (∀ n' m1' e',
    n' ≤ n →
    m1' ⊥ m2 →
    locks (subst E e') ⊆ locks m1' →
    ax P l n' l (Expr (subst E e')) m1' →
    ax Q l n' l (Expr (subst E' e')) (m1' ∪ m2)) →
  ax Q l n (k ++ [CFun E'] ++ l) φ (m1 ∪ m2).
Proof.
  intros HE. revert m1 φ k. induction n as [|n IH]; [intros; apply ax_O |].

  intros m1 φ k ? Hax Hnext.
  inversion Hax as [| | ???? Hred Hstep]; simplify_list_equality.
  apply ax_further.
  { intros mf ?. rewrite <-(associative_eq (∪)).
    destruct (Hred (m2 ∪ mf)) as [S' p].
    { by apply mem_disjoint_union_move_l. }
    apply (cstep_call_inv _ _ E E' _ _ _ _ _ p);
      intros; subst; eexists; eauto. }

  intros mf S' ? p. rewrite <-(associative_eq (∪)) in p.
  apply (cstep_call_inv _ _ _ E _ _ _ _ _ p).
  * intros k' φ' m' p'.
    feed inversion (Hstep (m2 ∪ mf)
      (State (k' ++ [CFun E] ++ l) φ' m'));
      subst; trivial.
    { by apply mem_disjoint_union_move_l. }
    rewrite (associative_eq (∪)). decompose_mem_disjoint.
    constructor; try done.
    { rewrite mem_locks_union by done. esolve_elem_of. }
    by apply IH; auto with arith.
  * intros v ? ? p'. subst.
    feed inversion (Hstep (m2 ∪ mf)
      (State l (Expr (subst E (valc v)%E))
      (m1 ∪ (m2 ∪ mf)))) as [???]; subst; trivial.
    { by apply mem_disjoint_union_move_l. }
    rewrite (associative_eq (∪)). decompose_mem_disjoint.
    constructor; try done.
    { rewrite mem_locks_union by done. simpl in *.
      rewrite ectx_subst_locks in H9 |- *. esolve_elem_of. (* fixme *) }
    by apply Hnext; auto with arith.
Qed.

Lemma ax_expr_compose n {vn} δp (Ps : vec vassert vn) (Q : vassert)
    (E : ectx_full vn) (es : vec expr vn) (l : ctx) (ms : vec mem vn) :
  locks E = ∅ →
  list_disjoint ms →
  (∀ i, locks (es !!! i) ⊆ locks (ms !!! i)) →
  (∀ i, ax (ax_expr_P δp (Ps !!! i)) l n l (Expr (es !!! i)) (ms !!! i)) →
  (∀ (Ωs : vec _ vn) (vs : vec val vn) (ms' : vec mem vn),
    list_disjoint ms' →
    (∀ i, locks (ms' !!! i) = Ωs !!! i) →
    (∀ i, assert_holds δp ((Ps !!! i) (vs !!! i))
      (get_stack l) (ms' !!! i)) →
    ax (ax_expr_P δp Q) l n l
      (Expr (depsubst E (vzip_with EVal Ωs vs)%E)) (⋃ ms')) →
  ax (ax_expr_P δp Q) l n l (Expr (depsubst E es)) (⋃ ms).
Proof.
  intros HE. revert es ms.
  induction n as [[|n] IH] using lt_wf_ind; [intros; apply ax_O |].

  intros es ms ? Hes Hax1 Hax2.
  destruct (expr_vec_values es) as [(Ωs & vs & ?) | [i Hi]]; subst.
  { apply Hax2.
    + done.
    + intros i. specialize (Hax1 i). rewrite vlookup_zip_with in Hax1.
      eauto using ax_expr_val_locks.
    + intros i. specialize (Hax1 i). rewrite vlookup_zip_with in Hax1.
      eauto using ax_expr_val. }

  apply ax_further.
  { intros mf ?.
    rewrite (ectx_full_to_item_correct _ _ i).
    apply (cred_ectx _ [_]).
    rewrite <-(mem_union_delete_vec ms i), <-(associative_eq (∪)) by done.
    apply (ax_red (ax_expr_P δp (Ps !!! i)) n).
    + apply mem_disjoint_union_move_l.
      - by apply mem_list_disjoint_delete_vec_r.
      - by rewrite mem_union_delete_vec.
    + done.
    + contradict Hi. eauto using ax_expr_P_is_value. }

  intros mf S' ? p.
  apply (cstep_expr_depsubst_inv _ _ _ _ _ _ _ p); clear p.
  * clear i Hi. intros i e' m' p'.
    feed inversion (ax_step (ax_expr_P δp (Ps !!! i))
      n l (⋃ delete (fin_to_nat i) (vec_to_list ms) ∪ mf)
      l (Expr (es !!! i)) (ms !!! i) (State l (Expr e') m'))
      as [???? m'']; subst.
    { apply mem_disjoint_union_move_l.
      + by apply mem_list_disjoint_delete_vec_r.
      + by rewrite mem_union_delete_vec. }
    { done. }
    { by rewrite (associative_eq (∪)), mem_union_delete_vec. }

    rewrite (associative_eq (∪)). decompose_mem_disjoint.
    rewrite <-mem_union_insert_vec by done. constructor.
    { by apply mem_disjoint_insert_vec_l. }
    { done. }
    { simpl. rewrite ectx_full_subst_locks, HE, (left_id ∅ _).
      rewrite mem_locks_union_list by eauto using mem_list_disjoint_insert_vec.
      rewrite <-!vec_to_list_map.
      apply union_list_preserving. apply Forall2_vlookup.
      intros j. destruct (decide (i = j)); subst.
      + by rewrite !vlookup_map, !vlookup_insert.
      + rewrite !vlookup_map, !vlookup_insert_ne by done. auto. }

    apply IH; auto with arith.
    + by apply mem_list_disjoint_insert_vec.
    + intros j. destruct (decide (i = j)); subst.
      - by rewrite !vlookup_insert.
      - rewrite !vlookup_insert_ne by done. auto.
    + intros j. destruct (decide (i = j)); subst.
      - by rewrite !vlookup_insert.
      - rewrite !vlookup_insert_ne by done. apply ax_S, Hax1.
    + intros ωs vs ms' ???. by apply ax_S, Hax2.
  * clear i Hi. intros i E' f Ωs vs ? HΩs p.

    assert (mem_unlock (⋃ Ωs) (⋃ ms ∪ mf) = mem_unlock (⋃ Ωs) (ms !!! i) ∪
      ⋃ delete (fin_to_nat i) (vec_to_list ms) ∪ mf) as Hms.
    { rewrite <-(associative_eq _), <-(mem_union_delete_vec ms i) by done.
      rewrite <-(associative_eq _), mem_unlock_union_l; trivial.
      + apply mem_disjoint_union_move_l;
          auto using mem_list_disjoint_delete_vec_r.
        by rewrite mem_union_delete_vec.
      + transitivity (locks (es !!! i)); [|done].
        rewrite HΩs. rewrite ectx_subst_locks. simpl.
        rewrite zip_with_fmap_fst by done. apply union_subseteq_r. }
    assert (mem_unlock (⋃ Ωs) (ms !!! i) ⊥
      ⋃ delete (fin_to_nat i) (vec_to_list ms) ∪ mf) as Hmsi.
    { apply mem_disjoint_union_move_l.
      { by apply mem_disjoint_unlock_l, mem_list_disjoint_delete_vec_r. }
      rewrite <-mem_unlock_union_l, mem_union_delete_vec.
      + by apply mem_disjoint_unlock_l.
      + done.
      + by apply mem_list_disjoint_delete_vec_r.
      + transitivity (locks (es !!! i)); [|done].
        rewrite HΩs. rewrite ectx_subst_locks. simpl.
        rewrite zip_with_fmap_fst by done. apply union_subseteq_r. }

    rewrite Hms in p |- *. rewrite <-(mem_union_delete_vec ms i) in p by done.
    constructor.
    { apply mem_disjoint_union_move_r; eauto with mem_disjoint. }
    { done. }
    { simpl. apply subseteq_empty. }

    apply ax_call_compose with (P:=ax_expr_P δp (Ps !!! i)) (k:=[]) (E:=E').
    { rewrite locks_snoc. apply union_preserving_l.
      rewrite ectx_full_to_item_locks, HE, (left_id ∅ _).
      rewrite mem_locks_union_list by
        eauto using mem_list_disjoint_sublist, sublist_delete.
      apply union_list_preserving, Forall2_fmap, Forall2_delete.
      apply Forall2_vlookup. auto. }
    { by apply mem_disjoint_unlock_l, mem_list_disjoint_delete_vec_r. }
    { feed inversion (ax_step (ax_expr_P δp (Ps !!! i)) n
        l (⋃ delete (fin_to_nat i) (vec_to_list ms) ∪ mf)
        l (Expr (es !!! i)) (ms !!! i)
        (State (CFun E' :: l) (Call f vs) (mem_unlock (⋃ Ωs) (ms !!! i) ∪
          (⋃ delete (fin_to_nat i) (vec_to_list ms) ∪ mf)))); subst; trivial.
      + apply mem_disjoint_union_move_l.
        - by apply mem_list_disjoint_delete_vec_r.
        - by rewrite mem_union_delete_vec.
      + by rewrite !(associative_eq (∪)).
      + by simplify_mem_equality. }

    intros n' m' e' ??? Hax.
    rewrite <-mem_union_insert_vec by done.
    rewrite subst_snoc, <-ectx_full_to_item_correct_alt.
    apply IH; auto with arith.
    + by apply mem_list_disjoint_insert_vec.
    + intros j. destruct (decide (i = j)); subst.
      - by rewrite !vlookup_insert.
      - rewrite !vlookup_insert_ne by done. auto.
    + intros j. destruct (decide (i = j)); subst.
      - by rewrite !vlookup_insert.
      - rewrite !vlookup_insert_ne by done.
        apply ax_le with (S n); auto with arith.
    + intros ωs' vs' ms' ???.
      apply ax_le with (S n); auto with arith.

  * intros ωs vs Hvs. destruct Hi. by rewrite Hvs, vlookup_zip_with.
  * clear i Hi. intros i p.
    destruct (ax_step_undef
      (ax_expr_P δp (Ps !!! i)) n
      l (⋃ delete (fin_to_nat i) (vec_to_list ms) ∪ mf)
      l (Expr (es !!! i)) (ms !!! i) l (⋃ ms ∪ mf)); trivial.
    + apply mem_disjoint_union_move_l.
      - by apply mem_list_disjoint_delete_vec_r.
      - by rewrite mem_union_delete_vec.
    + by rewrite (associative_eq (∪)), mem_union_delete_vec.
Qed.

(** * Partial program correctness *)
(** We prove that the interpretation of the statement Hoare judgment indeed
implies partial program correctness. *)
Lemma ax_stmt_sound_sep P Q s m mf S' :
  ∅ ⊨ₜ {{ P }} s {{ Q }} →
  locks s = ∅ →
  locks m = ∅ →
  m ⊥ mf →
  assert_holds ∅ P [] m →
  δ ⊢ₛ State [] (Stmt ↘ s) (m ∪ mf) ⇒* S' →
    (∃ m', S' = State [] (Stmt ↗ s) (m' ∪ mf) ∧
           assert_holds ∅ (Q VVoid) [] m')
  ∨ (∃ m' v, S' = State [] (Stmt (⇈ v) s) (m' ∪ mf) ∧
             assert_holds ∅ (Q v) [] m')
  ∨ red (cstep δ) S'.
Proof.
  intros Hax Hs Hm ? ? p.
  apply rtc_bsteps in p. destruct p as [n p].
  feed inversion (ax_steps
    (ax_stmt_P s ∅ (dassert_pack_top P Q))
    n 1 [] mf (Stmt ↘ s) [] m S') as [???????? Hax']; subst; try done.
  * simpl. rewrite Hs. apply subseteq_empty.
  * rewrite <-fpure_empty. apply Hax; auto with ax.
    simpl. by rewrite fpure_empty.
  * by apply (bsteps_subrel (cstep δ) _ _).
  * inversion Hax' as [|??? [d' ??]|]; subst.
    + destruct d'; naive_solver.
    + right; right. apply (red_subrel (cstep_in_ctx δ []) _ _); auto.
Qed.
Lemma ax_stmt_sound P R s m S' :
  ∅ ⊨ₜ {{ P }} s {{ R }} →
  locks s = ∅ →
  locks m = ∅ →
  assert_holds ∅ P [] m →
  δ ⊢ₛ State [] (Stmt ↘ s) m ⇒* S' →
    (∃ m', S' = State [] (Stmt ↗ s) m' ∧ assert_holds ∅ (R VVoid) [] m')
  ∨ (∃ m' v, S' = State [] (Stmt (⇈ v) s) m' ∧ assert_holds ∅ (R v) [] m')
  ∨ red (cstep δ) S'.
Proof.
  intros ???? p. rewrite <-(right_id_eq ∅ (∪) m) in p.
  destruct (ax_stmt_sound_sep P R s m ∅ S') as [[? [E ?]]|[[?[?[E ?]]]|]];
    try rewrite (right_id_eq ∅ (∪)) in E; intuition eauto with mem_disjoint.
Qed.

Lemma ax_stmt_looping_sep P s m mf :
  ∅ ⊨ₜ {{ P }} s {{ λ _, False }} →
  locks s = ∅ →
  locks m = ∅ →
  m ⊥ mf →
  assert_holds ∅ P [] m →
  looping (cstep δ) (State [] (Stmt ↘ s) (m ∪ mf)).
Proof.
  intros Hax ????. apply looping_alt. intros S' p.
  destruct (ax_stmt_sound_sep P (λ _, False)%A s m mf S')
    as [[??]|[[?[??]]|?]]; by intuition.
Qed.
Lemma ax_stmt_looping P s m :
  ∅ ⊨ₜ {{ P }} s {{ λ _, False }} →
  locks s = ∅ →
  locks m = ∅ →
  assert_holds ∅ P [] m →
  looping (cstep δ) (State [] (Stmt ↘ s) m).
Proof.
  intros. rewrite <-(right_id_eq ∅ (∪) m).
  apply ax_stmt_looping_sep with P; auto with mem_disjoint.
Qed.

(** * The Hoare rules *)
(** We prove that the Hoare rules are inhabited by the interpretation of the
Hoare judgment. *)

(** ** Logical rules *)
Lemma ax_stmt_weaken_packed Δ Pd Pd' s :
  Δ \ Pd ⊨ₚ s →
  (∀ d, down d s → Pd' d ⊆@{fpure Δ} Pd d) →
  (∀ d, up d s → Pd d ⊆@{fpure Δ} Pd' d) →
  Δ \ Pd' ⊨ₚ s.
Proof.
  intros Hax Hdown Hup n k d m ?????.
  apply ax_weaken with (ax_stmt_P s (fpure Δ) Pd).
  * intros ?? []; constructor; solve_assert.
  * by apply Hax, Hdown.
Qed.

Lemma ax_stmt_weaken_pre Δ R J P P' Q s :
  Δ \ R \ J ⊨ₛ {{ P }} s {{ Q }} →
  P' ⊆@{fpure Δ} P →
  Δ \ R \ J ⊨ₛ {{ P' }} s {{ Q }}.
Proof. intros. eapply ax_stmt_weaken_packed; intros []; solve_assert. Qed.
Lemma ax_stmt_weaken_post Δ R J P Q Q' s :
  Δ \ R \ J ⊨ₛ {{ P }} s {{ Q }} →
  Q ⊆@{fpure Δ} Q' →
  Δ \ R \ J ⊨ₛ {{ P }} s {{ Q' }}.
Proof. intros. eapply ax_stmt_weaken_packed; intros []; solve_assert. Qed.

Lemma ax_stmt_packed_right_frame Δ A Pd s :
  ax_stmt_packed Δ Pd s →
  ax_stmt_packed Δ ((λ P, P ★ A)%A <$> Pd) s.
Proof.
  intros Hax n k d m HΔ Hd ? Hm Hpre.
  rewrite directed_fmap_spec in Hpre.
  destruct Hpre as (m1&m2&?&?&?&?); simplify_equality.
  rewrite mem_locks_union in Hm by done. decompose_empty.
  apply ax_frame with (ax_stmt_P s (fpure Δ) Pd); auto.
  intros m ?? []; constructor; trivial.
  + rewrite mem_locks_union by done. by apply empty_union_L.
  + rewrite directed_fmap_spec. solve_assert.
Qed.
Lemma ax_stmt_packed_left_frame Δ A Pd s :
  ax_stmt_packed Δ Pd s →
  ax_stmt_packed Δ ((λ P, A ★ P)%A <$> Pd) s.
Proof.
  intros Hax. apply (ax_stmt_packed_right_frame _ A) in Hax.
  eapply ax_stmt_weaken_packed; [eassumption | |].
  { by intros [] ?; unfold fmap; simpl; rewrite (commutative _). }
  { by intros [] ?; unfold fmap; simpl; rewrite (commutative _). }
Qed.
Lemma ax_stmt_right_frame Δ R J A P Q s :
  Δ \ R \ J ⊨ₛ {{ P }} s {{ Q }} →
  Δ \ (λ v, R v ★ A) \ (λ l, J l ★ A) ⊨ₛ {{ P ★ A }} s {{ Q ★ A }}.
Proof. apply ax_stmt_packed_right_frame. Qed.
Lemma ax_stmt_left_frame Δ R J A P Q s :
  Δ \ R \ J ⊨ₛ {{ P }} s {{ Q }} →
  Δ \ (λ v, A ★ R v) \ (λ l, A ★ J l) ⊨ₛ {{ A ★ P }} s {{ A ★ Q }}.
Proof. apply ax_stmt_packed_left_frame. Qed.

Lemma ax_stmt_and Δ R J P Q Q' s :
  Δ \ R \ J ⊨ₛ {{ P }} s {{ Q }} →
  Δ \ R \ J ⊨ₛ {{ P }} s {{ Q' }} →
  Δ \ R \ J ⊨ₛ {{ P }} s {{ Q ∧ Q' }}.
Proof.
  intros Hax1 Hax2 n k d m ???? Hpre.
  eapply (ax_and (ax_stmt_P s (fpure Δ) _) (ax_stmt_P s (fpure Δ) _) _);
    [| apply Hax1 | apply Hax2]; trivial.
  * intros ??? [d' ???]. inversion 1; subst.
    constructor; [done|done|destruct d'; solve_assert].
  * destruct d; solve_assert.
  * destruct d; solve_assert.
Qed.

Lemma ax_stmt_or Δ R J P P' Q s :
  Δ \ R \ J ⊨ₛ {{ P }} s {{ Q }} →
  Δ \ R \ J ⊨ₛ {{ P' }} s {{ Q }} →
  Δ \ R \ J ⊨ₛ {{ P ∨ P' }} s {{ Q }}.
Proof.
  intros Hax1 Hax2 n k [] m HΔ Hd ?? Hpre; discriminate_down_up.
  * destruct Hpre.
    + apply ax_weaken with (ax_stmt_P s (fpure Δ) (dassert_pack P Q R J)); auto.
      intros ?? [[] ??]; constructor; solve_assert.
    + apply ax_weaken with (ax_stmt_P s (fpure Δ) (dassert_pack P' Q R J));auto.
      intros ?? [[] ??]; constructor; solve_assert.
  * apply ax_weaken with (ax_stmt_P s
        (fpure Δ) (dassert_pack P Q R J)); auto.
    intros ?? [[] ??]; constructor; solve_assert.
Qed.

Lemma ax_stmt_ex_pre `{!Inhabited A} Δ R J (P : A → assert) Q s :
  (∀ x, Δ \ R \ J ⊨ₛ {{ P x }} s {{ Q }}) →
  Δ \ R \ J ⊨ₛ {{ ∃ x, P x }} s {{ Q }}.
Proof.
  intros Hax n k [] m HΔ Hd ?? Hpre; discriminate_down_up.
  * destruct Hpre as [x Hpre].
    apply ax_weaken with (ax_stmt_P s (fpure Δ) (dassert_pack (P x) Q R J)).
    + intros ?? [[] ??]; constructor; solve_assert.
    + by apply Hax.
  * destruct (_ : Inhabited A) as [x].
    apply ax_weaken with (ax_stmt_P s (fpure Δ) (dassert_pack (P x) Q R J)).
    + intros ?? [[] ??]; constructor; solve_assert.
    + by apply Hax.
Qed.
Lemma ax_stmt_ex_post `{!Inhabited A} Δ R J P (Q : A → assert) s x :
  Δ \ R \ J ⊨ₛ {{ P }} s {{ Q x }} →
  Δ \ R \ J ⊨ₛ {{ P }} s {{ ∃ x, Q x }}.
Proof. intro. apply ax_stmt_weaken_post with (Q x); solve_assert. Qed.

Lemma ax_expr_weaken Δ P P' Q Q' e :
  Δ ⊨ₑ {{ P' }} e {{ Q' }} →
  P ⊆@{fpure Δ} P' →
  (∀ v, Q' v ⊆@{fpure Δ} Q v) →
  Δ ⊨ₑ {{ P }} e {{ Q }}.
Proof.
  intros Hax HP HQ n k m ????. apply ax_weaken with (ax_expr_P (fpure Δ) Q').
  * intros ?? []; constructor; solve_assert.
  * by apply Hax, HP.
Qed.
Lemma ax_expr_weaken_pre Δ P P' Q e :
  Δ ⊨ₑ {{ P' }} e {{ Q }} →
  P ⊆@{fpure Δ} P' →
  Δ ⊨ₑ {{ P }} e {{ Q }}.
Proof. intros. by eapply ax_expr_weaken; eauto. Qed.
Lemma ax_expr_weaken_post Δ P Q Q' e :
  Δ ⊨ₑ {{ P }} e {{ Q' }} →
  (∀ v, Q' v ⊆@{fpure Δ} Q v) →
  Δ ⊨ₑ {{ P }} e {{ Q }}.
Proof. intros. by eapply ax_expr_weaken; eauto. Qed.

Lemma ax_expr_right_frame Δ A P Q e :
  Δ ⊨ₑ {{ P }} e {{ λ v, Q v }} →
  Δ ⊨ₑ {{ P ★ A }} e {{ λ v, Q v ★ A }}.
Proof.
  intros Hax n k m HΔ ? Hm Hpre.
  destruct Hpre as (m1&m2&?&?&?&?); simplify_equality.
  rewrite mem_locks_union in Hm by done. decompose_empty.
  apply ax_frame with (ax_expr_P (fpure Δ) Q); auto.
  intros m ?? [v ?]. constructor.
  + rewrite mem_locks_union by done. esolve_elem_of.
  + solve_assert.
Qed.
Lemma ax_expr_left_frame Δ A P Q e :
  Δ ⊨ₑ {{ P }} e {{ λ v, Q v }} →
  Δ ⊨ₑ {{ A ★ P }} e {{ λ v, A ★ Q v }}.
Proof.
  setoid_rewrite (commutative assert_sep).
  apply ax_expr_right_frame.
Qed.

(** ** Rules for function calls *)
Lemma ax_funs_add n Δ Δ' :
  Δ' ⊥ Δ →
  fassert_env_fun_indep (dom _ (fpure Δ')) Δ →
  (∀ f Pf c vs,
    Δ' !! f = Some Pf → ∃ sf,
    δ !! f = Some sf ∧
    locks sf = ∅ ∧
    Δ' ∪ Δ ⊨ₜ {{ Π imap (λ i v, var i ↦{Writable} valc v) vs ★ fpre Pf c vs }}
     sf
    {{ λ v, Π imap (λ i _, var i ↦{Writable} -) vs ★ fpost Pf c vs v }}) →
  ax_funs n Δ →
  ax_funs n (Δ' ∪ Δ).
Proof.
  intros ? Hpure HaxΔ' HΔ.
  induction n as [|n IH]; [by constructor |].
  intros f Pf c vs m k Hf Hm Hpre.

  rewrite map_union_commutative, lookup_union_Some in Hf by done.
  destruct Hf as [?|?].
  { rewrite fpure_union in Hpre |- * by done.
    rewrite fun_indep_union_l in Hpre by eauto using lookup_fpre_fun_indep.
    rewrite ax_fun_P_union_l_pure by eauto. apply HΔ; try done. }

  destruct (HaxΔ' f Pf c vs) as (sf & Hsf & Hsflocks & Haxsf); trivial.

  apply ax_further.
  { intros. solve_cred. }

  intros mf S' ? p. inv_cstep p.
  simplify_map_equality.
  match goal with
  | H : alloc_params _ _ _ _ _ |- _ =>
    apply alloc_params_alloc_list in H; destruct H as [? [Hfree ?]]; subst
  end.

  pose proof (is_free_list_nodup _ _ Hfree).
  rewrite is_free_list_union in Hfree. destruct Hfree.
  rewrite mem_alloc_list_union_l by (by rewrite zip_fst).

  constructor.
  { apply mem_disjoint_alloc_list_l. by rewrite zip_fst. done. }
  { done. }
  { esolve_elem_of. }

  eapply ax_compose_cons; [| clear dependent m mf S' f].
  { eapply Haxsf; eauto.
    * by apply IH, ax_funs_S.
    * rewrite mem_locks_alloc_list, Hm; by rewrite ?zip_fst.
    * simpl. eauto using assert_alloc_params_alt. }

  intros m ? [d ?? Hpost]. apply ax_further_pred.
  { intros. solve_cred. }
  intros mf S' ? p.
  destruct d; discriminate_down_up; inv_cstep p.
  * simpl in Hpost. apply assert_free_params in Hpost;
      eauto using Writable_fragment. destruct Hpost.
    rewrite mem_delete_list_union, (mem_delete_list_free mf)
      by eauto using is_free_list_fragment_l, Writable_fragment.
    constructor; try (by auto with mem_disjoint); [esolve_elem_of |].
    apply ax_done.
    constructor. by apply mem_locks_delete_list_empty. solve_assert.
  * simpl in Hpost; apply assert_free_params in Hpost;
      eauto using Writable_fragment. destruct Hpost.
    rewrite mem_delete_list_union, (mem_delete_list_free mf)
      by eauto using is_free_list_fragment_l, Writable_fragment.
    constructor; try (by auto with mem_disjoint); [esolve_elem_of |].
    apply ax_done.
    constructor. by apply mem_locks_delete_list_empty. solve_assert.
Qed.

Lemma ax_stmt_funs_add Δ Δ' Pd s :
  Δ' ⊥ Δ →
  fassert_env_fun_indep (dom _ (fpure Δ')) Δ →
  (∀ d, FunIndep (dom _ (fpure Δ')) (Pd d)) →
  (∀ f Pf c vs,
    Δ' !! f = Some Pf → ∃ sf,
    δ !! f = Some sf ∧
    locks sf = ∅ ∧
    Δ' ∪ Δ ⊨ₜ {{ Π imap (λ i v, var i ↦{Writable} valc v) vs ★ fpre Pf c vs }}
     sf
    {{ λ v, Π imap (λ i _, var i ↦{Writable} -) vs ★ fpost Pf c vs v }}) →
  Δ' ∪ Δ \ Pd ⊨ₚ s →
  Δ \ Pd ⊨ₚ s.
Proof.
  intros ???? Hax ??????.
  rewrite <-ax_stmt_P_union_l_pure with (δp:=fpure Δ') by eauto.
  rewrite <-fun_indep_union_l with (δ1:=fpure Δ') by eauto.
  rewrite <-fpure_union by done. eapply Hax; eauto using ax_funs_add.
Qed.
Lemma ax_expr_funs_add Δ Δ' P Q e :
  Δ' ⊥ Δ →
  fassert_env_fun_indep (dom _ (fpure Δ')) Δ →
  FunIndep (dom _ (fpure Δ')) P →
  (∀ v, FunIndep (dom _ (fpure Δ')) (Q v)) →
  (∀ f Pf c vs,
    Δ' !! f = Some Pf → ∃ sf,
    δ !! f = Some sf ∧
    locks sf = ∅ ∧
    Δ' ∪ Δ ⊨ₜ {{ Π imap (λ i v, var i ↦{Writable} valc v) vs ★ fpre Pf c vs }}
     sf
    {{ λ v, Π imap (λ i _, var i ↦{Writable} -) vs ★ fpost Pf c vs v }}) →
  Δ' ∪ Δ ⊨ₑ {{ P }} e {{ Q }} →
  Δ ⊨ₑ {{ P }} e {{ Q }}.
Proof.
  intros ????? Hax ??????.
  rewrite <-ax_expr_P_union_l_pure with (δp:=fpure Δ') by eauto.
  rewrite <-fun_indep_union_l with (δ1:=fpure Δ') by eauto.
  rewrite <-fpure_union by done. eapply Hax; eauto using ax_funs_add.
Qed.

Lemma ax_call Δ f Pf (c : fcommon Pf) {vn} (Ps : vec assert vn)
    (es : vec expr vn) (Qs : vec vassert vn) (Q : list val → assert) :
  Δ !! f = Some Pf →
  (∀ vs, (Π vzip_with ($) Qs vs)%A ⊆@{fpure Δ} (fpre Pf c vs ★ Q vs)%A) →
  (∀ i, Δ ⊨ₑ {{ Ps !!! i }} es !!! i {{ λ v, (Qs !!! i) v ▷ }}) →
  Δ ⊨ₑ {{ Π Ps }} call f @ es {{ λ v, ∃ vs, fpost Pf c vs v ★ Q vs }}.
Proof.
  intros Hf HPf Haxs n k m HΔ Hes Hm Hpre. simpl in Hes.

  apply assert_sep_list_alt_vec in Hpre.
  destruct Hpre as (ms &?&?&?); subst.

  rewrite empty_union_list_L, Forall_fmap, Forall_vlookup in Hes.
  simpl in Hes. rewrite mem_locks_union_list, empty_union_list_L,
    Forall_fmap, Forall_vlookup in Hm by done. simpl in Hm.

  apply (ax_expr_compose n (fpure Δ) (vmap (assert_unlock ∘) Qs) _
    (DCCall f) es k ms); trivial.
  { esolve_elem_of. }
  { intros i. rewrite vlookup_map. by apply Haxs. }

  clear dependent ms es. intros Ωs vs ms ? Hms Hax.
  assert (⋃ Ωs = locks (⋃ ms)) as HΩs.
  { rewrite mem_locks_union_list, <-vec_to_list_map by done.
    f_equal; f_equal. apply vec_eq. intros i. by rewrite vlookup_map. }
  destruct (HPf vs (get_stack k) (mem_unlock (⋃ Ωs) (⋃ ms)))
    as (m1 & m2 & Hm12 & ? & HPf' & HQ); clear HPf.
  { rewrite HΩs, mem_unlock_all_union_list by done.
    apply assert_sep_list_alt_2.
    { by apply mem_list_disjoint_unlock_all. }
    rewrite <-vec_to_list_map. apply Forall2_vlookup. intros i.
    rewrite vlookup_map, vlookup_zip_with.
    specialize (Hax i). rewrite vlookup_map in Hax. auto. }
  assert (locks m1 ∪ locks m2 = ∅).
  { by rewrite <-mem_locks_union, Hm12, HΩs, mem_locks_unlock_all. }
  decompose_empty.

  simpl. rewrite vec_to_list_zip_with.
  pose proof (vec_to_list_same_length Ωs vs).
  apply ax_further_pred.
  { intros. solve_cred. }

  intros mf S' ? p.
  apply (cstep_expr_call_inv _ _ _ _ _ _ _ _ p); clear p.
  * done.
  * rewrite mem_unlock_union_l by solve_elem_of.
    constructor; try (by auto with mem_disjoint); [solve_elem_of|].
    rewrite <-Hm12.
    apply ax_frame with (ax_expr_P (fpure Δ) (fpost Pf c vs)); auto.
    { clear dependent m1 ms mf S'.
      intros m1 φ ? [v ?? Hpost]. constructor.
      { rewrite mem_locks_union; esolve_elem_of. }
      exists vs. solve_assert. }

    apply ax_compose_cons with (ax_fun_P (fpure Δ) Pf c vs);
      [|clear dependent ms mf S'].
    { apply ax_pred, HΔ; try done.
      by apply (stack_indep _ (get_stack k)). }

    intros m' φ' [v ? Hpost].
    apply (stack_indep _ _ (get_stack k)) in Hpost.
    apply ax_further_pred.
    { intros. solve_cred. }

    intros mf S' ? p. inv_cstep p. constructor; try done.
    + esolve_elem_of.
    + apply ax_done; constructor; solve_assert.
  * intros. exfalso. eauto with cstep.
Qed.

(** ** Rules for expressions *)
Lemma ax_expr_base Δ e :
  Δ ⊨ₑ {{ ∃ v, e ⇓ v }} e {{ λ v, e ⇓ v }}.
Proof.
  intros n k m HΔ He Hm [v Heval]. unfold_assert in *.
  revert e He Heval.
  cut (∀ e e',
    locks e = ∅ →
    ⟦ e ⟧ (fpure Δ) (get_stack k) m = Some v →
    ⟦ e' ⟧ (fpure Δ) (get_stack k) m = Some v →
    ax (ax_expr_P (fpure Δ) (λ v, (e' ⇓ v)%A)) k n k (Expr e) m).
  { intros help ???. by apply help. }

  induction n as [|n IH]; [by constructor |].
  intros e e' He Heval Heval'.
  destruct (decide (is_value e)) as [Hval | Hval].
  { inversion Hval; subst. simpl in He. subst.
    apply ax_done. constructor; solve_assert. }

  apply ax_further.
  { intros. apply cred_expr_eval with (fpure Δ) v;
      eauto using expr_eval_weaken_mem, mem_union_subseteq_l. }

  intros mf S' ? [p Hk]. revert Hk. pattern S'.
  apply (cstep_focus_inv _ _ _ _ p); clear p;
    try solve [simpl; intros; simplify_suffix_of].
  * intros E e1 e2 m2 ? p _. subst.
    apply expr_eval_subst_inv in Heval.
    destruct Heval as [w [Heval ?]].
    edestruct ehstep_expr_eval_inv; eauto using mem_union_subseteq_l.
    erewrite ectx_subst_locks, ehstep_pure_locks,
      <-ectx_subst_locks in He by eauto using expr_eval_is_pure.
    subst. constructor; try done; [esolve_elem_of |].
    apply IH; auto with ax.
    by rewrite (subst_preserves_expr_eval _ _ _ _ _ (valc w)).
  * intros E f Ωs vs ?? _. subst.
    rewrite ectx_subst_locks in He. simpl in He.
    rewrite zip_with_fmap_fst in He by done.
    rewrite empty_union_L in He. destruct He as [HE HΩs].

    apply expr_eval_subst_inv in Heval.
    destruct Heval as [w [Heval ?]]. simpl in Heval.
    destruct (fpure Δ !! f) as [F|] eqn:Hf; simpl in Heval; [|done].
    apply lookup_fpure_Some in Hf.
    rewrite mapM_expr_eval_val in Heval by done. simpl in Heval.

    rewrite HΩs, mem_unlock_empty_locks. constructor; try done.
    { solve_elem_of. }

    apply ax_compose_cons with (λ _ m' φ, m' = m ∧ φ = Return w).
    { rewrite <-(left_id ∅ (∪) m).
      apply ax_frame with (ax_fun_P (fpure Δ) (FPure F) () vs).
      + intros ??? [?? [??]]. unfold_assert in *. subst.
        rewrite (left_id ∅ _). intuition congruence.
      + by apply ax_S, HΔ; rewrite ?mem_locks_empty.
      + apply mem_disjoint_empty_l. }

    intros ?? [??]; subst. apply ax_S, ax_further.
    { intros. solve_cred. }

    clear dependent mf S'.
    intros mf S' ? p. inv_cstep p. constructor; try done.
    { simpl. rewrite ectx_subst_locks. esolve_elem_of. }

    apply IH; auto with ax.
    rewrite ectx_subst_locks. esolve_elem_of.
  * intros. subst. exfalso. eauto using
      ehsafe_expr_eval_subst, expr_eval_weaken_mem, mem_union_subseteq_l.
Qed.

Lemma ax_assign Δ γ el Pl Ql er Pr Qr R :
  Write ⊆ perm_kind γ →
  Δ ⊨ₑ {{ Pl }} el {{ Ql }} →
  Δ ⊨ₑ {{ Pr }} er {{ Qr }} →
  (∀ a v, (Ql a ★ Qr v)%A ⊆@{fpure Δ} (valc a ↦{γ} - ★ R a v)%A) →
  Δ ⊨ₑ {{ Pl ★ Pr }}
         el ::= er
       {{ λ v, ∃ a, valc a ↦{perm_lock γ} valc v ★ R a v }}.
Proof.
  intros Hγ Haxl Haxr Hassign n k ? HΔ He Hm (m1&m2&?&?&?&?); subst.
  simpl in He. rewrite mem_locks_union in Hm by done. decompose_empty.

  rewrite <-(right_id_eq ∅ (∪) m2).
  apply (ax_expr_compose n (fpure Δ)
    [# Ql;Qr] _ DCAssign [# el;er] k [# m1;m2]).
  { done. }
  { by apply mem_list_disjoint_double. }
  { intros. inv_all_vec_fin; esolve_elem_of. }
  { intros. inv_all_vec_fin; simpl; auto. }

  clear dependent m1 m2 HΔ Haxl Haxr. intros Ωs vs ms.
  inv_vec Ωs; intros Ω1 Ωs; inv_vec Ωs; intros Ω2 Ωs; inv_vec Ωs.
  inv_vec vs; intros v1 vs; inv_vec vs; intros v2 vs; inv_vec vs.
  inv_vec ms; intros m1 ms; inv_vec ms; intros m2 ms; inv_vec ms.
  simpl. intros Hdisjoint HΩs Hax. rewrite (right_id_eq ∅ (∪) m2).
  pose proof (HΩs 0%fin) as HΩl. pose proof (HΩs 1%fin) as HΩr.
  pose proof (Hax 0%fin) as Haxl. pose proof (Hax 1%fin) as Haxr.
  simpl in HΩl, HΩr, Haxl, Haxr. clear HΩs Hax.
  rewrite mem_list_disjoint_double in Hdisjoint.

  destruct (Hassign v1 v2 (get_stack k) (m1 ∪ m2))
    as (m3 & m4 & Hm3412 & Hm4 & [(a & ? & Ha & ?) HR]).
  { solve_assert. }

  rewrite expr_eval_val in Ha.
  assert (locks (m3 ∪ m4) = Ω1 ∪ Ω2) as HΩ.
  { rewrite Hm3412, mem_locks_union by done.
    clear Ha. esolve_elem_of. }
  clear Hassign HΩl HΩr.
  rewrite <-Hm3412. simplify_equality. clear dependent m1 m2.

  apply ax_further_pred.
  { intros. solve_cred. }

  intros mf' S' Hmf p. inv_cstep p.
  * inv_ehstep. simpl.
    erewrite !mem_lock_insert_union_fragment_l by eauto with simpl_mem.
    rewrite mem_lock_insert_singleton.

    pose proof Hm4 as Hm4'.
    eapply mem_disjoint_lock_insert_fragment_l in Hm4'; eauto with simpl_mem.
    rewrite mem_lock_insert_singleton in Hm4'.

    pose proof Hmf as Hmf'.
    eapply mem_disjoint_lock_insert_fragment_l in Hmf'; eauto with simpl_mem.
    erewrite !mem_lock_insert_union_fragment_l in Hmf' by eauto with simpl_mem.
    rewrite mem_lock_insert_singleton in Hmf'.

    assert (perm_kind γ ≠ Locked).
    { intros E. rewrite E in Hγ. inversion Hγ. }

    rewrite mem_locks_union, mem_locks_singleton_ne in HΩ by done.
    constructor.
    + eauto.
    + done.
    + simpl. rewrite mem_locks_union, mem_locks_singleton
        by eauto using memperm_kind_lock. esolve_elem_of.
    + apply ax_done. constructor; [|solve_assert].
      rewrite mem_locks_union, mem_locks_singleton
        by eauto using memperm_kind_lock.
      by rewrite <-(associative_eq _), <-HΩ, (left_id_eq ∅ _).
  * exfalso; eauto 8 with cstep.
Qed.

Lemma ax_load Δ γ e P Q :
  perm_kind γ ≠ Locked →
  Δ ⊨ₑ {{ P }} e {{ λ a, ∃ v, Q a v ★ valc a ↦{γ} valc v }} →
  Δ ⊨ₑ {{ P }} load e {{ λ v, ∃ a, Q a v ★ valc a ↦{γ} valc v }}.
Proof.
  intros Hγ Hax n k m ??? Hpre.
  rewrite <-(right_id_eq ∅ (∪) m).
  apply (ax_expr_compose n (fpure Δ)
    [# λ a, ∃ v, Q a v ★ valc a ↦{γ} valc v]%A _ DCLoad [# e] k [# m]).
  { done. }
  { apply mem_list_disjoint_singleton. }
  { intros. inv_all_vec_fin; esolve_elem_of. }
  { intros. inv_all_vec_fin; simpl; auto. }

  clear dependent m Hax. intros Ωs vs ms.
  inv_vec Ωs; intros Ω Ωs; inv_vec Ωs.
  inv_vec vs; intros v vs; inv_vec vs.
  inv_vec ms; intros m ms; inv_vec ms; simpl; intros _ HΩ Hax.
  rewrite (right_id_eq ∅ (∪) m).
  specialize (HΩ 0%fin). simpl in HΩ.
  specialize (Hax 0%fin). simpl in Hax.

  destruct Hax as (?&m1&?&?&?&?&a'&v'&?&?&?); simpl in *; simplify_equality.
  apply ax_further_pred.
  { intros. solve_cred. }

  intros mf S' ? p. inv_cstep p.
  * inv_ehstep. simplify_mem_equality. constructor; try done.
    apply ax_done. constructor.
    { by rewrite mem_locks_union. }
    solve_assert.
  * exfalso; eauto with cstep.
Qed.

Lemma ax_alloc Δ :
  Δ ⊨ₑ {{ emp }} alloc {{ λ a, valc a ↦{Freeable} - }}.
Proof.
  intros n k ?? _ _ ?. unfold_assert in *; subst.
  apply ax_further_pred.
  { intros. solve_cred. }
  intros mf S' ? p. rewrite (left_id_eq ∅ (∪)) in p. inv_cstep p.
  * inv_ehstep. rewrite mem_alloc_singleton_l by done.
    constructor; try (by auto with mem_disjoint); [esolve_elem_of|].
    apply ax_done. constructor.
    { by apply mem_locks_singleton_ne. }
    solve_assert.
  * exfalso; eauto with cstep.
Qed.

Lemma ax_free Δ e P Q :
  Δ ⊨ₑ {{ P }} e {{ λ a, Q ★ valc a ↦{Freeable} - }} →
  Δ ⊨ₑ {{ P }} free e {{ λ v, Q }}.
Proof.
  intros Hax n k m ??? Hpre.
  rewrite <-(right_id_eq ∅ (∪) m).
  apply (ax_expr_compose n (fpure Δ)
    [# λ a, Q ★ valc a ↦{Freeable} -]%A _ DCFree [# e] k [# m]).
  { done. }
  { apply mem_list_disjoint_singleton. }
  { intros. inv_all_vec_fin; esolve_elem_of. }
  { intros. inv_all_vec_fin; simpl; auto. }

  clear dependent m Hax. intros Ωs vs ms.
  inv_vec Ωs; intros Ω Ωs; inv_vec Ωs.
  inv_vec vs; intros v vs; inv_vec vs.
  inv_vec ms; intros m ms; inv_vec ms; simpl; intros _ HΩs Hax.
  rewrite (right_id_eq ∅ (∪) m).

  specialize (Hax 0%fin). simpl in Hax.
  specialize (HΩs 0%fin). simpl in HΩs. subst.

  destruct Hax as (m1&?&?&?&?&a&v'&?&?); simpl in *; simplify_equality.
  apply ax_further_pred.
  { intros. solve_cred. }

  intros mf S' ? p. inv_cstep p.
  * inv_ehstep.
    erewrite mem_delete_union_l, mem_delete_union_r by eauto with simpl_mem.
    rewrite mem_delete_singleton, (right_id_eq ∅ _).
    rewrite mem_locks_union, mem_locks_singleton_ne, (right_id_eq ∅ _) by done.
    decompose_mem_disjoint. constructor; try done.
    by apply ax_done; constructor.
  * exfalso; eauto 10 with cstep.
Qed.

Lemma ax_unop Δ op e P Q :
  Δ ⊨ₑ {{ P }} e {{ Q }} →
  (∀ v, Q v ⊆@{fpure Δ} (⊙{op} valc v ⇓-)%A) →
  Δ ⊨ₑ {{ P }}
         ⊙{op} e
       {{ λ v', ∃ v, ⊙{op} valc v ⇓ v' ∧ Q v }}.
Proof.
  intros Hax Hop n k m ????.
  rewrite <-(right_id_eq ∅ (∪) m).
  apply (ax_expr_compose n (fpure Δ) [# Q] _ (DCUnOp op) [# e] k [# m]).
  { done. }
  { simpl. eauto with mem_disjoint. }
  { intros. inv_all_vec_fin; esolve_elem_of. }
  { intros. inv_all_vec_fin; simpl; auto. }

  clear dependent m Hax e. intros Ωs vs ms.
  inv_vec Ωs; intros Ω Ωs; inv_vec Ωs.
  inv_vec vs; intros v vs; inv_vec vs.
  inv_vec ms; intros m ms; inv_vec ms.
  simpl. intros _ HΩ Hax. rewrite (right_id_eq ∅ (∪) m).
  specialize (HΩ 0%fin). simpl in HΩ.
  specialize (Hax 0%fin). simpl in Hax.

  destruct (Hop v (get_stack k) m) as [v' Hv'].
  { solve_assert. }
  clear Hop. unfold_assert in *; simpl in Hv'.

  apply ax_further_pred.
  { intros. solve_cred. }

  intros mf' S' ? p. inv_cstep p.
  * inv_ehstep. constructor; try done.
    apply ax_done; constructor; try done.
    exists v. solve_assert.
  * exfalso; eauto with cstep.
Qed.

Lemma ax_binop Δ op el Pl Ql er Pr Qr :
  Δ ⊨ₑ {{ Pl }} el {{ Ql }} →
  Δ ⊨ₑ {{ Pr }} er {{ Qr }} →
  (∀ vl vr, (Ql vl ★ Qr vr)%A ⊆@{fpure Δ} (valc vl ⊙{op} valc vr ⇓-)%A) →
  Δ ⊨ₑ {{ Pl ★ Pr }}
         el ⊙{op} er
       {{ λ v', ∃ vl vr, valc vl ⊙{op} valc vr ⇓ v' ∧ (Ql vl ★ Qr vr) }}.
Proof.
  intros Haxl Haxr Hop n k ??? Hm (m1&m2&?&?&?&?); subst.
  rewrite mem_locks_union in Hm by done. simpl in *. decompose_empty.
  rewrite <-(right_id_eq ∅ (∪) m2).
  apply (ax_expr_compose n (fpure Δ)
    [# Ql;Qr] _ (DCBinOp op) [# el;er] k [# m1;m2]).
  { done. }
  { simpl. by apply mem_list_disjoint_double. }
  { intros. inv_all_vec_fin; esolve_elem_of. }
  { intros. inv_all_vec_fin; simpl; auto. }

  clear dependent m1 m2 Haxl Haxr. intros Ωs vs ms.
  inv_vec Ωs; intros Ω1 Ωs; inv_vec Ωs; intros Ω2 Ωs; inv_vec Ωs.
  inv_vec vs; intros v1 vs; inv_vec vs; intros v2 vs; inv_vec vs.
  inv_vec ms; intros m1 ms; inv_vec ms; intros m2 ms; inv_vec ms.
  simpl. intros Hdisjoint HΩs Hax. rewrite (right_id_eq ∅ (∪) m2).
  pose proof (HΩs 0%fin) as HΩl. pose proof (HΩs 1%fin) as HΩr.
  pose proof (Hax 0%fin) as Haxl. pose proof (Hax 1%fin) as Haxr.
  simpl in HΩl, HΩr, Haxl, Haxr. clear HΩs Hax.
  rewrite mem_list_disjoint_double in Hdisjoint.

  destruct (Hop v1 v2 (get_stack k) (m1 ∪ m2)) as [v' Hv'].
  { solve_assert. }
  clear Hop. unfold_assert in *; simpl in Hv'.

  apply ax_further_pred.
  { intros. solve_cred. }

  intros mf' S' ? p. inv_cstep p.
  * inv_ehstep. rewrite <-mem_locks_union by done.
    constructor; try done. apply ax_done; constructor; try done.
    exists v1 v2. solve_assert.
  * exfalso; eauto with cstep.
Qed.

Lemma ax_expr_if Δ e el er P (P' : vassert) Q :
  Δ ⊨ₑ {{ P }} e {{ λ v, P' v ▷ }} →
  Δ ⊨ₑ {{ assert_is_true P' }} el {{ Q }} →
  Δ ⊨ₑ {{ assert_is_false P' }} er {{ Q }} →
  Δ ⊨ₑ {{ P }} IF e then el else er {{ Q }}.
Proof.
  intros Hax Haxl Haxr n k m HΔ He Hm Hpre.
  simpl in He. decompose_empty.
  rewrite <-(right_id_eq ∅ (∪) m).
  apply (ax_expr_compose n (fpure Δ)
    [# assert_unlock ∘ P'] _ (DCIf el er) [# e] k [# m]).
  { simpl. by apply empty_union_L. }
  { apply mem_list_disjoint_singleton. }
  { intros. inv_all_vec_fin; esolve_elem_of. }
  { intros. inv_all_vec_fin; simpl; intuition. }

  clear dependent e m. intros Ωs vs ms.
  inv_vec Ωs; intros Ω Ωs; inv_vec Ωs.
  inv_vec vs; intros v vs; inv_vec vs.
  inv_vec ms; intros m ms; inv_vec ms; simpl; intros ? HΩ Hax.
  rewrite (right_id_eq ∅ (∪) m).
  specialize (Hax 0%fin). simpl in Hax.
  specialize (HΩ 0%fin). simpl in HΩ.

  apply ax_further_pred.
  { intros. simpl. destruct (val_true_false_dec v); solve_cred. }

  intros mf S' ? p. inv_cstep p.
  * inv_ehstep.
    + rewrite mem_unlock_union_l by done.
      apply mk_ax_next_alt; try by auto with mem_disjoint.
      apply Haxl; rewrite ?mem_locks_unlock_all; auto with ax.
      solve_assert.
    + rewrite mem_unlock_union_l by done.
      apply mk_ax_next_alt; try by auto with mem_disjoint.
      apply Haxr; rewrite ?mem_locks_unlock_all; auto with ax.
      solve_assert.
  * exfalso; destruct (val_true_false_dec v); eauto with cstep.
Qed.

(** ** Rules for statements *)
Lemma ax_do Δ R J P Q e :
  Δ ⊨ₑ {{ P }} e {{ λ _, Q ▷ }} →
  Δ \ R \ J ⊨ₛ {{ P }} do e {{ Q }}.
Proof.
  intros Hax n k [] m ?? He ??; discriminate_down_up.
  apply ax_further_pred.
  { intros. solve_cred. }
  intros mf S' ? p. inv_cstep p. constructor; try done.
  { esolve_elem_of. }
  clear dependent mf S'. eapply ax_compose_cons; auto with ax.
  intros m' φ' [v ???]. apply ax_further_pred.
  { intros. solve_cred. }
  intros mf S' ? p. inv_cstep p.
  rewrite mem_unlock_union_l by solve_elem_of.
  apply mk_ax_next_alt; try by auto with mem_disjoint.
  clear dependent m mf φ' v S'.
  apply ax_done; constructor; auto. by rewrite mem_locks_unlock_all.
Qed.

Lemma ax_skip Δ R J P : Δ \ R \ J ⊨ₛ {{ P }} skip {{ P }}.
Proof.
  intros n k [] m ?????; discriminate_down_up.
  apply ax_further_pred.
  { intros. solve_cred. }
  intros mf S' ? p. inv_cstep p.
  apply mk_ax_next_alt; try done.
  clear dependent mf S'. by apply ax_done; constructor.
Qed.

Lemma ax_ret Δ J P R e Q :
  Δ ⊨ₑ {{ P }} e {{ λ v, R v ▷ }} →
  Δ \ R \ J ⊨ₛ {{ P }} ret e {{ Q }}.
Proof.
  intros Hax n k [] m ?? He ??; discriminate_down_up.
  apply ax_further_pred.
  { intros. solve_cred. }
  intros mf S' ? p. inv_cstep p. apply mk_ax_next_alt; try done.
  clear dependent mf S'. eapply ax_compose_cons; auto with ax.
  intros m' φ' [v ???]. apply ax_further_pred.
  { intros. solve_cred. }
  intros mf S' ? p. inv_cstep p.
  rewrite mem_unlock_union_l by solve_elem_of.
  apply mk_ax_next_alt; try by auto with mem_disjoint.
  clear dependent m mf φ' S'.
  apply ax_done; constructor; auto. by rewrite mem_locks_unlock_all.
Qed.

Lemma ax_packed_blk Δ Pd s :
  Δ \ (λ P, var O ↦{Writable} - ★ P↑)%A <$> Pd ⊨ₚ s →
  Δ \ Pd ⊨ₚ blk s.
Proof.
  intros Hax n k. revert n.
  cut (∀ n d m b,
   ax_funs n Δ →
   is_free m b →
   down d s →
   locks s = ∅ →
   locks m = ∅ →
   assert_holds (fpure Δ) (Pd d) (get_stack k) m →
   ax (ax_stmt_P (blk s) (fpure Δ) Pd) k n
     (CBlock b :: k) (Stmt d s) (mem_alloc b voidc Writable m)).
  { intros help n d m ?????. apply ax_further_pred.
    { intros. solve_cred. }
    intros mf S' ? p.
    destruct d; discriminate_down_up; inv_cstep p; decompose_is_free.
    * rewrite mem_alloc_union_l by done.
      apply mk_ax_next_alt; try by auto with mem_disjoint.
      apply help; auto with ax.
    * rewrite mem_alloc_union_l by done.
      apply mk_ax_next_alt; try by auto with mem_disjoint.
      apply help; auto with ax. }

  intros n d m b v ?????.
  eapply ax_compose_cons; [| clear dependent m v d].
  { eapply Hax; eauto.
    { by rewrite mem_locks_alloc. }
    rewrite directed_fmap_spec. simpl. by apply assert_alloc. }

  intros m φ [d ?? Hpost]. apply ax_further_pred.
  { intros. solve_cred. }

  rewrite directed_fmap_spec in Hpost. simpl in Hpost.
  apply assert_free in Hpost; [|by auto using Writable_fragment].
  destruct Hpost. intros mf S' ? p.
  destruct d; discriminate_down_up; inv_cstep p.
  * erewrite mem_delete_union_l by eauto using Writable_fragment.
    apply mk_ax_next_alt; try by auto with mem_disjoint.
    apply ax_done; constructor; try done. by apply mem_locks_delete_empty.
  * erewrite mem_delete_union_l by eauto using Writable_fragment.
    apply mk_ax_next_alt; try by auto with mem_disjoint.
    apply ax_done; constructor; try done. by apply mem_locks_delete_empty.
  * erewrite mem_delete_union_l by eauto using Writable_fragment.
    apply mk_ax_next_alt; try by auto with mem_disjoint.
    apply ax_done; constructor; try done. by apply mem_locks_delete_empty.
Qed.

Lemma ax_blk Δ R J P Q s :
  Δ \ (λ v, var O ↦{Writable} - ★ R v↑) \ (λ l, var O ↦{Writable} - ★ J l↑) ⊨ₛ
    {{ var O ↦{Writable} - ★ P↑ }} s {{ var O ↦{Writable} - ★ Q↑ }} →
  Δ \ R \ J ⊨ₛ {{ P }} blk s {{ Q }}.
Proof. intros. by apply ax_packed_blk. Qed.

Lemma ax_label Δ R J l s Q :
  Δ \ R \ J ⊨ₛ {{ J l }} s {{ Q }} →
  Δ \ R \ J ⊨ₛ {{ J l }} l :; s {{ Q }}.
Proof.
  intros Hax n k. revert n.
  set (Pd := dassert_pack (J l) Q R J).
  cut (∀ n d m,
   ax_funs n Δ →
   down d s →
   locks s = ∅ →
   locks m = ∅ →
   assert_holds (fpure Δ) (Pd d) (get_stack k) m →
   ax (ax_stmt_P (l :; s) (fpure Δ) Pd) k n
     (CStmt (l :; □) :: k) (Stmt d s) m).
  { intros help n d m ?? Hs ??. apply ax_further_pred.
    { intros. clear dependent Pd. solve_cred. }
    intros mf S' ? p. simpl in Hs.
    by destruct d; discriminate_down_up; inv_cstep p;
      apply mk_ax_next_alt; auto with ax. }

  induction n as [|n IH]; [constructor |].
  intros d m ?????.
  eapply ax_compose_cons; [by apply Hax | clear dependent m d].

  intros m φ [d ?? Hpost]. apply ax_further.
  { intros. solve_cred. }

  intros mf S' ? p. destruct d; discriminate_down_up; inv_cstep p.
  * apply mk_ax_next_alt; try done. by apply ax_done.
  * apply mk_ax_next_alt; try done. by apply ax_done.
  * match goal with
    | _ : ?l' ∉ labels s |- _ => destruct (decide (l' = l))
    end; subst.
    + apply mk_ax_next_alt; try done. apply ax_further_pred.
      { intros. solve_cred. }
      intros mf' S'' ? p. inv_cstep p.
      by apply mk_ax_next_alt; auto with ax.
    + apply mk_ax_next_alt; try done.
      apply ax_done; constructor; try done. solve_elem_of.
Qed.

Lemma ax_while Δ R J P Q e s :
  Δ ⊨ₑ {{ P }} e {{ λ v, Q v ▷ }} →
  Δ \ R \ J ⊨ₛ {{ assert_is_true Q }} s {{ P }} →
  Δ \ R \ J ⊨ₛ {{ P }} while (e) s {{ assert_is_false Q }}.
Proof.
  intros Haxe Hax n k. revert n.
  set (Pd := dassert_pack P (assert_is_false Q) R J).
  set (Pd' := dassert_pack (assert_is_true Q) P R J).
  cut (∀ n d m,
   ax_funs n Δ →
   down d s →
   locks e = ∅ →
   locks s = ∅ →
   locks m = ∅ →
   assert_holds (fpure Δ) (Pd' d) (get_stack k) m →
   ax (ax_stmt_P (while (e) s) (fpure Δ) Pd) k n
     (CStmt (while (e) □) :: k) (Stmt d s) m).
  { intros help n [] m ?? Hs ??; simpl in Hs;
      decompose_empty; discriminate_down_up.
    * apply ax_further_pred.
      { intros. solve_cred. }
      intros mf S' ? p. inv_cstep p.
      apply mk_ax_next_alt; try done.
      eapply ax_compose_cons;
        [apply Haxe; auto with ax | clear dependent m mf S'].
      intros m φ [v ???]. apply ax_further_pred.
      { intros. destruct (val_true_false_dec v); solve_cred. }
      intros mf S' ? p. inv_cstep p.
      + rewrite mem_unlock_union_l by done.
        apply mk_ax_next_alt; try by auto with mem_disjoint.
        apply help; rewrite ?mem_locks_unlock_all; auto with ax. solve_assert.
      + rewrite mem_unlock_union_l by done.
        apply mk_ax_next_alt; try (by auto with mem_disjoint);[esolve_elem_of|].
        apply ax_done; constructor; rewrite ?mem_locks_unlock_all; try done.
        solve_assert.
    * apply ax_further_pred.
      { intros. solve_cred. }
      intros mf S' ? p. inv_cstep p.
      by apply mk_ax_next_alt; auto with ax. }

  induction n as [|n IH]; [constructor |].
  intros d m ??????.
  eapply ax_compose_cons; [by apply Hax | clear dependent m d].

  intros m φ [d ?? Hpost]. apply ax_further.
  { intros. solve_cred. }

  intros mf S' ? p. destruct d; discriminate_down_up; inv_cstep p.
  * apply mk_ax_next_alt; try done.
    { simpl. by apply empty_union_L. }
    clear dependent φ mf S'. apply ax_further_pred.
    { intros. solve_cred. }
    intros mf S' ? p. inv_cstep p.
    apply mk_ax_next_alt; try done. eapply ax_compose_cons;
      [apply Haxe; auto with ax | clear dependent m mf S'].
    intros m φ [v ???]. apply ax_further_pred.
    { intros. destruct (val_true_false_dec v); solve_cred. }
    intros mf S' ? p. inv_cstep p.
    + rewrite mem_unlock_union_l by done.
      apply mk_ax_next_alt; try by auto with mem_disjoint.
      apply ax_pred, ax_pred, IH; rewrite ?mem_locks_unlock_all; auto with ax.
      solve_assert.
    + rewrite mem_unlock_union_l by done.
      apply mk_ax_next_alt; try by auto with mem_disjoint.
      { simpl. by apply empty_union_L. }
      apply ax_done; constructor; rewrite ?mem_locks_unlock_all; try done.
      solve_assert.
  * apply mk_ax_next_alt; try done; [esolve_elem_of |]. by apply ax_done.
  * apply mk_ax_next_alt; try done; [esolve_elem_of |]. by apply ax_done.
Qed.

Lemma ax_comp Δ R J sl sr P P' Q :
  Δ \ R \ J ⊨ₛ {{ P }} sl {{ P' }} →
  Δ \ R \ J ⊨ₛ {{ P' }} sr {{ Q }} →
  Δ \ R \ J ⊨ₛ {{ P }} sl ;; sr {{ Q }}.
Proof.
  intros Haxl Haxr n k. revert n.
  set (Pd := dassert_pack P Q R J).
  set (Pdl := dassert_pack P P' R J).
  set (Pdr := dassert_pack P' Q R J).
  cut (∀ n d m,
   ax_funs n Δ →
   locks sl = ∅ →
   locks sr = ∅ →
   locks m = ∅ →
   (down d sl → assert_holds (fpure Δ) (Pdl d) (get_stack k) m →
     ax (ax_stmt_P (sl ;; sr) (fpure Δ) Pd) k n
       (CStmt (□ ;; sr) :: k) (Stmt d sl) m)
   ∧ (down d sr → assert_holds (fpure Δ) (Pdr d) (get_stack k) m →
     ax (ax_stmt_P (sl ;; sr) (fpure Δ) Pd) k n
       (CStmt (sl ;; □) :: k) (Stmt d sr) m)).
  { intros help n d m ?? Hs ??. simpl in Hs. decompose_empty.
    apply ax_further_pred.
    { intros. solve_cred. }
    intros mf S' ? p.
    destruct d; discriminate_down_up; inv_cstep p.
    * apply mk_ax_next_alt; try done. eapply help; eauto with ax.
    * apply mk_ax_next_alt; try done. eapply help; eauto with ax.
    * apply mk_ax_next_alt; try done. eapply help; eauto with ax. }

  induction n as [|n IH]; [repeat constructor |].
  intros d m; split; intros ??.

  * eapply ax_compose_cons; [by apply Haxl | clear dependent m d].
    intros m φ [d ?? Hpost]. apply ax_further.
    { intros. solve_cred. }

    intros mf S' ? p. destruct d; discriminate_down_up; inv_cstep p.
    + apply mk_ax_next_alt; try done. eapply IH; auto with ax arith.
    + apply mk_ax_next_alt; try done.
      { simpl. by apply empty_union_L. }
      by apply ax_done.
    + match goal with
      | _ : ?l ∉ labels sl |- _ => destruct (decide (l ∈ labels sr))
      end; subst.
      - apply mk_ax_next_alt; try done; [esolve_elem_of|].
        apply ax_further_pred.
        { intros. solve_cred. }
        intros mf' S'' ? p. inv_cstep p.
        apply mk_ax_next_alt; try done. apply ax_pred, IH; auto with ax.
      - apply mk_ax_next_alt; try done; [esolve_elem_of|].
        apply ax_done; constructor; solve_elem_of.

  * eapply ax_compose_cons; [by apply Haxr | clear dependent m d].
    intros m φ [d ?? Hpost]. apply ax_further.
    { intros. solve_cred. }

    intros mf S' ? p. destruct d; discriminate_down_up; inv_cstep p.
    + apply mk_ax_next_alt; try done; [esolve_elem_of |]. by apply ax_done.
    + apply mk_ax_next_alt; try done; [esolve_elem_of |]. by apply ax_done.
    + match goal with
      | _ : ?l ∉ labels sr |- _ => destruct (decide (l ∈ labels sl))
      end; subst.
      - apply mk_ax_next_alt; try done; [esolve_elem_of |].
        apply ax_further_pred.
        { intros. solve_cred. }
        intros mf' S'' ? p. inv_cstep p.
        apply mk_ax_next_alt; try done. apply ax_pred, IH; auto with ax.
      - apply mk_ax_next_alt; try done; [esolve_elem_of |].
        apply ax_done; constructor; solve_elem_of.
Qed.

Lemma ax_if Δ R J e sl sr P P' Q :
  Δ ⊨ₑ {{ P }} e {{ λ v, P' v ▷ }} →
  Δ \ R \ J ⊨ₛ {{ assert_is_true P' }} sl {{ Q }} →
  Δ \ R \ J ⊨ₛ {{ assert_is_false P' }} sr {{ Q }} →
  Δ \ R \ J ⊨ₛ {{ P }} IF e then sl else sr {{ Q }}.
Proof.
  intros Haxe Haxl Haxr n k. revert n.
  set (Pd := dassert_pack P Q R J).
  set (Pdl := dassert_pack (assert_is_true P') Q R J).
  set (Pdr := dassert_pack (assert_is_false P') Q R J).
  cut (∀ n d m,
   ax_funs n Δ →
   locks e = ∅ →
   locks sl = ∅ →
   locks sr = ∅ →
   locks m = ∅ →
   (down d sl → assert_holds (fpure Δ) (Pdl d) (get_stack k) m →
     ax (ax_stmt_P (IF e then sl else sr) (fpure Δ) Pd) k n
       (CStmt (IF e then □ else sr) :: k) (Stmt d sl) m)
   ∧ (down d sr → assert_holds (fpure Δ) (Pdr d) (get_stack k) m →
     ax (ax_stmt_P (IF e then sl else sr) (fpure Δ) Pd) k n
       (CStmt (IF e then sl else □) :: k) (Stmt d sr) m)).
  { intros help n [] m ?? Hs ??; simpl in Hs;
      decompose_empty; discriminate_down_up.
    * apply ax_further_pred.
      { intros. solve_cred. }
      intros mf S' ? p. inv_cstep p.
      apply mk_ax_next_alt; try done. eapply ax_compose_cons;
        [apply Haxe; auto with ax | clear dependent m mf S'].
      intros m φ [v ???]. apply ax_further_pred.
      { intros. destruct (val_true_false_dec v); solve_cred. }
      intros mf S' ? p. inv_cstep p.
      + rewrite mem_unlock_union_l by done.
        apply mk_ax_next_alt; try by auto with mem_disjoint.
        apply help; rewrite ?mem_locks_unlock_all; auto with ax. solve_assert.
      + rewrite mem_unlock_union_l by done.
        apply mk_ax_next_alt; try by auto with mem_disjoint.
        apply help; rewrite ?mem_locks_unlock_all; auto with ax. solve_assert.
    * apply ax_further_pred.
      { intros. solve_cred. }
      intros mf S' ? p. inv_cstep p.
      + apply mk_ax_next_alt; try by auto with mem_disjoint.
        apply help; rewrite ?mem_locks_unlock_all; auto with ax.
      + apply mk_ax_next_alt; try by auto with mem_disjoint.
        apply help; rewrite ?mem_locks_unlock_all; auto with ax. }

  induction n as [|n IH]; [repeat constructor |].
  intros d m; split; intros ??.

  * eapply ax_compose_cons; [by apply Haxl | clear dependent m d].
    intros m φ [d ?? Hpost]. apply ax_further.
    { intros. solve_cred. }

    intros mf S' ? p. destruct d; discriminate_down_up; inv_cstep p.
    + apply mk_ax_next_alt; try done; [esolve_elem_of|]. by apply ax_done.
    + apply mk_ax_next_alt; try done; [esolve_elem_of|]. by apply ax_done.
    + match goal with
      | _ : ?l ∉ labels sl |- _ => destruct (decide (l ∈ labels sr))
      end; subst.
      - apply mk_ax_next_alt; try done; [esolve_elem_of|].
        apply ax_further_pred.
        { intros. solve_cred. }
        intros mf' S'' ? p. inv_cstep p.
        apply mk_ax_next_alt; try done. apply ax_pred, IH; auto with ax.
      - apply mk_ax_next_alt; try done; [esolve_elem_of|].
        apply ax_done. constructor; solve_elem_of.

  * eapply ax_compose_cons; [by apply Haxr | clear dependent m d].
    intros m φ [d ?? Hpost]. apply ax_further.
    { intros. solve_cred. }

    intros mf S' ? p. destruct d; discriminate_down_up; inv_cstep p.
    + apply mk_ax_next_alt; try done; [esolve_elem_of|]. by apply ax_done.
    + apply mk_ax_next_alt; try done; [esolve_elem_of|]. by apply ax_done.
    + match goal with
      | _ : ?l ∉ labels sr |- _ => destruct (decide (l ∈ labels sl))
      end; subst.
      - apply mk_ax_next_alt; try done; [esolve_elem_of|].
        apply ax_further_pred.
        { intros. solve_cred. }
        intros mf' S'' ? p. inv_cstep p.
        apply mk_ax_next_alt; try done. apply ax_pred, IH; auto with ax.
      - apply mk_ax_next_alt; try done; [esolve_elem_of|].
        apply ax_done. constructor; solve_elem_of.
Qed.
End axiomatic.

Instance: Params (@ax_stmt_packed) 2.
Instance: Params (@ax_stmt) 2.
Instance: Params (@ax_stmt_top) 2.
Instance: Params (@ax_expr) 2.

Notation fassert_env := (funmap fassert).
Notation dassert := (direction → assert).
Notation dassert_pack P Q R J := (@directed_pack assert P%A Q%A R%A J%A).

Notation "δ \ Δ \ P ⊨ₚ s" :=
  (ax_stmt_packed δ Δ P%A s%S)
  (at level 74, Δ at next level, P at next level,
   format "δ  \  Δ  \  P  ⊨ₚ  '[' s ']'").
Notation "δ \ Δ \ R \ J ⊨ₛ {{ P }} s {{ Q }}" :=
  (ax_stmt δ Δ R%A J%A P%A s%S Q%A)
  (at level 74, Δ at next level, R at next level, J at next level,
   format "δ  \  Δ  \  R  \  J  ⊨ₛ  '[' {{  P  }} '/'  s  '/' {{  Q  }} ']'").
Notation "δ \ Δ ⊨ₜ {{ P }} s {{ Q }}" :=
  (ax_stmt_top δ Δ P%A s%S Q%A)
  (at level 74, format "δ  \  Δ  ⊨ₜ  '[' {{  P  }} '/'  s  '/' {{  Q  }} ']'").
Notation "δ \ Δ ⊨ₑ {{ P }} e {{ Q }}" :=
  (ax_expr δ Δ P%A e%E Q%A)
  (at level 74, Δ at next level,
   format "δ  \  Δ  ⊨ₑ  '[' {{  P  }} '/'  e  '/' {{  Q  }} ']'").
