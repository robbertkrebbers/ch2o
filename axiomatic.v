(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file defines an axiomatic semantics (in the form of separation logic)
for our language. This axiomatic semantics has two judgments: one for
statements and one for expressions. Statement judgment are sextuples of the
shape [Δ\ R\ J ⊨ₛ {{ P }} s {{ Q }}] where:

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

(** Expression judgments are quintuples [Δ\ A ⊨ₑ {{ P }} e {{ Q }}]. As usual,
[P] and [Q] are the pre- and postcondition of [e], but whereas the precondition
is just an assertion, the postcondition is a function from values to assertions.
It ensures that if execution of [e] yields a value [v], then [Q v] holds. The
environment [A] can be used to "frame" writable memory that is being shared by
all function calls. *)

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
(** We want [Δ\ R\ J ⊨ₛ {{ P }} s {{ Q }}] to ensure partial program
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
  Hence, [Δ\ Pd ⊨ₚ s] should at least guarantee that if [P d k m] and
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
[Δ\ A ⊨ₑ {{ P }} e {{ Q }}] as well. Therefore, we first define a more general
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

Notation ax_assert := (ctx → mem → focus → Prop).
Record ax_frame_cond A := {
  frame : ctx → focus → mem → mem → A → Prop;
  unframe : ctx → focus → mem → mem → A → Prop
}.
Arguments frame {_} _ _ _ _ _ _.
Arguments unframe {_} _ _ _ _ _ _.

Section ax.
  Context `(F: ax_frame_cond A) (P : ax_assert).
  Context `{Pnf: PropHolds (∀ l φ m m' a,
    P l m φ → frame F l φ m m' a → nf (cstep_in_ctx δ l) (State l φ m'))}.

  Inductive ax (l : ctx) : nat → ctx → focus → mem → Prop :=
    | ax_O k φ m : ax l 0 k φ m
    | ax_done n φ m : P l m φ → ax l n l φ m
    | ax_further n k φ m :
       (∀ m' a,
         frame F k φ m m' a →
         red (cstep_in_ctx δ l) (State k φ m')) →
       (∀ m' a S',
         frame F k φ m m' a →
         δ ⊢ₛ State k φ m' ⇒{l} S' →
         ax_next l n a S') →
       ax l (S n) k φ m
  with ax_next (l : ctx) : nat → A → state → Prop :=
    | mk_ax_next n k φ m m' a :
       unframe F k φ m m' a →
       φ ≠ Undef →
       locks φ ⊆ locks m →
       ax l n k φ m →
       ax_next l n a (State k φ m').

  Lemma mk_ax_next_empty l n k φ m m' a :
    unframe F k φ m m' a →
    φ ≠ Undef →
    locks φ = ∅ →
    ax l n k φ m →
    ax_next l n a (State k φ m').
  Proof. econstructor; esolve_elem_of. Qed.

  Lemma ax_further_pred l n k φ m :
    (∀ m' a,
      frame F k φ m m' a →
      red (cstep_in_ctx δ l) (State k φ m')) →
    (∀ m' a S',
      frame F k φ m m' a →
      δ ⊢ₛ State k φ m' ⇒{l} S' →
      ax_next l (pred n) a S') →
    ax l n k φ m.
  Proof. destruct n; econstructor (by eauto). Qed.

  Lemma ax_S l n k φ m (Hax : ax l (S n) k φ m) : ax l n k φ m
  with ax_next_S l n a S' (Hax : ax_next l (S n) a S') : ax_next l n a S'.
  Proof.
  { inversion Hax; subst.
    * by apply ax_done.
    * destruct n; [apply ax_O |].
      apply ax_further; [done |]. intros. apply (ax_next_S). eauto. }
  { inversion Hax; subst. econstructor; eauto. }
  Qed.

  Lemma ax_plus_l l n1 n2 k φ m : ax l (n1 + n2) k φ m → ax l n2 k φ m.
  Proof. induction n1; simpl; auto using ax_S. Qed.
  Lemma ax_next_plus_l l n1 n2 a S' :
    ax_next l (n1 + n2) a S' → ax_next l n2 a S'.
  Proof. induction n1; simpl; auto using ax_next_S. Qed.
  Lemma ax_le l n1 n2 k φ m : ax l n2 k φ m → n1 ≤ n2 → ax l n1 k φ m.
  Proof.
    intros Hax ?. rewrite (Minus.le_plus_minus n1 n2), plus_comm in Hax;
      eauto using ax_plus_l.
  Qed.
  Lemma ax_next_le l n1 n2 a S : ax_next l n2 a S → n1 ≤ n2 → ax_next l n1 a S.
  Proof.
    intros Hax ?. rewrite (Minus.le_plus_minus n1 n2), plus_comm in Hax;
      eauto using ax_next_plus_l.
  Qed.
  Lemma ax_pred l n k φ m : ax l n k φ m → ax l (pred n) k φ m.
  Proof. intros. eauto using ax_le with arith. Qed.

  Lemma ax_step l n k φ m m' a S' :
    frame F k φ m m' a →
    δ ⊢ₛ State k φ m' ⇒{l} S' →
    ax l (S n) k φ m →
    ax_next l n a S'.
  Proof.
    inversion 3 as [| | ???? _ Hnext]; subst; eauto.
    destruct (Pnf k φ m m' a); trivial. solve_cred.
  Qed.

  Lemma ax_red l n k φ m m' a :
    frame F k φ m m' a →
    ¬P k m φ →
    ax l (S n) k φ m →
    red (cstep_in_ctx δ l) (State k φ m').
  Proof. inversion 3; subst; by eauto. Qed.

  Lemma ax_step_undef l n k φ m m' a k' m'' :
    frame F k φ m m' a →
    δ ⊢ₛ State k φ m' ⇒{l} State k' Undef m'' →
    ¬ax l (S n) k φ m.
  Proof.
    intros ? p Hax.
    by feed inversion (ax_step l n k φ m m' a (State k' Undef m'')); subst.
  Qed.

  Lemma ax_steps n1 n2 l k φ m m' a S' :
    (∀ k φ k' φ' m m' a, unframe F k φ m m' a → frame F k' φ' m m' a) →
    (∀ k φ k' φ' m m' a, frame F k φ m m' a → unframe F k' φ' m m' a) →
    frame F k φ m m' a →
    φ ≠ Undef →
    locks φ ⊆ locks m →
    ax l (n1 + n2) k φ m →
    δ ⊢ₛ State k φ m' ⇒{l}^n1 S' →
    ax_next l n2 a S'.
  Proof.
    intros ??. revert k φ m m'. induction n1 as [n1 IH] using lt_wf_ind.
    intros k φ m m' ??? Hax p. inv_csteps p as [|n' ? S'' ? p1 p2].
    * econstructor; eauto using ax_plus_l.
    * feed inversion (ax_step l (n' + n2) k φ m m' a S''); subst; eauto.
  Qed.
End ax.
Hint Resolve ax_pred ax_S : ax.

(** The predicate [ax] can be composed. This property is used to prove the
structural Hoare rules. *)
Definition ax_compose_diagram `(F : ax_frame_cond A) `(G : ax_frame_cond B)
    (l : ctx) := ∀ k φ m m' b,
  l `suffix_of` k →
  frame G k φ m m' b →
  ∃ a, frame F k φ m m' a ∧ ∀ k' φ' m2 m2',
    l `suffix_of` k' →
    unframe F k' φ' m2 m2' a → unframe G k' φ' m2 m2' b.

Lemma ax_compose `(F : ax_frame_cond A) `(G : ax_frame_cond B)
    P Q n φ k1 k2 k3 m :
  k2 `suffix_of` k1 → k3 `suffix_of` k2 →
  ax_compose_diagram F G k2 →
  ax F P k2 n k1 φ m →
  (∀ m' φ', P k2 m' φ' → ax G Q k3 n k2 φ' m') →
  ax G Q k3 n k1 φ m.
Proof.
  revert φ k1 m. induction n as [|n IH].
  { intros. apply ax_O. }
  intros φ k1 m ?? HF Hax Hnext.
  inversion Hax as [| | ???? Hred Hstep]; subst.
  { by apply Hnext. }
  apply ax_further.
  { intros m' a ?. apply (red_subrel (cstep_in_ctx δ k2) _ _).
    destruct (HF k1 φ m m' a) as (b&?&?); eauto. }
  intros m' a S' ? [p _]. destruct (HF k1 φ m m' a) as (b&?&?); auto.
  feed pose proof (cred_preserves_subctx δ k2 (State k1 φ m') S'); eauto.
  feed destruct (Hstep m' b S') as [? k' φ' mf' m2 m2']; auto.
  * by split.
  * econstructor; eauto. apply IH; eauto using ax_S.
Qed.

(** A variant of the previous lemma that is more convenient for backwards
chaining. *)
Lemma ax_compose_cons `(F : ax_frame_cond A) `(G : ax_frame_cond B)
    P Q n φ l E m :
  ax_compose_diagram F G (E :: l) →
  ax F P (E :: l) n (E :: l) φ m →
  (∀ m' φ', P (E :: l) m' φ' → ax G Q l n (E :: l) φ' m') →
  ax G Q l n (E :: l) φ m.
Proof. apply ax_compose; solve_suffix_of. Qed.
Lemma ax_compose_diagram_diag `(F : ax_frame_cond A) k :
  ax_compose_diagram F F k.
Proof. red. eauto. Qed.
Hint Resolve ax_compose_diagram_diag : ax.

(** The predicates [ax] satisfies an abstract version of the frame, weaken, and
conjunction rule. These abstract versions are used to prove the concrete rules
for both the expression and statement judgment. *)
Definition ax_frame_diagram `(F : ax_frame_cond A) `(G : ax_frame_cond B)
    (mf : mem) := ∀ k φ m m' b,
  ⊥ [m; mf] →
  frame G k φ (m ∪ mf) m' b →
  ∃ a, frame F k φ m m' a ∧ ∀ k' φ' m2 m2',
    unframe F k' φ' m2 m2' a →
    unframe G k' φ' (m2 ∪ mf) m2' b ∧ ⊥ [m2; mf].
Lemma ax_frame_diagram_empty `(F : ax_frame_cond A) : ax_frame_diagram F F ∅.
Proof.
  intros ???? a ? Ha. exists a. rewrite (right_id_L ∅ (∪)) in Ha. split; auto.
  intros. rewrite (right_id_L ∅ (∪)). split; auto; solve_mem_disjoint.
Qed.

Lemma ax_frame `(F : ax_frame_cond A) `(G : ax_frame_cond B)
    (P Q : ax_assert) l n k φ m mf :
  ax_frame_diagram F G mf →
  (∀ m φ, ⊥ [m; mf] → P l m φ → Q l (m ∪ mf) φ) →
  ax F P l n k φ m →
  ⊥ [m; mf] →
  ax G Q l n k φ (m ∪ mf).
Proof.
  intros HFG HPQ. revert k φ m. induction n as [|n]; [constructor |].
  intros k φ m Hax ?. inversion Hax as [| |???? Hred Hstep]; subst.
  { by apply ax_done, HPQ. }
  apply ax_further.
  { intros m' a ?. destruct (HFG k φ m m' a) as (b&?&?); eauto. }
  intros m' a S' ? p. destruct (HFG k φ m m' a) as (b&?&Hunframe); auto.
  feed inversion (Hstep m' b S') as [? k' φ' m2 m2' ?]; subst; auto.
  destruct (Hunframe k' φ' m2 m2'); trivial.
  apply mk_ax_next with (m2 ∪ mf); eauto.
  rewrite mem_locks_union by done. solve_elem_of.
Qed.

Lemma ax_weaken {A} (F G : ax_frame_cond A) (P Q : ax_assert) l n k φ m :
  (∀ k φ m m' a, frame G k φ m m' a → frame F k φ m m' a) →
  (∀ k φ m m' a, unframe F k φ m m' a → unframe G k φ m m' a) →
  (∀ m φ, P l φ m → Q l φ m) →
  ax F P l n k φ m → ax G Q l n k φ m.
Proof.
  intros Hf Hunf HPQ. revert k φ m. induction n as [|n]; [constructor |].
  intros k φ m Hax. inversion Hax as [| |???? Hred Hstep]; subst.
  { by apply ax_done, HPQ. }
  apply ax_further; eauto. intros m' a S' ? p.
  feed inversion (Hstep m' a S'); eauto. econstructor; eauto.
Qed.

(** The standard framing condition that just adds an arbitrary frame to the
memory before each step and takes it off after. *)
Definition ax_disjoint_cond: ax_frame_cond mem := {|
  frame k φ m m' mf := m' = m ∪ mf ∧ ⊥ [m; mf];
  unframe k φ m m' mf := m' = m ∪ mf ∧ ⊥ [m; mf]
|}.
Lemma ax_disjoint_cond_frame_diagram mf :
  ax_frame_diagram ax_disjoint_cond ax_disjoint_cond mf.
Proof.
  intros k φ m m' mf' ? [??]; subst. exists (mf ∪ mf'). split; [split|].
  * by rewrite (associative_L (∪)).
  * solve_mem_disjoint.
  * intros k' φ' m2 m2' [??]; subst. simplify_mem_disjoint_hyps.
    split; [split |]; auto with mem. by rewrite <-(associative_L (∪)).
Qed.
Hint Resolve ax_disjoint_cond_frame_diagram : ax.

Lemma ax_and `(F : ax_frame_cond A) (P Q R : ctx → mem → focus → Prop)
  `{Pnf : PropHolds (∀ l φ m m' a,
    P l m φ → frame F l φ m m' a → nf (cstep_in_ctx δ l) (State l φ m'))}
  `{Qnf : PropHolds (∀ l φ m m' a,
    Q l m φ → frame F l φ m m' a → nf (cstep_in_ctx δ l) (State l φ m'))}
    l n k φ m :
  (∀ k φ m, ∃ m' a,  frame F k φ m m' a) →
  (∀ k φ a m1 m2 m', unframe F k φ m1 m' a → unframe F k φ m2 m' a → m1 = m2) →
  (∀ ρ m φ, P ρ m φ → Q ρ m φ → R ρ m φ) →
  ax F P l n k φ m → ax F Q l n k φ m → ax F R l n k φ m.
Proof.
  intros HFex HFuni HPQ. revert k φ m. induction n as [|n]; [constructor |].
  intros k φ m Hax1 Hax2. inversion Hax1 as [| |???? Hred1 Hstep1];
    inversion Hax2 as [| |???? Hred2 Hstep2]; subst.
  * by apply ax_done, HPQ.
  * exfalso. edestruct HFex as (m'&a&?); eauto.
    eapply Pnf, (Hred2 m' a); eauto.
  * exfalso. edestruct HFex as (m'&a&?); eauto.
    eapply Qnf, (Hred1 m' a); eauto.
  * apply ax_further; [done |]. intros m' a S' HF1 p.
    feed destruct (Hstep1 _ _ _ HF1 p) as [?????? HF1']; trivial.
    feed inversion (Hstep2 _ _ _ HF1 p) as [?????? HF1'']; trivial.
    specialize (HFuni _ _ _ _ _ _ HF1' HF1''); subst. econstructor; eauto.
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
  | FPure F => λ _ vs, (emp ∧ ⌜ F vs ≠ None ⌝)%A
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

Lemma lookup_fpure_Some Δ f F : fpure Δ !! f = Some F ↔ Δ !! f = Some (FPure F).
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
  apply map_empty. intro. unfold fpure. by rewrite lookup_merge, lookup_empty.
Qed.
Lemma fassert_disjoint_union Δ1 Δ2 : Δ1 ⊥ Δ2 → fpure Δ1 ⊥ fpure Δ2.
Proof. intros ????. rewrite !lookup_fpure_Some. eauto. Qed.
Lemma fpure_union Δ1 Δ2 : Δ1 ⊥ Δ2 → fpure (Δ1 ∪ Δ2) = fpure Δ1 ∪ fpure Δ2.
Proof.
  intros. apply map_eq. intros f. apply option_eq. intros F.
  by rewrite lookup_fpure_Some, !lookup_union_Some,
    !lookup_fpure_Some by auto using fassert_disjoint_union.
Qed.

Definition fassert_fun_indep (fs : funset) (Pf : fassert) : Prop :=
  match Pf with
  | FImpure _ pre post _ _ =>
    (∀ c vs, FunIndep fs (pre c vs)) ∧ (∀ c vs v, FunIndep fs (post c vs v))
  | FPure _ => True
  end.
Lemma fpre_fun_indep fs Pf c vs :
  fassert_fun_indep fs Pf → FunIndep fs (fpre Pf c vs).
Proof. destruct Pf; simpl. apply _. by intros [??]. Qed.
Lemma fpost_fun_indep fs Pf c vs v :
  fassert_fun_indep fs Pf → FunIndep fs (fpost Pf c vs v).
Proof. destruct Pf; simpl. apply _. by intros [??]. Qed.

Definition fassert_env_fun_indep (fs : funset) : fassert_env → Prop :=
  map_forall (λ _, fassert_fun_indep fs).

Lemma lookup_fpre_fun_indep Δ fs f Pf c vs :
  fassert_env_fun_indep fs Δ → Δ !! f = Some Pf → FunIndep fs (fpre Pf c vs).
Proof. intros HΔ ?. eapply fpre_fun_indep, HΔ; eauto. Qed.
Lemma lookup_fpost_fun_indep Δ fs f Pf c vs v :
  fassert_env_fun_indep fs Δ → Δ !! f = Some Pf →
  FunIndep fs (fpost Pf c vs v).
Proof. intros HΔ ?. eapply fpost_fun_indep, HΔ; eauto. Qed.

(** The predicate [ax_funs n Δ] states that the functions in [Δ] behave
accordingly. Intuitively this means that if a [Call f vs] with [vs] satisfying
the precondition of [f] terminates, then the result is a [Return v] with [v]
satisfying the postcondition of [f]. *)
Inductive ax_fun_post (δp : purefuns) (Pf : fassert) (c : fcommon Pf)
    (vs : list val) (k : ctx) (m : mem) : focus → Prop :=
  mk_ax_fun_P v :
    locks m = ∅ →
    assert_holds δp (fpost Pf c vs v) (get_stack k) m →
    ax_fun_post δp Pf c vs k m (Return v).
Definition ax_funs (n : nat) (Δ : fassert_env) : Prop :=
  ∀ f Pf c vs m k,
    Δ !! f = Some Pf →
    locks m = ∅ →
    assert_holds (fpure Δ) (fpre Pf c vs) (get_stack k) m →
    ax ax_disjoint_cond (ax_fun_post (fpure Δ) Pf c vs) k n k (Call f vs) m.

Instance: PropHolds (∀ l φ m m' mf,
  ax_fun_post δp Pf c vs l m φ → frame ax_disjoint_cond l φ m m' mf →
  nf (cstep_in_ctx δ l) (State l φ m')).
Proof. destruct 1. intros ? [? p]. inv_cstep p. Qed.

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

Lemma ax_fun_union_l_pure δp Δ f Pf c vs l n k φ m :
  fassert_env_fun_indep (dom funset δp) Δ → Δ !! f = Some Pf →
  ax ax_disjoint_cond (ax_fun_post (fpure Δ) Pf c vs) l n k φ m →
    ax ax_disjoint_cond (ax_fun_post (δp ∪ fpure Δ) Pf c vs) l n k φ m.
Proof.
  intros ??. apply ax_weaken; auto. destruct 1; constructor; eauto.
  eapply fun_indep_union_l; eauto using lookup_fpost_fun_indep.
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
    pointwise_relation _ R ==> pointwise_relation _ R) (@directed_pack A).
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
  dassert := dassert_pack P (R indetc%V) R (λ _, False%A).

(** ** The Hoare judgment for statements *)
(** Now the interpretation of the statement Hoare judgment is just taking all
of the previously defined notions together. We require both the program and
the memory to contain no locks at the start. Also, we require all locks to be
released in the end, as each statement that contains an expression always has
a sequence point in the end. *)
Inductive ax_stmt_post (s : stmt) (δp : purefuns) (Pd : dassert)
    (k : ctx) (m : mem) : focus → Prop :=
  mk_ax_stmt_P d :
    up d s →
    locks m = ∅ →
    assert_holds δp (Pd d) (get_stack k) m →
    ax_stmt_post s δp Pd k m (Stmt d s).
Definition ax_stmt_packed (Δ : fassert_env) (Pd : dassert) (s : stmt) : Prop :=
  ∀ n k d m,
    ax_funs n Δ →
    down d s →
    locks s = ∅ →
    locks m = ∅ →
    assert_holds (fpure Δ) (Pd d) (get_stack k) m →
    ax ax_disjoint_cond (ax_stmt_post s (fpure Δ) Pd) k n k (Stmt d s) m.
Notation "Δ \ P ⊨ₚ s" :=
  (ax_stmt_packed Δ P%A s%S)
  (at level 74, P at next level, format "Δ  \  P  ⊨ₚ  '[' s ']'").

Instance: PropHolds (∀ l φ m m' mf,
  ax_stmt_post s δp Pd l m φ → frame ax_disjoint_cond l φ m m' mf →
  nf (cstep_in_ctx δ l) (State l φ m')).
Proof. destruct 1. intros ? [? p]. inv_cstep p. Qed.

Global Instance ax_stmt_packed_proper: Proper
  (pointwise_relation _ (≡@{fpure Δ}) ==> (=) ==> iff) (ax_stmt_packed Δ).
Proof.
  intros Δ. cut (Proper
    (pointwise_relation _ (≡@{fpure Δ}) ==> (=) ==> impl) (ax_stmt_packed Δ)).
  { intros help. by split; apply help. }
  intros Pd Qd E1 ??? Hax ?????????; subst.
  eapply ax_weaken; [| | |apply Hax]; auto.
  * destruct 1; constructor; eauto. by apply E1.
  * by apply E1.
Qed.

Definition ax_stmt Δ R J P s Q := Δ \ dassert_pack P Q R J ⊨ₚ s.
Definition ax_stmt_top Δ P s Q := Δ \ dassert_pack_top P Q ⊨ₚ s.

(* The level is just below logical negation (whose level is 75). *)
Notation "Δ \ R \ J ⊨ₛ {{ P }} s {{ Q }}" :=
  (ax_stmt Δ R%A J%A P%A s%S Q%A)
  (at level 74, J at next level, R at next level,
   format "Δ \  R \  J  ⊨ₛ  '[' {{  P  }} '/'  s  '/' {{  Q  }} ']'").
Notation "Δ ⊨ₜ {{ P }} s {{ Q }}" :=
  (ax_stmt_top Δ P%A s%S Q%A)
  (at level 74, format "Δ  ⊨ₜ  '[' {{  P  }} '/'  s  '/' {{  Q  }} ']'").

Lemma ax_stmt_top_unfold Δ P s Q :
  Δ ⊨ₜ {{ P }} s {{ Q }} ↔ Δ \ Q \ (λ _, False) ⊨ₛ {{ P }} s {{ Q indetc%V }}.
Proof. done. Qed.
Global Instance ax_stmt_proper: Proper
  (pointwise_relation _ (≡@{fpure Δ}) ==> pointwise_relation _ (≡@{fpure Δ}) ==>
     (≡@{fpure Δ}) ==> (=) ==> (≡@{fpure Δ}) ==> iff) (ax_stmt Δ).
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

Lemma ax_stmt_union_l_pure δp Δ s Pd l n k φ m :
  (∀ d, FunIndep (dom funset δp) (Pd d)) →
  fassert_env_fun_indep (dom funset δp) Δ →
  ax ax_disjoint_cond (ax_stmt_post s (δp ∪ fpure Δ) Pd) l n k φ m →
  ax ax_disjoint_cond (ax_stmt_post s (fpure Δ) Pd) l n k φ m.
Proof.
  intros ??. apply ax_weaken; auto.
  destruct 1; constructor; eauto. eapply fun_indep_union_l; eauto.
Qed.

(** ** The Hoare judgment for expressions *)
(** The interpretation of the expression judgment is defined similarly as the
interpretation of the judgment for statements. At the start, we require both
the expression and the memory to be lock free. In the end, the locks in the
memory should exactly match the annotated locations in the final expression
that remain to be unlocked. The latter is important, as an unlock operation at
a sequence point thereby corresponds to unlocking everything. *)
Inductive ax_expr_frame := InExpr (mf mA : mem) | InFun (mf : mem).
Inductive ax_expr_cond_frame (δp : purefuns) (l : ctx) (A : assert)
    (k : ctx) (φ : focus) (m m' : mem) : ax_expr_frame → Prop :=
  | ax_frame_in_expr mA mf :
     m' = m ∪ mf ∪ mA →
     l = k →
     ⊥ [m; mf; mA] →
     assert_holds δp A (get_stack l) mA →
     locks mA = ∅ →
     ax_expr_cond_frame δp l A k φ m m' (InExpr mf mA)
  | ax_frame_in_fun mf :
     m' = m ∪ mf →
     l ≠ k →
     ⊥ [m; mf] →
     ax_expr_cond_frame δp l A k φ m m' (InFun mf).
Inductive ax_expr_cond_unframe (δp : purefuns) (l : ctx) (A : assert)
    (k : ctx) (φ : focus) (m m' : mem) : ax_expr_frame → Prop :=
  | ax_unframe_expr_to_expr mA mf :
     m' = m ∪ mf ∪ mA →
     l = k →
     ⊥ [m; mf; mA] →
     ax_expr_cond_unframe δp l A k φ m m' (InExpr mf mA)
  | ax_unframe_fun_to_expr mA mf :
     m' = m ∪ mf ∪ mA →
     l = k →
     ⊥ [m; mf; mA] →
     assert_holds δp A (get_stack l) mA →
     locks mA = ∅ →
     ax_expr_cond_unframe δp l A k φ m m' (InFun mf)
  | ax_unframe_expr_to_fun m'' mA mf :
     m = m'' ∪ mA →
     m' = m'' ∪ mf ∪ mA →
     l ≠ k →
     ⊥ [m''; mf; mA] →
     ax_expr_cond_unframe δp l A k φ m m' (InExpr mf mA)
  | ax_unframe_fun_to_fun mf :
     m' = m ∪ mf →
     l ≠ k →
     ⊥ [m; mf] →
     ax_expr_cond_unframe δp l A k φ m m' (InFun mf).
Definition ax_expr_cond (δp : purefuns) (l : ctx)
    (A : assert) : ax_frame_cond ax_expr_frame := {|
  frame := ax_expr_cond_frame δp l A;
  unframe := ax_expr_cond_unframe δp l A
|}.

Definition ax_expr_funframe (δp : purefuns) (A : assert) (k : ctx) (m : mem) :=
  ∃ mA, ⊥ [mA; m] ∧ locks mA = ∅ ∧ assert_holds δp A (get_stack k) mA.
Lemma ax_expr_funframe_emp δp k m : ax_expr_funframe δp emp k m.
Proof. eexists ∅. rewrite mem_locks_empty. solve_assert. Qed.
Hint Resolve ax_expr_funframe_emp : ax.
Lemma ax_expr_funframe_weaken δp A k m1 m2 :
  ax_expr_funframe δp A k m2 → m1 ⊆ m2 → ax_expr_funframe δp A k m1.
Proof. intros (mA&?&?&?) Hm12. exists mA. by rewrite Hm12. Qed.

Lemma ax_disjoint_expr_compose_diagram δp E l A :
  ax_compose_diagram ax_disjoint_cond (ax_expr_cond δp l A) (E :: l).
Proof.
  intros k φ a m m' ?. simpl. inversion 1; subst.
  * simplify_suffix_of.
  * exists mf. split; [done|]. intros k' φ' m2 m2' ? [??]; subst.
    constructor; trivial. intro; simplify_suffix_of.
Qed.
Lemma ax_expr_disjoint_compose_diagram δp l l' :
  ax_compose_diagram (ax_expr_cond δp l emp) ax_disjoint_cond l'.
Proof.
  intros k φ m m' mf ? [??]; subst. simpl. destruct (decide (l = k)); subst.
  * exists (InExpr mf ∅). split.
    { constructor; auto with mem.
      + by rewrite (right_id_L ∅ (∪)).
      + solve_assert.
      + by rewrite mem_locks_empty. }
    intros k' φ' m2 m2' _. inversion 1; subst.
    + rewrite (right_id_L ∅ (∪)); auto with mem.
    + rewrite !(right_id_L ∅ (∪)). auto with mem.
  * exists (InFun mf). split; [by constructor |].
    intros k' φ' m2 m2' _. inversion 1; unfold_assert in *; subst; [|done].
    rewrite (right_id_L ∅ (∪)); auto with mem.
Qed.
Lemma ax_expr_cond_frame_diagram_simple δp l B mf :
  ax_frame_diagram (ax_expr_cond δp l B) (ax_expr_cond δp l B) mf.
Proof.
  intros k φ m m' ?. destruct 2 as [mA mf'|mf']; subst.
  * simplify_mem_disjoint_hyps. exists (InExpr (mf ∪ mf') mA). split.
    { constructor; auto with mem. by rewrite (associative_L (∪)). }
    intros k' φ' m2 m2'.
    inversion 1 as [| |m''|]; simplify_mem_disjoint_hyps; subst.
    + split; [|solve_mem_disjoint].
      apply ax_unframe_expr_to_expr; auto with mem.
      by rewrite (associative_L (∪)).
    + split; [|solve_mem_disjoint].
      apply ax_unframe_expr_to_fun with (m'' ∪ mf); auto with mem.
      - rewrite <-!(associative_L (∪)).
        by rewrite (mem_union_commutative mA) by solve_mem_disjoint.
      - by rewrite !(associative_L (∪)).
  * simplify_mem_disjoint_hyps. exists (InFun (mf ∪ mf')). split.
    { constructor; auto with mem. by rewrite (associative_L (∪)). }
    intros k' φ' m2 m2'.
    inversion 1 as [|mA| |]; simplify_mem_disjoint_hyps; subst.
    + split; [|solve_mem_disjoint].
      apply ax_unframe_fun_to_expr with mA; auto with mem.
      by rewrite (associative_L (∪)).
    + split; [|solve_mem_disjoint].
      apply ax_unframe_fun_to_fun; auto with mem.
      by rewrite (associative_L (∪)).
Qed.
Hint Resolve ax_disjoint_expr_compose_diagram : ax.
Hint Resolve ax_expr_disjoint_compose_diagram : ax.
Hint Resolve ax_expr_cond_frame_diagram_simple : ax.

Inductive ax_expr_post (δp : purefuns) (Q : val → assert)
    (k : ctx) (m : mem) : focus → Prop :=
  mk_ax_expr_P v Ω :
    locks m = Ω →
    assert_holds δp (Q v) (get_stack k) m →
    ax_expr_post δp Q k m (Expr (valc@{Ω} v)).
Definition ax_expr (Δ : fassert_env) (A P : assert)
    (e : expr) (Q : val → assert) : Prop :=
  ∀ n k m,
    ax_funs n Δ →
    locks e = ∅ →
    locks m = ∅ →
    ax_expr_funframe (fpure Δ) A k m →
    assert_holds (fpure Δ) P (get_stack k) m →
    ax (ax_expr_cond (fpure Δ) k A) (ax_expr_post (fpure Δ) Q) k n k (Expr e) m.
Notation "Δ \ A ⊨ₑ {{ P }} e {{ Q }}" := (ax_expr Δ A%A P%A e%E Q%A)
  (at level 74, A at next level,
  format "Δ \  A  ⊨ₑ  '[' {{  P  }} '/'  e  '/' {{  Q  }} ']'").

Instance: PropHolds (∀ l φ m m' mf,
  ax_expr_post δp Q l m φ →
  frame (ax_expr_cond δp l' A) l φ m m' mf →
  nf (cstep_in_ctx δ l) (State l φ m')).
Proof. destruct 1. intros. apply cnf_val. Qed.

Global Instance ax_expr_proper: Proper ((≡@{fpure Δ}) ==> (≡@{fpure Δ}) ==>
  (=) ==> pointwise_relation _ (≡@{fpure Δ}) ==> iff) (ax_expr Δ).
Proof.
  intros Δ. cut (Proper ((≡@{fpure Δ}) ==> (≡@{fpure Δ}) ==>
    (=) ==> pointwise_relation _ (≡@{fpure Δ}) ==> impl) (ax_expr Δ)).
  { intros help. by split; apply help. }
  intros A1 A2 E1 P1 P2 E2 ??? Q1 Q2 E3 Hax ?????? (?&?&?&?) ?; subst.
  eapply ax_weaken; [| | |apply Hax]; auto.
  * destruct 1; constructor; auto. by apply E1.
  * destruct 1; econstructor (first [by eauto | by apply E1]).
  * destruct 1; constructor; auto. by apply E3.
  * repeat esplit; eauto. by apply E1.
  * by apply E2.
Qed.

Lemma ax_expr_post_is_value δp Q ρ m e :
  ax_expr_post δp Q ρ m (Expr e) → is_value e.
Proof. by inversion 1. Qed.
Lemma ax_expr_val δp A P n k v Ω m :
  ax_expr_funframe δp A k m →
  ax (ax_expr_cond δp k A) (ax_expr_post δp P) k (S n) k (Expr (valc@{Ω} v)) m →
  assert_holds δp (P v) (get_stack k) m.
Proof.
  intros (mA&?&?&?). inversion 1 as [|??? [????]|???? Hred]; subst; auto.
  destruct (cnf_val δ k Ω v (m ∪ mA)). apply Hred with (InExpr ∅ mA).
  constructor; auto with mem. by rewrite (right_id_L ∅ (∪)).
Qed.
Lemma ax_expr_val_locks δp A P n k v Ω m :
  ax_expr_funframe δp A k m →
  ax (ax_expr_cond δp k A) (ax_expr_post δp P) k (S n) k (Expr (valc@{Ω} v)) m →
  locks m = Ω.
Proof.
  intros (mA&?&?&?). inversion 1 as [|??? [????]|???? Hred]; subst; auto.
  destruct (cnf_val δ k Ω v (m ∪ mA)). apply Hred with (InExpr ∅ mA).
  constructor; auto with mem. by rewrite (right_id_L ∅ (∪)).
Qed.

Lemma ax_expr_union_l_pure δp Δ A Q l n k φ m :
  (∀ v, FunIndep (dom funset δp) (Q v)) → FunIndep (dom funset δp) A →
  fassert_env_fun_indep (dom funset δp) Δ →
  ax (ax_expr_cond (δp ∪ fpure Δ) k A)
    (ax_expr_post (δp ∪ fpure Δ) Q) l n k φ m →
  ax (ax_expr_cond (fpure Δ) k A) (ax_expr_post (fpure Δ) Q) l n k φ m.
Proof.
  intros ???. apply ax_weaken; auto.
  * destruct 1; constructor; eauto. eapply fun_indep_union_l; eauto.
  * destruct 1; try econstructor (eauto; eapply fun_indep_union_l; eauto).
  * destruct 1; constructor; eauto. eapply fun_indep_union_l; eauto.
Qed.

(** The lemma [ax_expr_compose] is used to prove the structural Hoare rules for
expressions. It is proven by chasing all (interleaved) reduction paths for the
compound expression. This is done step-wise by distinguishing the following
cases:

- All subexpressions are values.
- Some subexpression contains a redex that is not a function call.
- Some subexpression contains a redex that is a function call. In this case we
  use the lemma [ax_call_compose]. *)
Lemma ax_call_compose δp A P Q (E : ectx) E' n φ l k m1 m2 mA :
  locks E' ⊆ locks E ∪ locks m2 →
  ⊥ [m1; m2; mA] →
  ax (ax_expr_cond δp l A) P l n (k ++ [CFun E] ++ l) φ (m1 ∪ mA) →
  (∀ n' m1' e',
    n' ≤ n →
    ⊥ [m1'; m2] →
    ax_expr_funframe δp A l (m1' ∪ m2) →
    locks (subst E e') ⊆ locks m1' →
    ax (ax_expr_cond δp l A) P l n' l (Expr (subst E e')) m1' →
    ax (ax_expr_cond δp l A) Q l n' l (Expr (subst E' e')) (m1' ∪ m2)) →
  ax (ax_expr_cond δp l A) Q l n (k ++ [CFun E'] ++ l) φ (m1 ∪ m2 ∪ mA).
Proof.
  intros HE Hm. rewrite <-(associative_L (∪)),
    (mem_union_commutative m2), (associative_L (∪)) by solve_mem_disjoint.
  cut (⊥ [m1 ∪ mA; m2]); [|solve_mem_disjoint].
  revert φ k. generalize (m1 ∪ mA). clear m1 mA Hm.

  induction n as [|n IH]; [intros; apply ax_O |].
  intros m1 φ k ? Hax Hnext.
  inversion Hax as [| |???? Hred Hstep]; simplify_list_equality.
  apply ax_further.
  { intros m' a Hframe; inversion_clear Hframe; simplify_list_equality.
    simplify_mem_disjoint_hyps.

    destruct (Hred (m1 ∪ m2 ∪ mf) (InFun (m2 ∪ mf))) as [S' p].
    { rewrite <-(associative_L (∪)).
      constructor; auto with mem. intro; simplify_list_equality. }
    apply (cstep_call_inv _ _ E E' _ _ _ _ _ p); intros; subst; red; eauto. }

  intros ?? S' Hframe p;
    inversion_clear Hframe as [mA mf|mf]; simplify_list_equality.
  simplify_mem_disjoint_hyps.

  apply (cstep_call_inv _ _ _ E _ _ _ _ _ p).
  * intros k' φ' m' p'.
    feed inversion (Hstep (m1 ∪ m2 ∪ mf) (InFun (m2 ∪ mf))
      (State (k' ++ [CFun E] ++ l) φ' m'))
      as [??? m1' ?? Hunframe]; subst; trivial.
    { constructor; auto with mem.
      + by rewrite (associative_L (∪)).
      + intro; simplify_list_equality. }
    inversion_clear Hunframe as [|mA| |]; simplify_list_equality.
    simplify_mem_disjoint_hyps.

    apply mk_ax_next with (m1' ∪ m2); trivial.
    + apply ax_unframe_fun_to_fun; auto with mem.
      - by rewrite (associative_L (∪)).
      - intro; simplify_list_equality.
    + rewrite mem_locks_union by solve_mem_disjoint. esolve_elem_of.
    + apply IH; auto with mem.
  * intros v ? ? p'; subst.
    feed inversion (Hstep (m1 ∪ m2 ∪ mf) (InFun (m2 ∪ mf))
      (State l (Expr (subst E (valc v)%E))
      (m1 ∪ (m2 ∪ mf)))) as [??? m1' ?? Hunframe _ Hlocks]; subst; trivial.
    { constructor; auto with mem.
      + by rewrite (associative_L (∪)).
      + intro; simplify_list_equality. }
    { by rewrite (associative_L (∪)). }

    inversion_clear Hunframe as [|mA ? Hm| |]; simplify_list_equality.
    simplify_mem_disjoint_hyps.

    assert (m1 = m1' ∪ mA); subst.
    { apply mem_union_cancel_r with (m2 ∪ mf); auto with mem.
      rewrite <-(associative_L (∪)).
      rewrite (mem_union_commutative mA) by solve_mem_disjoint.
      by rewrite (associative_L (∪) m1'). }
    simplify_mem_disjoint_hyps.

    apply mk_ax_next with (m1' ∪ m2).
    + apply ax_unframe_fun_to_expr with mA; auto with mem.
      by rewrite !(associative_L (∪)) in Hm.
    + done.
    + rewrite mem_locks_union by solve_mem_disjoint. revert Hlocks HE. clear.
      simpl. rewrite !ectx_subst_locks. esolve_elem_of.
    + eapply Hnext; auto with mem. exists mA; auto with mem.
Qed.

Lemma ax_expr_compose n {vn} δp A (Ps : vec vassert vn) (Q : vassert)
    (E : ectx_full vn) (es : vec expr vn) (l : ctx) (ms : vec mem vn) :
  locks E = ∅ →
  ⊥ ms →
  ax_expr_funframe δp A l (⋃ ms) →
  (∀ i, locks (es !!! i) ⊆ locks (ms !!! i)) →
  (∀ i, ax (ax_expr_cond δp l A) (ax_expr_post δp (Ps !!! i)) l n l
           (Expr (es !!! i)) (ms !!! i)) →
  (∀ (Ωs : vec _ vn) (vs : vec val vn) (ms' : vec mem vn),
    ⊥ ms' →
    (∀ i, locks (ms' !!! i) = Ωs !!! i) →
    (∀ i, assert_holds δp ((Ps !!! i) (vs !!! i)) (get_stack l) (ms' !!! i)) →
    ax (ax_expr_cond δp l A) (ax_expr_post δp Q) l n l
       (Expr (depsubst E (vzip_with EVal Ωs vs)%E)) (⋃ ms')) →
  ax (ax_expr_cond δp l A) (ax_expr_post δp Q) l n l
     (Expr (depsubst E es)) (⋃ ms).
Proof.
  intros HE. revert es ms.
  induction n as [[|n] IH] using lt_wf_ind; [intros; apply ax_O |].

  intros es ms ? HA Hes Hax1 Hax2.
  destruct (expr_vec_values es) as [(Ωs&vs&?)|[i Hi]]; subst.
  { apply Hax2.
    + done.
    + intros i. specialize (Hax1 i). rewrite vlookup_zip_with in Hax1.
      eauto using
        ax_expr_val_locks, ax_expr_funframe_weaken, mem_subseteq_lookup_vec.
    + intros i. specialize (Hax1 i). rewrite vlookup_zip_with in Hax1.
      eauto using
        ax_expr_val, ax_expr_funframe_weaken, mem_subseteq_lookup_vec. }

  apply ax_further.
  { intros ?? Hframe; inversion_clear Hframe; simplify_list_equality.
    simplify_mem_disjoint_hyps.
    rewrite (ectx_full_to_item_correct _ _ i). apply (cred_ectx _ [_]).
    eapply (ax_red (ax_expr_cond δp l A) (ax_expr_post δp (Ps !!! i)) _ n)
      with (ms !!! i) (InExpr (⋃ delete (i:nat) (ms:list _) ∪ mf) mA), Hax1.
    + econstructor; eauto.
      - by rewrite !(associative_L (∪)),
          mem_union_delete_vec by solve_mem_disjoint.
      - rewrite <-mem_disjoint_union_le, <-mem_disjoint_union_list_le.
        rewrite app_comm_cons, mem_disjoint_delete_vec; solve_mem_disjoint.
    + contradict Hi; eauto using ax_expr_post_is_value. }

  intros m' a S' Hframe p;
    inversion_clear Hframe as [mA mf ?? Hm|]; simplify_list_equality.
  simplify_mem_disjoint_hyps.

  apply (cstep_expr_depsubst_inv _ _ _ _ _ _ _ p); clear p.
  * clear i Hi. intros i e' m2 p'.
    rewrite <-(mem_disjoint_delete_vec _ i) in Hm.

    feed inversion (ax_step (ax_expr_cond δp l A) (ax_expr_post δp (Ps !!! i))
      l n l (Expr (es !!! i)) (ms !!! i)
      (ms !!! i ∪ ⋃ delete (i:nat) (ms:list _) ∪ mf ∪ mA)
      (InExpr (⋃ delete (i:nat) (ms:list _) ∪ mf) mA)
      (State l (Expr e') m2)) as [??? m ?? Hunframe _]; subst.
    { constructor; auto with mem. by rewrite (associative_L (∪)). }
    { by rewrite mem_union_delete_vec. }
    { auto. }

    inversion_clear Hunframe; simplify_list_equality.
    simplify_mem_disjoint_hyps.
    apply mk_ax_next with (m ∪ ⋃ delete (i:nat) (ms:list _)).
    { constructor; auto with mem. by rewrite (associative_L (∪)). }
    { done. }
    { simpl. rewrite ectx_full_subst_locks, HE, (left_id_L ∅ (∪)).
      rewrite <-mem_union_insert_vec by solve_mem_disjoint.
      rewrite mem_locks_union_list
        by (rewrite mem_disjoint_insert_vec; solve_mem_disjoint).
      apply union_list_preserving, Forall2_fmap, Forall2_vlookup.
      intros j. destruct (decide (i = j)); subst.
      + by rewrite !vlookup_insert.
      + by rewrite !vlookup_insert_ne. }
    rewrite <-mem_union_insert_vec by solve_mem_disjoint.

    apply IH; auto with arith.
    + rewrite mem_disjoint_insert_vec; solve_mem_disjoint.
    + exists mA. split; [|done].
      rewrite <-mem_disjoint_union_list_le.
      rewrite mem_disjoint_insert_vec. solve_mem_disjoint.
    + intros j. destruct (decide (i = j)); subst.
      - by rewrite !vlookup_insert.
      - by rewrite !vlookup_insert_ne.
    + intros j. destruct (decide (i = j)); subst.
      - by rewrite !vlookup_insert.
      - rewrite !vlookup_insert_ne by done. apply ax_S, Hax1.
    + intros ωs vs ms' ???. by apply ax_S, Hax2.
  * clear i Hi. intros i E' f Ωs vs ? HΩs p.
    rewrite <-(mem_disjoint_delete_vec _ i) in Hm.

    assert (⋃ Ωs ⊆ locks (ms !!! i)).
    { transitivity (locks (es !!! i)); [|done].
      rewrite HΩs. rewrite ectx_subst_locks. simpl.
      rewrite zip_with_fmap_fst by done. apply union_subseteq_r. }

    apply mk_ax_next with
      (mem_unlock (⋃ Ωs) (ms !!! i) ∪ ⋃ delete (i:nat) (ms:list _) ∪ mA).
    { eapply ax_unframe_expr_to_fun; eauto.
      + rewrite <-!(associative_L (∪)).
        rewrite <-!mem_unlock_union_l by auto with mem.
        by rewrite !(associative_L (∪)),
          mem_union_delete_vec by solve_mem_disjoint.
      + intro; simplify_list_equality.
      + rewrite <-mem_disjoint_union_le, <-mem_disjoint_union_list_le.
        rewrite <-mem_disjoint_unlock. solve_mem_disjoint. }
    { done. }
    { simpl. apply subseteq_empty. }

    apply ax_call_compose with (P:=ax_expr_post δp (Ps !!! i)) (k:=[]) (E:=E').
    { rewrite locks_snoc. apply union_preserving_l.
      rewrite ectx_full_to_item_locks, HE, (left_id_L ∅ (∪)).
      rewrite mem_locks_union_list by solve_mem_disjoint.
      apply union_list_preserving, Forall2_fmap, Forall2_delete.
      apply Forall2_vlookup; auto. }
    { rewrite <-mem_disjoint_unlock; solve_mem_disjoint. }
    { feed inversion (ax_step (ax_expr_cond δp l A) (ax_expr_post δp (Ps !!! i))
        l n l (Expr (es !!! i)) (ms !!! i)
        (⋃ ms ∪ mf ∪ mA) (InExpr (⋃ delete (i:nat) (ms:list _) ∪ mf) mA)
        (State (CFun E' :: l) (Call f vs) (mem_unlock (⋃ Ωs) (⋃ ms ∪ mf ∪ mA))))
        as [??? m ?? Hunframe _]; trivial; subst.
      { constructor; auto with mem. by rewrite (associative_L (∪)),
          mem_union_delete_vec by solve_mem_disjoint. }

      inversion_clear Hunframe; simplify_list_equality.
      simplify_mem_disjoint_hyps.
      replace (mem_unlock (⋃ Ωs) (ms !!! i)) with m''; [done|].
      apply mem_union_cancel_r with (⋃ delete (i:nat) (ms:list _) ∪ mf ∪ mA).
      { solve_mem_disjoint. }
      { rewrite <-mem_disjoint_unlock; solve_mem_disjoint. }
      rewrite <-mem_unlock_union_l by auto with mem.
      rewrite (associative_L (∪) m''), !(associative_L (∪) (ms !!! i)).
      by rewrite mem_union_delete_vec by solve_mem_disjoint. }

    intros n' m' e' ???? Hax. simplify_mem_disjoint_hyps.
    rewrite <-mem_union_insert_vec by solve_mem_disjoint.

    rewrite subst_snoc, <-ectx_full_to_item_correct_alt.
    apply IH; auto with arith.
    + rewrite mem_disjoint_insert_vec; solve_mem_disjoint.
    + by rewrite mem_union_insert_vec by solve_mem_disjoint.
    + intros j. destruct (decide (i = j)); simplify_equality.
      - by rewrite !vlookup_insert.
      - by rewrite !vlookup_insert_ne.
    + intros j. destruct (decide (i = j)); simplify_equality.
      - by rewrite !vlookup_insert.
      - rewrite !vlookup_insert_ne by done.
        apply ax_le with (S n); auto with arith.
    + intros ωs' vs' ms' ???.
      apply ax_le with (S n); auto with arith.
  * intros ωs vs Hvs. destruct Hi. by rewrite Hvs, vlookup_zip_with.
  * clear i Hi. intros i p. destruct (ax_step_undef (ax_expr_cond δp l A)
      (ax_expr_post δp (Ps !!! i)) l n l (Expr (es !!! i))
      (ms !!! i) (⋃ ms ∪ mf ∪ mA)
      (InExpr (⋃ delete (i:nat) (ms:list _) ∪ mf) mA) l
      (⋃ ms ∪ mf ∪ mA)); trivial.
    constructor; auto.
    + by rewrite (associative_L (∪)),
        mem_union_delete_vec by solve_mem_disjoint.
    + rewrite <-(mem_disjoint_delete_vec _ i) in Hm. solve_mem_disjoint.
Qed.

(** * Partial program correctness *)
(** We prove that the interpretation of the statement Hoare judgment indeed
implies partial program correctness. *)
Lemma ax_stmt_sound_sep P Q s m mf S' :
  ∅ ⊨ₜ {{ P }} s {{ Q }} →
  locks s = ∅ → locks m = ∅ → ⊥ [m; mf] →
  assert_holds ∅ P [] m →
  δ ⊢ₛ State [] (Stmt ↘ s) (m ∪ mf) ⇒* S' →
    (∃ m', S' = State [] (Stmt ↗ s) (m'∪mf) ∧ assert_holds ∅ (Q indetc%V) [] m')
  ∨ (∃ m' v, S' = State [] (Stmt (⇈ v) s) (m'∪mf) ∧ assert_holds ∅ (Q v) [] m')
  ∨ red (cstep δ) S'.
Proof.
  intros Hax Hs Hm ? ? p. apply rtc_bsteps in p. destruct p as [n p].
  feed inversion (ax_steps ax_disjoint_cond
    (ax_stmt_post s ∅ (dassert_pack_top P Q)) n 1 [] [] (Stmt ↘ s)
    m (m ∪ mf) mf S') as [?????? [??] ?? Hax']; subst; try done.
  * simpl. esolve_elem_of.
  * rewrite <-fpure_empty. apply Hax; auto with ax.
    simpl. by rewrite fpure_empty.
  * by apply (bsteps_subrel (cstep δ) _ _).
  * inversion Hax' as [|??? [d' ??]|???? Hred]; subst.
    { destruct d'; naive_solver. }
    right; right. eapply (red_subrel (cstep_in_ctx δ []) _ _), Hred.
    split; eauto.
Qed.
Lemma ax_stmt_sound P R s m S' :
  ∅ ⊨ₜ {{ P }} s {{ R }} →
  locks s = ∅ → locks m = ∅ →
  assert_holds ∅ P [] m →
  δ ⊢ₛ State [] (Stmt ↘ s) m ⇒* S' →
    (∃ m', S' = State [] (Stmt ↗ s) m' ∧ assert_holds ∅ (R indetc%V) [] m')
  ∨ (∃ m' v, S' = State [] (Stmt (⇈ v) s) m' ∧ assert_holds ∅ (R v) [] m')
  ∨ red (cstep δ) S'.
Proof.
  intros ???? p. rewrite <-(right_id_L ∅ (∪) m) in p.
  destruct (ax_stmt_sound_sep P R s m ∅ S') as [[? [E ?]]|[[?[?[E ?]]]|]];
    try rewrite (right_id_L ∅ (∪)) in E; intuition eauto with mem.
Qed.

Lemma ax_stmt_looping_sep P s m mf :
  ∅ ⊨ₜ {{ P }} s {{ λ _, False }} →
  locks s = ∅ → locks m = ∅ → ⊥ [m; mf] →
  assert_holds ∅ P [] m →
  looping (cstep δ) (State [] (Stmt ↘ s) (m ∪ mf)).
Proof.
  intros Hax ????. apply looping_alt. intros S' p.
  destruct (ax_stmt_sound_sep P (λ _, False)%A s m mf S')
    as [[??]|[[?[??]]|?]]; by intuition.
Qed.
Lemma ax_stmt_looping P s m :
  ∅ ⊨ₜ {{ P }} s {{ λ _, False }} →
  locks s = ∅ → locks m = ∅ →
  assert_holds ∅ P [] m →
  looping (cstep δ) (State [] (Stmt ↘ s) m).
Proof.
  intros. rewrite <-(right_id_L ∅ (∪) m).
  apply ax_stmt_looping_sep with P; auto with mem.
Qed.

(** * The Hoare rules *)
(** We prove that the Hoare rules are inhabited by the interpretation of the
Hoare judgment. *)
(** ** Logical rules *)
Lemma ax_stmt_weaken_packed Δ Pd Pd' s :
  (∀ d, down d s → Pd' d ⊑@{fpure Δ} Pd d) →
  (∀ d, up d s → Pd d ⊑@{fpure Δ} Pd' d) →
  Δ\ Pd ⊨ₚ s → Δ\ Pd' ⊨ₚ s.
Proof.
  intros Hdown Hup Hax n k d m ?????.
  apply ax_weaken with ax_disjoint_cond (ax_stmt_post s (fpure Δ) Pd); auto.
  * intros ?? []; constructor; try done. by apply Hup.
  * by apply Hax, Hdown.
Qed.

Lemma ax_stmt_weaken_pre Δ R J P P' Q s :
  P' ⊑@{fpure Δ} P →
  Δ\ R\ J ⊨ₛ {{ P }} s {{ Q }} → Δ\ R\ J ⊨ₛ {{ P' }} s {{ Q }}.
Proof. intro. by apply ax_stmt_weaken_packed; intros []. Qed.
Lemma ax_stmt_weaken_post Δ R J P Q Q' s :
  Q ⊑@{fpure Δ} Q' →
  Δ\ R\ J ⊨ₛ {{ P }} s {{ Q }} → Δ\ R\ J ⊨ₛ {{ P }} s {{ Q' }}.
Proof. intro. by apply ax_stmt_weaken_packed; intros []. Qed.

Lemma ax_stmt_packed_frame_r Δ A Pd s : Δ\ Pd ⊨ₚ s → Δ\ (★ A)%A <$> Pd ⊨ₚ s.
Proof.
  intros Hax n k d m HΔ Hd ? Hm Hpre. rewrite directed_fmap_spec in Hpre.
  destruct Hpre as (m1&m2&?&?&?&?); simplify_equality.
  rewrite mem_locks_union in Hm by done. decompose_empty.
  apply ax_frame with ax_disjoint_cond
    (ax_stmt_post s (fpure Δ) Pd); auto with ax.
  intros m ?? []; constructor; trivial.
  + rewrite mem_locks_union by done. by apply empty_union_L.
  + rewrite directed_fmap_spec. by exists m m2.
Qed.
Lemma ax_stmt_packed_frame_l Δ A Pd s : Δ\ Pd ⊨ₚ s → Δ\ (A ★)%A <$> Pd ⊨ₚ s.
Proof.
  intros Hax. apply (ax_stmt_packed_frame_r _ A) in Hax.
  eapply ax_stmt_weaken_packed, Hax.
  { by intros [] ?; unfold fmap; simpl; rewrite (commutative _). }
  { by intros [] ?; unfold fmap; simpl; rewrite (commutative _). }
Qed.
Lemma ax_stmt_frame_r Δ R J A P Q s :
  Δ\ R\ J ⊨ₛ {{ P }} s {{ Q }} →
  Δ\ (λ v, R v ★ A)\ (λ l, J l ★ A) ⊨ₛ {{ P ★ A }} s {{ Q ★ A }}.
Proof. apply ax_stmt_packed_frame_r. Qed.
Lemma ax_stmt_frame_l Δ R J A P Q s :
  Δ\ R \ J ⊨ₛ {{ P }} s {{ Q }} →
  Δ\ (λ v, A ★ R v)\ (λ l, A ★ J l) ⊨ₛ {{ A ★ P }} s {{ A ★ Q }}.
Proof. apply ax_stmt_packed_frame_l. Qed.

Lemma ax_stmt_and Δ R J P Q Q' s :
  Δ\ R\ J ⊨ₛ {{ P }} s {{ Q }} → Δ\ R\ J ⊨ₛ {{ P }} s {{ Q' }} →
  Δ\ R\ J ⊨ₛ {{ P }} s {{ Q ∧ Q' }}.
Proof.
  intros Hax1 Hax2 n k d m ???? Hpre. eapply (ax_and ax_disjoint_cond
    (ax_stmt_post s (fpure Δ) _) (ax_stmt_post s (fpure Δ) _) _);
    [| | |apply Hax1|apply Hax2]; trivial.
  * intros k' φ' m'. exists m'; eexists ∅; simpl.
    rewrite (right_id_L ∅ (∪)); auto with mem.
  * by intros ?????? [??] [??]; simplify_mem_equality.
  * intros ??? [d' ???]; inversion 1; subst.
    constructor; try done; by destruct d'.
  * by destruct d.
  * by destruct d.
Qed.

Lemma ax_stmt_or Δ R J P P' Q s :
  Δ\ R\ J ⊨ₛ {{ P }} s {{ Q }} → Δ\ R\ J ⊨ₛ {{ P' }} s {{ Q }} →
  Δ\ R\ J ⊨ₛ {{ P ∨ P' }} s {{ Q }}.
Proof.
  intros Hax1 Hax2 n k [] m HΔ Hd ?? Hpre; discriminate_down_up.
  * destruct Hpre.
    + apply ax_weaken with ax_disjoint_cond
        (ax_stmt_post s (fpure Δ) (dassert_pack P Q R J)); auto.
      by intros ?? [[] ??]; constructor.
    + apply ax_weaken with ax_disjoint_cond
        (ax_stmt_post s (fpure Δ) (dassert_pack P' Q R J));auto.
      by intros ?? [[] ??]; constructor.
  * apply ax_weaken with ax_disjoint_cond
      (ax_stmt_post s (fpure Δ) (dassert_pack P Q R J)); auto.
    by intros ?? [[] ??]; constructor.
Qed.

Lemma ax_stmt_exist_pre `{!Inhabited A} Δ R J (P : A → assert) Q s :
  (∀ x, Δ\ R\ J ⊨ₛ {{ P x }} s {{ Q }}) → Δ\ R\ J ⊨ₛ {{ ∃ x, P x }} s {{ Q }}.
Proof.
  intros Hax n k [] m HΔ Hd ?? Hpre; discriminate_down_up.
  * destruct Hpre as [x Hpre]. apply ax_weaken with ax_disjoint_cond
      (ax_stmt_post s (fpure Δ) (dassert_pack (P x) Q R J)); auto.
    + by intros ?? [[] ??]; constructor.
    + by apply Hax.
  * destruct (_ : Inhabited A) as [x]. apply ax_weaken with ax_disjoint_cond
      (ax_stmt_post s (fpure Δ) (dassert_pack (P x) Q R J)); auto.
    + by intros ?? [[] ??]; constructor.
    + by apply Hax.
Qed.
Lemma ax_stmt_exist_post `{A} Δ R J P (Q : A → assert) s x :
  Δ\ R\ J ⊨ₛ {{ P }} s {{ Q x }} → Δ\ R\ J ⊨ₛ {{ P }} s {{ ∃ x, Q x }}.
Proof. apply ax_stmt_weaken_post. by apply assert_exist_intro with x. Qed.
Lemma ax_expr_exist_pre {A} Δ (B : assert) (P : A → assert) Q e :
  (∀ x, Δ\ B ⊨ₑ {{ P x }} e {{ Q }}) → Δ\ B ⊨ₑ {{ ∃ x, P x }} e {{ Q }}.
Proof. intros Hax n k m HΔ Hd ?? [x Hpre]. eapply Hax; eauto. Qed.

Lemma ax_expr_weaken Δ P P' A Q Q' e :
  P ⊑@{fpure Δ} P' → (∀ v, Q' v ⊑@{fpure Δ} Q v) →
  Δ\ A ⊨ₑ {{ P' }} e {{ Q' }} → Δ\ A ⊨ₑ {{ P }} e {{ Q }}.
Proof.
  intros HP HQ Hax n k m ?????. apply ax_weaken
    with (ax_expr_cond (fpure Δ) k A) (ax_expr_post (fpure Δ) Q'); auto.
  intros ?? []; constructor; try done. by apply HQ.
Qed.
Lemma ax_expr_weaken_pre Δ A P P' Q e :
  P ⊑@{fpure Δ} P' → Δ\ A ⊨ₑ {{ P' }} e {{ Q }} → Δ\ A ⊨ₑ {{ P }} e {{ Q }}.
Proof. intro. by apply ax_expr_weaken. Qed.
Lemma ax_expr_weaken_post Δ A P Q Q' e :
  (∀ v, Q' v ⊑@{fpure Δ} Q v) →
  Δ\ A ⊨ₑ {{ P }} e {{ Q' }} → Δ\ A ⊨ₑ {{ P }} e {{ Q }}.
Proof. intro. by apply ax_expr_weaken. Qed.

Lemma ax_expr_frame_r Δ B A P Q e :
  Δ\ B ⊨ₑ {{ P }} e {{ λ v, Q v }} → Δ\ B ⊨ₑ {{ P ★ A }} e {{ λ v, Q v ★ A }}.
Proof.
  intros Hax n k m HΔ ? Hm ? (m1&m2&?&?&?&?); simplify_equality.
  rewrite mem_locks_union in Hm by done. decompose_empty.
  apply ax_frame with (ax_expr_cond (fpure Δ) k B)
    (ax_expr_post (fpure Δ) Q); auto with ax.
  * intros m ?? [v ?]. constructor.
    + rewrite mem_locks_union by done. esolve_elem_of.
    + by exists m m2.
  * eauto using ax_expr_funframe_weaken, mem_union_subseteq_l.
Qed.
Lemma ax_expr_frame_l Δ B A P Q e :
  Δ\ B ⊨ₑ {{ P }} e {{ λ v, Q v }} → Δ\ B ⊨ₑ {{ A ★ P }} e {{ λ v, A ★ Q v }}.
Proof. setoid_rewrite (commutative (★))%A. apply ax_expr_frame_r. Qed.

Lemma ax_expr_funframe_r Δ B A P Q e :
  Δ\ A ★ B ⊨ₑ {{ P }} e {{ λ v, Q v }} →
  Δ\ B ⊨ₑ {{ P ★ A }} e {{ λ v, Q v ★ A }}.
Proof.
  cut (∀ δp n l k φ m,
    ax (ax_expr_cond δp l (A ★ B)) (ax_expr_post δp Q) l n k φ m →
    (l = k → ∀ mA,
      ⊥ [m; mA] →
      assert_holds δp A (get_stack k) mA →
      locks mA = ∅ →
      ax (ax_expr_cond δp l B)
         (ax_expr_post δp (λ v, Q v ★ A))%A l n k φ (m ∪ mA))
    ∧ (l ≠ k →
      ax (ax_expr_cond δp l B) (ax_expr_post δp (λ v, Q v ★ A))%A l n k φ m)).
  { intros help Hax n k ? HΔ ? Hm (mB&?&?&?) (m&mA&?&?&?&?); simplify_equality.
    rewrite mem_locks_union in Hm by done; decompose_empty.
    refine (proj1 (help (fpure Δ) n k k (Expr e) m _) _ mA _ _ _); auto.
    apply Hax; auto. exists (mA ∪ mB); split_ands.
    * solve_mem_disjoint.
    * rewrite mem_locks_union by solve_mem_disjoint. by apply empty_union_L.
    * solve_assert. }
  clear P Δ. intros δp n l. induction n as [|n].
  { repeat constructor. }
  intros k φ m Hax. inversion Hax as [|??? [v ???]|???? Hred Hstep]; subst.
  { split; [|done]. intros _ mA ???. apply ax_done. constructor.
    * rewrite mem_locks_union by solve_mem_disjoint. esolve_elem_of.
    * solve_assert. }

  split.
  * intros ? mA ???; subst. apply ax_further.
    { intros ?? Hframe; inversion_clear Hframe as [mB mf|]; simplify_equality.
      simplify_mem_disjoint_hyps.
      rewrite <-!(associative_L (∪) m), (mem_union_commutative mA),
        <-(associative_L (∪) mf), (associative_L (∪) m) by solve_mem_disjoint.
      eapply Hred, ax_frame_in_expr; eauto with mem.
      + solve_assert.
      + rewrite mem_locks_union by solve_mem_disjoint. by apply empty_union_L. }
    intros ?? S' Hframe p; inversion_clear Hframe as [mB mf|];
      simplify_equality; simplify_mem_disjoint_hyps.
    feed inversion (Hstep (m ∪ mA ∪ mf ∪ mB) (InExpr mf (mA ∪ mB)) S')
      as [? k' φ' m' ?? Hunframe]; subst; auto.
    { constructor; auto with mem.
      * by rewrite <-!(associative_L (∪) m), (mem_union_commutative mA),
          <-(associative_L (∪) mf), (associative_L (∪) m) by solve_mem_disjoint.
      * solve_assert.
      * rewrite mem_locks_union by solve_mem_disjoint. by apply empty_union_L. }
    inversion Hunframe as [| |m''|]; subst.
    + apply mk_ax_next with (m' ∪ mA); auto.
      - apply ax_unframe_expr_to_expr; auto with mem.
        by rewrite <-!(associative_L (∪) m'), (mem_union_commutative mA mf),
          !(associative_L (∪)) by solve_mem_disjoint.
      - rewrite mem_locks_union by solve_mem_disjoint. esolve_elem_of.
      - refine (proj1 (IHn _ _ _ _) _ _ _ _ _); auto with mem.
    + apply mk_ax_next with (m'' ∪ mA ∪ mB); auto.
      - apply ax_unframe_expr_to_fun with (m'' ∪ mA); auto with mem.
        by rewrite <-!(associative_L (∪) m''), (mem_union_commutative mA mf),
          !(associative_L (∪)) by solve_mem_disjoint.
      - by rewrite <-(associative_L (∪)).
      - refine (proj2 (IHn _ _ _ _) _); auto with mem.
        by rewrite <-(associative_L (∪)).
  * intros ?. apply ax_further.
    { intros ?? Hframe; inversion_clear Hframe as [|mf]; simplify_equality.
      by eapply Hred, ax_frame_in_fun. }
    intros ?? S' Hframe p; inversion_clear Hframe as [|mf]; simplify_equality.
    feed inversion (Hstep (m ∪ mf) (InFun mf) S')
      as [? k' φ' m' ?? Hunframe]; subst; auto.
    { by apply ax_frame_in_fun. }
    inversion Hunframe as [|????? (mA&mB&?&?&?&?) HmAB| |]; subst.
    rewrite mem_locks_union in HmAB by done; decompose_empty.
    + apply mk_ax_next with (m' ∪ mA); auto.
      - eapply ax_unframe_fun_to_expr with mB; auto with mem.
        by rewrite <-!(associative_L (∪) m'), (mem_union_commutative mA mf),
          !(associative_L (∪)) by solve_mem_disjoint.
      - rewrite mem_locks_union by solve_mem_disjoint. esolve_elem_of.
      - refine (proj1 (IHn _ _ _ _) _ _ _ _ _); auto with mem.
    + apply mk_ax_next with m'; auto.
      - by apply ax_unframe_fun_to_fun.
      - by refine (proj2 (IHn _ _ _ _) _).
Qed.
Lemma ax_expr_funframe_l Δ B A P Q e :
  Δ\ A ★ B ⊨ₑ {{ P }} e {{ λ v, Q v }} →
  Δ\ B ⊨ₑ {{ A ★ P }} e {{ λ v, A ★ Q v }}.
Proof.
  intro. setoid_rewrite (commutative (★))%A. by apply ax_expr_funframe_r.
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
  ax_funs n Δ → ax_funs n (Δ' ∪ Δ).
Proof.
  intros ? Hpure HaxΔ' HΔ.
  induction n as [|n IH]; [by constructor |]. intros f Pf c vs m k Hf Hm Hpre.

  rewrite map_union_commutative, lookup_union_Some in Hf by done.
  destruct Hf as [?|?].
  { rewrite fpure_union in Hpre |- * by done.
    rewrite fun_indep_union_l in Hpre by eauto using lookup_fpre_fun_indep.
    eapply ax_fun_union_l_pure; eauto. }

  destruct (HaxΔ' f Pf c vs) as (sf & Hsf & Hsflocks & Haxsf); trivial.

  apply ax_further.
  { intros. solve_cred. }

  intros ? mf S' [??] p; subst. inv_cstep p; simplify_option_equality.
  match goal with
  | H : alloc_params _ _ _ _ _ |- _ =>
    apply alloc_params_alloc_list in H; destruct H as (?&Hfree&?); subst
  end.

  pose proof (is_free_list_nodup _ _ Hfree).
  rewrite is_free_list_union in Hfree. destruct Hfree.
  rewrite mem_alloc_list_union_l by (by rewrite zip_fst).

  econstructor.
  { split. done. rewrite mem_disjoint_alloc_list; [done|].
    repeat constructor; trivial. rewrite zip_fst by done.
    auto using is_free_list_free. }
  { done. }
  { esolve_elem_of. }

  eapply ax_compose_cons; [|eapply Haxsf; eauto | clear dependent m mf S' f].
  { auto with ax. }
  { auto with ax. }
  { rewrite mem_locks_alloc_list, Hm; by rewrite ?zip_fst. }
  { simpl. eauto using assert_alloc_params_alt. }

  intros m ? [d ?? Hpost]. apply ax_further_pred.
  { intros. solve_cred. }
  intros ? mf S' [??] p; subst.
  destruct d; discriminate_down_up; inv_cstep p.
  * simpl in Hpost. apply assert_free_params in Hpost;
      eauto using Writable_fragment. destruct Hpost.
    rewrite mem_delete_list_union, (mem_delete_list_free mf)
      by eauto using is_free_list_fragment_l, Writable_fragment.
    eapply mk_ax_next_empty; try done.
    { split. done. by rewrite mem_delete_list_subseteq. }
    apply ax_done.
    constructor. by apply mem_locks_delete_list_empty. done.
  * simpl in Hpost; apply assert_free_params in Hpost;
      eauto using Writable_fragment. destruct Hpost.
    rewrite mem_delete_list_union, (mem_delete_list_free mf)
      by eauto using is_free_list_fragment_l, Writable_fragment.
    eapply mk_ax_next_empty; try done.
    { split. done. by rewrite mem_delete_list_subseteq. }
    apply ax_done.
    constructor. by apply mem_locks_delete_list_empty. done.
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
  Δ' ∪ Δ\ Pd ⊨ₚ s → Δ\ Pd ⊨ₚ s.
Proof.
  intros ???? Hax; repeat intro.
  apply ax_stmt_union_l_pure with (fpure Δ'); eauto.
  rewrite <-fpure_union by done. eapply Hax; eauto using ax_funs_add.
  by rewrite fpure_union, fun_indep_union_l by eauto.
Qed.
Lemma ax_expr_funs_add Δ Δ' P A Q e :
  Δ' ⊥ Δ →
  fassert_env_fun_indep (dom _ (fpure Δ')) Δ →
  FunIndep (dom _ (fpure Δ')) A →
  FunIndep (dom _ (fpure Δ')) P →
  (∀ v, FunIndep (dom _ (fpure Δ')) (Q v)) →
  (∀ f Pf c vs,
    Δ' !! f = Some Pf → ∃ sf,
    δ !! f = Some sf ∧
    locks sf = ∅ ∧
    Δ' ∪ Δ ⊨ₜ {{ Π imap (λ i v, var i ↦{Writable} valc v) vs ★ fpre Pf c vs }}
     sf
    {{ λ v, Π imap (λ i _, var i ↦{Writable} -) vs ★ fpost Pf c vs v }}) →
  Δ' ∪ Δ\ A ⊨ₑ {{ P }} e {{ Q }} → Δ\ A ⊨ₑ {{ P }} e {{ Q }}.
Proof.
  intros ?????? Hax ?????? (mA&?&?) ?.
  apply ax_expr_union_l_pure with (fpure Δ'); eauto.
  rewrite <-fpure_union by done. eapply Hax; eauto using ax_funs_add.
  + exists mA. by rewrite fpure_union, fun_indep_union_l by eauto.
  + by rewrite fpure_union, fun_indep_union_l by eauto.
Qed.

Lemma ax_call Δ A f Pf (c : fcommon Pf) {vn} (Ps : vec assert vn)
    (es : vec expr vn) (Qs : vec vassert vn) (Q : list val → assert) R :
  Δ !! f = Some Pf →
  (∀ vs, (A ★ Π vzip_with ($) Qs vs)%A ⊑@{fpure Δ} (fpre Pf c vs ★ Q vs)%A) →
  (∀ vs v, (fpost Pf c vs v ★ Q vs)%A ⊑@{fpure Δ} (A ★ R v)%A) →
  (∀ i, Δ\ A ⊨ₑ {{ Ps !!! i }} es !!! i {{ λ v, (Qs !!! i) v ▷ }}) →
  Δ\ A ⊨ₑ {{ Π Ps }} call f @ es {{ R }}.
Proof.
  intros Hf Hfpre Hfpost Haxs n k m HΔ Hes Hm Hframe Hpre. simpl in Hes.
  apply assert_sep_list_alt_vec in Hpre. destruct Hpre as (ms&?&?&?); subst.

  rewrite empty_union_list_L, Forall_fmap,
    Forall_vlookup in Hes; simpl in Hes.
  rewrite mem_locks_union_list, empty_union_list_L,
    Forall_fmap, Forall_vlookup in Hm by done; simpl in Hm.

  apply (ax_expr_compose n (fpure Δ) A (vmap (assert_unlock ∘) Qs) _
    (DCCall f) es k ms); trivial.
  { esolve_elem_of. }
  { intros i. rewrite vlookup_map. apply Haxs; eauto using
      ax_expr_funframe_weaken, mem_subseteq_lookup_vec. }

  clear dependent ms es. intros Ωs vs ms ? Hms Hax.
  assert (⋃ Ωs = locks (⋃ ms)) as HΩs.
  { rewrite mem_locks_union_list, <-vec_to_list_map by done.
    f_equal; f_equal. apply vec_eq. intros; by rewrite vlookup_map. }

  simpl. rewrite vec_to_list_zip_with.
  pose proof (vec_to_list_same_length Ωs vs).
  apply ax_further_pred.
  { intros. solve_cred. }

  intros m' frame S' Hframe p.
  inversion_clear Hframe as [mA mf|]; simplify_equality; clear frame.
  simplify_mem_disjoint_hyps.

  destruct (Hfpre vs (get_stack k) (mA ∪ mem_unlock (⋃ Ωs) (⋃ ms)))
    as (m1 & m2 & Hm12 & ? & HPf' & HQ); clear Hfpre.
  { exists mA (mem_unlock (⋃ Ωs) (⋃ ms)); split_ands; auto.
    { rewrite <-mem_disjoint_unlock. solve_mem_disjoint. }
    rewrite HΩs, mem_unlock_all_union_list by done.
    apply assert_sep_list_alt_2.
    { by rewrite <-mem_disjoint_unlock_all. }
    rewrite <-vec_to_list_map. apply Forall2_vlookup. intros i.
    rewrite vlookup_map, vlookup_zip_with.
    specialize (Hax i); rewrite vlookup_map in Hax; auto. }

  assert (locks m1 ∪ locks m2 = ∅); decompose_empty.
  { rewrite <-mem_locks_union, Hm12, HΩs by done.
    rewrite mem_locks_union, mem_locks_unlock_all by
      (rewrite <-mem_disjoint_unlock; solve_mem_disjoint). esolve_elem_of. }

  apply (cstep_expr_call_inv _ _ _ _ _ _ _ _ p); clear p.
  * done.
  * assert (⋃ Ωs ⊆ locks (⋃ ms ∪ mf)).
    { rewrite mem_locks_union, <-HΩs by solve_mem_disjoint; solve_elem_of. }
    rewrite mem_unlock_union_l by auto with mem.
    econstructor.
    { apply ax_unframe_expr_to_fun with (mem_unlock (⋃ Ωs) (⋃ ms)).
      + done.
      + by rewrite mem_unlock_union_l by (solve_mem_disjoint || solve_elem_of).
      + intro. discriminate_list_equality.
      + rewrite <-mem_disjoint_unlock. solve_mem_disjoint. }
    { done. }
    { solve_elem_of. }
    rewrite (mem_union_commutative _ mA), <-Hm12 by
      (rewrite <-mem_disjoint_unlock; solve_mem_disjoint).
    clear dependent mA Ωs ms mf S'.

    apply ax_compose_cons with ax_disjoint_cond (λ k' m φ, ∃ m1 m2,
      m1 ∪ m2 = m ∧ ⊥ [m1; m2] ∧ locks m2 = ∅ ∧
      ax_fun_post (fpure Δ) Pf c vs k' m1 φ ∧
      assert_holds (fpure Δ) (Q vs) (get_stack k) m2); auto with ax.
    { apply ax_frame with ax_disjoint_cond
        (ax_fun_post (fpure Δ) Pf c vs); eauto 8 with ax.
      apply ax_pred, HΔ; try done. by apply (stack_indep _ (get_stack k)). }
    clear dependent m1 m2. intros ?? (m1&m2&?&?&?&[v ? Hpost]&?); subst.
    apply (stack_indep _ _ (get_stack k)) in Hpost.
    apply ax_further_pred.
    { intros. solve_cred. }

    intros ?? S' Hframe p.
    inversion_clear Hframe as [|mf ? _ Hm]; simplify_list_equality.
    destruct (Hfpost vs v (get_stack k) (m1 ∪ m2))
      as (m3&m4&Hm34&?&?&?); [solve_assert |].
    rewrite <-Hm34 in p, Hm.
    assert (locks m3 ∪ locks m4 = ∅); decompose_empty.
    { by rewrite <-mem_locks_union, Hm34, mem_locks_union, empty_union_L. }
    clear dependent m1 m2. simplify_mem_disjoint_hyps.

    inv_cstep p. apply mk_ax_next with m4.
    + apply ax_unframe_fun_to_expr with m3; auto with mem.
      by rewrite (mem_union_commutative _ m3),
        (associative_L (∪)) by solve_mem_disjoint.
    + done.
    + solve_elem_of.
    + by apply ax_done; constructor.
  * intros; exfalso; eauto with cstep.
Qed.

(** ** Rules for expressions *)
Lemma ax_expr_base Δ A P e v :
  P ⊑@{fpure Δ} (e ⇓ v)%A → Δ\ A ⊨ₑ {{ P }} e {{ λ v', ⌜v = v'⌝ ∧ P }}.
Proof.
  intros HPeval n k m HΔ He Hm HA HP. cut (∀ e',
    locks e' = ∅ →
    ⟦ e' ⟧ (fpure Δ) (get_stack k) m = Some v →
    ax (ax_expr_cond (fpure Δ) k A)
      (ax_expr_post (fpure Δ) (λ v', (⌜v = v'⌝ ∧ P)%A)) k n k (Expr e') m).
  { intros help. apply help; auto. apply HPeval; solve_assert. }

  clear He HPeval. induction n as [|n IH]; [by constructor |].
  intros e' He' Heval. destruct (decide (is_value e')) as [Hval | Hval].
  { inversion Hval; simplify_expr_equality. by apply ax_done. }

  apply ax_further.
  { intros ?? Hframe. inversion_clear Hframe as [mA mf|]; simplify_equality.
    apply cred_expr_eval with (fpure Δ) v; auto. rewrite <-(associative_L (∪)).
    apply expr_eval_weaken_mem with m; auto with mem. }

  intros ? frame S' Hframe [p Hk].
  inversion_clear Hframe as [mA mf|]; clear frame; simplify_equality.
  assert (is_pure (dom _ (fpure Δ)) e').
  { eapply expr_eval_is_pure, Heval; eauto with mem. }

  revert Hk. pattern S'. apply (cstep_focus_inv _ _ _ _ p); clear p;
    try solve [simpl; intros; simplify_suffix_of].
  * intros E e1 e2 m2 ? p _; subst.
    efeed pose proof ehstep_pure_mem; eauto using ectx_is_pure. subst.
    erewrite ectx_subst_locks, ehstep_pure_locks in He'
      by eauto using ectx_is_pure.

    apply mk_ax_next_empty with m; try done.
    { apply ax_unframe_expr_to_expr; auto with mem. }
    { simpl. by rewrite ectx_subst_locks. }

    apply IH; auto with ax.
    { simpl. by rewrite ectx_subst_locks. }
    eapply ehstep_expr_eval_subst_inv; eauto.
    rewrite <-(associative_L (∪)); auto with mem.
  * intros E f Ωs vs ?? _; subst.
    rewrite ectx_subst_locks in He'; simpl in He'.
    rewrite zip_with_fmap_fst in He' by done.
    rewrite empty_union_L in He'; destruct He' as [HE HΩs].

    rewrite expr_eval_subst in Heval;
      destruct Heval as (w&Heval&?); simpl in Heval.
    destruct (fpure Δ !! f) as [F|] eqn:Hf; simpl in Heval; [|done].
    rewrite lookup_fpure_Some in Hf.
    rewrite mapM_expr_eval_val in Heval by done; simpl in Heval.

    rewrite HΩs, mem_unlock_empty_locks.
    apply mk_ax_next_empty with (m ∪ mA); try done.
    { apply ax_unframe_expr_to_fun with m; auto.
      intro; discriminate_list_equality. }

    apply ax_compose_cons with ax_disjoint_cond
      (λ _ m' φ, m' = m ∪ mA ∧ φ = Return w); auto with ax.
    { rewrite <-(left_id_L ∅ (∪) (m ∪ mA)).
      apply ax_frame with ax_disjoint_cond
        (ax_fun_post (fpure Δ) (FPure F) () vs); auto with ax.
      + intros ??? [?? [??]]. unfold_assert in *; subst.
        rewrite (left_id_L ∅ (∪)). intuition congruence.
      + apply ax_S, HΔ; rewrite ?mem_locks_empty; auto.
        solve_assert auto with congruence.
      + solve_mem_disjoint. }

    intros ?? [??]; subst. apply ax_S, ax_further.
    { intros; solve_cred. }

    clear dependent S'. intros ?? S' Hframe p.
    inversion_clear Hframe as [|mf']; simplify_list_equality.
    simplify_mem_disjoint_hyps. clear dependent mf.

    inv_cstep p. apply mk_ax_next_empty with m.
    { apply ax_unframe_fun_to_expr with mA; auto with mem.
      by rewrite <-!(associative_L (∪) m),
        (mem_union_commutative mA) by solve_mem_disjoint. }
    { done. }
    { simpl. rewrite ectx_subst_locks, HE. clear; solve_elem_of. }

    apply IH; auto with ax.
    simpl. rewrite ectx_subst_locks, HE. clear; solve_elem_of.
  * intros E e1 ?? []; subst.
    apply ehsafe_expr_eval_subst with (fpure Δ) E v; trivial.
    rewrite <-(associative_L (∪)).
    apply expr_eval_weaken_mem with m; auto with mem.
Qed.

Definition assign_assert (vr va : val) (ass : assign) (v' va' : val) : assert :=
  match ass with
  | Assign => ⌜ va' = vr ∧ v' = vr ⌝
  | PreOp op => valc va ⊙{op} valc vr ⇓ va' ∧ ⌜ v' = va' ⌝
  | PostOp op => valc va ⊙{op} valc vr ⇓ va' ∧ ⌜ v' = va ⌝
  end%A.

Lemma ax_assign_aux Δ A ass γ el Pl Ql er Pr Qr R :
  Write ⊆ perm_kind γ →
  Δ\ A ⊨ₑ {{ Pl }} el {{ Ql }} →
  Δ\ A ⊨ₑ {{ Pr }} er {{ Qr }} →
  (∀ a vr, (Ql a ★ Qr vr)%A ⊑@{fpure Δ} (∃ va v' va',
    valc a ↦{γ} valc va ★ (R a v' va' ∧ assign_assert vr va ass v' va'))%A) →
  Δ\ A ⊨ₑ {{ Pl ★ Pr }}
            el ::=@{ass} er
          {{ λ v', ∃ a va', valc a ↦{perm_lock γ} valc va' ★ R a v' va' }}.
Proof.
  intros Hγ Haxl Haxr Hassign n k ? HΔ He Hm HA (m1&m2&?&?&?&?); subst.
  simpl in He. rewrite mem_locks_union in Hm by done. decompose_empty.

  rewrite <-(right_id_L ∅ (∪) m2).
  apply (ax_expr_compose n (fpure Δ) A
    [# Ql;Qr] _ (DCAssign ass) [# el;er] k [# m1;m2]).
  { done. }
  { done. }
  { simpl; by rewrite (right_id_L ∅ (∪)). }
  { simpl; intros; inv_all_vec_fin; esolve_elem_of. }
  { intros; inv_all_vec_fin; simpl; eauto using ax_expr_funframe_weaken,
      mem_union_subseteq_l, mem_union_subseteq_r. }

  clear dependent m1 m2 HΔ Haxl Haxr. intros Ωs vs ms.
  inv_vec Ωs; intros Ω1 Ωs; inv_vec Ωs; intros Ω2 Ωs; inv_vec Ωs.
  inv_vec vs; intros v1 vs; inv_vec vs; intros v2 vs; inv_vec vs.
  inv_vec ms; intros m1 ms; inv_vec ms; intros m2 ms; inv_vec ms.
  simpl. intros Hdisjoint HΩs Hax. rewrite (right_id_L ∅ (∪) m2).
  pose proof (HΩs 0%fin) as HΩl. pose proof (HΩs 1%fin) as HΩr.
  pose proof (Hax 0%fin) as Haxl. pose proof (Hax 1%fin) as Haxr.
  simpl in HΩl, HΩr, Haxl, Haxr. clear HΩs Hax.

  destruct (Hassign v1 v2 (get_stack k) (m1 ∪ m2))
    as (va&v'&va'&m3&m4&Hm3412&Hm34&(a&v&FOO&Ha&?)&HR&Hass); simplify_equality.
  { by exists m1 m2. }
  rewrite <-Hm3412.

  assert (locks ({[a, v, γ]} ∪ m4) = locks m1 ∪ locks m2) as HΩ.
  { by rewrite Hm3412, mem_locks_union by done. }
  revert HΩ; generalize (locks m1) (locks m2); clear dependent m1 m2.
  intros Ω1 Ω2 HΩ.
  assert (perm_kind γ ≠ Locked) by (by inversion Hγ).

  apply ax_further_pred.
  { intros ?? Hframe; inversion_clear Hframe; simplify_equality.
    destruct ass; unfold_assert in Hass; solve_cred. }

  intros ?? S' Hframe p.
  inversion_clear Hframe as [mA mf ?? Hm|]; simplify_equality.
  simplify_mem_disjoint_hyps. inv_cstep p; [inv_ehstep; inv_assign_sem; simpl |].
  * erewrite !mem_lock_insert_union_fragment_l by auto with mem.
    rewrite mem_lock_insert_singleton.
    erewrite mem_disjoint_lock_insert_singleton in Hm by auto with mem.

    rewrite mem_locks_union, mem_locks_singleton_ne in HΩ by done.
    econstructor.
    + apply ax_unframe_expr_to_expr; auto with mem.
    + done.
    + simpl. rewrite mem_locks_union, mem_locks_singleton by auto with mem.
      rewrite <-(associative_L (∪)), <-HΩ. clear; solve_elem_of.
    + apply ax_done. constructor.
      { rewrite mem_locks_union, mem_locks_singleton by auto with mem.
        rewrite <-(associative_L (∪)), <-HΩ. clear; solve_elem_of. }
      solve_assert.
  * simplify_mem_equality.
    erewrite !mem_lock_insert_union_fragment_l by auto with mem.
    rewrite mem_lock_insert_singleton.
    erewrite mem_disjoint_lock_insert_singleton in Hm by auto with mem.

    rewrite mem_locks_union, mem_locks_singleton_ne in HΩ by done.
    econstructor.
    + apply ax_unframe_expr_to_expr; auto with mem.
    + done.
    + simpl. rewrite mem_locks_union, mem_locks_singleton by auto with mem.
      rewrite <-(associative_L (∪)), <-HΩ. clear; solve_elem_of.
    + apply ax_done. constructor.
      { rewrite mem_locks_union, mem_locks_singleton by auto with mem.
        rewrite <-(associative_L (∪)), <-HΩ. clear; solve_elem_of. }
      unfold_assert in Hass; destruct Hass; simplify_option_equality.
      solve_assert.
  * simplify_mem_equality.
    erewrite !mem_lock_insert_union_fragment_l by auto with mem.
    rewrite mem_lock_insert_singleton.
    erewrite mem_disjoint_lock_insert_singleton in Hm by auto with mem.

    rewrite mem_locks_union, mem_locks_singleton_ne in HΩ by done.
    econstructor.
    + apply ax_unframe_expr_to_expr; auto with mem.
    + done.
    + simpl. rewrite mem_locks_union, mem_locks_singleton by auto with mem.
      rewrite <-(associative_L (∪)), <-HΩ. clear; solve_elem_of.
    + apply ax_done. constructor.
      { rewrite mem_locks_union, mem_locks_singleton by auto with mem.
        rewrite <-(associative_L (∪)), <-HΩ. clear; solve_elem_of. }
      unfold_assert in Hass; destruct Hass; simplify_option_equality.
      solve_assert.
  * destruct ass; unfold_assert in Hass; naive_solver eauto 10 with cstep.
Qed.

Lemma ax_assign Δ A γ el Pl Ql er Pr Qr R :
  Write ⊆ perm_kind γ →
  Δ\ A ⊨ₑ {{ Pl }} el {{ Ql }} →
  Δ\ A ⊨ₑ {{ Pr }} er {{ Qr }} →
  (∀ a vr, (Ql a ★ Qr vr)%A ⊑@{fpure Δ} (valc a ↦{γ} - ★ R a vr)%A) →
  Δ\ A ⊨ₑ {{ Pl ★ Pr }}
    el ::= er
  {{ λ v, ∃ a, valc a ↦{perm_lock γ} valc v ★ R a v }}.
Proof.
  intros. set (R' (a v' va' : val) := (R a v' ∧ ⌜ va' = v' ⌝)%A).
  apply ax_expr_weaken_post with
    (λ v', ∃ a va', valc a ↦{perm_lock γ} valc va' ★ R' a v' va')%A.
  { solve_assert. }
  eapply ax_assign_aux; solve_assert.
Qed.
Lemma ax_assign_pre Δ A op γ el Pl Ql er Pr Qr R :
  Write ⊆ perm_kind γ →
  Δ\ A ⊨ₑ {{ Pl }} el {{ Ql }} →
  Δ\ A ⊨ₑ {{ Pr }} er {{ Qr }} →
  (∀ a vr, (Ql a ★ Qr vr)%A ⊑@{fpure Δ} (∃ va va',
    valc a ↦{γ} valc va ★ R a va' ∧ valc va ⊙{op} valc vr ⇓ va')%A) →
  Δ\ A ⊨ₑ {{ Pl ★ Pr }}
    el ::⊙{op}= er
  {{ λ v, ∃ a, valc a ↦{perm_lock γ} valc v ★ R a v }}.
Proof.
  intros. set (R' (a v' va' : val) := (R a v' ∧ ⌜ va' = v' ⌝)%A).
  apply ax_expr_weaken_post with
    (λ v', ∃ a va', valc a ↦{perm_lock γ} valc va' ★ R' a v' va')%A.
  { solve_assert. }
  eapply ax_assign_aux; eauto. solve_assert.
Qed.

Lemma ax_load Δ A γ e P Q :
  perm_kind γ ≠ Locked →
  Δ\ A ⊨ₑ {{ P }} e {{ λ a, ∃ v, Q a v ★ valc a ↦{γ} valc v }} →
  Δ\ A ⊨ₑ {{ P }} load e {{ λ v, ∃ a, Q a v ★ valc a ↦{γ} valc v }}.
Proof.
  intros Hγ Hax n k m ??? HA Hpre. rewrite <-(right_id_L ∅ (∪) m).
  apply (ax_expr_compose n (fpure Δ) A
    [# λ a, ∃ v, Q a v ★ valc a ↦{γ} valc v]%A _ DCLoad [# e] k [# m]).
  { done. }
  { simpl; solve_mem_disjoint. }
  { simpl; by rewrite (right_id_L ∅ (∪)). }
  { intros; inv_all_vec_fin; esolve_elem_of. }
  { intros; inv_all_vec_fin; simpl; auto. }

  clear dependent m Hax. intros Ωs vs ms.
  inv_vec Ωs; intros Ω Ωs; inv_vec Ωs. inv_vec vs; intros v vs; inv_vec vs.
  inv_vec ms; intros m ms; inv_vec ms; simpl; intros _ HΩ Hax.
  rewrite (right_id_L ∅ (∪) m).
  specialize (HΩ 0%fin); simpl in HΩ. specialize (Hax 0%fin); simpl in Hax.

  destruct Hax as (?&m1&?&?&?&?&a'&v'&?&?&?); simpl in *; simplify_equality.
  apply ax_further_pred.
  { intros ?? Hframe; inversion_clear Hframe; simplify_equality.
   solve_cred. }

  intros ?? S' Hframe p; inversion_clear Hframe; simplify_equality.
  inv_cstep p.
  * inv_ehstep; simplify_mem_equality. econstructor.
    + by apply ax_unframe_expr_to_expr.
    + done.
    + done.
    + apply ax_done. constructor. by rewrite mem_locks_union. solve_assert.
  * exfalso; eauto with cstep.
Qed.

Lemma ax_alloc Δ A : Δ\ A ⊨ₑ {{ emp }} alloc {{ λ a, valc a ↦{Freeable} - }}.
Proof.
  intros n k ?? _ _ ? ?; unfold_assert in *; subst.
  apply ax_further_pred.
  { intros; solve_cred. }
  intros ?? S' Hframe p; inversion_clear Hframe; simplify_equality.
  rewrite (left_id_L ∅ (∪)) in p. inv_cstep p.
  * inv_ehstep. rewrite mem_alloc_singleton_l, (associative_L (∪)) by done.
    decompose_is_free. eapply mk_ax_next_empty.
    + apply ax_unframe_expr_to_expr; auto with mem.
      apply mem_disjoint_singleton; [by repeat constructor|]; auto with mem.
    + done.
    + done.
    + apply ax_done. constructor. by apply mem_locks_singleton_ne. solve_assert.
  * exfalso; eauto with cstep.
Qed.

Lemma ax_free Δ A e P Q :
  Δ\ A ⊨ₑ {{ P }} e {{ λ a, Q ★ valc a ↦{Freeable} - }} →
  Δ\ A ⊨ₑ {{ P }} free e {{ λ v, Q }}.
Proof.
  intros Hax n k m ???? Hpre. rewrite <-(right_id_L ∅ (∪) m).
  apply (ax_expr_compose n (fpure Δ) A
    [# λ a, Q ★ valc a ↦{Freeable} -]%A _ DCFree [# e] k [# m]).
  { done. }
  { simpl; solve_mem_disjoint. }
  { simpl; by rewrite (right_id_L ∅ (∪)). }
  { intros; inv_all_vec_fin; esolve_elem_of. }
  { intros; inv_all_vec_fin; simpl; auto. }

  clear dependent m Hax. intros Ωs vs ms.
  inv_vec Ωs; intros Ω Ωs; inv_vec Ωs. inv_vec vs; intros v vs; inv_vec vs.
  inv_vec ms; intros m ms; inv_vec ms; simpl; intros _ HΩs Hax.
  rewrite (right_id_L ∅ (∪) m).

  specialize (Hax 0%fin); simpl in Hax. specialize (HΩs 0%fin); simpl in HΩs.

  destruct Hax as (m1&?&?&?&?&?&a&v'&?&?&?); simpl in *; simplify_equality.
  apply ax_further_pred.
  { intros ?? Hframe; inversion_clear Hframe; simplify_equality.
    solve_cred. }

  intros ?? S' Hframe p; inversion_clear Hframe; simplify_equality.
  simplify_mem_disjoint_hyps. inv_cstep p.
  * inv_ehstep.
    erewrite 2!mem_delete_union_l, mem_delete_union_r by auto with mem.
    rewrite mem_delete_singleton, (right_id_L ∅ (∪)).
    rewrite mem_locks_union, mem_locks_singleton_ne, (right_id_L ∅ (∪)) by done.
    econstructor.
    + apply ax_unframe_expr_to_expr; auto with mem.
    + done.
    + done.
    + by apply ax_done; constructor.
  * exfalso; eauto 10 with cstep.
Qed.

Lemma ax_unop Δ A op e P Q R :
  Δ\ A ⊨ₑ {{ P }} e {{ Q }} →
  (∀ v', Q v' ⊑@{fpure Δ} (∃ v, R v v' ∧ ⊙{op} valc v' ⇓ v)%A) →
  Δ\ A ⊨ₑ {{ P }} ⊙{op} e {{ λ v, ∃ v', R v v' }}.
Proof.
  intros Hax Hop n k m ?????. rewrite <-(right_id_L ∅ (∪) m).
  apply (ax_expr_compose n (fpure Δ) A [# Q] _ (DCUnOp op) [# e] k [# m]).
  { done. }
  { simpl; solve_mem_disjoint. }
  { simpl; by rewrite (right_id_L ∅ (∪)). }
  { intros; inv_all_vec_fin; esolve_elem_of. }
  { intros; inv_all_vec_fin; simpl; auto. }

  clear dependent m Hax e. intros Ωs vs ms.
  inv_vec Ωs; intros Ω Ωs; inv_vec Ωs. inv_vec vs; intros v vs; inv_vec vs.
  inv_vec ms; intros m ms; inv_vec ms.
  simpl. intros _ HΩ Hax. rewrite (right_id_L ∅ (∪) m).
  specialize (HΩ 0%fin); simpl in HΩ. specialize (Hax 0%fin); simpl in Hax.

  destruct (Hop v (get_stack k) m) as (v'&Hv'&?); [done|].
  clear Hop. unfold_assert in *.

  apply ax_further_pred.
  { intros; solve_cred. }

  intros ?? S' Hframe p; inversion_clear Hframe; simplify_equality.
  simplify_mem_disjoint_hyps. inv_cstep p.
  * inv_ehstep. simplify_option_equality. econstructor.
    + apply ax_unframe_expr_to_expr; auto with mem.
    + done.
    + done.
    + apply ax_done; constructor; try done. by exists v.
  * exfalso; eauto with cstep.
Qed.

Lemma ax_binop Δ A op el Pl Ql er Pr Qr R :
  Δ\ A ⊨ₑ {{ Pl }} el {{ Ql }} → Δ\ A ⊨ₑ {{ Pr }} er {{ Qr }} →
  (∀ vl vr, (Ql vl ★ Qr vr)%A
    ⊑@{fpure Δ} (∃ v, R v vl vr ∧ valc vl ⊙{op} valc vr ⇓ v)%A) →
  Δ\ A ⊨ₑ {{ Pl ★ Pr }} el ⊙{op} er {{ λ v, ∃ vl vr, R v vl vr }}.
Proof.
  intros Haxl Haxr Hop n k ??? Hm ? (m1&m2&?&?&?&?); subst.
  rewrite mem_locks_union in Hm by done. simpl in *. decompose_empty.
  rewrite <-(right_id_L ∅ (∪) m2). apply (ax_expr_compose n (fpure Δ) A
    [# Ql;Qr] _ (DCBinOp op) [# el;er] k [# m1;m2]).
  { done. }
  { simpl; solve_mem_disjoint. }
  { simpl; by rewrite (right_id_L ∅ (∪)). }
  { intros; inv_all_vec_fin; esolve_elem_of. }
  { intros; inv_all_vec_fin; simpl; eauto using ax_expr_funframe_weaken,
      mem_union_subseteq_l, mem_union_subseteq_r. }

  clear dependent m1 m2 Haxl Haxr. intros Ωs vs ms.
  inv_vec Ωs; intros Ω1 Ωs; inv_vec Ωs; intros Ω2 Ωs; inv_vec Ωs.
  inv_vec vs; intros v1 vs; inv_vec vs; intros v2 vs; inv_vec vs.
  inv_vec ms; intros m1 ms; inv_vec ms; intros m2 ms; inv_vec ms.
  simpl. intros Hdisjoint HΩs Hax. rewrite (right_id_L ∅ (∪) m2).
  pose proof (HΩs 0%fin) as HΩl. pose proof (HΩs 1%fin) as HΩr.
  pose proof (Hax 0%fin) as Haxl. pose proof (Hax 1%fin) as Haxr.
  simpl in HΩl, HΩr, Haxl, Haxr. clear HΩs Hax.

  destruct (Hop v1 v2 (get_stack k) (m1 ∪ m2)) as (v'&?&?).
  { by exists m1 m2. }
  clear Hop. unfold_assert in *.

  apply ax_further_pred.
  { intros. solve_cred. }

  intros ?? S' Hframe p; inversion_clear Hframe; simplify_equality.
  simplify_mem_disjoint_hyps. inv_cstep p.
  * inv_ehstep. rewrite <-mem_locks_union by done.
    simplify_option_equality. econstructor.
    + apply ax_unframe_expr_to_expr; auto with mem.
    + done.
    + done.
    + apply ax_done; constructor; try done. exists v1 v2. solve_assert.
  * exfalso; eauto with cstep.
Qed.

Lemma ax_expr_if Δ A e el er P (P' : vassert) Q :
  Δ\ A ⊨ₑ {{ P }} e {{ λ v, ⌜ v ≠ indetc ⌝%V ∧ P' v ▷ }} →
  Δ\ A ⊨ₑ {{ assert_is_true P' }} el {{ Q }} →
  Δ\ A ⊨ₑ {{ assert_is_false P' }} er {{ Q }} →
  Δ\ A ⊨ₑ {{ P }} IF e then el else er {{ Q }}.
Proof.
  intros Hax Haxl Haxr n k m HΔ He Hm Hpre HA.
  simpl in He. decompose_empty. rewrite <-(right_id_L ∅ (∪) m).
  apply (ax_expr_compose n (fpure Δ) A
    [# λ v, ⌜ v ≠ indetc ⌝%V ∧ P' v ▷]%A _ (DCIf el er) [# e] k [# m]).
  { simpl; by apply empty_union_L. }
  { simpl; solve_mem_disjoint. }
  { simpl; by rewrite (right_id_L ∅ (∪)). }
  { intros; inv_all_vec_fin; esolve_elem_of. }
  { intros; inv_all_vec_fin; simpl; intuition. }

  clear dependent e m. intros Ωs vs ms.
  inv_vec Ωs; intros Ω Ωs; inv_vec Ωs. inv_vec vs; intros v vs; inv_vec vs.
  inv_vec ms; intros m ms; inv_vec ms; simpl; intros ? HΩ Hax.
  rewrite (right_id_L ∅ (∪) m).
  specialize (Hax 0%fin); simpl in Hax. specialize (HΩ 0%fin); simpl in HΩ.

  apply ax_further_pred.
  { intros ?? Hframe. inversion Hframe; simplify_list_equality.
    destruct (val_true_false_dec v); solve_assert || solve_cred. }

  intros ?? S' Hframe p; inversion_clear Hframe as [mA mf|]; simplify_equality.
  simplify_mem_disjoint_hyps. inv_cstep p.
  * inv_ehstep.
    + rewrite <-(associative_L (∪)), mem_unlock_union_l by auto with mem.
      rewrite (associative_L (∪)). eapply mk_ax_next_empty.
      - apply ax_unframe_expr_to_expr; auto with mem.
        by rewrite <-mem_disjoint_unlock.
      - done.
      - done.
      - apply Haxl; rewrite ?mem_locks_unlock_all; auto with ax.
        { exists mA. rewrite <-mem_disjoint_unlock; auto with mem. }
        solve_assert.
    + rewrite <-(associative_L (∪)), mem_unlock_union_l by auto with mem.
      rewrite (associative_L (∪)). eapply mk_ax_next_empty.
      - apply ax_unframe_expr_to_expr; auto with mem.
        by rewrite <-mem_disjoint_unlock.
      - done.
      - done.
      - apply Haxr; rewrite ?mem_locks_unlock_all; auto with ax.
        { exists mA. rewrite <-mem_disjoint_unlock; auto with mem. }
        solve_assert.
  * exfalso; destruct (val_true_false_dec v); solve_assert eauto with cstep.
Qed.

Lemma ax_expr_comma Δ A el er P P' Q :
  Δ\ A ⊨ₑ {{ P }} el {{ λ v, ⌜ v ≠ indetc ⌝%V ∧ P' ▷ }} →
  Δ\ A ⊨ₑ {{ P' }} er {{ Q }} →
  Δ\ A ⊨ₑ {{ P }} el ,, er {{ Q }}.
Proof.
  intros Haxl Haxr n k m HΔ He Hm Hpre HA.
  simpl in He. decompose_empty. rewrite <-(right_id_L ∅ (∪) m).
  apply (ax_expr_compose n (fpure Δ) A
    [# λ v, ⌜ v ≠ indetc ⌝%V ∧ P' ▷]%A _ (DCComma er) [# el] k [# m]).
  { done.  }
  { simpl; solve_mem_disjoint. }
  { simpl; by rewrite (right_id_L ∅ (∪)). }
  { intros; inv_all_vec_fin; esolve_elem_of. }
  { intros; inv_all_vec_fin; simpl; intuition. }

  clear dependent m. intros Ωs vs ms.
  inv_vec Ωs; intros Ω Ωs; inv_vec Ωs. inv_vec vs; intros v vs; inv_vec vs.
  inv_vec ms; intros m ms; inv_vec ms; simpl; intros ? HΩ Hax.
  rewrite (right_id_L ∅ (∪) m).
  specialize (Hax 0%fin); simpl in Hax. specialize (HΩ 0%fin); simpl in HΩ.

  apply ax_further_pred.
  { intros ?? Hframe. inversion Hframe; simplify_list_equality.
    solve_cred. }

  intros ?? S' Hframe p; inversion_clear Hframe as [mA mf|]; simplify_equality.
  simplify_mem_disjoint_hyps. inv_cstep p.
  * inv_ehstep.
    rewrite <-(associative_L (∪)), mem_unlock_union_l by auto with mem.
    rewrite (associative_L (∪)). eapply mk_ax_next_empty.
    - apply ax_unframe_expr_to_expr; auto with mem.
      by rewrite <-mem_disjoint_unlock.
    - done.
    - done.
    - apply Haxr; rewrite ?mem_locks_unlock_all; auto with ax.
      { exists mA. rewrite <-mem_disjoint_unlock; auto with mem. }
      solve_assert.
  * exfalso; eauto with cstep.
Qed.

(** ** Rules for statements *)
Lemma ax_do Δ R J P Q e :
  Δ\ emp ⊨ₑ {{ P }} e {{ λ _, Q ▷ }} → Δ\ R\ J ⊨ₛ {{ P }} do e {{ Q }}.
Proof.
  intros Hax n k [] m ?? He ??; discriminate_down_up.
  apply ax_further_pred.
  { intros. solve_cred. }
  intros ? mf S' [??] p; subst. inv_cstep p. econstructor; try done.
  { esolve_elem_of. }
  clear dependent mf S'. eapply ax_compose_cons; auto with ax.
  intros m' φ' [v ???]. apply ax_further_pred.
  { intros. solve_cred. }
  intros ? mf S' [??] p. inv_cstep p.
  rewrite mem_unlock_union_l by solve_elem_of.
  eapply mk_ax_next_empty; try done.
  { split. done. by rewrite <-mem_disjoint_unlock. }
  clear dependent m mf φ' v S'.
  apply ax_done; constructor; auto. by rewrite mem_locks_unlock_all.
Qed.

Lemma ax_skip Δ R J P : Δ\ R\ J ⊨ₛ {{ P }} skip {{ P }}.
Proof.
  intros n k [] m ?????; discriminate_down_up.
  apply ax_further_pred.
  { intros. solve_cred. }
  intros m' mf S' [??] p; subst. inv_cstep p.
  eapply mk_ax_next_empty; try done.
  clear dependent mf S'. by apply ax_done; constructor.
Qed.

Lemma ax_ret Δ J P R e Q :
  Δ\ emp ⊨ₑ {{ P }} e {{ λ v, R v ▷ }} → Δ\ R\ J ⊨ₛ {{ P }} ret e {{ Q }}.
Proof.
  intros Hax n k [] m ?? He ??; discriminate_down_up.
  apply ax_further_pred.
  { intros. solve_cred. }
  intros ? mf S' [??] p; subst. inv_cstep p.
  eapply mk_ax_next_empty; try done.
  clear dependent mf S'. eapply ax_compose_cons; eauto with ax.
  intros m' φ' [v ???]. apply ax_further_pred.
  { intros. solve_cred. }
  intros ? mf S' [??] p; subst. inv_cstep p.
  rewrite mem_unlock_union_l by solve_elem_of.
  eapply mk_ax_next_empty; try done.
  { split. done. by rewrite <-mem_disjoint_unlock. }
  clear dependent m mf φ' S'.
  apply ax_done; constructor; auto. by rewrite mem_locks_unlock_all.
Qed.

Lemma ax_packed_blk Δ Pd c s :
  Δ\ (λ P, var O ↦{block_perm c} - ★ P↑)%A <$> Pd ⊨ₚ s → Δ\ Pd ⊨ₚ blk@{c} s.
Proof.
  intros Hax n k. revert n.
  cut (∀ n d m b,
   ax_funs n Δ → is_free m b → down d s → locks s = ∅ → locks m = ∅ →
   assert_holds (fpure Δ) (Pd d) (get_stack k) m →
   ax ax_disjoint_cond (ax_stmt_post (blk@{c} s) (fpure Δ) Pd) k n
     (CBlock c b :: k) (Stmt d s) (mem_alloc b indetc (block_perm c) m)).
  { intros help n d m ?????. apply ax_further_pred.
    { intros. solve_cred. }
    intros ? mf S' [??] p; subst.
    destruct d; discriminate_down_up; inv_cstep p; decompose_is_free.
    * rewrite mem_alloc_union_l by done.
      eapply mk_ax_next_empty; try done.
      { split. done. by rewrite mem_disjoint_alloc by (by repeat constructor). }
      apply help; auto with ax.
    * rewrite mem_alloc_union_l by done.
      eapply mk_ax_next_empty; try done.
      { split. done. by rewrite mem_disjoint_alloc by (by repeat constructor). }
      apply help; auto with ax. }

  intros n d m b v ?????. eapply ax_compose_cons; [| | clear dependent m v d].
  { apply ax_compose_diagram_diag. }
  { eapply Hax; eauto.
    { by rewrite mem_locks_alloc by eauto using block_perm_locked. }
    rewrite directed_fmap_spec. simpl. by apply assert_alloc. }

  intros m φ [d ?? Hpost]. apply ax_further_pred.
  { intros. solve_cred. }

  rewrite directed_fmap_spec in Hpost. simpl in Hpost.
  apply assert_free in Hpost; [|by auto using block_perm_fragment].
  destruct Hpost. intros ? mf S' [??] p; subst.
  destruct d; discriminate_down_up; inv_cstep p.
  * erewrite mem_delete_union_l by eauto using block_perm_fragment.
    eapply mk_ax_next_empty; try done.
    { split. done. by rewrite mem_delete_subseteq. }
    apply ax_done; constructor; try done. by apply mem_locks_delete_empty.
  * erewrite mem_delete_union_l by eauto using block_perm_fragment.
    eapply mk_ax_next_empty; try done.
    { split. done. by rewrite mem_delete_subseteq. }
    apply ax_done; constructor; try done. by apply mem_locks_delete_empty.
  * erewrite mem_delete_union_l by eauto using block_perm_fragment.
    eapply mk_ax_next_empty; try done.
    { split. done. by rewrite mem_delete_subseteq. }
    apply ax_done; constructor; try done. by apply mem_locks_delete_empty.
Qed.
Lemma ax_blk Δ R J P Q c s :
  Δ\ (λ v, var O ↦{block_perm c} - ★ R v↑)\
    (λ l, var O ↦{block_perm c} - ★ J l↑) ⊨ₛ
    {{ var O ↦{block_perm c} - ★ P↑ }} s {{ var O ↦{block_perm c} - ★ Q↑ }} →
  Δ\ R\ J ⊨ₛ {{ P }} blk@{c} s {{ Q }}.
Proof. intros. by apply ax_packed_blk. Qed.

Lemma ax_label Δ R J l s Q :
  Δ\ R\ J ⊨ₛ {{ J l }} s {{ Q }} → Δ\ R\ J ⊨ₛ {{ J l }} l :; s {{ Q }}.
Proof.
  intros Hax n k. revert n.
  set (Pd := dassert_pack (J l) Q R J).
  cut (∀ n d m,
   ax_funs n Δ → down d s → locks s = ∅ → locks m = ∅ →
   assert_holds (fpure Δ) (Pd d) (get_stack k) m →
   ax ax_disjoint_cond (ax_stmt_post (l :; s) (fpure Δ) Pd) k n
     (CStmt (l :; □) :: k) (Stmt d s) m).
  { intros help n d m ?? Hs ??. apply ax_further_pred.
    { intros. clear dependent Pd. solve_cred. }
    intros ?? S' [??] p; simpl in Hs;
    destruct d; discriminate_down_up; inv_cstep p;
      eapply mk_ax_next_empty; try done; auto with ax. }

  induction n as [|n IH]; [constructor |]. intros d m ?????.
  eapply ax_compose_cons; [|by apply Hax | clear dependent m d].
  { auto with ax. }

  intros m φ [d ?? Hpost]. apply ax_further.
  { intros. solve_cred. }

  intros ? mf S' [??] p; subst.
  destruct d; discriminate_down_up; inv_cstep p.
  * eapply mk_ax_next_empty; try done. by apply ax_done.
  * eapply mk_ax_next_empty; try done. by apply ax_done.
  * match goal with
    | _ : ?l' ∉ labels s |- _ => destruct (decide (l' = l))
    end; subst.
    + eapply mk_ax_next_empty; try done. apply ax_further_pred.
      { intros. solve_cred. }
      intros ? mf' S'' [??] p; subst. inv_cstep p.
      eapply mk_ax_next_empty; try done; auto with ax.
    + eapply mk_ax_next_empty; try done.
      apply ax_done; constructor; try done. solve_elem_of.
Qed.

Lemma ax_while Δ R J P Q e s :
  Δ\ emp ⊨ₑ {{ P }} e {{ λ v, ⌜ v ≠ indetc ⌝%V ∧ Q v ▷ }} →
  Δ\ R\ J ⊨ₛ {{ assert_is_true Q }} s {{ P }} →
  Δ\ R\ J ⊨ₛ {{ P }} while (e) s {{ assert_is_false Q }}.
Proof.
  intros Haxe Hax n k. revert n.
  set (Pd := dassert_pack P (assert_is_false Q) R J).
  set (Pd' := dassert_pack (assert_is_true Q) P R J).
  cut (∀ n d m,
   ax_funs n Δ → down d s → locks e = ∅ → locks s = ∅ → locks m = ∅ →
   assert_holds (fpure Δ) (Pd' d) (get_stack k) m →
   ax ax_disjoint_cond (ax_stmt_post (while (e) s) (fpure Δ) Pd) k n
     (CStmt (while (e) □) :: k) (Stmt d s) m).
  { intros help n [] m ?? Hs ??; simpl in Hs;
      decompose_empty; discriminate_down_up.
    * apply ax_further_pred.
      { intros. solve_cred. }
      intros ? mf S' [??] p; subst. inv_cstep p.
      eapply mk_ax_next_empty; try done.
      eapply ax_compose_cons;
        [|apply Haxe; auto with ax | clear dependent m mf S'].
      { auto with ax. }
      intros m φ [v ???]. apply ax_further_pred.
      { intros ?? Hframe. inversion Hframe; simplify_list_equality.
        destruct (val_true_false_dec v); solve_cred || solve_assert. }
      intros ? mf S' [??] p; subst. inv_cstep p.
      + rewrite mem_unlock_union_l by done.
        eapply mk_ax_next_empty; try done.
        { split. done. by rewrite <-mem_disjoint_unlock. }
        apply help; rewrite ?mem_locks_unlock_all; auto with ax. solve_assert.
      + rewrite mem_unlock_union_l by done.
        eapply mk_ax_next_empty; try done.
        { split. done. by rewrite <-mem_disjoint_unlock. }
        { esolve_elem_of. }
        apply ax_done; constructor; rewrite ?mem_locks_unlock_all; try done.
        solve_assert.
    * apply ax_further_pred.
      { intros. solve_cred. }
      intros ? mf S' [??] p; subst. inv_cstep p.
      eapply mk_ax_next_empty; try done; auto with ax. }

  induction n as [|n IH]; [constructor |]. intros d m ??????.
  eapply ax_compose_cons; [|by apply Hax | clear dependent m d].
  { auto with ax. }

  intros m φ [d ?? Hpost]. apply ax_further.
  { intros. solve_cred. }

  intros ? mf S' [??] p; subst. destruct d; discriminate_down_up; inv_cstep p.
  * eapply mk_ax_next_empty; try done.
    { simpl. by apply empty_union_L. }
    clear dependent φ mf S'. apply ax_further_pred.
    { intros. solve_cred. }
    intros ? mf S' [??] p; subst. inv_cstep p.
    eapply mk_ax_next_empty; try done. eapply ax_compose_cons;
      [|apply Haxe; auto with ax | clear dependent m mf S'].
    { auto with ax. }
    intros m φ [v ???]. apply ax_further_pred.
    { intros. destruct (val_true_false_dec v); solve_cred || solve_assert. }
    intros ? mf S' [??] p; subst. inv_cstep p.
    + rewrite mem_unlock_union_l by done.
      eapply mk_ax_next_empty; try done.
      { split. done. by rewrite <-mem_disjoint_unlock. }
      apply ax_pred, ax_pred, IH; rewrite ?mem_locks_unlock_all; auto with ax.
      solve_assert.
    + rewrite mem_unlock_union_l by done.
      eapply mk_ax_next_empty; try done.
      { split. done. by rewrite <-mem_disjoint_unlock. }
      { simpl. by apply empty_union_L. }
      apply ax_done; constructor; rewrite ?mem_locks_unlock_all; try done.
      solve_assert.
  * eapply mk_ax_next_empty; try done; [esolve_elem_of |]. by apply ax_done.
  * eapply mk_ax_next_empty; try done; [esolve_elem_of |]. by apply ax_done.
Qed.

Lemma ax_comp Δ R J sl sr P P' Q :
  Δ\ R\ J ⊨ₛ {{ P }} sl {{ P' }} → Δ\ R\ J ⊨ₛ {{ P' }} sr {{ Q }} →
  Δ\ R\ J ⊨ₛ {{ P }} sl ;; sr {{ Q }}.
Proof.
  intros Haxl Haxr n k. revert n.
  set (Pd := dassert_pack P Q R J).
  set (Pdl := dassert_pack P P' R J).
  set (Pdr := dassert_pack P' Q R J).
  cut (∀ n d m,
   ax_funs n Δ → locks sl = ∅ → locks sr = ∅ → locks m = ∅ →
   (down d sl → assert_holds (fpure Δ) (Pdl d) (get_stack k) m →
     ax ax_disjoint_cond (ax_stmt_post (sl ;; sr) (fpure Δ) Pd) k n
       (CStmt (□ ;; sr) :: k) (Stmt d sl) m)
   ∧ (down d sr → assert_holds (fpure Δ) (Pdr d) (get_stack k) m →
     ax ax_disjoint_cond (ax_stmt_post (sl ;; sr) (fpure Δ) Pd) k n
       (CStmt (sl ;; □) :: k) (Stmt d sr) m)).
  { intros help n d m ?? Hs ??; simpl in Hs; decompose_empty.
    apply ax_further_pred.
    { intros. solve_cred. }
    intros ? mf S' [??] p; subst.
    destruct d; discriminate_down_up; inv_cstep p;
      eapply mk_ax_next_empty; try done; eapply help; eauto with ax. }

  induction n as [|n IH]; [repeat constructor |]. intros d m; split; intros ??.

  * eapply ax_compose_cons; [|by apply Haxl | clear dependent m d].
    { auto with ax. }
    intros m φ [d ?? Hpost]. apply ax_further.
    { intros. solve_cred. }

    intros ? mf S' [??] p; subst. destruct d; discriminate_down_up; inv_cstep p.
    + eapply mk_ax_next_empty; try done. eapply IH; auto with ax arith.
    + eapply mk_ax_next_empty; try done.
      { simpl. by apply empty_union_L. }
      by apply ax_done.
    + match goal with
      | _ : ?l ∉ labels sl |- _ => destruct (decide (l ∈ labels sr))
      end; subst.
      - eapply mk_ax_next_empty; try done.
        { by apply empty_union_L. }
        apply ax_further_pred.
        { intros; solve_cred. }
        intros ? mf' S'' [??] p; subst. inv_cstep p.
        eapply mk_ax_next_empty; try done. apply ax_pred, IH; auto with ax.
      - eapply mk_ax_next_empty; try done. esolve_elem_of.
        apply ax_done; constructor; solve_elem_of.

  * eapply ax_compose_cons; [|by apply Haxr | clear dependent m d].
    { auto with ax. }
    intros m φ [d ?? Hpost]. apply ax_further.
    { intros. solve_cred. }

    intros ? mf S' [??] p; subst. destruct d; discriminate_down_up; inv_cstep p.
    + eapply mk_ax_next_empty; try done. esolve_elem_of. by apply ax_done.
    + eapply mk_ax_next_empty; try done. esolve_elem_of. by apply ax_done.
    + match goal with
      | _ : ?l ∉ labels sr |- _ => destruct (decide (l ∈ labels sl))
      end; subst.
      - eapply mk_ax_next_empty; try done; [esolve_elem_of |].
        apply ax_further_pred.
        { intros; solve_cred. }
        intros ? mf' S'' [??] p; subst. inv_cstep p.
        eapply mk_ax_next_empty; try done. apply ax_pred, IH; auto with ax.
      - eapply mk_ax_next_empty; try done; [esolve_elem_of |].
        apply ax_done; constructor; solve_elem_of.
Qed.

Lemma ax_if Δ R J e sl sr P P' Q :
  Δ\ emp ⊨ₑ {{ P }} e {{ λ v, ⌜ v ≠ indetc ⌝%V ∧ P' v ▷ }} →
  Δ\ R\ J ⊨ₛ {{ assert_is_true P' }} sl {{ Q }} →
  Δ\ R\ J ⊨ₛ {{ assert_is_false P' }} sr {{ Q }} →
  Δ\ R\ J ⊨ₛ {{ P }} IF e then sl else sr {{ Q }}.
Proof.
  intros Haxe Haxl Haxr n k. revert n.
  set (Pd := dassert_pack P Q R J).
  set (Pdl := dassert_pack (assert_is_true P') Q R J).
  set (Pdr := dassert_pack (assert_is_false P') Q R J).
  cut (∀ n d m,
   ax_funs n Δ → locks e = ∅ → locks sl = ∅ → locks sr = ∅ → locks m = ∅ →
   (down d sl → assert_holds (fpure Δ) (Pdl d) (get_stack k) m →
     ax ax_disjoint_cond (ax_stmt_post (IF e then sl else sr) (fpure Δ) Pd) k n
       (CStmt (IF e then □ else sr) :: k) (Stmt d sl) m)
   ∧ (down d sr → assert_holds (fpure Δ) (Pdr d) (get_stack k) m →
     ax ax_disjoint_cond (ax_stmt_post (IF e then sl else sr) (fpure Δ) Pd) k n
       (CStmt (IF e then sl else □) :: k) (Stmt d sr) m)).
  { intros help n [] m ?? Hs ??; simpl in Hs;
      decompose_empty; discriminate_down_up.
    * apply ax_further_pred.
      { intros. solve_cred. }
      intros ? mf S' [??] p; subst. inv_cstep p.
      eapply mk_ax_next_empty; try done. eapply ax_compose_cons;
        [|apply Haxe; auto with ax | clear dependent m mf S'].
      { auto with ax. }
      intros m φ [v ???]. apply ax_further_pred.
      { intros. destruct (val_true_false_dec v); solve_cred || solve_assert. }
      intros ? mf S' [??] p; subst. inv_cstep p.
      + rewrite mem_unlock_union_l by done.
        eapply mk_ax_next_empty; try done.
        { split. done. by rewrite <-mem_disjoint_unlock. }
        apply help; rewrite ?mem_locks_unlock_all; auto with ax. solve_assert.
      + rewrite mem_unlock_union_l by done.
        eapply mk_ax_next_empty; try done.
        { split. done. by rewrite <-mem_disjoint_unlock. }
        apply help; rewrite ?mem_locks_unlock_all; auto with ax. solve_assert.
    * apply ax_further_pred.
      { intros. solve_cred. }
      intros ? mf S' [??] p; subst. inv_cstep p.
      + eapply mk_ax_next_empty; try done.
        apply help; rewrite ?mem_locks_unlock_all; auto with ax.
      + eapply mk_ax_next_empty; try done.
        apply help; rewrite ?mem_locks_unlock_all; auto with ax. }

  induction n as [|n IH]; [repeat constructor |]. intros d m; split; intros ??.

  * eapply ax_compose_cons; [|by apply Haxl | clear dependent m d].
    { auto with ax. }
    intros m φ [d ?? Hpost]. apply ax_further.
    { intros; solve_cred. }

    intros ? mf S' [??] p; subst. destruct d; discriminate_down_up; inv_cstep p.
    + eapply mk_ax_next_empty; try done. esolve_elem_of. by apply ax_done.
    + eapply mk_ax_next_empty; try done. esolve_elem_of. by apply ax_done.
    + match goal with
      | _ : ?l ∉ labels sl |- _ => destruct (decide (l ∈ labels sr))
      end; subst.
      - eapply mk_ax_next_empty; try done; [esolve_elem_of|].
        apply ax_further_pred.
        { intros; solve_cred. }
        intros ? mf' S'' [??] p; subst. inv_cstep p.
        eapply mk_ax_next_empty; try done. apply ax_pred, IH; auto with ax.
      - eapply mk_ax_next_empty; try done; [esolve_elem_of|].
        apply ax_done. constructor; solve_elem_of.

  * eapply ax_compose_cons; [|by apply Haxr | clear dependent m d].
    { auto with ax. }
    intros m φ [d ?? Hpost]. apply ax_further.
    { intros. solve_cred. }

    intros ? mf S' [??] p; subst. destruct d; discriminate_down_up; inv_cstep p.
    + eapply mk_ax_next_empty; try done; [esolve_elem_of|]. by apply ax_done.
    + eapply mk_ax_next_empty; try done; [esolve_elem_of|]. by apply ax_done.
    + match goal with
      | _ : ?l ∉ labels sr |- _ => destruct (decide (l ∈ labels sl))
      end; subst.
      - eapply mk_ax_next_empty; try done; [esolve_elem_of|].
        apply ax_further_pred.
        { intros. solve_cred. }
        intros ? mf' S'' [??] p; subst. inv_cstep p.
        eapply mk_ax_next_empty; try done. apply ax_pred, IH; auto with ax.
      - eapply mk_ax_next_empty; try done; [esolve_elem_of|].
        apply ax_done; constructor; solve_elem_of.
Qed.

(** ** Derived rules *)
Lemma ax_assign_load_free_lhs Δ P Q γ el er v :
  load_free el → Write ⊆ perm_kind γ →
  Δ\ emp ⊨ₑ {{ el ↦{γ} - ★ P }} er {{ λ v', ⌜ v = v' ⌝ ∧ el ↦{γ} - ★ Q }} →
  Δ\ emp ⊨ₑ {{ el ↦{γ} - ★ P }}
    el ::= er
  {{ λ v', ⌜ v = v' ⌝ ∧ el ↦{perm_lock γ} valc v ★ Q }}.
Proof.
  intros ?? Her. rewrite assert_exist_sep; apply ax_expr_exist_pre; intros vl.
  rewrite assert_singleton_eval_l_alt, assert_exist_and, assert_exist_sep;
    apply ax_expr_exist_pre; intros a.
  apply ax_expr_weaken with
    ((el ⇓ a ∧ emp) ★ (el ↦{γ} - ★ P))%A
    (λ v', ∃ a', valc a' ↦{perm_lock γ} valc v' ★
      (⌜ v = v' ∧ a = a' ⌝ ∧ el ⇓ a' ∧ Q))%A.
  { rewrite (associative (★))%A by apply _; f_equiv.
    rewrite <-assert_and_sep_emp_l by apply _. solve_assert. }
  { intro v'; apply assert_exist_elim; intros a'.
    rewrite <-(assert_singleton_eval_l_1 _ el a').
    rewrite assert_and_sep_associative by apply _.
    rewrite !assert_sep_and_swap by apply _. solve_assert. }
  eapply ax_assign.
  { done. }
  { apply ax_expr_base; solve_assert. }
  { apply Her. }
  intros a' v'; simpl.
  rewrite !assert_sep_and_swap, (associative (★))%A by apply _; f_equiv.
  rewrite <-!(associative (∧))%A, <-assert_and_sep_associative by apply _.
  apply assert_Prop_intro_l; intros ->.
  rewrite (commutative (∧) emp)%A, (associative (∧))%A.
  rewrite <-assert_and_sep_emp_l by apply _.
  rewrite <-(assert_eval_singleton__1 _ el a'). solve_assert.
Qed.

Lemma ax_assign_simple Δ J R P γ el er v :
  UnlockIndep P → load_free el →
  Write ⊆ perm_kind γ →
  (el ↦{γ} - ★ P)%A ⊑@{fpure Δ} (er ⇓ v)%A →
  Δ\ R\ J ⊨ₛ {{ el ↦{γ} - ★ P }} do (el ::= er) {{ el ↦{γ} valc v ★ P }}.
Proof.
  intros ??? HP. apply ax_do. apply ax_expr_weaken_post with
    (λ v', ⌜ v = v' ⌝ ∧ (el ↦{perm_lock γ} valc v ★ P))%A.
  { intros. rewrite <-assert_unlock_sep, <-assert_lock_singleton by done.
    rewrite <-(assert_unlock_unlock_indep P). solve_assert. }
  apply ax_assign_load_free_lhs; auto. by apply ax_expr_base.
Qed.
Lemma ax_assign_simple_twice Δ J R P γ1 γ2 el1 el2 er v :
  UnlockIndep P → load_free el1 → load_free el2 →
  Write ⊆ perm_kind γ1 → Write ⊆ perm_kind γ2 →
  (el1 ↦{γ1} - ★ el2 ↦{γ2} - ★ P)%A ⊑@{fpure Δ} (er ⇓ v)%A →
  Δ\ R\ J ⊨ₛ {{ el1 ↦{γ1} - ★ el2 ↦{γ2} - ★ P }}
    do (el1 ::= el2 ::= er)
  {{ el1 ↦{γ1} valc v ★ el2 ↦{γ2} valc v ★ P }}.
Proof.
  intros ????? HP. apply ax_do. apply ax_expr_weaken_post with
    (λ v', ⌜ v = v' ⌝ ∧ (el1 ↦{perm_lock γ1} valc v ★
            el2 ↦{perm_lock γ2} valc v ★ P))%A.
  { intros. rewrite <-!assert_unlock_sep, <-!assert_lock_singleton by done.
    rewrite <-(assert_unlock_unlock_indep P). solve_assert. }
  apply ax_assign_load_free_lhs; auto.
  setoid_rewrite (associative (★) (el1 ↦{γ1} -))%A.
  setoid_rewrite (commutative (★) (el1 ↦{γ1} -))%A.
  setoid_rewrite <-(associative (★))%A.
  apply ax_assign_load_free_lhs; auto.
  apply ax_expr_base. by rewrite (associative (★))%A,
    (commutative (★) (el2 ↦{γ2} -))%A, <-(associative (★))%A.
Qed.

Lemma ax_ret_simple Δ J R Q e v :
  UnlockIndep (R v) → Δ\ R\ J ⊨ₛ {{ e⇓v ∧ R v }} ret e {{ Q }}.
Proof.
  intros. apply ax_ret, ax_expr_weaken_post with
    (λ v', ⌜ v = v' ⌝ ∧ (e ⇓ v ∧ R v))%A.
  { intros v'. apply assert_Prop_intro_l; intros; subst.
    rewrite <-(assert_unlock_unlock_indep (R v')). solve_assert. }
  apply ax_expr_base. solve_assert.
Qed.
Lemma ax_ret_assign Δ J R Q P γ el er v :
  UnlockIndep P → load_free el →
  Write ⊆ perm_kind γ →
  (el ↦{γ} - ★ P)%A ⊑@{fpure Δ} (er ⇓ v)%A →
  (el ↦{γ} - ★ P)%A ⊑@{fpure Δ} R v →
  Δ\ R\ J ⊨ₛ {{ el ↦{γ} - ★ P }} ret (el ::= er) {{ Q }}.
Proof.
  intros ???? HP HPR. apply ax_ret. apply ax_expr_weaken_post with
    (λ v', ⌜ v = v' ⌝ ∧ (el ↦{perm_lock γ} valc v ★ P))%A.
  { intros v'. apply assert_Prop_intro_l; intros ->.
    rewrite <-HP, <-assert_unlock_sep, assert_lock_singleton by done.
    rewrite <-(assert_unlock_unlock_indep P). solve_assert. }
  apply ax_assign_load_free_lhs; auto. by apply ax_expr_base.
Qed.

Lemma ax_while_simple Δ J R P e s :
  UnlockIndep P →
  Δ\ R\ J ⊨ₛ {{ e⇓true ∧ P }} s {{ ∃ v, e⇓v ∧ ⌜ v ≠ indetc ⌝%V ∧ P }} →
  Δ\ R\ J ⊨ₛ {{ ∃ v, e⇓v ∧ ⌜v ≠ indetc⌝%V ∧ P }} while (e) s {{ e⇓false ∧ P }}.
Proof.
  intros ? Hs. apply ax_stmt_weaken_post
    with (assert_is_false (λ v, e ⇓ v ∧ P))%A, ax_while.
  * solve_assert.
  * apply ax_expr_exist_pre; intros v.
    apply ax_expr_weaken_post with
      (λ v', ⌜ v = v' ⌝ ∧ e ⇓ v ∧ ⌜ v ≠ indetc%V ⌝ ∧ P)%A.
    { intros v'. rewrite assert_unlock_and, <-(assert_unlock_unlock_indep P).
      rewrite assert_unlock_expr; solve_assert. }
    apply ax_expr_base; solve_assert.
  * eapply ax_stmt_weaken_pre, Hs; solve_assert.
Qed.
Lemma ax_if_simple Δ J R e sl sr P Q :
  UnlockIndep P →
  Δ\ R\ J ⊨ₛ {{ e⇓true ∧ P }} sl {{ Q }} →
  Δ\ R\ J ⊨ₛ {{ e⇓false ∧ P }} sr {{ Q }} →
  Δ\ R\ J ⊨ₛ {{ ∃ v, e⇓v ∧ ⌜v ≠ indetc⌝%V ∧ P }} IF e then sl else sr {{ Q }}.
Proof.
  intros ? Hsl Hsr. eapply ax_if with (λ v, e ⇓ v ∧ P)%A.
  * apply ax_expr_exist_pre; intros v.
    apply ax_expr_weaken_post with
      (λ v', ⌜ v = v' ⌝ ∧ e ⇓ v ∧ ⌜ v ≠ indetc%V ⌝ ∧ P)%A.
    { intros v'. rewrite assert_unlock_and, <-(assert_unlock_unlock_indep P).
      rewrite assert_unlock_expr; solve_assert. }
    apply ax_expr_base; solve_assert.
  * eapply ax_stmt_weaken_pre, Hsl; solve_assert.
  * eapply ax_stmt_weaken_pre, Hsr; solve_assert.
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
   format "δ \  Δ \  P  ⊨ₚ  '[' s ']'").
Notation "δ \ Δ \ R \ J ⊨ₛ {{ P }} s {{ Q }}" :=
  (ax_stmt δ Δ R%A J%A P%A s%S Q%A)
  (at level 74, Δ at next level, R at next level, J at next level,
   format "δ \  Δ \  R  \  J  ⊨ₛ  '[' {{  P  }} '/'  s  '/' {{  Q  }} ']'").
Notation "δ \ Δ ⊨ₜ {{ P }} s {{ Q }}" :=
  (ax_stmt_top δ Δ P%A s%S Q%A)
  (at level 74, Δ at next level,
   format "δ \  Δ  ⊨ₜ  '[' {{  P  }} '/'  s  '/' {{  Q  }} ']'").
Notation "δ \ Δ \ A ⊨ₑ {{ P }} e {{ Q }}" :=
  (ax_expr δ Δ A%A P%A e%E Q%A)
  (at level 74, Δ at next level, A at next level,
   format "δ \  Δ \  A  ⊨ₑ  '[' {{  P  }} '/'  e  '/' {{  Q  }} ']'").
