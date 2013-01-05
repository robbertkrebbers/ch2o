(* Copyright (c) 2012, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file defines an axiomatic semantics (in the form of separation logic)
for our language. This axiomatic semantics has two judgments: one for
statements and one for expressions. Statement judgment are sextuples of the
shape [Δ / R / J ⊨ₛ {{ P }} s {{ Q }}] where:

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
Require Export assertions smallstep.
Local Open Scope nat_scope.

Section axiomatic.
Context (δ : funenv).

(** * The Hoare judgment *)
(** We want [Δ / R / J ⊨ₛ {{ P }} s {{ Q }}] to ensure partial program
correctness. Intuitively, that means: if [P (get_stack k) m] and
[State k (Stmt s ↘) m ⇒* State k (Stmt s ↗) m'], then [Q (get_stack k) m'].
Due to the additional features we consider, we need to make the interpretation
somewhat stronger.

- We also have to account for reductions starting or ending in the directions
  [⇈] or [↷]. The notation [Δ \ Pd ⊨ₚ s] to take [R], [J], [P] and [Q] together
  as one function [Pd] comes in handy here.
  The intuitive meaning of [Δ \ Pd ⊨ₚ s] should thus be: if
  [Pd d (get_stack k) m] and [State k (Stmt s d) m ⇒* State k (Stmt s d') m'],
  then [Pd d' (get_stack k) m'].
- We should enforce the reduction [State k (Stmt s d) m ⇒*
  State k (Stmt s d') m'] to remain below [k] as it could otherwise pop too
  many items of the program context.
- Our language has various kinds of undefined behavior (e.g. invalid pointer
  dereferences). We therefore also want [Δ \ Pd ⊨ₚ s] to guarantee that [s]
  does not exhibit such undefined behaviors.
  Hence, [Δ \ Pd ⊨ₚ s] should at least be defined as: if [P d k m] and
  [State k (Stmt s d) m ⇒* S], then [S] is either:
-- reducible (no undefined behavior has occurred), or,
-- of the shape [State k (Stmt s d') m'] with [Pd d' (get_stack k) m']
   (execution is finished).

- The program should satisfy a form of memory safety so as the make the frame
  rule derivable. Also, in order to deal with non-deterministic execution
  of expressions, we should be able to interleave executions of different
  subexpressions.
  Hence, if before execution the memory can be extended with a disjoint part
  [mf] (also called the framing memory), that part should not be modified during
  the execution. Also, to allow interleaving, the framing memory [mf] should be
  allowed to be changed at any point during the execution.
- We take a step indexed approach in order to relate the assertions of
  functions in [Δ] to the statement [s].

Nearly all of the above properties apply to the expression judgment
[Δ ⊨ₑ {{ P }} e {{ Q }}] as well. Therefore, we first define a more general
notion that captures these properties for both kinds of judgments. *)

(** The intuitive meaning of the predicate [ax P l n k φ m] is that all
[(δ⇒ₛ{l})]-reductions paths of at most [n] steps starting at
[State k φ (m ∪ mf)] for an arbitrary framing memory [mf], do not exhibit
undefined behavior, do not get stuck, and if finished satisfy [P]. To allow the
framing memory [mf] to be changed during the execution, we define this predicate
inductively using single steps, instead of defining it by means of
[(δ⇒ₛ{l}^n)]-reduction paths. *)
Section ax.
  Context (P : stack → mem → focus → Prop).
  Context `{P_nf : PropHolds (∀ mf l m φ,
    P (get_stack l) m φ → nf (δ⇒ₛ{l}) (State l φ (m ∪ mf)))}.

  Inductive ax (l : ctx) : nat → ctx → focus → mem → Prop :=
    | ax_O k φ m :
       ax l 0 k φ m
    | ax_done n φ m :
       P (get_stack l) m φ →
       ax l n l φ m
    | ax_further n k φ m :
       (∀ mf,
         m ⊥ mf →
         red (δ⇒ₛ{l}) (State k φ (m ∪ mf))) →
       (∀ mf S',
         m ⊥ mf →
         δ ⊢ₛ State k φ (m ∪ mf) ⇒{l} S' →
         ax_next l n mf S') →
       ax l (S n) k φ m
  with ax_next (l : ctx) : nat → mem → state → Prop :=
    | mk_ax_next n mf k φ m :
       m ⊥ mf →
       φ ≠ Undef →
       ax l n k φ m →
       ax_next l n mf (State k φ (m ∪ mf)).

  Lemma ax_further_pred l n k φ m :
    (∀ mf,
      m ⊥ mf →
      red (δ⇒ₛ{l}) (State k φ (m ∪ mf))) →
    (∀ mf S',
      m ⊥ mf →
      δ ⊢ₛ State k φ (m ∪ mf) ⇒{l} S' →
      ax_next l (pred n) mf S') →
    ax l n k φ m.
  Proof. destruct n; constructor (solve [auto]). Qed.

  Lemma ax_S l n k φ m (Hax : ax l (S n) k φ m) : ax l n k φ m
  with ax_next_S l n mf S' (Hax : ax_next l (S n) mf S') : ax_next l n mf S'.
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
    inversion Hax as [| | ???? _ Hnext]; simplify_mem_equality.
    * destruct (P_nf mf k m φ). done. solve_cred.
    * eauto.
  Qed.

  Lemma ax_red n l mf k φ m :
    m ⊥ mf →
    ax l (S n) k φ m →
    ¬P (get_stack k) m φ →
    red (δ⇒ₛ{l}) (State k φ (m ∪ mf)).
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
    φ ≠ Undef →
    m ⊥ mf →
    ax l (n1 + n2) k φ m →
    δ ⊢ₛ State k φ (m ∪ mf) ⇒{l}^n1 S' →
    ax_next l n2 mf S'.
  Proof.
    revert k φ m.
    induction n1 as [n1 IH] using lt_wf_ind.
    intros k φ m ?? Hax p.
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
  { intros mf ?. apply (red_subrel (δ ⇒ₛ{k2}) _ _). auto. }
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
    apply Hred. solve_mem_disjoint. }
  intros mf S' ? p.
  feed inversion (Hstep (m2 ∪ mf) S'); subst.
  * solve_mem_disjoint.
  * by rewrite (associative_eq _).
  * rewrite (associative_eq _).
    constructor; solve_mem_disjoint.
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
  * solve_mem_disjoint.
Qed.

Global Instance: Proper (((=) ==> (=) ==> (=) ==> impl) ==>
   (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> impl) ax.
Proof.
  intros ?? H ? l ?? n ?? k ?? φ ?? m ?. subst.
  red. apply ax_weaken. intros ??. by apply H.
Qed.
Global Instance: Proper (((=) ==> (=) ==> (=) ==> iff) ==>
   (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> iff) ax.
Proof.
  intros ?? H ? l ?? n ?? k ?? φ ?? m ?. subst.
  split; apply ax_weaken;
   intros ??; apply H; first [by eauto | by symmetry; eauto].
Qed.

Lemma ax_and (P Q R : stack → mem → focus → Prop)
  `{P_nf : PropHolds (∀ mf l m φ,
     P (get_stack l) m φ → nf (δ⇒ₛ{l}) (State l φ (m ∪ mf)))}
  `{Q_nf : PropHolds (∀ mf l m φ,
     Q (get_stack l) m φ → nf (δ⇒ₛ{l}) (State l φ (m ∪ mf)))}
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
  * exfalso. eapply P_nf, (Hred2 ∅); eauto with mem.
  * exfalso. eapply Q_nf, (Hred1 ∅); eauto with mem.
  * apply ax_further; [done |]. intros mf S' ??.
    specialize (Hstep1 mf S'). specialize (Hstep2 mf S').
    feed destruct Hstep1; feed inversion Hstep2; subst; trivial.
    simplify_mem_equality.
    constructor; auto.
Qed.

(** ** Function calls *)
(** We define assertions of functions as a dependently typed record [fassert]
consisting of the function's pre- and postcondition. The pre- and postcondition
should be stack independent because local variables may have a different
meaning at the calling function than within the called function's body.
Furthermore, to relate the postcondition to the precondition, we extend this
record with a field [fcommon] that is used in both. This approach is similar
to (Appel/Blazy, 2007), but we also allow the postcondition to refer to the
function's arguments. *)
Record fassert := FAssert {
  fcommon : Type;
  fpre : fcommon → list value → assert;
  fpost : fcommon → list value → value → assert;
  fpre_stack_indep c vs : StackIndep (fpre c vs);
  fpost_stack_indep c vs v : StackIndep (fpost c vs v)
}.
Add Printing Constructor fassert.
Global Existing Instance fpre_stack_indep.
Global Existing Instance fpost_stack_indep.
Notation fassert_env := (funmap fassert).

(** The predicate [ax_funs n Δ] states that the functions in [Δ] behave
accordingly. Intuitively this means that if a [Call f vs] with [vs] satisfying
the precondition of [f] terminates, then the result is a [Return v] with [v]
satisfying the postcondition of [f]. *)
Inductive ax_fun_P (Pf : fassert) (c : fcommon Pf) (vs : list value)
    (ρ : stack) (m : mem) : focus → Prop :=
  | make_ax_fun_P v :
     fpost Pf c vs v ρ m →
     ax_fun_P Pf c vs ρ m (Return v).
Definition ax_funs (n : nat) (Δ : fassert_env) : Prop :=
  ∀ f Pf c vs m k,
    Δ !! f = Some Pf →
    fpre Pf c vs (get_stack k) m →
    ax (ax_fun_P Pf c vs) k n k (Call f vs) m.

Instance: PropHolds (∀ mf l m φ,
  ax_fun_P Pf c vs (get_stack l) m φ →
  nf (δ⇒ₛ{l}) (State l φ (m ∪ mf))).
Proof. destruct 1. intros [? p]. inv_cstep p. Qed.
Instance: PropHolds (∀ ρ m, ¬ax_fun_P Pf c vs ρ m Undef).
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

(** ** Directed assertions *)
(** The statement judgment will be of the shape [Δ \ Pd ⊨ₚ s] where [Pd] is
a function from directions to assertions taking the pre- and post, returning,
and jumping condition together. We generalize this idea slightly, and define
the type [directed A] as functions [direction → A]. *)
Definition directed_pack {A} (P : A) (Q : A) (R : value → A)
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
of the previously defined notions together. *)
Inductive ax_stmt_P s (Pd : dassert) (ρ : stack) (m : mem) : focus → Prop :=
  make_ax_stmt_P d :
    up d s →
    Pd d ρ m →
    ax_stmt_P s Pd ρ m (Stmt d s).
Definition ax_stmt_packed (Δ : fassert_env) (Pd : dassert) (s : stmt) : Prop :=
  ∀ n k d m,
    ax_funs n Δ →
    down d s →
    Pd d (get_stack k) m →
    ax (ax_stmt_P s Pd) k n k (Stmt d s) m.
Notation "Δ \ P ⊨ₚ s" :=
  (ax_stmt_packed Δ P%A s%S)
  (at level 74, P at next level, format "Δ  \  P  ⊨ₚ  '[' s ']'").

Instance: PropHolds (∀ mf l m φ,
  ax_stmt_P s Pd (get_stack l) m φ →
  nf (δ⇒ₛ{l}) (State l φ (m ∪ mf))).
Proof. destruct 1. intros [? p]. inv_cstep p. Qed.

Instance ax_stmt_P_proper: Proper
  (pointwise_relation _ (≡) ==> (=) ==> (=) ==> (=) ==> iff)
  (ax_stmt_P s).
Proof.
  intros ??? E. repeat intro; subst.
  split; destruct 1; by constructor; [|eapply E; eauto].
Qed.

Global Instance ax_stmt_packed_proper: Proper
  (pointwise_relation _ (≡) ==> (=) ==> iff) (ax_stmt_packed Δ).
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
  Δ ⊨ₜ {{ P }} s {{ Q }} ↔ Δ \ Q \ (λ _, False) ⊨ₛ {{ P }} s {{ Q void%V }}.
Proof. done. Qed.

Global Instance ax_stmt_proper: Proper
  (pointwise_relation _ (≡) ==> pointwise_relation _ (≡) ==>
    (≡) ==> (=) ==> (≡) ==> iff) (ax_stmt Δ).
Proof.
  intros ??? E1 ?? E2 ?? E3 ??? ?? E4; subst.
  unfold ax_stmt. by rewrite E1, E2, E3, E4.
Qed.
Global Instance ax_stmt_top_proper: Proper
  ((≡) ==> (=) ==> pointwise_relation _ (≡) ==> iff) (ax_stmt_top Δ).
Proof.
  intros ??? E1 ??? ?? E2; subst.
  unfold ax_stmt_top, dassert_pack_top. by rewrite E1, E2.
Qed.

(** ** The Hoare judgment for expressions *)
(** The interpretation of the expression judgment is defined similarly. *)
Inductive ax_expr_P (Q : value → assert) (ρ : stack) (m : mem) : focus → Prop :=
  make_ax_expr_P v :
    Q v ρ m →
    ax_expr_P Q ρ m (Expr (val v)).
Definition ax_expr (Δ : fassert_env) (P : assert)
    (e : expr) (Q : value → assert) : Prop :=
  ∀ n k m,
    ax_funs n Δ →
    P (get_stack k) m →
    ax (ax_expr_P Q) k n k (Expr e) m.
Notation "Δ ⊨ₑ {{ P }} e {{ Q }}" :=
  (ax_expr Δ P%A e%E Q%A)
  (at level 74, format "Δ  ⊨ₑ  '[' {{  P  }} '/'  e  '/' {{  Q  }} ']'").

Instance: PropHolds (∀ mf l m φ,
  ax_expr_P Q (get_stack l) m φ →
  nf (δ⇒ₛ{l}) (State l φ (m ∪ mf))).
Proof. destruct 1. apply cnf_val. Qed.

Instance ax_expr_P_proper: Proper
  (pointwise_relation _ (≡) ==> (=) ==> (=) ==> (=) ==> iff) ax_expr_P.
Proof.
  intros ?? E. repeat intro; subst.
  split; destruct 1; constructor; eapply E; eauto.
Qed.

Lemma ax_expr_P_is_value P ρ m e :
  ax_expr_P P ρ m (Expr e) → is_value e.
Proof. by inversion 1. Qed.

Lemma ax_expr_val P n k v m :
  ax (ax_expr_P P) k (S n) k (Expr (val v)) m →
  P v (get_stack k) m.
Proof.
  inversion 1 as [|??? [??] | ???? Hred]; subst.
  * done.
  * destruct (cnf_val δ k v (m ∪ ∅)).
    apply Hred. solve_mem_disjoint.
Qed.

Global Instance ax_expr_proper: Proper
  ((≡) ==> (=) ==> pointwise_relation _ (≡) ==> iff) (ax_expr Δ).
Proof.
  intros Δ P Q E1 ??? Pf Qf E2; subst. unfold ax_expr.
  by setoid_rewrite E1; setoid_rewrite E2.
Qed.

(** The lemma [ax_expr_compose] is used to prove the structural Hoare rules for
expressions. It is proven by chasing all reduction paths for a compound
expression. This is done step-wise by distinguishing the following cases:

- All subexpressions are values.
- Some subexpression contains a redex that is not a function call.
- Some subexpression contains a redex that is a function call. In this case we
  use the lemma [ax_call_compose]. *)
Lemma ax_call_compose P Q (E E' : ectx) n φ l k m1 m2 :
  m1 ⊥ m2 →
  ax P l n (k ++ [CCall E] ++ l) φ m1 →
  (∀ n' m1' e',
    n' ≤ n →
    m1' ⊥ m2 →
    ax P l n' l (Expr (subst E e')) m1' →
    ax Q l n' l (Expr (subst E' e')) (m1' ∪ m2)) →
  ax Q l n (k ++ [CCall E'] ++ l) φ (m1 ∪ m2).
Proof.
  revert m1 φ k. induction n as [|n IH]; [intros; apply ax_O |].

  intros m1 φ k ? Hax Hnext.
  inversion Hax as [| | ???? Hred Hstep]; simplify_list_equality.
  apply ax_further.
  { intros mf ?. rewrite <-(associative_eq (∪)).
    destruct (Hred (m2 ∪ mf)) as [S' p]; [solve_mem_disjoint |].
    apply (cstep_call_inv _ _ _ E' _ _ _ _ _ p);
      intros; subst; eexists; eauto. }

  intros mf S' ? p. rewrite <-(associative_eq (∪)) in p.
  apply (cstep_call_inv _ _ _ E _ _ _ _ _ p).
  * intros k' φ' m' p'.
    feed inversion (Hstep (m2 ∪ mf)
      (State (k' ++ [CCall E] ++ l) φ' m'));
      subst; trivial.
    { solve_mem_disjoint. }
    rewrite (associative_eq (∪)).
    constructor; [solve_mem_disjoint | done |].
    apply IH; auto with arith; solve_mem_disjoint.
  * intros v ? ? p'. subst.
    feed inversion (Hstep (m2 ∪ mf)
      (State l (Expr (subst E (val v)%E))
      (m1 ∪ (m2 ∪ mf)))) as [???]; subst; trivial.
    { solve_mem_disjoint. }
    rewrite (associative_eq (∪)).
    constructor; [solve_mem_disjoint | done |].
    apply Hnext; auto with arith; solve_mem_disjoint.
Qed.

Lemma ax_expr_compose n {vn} (Ps : vec vassert vn) (Q : vassert)
    (E : ectx_full vn) (es : vec expr vn) (l : ctx) (ms : vec mem vn) :
  list_disjoint ms →
  (∀ i, ax (ax_expr_P (Ps !!! i)) l n l (Expr (es !!! i)) (ms !!! i)) →
  (∀ vs (ms' : vec mem vn),
    list_disjoint ms' →
    (∀ i, (Ps !!! i) (vs !!! i) (get_stack l) (ms' !!! i)) →
    ax (ax_expr_P Q) l n l (Expr (depsubst E (vmap EVal vs)%E)) (⋃ ms')) →
  ax (ax_expr_P Q) l n l (Expr (depsubst E es)) (⋃ ms).
Proof.
  revert es ms.
  induction n as [[|n] IH] using lt_wf_ind; [intros; apply ax_O |].

  intros es ms ? Hax1 Hax2.
  destruct (expr_vec_values es) as [[vs ?] | [i Hi]]; subst.
  { apply Hax2; [done | intros i].
    apply ax_expr_val with n.
    by rewrite <-(vlookup_map EVal vs). }

  apply ax_further.
  { intros mf ?.
    rewrite (ectx_full_to_item_correct _ _ i).
    apply (cred_ectx _ [_]).
    rewrite <-(finmap_union_delete_vec ms i),
      <-(associative_eq (∪)) by done.
    apply (ax_red (ax_expr_P (Ps !!! i)) n); trivial.
    + solve_mem_disjoint.
    + contradict Hi. eauto using ax_expr_P_is_value. }

  intros mf S' ? p.
  apply (cstep_expr_depsubst_inv _ _ _ _ _ _ _ p); clear p.
  * clear i Hi. intros i e' m' p'.
    feed inversion (ax_step (ax_expr_P (Ps !!! i)) n
      l (⋃ delete (fin_to_nat i) (vec_to_list ms) ∪ mf)
      l (Expr (es !!! i)) (ms !!! i) (State l (Expr e') m'))
      as [???? m'']; subst; trivial.
    { solve_mem_disjoint. }
    { by rewrite (associative_eq (∪)), finmap_union_delete_vec. }

    rewrite (associative_eq (∪)). constructor.
    { solve_mem_disjoint. }
    { done. }

    rewrite <-finmap_union_insert_vec by solve_mem_disjoint.
    apply IH; auto with arith.
    + solve_mem_disjoint.
    + intros j. destruct (decide (i = j)); subst.
      - by rewrite !vlookup_insert.
      - rewrite !vlookup_insert_ne by done. apply ax_S, Hax1.
    + intros vs ms' ??. by apply ax_S, Hax2.
  * clear i Hi. intros i E' f vs HE p.
    constructor; [done | done |].
    rewrite <-(finmap_union_delete_vec ms i) by done.
    apply ax_call_compose with (P:=ax_expr_P (Ps !!! i)) (k:=[]) (E:=E').
    { solve_mem_disjoint. }
    { feed inversion (ax_step (ax_expr_P (Ps !!! i)) n
        l (⋃ delete (fin_to_nat i) (vec_to_list ms) ∪ mf)
        l (Expr (es !!! i)) (ms !!! i)
        (State (CCall E' :: l) (Call f vs) (ms !!! i ∪
          (⋃ delete (fin_to_nat i) (vec_to_list ms) ∪ mf)))); subst; trivial.
      + solve_mem_disjoint.
      + by rewrite (associative_eq (∪)), finmap_union_delete_vec.
      + by simplify_mem_equality. }

    intros n' m' e' ?? Hax.
    rewrite <-finmap_union_insert_vec by done.
    rewrite list_subst_snoc, <-ectx_full_to_item_correct_alt.
    apply IH; auto with arith.
    + solve_mem_disjoint.
    + intros j. destruct (decide (i = j)); subst.
      - by rewrite !vlookup_insert.
      - rewrite !vlookup_insert_ne by done.
        apply ax_le with (S n); auto with arith.
    + intros vs' ms' ??.
      apply ax_le with (S n); auto with arith.

  * intros vs Hvs. destruct Hi. by rewrite Hvs, vlookup_map.

  * clear i Hi. intros i p.
    destruct (ax_step_undef
      (ax_expr_P (Ps !!! i)) n
      l (⋃ delete (fin_to_nat i) (vec_to_list ms) ∪ mf)
      l (Expr (es !!! i)) (ms !!! i) l (⋃ ms ∪ mf)); trivial.
    + solve_mem_disjoint.
    + by rewrite (associative_eq (∪)), finmap_union_delete_vec.
Qed.

(** * Partial program correctness *)
(** We prove that the interpretation of the statement Hoare judgment indeed
satisfies partial program correctness. *)
Lemma ax_stmt_sound_sep P Q s m mf S' :
  ∅ ⊨ₜ {{ P }} s {{ Q }} →
  m ⊥ mf →
  P [] m →
  δ ⊢ₛ State [] (Stmt ↘ s) (m ∪ mf) ⇒* S' →
    (∃ m', S' = State [] (Stmt ↗ s) (m' ∪ mf) ∧ Q VVoid [] m')
  ∨ (∃ m' v, S' = State [] (Stmt (⇈ v) s) (m' ∪ mf) ∧ Q v [] m')
  ∨ red (δ⇒ₛ) S'.
Proof.
  intros Hax ? ? p.
  apply rtc_bsteps in p. destruct p as [n p].
  feed inversion (ax_steps
    (ax_stmt_P s (dassert_pack_top P Q))
    n 1 [] mf (Stmt ↘ s) [] m S') as [??????? Hax']; subst; try done.
  * apply Hax; auto with ax.
  * by apply (bsteps_subrel (δ⇒ₛ) _ _).
  * inversion Hax' as [|??? [d' ??]|]; subst.
    + destruct d'; naive_solver.
    + right; right. apply (red_subrel (δ⇒ₛ{ [] }) _ _); auto.
Qed.
Lemma ax_stmt_sound P R s m S' :
  ∅ ⊨ₜ {{ P }} s {{ R }} →
  P [] m →
  δ ⊢ₛ State [] (Stmt ↘ s) m ⇒* S' →
    (∃ m', S' = State [] (Stmt ↗ s) m' ∧ R VVoid [] m')
  ∨ (∃ m' v, S' = State [] (Stmt (⇈ v) s) m' ∧ R v [] m')
  ∨ red (δ⇒ₛ) S'.
Proof.
  intros ?? p. rewrite <-(right_id_eq ∅ (∪) m) in p.
  destruct (ax_stmt_sound_sep P R s m ∅ S') as [[?[E ?]]|[[?[?[E ?]]]|]];
    try rewrite (right_id_eq ∅ (∪)) in E; intuition eauto with mem.
Qed.

Lemma ax_stmt_looping_sep P s m mf :
  ∅ ⊨ₜ {{ P }} s {{ λ _, False }} →
  m ⊥ mf →
  P [] m →
  looping (δ⇒ₛ) (State [] (Stmt ↘ s) (m ∪ mf)).
Proof.
  intros Hax ??. apply looping_alt. intros S' p.
  destruct (ax_stmt_sound_sep P (λ _, False)%A s m mf S')
    as [[??]|[[?[??]]|?]]; by intuition.
Qed.
Lemma ax_stmt_looping P s m :
  ∅ ⊨ₜ {{ P }} s {{ λ _, False }} →
  P [] m →
  looping (δ⇒ₛ) (State [] (Stmt ↘ s) m).
Proof.
  intros. rewrite <-(right_id_eq ∅ (∪) m).
  apply ax_stmt_looping_sep with P; auto with mem.
Qed.

(** * The Hoare rules *)
(** We prove that the Hoare rules are inhabited by the interpretation of the
Hoare judgment. *)

(** ** Logical rules *)
Lemma ax_stmt_weaken_packed Δ Pd Pd' s :
  Δ \ Pd ⊨ₚ s →
  (∀ d, down d s → Pd' d ⊆ Pd d) →
  (∀ d, up d s → Pd d ⊆ Pd' d) →
  Δ \ Pd' ⊨ₚ s.
Proof.
  intros Hax Hdown Hup n k d m ???.
  apply ax_weaken with (ax_stmt_P s Pd).
  * intros ?? []; constructor; solve_assert.
  * by apply Hax, Hdown.
Qed.

Lemma ax_stmt_weaken_pre Δ R J P P' Q s :
  Δ \ R \ J ⊨ₛ {{ P }} s {{ Q }} →
  P' ⊆ P →
  Δ \ R \ J ⊨ₛ {{ P' }} s {{ Q }}.
Proof. intros. eapply ax_stmt_weaken_packed; intros []; solve_assert. Qed.
Lemma ax_stmt_weaken_post Δ R J P Q Q' s :
  Δ \ R \ J ⊨ₛ {{ P }} s {{ Q }} →
  Q ⊆ Q' →
  Δ \ R \ J ⊨ₛ {{ P }} s {{ Q' }}.
Proof. intros. eapply ax_stmt_weaken_packed; intros []; solve_assert. Qed.

Lemma ax_stmt_packed_right_frame Δ A Pd s :
  ax_stmt_packed Δ Pd s →
  ax_stmt_packed Δ ((λ P, P ★ A)%A <$> Pd) s.
Proof.
  intros Hax n k d m HΔ Hd Hpre.
  rewrite directed_fmap_spec in Hpre.
  destruct Hpre as [m1 [m2 [? [? [??]]]]]; simplify_equality.
  apply ax_frame with (ax_stmt_P s Pd); auto.
  intros m ?? []; constructor; [done |].
  rewrite directed_fmap_spec. solve_assert.
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
  intros Hax1 Hax2 n k d m ?? Hpre.
  eapply (ax_and (ax_stmt_P s _) (ax_stmt_P s _) _);
    [| apply Hax1 | apply Hax2]; trivial.
  * intros ??? [d' ??]. inversion 1; subst.
    constructor; [done | destruct d'; solve_assert].
  * destruct d; solve_assert.
  * destruct d; solve_assert.
Qed.

Lemma ax_stmt_or Δ R J P P' Q s :
  Δ \ R \ J ⊨ₛ {{ P }} s {{ Q }} →
  Δ \ R \ J ⊨ₛ {{ P' }} s {{ Q }} →
  Δ \ R \ J ⊨ₛ {{ P ∨ P' }} s {{ Q }}.
Proof.
  intros Hax1 Hax2 n k [] m HΔ Hd Hpre; discriminate_down_up.
  * destruct Hpre.
    + apply ax_weaken with (ax_stmt_P s (dassert_pack P Q R J)); auto.
      intros ?? [[] ??]; constructor; solve_assert.
    + apply ax_weaken with (ax_stmt_P s (dassert_pack P' Q R J)); auto.
      intros ?? [[] ??]; constructor; solve_assert.
  * apply ax_weaken with (ax_stmt_P s (dassert_pack P Q R J)); auto.
    intros ?? [[] ??]; constructor; solve_assert.
Qed.

Lemma ax_stmt_ex_pre `{!Inhabited A} Δ R J (P : A → assert) Q s :
  (∀ x, Δ \ R \ J ⊨ₛ {{ P x }} s {{ Q }}) →
  Δ \ R \ J ⊨ₛ {{ ∃ x, P x }} s {{ Q }}.
Proof.
  intros Hax n k [] m HΔ Hd Hpre; discriminate_down_up.
  * destruct Hpre as [x Hpre].
    apply ax_weaken with (ax_stmt_P s (dassert_pack (P x) Q R J)).
    + intros ?? [[] ??]; constructor; solve_assert.
    + by apply Hax.
  * destruct (_ : Inhabited A) as [x].
    apply ax_weaken with (ax_stmt_P s (dassert_pack (P x) Q R J)).
    + intros ?? [[] ??]; constructor; solve_assert.
    + by apply Hax.
Qed.
Lemma ax_stmt_ex_post `{!Inhabited A} Δ R J P (Q : A → assert) s x :
  Δ \ R \ J ⊨ₛ {{ P }} s {{ Q x }} →
  Δ \ R \ J ⊨ₛ {{ P }} s {{ ∃ x, Q x }}.
Proof. intro. apply ax_stmt_weaken_post with (Q x); solve_assert. Qed.

Lemma ax_expr_weaken Δ P P' Q Q' e :
  Δ ⊨ₑ {{ P' }} e {{ Q' }} →
  P ⊆ P' →
  (∀ v, Q' v ⊆ Q v) →
  Δ ⊨ₑ {{ P }} e {{ Q }}.
Proof.
  intros Hax HP HQ n k m ??.
  apply ax_weaken with (ax_expr_P Q').
  * intros ?? []; constructor; solve_assert.
  * by apply Hax, HP.
Qed.
Lemma ax_expr_weaken_pre Δ P P' Q e :
  Δ ⊨ₑ {{ P' }} e {{ Q }} →
  P ⊆ P' →
  Δ ⊨ₑ {{ P }} e {{ Q }}.
Proof. intros. eapply ax_expr_weaken; eauto. Qed.
Lemma ax_expr_weaken_post Δ P Q Q' e :
  Δ ⊨ₑ {{ P }} e {{ Q' }} →
  (∀ v, Q' v ⊆ Q v) →
  Δ ⊨ₑ {{ P }} e {{ Q }}.
Proof. intros. eapply ax_expr_weaken; eauto. Qed.

Lemma ax_expr_right_frame Δ A P Q e :
  Δ ⊨ₑ {{ P }} e {{ λ v, Q v }} →
  Δ ⊨ₑ {{ P ★ A }} e {{ λ v, Q v ★ A }}.
Proof.
  intros Hax n k m HΔ Hpre.
  destruct Hpre as [m1 [m2 [? [? [??]]]]]; simplify_equality.
  apply ax_frame with (ax_expr_P Q); auto.
  intros m ?? [v ?]. constructor. solve_assert.
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
  (∀ f Pf c vs,
    Δ' !! f = Some Pf → ∃ sf,
    δ !! f = Some sf ∧
    Δ' ∪ Δ ⊨ₜ {{ Π imap (λ i v, var i ↦ val v) vs ★ fpre Pf c vs }}
     sf
    {{ λ v, Π imap (λ i _, var i ↦ -) vs ★ fpost Pf c vs v }}) →
  ax_funs n Δ →
  ax_funs n (Δ' ∪ Δ).
Proof.
  intros HaxΔ' HΔ.
  induction n as [|n IH]; [by constructor |].
  intros f Pf c vs m k Hf Hpre.
  rewrite finmap_union_Some_raw in Hf.
  destruct Hf as [? | [_ ?]]; [| eapply HΔ; eauto ].
  destruct (HaxΔ' f Pf c vs) as [sf [Hsf Haxsf]]; trivial.

  apply ax_further.
  { intros. solve_cred. }

  intros mf S' ? p. inv_cstep p.
  simplify_map_equality.
  match goal with
  | H : alloc_params _ _ _ _ |- _ =>
    apply alloc_params_insert_list in H;
    destruct H as [? [Hfree ?]]; subst
  end.

  pose proof (is_free_list_nodup _ _ Hfree).
  decompose_is_free.
  rewrite finmap_insert_list_union, (associative_eq (∪)).
  constructor; [solve_mem_disjoint | done |].
  rewrite <-finmap_insert_list_union.

  eapply ax_compose_cons; [| clear dependent m mf S' f Δ].
  { eapply Haxsf; eauto.
    * by apply IH, ax_funs_S.
    * simpl. eauto using assert_alloc_params_alt. }

  intros m ? [d ? Hpost]. apply ax_further_pred.
  { intros. solve_cred. }
  intros mf S' ? p.
  destruct d; discriminate_down_up; inv_cstep p.
  * simpl in Hpost; apply assert_free_params in Hpost; eauto with mem.
    destruct Hpost.
    rewrite finmap_union_delete_list, (delete_list_notin mf).
    { by constructor; [solve_mem_disjoint | done | apply ax_done]. }
    apply Forall_impl with (λ i, ∃ v, m !! i = Some v); auto.
    intros b [??]; eauto using finmap_disjoint_Some_l.
  * simpl in Hpost; apply assert_free_params in Hpost; eauto with mem.
    destruct Hpost.
    rewrite finmap_union_delete_list, (delete_list_notin mf).
    { by constructor; [solve_mem_disjoint | done | apply ax_done]. }
    apply Forall_impl with (λ i, ∃ v, m !! i = Some v); auto.
    intros b [??]; eauto using finmap_disjoint_Some_l.
Qed.

Lemma ax_stmt_funs_add Δ Δ' Pd s :
  (∀ f Pf c vs,
    Δ' !! f = Some Pf → ∃ sf,
    δ !! f = Some sf ∧
    Δ' ∪ Δ ⊨ₜ {{ Π imap (λ i v, var i ↦ val v) vs ★ fpre Pf c vs }}
     sf
    {{ λ v, Π imap (λ i _, var i ↦ -) vs ★ fpost Pf c vs v }}) →
  Δ' ∪ Δ \ Pd ⊨ₚ s →
  Δ \ Pd ⊨ₚ s.
Proof. intros ? Hax ?????. apply Hax; eauto using ax_funs_add. Qed.
Lemma ax_expr_funs_add Δ Δ' P Q e :
  (∀ f Pf c vs,
    Δ' !! f = Some Pf → ∃ sf,
    δ !! f = Some sf ∧
    Δ' ∪ Δ ⊨ₜ {{ Π imap (λ i v, var i ↦ val v) vs ★ fpre Pf c vs }}
     sf
    {{ λ v, Π imap (λ i _, var i ↦ -) vs ★ fpost Pf c vs v }}) →
  Δ' ∪ Δ ⊨ₑ {{ P }} e {{ Q }} →
  Δ ⊨ₑ {{ P }} e {{ Q }}.
Proof. intros ? Hax ?????. apply Hax; eauto using ax_funs_add. Qed.

Lemma ax_call Δ f Pf (c : fcommon Pf)
    {vn} (Ps : vec assert vn) (es : vec expr vn) (Qs : vec vassert vn) :
  Δ !! f = Some Pf →
  (∀ vs, Π vzip_with ($) Qs vs → fpre Pf c vs)%A →
  (∀ i, Δ ⊨ₑ {{ Ps !!! i }} es !!! i {{ Qs !!! i }}) →
  Δ ⊨ₑ {{ Π Ps }} call f @ es {{ λ v, ∃ vs, fpost Pf c vs v }}.
Proof.
  intros Hf HPf Haxs n k m HΔ Hpre.
  apply assert_sep_list_alt_vec in Hpre.
  destruct Hpre as [ms [? [??]]]; subst.
  apply (ax_expr_compose n Qs _ (DCCall f) es k ms); trivial.
  { intros i. by apply Haxs. }

  clear dependent ms es. intros vs ms ? Hax.
  simpl. rewrite vec_to_list_map.

  apply ax_further_pred.
  { intros. solve_cred. }

  intros mf S' ? p.
  apply (cstep_expr_call_inv _ _ _ _ _ _ _ p); clear p.
  * constructor; [done | done |].
    apply ax_compose_cons with (ax_fun_P Pf c vs);
       [|clear dependent ms mf S'].
    { apply ax_pred, HΔ; [done |].
      apply (stack_indep (get_stack k)).
      apply HPf. apply assert_sep_list_alt_vec_2; [done |].
      intros i. by rewrite vzip_with_lookup. }

    intros m' φ' [v Hpost].
    apply (stack_indep _ (get_stack k)) in Hpost.
    apply ax_further_pred.
    { intros. solve_cred. }

    intros mf S' ? p. inv_cstep p.
    by constructor; [| | apply ax_done; constructor; solve_assert].
  * intros. exfalso. eauto with cstep.
Qed.

(** ** Structural rules *)
Lemma ax_expr_base Δ e :
  Δ ⊨ₑ {{ ∃ v, e ⇓ v }} e {{ λ v, e ⇓ v }}.
Proof.
  intros n k m _ [v Heval]. unfold_assert in Heval.
  revert e Heval.
  cut (∀ e e',
    ⟦ e ⟧ (get_stack k) m = Some v →
    ⟦ e' ⟧ (get_stack k) m = Some v →
    ax (ax_expr_P (λ v, (e' ⇓ v)%A)) k n k (Expr e) m).
  { intros help ??. by apply help. }

  induction n as [|n IH]; [by constructor |].
  intros e e' Heval Heval'.
  destruct (decide (is_value e)) as [Hval | Hval].
  { inversion Hval. apply ax_done. constructor. solve_assert. }

  apply ax_further.
  { eauto using cred_expr_eval, expr_eval_weaken_mem with mem. }

  intros mf S' ? p. inv_cstep p.
  * apply expr_eval_subst_inv in Heval.
    destruct Heval as [v' [Heval ?]].
    edestruct ehstep_expr_eval_inv; eauto with mem.
    subst. constructor; [done | done |].
    apply IH; [|done].
    by rewrite (subst_preserves_expr_eval _ _ (val v')).
  * apply expr_eval_subst_inv in Heval.
    by destruct Heval as [? [??]].
  * exfalso. eauto using
      ehsafe_expr_eval_subst, expr_eval_weaken_mem with mem.
Qed.

Lemma ax_assign Δ el Pl Ql er Pr Qr R :
  Δ ⊨ₑ {{ Pl }} el {{ Ql }} →
  Δ ⊨ₑ {{ Pr }} er {{ Qr }} →
  (∀ a v, Ql a ★ Qr v → val a ↦ - ★ R a v)%A →
  Δ ⊨ₑ {{ Pl ★ Pr }} el ::= er {{ λ v, ∃ a, val a ↦ val v ★ R a v }}.
Proof.
  intros Haxl Haxr Hassign n k ?? [m1 [m2 [? [? [??]]]]]; subst.
  rewrite <-(right_id_eq ∅ (∪) m2).
  apply (ax_expr_compose n [# Ql;Qr] _ DCAssign [# el;er] k [# m1;m2]).
  { simpl. solve_mem_disjoint. }
  { intros. inv_all_vec_fin; simpl; auto. }

  clear dependent m1 m2 Δ. intros vs ms.
  inv_vec vs; intros v1 vs; inv_vec vs; intros v2 vs; inv_vec vs.
  inv_vec ms; intros m1 ms; inv_vec ms; intros m2 ms; inv_vec ms.
  simpl. intros Hdisjoint Hax. rewrite (right_id_eq ∅ (∪) m2).
  pose proof (Hax 0%fin) as Haxl. pose proof (Hax 1%fin) as Haxr.
  simpl in Haxl, Haxr. clear Hax.

  destruct (Hassign (get_stack k) (m1 ∪ m2) v1 v2)
    as [m3 [m4 [Hm3m4 [? [[a [? [Ha ?]]] HR]]]]].
  { solve_assert. }
  clear Hassign. unfold_assert in Ha; simpl in Ha.
  rewrite <-Hm3m4. simplify_equality. clear dependent m1 m2.

  apply ax_further_pred.
  { intros. solve_cred. }

  intros mf' S' ? p. inv_cstep p.
  * inv_ehstep.
    rewrite !finmap_union_insert_l, insert_singleton.
    constructor; [solve_mem_disjoint | done |].
    apply ax_done; constructor; solve_assert.
  * exfalso; eauto 6 with cstep.
Qed.

Lemma ax_load Δ e P Q :
  Δ ⊨ₑ {{ P }} e {{ λ a, ∃ v, Q a v ★ val a ↦ val v }} →
  Δ ⊨ₑ {{ P }} load e {{ λ v, ∃ a, Q a v ★ val a ↦ val v }}.
Proof.
  intros Hax n k m ? Hpre.
  rewrite <-(right_id_eq ∅ (∪) m).
  apply (ax_expr_compose n
    [# λ a, ∃ v, Q a v ★ val a ↦ val v]%A _ DCLoad [# e] k [# m]).
  { simpl. solve_mem_disjoint. }
  { intros. inv_all_vec_fin; simpl; auto. }

  clear dependent m Δ. intros vs ms.
  inv_vec vs; intros v vs; inv_vec vs.
  inv_vec ms; intros m ms; inv_vec ms; simpl; intros ? Hax.
  rewrite (right_id_eq ∅ (∪) m).

  specialize (Hax 0%fin). simpl in Hax.
  destruct Hax as [? [m1 [? [? [? [? [a' [v' [? [??]]]]]]]]]];
    simpl in *; simplify_equality.
  apply ax_further_pred.
  { intros. simpl. solve_cred. }

  intros mf S' ? p. inv_cstep p.
  * inv_ehstep. simplify_mem_equality.
    constructor; [solve_mem_disjoint | done | apply ax_done].
    constructor; solve_assert.
  * exfalso; eauto with cstep.
Qed.

Lemma ax_alloc Δ :
  Δ ⊨ₑ {{ emp }} alloc {{ λ a, val a ↦ - }}.
Proof.
  intros n k ???. unfold_assert in *; subst.
  apply ax_further_pred.
  { intros. solve_cred. }
  intros mf S' ? p. rewrite (left_id_eq ∅ (∪)) in p. inv_cstep p.
  * inv_ehstep. rewrite finmap_union_singleton_l.
    constructor; [solve_mem_disjoint | done | apply ax_done].
    constructor. solve_assert.
  * exfalso; eauto with cstep.
Qed.

Lemma ax_free Δ e P Q :
  Δ ⊨ₑ {{ P }} e {{ λ a, Q ★ val a ↦ - }} →
  Δ ⊨ₑ {{ P }} free e {{ λ v, Q }}.
Proof.
  intros Hax n k m ? Hpre.
  rewrite <-(right_id_eq ∅ (∪) m).
  apply (ax_expr_compose n [# λ a, Q ★ val a ↦ -]%A _ DCFree [# e] k [# m]).
  { simpl. solve_mem_disjoint. }
  { intros. inv_all_vec_fin; simpl; auto. }

  clear dependent m Δ. intros vs ms.
  inv_vec vs; intros v vs; inv_vec vs.
  inv_vec ms; intros m ms; inv_vec ms; simpl; intros ? Hax.
  rewrite (right_id_eq ∅ (∪) m).

  specialize (Hax 0%fin). simpl in Hax.
  destruct Hax as [m1 [? [? [? [? [a [v' [??]]]]]]]];
    simpl in *; simplify_equality.
  apply ax_further_pred.
  { intros. simpl. solve_cred. }

  intros mf S' ? p. inv_cstep p.
  * inv_ehstep.
    decompose_map_disjoint.
    rewrite !finmap_union_delete, (delete_notin mf),
      (delete_notin m1), delete_singleton, (right_id_eq ∅ (∪)) by
        by eauto using finmap_disjoint_Some_r.
    by constructor; [| | apply ax_done].
  * exfalso; eauto with cstep.
Qed.

Lemma ax_unop Δ op e P Q :
  Δ ⊨ₑ {{ P }} e {{ Q }} →
  (∀ v, Q v → @{op} val v ⇓-)%A →
  Δ ⊨ₑ {{ P }} @{op} e
       {{ λ v', ∃ v, @{op} val v ⇓ v' ∧ Q v }}.
Proof.
  intros Hax Hop n k m ??.
  rewrite <-(right_id_eq ∅ (∪) m).
  apply (ax_expr_compose n [# Q] _ (DCUnOp op) [# e] k [# m]).
  { simpl. solve_mem_disjoint. }
  { intros. inv_all_vec_fin; simpl; auto. }

  clear dependent m Δ. intros vs ms.
  inv_vec vs; intros v vs; inv_vec vs.
  inv_vec ms; intros m ms; inv_vec ms.
  simpl. intros Hdisjoint Hax. rewrite (right_id_eq ∅ (∪) m).
  specialize (Hax 0%fin). simpl in Hax.

  destruct (Hop (get_stack k) m v) as [v' Hv'].
  { solve_assert. }
  clear Hop. unfold_assert in Hv'; simpl in Hv'.

  apply ax_further_pred.
  { intros. solve_cred. }

  intros mf' S' ? p. inv_cstep p.
  * inv_ehstep.
    constructor; [solve_mem_disjoint | done |].
    apply ax_done; constructor.
    exists v. solve_assert.
  * exfalso; eauto with cstep.
Qed.

Lemma ax_binop Δ op el Pl Ql er Pr Qr :
  Δ ⊨ₑ {{ Pl }} el {{ Ql }} →
  Δ ⊨ₑ {{ Pr }} er {{ Qr }} →
  (∀ vl vr, Ql vl ★ Qr vr → val vl @{op} val vr ⇓-)%A →
  Δ ⊨ₑ {{ Pl ★ Pr }} el @{op} er
       {{ λ v', ∃ vl vr, val vl @{op} val vr ⇓ v' ∧ (Ql vl ★ Qr vr) }}.
Proof.
  intros Haxl Haxr Hop n k ?? [m1 [m2 [? [? [??]]]]]; subst.
  rewrite <-(right_id_eq ∅ (∪) m2).
  apply (ax_expr_compose n [# Ql;Qr] _ (DCBinOp op) [# el;er] k [# m1;m2]).
  { simpl. solve_mem_disjoint. }
  { intros. inv_all_vec_fin; simpl; auto. }

  clear dependent m1 m2 Δ. intros vs ms.
  inv_vec vs; intros v1 vs; inv_vec vs; intros v2 vs; inv_vec vs.
  inv_vec ms; intros m1 ms; inv_vec ms; intros m2 ms; inv_vec ms.
  simpl. intros Hdisjoint Hax. rewrite (right_id_eq ∅ (∪) m2).
  pose proof (Hax 0%fin) as Haxl. pose proof (Hax 1%fin) as Haxr.
  simpl in Haxl, Haxr. clear Hax.

  destruct (Hop (get_stack k) (m1 ∪ m2) v1 v2) as [v' Hv'].
  { solve_assert. }
  clear Hop. unfold_assert in Hv'; simpl in Hv'.

  apply ax_further_pred.
  { intros. solve_cred. }

  intros mf' S' ? p. inv_cstep p.
  * inv_ehstep.
    constructor; [solve_mem_disjoint | done |].
    apply ax_done; constructor.
    exists v1 v2. solve_assert.
  * exfalso; eauto with cstep.
Qed.

Lemma ax_expr_if Δ e el er P P' Q :
  Δ ⊨ₑ {{ P }} e {{ P' }} →
  Δ ⊨ₑ {{ assert_is_true P' }} el {{ Q }} →
  Δ ⊨ₑ {{ assert_is_false P' }} er {{ Q }} →
  Δ ⊨ₑ {{ P }} IF e then el else er {{ Q }}.
Proof.
  intros Hax Haxl Haxr n k m HΔ Hpre.
  rewrite <-(right_id_eq ∅ (∪) m).
  apply (ax_expr_compose n [# P'] _ (DCIf el er) [# e] k [# m]).
  { simpl. solve_mem_disjoint. }
  { intros. inv_all_vec_fin; simpl; auto. }

  clear dependent e m. intros vs ms.
  inv_vec vs; intros v vs; inv_vec vs.
  inv_vec ms; intros m ms; inv_vec ms; simpl; intros ? Hax.
  rewrite (right_id_eq ∅ (∪) m).
  specialize (Hax 0%fin). simpl in Hax.

  apply ax_further_pred.
  { intros. simpl. destruct (value_true_false_dec v); solve_cred. }

  intros mf S' ? p. inv_cstep p.
  * inv_ehstep.
    + constructor; [solve_mem_disjoint | done |].
      apply Haxl. auto with ax. solve_assert.
    + constructor; [solve_mem_disjoint | done |].
      apply Haxr. auto with ax. solve_assert.
  * exfalso; destruct (value_true_false_dec v); eauto with cstep.
Qed.

Lemma ax_do Δ R J P Q e : 
  Δ ⊨ₑ {{ P }} e {{ λ _, Q }} →
  Δ \ R \ J ⊨ₛ {{ P }} do e {{ Q }}.
Proof.
  intros Hax n k [] m ???; discriminate_down_up.
  apply ax_further_pred.
  { intros. solve_cred. }
  intros mf S' ? p. inv_cstep p.
  constructor; [done | done | clear dependent mf S'].
  eapply ax_compose_cons; auto with ax.
  intros m' φ' [v ?]. apply ax_further_pred.
  { intros. solve_cred. }
  intros mf S' ? p. inv_cstep p.
  constructor; [done | done | clear dependent m mf φ' v S'].
  by apply ax_done; constructor.
Qed.

Lemma ax_skip Δ R J P : Δ \ R \ J ⊨ₛ {{ P }} skip {{ P }}.
Proof.
  intros n k [] m ???; discriminate_down_up.
  apply ax_further_pred.
  { intros. solve_cred. }
  intros mf S' ? p. inv_cstep p.
  constructor; [done | done |clear dependent mf S'].
  by apply ax_done; constructor.
Qed.

Lemma ax_ret Δ J P R e Q :
  Δ ⊨ₑ {{ P }} e {{ R }} →
  Δ \ R \ J ⊨ₛ {{ P }} ret e {{ Q }}.
Proof.
  intros Hax n k [] m ???; discriminate_down_up.
  apply ax_further_pred.
  { intros. solve_cred. }
  intros mf S' ? p. inv_cstep p.
  constructor; [done | done | clear dependent mf S'].
  eapply ax_compose_cons; auto with ax.
  intros m' φ' [v ?]. apply ax_further_pred.
  { intros. solve_cred. }
  intros mf S' ? p. inv_cstep p.
  constructor; [done | done | clear dependent m mf φ' S'].
  by apply ax_done; constructor.
Qed.

Lemma ax_packed_blk Δ Pd s :
  Δ \ (λ P, var O ↦ - ★ P↑)%A <$> Pd ⊨ₚ s →
  Δ \ Pd ⊨ₚ blk s.
Proof.
  intros Hax n k. revert n.
  cut (∀ n d m b v,
   ax_funs n Δ → is_free m b → down d s →
   (Pd d) (get_stack k) m →
   ax (ax_stmt_P (blk s) Pd) k n
     (CBlock b :: k) (Stmt d s) (<[b:=v]>m)).
  { intros help n d m ???. apply ax_further_pred.
    { intros. solve_cred. }
    intros mf S' ? p.
    destruct d; discriminate_down_up; inv_cstep p;
      rewrite finmap_union_insert_l; decompose_is_free;
      by constructor; [solve_mem_disjoint | |]; auto with ax. }

  intros n d m b v ????.
  eapply ax_compose_cons; [| clear dependent m v d].
  { eapply Hax; simpl; eauto.
    rewrite directed_fmap_spec. by apply assert_alloc. }

  intros m φ [d ? Hpost]. apply ax_further_pred.
  { intros. solve_cred. }

  rewrite directed_fmap_spec in Hpost. simpl in Hpost.
  apply assert_free in Hpost. destruct Hpost as [? [v' ?]].
  intros mf S' ? p.
  destruct d; discriminate_down_up; inv_cstep p;
    rewrite finmap_union_delete, (delete_notin mf)
      by eauto using finmap_disjoint_Some_l;
    by constructor; [solve_mem_disjoint | | apply ax_done].
Qed.

Lemma ax_blk Δ R J P Q s :
  Δ \ (λ v, var O ↦ - ★ R v↑) \ (λ l, var O ↦ - ★ J l↑)
    ⊨ₛ {{ var O ↦ - ★ P↑ }} s {{ var O ↦ - ★ Q↑ }} →
  Δ \ R \ J ⊨ₛ {{ P }} blk s {{ Q }}.
Proof. intros. by apply ax_packed_blk. Qed.

Lemma ax_label Δ R J l s Q :
  Δ \ R \ J ⊨ₛ {{ J l }} s {{ Q }} →
  Δ \ R \ J ⊨ₛ {{ J l }} l :; s {{ Q }}.
Proof.
  intros Hax n k. revert n.
  set (Pd := dassert_pack (J l) Q R J).
  cut (∀ n d m,
   ax_funs n Δ → down d s → Pd d (get_stack k) m →
   ax (ax_stmt_P (l :; s) Pd) k n
     (CStmt (l :; □) :: k) (Stmt d s) m).
  { intros help n d m ???. apply ax_further_pred.
    { intros. clear dependent Pd. solve_cred. }
    intros mf S' ? p.
    destruct d; discriminate_down_up; inv_cstep p;
      by constructor; auto with ax. }

  induction n as [|n IH]; [constructor |].
  intros d m ???.
  eapply ax_compose_cons; [by apply Hax | clear dependent m d].

  intros m φ [d ? Hpost]. apply ax_further.
  { intros. solve_cred. }

  intros mf S' ? p. destruct d; discriminate_down_up; inv_cstep p.
  * by constructor; [| | apply ax_done].
  * by constructor; [| | apply ax_done].
  * match goal with
    | _ : ?l' ∉ labels s |- _ => destruct (decide (l' = l))
    end; subst.
    + constructor; [done | done | apply ax_further_pred].
      { intros. solve_cred. }
      intros mf' S'' ? p. inv_cstep p.
      by constructor; auto with ax.
    + by constructor; [| | apply ax_done; constructor; solve_elem_of].
Qed.

Lemma ax_while Δ R J P Q e s :
  Δ ⊨ₑ {{ P }} e {{ Q }} →
  Δ \ R \ J ⊨ₛ {{ assert_is_true Q }} s {{ P }} →
  Δ \ R \ J ⊨ₛ {{ P }} while (e) s {{ assert_is_false Q }}.
Proof.
  intros Haxe Hax n k. revert n.
  set (Pd := dassert_pack P (assert_is_false Q) R J).
  set (Pd' := dassert_pack (assert_is_true Q) P R J).
  cut (∀ n d m,
   ax_funs n Δ → down d s → Pd' d (get_stack k) m →
   ax (ax_stmt_P (while (e) s) Pd) k n
     (CStmt (while (e) □) :: k) (Stmt d s) m).
  { intros help n [] m ???; discriminate_down_up.
    * apply ax_further_pred.
      { intros. solve_cred. }
      intros mf S' ? p. inv_cstep p.
      constructor; [done | done |].
      eapply ax_compose_cons;
        [apply Haxe; auto with ax | clear dependent m mf S'].
      intros m φ [v ?]. apply ax_further_pred.
      { intros. destruct (value_true_false_dec v); solve_cred. }
      intros mf S' ? p. inv_cstep p.
      + by constructor; [| | apply help; auto with ax; solve_assert].
      + by constructor; [| | apply ax_done; constructor; solve_assert].
    * apply ax_further_pred.
      { intros. solve_cred. }
      intros mf S' ? p. inv_cstep p. by constructor; auto with ax. }

  induction n as [|n IH]; [constructor |].
  intros d m ???.
  eapply ax_compose_cons; [by apply Hax | clear dependent m d].

  intros m φ [d ? Hpost]. apply ax_further.
  { intros. solve_cred. }

  intros mf S' ? p. destruct d; discriminate_down_up; inv_cstep p.
  * constructor; [done | done | clear dependent φ mf S'].
    apply ax_further_pred.
    { intros. solve_cred. }
    intros mf S' ? p. inv_cstep p.
    constructor; [done | done |].
    eapply ax_compose_cons;
      [apply Haxe; auto with ax | clear dependent m mf S'].
    intros m φ [v ?]. apply ax_further_pred.
    { intros. destruct (value_true_false_dec v); solve_cred. }
    intros mf S' ? p. inv_cstep p.
    + constructor; [done | done |].
      apply ax_pred, ax_pred, IH; auto with ax; solve_assert.
    + by constructor; [| | apply ax_done; constructor; solve_assert].
  * by constructor; [| | apply ax_done].
  * by constructor; [| | apply ax_done].
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
   (down d sl → Pdl d (get_stack k) m →
     ax (ax_stmt_P (sl ;; sr) Pd) k n
       (CStmt (□ ;; sr) :: k) (Stmt d sl) m)
   ∧ (down d sr → Pdr d (get_stack k) m →
     ax (ax_stmt_P (sl ;; sr) Pd) k n
       (CStmt (sl ;; □) :: k) (Stmt d sr) m)).
  { intros help n d m ???. apply ax_further_pred.
    { intros. solve_cred. }
    intros mf S' ? p.
    destruct d; discriminate_down_up; inv_cstep p;
      by constructor; [done | done | eapply help]; eauto with ax. }

  induction n as [|n IH]; [repeat constructor |].
  intros d m ?; split; intros ??.

  * eapply ax_compose_cons; [by apply Haxl | clear dependent m d].
    intros m φ [d ? Hpost]. apply ax_further.
    { intros. solve_cred. }

    intros mf S' ? p. destruct d; discriminate_down_up; inv_cstep p.
    + constructor; [done | done | eapply IH]; auto with ax arith.
    + by constructor; [| | apply ax_done].
    + match goal with
      | _ : ?l ∉ labels sl |- _ => destruct (decide (l ∈ labels sr))
      end; subst.
      - constructor; [done | done | apply ax_further_pred].
        { intros. solve_cred. }
        intros mf' S'' ? p. inv_cstep p.
        constructor; [done | done | apply ax_pred, IH]; auto with ax.
      - by constructor; [| | apply ax_done; constructor; solve_elem_of].

  * eapply ax_compose_cons; [by apply Haxr | clear dependent m d].
    intros m φ [d ? Hpost]. apply ax_further.
    { intros. solve_cred. }

    intros mf S' ? p. destruct d; discriminate_down_up; inv_cstep p.
    + by constructor; [| | apply ax_done].
    + by constructor; [| | apply ax_done].
    + match goal with
      | _ : ?l ∉ labels sr |- _ => destruct (decide (l ∈ labels sl))
      end; subst.
      - constructor; [done | done | apply ax_further_pred].
        { intros. solve_cred. }
        intros mf' S'' ? p. inv_cstep p.
        constructor; [done | done | apply ax_pred, IH]; auto with ax.
      - by constructor; [| | apply ax_done; constructor; solve_elem_of].
Qed.

Lemma ax_if Δ R J e sl sr P P' Q :
  Δ ⊨ₑ {{ P }} e {{ P' }} →
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
   (down d sl → Pdl d (get_stack k) m →
     ax (ax_stmt_P (IF e then sl else sr) Pd) k n
       (CStmt (IF e then □ else sr) :: k) (Stmt d sl) m)
   ∧ (down d sr → Pdr d (get_stack k) m →
     ax (ax_stmt_P (IF e then sl else sr) Pd) k n
       (CStmt (IF e then sl else □) :: k) (Stmt d sr) m)).
  { intros help n [] m ???; discriminate_down_up.
    * apply ax_further_pred.
      { intros. solve_cred. }
      intros mf S' ? p. inv_cstep p.
      constructor; [done | done |].
      eapply ax_compose_cons;
        [apply Haxe; auto with ax | clear dependent m mf S'].
      intros m φ [v ?]. apply ax_further_pred.
      { intros. destruct (value_true_false_dec v); solve_cred. }
      intros mf S' ? p. inv_cstep p;
        by constructor; [| | apply help; auto with ax; solve_assert].
    * apply ax_further_pred.
      { intros. solve_cred. }
      intros mf S' ? p. inv_cstep p;
        by constructor; [| | apply help; auto with ax]. }

  induction n as [|n IH]; [repeat constructor |].
  intros d m ?; split; intros ??.

  * eapply ax_compose_cons; [by apply Haxl | clear dependent m d].
    intros m φ [d ? Hpost]. apply ax_further.
    { intros. solve_cred. }

    intros mf S' ? p. destruct d; discriminate_down_up; inv_cstep p.
    + by constructor; [| | apply ax_done].
    + by constructor; [| | apply ax_done].
    + match goal with
      | _ : ?l ∉ labels sl |- _ => destruct (decide (l ∈ labels sr))
      end; subst.
      - constructor; [done | done | apply ax_further_pred].
        { intros. solve_cred. }
        intros mf' S'' ? p. inv_cstep p.
        constructor; [done | done | apply ax_pred, IH]; auto with ax.
      - by constructor; [| | apply ax_done; constructor; solve_elem_of].

  * eapply ax_compose_cons; [by apply Haxr | clear dependent m d].
    intros m φ [d ? Hpost]. apply ax_further.
    { intros. solve_cred. }

    intros mf S' ? p. destruct d; discriminate_down_up; inv_cstep p.
    + by constructor; [| | apply ax_done].
    + by constructor; [| | apply ax_done].
    + match goal with
      | _ : ?l ∉ labels sr |- _ => destruct (decide (l ∈ labels sl))
      end; subst.
      - constructor; [done | done | apply ax_further_pred].
        { intros. solve_cred. }
        intros mf' S'' ? p. inv_cstep p.
        constructor; [done | done | apply ax_pred, IH]; auto with ax.
      - by constructor; [| | apply ax_done; constructor; solve_elem_of].
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
  (at level 74, P at next level,
   format "δ  \  Δ  \  P  ⊨ₚ  '[' s ']'").
Notation "δ \ Δ \ R \ J ⊨ₛ {{ P }} s {{ Q }}" :=
  (ax_stmt δ Δ R%A J%A P%A s%S Q%A)
  (at level 74, J at next level, R at next level,
   format "δ  \  Δ  \  R  \  J  ⊨ₛ  '[' {{  P  }} '/'  s  '/' {{  Q  }} ']'").
Notation "δ \ Δ ⊨ₜ {{ P }} s {{ Q }}" :=
  (ax_stmt_top δ Δ P%A s%S Q%A)
  (at level 74, format "δ  \  Δ  ⊨ₜ  '[' {{  P  }} '/'  s  '/' {{  Q  }} ']'").
Notation "δ \ Δ ⊨ₑ {{ P }} e {{ Q }}" :=
  (ax_expr δ Δ P%A e%E Q%A)
  (at level 74, format "δ  \  Δ  ⊨ₑ  '[' {{  P  }} '/'  e  '/' {{  Q  }} ']'").
