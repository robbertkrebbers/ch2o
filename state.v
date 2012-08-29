(* Copyright (c) 2012, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** Our operational semantics is a binary relation between execution states. We
consider three kinds of execution states:
- Execution of statements,
- Calling a function,
- Returning from a function.

When execution of a statement is finished, a transition to the return state
is performed. The return state then performs a transition back to the caller.
When a function is called, a transition to the call state is performed. The call
state then performs a transition to a statement state with the called function's
body. This distinction between execution states is adapted from Compcert,
however we do not consider an explicit stuck state for undefined behavior. *)
Require Export statements.

(** * Definitions *)
(** Execution of statements is performed by moving the focus of the substatement
that is being executed. This movement may occur in four directions: down [↘]
towards a leaf (assignment, skip, ...), up [↗] from a leaf to the next statement
to be executed, to the top [⇈] after a return, or it may jump [↷] to a label
after a goto. *)
Inductive direction :=
  | Down : direction
  | Up : direction
  | Top : option value → direction
  | Jump : label → direction.
Notation "↘" := Down : C_scope.
Notation "↗" := Up : C_scope.
Notation "⇈ mv" := (Top mv) (at level 20) : C_scope.
Notation "↷ l" := (Jump l) (at level 20) : C_scope.

Instance direction_eq_dec (d1 d2 : direction) : Decision (d1 = d2).
Proof. solve_decision. Defined.

Definition down (d : direction) (s : stmt) : Prop :=
  match d with
  | ↘ => True
  | ↷ l => l ∈ labels s
  | _ => False
  end.
Definition up (d : direction) (s : stmt) : Prop :=
  match d with
  | ↗ => True
  | ⇈ _ => True
  | ↷ l => l ∉ labels s
  | _ => False
  end.

Hint Extern 0 (down _ _) => constructor.
Hint Extern 0 (up _ _) => constructor.

Lemma not_down_up d s : ¬down d s → up d s.
Proof. destruct d; intuition. Qed.

Definition down_up_dec d s : {down d s} + {up d s} :=
  match d with
  | ↘ => left I
  | ↗ => right I
  | ⇈ _ => right I
  | ↷ l => decide_rel (∈) l (labels s)
  end.

(** The type [location] contains the part of the execution states that is not
shared between the three kinds of execution states. An execution state [state]
is a [location] equiped with a program context and memory. A statement state
[Stmt] contains the statement to be executed and the direction in which the
execution is performed, a call state [Call] contains the name of the function
to be called, and the values of the arguments, and a return state [Return]
contains the return value of the called function. *)
Inductive location :=
  | Stmt : direction → stmt → location
  | Call : funname → list value → location
  | Return : option value → location.

Record state := State {
  SCtx : ctx;
  SLoc : location;
  SMem : mem
}.
Add Printing Constructor state.

Instance location_eq_dec (loc1 loc2 : location) : Decision (loc1 = loc2).
Proof. solve_decision. Defined.
Instance state_eq_dec (S1 S2 : state) : Decision (S1 = S2).
Proof. solve_decision. Defined.

(** * Theorems *)
(** Our definition of execution state allows many incorrect states. For example,
while in a [Call] state, the context should always contain a [CCall] as its last
element, whereas this is not enforced by the definition of execution states.
We define the proposition [ctx_wf k loc k' loc'] which states that starting at
a state with location [loc] in context [k], it is valid to build a state with
location [loc'] in context [k']. *)

(** In the file [smallstep], we will prove that our operational semantics
preserves well formed statements. This is the key property to prove that if 
[State k (Stmt d s) m] reduces to [State k (Stmt d' s') m'], then we have
[s = s']. *)

(** We restrict to a type of locations [simple_location] that contains less
information than [location] so as to obtain a more powerful induction principle
for [ctx_wf]. *)
Inductive simple_location :=
  | Stmt_ : stmt → simple_location
  | Call_ : funname → simple_location
  | Return_ : simple_location.

Definition to_simple_location (loc : location) : simple_location :=
  match loc with
  | Stmt _ s => Stmt_ s
  | Call f _ => Call_ f
  | Return _ => Return_
  end.
Coercion to_simple_location : location >-> simple_location.

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

Section ctx_wf.
Context (δ : funenv).

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
Proof. induction 1; simpl in *; solve_suffix_of. Qed.

Lemma ctx_wf_related k loc k' loc1 loc2 :
  ctx_wf k loc k' loc1 → ctx_wf k loc k' loc2 → loc1 ≍ loc2.
Proof.
  intros wf1. revert loc2.
  induction wf1; inversion 1; subst; simpl in *; trivial; try
    match goal with
    | H : ctx_wf _ _ _ _ |- _ =>
      apply ctx_wf_suffix_of in H; solve_suffix_of
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
