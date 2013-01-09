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
Proof. destruct d; simpl; intuition. Qed.

Definition down_up_dec d s : {down d s} + {up d s} :=
  match d with
  | ↘ => left I
  | ↗ => right I
  | ⇈ _ => right I
  | ↷ l => decide_rel (∈) l (labels s)
  end.

Tactic Notation "discriminate_down_up" hyp(H) := repeat
  match type of H with
  | up _ _ => progress simpl in H
  | down _ _ => progress simpl in H
  | True => clear H
  | False => destruct H
  | ?l ∉ _ => destruct H; solve_stmt_elem_of
  | ?l ∈ _ => solve [decompose_elem_of H]
  end.
Tactic Notation "discriminate_down_up" := repeat
  match goal with
  | H : up _ _ |- _ => discriminate_down_up H
  | H : down _ _ |- _ => discriminate_down_up H
  end.

(** The type [focus] describes the part of the program that is currently
focused. An execution state [state] is a [focus] equipped with a program context
and memory. The focus [Stmt] is used for execution of statements. It contains
the statement to be executed and the direction in which the execution should be
performed. The focus [Call] is used to call a function, it contains the name of
the called function and the values of the arguments. The focus [Return] is used
to return from the called function to the calling function, it contains the
return value. *)
Inductive focus :=
  | Stmt : direction → stmt → focus
  | Call : funname → list value → focus
  | Return : option value → focus.

Record state := State {
  SCtx : ctx;
  SFoc : focus;
  SMem : mem
}.
Add Printing Constructor state.

Instance focus_eq_dec (φ1 φ2 : focus) : Decision (φ1 = φ2).
Proof. solve_decision. Defined.
Instance state_eq_dec (S1 S2 : state) : Decision (S1 = S2).
Proof. solve_decision. Defined.

(** * Theorems *)
(** Our definition of execution state allows many incorrect states. For example,
while in a [Call] state, the context should always contain a [CCall] as its last
element, whereas this is not enforced by the definition of execution states.
We define the proposition [ctx_wf k φ k' φ'] which states that starting at
a state with focus [φ] in context [k], it is valid to build a state with
focus [φ'] in context [k']. *)

(** In the file [smallstep], we will prove that our operational semantics
preserves well-formed statements. This is the key property to prove that if 
[State k (Stmt d s) m] reduces to [State k (Stmt d' s') m'], then we have
[s = s']. *)

(** We restrict to a type of focuss [simple_focus] that contains less
information than [focus] so as to obtain a more powerful induction principle
for [ctx_wf]. *)
Inductive simple_focus :=
  | Stmt_ : stmt → simple_focus
  | Call_ : funname → simple_focus
  | Return_ : simple_focus.

Definition to_simple_focus (φ : focus) : simple_focus :=
  match φ with
  | Stmt _ s => Stmt_ s
  | Call f _ => Call_ f
  | Return _ => Return_
  end.
Coercion to_simple_focus : focus >-> simple_focus.

Definition simple_focus_related (φ1 φ2 : simple_focus) : Prop :=
  match φ1, φ2 with
  | Stmt_ s1, Stmt_ s2 => s1 = s2
  | Call_ f1, Call_ f2 => f1 = f2
  | _, _ => True
  end.
Local Infix "≍" := simple_focus_related (at level 80).
Arguments simple_focus_related !_ !_.

Instance: Reflexive simple_focus_related.
Proof. by intros []. Qed.

Section ctx_wf.
Context (δ : funenv).

Inductive ctx_wf (k : ctx) (φ : simple_focus) :
      ctx → simple_focus → Prop :=
  | ctx_wf_start :
     ctx_wf k φ k φ
  | ctx_wf_item k' E s :
     ctx_wf k φ k' (Stmt_ (subst E s)) →
     ctx_wf k φ (CItem E :: k') (Stmt_ s)
  | ctx_wf_bφk k' b s :
     ctx_wf k φ k' (Stmt_ (block s)) →
     ctx_wf k φ (CBlock b :: k') (Stmt_ s)
  | ctx_wf_call k' e f es :
     ctx_wf k φ k' (Stmt_ (SCall e f es)) →
     ctx_wf k φ (CCall e f es :: k') (Call_ f)
  | ctx_wf_return k' f :
     ctx_wf k φ k' (Call_ f) →
     ctx_wf k φ k' Return_
  | ctx_wf_params k' f bs s :
     δ !! f = Some s →
     ctx_wf k φ k' (Call_ f) →
     ctx_wf k φ (CParams bs :: k') (Stmt_ s).

Lemma ctx_wf_suffix_of k φ k' φ' :
  ctx_wf k φ k' φ' → suffix_of k k'.
Proof. induction 1; simpl in *; solve_suffix_of. Qed.

Lemma ctx_wf_related k φ k' φ1 φ2 :
  ctx_wf k φ k' φ1 → ctx_wf k φ k' φ2 → φ1 ≍ φ2.
Proof.
  intros wf1. revert φ2.
  induction wf1; inversion 1; subst; simpl in *; trivial; try
    match goal with
    | H : ctx_wf _ _ _ _ |- _ =>
      apply ctx_wf_suffix_of in H; solve_suffix_of
    end.
  * destruct φ; simpl in *; auto.
  * eapply (injective (subst _)), (IHwf1 (Stmt_ _)); eassumption.
  * eapply (injective SBlock), (IHwf1 (Stmt_ _)); eassumption.
  * efeed specialize IHwf1; eauto; simpl in *; congruence.
Qed.

Lemma ctx_wf_unique k φ k' s1 s2 :
  ctx_wf k φ k' (Stmt_ s1) → ctx_wf k φ k' (Stmt_ s2) → s1 = s2.
Proof. apply ctx_wf_related. Qed.
End ctx_wf.
