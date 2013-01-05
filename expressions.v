(* Copyright (c) 2012, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file defines expressions and some associated theory. Most importantly,
to define the operational semantics of expressions in the file [smallstep], we
define evaluation contexts here. Besides, we define a denotational semantics
for side-effect free expressions. Notations for expressions are declared in the
scope [expr_scope]. *)
Require Export memory contexts.

(** * Function names *)
(** We use the type [N] of binary natural numbers for function names, and the
implementation [Nmap] for efficient finite maps over function names. *)
Definition funname := N.
Definition funmap := Nmap.

Instance funname_eq_dec: ∀ i1 i2: funname, Decision (i1 = i2) := decide_rel (=).
Instance funname_fresh `{FinCollection funname C} : Fresh funname C := _.
Instance funname_fresh_spec `{FinCollection funname C} :
  FreshSpec funname C := _.

Instance funmap_dec {A} `{∀ a1 a2 : A, Decision (a1 = a2)} :
  ∀ m1 m2 : funmap A, Decision (m1 = m2) := decide_rel (=).
Instance funmap_empty {A} : Empty (funmap A) := @empty (Nmap A) _.
Instance funmap_lookup {A} : Lookup funname A (funmap A) :=
  @lookup _ _ (Nmap A) _.
Instance funmap_partial_alter {A} : PartialAlter funname A (funmap A) :=
  @partial_alter _ _ (Nmap A) _.
Instance funmap_to_list {A} : FinMapToList funname A (funmap A) :=
  @finmap_to_list _ _ (funmap A) _.
Instance funmap_merge {A} : Merge A (funmap A) := @merge _ (Nmap A) _.
Instance funmap_fmap: FMap funmap := λ A B f, @fmap Nmap _ _ f _.
Instance: FinMap funname funmap := _.

Typeclasses Opaque funname funmap.

(** * Operations *)
(** We define a data type of unary and binary operations, and give denotations
for these as partial functions over values. *)
Inductive unop :=
  | NotOp | NegOp.
Inductive binop :=
  | PlusOp | MinusOp | MultOp | DivOp | ModOp
  | LeOp | LtOp | EqOp.

Instance unop_eq_dec (op1 op2 : unop) : Decision (op1 = op2).
Proof. solve_decision. Defined.
Instance binop_eq_dec (op1 op2 : binop) : Decision (op1 = op2).
Proof. solve_decision. Defined.

Definition eval_unop (op : unop) (v : value) : option value :=
  match op, v with
  | NotOp, v =>
    if value_true_false_dec v then Some (int 0) else Some (int 1)
  | NegOp, int x => Some (int (-x))
  | _, _ => None
  end%V.
Definition eval_binop (op : binop) (v1 v2 : value) : option value :=
  match op, v1, v2 with
  | PlusOp, int x1, int x2 => Some (int (x1 + x2))
  | MinusOp, int x1, int x2 => Some (int (x1 - x2))
  | MultOp, int x1, int x2 => Some (int (x1 * x2))
  | DivOp, int x1, int x2 => Some (int (x1 / x2))
  | ModOp, int x1, int x2 => Some (int (Zmod x1 x2))
  | LeOp, int x1, int x2 => Some (int (Z_decide_rel (≤)%Z x1 x2))
  | LtOp, int x1, int x2 => Some (int (Z_decide_rel (<)%Z x1 x2))
  | EqOp, int x1, int x2 => Some (int (Z_decide_rel (=) x1 x2))
  | EqOp, ptr b1, ptr b2 => Some (int (Z_decide_rel (=) b1 b2))
  | EqOp, null, null => Some (int 1)
  | EqOp, int _, null => Some (int 0)
  | EqOp, null, int _ => Some (int 0)
  | _, _, _ => None
  end%V.

(** * Syntax *)
(** The variables used in expressions are De Bruijn indexes, i.e. the variable
[var i] refers to the [i]th value on the stack. De Bruijn indexes avoid us
having to deal with shadowing due to block scope variables. Especially in
the axiomatic semantics this is useful, as we do not want to loose information
because a local variable may shadow an already existing one. *)
Inductive expr : Type :=
  | EVar : nat → expr
  | EVal : value → expr
  | EAssign : expr → expr → expr
  | ECall : funname → list expr → expr
  | ELoad : expr → expr
  | EAlloc : expr
  | EFree : expr → expr
  | EUnOp : unop → expr → expr
  | EBinOp : binop → expr → expr → expr
  | EIf : expr → expr → expr → expr.

(** Stacks are lists of memory indexes rather than lists of values. This allows
us to treat pointers to both local and allocated storage in a uniform way.
Evaluation of a variable will therefore consist of a looking up its address in
the stack and returning a pointer to that address. *)

Notation stack := (list index) (only parsing).

(** We use the scope [expr_scope] to declare notations for expressions. We
overload some notations already in [value_scope], and define both general and
specific notations for operations, allowing us for example to to write
[int 10 + int 20] instead of the much longer
[val (int 10) @op{PlusOp} val (int 20)]. *)
Delimit Scope expr_scope with E.
Bind Scope expr_scope with expr.
Arguments EAssign _%expr_scope _%expr_scope.
Arguments ECall _ _%expr_scope.
Arguments ELoad _%expr_scope.
Arguments EFree _%expr_scope.
Arguments EUnOp _ _%expr_scope.
Arguments EBinOp _ _%expr_scope _%expr_scope.

Notation "'var' x" := (EVar x) (at level 10) : expr_scope.
Notation "'val' v" := (EVal v) (at level 10) : expr_scope.
Notation "'void'" := (EVal void) : expr_scope.
Notation "'int' x" := (EVal (int x%Z)) : expr_scope.
Notation "'ptr' b" := (EVal (ptr b%N)) : expr_scope.
Notation "'null'" := (EVal null) : expr_scope.
Infix "::=" := EAssign (at level 60) : expr_scope.
(* The infixes ++ and :: are at level 60, <$> at 65. *)
Notation "'call' f @ es" := (ECall f es)
  (at level 10, es at level 66) : expr_scope.
Notation "'load' e" := (ELoad e) (at level 10) : expr_scope.
Notation "'alloc'" := EAlloc : expr_scope.
Notation "'free' e" := (EFree e) (at level 10) : expr_scope.
Notation "@{ op } e" := (EUnOp op e)
  (at level 21, format "@{ op }  e") : expr_scope.
Notation "el @{ op } er" := (EBinOp op el er)
  (at level 50, format "el  @{ op }  er") : expr_scope.
Notation "'IF' e 'then' el 'else' er" := (EIf e el er) : expr_scope.

Infix "+" := (EBinOp PlusOp) : expr_scope.
Infix "-" := (EBinOp MinusOp) : expr_scope.
Infix "*" := (EBinOp MultOp) : expr_scope.
Infix "/" := (EBinOp DivOp) : expr_scope.
Infix "≤" := (EBinOp LeOp) : expr_scope.
Infix "<" := (EBinOp LtOp) : expr_scope.
Infix "=" := (EBinOp EqOp) : expr_scope.
Notation "- e" := (EUnOp NegOp e) : expr_scope.

Instance: Injective (=) (=) EVar.
Proof. by injection 1. Qed.
Instance: Injective (=) (=) EVal.
Proof. by injection 1. Qed.
Instance: Injective (=) (=) ELoad.
Proof. by injection 1. Qed.
Instance: Injective (=) (=) EFree.
Proof. by injection 1. Qed.

Instance expr_eq_dec: ∀ e1 e2 : expr, Decision (e1 = e2).
Proof.
  refine (fix go e1 e2 : Decision (e1 = e2) :=
  match e1, e2 with
  | var i1, var i2 => cast_if (decide_rel (=) i1 i2)
  | val v1, val v2 => cast_if (decide_rel (=) v1 v2)
  | el1 ::= er1, el2 ::= er2 => cast_if_and (decide_rel (=) el1 el2)
     (decide_rel (=) er1 er2)
  | call f1 @ es1, call f2 @ es2 => cast_if_and (decide_rel (=) f1 f2)
     (decide_rel (=) es1 es2)
  | load e1, load e2 => cast_if (decide_rel (=) e1 e2)
  | alloc, alloc => left _
  | free e1, free e2 => cast_if (decide_rel (=) e1 e2)
  | @{op1} e1, @{op2} e2 => cast_if_and (decide_rel (=) op1 op2)
     (decide_rel (=) e1 e2)
  | el1 @{op1} er1, el2 @{op2} er2 => cast_if_and3 (decide_rel (=) op1 op2)
     (decide_rel (=) el1 el2) (decide_rel (=) er1 er2)
  | (IF e1 then el1 else er1), (IF e2 then el2 else er2) =>
     cast_if_and3 (decide_rel (=) e1 e2)
       (decide_rel (=) el1 el2) (decide_rel (=) er1 er2)
  | _, _ => right _
  end%E); clear go; try abstract congruence.
Defined.

(** The sequenced "or" and "and" operation are defined in terms of the
conditional. This keeps the expression language small. *)
Definition EAnd (e1 e2 : expr) :=
  (IF e1 then (IF e2 then int 1 else int 0) else int 0)%E.
Infix "&&" := EAnd : expr_scope.
Definition EOr (e1 e2 : expr) :=
  (IF e1 then int 1 else (IF e2 then int 1 else int 0))%E.
Infix "||" := EOr : expr_scope.

(** * Induction principles *)
(** The induction principles that Coq generates for nested inductive types are
too weak. For the case of expressions, the branch of [call f @ es] does not
contain an induction hypothesis for the function arguments [es]. We therefore
define an appropriate induction principle for expressions by hand. *)
Section expr_ind.
  Context (P : expr → Prop).
  Context (Pvar : ∀ x, P (var x)).
  Context (Pval : ∀ v, P (val v)).
  Context (Passign : ∀ el er, P el → P er → P (el ::= er)).
  Context (Pcall : ∀ f es, Forall P es → P (call f @ es)).
  Context (Pload : ∀ e, P e → P (load e)).
  Context (Palloc : P alloc).
  Context (Pfree : ∀ e, P e → P (free e)).
  Context (Punop : ∀ op e, P e → P (@{op} e)).
  Context (Pbinop : ∀ op e1 e2, P e1 → P e2 → P (e1 @{op} e2)).
  Context (Pif : ∀ e el er, P e → P el → P er → P (IF e then el else er)).

  Definition expr_ind_alt : ∀ e, P e :=
    fix go e : P e :=
    match e with
    | var x => Pvar x
    | val v => Pval v
    | el ::= er => Passign _ _ (go el) (go er)
    | call f @ es => Pcall f es $ list_ind (Forall P)
       (Forall_nil _)
       (λ e _, Forall_cons _ _ _ (go e)) es
    | load e => Pload e (go e)
    | alloc => Palloc
    | free e => Pfree e (go e)
    | @{op} e => Punop op _ (go e)
    | el @{op} er => Pbinop op _ _ (go el) (go er)
    | (IF e then el else er) => Pif _ _ _ (go e) (go el) (go er)
    end%E.
End expr_ind.

(** We also define [size e] giving the number of nodes in an expression. This
measure can be used for well-founded induction on expressions. *)
Instance expr_size: Size expr :=
  fix go (e : expr) : nat :=
  let _ : Size _ := go in
  match e with
  | var _ => 0
  | val _ => 0
  | el ::= er => S (size el + size er)
  | call _ @ es => S (sum_list_with size es)
  | load e => S (size e)
  | alloc => 0
  | free e => S (size e)
  | @{_} e => S (size e)
  | el @{_} er => S (size el + size er)
  | (IF e then el else er) => S (size e + size el + size er)
  end%E.

Lemma expr_wf_ind (P : expr → Prop)
  (Pind : ∀ e, (∀ e', size e' < size e → P e') → P e) : ∀ e, P e.
Proof.
  cut (∀ n e, size e < n → P e).
  { intros help e. apply (help (S (size e))). lia. }
  induction n.
  * intros. lia.
  * intros e ?. apply Pind. intros. apply IHn. lia.
Qed.

(** * Miscellaneous Operations and properties *)
(** The operation [e↑] increases all De Bruijn indexes of variables in [e]
by one. That means, each variable [var x] in [e] becomes [var (S x)]. *)
Reserved Notation "e ↑" (at level 20, format "e ↑").
Fixpoint expr_lift (e : expr) : expr :=
  match e with
  | var x => var (S x)
  | val v => val v
  | el ::= er => el↑ ::= er↑
  | call f @ es => call f @ expr_lift <$> es
  | load e => load (e↑)
  | alloc => alloc
  | free e => free (e↑)
  | @{op} e => @{op} e↑
  | el @{op} er => el↑ @{op} er↑
  | (IF e then el else er) => IF e↑ then el↑ else er↑
  end%E
where "e ↑" := (expr_lift e) : expr_scope.

(** The predicate [is_value e] states that [e] is a value (i.e. execution of
[e] is finished), the predicate [is_redex e] states that [e] is a head redex
(i.e. a head reduction step is possible). *)
Inductive is_value : expr → Prop :=
  | is_value_val v : is_value (val v).
Inductive is_redex : expr → Prop :=
  | is_redex_var x : is_redex (var x)
  | is_redex_assign el er :
     is_value el → is_value er → is_redex (el ::= er)
  | is_redex_call f es : Forall is_value es → is_redex (call f @ es)
  | is_redex_load e : is_value e → is_redex (load e)
  | is_redex_alloc : is_redex alloc
  | is_redex_free e : is_value e → is_redex (free e)
  | is_redex_unop op e :
     is_value e → is_redex (@{op} e)
  | is_redex_binop op el er :
     is_value el → is_value er → is_redex (el @{op} er)
  | is_redex_if e el er :
     is_value e → is_redex (IF e then el else er).

Instance is_value_dec e : Decision (is_value e).
Proof.
 refine (
  match e with
  | val _ => left _
  | _ => right _
  end%E); try constructor; abstract (inversion 1).
Defined.
Instance is_redex_dec e : Decision (is_redex e).
Proof.
 refine (
  match e with
  | var _ => left _
  | val _ => right _
  | el ::= er => cast_if_and (decide (is_value el)) (decide (is_value er))
  | call _ @ es => cast_if (decide (Forall is_value es))
  | load e => cast_if (decide (is_value e))
  | alloc => left _
  | free e => cast_if (decide (is_value e))
  | @{_} e => cast_if (decide (is_value e))
  | el @{_} er => cast_if_and (decide (is_value el)) (decide (is_value er))
  | (IF e then _ else _) => cast_if (decide (is_value e))
  end%E); try (by constructor); abstract (by inversion 1).
Defined.

Lemma is_redex_value e : is_redex e → is_value e → False.
Proof. destruct 1; inversion 1. Qed.
Lemma is_redex_val v : ¬is_redex (val v).
Proof. inversion 1. Qed.

Lemma is_value_alt e : is_value e ↔ ∃ v, e = (val v)%E.
Proof.
  split.
  * inversion 1. eauto.
  * intros [??]. by subst.
Qed.
Lemma Forall_is_value_alt es : Forall is_value es ↔ ∃ vs, es = EVal <$> vs.
Proof.
  split.
  * induction 1 as [|?? [v] _ IH].
    + by eexists [].
    + destruct IH as [vs ?]. exists (v :: vs). by subst.
  * intros [vs H]. subst. rewrite Forall_fmap.
    apply Forall_true, is_value_val.
Qed.

(** * Evaluation of side-effect free expressions *)
(** We define a denotational semantics [⟦ e ⟧] for side-effect free expressions
[e] by structural recursion over [e]. Expressions with side-effects are given
no semantics here. *)
Reserved Notation "⟦ e ⟧" (format "⟦  e  ⟧").

Fixpoint expr_eval (e : expr) (ρ : stack) (m : mem) : option value :=
  match e with
  | var x =>
     b ← ρ !! x;
     Some (ptr b)%V
  | val v => Some v
  | load e =>
     v ← ⟦ e ⟧ ρ m;
     a ← is_ptr v;
     m !! a
  | @{op} e =>
     v ← ⟦ e ⟧ ρ m;
     eval_unop op v
  | el @{op} er =>
     vl ← ⟦ el ⟧ ρ m;
     vr ← ⟦ er ⟧ ρ m;
     eval_binop op vl vr
  | (IF e then el else er) =>
     v ← ⟦ e ⟧ ρ m;
     ⟦ if value_true_false_dec v then el else er ⟧ ρ m
  | _ => None
  end%E
where "⟦ e ⟧" := (expr_eval e) : C_scope.

(** * Contexts with one hole *)
(** We define singular expression contexts [ectx_item], and then full expression
(evaluation) contexts [ectx] are lists of expression contexts. These expression
contexts allow us to enforce an evaluation strategy. In particular, for the
conditional we merely allow a hole for the first branch. *)
Inductive ectx_item :=
  | CAssignL : expr → ectx_item
  | CAssignR : expr → ectx_item
  | CCall : funname → list expr → list expr → ectx_item
  | CLoad : ectx_item
  | CFree : ectx_item
  | CUnOp : unop → ectx_item
  | CBinOpL : binop → expr → ectx_item
  | CBinOpR : binop → expr → ectx_item
  | CIf : expr → expr → ectx_item.
Notation ectx := (list ectx_item).

Instance ectx_item_dec (E1 E2 : ectx_item) : Decision (E1 = E2).
Proof. solve_decision. Defined.

Bind Scope expr_scope with ectx_item.
Notation "□ ::= er" := (CAssignL er) (at level 60) : expr_scope.
Notation "el ::= □" := (CAssignR el)
  (at level 60, format "el  ::=  □") : expr_scope.
Notation "'call' f @ es1 □ es2" := (CCall f es1 es2)
  (at level 10, es1 at level 66, es2 at level 66) : expr_scope.
Notation "'load' □" := CLoad (at level 10, format "load  □") : expr_scope.
Notation "'free' □" := CFree (at level 10, format "free  □") : expr_scope.
Notation "@{ op } □" := (CUnOp op)
  (at level 21, format "@{ op } □") : expr_scope.
Notation "□ @{ op } er" := (CBinOpL op er)
  (at level 50, format "□  @{ op }  er") : expr_scope.
Notation "el @{ op } □" := (CBinOpR op el)
  (at level 50, format "el  @{ op }  □") : expr_scope.
Notation "'IF' □ 'then' el 'else' er" := (CIf el er)
  (at level 200, format "'IF'  □  'then'  el  'else'  er") : expr_scope.

(** Substitution is defined in a straightforward way. Using the type class
instances in the file [contexts], it is lifted to full expression contexts. *)
Instance ectx_item_subst: Subst ectx_item expr expr := λ E e,
  match E with
  | □ ::= er => e ::= er
  | el ::= □ => el ::= e
  | call f @ es1 □ es2 => call f @ (reverse es1 ++ e :: es2)
  | load □ => load e
  | free □ => free e
  | @{op} □ => @{op} e
  | □ @{op} er => e @{op} er
  | el @{op} □ => el @{op} e
  | (IF □ then el else er) => IF e then el else er
  end%E.
Instance: DestructSubst ectx_item_subst.

Instance: ∀ E : ectx_item, Injective (=) (=) (subst E).
Proof.
  destruct E; intros ???; simpl in *;
    simplify_list_equality; trivial.
Qed.

Lemma is_value_ectx_item (E : ectx_item) e : ¬is_value (subst E e).
Proof. destruct E; inversion 1. Qed.
Lemma is_value_ectx (E : ectx) e : is_redex e → ¬is_value (subst E e).
Proof.
  destruct E as [|E E' _] using rev_ind.
  * eauto using is_redex_value.
  * rewrite list_subst_snoc. auto using is_value_ectx_item.
Qed.

(** The induction principle [ectx_expr_ind] is used to perform simultaneous
induction on an expression [e] and context [E]. Although a similar result can
be obtained by generalizing over [E] before doing the induction on [e], this
induction principle is more useful together with automation. Automation now
does not have to instantiate the induction hypothesis with the appropriate
context. *)
Section ectx_expr_ind.
  Context (P : ectx → expr → Prop).
  Context (Pvar : ∀ E x, P E (var x)).
  Context (Pval : ∀ E v, P E (val v)).
  Context (Passign : ∀ E el er,
    P ((□ ::= er)%E :: E) el → P ((el ::= □)%E :: E) er → P E (el ::= er)).
  Context (Pcall : ∀ E f es,
    zipped_Forall (λ esl esr, P ((call f @ esl □ esr)%E :: E)) [] es →
    P E (call f @ es)).
  Context (Pload : ∀ E e, P ((load □)%E :: E) e → P E (load e)).
  Context (Palloc : ∀ E, P E alloc).
  Context (Pfree : ∀ E e, P ((free □)%E :: E) e → P E (free e)).
  Context (Punop : ∀ E op e, P ((@{op} □)%E :: E) e → P E (@{op} e)).
  Context (Pbinop : ∀ E op el er,
    P ((□ @{op} er)%E :: E) el →
    P ((el @{op} □)%E :: E) er →
    P E (el @{op} er)).
  Context (Pif : ∀ E e el er,
    P ((IF □ then el else er)%E :: E) e →
    P E (IF e then el else er)).

  Definition ectx_expr_ind : ∀ E e, P E e :=
    fix go E e : P E e :=
    match e with
    | var x => Pvar _ x
    | val v => Pval _ v
    | el ::= er => Passign _ _ _ (go _ el) (go _ er)
    | call f @ es => Pcall E f es $
       zipped_list_ind _ zipped_Forall_nil
        (λ _ _ e, @zipped_Forall_cons _ (λ _ _, P _) _ _ _ (go _ e)) [] es
    | load e => Pload _ _ (go _ e)
    | alloc => Palloc _
    | free e => Pfree _ _ (go _ e)
    | @{op} e => Punop _ op _ (go _ e)
    | el @{op} er => Pbinop _ op _ _ (go _ el) (go _ er)
    | (IF e then el else er) => Pif _ _ _ _ (go _ e)
    end%E.
End ectx_expr_ind.

Ltac ectx_expr_ind E e :=
  repeat match goal with
  | H : context [ E ] |- _ => revert H
  | H : context [ e ] |- _ => revert H
  end;
  revert E e;
  match goal with
  | |- ∀ E e, @?P E e => apply (ectx_expr_ind P)
  end.

(** * Contexts with multiple holes *)
(** We define singular expression contexts indexed by the number of holes. These
contexts are particularly useful to prove some of the Hoare rules in a more
general way. *)
Inductive ectx_full : nat → Type :=
  | DCVal : value → ectx_full 0
  | DCVar : nat → ectx_full 0
  | DCAssign : ectx_full 2
  | DCCall {n} : funname → ectx_full n
  | DCLoad : ectx_full 1
  | DCAlloc : ectx_full 0
  | DCFree : ectx_full 1
  | DCUnOp : unop → ectx_full 1
  | DCBinOp : binop → ectx_full 2
  | DCIf : expr → expr → ectx_full 1.

Instance ectx_full_subst: DepSubst ectx_full (vec expr) expr := λ _ E,
  match E with
  | DCVal v => λ _, val v
  | DCVar x => λ _, var x
  | DCAssign => λ es, es !!! 0 ::= es !!! 1
  | DCCall _ f => λ es, call f @ es
  | DCLoad => λ es, load (es !!! 0)
  | DCAlloc => λ es, alloc
  | DCFree => λ es, free (es !!! 0)
  | DCUnOp op => λ es, @{op} es !!! 0
  | DCBinOp op => λ es, es !!! 0 @{op} es !!! 1
  | DCIf el er => λ es, IF es !!! 0 then el else er
  end%E.

Lemma ectx_full_subst_inj {n} (E : ectx_full n) es1 es2 :
  depsubst E es1 = depsubst E es2 → es1 = es2.
Proof.
  destruct E; inv_all_vec_fin;
   simpl; intros; simplify_equality;
   auto using vec_to_list_inj2.
Qed.

(** Giving values [es] for the holes of the context [E], the function
[ectx_full_to_item E es i] yields a context with exactly one hole for the
[i]th value. The [i]th value in [es] is ignored. *)
Definition ectx_full_to_item {n} (E : ectx_full n)
    (es : vec expr n) (i : fin n) : ectx_item :=
  match E in ectx_full n return fin n → vec expr n → ectx_item with
  | DCVal v => fin_0_inv _
  | DCVar x => fin_0_inv _
  | DCAssign =>
     fin_S_inv _ (λ es, □ ::= es !!! 1)%E $
     fin_S_inv _ (λ es, es !!! 0 ::= □)%E $
     fin_0_inv _
  | DCCall _ f => λ i es,
     (call f @ reverse (take i es) □ drop (FS i) es)%E
  | DCLoad =>
     fin_S_inv _ (λ es, load □)%E $
     fin_0_inv _
  | DCAlloc => fin_0_inv _
  | DCFree =>
     fin_S_inv _ (λ es, free □)%E $
     fin_0_inv _
  | DCUnOp op =>
     fin_S_inv _ (λ es, @{op} □)%E $
     fin_0_inv _
  | DCBinOp op =>
     fin_S_inv _ (λ es, □ @{op} es !!! 1)%E $
     fin_S_inv _ (λ es, es !!! 0 @{op} □)%E $
     fin_0_inv _
  | DCIf el er =>
     fin_S_inv _ (λ es, IF □ then el else er)%E $
     fin_0_inv _
  end i es.

Lemma ectx_full_to_item_insert {n} (E : ectx_full n) es i e :
  ectx_full_to_item E (vinsert i e es) i = ectx_full_to_item E es i.
Proof.
  destruct E; inv_all_vec_fin; simpl; try reflexivity.
  rewrite !vec_to_list_insert,
   take_insert, drop_insert; auto with arith.
Qed.

Lemma ectx_full_to_item_correct {n} (E : ectx_full n) es i :
  depsubst E es = subst (ectx_full_to_item E es i) (es !!! i).
Proof.
  destruct E; inv_all_vec_fin; simpl; try reflexivity.
  by rewrite reverse_involutive, <-vec_to_list_take_drop_lookup.
Qed.

Lemma ectx_full_to_item_correct_alt {n} (E : ectx_full n) es i e :
  depsubst E (vinsert i e es) = subst (ectx_full_to_item E es i) e.
Proof.
  rewrite (ectx_full_to_item_correct _ _ i).
  by rewrite vlookup_insert, ectx_full_to_item_insert.
Qed.

Lemma ectx_full_item_subst {n} (E : ectx_full n) (es : vec expr n)
    (E' : ectx_item) (e : expr) :
  depsubst E es = subst E' e →
    ∃ i, e = es !!! i ∧ E' = ectx_full_to_item E es i.
Proof.
  intros H. destruct E, E'; simpl; simplify_equality; eauto.
  * edestruct (vec_to_list_lookup_middle es) as [i [H1 [? H2]]]; eauto.
    exists i. split; f_equal; trivial.
    by rewrite <-H1, reverse_involutive.
Qed.

Lemma Forall_is_value_alt_vec {n} (es : vec expr n) :
  Forall is_value es ↔ ∃ vs, es = vmap EVal vs.
Proof.
  rewrite Forall_is_value_alt. split.
  * intros [vs Hvs].
    rewrite <-(vec_to_list_of_list vs) in Hvs.
    rewrite <-vec_to_list_map in Hvs.
    pose proof (vec_to_list_inj1 _ _ Hvs); subst.
    apply vec_to_list_inj2 in Hvs; subst.
    by exists (list_to_vec vs).
  * intros [vs Hvs]. exists vs.
    by rewrite Hvs, vec_to_list_map.
Qed.

Lemma expr_vec_values {n} (es : vec expr n) :
  (∃ vs, es = vmap EVal vs) ∨ (∃ i, ¬is_value (es !!! i)).
Proof.
  destruct (Forall_Exists_dec is_value es) as [H | H].
  * left. by apply Forall_is_value_alt_vec.
  * right. by apply Exists_vlookup in H.
Qed.

Lemma is_redex_ectx_full {n} (E : ectx_full n) (es : vec expr n) :
  is_redex (depsubst E es) → Forall is_value es.
Proof.
  destruct E; inversion_clear 1; inv_all_vec_fin;
    repeat constructor; auto.
Qed.

(** * Theorems *)
(** Evaluation of expressions is preserved under extensions of the memory. *)
Lemma expr_eval_weaken_mem ρ m1 m2 e v :
  ⟦ e ⟧ ρ m1 = Some v →
  m1 ⊆ m2 →
  ⟦ e ⟧ ρ m2 = Some v.
Proof.
  revert v. induction e; intros; simplify_option_equality; auto.
  destruct (value_true_false_dec _); auto.
Qed.

Lemma expr_eval_weaken_inv ρ m1 m2 e v1 v2 :
  ⟦ e ⟧ ρ m1 = Some v1 →
  m1 ⊆ m2 →
  ⟦ e ⟧ ρ m2 = Some v2 →
  v1 = v2.
Proof.
  intros ? H1 H2.
  erewrite (expr_eval_weaken_mem _ m1 m2) in H2 by eauto.
  congruence.
Qed.

Lemma Forall_expr_eval_weaken_inv es ρ m1 m2 vs1 vs2 :
  Forall2 (λ e v, ⟦ e ⟧ ρ m1 = Some v) es vs1 →
  m1 ⊆ m2 →
  Forall2 (λ e v, ⟦ e ⟧ ρ m2 = Some v) es vs2 →
  vs1 = vs2.
Proof.
  intros ? H1 H2.
  apply (Forall2_unique (λ e v, ⟦ e ⟧ ρ m2 = Some v) es).
  * apply Forall2_impl with (λ e v, ⟦ e ⟧ ρ m1 = Some v);
      eauto using expr_eval_weaken_mem.
  * done.
  * congruence.
Qed.

Tactic Notation "simplify_expr_equality" "by" tactic3(tac) := repeat
  match goal with
  | _ => progress simplify_mem_equality by tac
  | _ => progress simplify_option_equality by tac
  | Ht : value_true ?v, Hf : value_false ?v |- _ =>
    destruct (value_true_false v Ht Hf)
  | H : is_ptr ?v = Some _ |- _ =>
    apply is_ptr_Some in H
  | H : context [ value_true_false_dec ?v ] |- _ =>
    destruct (value_true_false_dec v)
  | |- context [ value_true_false_dec ?v ] =>
    destruct (value_true_false_dec v)
  | H1 : ⟦ ?e ⟧ ?ρ ?m1 = Some ?v1, H2 : ⟦ ?e ⟧ ?ρ ?m2 = Some ?v2 |- _ =>
    let H3 := fresh in
    feed pose proof (expr_eval_weaken_inv e ρ m1 m2 v1 v2) as H3;
      [done | by tac | done | ];
    clear H2; symmetry in H3
  end.
Tactic Notation "simplify_expr_equality" :=
  simplify_expr_equality by eauto.

(** Lifting DeBruijn indexes distributes over expression evaluation. *)
Lemma expr_eval_lift ρ e m :
  ⟦ e↑ ⟧ ρ m = ⟦ e ⟧ (tail ρ) m.
Proof.
  induction e; intros; simpl; repeat
    match goal with
    | H : ⟦ _↑ ⟧ _ _ = _ |- _ => rewrite H
    | |- _ ← ?o; ⟦ if _ then _ else _ ⟧ _ _ = _ =>
      destruct o; simpl; try destruct (value_true_false_dec _)
    end; auto.
  by rewrite <-lookup_tail.
Qed.

(** Evaluation of expressions is preserved under extensions of the stack. *)
Lemma expr_eval_weaken_stack ρ ρ' m e v :
  ⟦ e ⟧ ρ m = Some v → ⟦ e ⟧ (ρ ++ ρ') m = Some v.
Proof.
  revert v. induction e; intros; simplify_expr_equality; auto.
  rewrite lookup_app_l.
  * by simplify_expr_equality.
  * eauto using lookup_lt_length_alt.
Qed.

(** If an expression has a denotation, then each subexpression has a
denotation as well. *)
Lemma expr_eval_subst_inv (E : ectx) e ρ m v :
  ⟦ subst E e ⟧ ρ m = Some v →
  ∃ v', ⟦ e ⟧ ρ m = Some v' ∧ ⟦ subst E (val v')%E ⟧ ρ m = Some v.
Proof.
  revert v. induction E as [|E' E IH] using rev_ind;
    simpl; intros v; [by eauto |].
  setoid_rewrite list_subst_snoc.
  intros; destruct E'; simplify_option_equality;
    naive_solver (by eauto || by simplify_option_equality).
Qed.

Lemma subst_preserves_expr_eval (E : ectx) e1 e2 ρ m :
  ⟦ e1 ⟧ ρ m = ⟦ e2 ⟧ ρ m →
  ⟦ subst E e1 ⟧ ρ m = ⟦ subst E e2 ⟧ ρ m.
Proof.
  intros. induction E as [|E' ? IH] using rev_ind; [done |].
  destruct E'; rewrite ?list_subst_snoc; simpl; rewrite ?IH; auto.
Qed.

(** The function [expr_redexes e] computes the set of redexes contained in an
expression [e]. Here, redexes are pairs [(E', e')] where [E'] is an expression
evaluation context, and [e'] an expression with [is_redex e']. *)
Section expr_split.
  Context C `{Collection (ectx * expr) C}.

  Definition expr_redexes_aux : ectx → expr → C :=
    fix go E e {struct e} :=
    if decide (is_redex e) then {[ (E, e) ]} else
    match e with
    | val v => ∅
    | var x => ∅ (* impossible *)
    | el ::= er => go (□ ::= er :: E) el ∪ go (el ::= □ :: E) er
    | call f @ es =>
       ⋃ (zipped_map (λ esl esr, go ((call f @ esl □ esr) :: E)) [] es)
    | load e => go (load □ :: E) e
    | alloc => ∅ (* impossible *)
    | free e => go (free □ :: E) e
    | @{op} e => go (@{op} □ :: E) e
    | e1 @{op} e2 => go (□ @{op} e2 :: E) e1 ∪ go (e1 @{op} □ :: E) e2
    | (IF e then el else er) => go ((IF □ then el else er) :: E) e
    end%E.
  Definition expr_redexes : expr → C := expr_redexes_aux [].

  Lemma expr_redexes_aux_is_redex E e E' e' :
    (E', e') ∈ expr_redexes_aux E e →
    is_redex e'.
  Proof.
    assert (∀ (f : list expr → list expr → expr → C) es,
      (E', e') ∈ ⋃ zipped_map f [] es →
      zipped_Forall (λ esl esr e, (E', e') ∈ f esl esr e → is_redex e') [] es →
      is_redex e').
    { intros f es Hes Hforall.
      rewrite elem_of_union_list in Hes.
      destruct Hes as [rs [Hes ?]].
      rewrite elem_of_zipped_map in Hes.
      destruct Hes as [? [? [? [??]]]]; subst.
      apply zipped_Forall_app in Hforall. inversion Hforall; subst. auto. }
    ectx_expr_ind E e;
     simpl; intros; repeat case_decide;
     try solve_elem_of (eauto; try constructor).
  Qed.
  Lemma expr_redexes_is_redex e E' e' :
    (E', e') ∈ expr_redexes e →
    is_redex e'.
  Proof. apply expr_redexes_aux_is_redex. Qed.

  Lemma expr_redexes_aux_correct E e E' e' :
    (E', e') ∈ expr_redexes_aux E e →
    subst E e = subst E' e'.
  Proof.
    assert (∀ g (f : list expr → list expr → expr → C) (E : ectx) es,
      (E', e') ∈ ⋃ zipped_map f [] es →
      zipped_Forall (λ esl esr e, (E', e') ∈ f esl esr e →
        subst E (g (reverse esl ++ [e] ++ esr)) = subst E' e') [] es →
      subst E (g es) = subst E' e').
    { intros ? g f es Hes Hforall.
      rewrite elem_of_union_list in Hes.
      destruct Hes as [rs [Hes ?]].
      rewrite elem_of_zipped_map in Hes.
      destruct Hes as [esl [? [? [??]]]]; subst.
      apply zipped_Forall_app in Hforall. inversion Hforall; subst.
      rewrite <-(reverse_involutive esl), <-(app_nil_r (reverse esl)).
      auto. }
    ectx_expr_ind E e;
     simpl; intros; repeat case_decide;
     solve_elem_of eauto.
  Qed.
  Lemma expr_redexes_correct e E' e' :
    (E', e') ∈ expr_redexes e →
    e = subst E' e'.
  Proof. apply expr_redexes_aux_correct. Qed.

  Lemma expr_redexes_aux_is_value E e :
    expr_redexes_aux E e ≡ ∅ →
    is_value e.
  Proof.
    assert (∀ (f : list expr → list expr → expr → C) es1 es2,
      ⋃ zipped_map f es1 es2 ≡ ∅ →
      zipped_Forall (λ esl esr e, f esl esr e ≡ ∅ → is_value e) es1 es2 →
      Forall is_value es2).
    { induction 2; simpl in *; decompose_empty; intuition. }
    ectx_expr_ind E e;
      simpl; intros; repeat case_decide; decompose_empty;
      try match goal with
      | |- is_value _ => constructor
      | H : ¬is_redex _ |- _ => destruct H; constructor
      end; eauto.
  Qed.
  Lemma expr_redexes_is_value e :
    expr_redexes e ≡ ∅ →
    is_value e.
  Proof. apply expr_redexes_aux_is_value. Qed.
  (* Todo: completeness *)
End expr_split.

Lemma is_value_or_redex e :
  is_value e ∨ ∃ (E' : ectx) e', is_redex e' ∧ e = subst E' e'.
Proof.
  destruct (elem_of_or_empty (expr_redexes (listset (ectx * expr)) e))
    as [[[E' e'] ?]|?].
  * right. exists E' e'. split.
    + by apply (expr_redexes_is_redex (listset _)) with e E'. 
    + by apply (expr_redexes_correct (listset _)).
  * left. by apply (expr_redexes_is_value (listset _)).
Qed.
Lemma is_value_is_redex e :
  ¬is_value e → ∃ (E' : ectx) e', is_redex e' ∧ e = subst E' e'.
Proof. intros. by destruct (is_value_or_redex e). Qed.
