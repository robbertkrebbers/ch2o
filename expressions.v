(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file defines expressions and some associated theory. Most importantly,
to define the operational semantics in the file [smallstep], we define
corresponding evaluation contexts. Notations for expressions are declared in the
scope [expr_scope]. *)
Require Import nmap mapset natmap.
Require Export values_old contexts.

(** * Function names *)
(** We use the type [N] of binary natural numbers for function names, and the
implementation [Nmap] for efficient finite maps over function names. *)
Definition funname := N.
Definition funmap := Nmap.
Notation funset := (mapset funmap).

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
  @map_to_list _ _ (funmap A) _.
Instance funmap_merge : Merge funmap := @merge Nmap _.
Instance funmap_fmap: FMap funmap := λ A B f, @fmap Nmap _ _ f _.
Instance: FinMap funname funmap := _.

Instance funmap_dom {A} : Dom (funmap A) funset := mapset_dom.
Instance: FinMapDom funname funmap funset := mapset_dom_spec.

Typeclasses Opaque funname funmap.

Class Funs A := funs : A → funset.
Arguments funs {_ _} !_ / : simpl nomatch.

(** * Stacks *)
(** Stacks are lists of memory indexes rather than lists of values. This allows
us to treat pointers to both automatically and dynamically allocated memory in
a uniform way. Evaluation of a variable will therefore consist of a looking up
its address in the stack and returning a pointer to that address. *)

Notation stack := (list index) (only parsing).
Class Vars A := vars: A → natset.
Arguments vars {_ _} !_ / : simpl nomatch.

(** * Syntax *)
(** The variables used in expressions are De Bruijn indexes, i.e. the variable
[var i] refers to the [i]th value on the stack. De Bruijn indexes avoid us
having to deal with shadowing due to block scope variables. Especially in
the axiomatic semantics this is useful, as we do not want to lose information
because a local variable may shadow an already existing one. *)

(** Values are annotated with a set of locked locations. Initially, all values
in a program should be annotated with the empty set. Whenever a write occurs
during the execution of the program, the written location is locked in memory,
and added to the set of locked locations in the subexpression where that write
occurred. On the execution of a connective that contains a sequence point, the
annotated locations in the subexpression where the sequence point occurred are
unlocked in memory and then discarded. Connectives without a sequence point
just take the union of the locked locations of their children. *)

(** This way of dealing with sequence points is more restrictive than the
treatment by (Norrish, PhD thesis) and (Ellison/Rosu, 2012), as whenever a
sequence point occurs, we only unlock the locations that have been locked by
evaluating the sub-expression corresponding to that particular sequence point,
instead of unlocking all locations. *)
Inductive assign :=
  | Assign (**i ordinary assignment *)
  | PreOp : binop → assign (**i assignment operators and prefix increment,
     decrement, etc. *)
  | PostOp : binop → assign (**i postfix increment, decrement, etc. *).

Inductive expr :=
  | EVar : nat → expr
  | EVal : indexset → val → expr
  | EAssign : assign → expr → expr → expr
  | ECall : funname → list expr → expr
  | ELoad : expr → expr
  | EAlloc : expr
  | EFree : expr → expr
  | EUnOp : unop → expr → expr
  | EBinOp : binop → expr → expr → expr
  | EIf : expr → expr → expr → expr
  | EComma : expr → expr → expr
  | ECast : int_type → expr → expr.

(** We use the scope [expr_scope] to declare notations for expressions. We
overload some notations already in [value_scope], and define both general and
specific notations for operations, allowing us for example to to write
[intc 10 + intc 20] instead of the much longer
[valc (intc 10) @op{PlusOp} valc (intc 20)]. *)
Delimit Scope expr_scope with E.
Bind Scope expr_scope with expr.

Arguments EVar _.
Arguments EVal _ _%val_scope.
Arguments EAssign _ _%expr_scope _%expr_scope.
Arguments ECall _ _%expr_scope.
Arguments ELoad _%expr_scope.
Arguments EAlloc.
Arguments EFree _%expr_scope.
Arguments EUnOp _ _%expr_scope.
Arguments EBinOp _ _%expr_scope _%expr_scope.
Arguments EIf _%expr_scope _%expr_scope _%expr_scope.
Arguments EComma _%expr_scope _%expr_scope.
Arguments ECast _ _%expr_scope.

Notation "'var' x" := (EVar x) (at level 10) : expr_scope.
Notation "'valc' @{ Ω } v" := (EVal Ω v)
  (at level 10, format "'valc' @{ Ω }  v") : expr_scope.
Notation "'valc' v" := (EVal ∅ v) (at level 10) : expr_scope.
Notation "'indetc' @{ Ω }" := (EVal Ω indetc)
  (at level 10, format "'indetc' @{ Ω }") : expr_scope.
Notation "'indetc'" := (EVal ∅ indetc) : expr_scope.
Notation "'intc' @{ Ω } x" := (EVal Ω (intc x))
  (at level 10, format "'intc' @{ Ω }  x") : expr_scope.
Notation "'intc' x" := (EVal ∅ (intc x%Z)) : expr_scope.
Notation "'ptrc' @{ Ω } b" := (EVal Ω (ptrc b))
  (at level 10, format "'ptrc' @{ Ω }  b") : expr_scope.
Notation "'ptrc' b" := (EVal ∅ (ptrc b)) : expr_scope.
Notation "'nullc' @{ Ω }" := (EVal Ω nullc)
  (at level 10, format "'nullc' @{ Ω }") : expr_scope.
Notation "'nullc'" := (EVal ∅ nullc) : expr_scope.
Notation "el ::=@{ ass } er" := (EAssign ass el er)
  (at level 60, format "el  ::=@{ ass }  er", right associativity) : expr_scope.
Infix "::=" := (EAssign Assign) (at level 60, right associativity) : expr_scope.
Infix "::⊙{ op }=" := (EAssign (PreOp op))
  (at level 60, right associativity) : expr_scope.
Infix "::=⊙{ op }" := (EAssign (PostOp op))
  (at level 60, right associativity) : expr_scope.
(* The infixes [++] and [::] are at level 60, [<$>] at 65. *)
Notation "'call' f @ es" := (ECall f es)
  (at level 10, es at level 66) : expr_scope.
Notation "'load' e" := (ELoad e) (at level 10) : expr_scope.
Notation "'alloc'" := EAlloc : expr_scope.
Notation "'free' e" := (EFree e) (at level 10) : expr_scope.
Notation "⊙{ op } e" := (EUnOp op e)
  (at level 21, format "⊙{ op }  e") : expr_scope.
Notation "el ⊙{ op } er" := (EBinOp op el er)
  (at level 50, format "el  ⊙{ op }  er") : expr_scope.
Notation "'IF' e 'then' el 'else' er" := (EIf e el er) : expr_scope.
Notation "'cast' @{ τ } e" := (ECast τ e)
  (at level 10, format "'cast' @{ τ }  e") : expr_scope.
Notation "el ,, er" := (EComma el er)
  (at level 55, right associativity, format "el  ,,  er") : expr_scope.

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
Instance: Injective (=) (=) ELoad.
Proof. by injection 1. Qed.
Instance: Injective (=) (=) EFree.
Proof. by injection 1. Qed.

Instance assign_eq_dec: ∀ a1 a2 : assign, Decision (a1 = a2).
Proof. solve_decision. Defined.
Instance expr_eq_dec: ∀ e1 e2 : expr, Decision (e1 = e2).
Proof.
  refine (fix go e1 e2 : Decision (e1 = e2) :=
  match e1, e2 with
  | var i1, var i2 => cast_if (decide_rel (=) i1 i2)
  | valc@{Ω1} v1, valc@{Ω2} v2 =>
     cast_if_and (decide_rel (=) Ω1 Ω2) (decide_rel (=) v1 v2)
  | el1 ::=@{ass1} er1, el2 ::=@{ass2} er2 =>
     cast_if_and3 (decide_rel (=) ass1 ass2) (decide_rel (=) el1 el2)
       (decide_rel (=) er1 er2)
  | call f1 @ es1, call f2 @ es2 => cast_if_and (decide_rel (=) f1 f2)
     (decide_rel (=) es1 es2)
  | load e1, load e2 => cast_if (decide_rel (=) e1 e2)
  | alloc, alloc => left _
  | free e1, free e2 => cast_if (decide_rel (=) e1 e2)
  | ⊙{op1} e1, ⊙{op2} e2 => cast_if_and (decide_rel (=) op1 op2)
     (decide_rel (=) e1 e2)
  | el1 ⊙{op1} er1, el2 ⊙{op2} er2 => cast_if_and3 (decide_rel (=) op1 op2)
     (decide_rel (=) el1 el2) (decide_rel (=) er1 er2)
  | (IF e1 then el1 else er1), (IF e2 then el2 else er2) =>
     cast_if_and3 (decide_rel (=) e1 e2)
       (decide_rel (=) el1 el2) (decide_rel (=) er1 er2)
  | el1 ,, er1, el2 ,, er2 =>
     cast_if_and (decide_rel (=) el1 el2) (decide_rel (=) er1 er2)
  | cast@{τ1} e1, cast@{τ2} e2 =>
     cast_if_and (decide_rel (=) τ1 τ2) (decide_rel (=) e1 e2)
  | _, _ => right _
  end%E); clear go; abstract congruence.
Defined.

(** The sequenced [||] and [&&] operators are defined in terms of the
conditional. This keeps the expression language small. *)
Definition EAnd (e1 e2 : expr) := (IF e1 then e2 else intc int_false)%E.
Infix "&&" := EAnd : expr_scope.
Definition EOr (e1 e2 : expr) := (IF e1 then intc int_true else e2)%E.
Infix "||" := EOr : expr_scope.

(** * Induction principles *)
(** The induction principles that Coq generates for nested inductive types are
too weak. For the case of expressions, the branch of [call f @ es] does not
contain an induction hypothesis for the function arguments [es]. We therefore
define an appropriate induction principle for expressions by hand. *)
Section expr_ind.
  Context (P : expr → Prop).
  Context (Pvar : ∀ x, P (var x)).
  Context (Pval : ∀ Ω v, P (valc@{Ω} v)).
  Context (Passign : ∀ a el er, P el → P er → P (el ::=@{ a } er)).
  Context (Pcall : ∀ f es, Forall P es → P (call f @ es)).
  Context (Pload : ∀ e, P e → P (load e)).
  Context (Palloc : P alloc).
  Context (Pfree : ∀ e, P e → P (free e)).
  Context (Punop : ∀ op e, P e → P (⊙{op} e)).
  Context (Pbinop : ∀ op e1 e2, P e1 → P e2 → P (e1 ⊙{op} e2)).
  Context (Pif : ∀ e el er, P e → P el → P er → P (IF e then el else er)).
  Context (Pcomma : ∀ el er, P el → P er → P (el ,, er)).
  Context (Pcast : ∀ τ e, P e → P (cast@{τ} e)).

  Definition expr_ind_alt : ∀ e, P e :=
    fix go e : P e :=
    match e with
    | var x => Pvar x
    | valc@{Ω} v => Pval Ω v
    | el ::=@{_} er => Passign _ _ _ (go el) (go er)
    | call f @ es => Pcall f es $ list_ind (Forall P)
       (Forall_nil_2 _) (λ e _, Forall_cons_2 _ _ _ (go e)) es
    | load e => Pload e (go e)
    | alloc => Palloc
    | free e => Pfree e (go e)
    | ⊙{op} e => Punop op _ (go e)
    | el ⊙{op} er => Pbinop op _ _ (go el) (go er)
    | (IF e then el else er) => Pif _ _ _ (go e) (go el) (go er)
    | el ,, er => Pcomma _ _ (go el) (go er)
    | cast@{τ} e => Pcast _ _ (go e)
    end%E.
End expr_ind.

(** We also define [size e] giving the number of nodes in an expression. This
measure can be used for well-founded induction on expressions. *)
Instance expr_size: Size expr :=
  fix go e : nat :=
  let _ : Size _ := go in
  match e with
  | var _ => 0
  | valc@{_} _ => 0
  | el ::=@{_} er => S (size el + size er)
  | call _ @ es => S (sum_list_with size es)
  | load e => S (size e)
  | alloc => 0
  | free e => S (size e)
  | ⊙{_} e => S (size e)
  | el ⊙{_} er => S (size el + size er)
  | (IF e then el else er) => S (size e + size el + size er)
  | el ,, er => S (size el + size er)
  | cast@{_} e => size e
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
(** An expression is [load_free] if it does not contain any occurrences of the
[load] operator. *)
Inductive load_free: expr → Prop :=
  | EVar_load_free x : load_free (var x)
  | EVal_load_free Ω v : load_free (valc@{Ω} v)
  | EAssign_load_free ass el er :
     load_free el → load_free er → load_free (el ::=@{ass} er)
  | ECall_load_free f es : Forall load_free es → load_free (call f @ es)
  | EAlloc_load_free : load_free alloc
  | EFree_load_free e : load_free e → load_free (free e)
  | EUnOp_load_free op e : load_free e → load_free (⊙{op} e)
  | EBinOp_load_free op el er :
     load_free el → load_free er → load_free (el ⊙{op} er)
  | EIf_load_free e el er :
     load_free e → load_free el → load_free er →
     load_free (IF e then el else er)
  | EComma_load_free el er :
     load_free el → load_free er →  load_free (el ,, er)
  | ECast_load_free τ e : load_free e → load_free (cast@{τ} e).

Section load_free_ind.
  Context (P : expr → Prop).
  Context (Pvar : ∀ x, P (var x)).
  Context (Pval : ∀ Ω v, P (valc@{Ω} v)).
  Context (Passign : ∀ ass el er,
    load_free el → P el → load_free er → P er → P (el ::=@{ass} er)).
  Context (Pcall : ∀ f es, Forall load_free es → Forall P es → P (call f @ es)).
  Context (Palloc : P alloc).
  Context (Pfree : ∀ e, load_free e → P e → P (free e)).
  Context (Punop : ∀ op e, load_free e → P e → P (⊙{op} e)).
  Context (Pbinop : ∀ op e1 e2,
    load_free e1 → P e1 → load_free e2 → P e2 → P (e1 ⊙{op} e2)).
  Context (Pif : ∀ e el er,
    load_free e → P e → load_free el → P el → load_free er → P er →
    P (IF e then el else er)).
  Context (Pcomma : ∀ el er,
    load_free el → P el → load_free er → P er → P (el ,, er)).
  Context (Pcast : ∀ τ e, load_free e → P e → P (cast@{τ} e)).

  Definition load_free_ind_alt: ∀ e, load_free e → P e :=
    fix go e H :=
    match H in load_free e return P e with
    | EVar_load_free x => Pvar _
    | EVal_load_free Ω v => Pval _ _
    | EAssign_load_free _ _ _ Hl Hr => Passign _ _ _ Hl (go _ Hl) Hr (go _ Hr)
    | ECall_load_free _ _ H => Pcall _ _ H (Forall_impl _ _ _ H go)
    | EAlloc_load_free => Palloc
    | EFree_load_free _ H => Pfree _ H (go _ H)
    | EUnOp_load_free _ _ H => Punop _ _ H (go _ H)
    | EBinOp_load_free _ _ _ H1 H2 =>
       Pbinop _ _ _ H1 (go _ H1) H2 (go _ H2)
    | EIf_load_free _ _ _ H Hl Hr =>
       Pif _ _ _ H (go _ H) Hl (go _ Hl) Hr (go _ Hr)
    | EComma_load_free _ _ Hl Hr =>
       Pcomma _ _ Hl (go _ Hl) Hr (go _ Hr)
    | ECast_load_free _ _ H => Pcast _ _ H (go _ H)
    end.
End load_free_ind.

Instance load_free_dec : ∀ e : expr, Decision (load_free e).
Proof.
 refine (
  fix go e :=
  match e return Decision (load_free e) with
  | var x => left _
  | valc@{_} _ => left _
  | el ::=@{_} er => cast_if_and (go el) (go er)
  | call f @ es => cast_if (decide (Forall load_free es))
  | load e => right _
  | alloc => left _
  | free e => cast_if (go e)
  | ⊙{op} e => cast_if (go e)
  | el ⊙{op} er => cast_if_and (go el) (go er)
  | (IF e then el else er) => cast_if_and3 (go e) (go el) (go er)
  | EComma el er => cast_if_and  (go el) (go er)
  | cast@{_} e => cast_if (go e)
  end%E); first [by constructor | by inversion 1].
Defined.

Instance expr_vars: Vars expr :=
  fix go e :=
  let _ : Vars _ := @go in
  match e with
  | var n => {[ n ]}
  | valc@{_} _ => ∅
  | el ::=@{_} er => vars el ∪ vars er
  | call _ @ es => ⋃ (vars <$> es)
  | alloc => ∅
  | load e
  | free e
  | ⊙{_} e => vars e
  | el ⊙{_} er => vars el ∪ vars er
  | (IF e then el else er) => vars e ∪ vars el ∪ vars er
  | el ,, er => vars el ∪ vars er
  | cast@{_} e => vars e
  end%E.

Instance expr_funs: Funs expr :=
  fix go e :=
  let _ : Funs _ := @go in
  match e with
  | var n => ∅
  | valc@{_} _ => ∅
  | el ::=@{_} er => funs el ∪ funs er
  | call f @ es => {[ f ]} ∪ ⋃ (funs <$> es)
  | alloc => ∅
  | load e
  | free e
  | ⊙{_} e => funs e
  | el ⊙{_} er => funs el ∪ funs er
  | (IF e then el else er) => funs e ∪ funs el ∪ funs er
  | el ,, er => funs el ∪ funs er
  | cast@{_} e => funs e
  end%E.

Hint Extern 1 (load_free _) => assumption : typeclass_instances.
Hint Extern 100 (load_free ?e) =>
  apply (bool_decide_unpack _); vm_compute; exact I : typeclass_instances.
Hint Extern 1 (vars _ = ∅) => assumption : typeclass_instances.
Hint Extern 100 (vars _ = ∅) =>
  apply (bool_decide_unpack _); vm_compute; exact I : typeclass_instances.

(** The operation [expr_locks e] yields the union of the sets of locked
locations in the leafs of [e]. *)
Instance expr_locks: Locks expr :=
  fix go e : indexset :=
  let _ : Locks _ := @go in
  match e with
  | var n => ∅
  | valc@{Ω} _ => Ω
  | el ::=@{_} er => locks el ∪ locks er
  | call _ @ es => ⋃ (locks <$> es)
  | alloc => ∅
  | load e
  | free e
  | ⊙{_} e => locks e
  | el ⊙{_} er => locks el ∪ locks er
  | (IF e then el else er) => locks e ∪ locks el ∪ locks er
  | el ,, er => locks el ∪ locks er
  | cast@{_} e => locks e
  end%E.

(** An expression is pure (or side-effect free) if it does not modify the
memory. Although these expressions may have sequence points (namely at the
conditional and at calls to pure functions), these sequence points are not
observable, as pure expressions do not allow any locations to get locked in
the first place. The predicate is parametrized by a set [fs] of names of pure
functions. The denotational semantics for pure expressions in the file
[expression_eval] uses a map from function names to denotations to deal with
pure function calls. *)
Inductive is_pure (fs : funset) : expr → Prop :=
  | EVar_pure x : is_pure fs (var x)
  | EVal_pure v : is_pure fs (valc v)
  | ECall_pure f es : f ∈ fs → Forall (is_pure fs) es → is_pure fs (call f @ es)
  | ELoad_pure e : is_pure fs e → is_pure fs (load e)
  | EUnOp_pure op e : is_pure fs e → is_pure fs (⊙{op} e)
  | EBinOp_pure op el er :
     is_pure fs el → is_pure fs er → is_pure fs (el ⊙{op} er)
  | EIf_pure e el er :
     is_pure fs e → is_pure fs el → is_pure fs er →
     is_pure fs (IF e then el else er)
  | EComma_pure el er :
     is_pure fs el → is_pure fs er → is_pure fs (el ,, er)
  | ECast_pure τ e : is_pure fs e → is_pure fs (cast@{τ} e).

Section is_pure_ind.
  Context (fs : funset) (P : expr → Prop).
  Context (Pvar : ∀ x, P (var x)).
  Context (Pval : ∀ v, P (valc v)).
  Context (Pcall : ∀ f es,
    f ∈ fs → Forall (is_pure fs) es → Forall P es → P (call f @ es)).
  Context (Pload : ∀ e, is_pure fs e → P e → P (load e)).
  Context (Punop : ∀ op e, is_pure fs e → P e → P (⊙{op} e)).
  Context (Pbinop : ∀ op e1 e2,
    is_pure fs e1 → P e1 → is_pure fs e2 → P e2 → P (e1 ⊙{op} e2)).
  Context (Pif : ∀ e el er,
    is_pure fs e → P e → is_pure fs el → P el → is_pure fs er → P er →
    P (IF e then el else er)).
  Context (Pcomma : ∀ el er,
    is_pure fs el → P el → is_pure fs er → P er → P (el ,, er)).
  Context (Pcast : ∀ τ e, is_pure fs e → P e → P (cast@{τ} e)).

  Definition is_pure_ind_alt: ∀ e, is_pure fs e → P e :=
    fix go e H  :=
    match H in is_pure _ e return P e with
    | EVar_pure x => Pvar _
    | EVal_pure v => Pval _
    | ECall_pure _ _ Hf H => Pcall _ _ Hf H (Forall_impl _ _ _ H go)
    | ELoad_pure _ H => Pload _ H (go _ H)
    | EUnOp_pure _ _ H => Punop _ _ H (go _ H)
    | EBinOp_pure _ _ _ H1 H2 => Pbinop _ _ _ H1 (go _ H1) H2 (go _ H2)
    | EIf_pure _ _ _ H Hl Hr => Pif _ _ _ H (go _ H) Hl (go _ Hl) Hr (go _ Hr)
    | EComma_pure _ _ Hl Hr => Pcomma _ _ Hl (go _ Hl) Hr (go _ Hr)
    | ECast_pure _ _ H => Pcast _ _ H (go _ H)
    end.
End is_pure_ind.

Instance is_pure_dec fs : ∀ e : expr, Decision (is_pure fs e).
Proof.
 refine (
  fix go e :=
  match e return Decision (is_pure fs e) with
  | var x => left _
  | valc@{Ω} _ => cast_if (decide (Ω = ∅))
  | call f @ es =>
     cast_if_and (decide (f ∈ fs)) (decide (Forall (is_pure fs) es))
  | load e => cast_if (go e)
  | ⊙{op} e => cast_if (go e)
  | el ⊙{op} er => cast_if_and (go el) (go er)
  | (IF e then el else er) => cast_if_and3 (go e) (go el) (go er)
  | el ,, er => cast_if_and (go el) (go er)
  | cast@{_} e => cast_if (go e)
  | _ => right _
  end%E); first [by subst; constructor | by inversion 1; subst].
Defined.
Lemma is_pure_locks fs (e : expr) : is_pure fs e → locks e = ∅.
Proof.
  assert (∀ (es : list expr) b,
    Forall (λ e, b ∉ locks e) es → b ∉ ⋃ (locks <$> es)).
  { induction 1; esolve_elem_of. }
  intros He. apply elem_of_equiv_empty_L. intros b.
  induction He using is_pure_ind_alt; esolve_elem_of.
Qed.

(** The operation [e↑] increases all De Bruijn indexes of variables in [e]
by one. That means, each variable [var x] in [e] becomes [var (S x)]. *)
Reserved Notation "e ↑" (at level 20, format "e ↑").
Fixpoint expr_lift (e : expr) : expr :=
  match e with
  | var x => var (S x)
  | valc@{Ω} v => valc@{Ω} v
  | el ::=@{ass} er => el↑ ::=@{ass} er↑
  | call f @ es => call f @ expr_lift <$> es
  | load e => load (e↑)
  | alloc => alloc
  | free e => free (e↑)
  | ⊙{op} e => ⊙{op} e↑
  | el ⊙{op} er => el↑ ⊙{op} er↑
  | (IF e then el else er) => IF e↑ then el↑ else er↑
  | el ,, er => el↑ ,, er↑
  | cast@{τ} e => cast@{τ} (e↑)
  end%E
where "e ↑" := (expr_lift e) : expr_scope.

(** The predicate [is_value e] states that [e] is a value (i.e. execution of
[e] is finished), the predicate [is_redex e] states that [e] is a head redex
(i.e. a head reduction step is possible). *)
Inductive is_value : expr → Prop :=
  | EVal_is_value Ω v : is_value (valc@{Ω} v).
Inductive is_redex : expr → Prop :=
  | EVar_is_redex x : is_redex (var x)
  | EAssign_is_redex ass el er :
     is_value el → is_value er → is_redex (el ::=@{ass} er)
  | ECall_is_redex f es : Forall is_value es → is_redex (call f @ es)
  | ELoad_is_redex e : is_value e → is_redex (load e)
  | EAlloc_is_redex : is_redex alloc
  | EFree_is_redex e : is_value e → is_redex (free e)
  | EUnOp_is_redex op e : is_value e → is_redex (⊙{op} e)
  | EBinOp_is_redex op el er :
     is_value el → is_value er → is_redex (el ⊙{op} er)
  | EIf_is_redex e el er : is_value e → is_redex (IF e then el else er)
  | EComma_is_redex el er : is_value el → is_redex (el ,, er)
  | ECast_is_redex τ e : is_value e → is_redex (cast@{τ} e).

Instance is_value_dec (e : expr) : Decision (is_value e).
Proof.
 refine (match e with valc@{_} _ => left _ | _ => right _ end%E);
  try constructor; abstract (inversion 1).
Defined.
Instance is_redex_dec (e : expr) : Decision (is_redex e).
Proof.
 refine (
  match e with
  | var _ => left _
  | valc@{_} _ => right _
  | el ::=@{_} er => cast_if_and (decide (is_value el)) (decide (is_value er))
  | call _ @ es => cast_if (decide (Forall is_value es))
  | alloc => left _
  | load e
  | free e
  | ⊙{_} e => cast_if (decide (is_value e))
  | el ⊙{_} er => cast_if_and (decide (is_value el)) (decide (is_value er))
  | (IF e then _ else _) => cast_if (decide (is_value e))
  | el ,, er => cast_if (decide (is_value el))
  | cast@{_} e => cast_if (decide (is_value e))
  end%E); try (by constructor); abstract (by inversion 1).
Defined.

Lemma is_redex_value e : is_redex e → is_value e → False.
Proof. destruct 1; inversion 1. Qed.
Lemma is_redex_val Ω v : ¬is_redex (valc@{Ω} v).
Proof. inversion 1. Qed.
Lemma is_value_alt e : is_value e ↔ ∃ Ω v, e = (valc@{Ω} v)%E.
Proof. split. inversion 1; eauto. by intros (?&?&?); subst. Qed.
Lemma Forall_is_value_alt es :
  Forall is_value es ↔ ∃ Ωs vs, es = zip_with EVal Ωs vs ∧ Ωs `same_length` vs.
Proof.
  split.
  * induction 1 as [|?? [Ω v] _ (Ωs & vs & ?&?)]; subst.
    + eexists [], []. split. done. constructor.
    + exists (Ω :: Ωs) (v :: vs). split. done. by constructor.
  * intros (Ωs & vs & H & Hvs); subst.
    induction Hvs; simpl; auto using EVal_is_value.
Qed.

(** * Contexts with one hole *)
(** We define singular expression contexts [ectx_item], and then full expression
(evaluation) contexts [ectx] are lists of expression contexts. These expression
contexts allow us to enforce an evaluation strategy. In particular, for the
conditional we merely allow a hole for the first branch. *)
Inductive ectx_item :=
  | CAssignL : assign → expr → ectx_item
  | CAssignR : assign → expr → ectx_item
  | CCall : funname → list expr → list expr → ectx_item
  | CLoad : ectx_item
  | CFree : ectx_item
  | CUnOp : unop → ectx_item
  | CBinOpL : binop → expr → ectx_item
  | CBinOpR : binop → expr → ectx_item
  | CIf : expr → expr → ectx_item
  | CComma : expr → ectx_item
  | CCast : int_type → ectx_item.
Notation ectx := (list ectx_item).

Bind Scope expr_scope with ectx_item.

Arguments CAssignL _ _.
Arguments CAssignR _ _.
Arguments CCall _ _ _.
Arguments CLoad.
Arguments CFree.
Arguments CUnOp _.
Arguments CBinOpL _ _.
Arguments CBinOpR _ _.
Arguments CIf _ _.
Arguments CComma _.
Arguments CCast _.

Notation "□ ::=@{ a } er" := (CAssignL a er)
  (at level 60, format "□  ::=@{ a }  er") : expr_scope.
Notation "el ::=@{ a } □" := (CAssignR a el)
  (at level 60, format "el  ::=@{ a }  □") : expr_scope.
Notation "'call' f @ es1 □ es2" := (CCall f es1 es2)
  (at level 10, es1 at level 66, es2 at level 66) : expr_scope.
Notation "'load' □" := CLoad (at level 10, format "load  □") : expr_scope.
Notation "'free' □" := CFree (at level 10, format "free  □") : expr_scope.
Notation "⊙{ op } □" := (CUnOp op)
  (at level 21, format "⊙{ op } □") : expr_scope.
Notation "□ ⊙{ op } er" := (CBinOpL op er)
  (at level 50, format "□  ⊙{ op }  er") : expr_scope.
Notation "el ⊙{ op } □" := (CBinOpR op el)
  (at level 50, format "el  ⊙{ op }  □") : expr_scope.
Notation "'IF' □ 'then' el 'else' er" := (CIf el er)
  (at level 200, format "'IF'  □  'then'  el  'else'  er") : expr_scope.
Notation "□ ,, er" := (CComma er) (at level 55, format "□  ,,  er") : expr_scope.
Notation "'cast' @{ τ } □" := (CCast τ)
  (at level 10, format "'cast' @{ τ }  □") : expr_scope.

Instance ectx_item_dec: ∀ Ei1 Ei2 : ectx_item, Decision (Ei1 = Ei2).
Proof. solve_decision. Defined.

(** Substitution is defined in a straightforward way. Using the type class
instances in the file [contexts], it is lifted to full expression contexts. *)
Instance ectx_item_subst: Subst ectx_item expr expr := λ Ei e,
  match Ei with
  | □ ::=@{ass} er => e ::=@{ass} er
  | el ::=@{ass} □ => el ::=@{ass} e
  | call f @ es1 □ es2 => call f @ (reverse es1 ++ e :: es2)
  | load □ => load e
  | free □ => free e
  | ⊙{op} □ => ⊙{op} e
  | □ ⊙{op} er => e ⊙{op} er
  | el ⊙{op} □ => el ⊙{op} e
  | □ ,, er => e ,, er
  | (IF □ then el else er) => IF e then el else er
  | cast @{τ} □ => cast @{τ} e
  end%E.
Instance: DestructSubst ectx_item_subst.

Instance: ∀ Ei : ectx_item, Injective (=) (=) (subst Ei).
Proof. by destruct Ei; intros ???; simplify_list_equality. Qed.

Lemma is_value_ectx_item (Ei : ectx_item) e : ¬is_value (subst Ei e).
Proof. destruct Ei; inversion 1. Qed.
Lemma is_value_ectx (E : ectx) e : is_value (subst E e) → E = [].
Proof.
  destruct E using rev_ind; auto.
  rewrite subst_snoc. intros; edestruct is_value_ectx_item; eauto.
Qed.
Lemma is_value_redex_ectx (E : ectx) e : is_redex e → ¬is_value (subst E e).
Proof.
  intros ? HEe. rewrite (is_value_ectx E e) in HEe by done; simpl in HEe.
  eauto using is_redex_value.
Qed.
Lemma is_redex_ectx_item (Ei : ectx_item) e: is_redex (subst Ei e) → is_value e.
Proof. by destruct Ei; inversion 1; decompose_Forall. Qed.
Lemma is_redex_ectx (E : ectx) e :
  is_redex (subst E e) → (E = [] ∧ is_redex e) ∨ (∃ Ei, E = [Ei] ∧ is_value e).
Proof.
  destruct E as [|Ei E _] using rev_ind; eauto.
  rewrite subst_snoc. intros HE. apply is_redex_ectx_item in HE.
  feed pose proof (is_value_ectx E e); subst; simpl in *; eauto.
Qed.

Instance ectx_locks: Locks ectx_item := λ Ei,
  match Ei with
  | □ ::=@{_} er => locks er
  | el ::=@{_} □ => locks el
  | call f @ es1 □ es2 => ⋃ (locks <$> es1) ∪ ⋃ (locks <$> es2)
  | load □ => ∅
  | free □ => ∅
  | ⊙{op} □ => ∅
  | □ ⊙{op} er => locks er
  | el ⊙{op} □ => locks el
  | (IF □ then el else er) => locks el ∪ locks er
  | □ ,, er => locks er
  | cast @{τ} □ => ∅
  end%E.

Lemma ectx_item_is_pure fs (Ei : ectx_item) (e : expr) :
  is_pure fs (subst Ei e) → is_pure fs e.
Proof. destruct Ei; simpl; inversion_clear 1; decompose_Forall; eauto. Qed.
Lemma ectx_is_pure fs (E : ectx) (e : expr) :
  is_pure fs (subst E e) → is_pure fs e.
Proof.
  induction E using rev_ind; rewrite ?subst_snoc; eauto using ectx_item_is_pure.
Qed.
Lemma ectx_item_subst_locks (Ei : ectx_item) e :
  locks (subst Ei e) = locks Ei ∪ locks e.
Proof.
  apply elem_of_equiv_L. intro. destruct Ei; simpl; try solve_elem_of.
  rewrite fmap_app, fmap_reverse; simpl.
  rewrite union_list_app_L, union_list_cons, union_list_reverse_L.
  solve_elem_of.
Qed.
Lemma ectx_subst_locks (E : ectx) e : locks (subst E e) = locks E ∪ locks e.
Proof.
  apply elem_of_equiv_L. intros. revert e. induction E as [|Ei E IH]; simpl.
  * solve_elem_of.
  * intros. rewrite IH, ectx_item_subst_locks. solve_elem_of.
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
  Context (Pval : ∀ E Ω v, P E (valc@{Ω} v)).
  Context (Passign : ∀ E ass el er,
    P ((□ ::=@{ass} er)%E :: E) el → P ((el ::=@{ass} □)%E :: E) er →
    P E (el ::=@{ass} er)).
  Context (Pcall : ∀ E f es,
    zipped_Forall (λ esl esr, P ((call f @ esl □ esr)%E :: E)) [] es →
    P E (call f @ es)).
  Context (Pload : ∀ E e, P ((load □)%E :: E) e → P E (load e)).
  Context (Palloc : ∀ E, P E alloc).
  Context (Pfree : ∀ E e, P ((free □)%E :: E) e → P E (free e)).
  Context (Punop : ∀ E op e, P ((⊙{op} □)%E :: E) e → P E (⊙{op} e)).
  Context (Pbinop : ∀ E op el er,
    P ((□ ⊙{op} er)%E :: E) el → P ((el ⊙{op} □)%E :: E) er →
    P E (el ⊙{op} er)).
  Context (Pif : ∀ E e el er,
    P ((IF □ then el else er)%E :: E) e → P E (IF e then el else er)).
  Context (Pcomma : ∀ E el er, P ((□ ,, er)%E :: E) el → P E (el ,, er)).
  Context (Pcast : ∀ E τ e,
    P ((cast @{τ} □)%E :: E) e → P E (cast @{τ} e)).

  Definition ectx_expr_ind : ∀ E e, P E e :=
    fix go E e : P E e :=
    match e with
    | var x => Pvar _ x
    | valc@{Ω} v => Pval _ Ω v
    | el ::=@{_} er => Passign _ _ _ _ (go _ el) (go _ er)
    | call f @ es => Pcall E f es $
       zipped_list_ind _ zipped_Forall_nil
        (λ _ _ e, @zipped_Forall_cons _ (λ _ _, P _) _ _ _ (go _ e)) [] es
    | load e => Pload _ _ (go _ e)
    | alloc => Palloc _
    | free e => Pfree _ _ (go _ e)
    | ⊙{op} e => Punop _ op _ (go _ e)
    | el ⊙{op} er => Pbinop _ op _ _ (go _ el) (go _ er)
    | (IF e then el else er) => Pif _ _ _ _ (go _ e)
    | el ,, er => Pcomma _ _ _ (go _ el)
    | cast @{τ} e => Pcast _ _ _ (go _ e)
    end%E.
End ectx_expr_ind.

Ltac ectx_expr_ind E e :=
  repeat match goal with
  | H : context [ E ] |- _ => revert H
  | H : context [ e ] |- _ => revert H
  end;
  revert E e;
  match goal with |- ∀ E e, @?P E e => apply (ectx_expr_ind P) end.

(** * Contexts with multiple holes *)
(** We define singular expression contexts indexed by the number of holes. These
contexts are particularly useful to prove some of the Hoare rules in a more
generic way. *)
Inductive ectx_full : nat → Type :=
  | DCVal : indexset → val → ectx_full 0
  | DCVar : nat → ectx_full 0
  | DCAssign : assign → ectx_full 2
  | DCCall {n} : funname → ectx_full n
  | DCLoad : ectx_full 1
  | DCAlloc : ectx_full 0
  | DCFree : ectx_full 1
  | DCUnOp : unop → ectx_full 1
  | DCBinOp : binop → ectx_full 2
  | DCIf : expr → expr → ectx_full 1
  | DCComma : expr → ectx_full 1
  | DCCast : int_type → ectx_full 1.

Arguments DCVal _ _.
Arguments DCVar _.
Arguments DCAssign _.
Arguments DCCall {_} _.
Arguments DCLoad.
Arguments DCAlloc.
Arguments DCFree.
Arguments DCUnOp _.
Arguments DCBinOp _.
Arguments DCIf _ _.
Arguments DCComma _.
Arguments DCCast _.

Instance ectx_full_subst: DepSubst ectx_full (vec expr) expr := λ _ E,
  match E with
  | DCVal Ω v => λ _, valc@{Ω} v
  | DCVar x => λ _, var x
  | DCAssign ass => λ es, es !!! 0 ::=@{ass} es !!! 1
  | DCCall _ f => λ es, call f @ es
  | DCLoad => λ es, load (es !!! 0)
  | DCAlloc => λ es, alloc
  | DCFree => λ es, free (es !!! 0)
  | DCUnOp op => λ es, ⊙{op} es !!! 0
  | DCBinOp op => λ es, es !!! 0 ⊙{op} es !!! 1
  | DCIf el er => λ es, IF es !!! 0 then el else er
  | DCComma er => λ es, es !!! 0 ,, er
  | DCCast τ => λ es, cast @{τ} (es !!! 0)
  end%E.
Instance ectx_full_locks {n} : Locks (ectx_full n) := λ E,
  match E with
  | DCVal Ω v => Ω
  | DCIf el er => locks el ∪ locks er
  | DCComma er => locks er
  | _ => ∅
  end%E.

Lemma ectx_full_subst_inj {n} (E : ectx_full n) es1 es2 :
  depsubst E es1 = depsubst E es2 → es1 = es2.
Proof.
  destruct E; inv_all_vec_fin; simpl; intros; simplify_equality;
    auto using vec_to_list_inj2.
Qed.
Lemma ectx_full_subst_locks {n} (E : ectx_full n) (es : vec expr n) :
  locks (depsubst E es) = locks E ∪ ⋃ (locks <$> vec_to_list es).
Proof.
  apply elem_of_equiv_L. intro. destruct E; inv_all_vec_fin; solve_elem_of.
Qed.

(** Giving values [es] for the holes of the context [E], the function
[ectx_full_to_item E es i] yields a context with exactly one hole for the
[i]th value. The [i]th value in [es] is ignored. *)
Definition ectx_full_to_item {n} (E : ectx_full n)
    (es : vec expr n) (i : fin n) : ectx_item :=
  match E in ectx_full n return fin n → vec expr n → ectx_item with
  | DCVal _ _ => fin_0_inv _
  | DCVar _ => fin_0_inv _
  | DCAssign ass =>
     fin_S_inv _ (λ es, □ ::=@{ass} es !!! 1)%E $
     fin_S_inv _ (λ es, es !!! 0 ::=@{ass} □)%E $ fin_0_inv _
  | DCCall _ f => λ i es, (call f @ reverse (take i es) □ drop (FS i) es)%E
  | DCLoad => fin_S_inv _ (λ es, load □)%E $ fin_0_inv _
  | DCAlloc => fin_0_inv _
  | DCFree => fin_S_inv _ (λ es, free □)%E $ fin_0_inv _
  | DCUnOp op => fin_S_inv _ (λ es, ⊙{op} □)%E $ fin_0_inv _
  | DCBinOp op =>
     fin_S_inv _ (λ es, □ ⊙{op} es !!! 1)%E $
     fin_S_inv _ (λ es, es !!! 0 ⊙{op} □)%E $ fin_0_inv _
  | DCIf el er => fin_S_inv _ (λ es, IF □ then el else er)%E $ fin_0_inv _
  | DCComma er => fin_S_inv _ (λ es, □ ,, er)%E $ fin_0_inv _
  | DCCast τ => fin_S_inv _ (λ es, cast@{τ} □)%E $ fin_0_inv _
  end i es.

Lemma ectx_full_to_item_insert {n} (E : ectx_full n) es i e :
  ectx_full_to_item E (vinsert i e es) i = ectx_full_to_item E es i.
Proof.
  destruct E; inv_all_vec_fin; simpl; try reflexivity.
  rewrite !vec_to_list_insert, take_insert, drop_insert; auto with arith.
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
Lemma ectx_full_item_subst {n} (E : ectx_full n) (es : vec _ n)
    (Ei : ectx_item) (e : expr) :
  depsubst E es = subst Ei e →
    ∃ i, e = es !!! i ∧ Ei = ectx_full_to_item E es i.
Proof.
  intros H. destruct E, Ei; simpl; simplify_equality; eauto.
  edestruct (vec_to_list_lookup_middle es) as (i&H1&?&H2); eauto.
  exists i. subst. by rewrite <-H1, reverse_involutive.
Qed.
Lemma Forall_is_value_alt_vec {n} (es : vec expr n) :
  Forall is_value es ↔ ∃ Ωs vs, es = vzip_with EVal Ωs vs.
Proof.
  rewrite Forall_is_value_alt. split.
  * intros (Ωs & vs & Hes & Hvs). revert n es Hes.
    induction Hvs; intros ?  [|???] ?; simpl in *;
      simplify_equality; try (done || by eexists [#], [#]).
    edestruct IHHvs as (?&?&?); eauto. subst.
    eexists (_ ::: _), (_ ::: _); simpl; eauto.
  * intros (Ωs & vs & Hes). exists Ωs vs. split.
    + by rewrite Hes, vec_to_list_zip_with.
    + apply vec_to_list_same_length.
Qed.
Lemma expr_vec_values {n} (es : vec expr n) :
  (∃ Ωs vs, es = vzip_with EVal Ωs vs) ∨ (∃ i, ¬is_value (es !!! i)).
Proof.
  destruct (Forall_Exists_dec is_value es) as [H | H].
  * left. by apply Forall_is_value_alt_vec.
  * right. by apply Exists_vlookup in H.
Qed.
Lemma is_redex_ectx_full {n} (E : ectx_full n) (es : vec _ n) :
  is_redex (depsubst E es) → Forall is_value es.
Proof.
  destruct E; inversion_clear 1; inv_all_vec_fin; repeat constructor; auto.
Qed.
Lemma ectx_full_to_item_locks {n} (E : ectx_full n) (es : vec _ n) i :
  locks (ectx_full_to_item E es i) =
    locks E ∪ ⋃ (locks <$> delete (fin_to_nat i) (vec_to_list es)).
Proof.
  apply elem_of_equiv_L. intros b.
  destruct E; inv_all_vec_fin; simpl; try esolve_elem_of.
  rewrite fmap_reverse, union_list_reverse.
  rewrite delete_take_drop, fmap_app, union_list_app. esolve_elem_of.
Qed.

(** The function [expr_redexes e] computes the set of redexes contained in an
expression [e]. Here, redexes are pairs [(E', e')] where [E'] is an expression
evaluation context, and [e'] an expression with [is_redex e']. *)
Section expr_split.
  Context C `{Collection (ectx * expr) C}.

  Definition expr_redexes_go : ectx → expr → C :=
    fix go E e {struct e} :=
    if decide (is_redex e) then {[ (E, e) ]} else
    match e with
    | valc@{_} _ => ∅
    | var x => ∅ (* impossible *)
    | el ::=@{ass} er => go (□ ::=@{ass} er :: E) el ∪ go (el ::=@{ass} □ :: E) er
    | call f @ es =>
       ⋃ zipped_map (λ esl esr, go ((call f @ esl □ esr) :: E)) [] es
    | load e => go (load □ :: E) e
    | alloc => ∅ (* impossible *)
    | free e => go (free □ :: E) e
    | ⊙{op} e => go (⊙{op} □ :: E) e
    | e1 ⊙{op} e2 => go (□ ⊙{op} e2 :: E) e1 ∪ go (e1 ⊙{op} □ :: E) e2
    | (IF e then el else er) => go ((IF □ then el else er) :: E) e
    | el ,, er => go ((□ ,, er) :: E) el
    | cast@{τ} e => go ((cast@{τ} □) :: E) e
    end%E.
  Definition expr_redexes : expr → C := expr_redexes_go [].

  Lemma expr_redexes_go_is_redex E e E' e' :
    (E', e') ∈ expr_redexes_go E e → is_redex e'.
  Proof.
    assert (∀ (f : list _ → list _ → expr → C) es,
      (E', e') ∈ ⋃ zipped_map f [] es →
      zipped_Forall (λ esl esr e, (E', e') ∈ f esl esr e → is_redex e') [] es →
      is_redex e').
    { intros f es Hes Hforall.
      rewrite elem_of_union_list in Hes. destruct Hes as (rs&Hes&?).
      rewrite elem_of_zipped_map in Hes. destruct Hes as (?&?&?&?&?); subst.
      apply zipped_Forall_app in Hforall. inversion Hforall; subst. auto. }
    ectx_expr_ind E e;
     simpl; intros; repeat case_decide; solve_elem_of (eauto; try constructor).
  Qed.
  Lemma expr_redexes_go_sound E e E' e' :
    (E', e') ∈ expr_redexes_go E e → subst E e = subst E' e'.
  Proof.
    assert (∀ g (f : list _ → list _ → expr → C) (E : ectx) es,
      (E', e') ∈ ⋃ zipped_map f [] es →
      zipped_Forall (λ esl esr e, (E', e') ∈ f esl esr e →
        subst E (g (reverse esl ++ [e] ++ esr)) = subst E' e') [] es →
      subst E (g es) = subst E' e').
    { intros ? g f es Hes Hforall.
      rewrite elem_of_union_list in Hes. destruct Hes as (rs&Hes&?).
      rewrite elem_of_zipped_map in Hes. destruct Hes as (esl&?&?&?&?); subst.
      apply zipped_Forall_app in Hforall. inversion Hforall; subst.
      rewrite <-(reverse_involutive esl), <-(right_id_L [] (++) (reverse esl)).
      auto. }
    ectx_expr_ind E e;
     simpl; intros; repeat case_decide; solve_elem_of eauto.
  Qed.
  Lemma expr_redexes_go_complete E' E e :
    is_redex e → (E ++ E', e) ∈ expr_redexes_go E' (subst E e).
  Proof.
    intros. revert E'. induction E as [|Ei E IH] using rev_ind; simpl.
    { intros. unfold expr_redexes_go. destruct e; case_decide; solve_elem_of. }
    intros E'. assert (¬is_redex (subst (E ++ [Ei]) e)) as Hredex.
    { intro. destruct (is_redex_ectx (E ++ [Ei]) e) as [[??]|(?&?&?)]; auto.
      * discriminate_list_equality.
      * eauto using is_redex_value. }
    rewrite subst_snoc in Hredex |- *. rewrite <-(associative_L (++)).
    destruct Ei; simpl; case_decide; try solve_elem_of.
    rewrite elem_of_union_list. eexists (expr_redexes_go _ _).
    rewrite elem_of_zipped_map. split; eauto. eexists (reverse _), _, _.
    split. done. by rewrite reverse_involutive, (right_id_L [] (++)). 
  Qed.

  Lemma expr_redexes_is_redex e E' e' : (E', e') ∈ expr_redexes e → is_redex e'.
  Proof. apply expr_redexes_go_is_redex. Qed.
  Lemma expr_redexes_sound e E' e' :
    (E', e') ∈ expr_redexes e → e = subst E' e'.
  Proof. apply expr_redexes_go_sound. Qed.
  Lemma expr_redexes_complete E e :
    is_redex e → (E, e) ∈ expr_redexes (subst E e).
  Proof.
    generalize (expr_redexes_go_complete [] E e).
    by rewrite (right_id_L [] (++) E).
  Qed.
  Lemma expr_redexes_correct e E' e' :
    (E', e') ∈ expr_redexes e ↔ e = subst E' e' ∧ is_redex e'.
  Proof.
    split.
    * eauto using expr_redexes_sound, expr_redexes_is_redex.
    * by intros [??]; subst; apply expr_redexes_complete.
  Qed.

  Lemma expr_redexes_go_is_value E e : expr_redexes_go E e ≡ ∅ → is_value e.
  Proof.
    assert (∀ (f : list _ → list _ → expr → C) es1 es2,
      ⋃ (zipped_map f es1 es2) ≡ ∅ →
      zipped_Forall (λ esl esr e, f esl esr e ≡ ∅ → is_value e) es1 es2 →
      Forall is_value es2).
    { intros ???. rewrite empty_union_list.
      induction 2; simpl in *; decompose_Forall; auto. }
    ectx_expr_ind E e;
      simpl; intros; repeat case_decide; decompose_empty;
      try match goal with
      | |- is_value _ => constructor
      | H : ¬is_redex _ |- _ => destruct H; constructor
      end; eauto.
  Qed.
  Lemma expr_redexes_is_value e : expr_redexes e ≡ ∅ → is_value e.
  Proof. apply expr_redexes_go_is_value. Qed.
End expr_split.

Lemma is_value_or_redex (e : expr) :
  is_value e ∨ ∃ (E' : ectx) e', is_redex e' ∧ e = subst E' e'.
Proof.
  destruct (elem_of_or_empty (expr_redexes
    (listset (ectx * expr)) e)) as [[[E' e'] ?]|?].
  * right. exists E' e'. split.
    + by apply (expr_redexes_is_redex (listset _)) with e E'. 
    + by apply (expr_redexes_correct (listset _)).
  * left. by apply (expr_redexes_is_value (listset _)).
Qed.
Lemma is_value_is_redex (e : expr) :
  ¬is_value e → ∃ (E' : ectx) e', is_redex e' ∧ e = subst E' e'.
Proof. intros. by destruct (is_value_or_redex e). Qed.
