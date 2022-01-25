(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file defines expressions and some associated theory. Most importantly,
to define the operational semantics in the file [smallstep], we define
corresponding evaluation contexts. Notations for expressions are declared in the
scope [expr_scope]. *)
From stdpp Require Import mapset natmap.
Require Export contexts assignments.

(** * Stacks *)
(** Stacks are lists of memory indexes rather than lists of values. This allows
us to treat pointers to both automatically and dynamically allocated memory in
a uniform way. Evaluation of a variable will therefore consist of a looking up
its address in the stack and returning a pointer to that address. *)

Notation stack K := (list (index * type K)) (only parsing).
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

Notation lrval K := (ptr K + val K)%type.

Inductive expr (K : iType) : iType :=
  | EVar : nat → expr K
  | EVal : lockset → lrval K → expr K
  | ERtoL : expr K → expr K
  | ERofL : expr K → expr K
  | EAssign : assign → expr K → expr K → expr K
  | ECall : expr K → list (expr K) → expr K
  | EAbort : type K → expr K
  | ELoad : expr K → expr K
  | EEltL : expr K → ref_seg K → expr K
  | EEltR : expr K → ref_seg K → expr K
  | EAlloc : type K → expr K → expr K
  | EFree : expr K → expr K
  | EUnOp : unop → expr K → expr K
  | EBinOp : binop → expr K → expr K → expr K
  | EIf : expr K → expr K → expr K → expr K
  | EComma : expr K → expr K → expr K
  | ECast : type K → expr K → expr K
  | EInsert : ref K → expr K → expr K → expr K.

(** We use the scope [expr_scope] to declare notations for expressions. We
overload some notations already in [value_scope], and define both general and
specific notations for operations, allowing us for example to to write
[intc 10 + intc 20] instead of the much longer
[valc (intc 10) ⊙{PlusOp} valc (intc 20)]. *)
Declare Scope expr_scope.
Delimit Scope expr_scope with E.
Bind Scope expr_scope with expr.
Local Open Scope expr_scope.

Arguments EVar {_} _.
Arguments EVal {_} _ _.
Arguments ERtoL {_} _%expr_scope.
Arguments ERofL {_} _%expr_scope.
Arguments EAssign {_} _ _%expr_scope _%expr_scope.
Arguments ECall {_} _%expr_scope _%expr_scope.
Arguments EAbort {_} _.
Arguments ELoad {_} _%expr_scope.
Arguments EEltL {_} _%expr_scope _.
Arguments EEltR {_} _%expr_scope _.
Arguments EAlloc {_} _%ctype_scope _%expr_scope.
Arguments EFree {_} _%expr_scope.
Arguments EUnOp {_} _ _%expr_scope.
Arguments EBinOp {_} _ _%expr_scope _%expr_scope.
Arguments EIf {_} _%expr_scope _%expr_scope _%expr_scope.
Arguments EComma {_} _%expr_scope _%expr_scope.
Arguments ECast {_} _ _%expr_scope.
Arguments EInsert {_} _ _%expr_scope _%expr_scope.

(* The infixes [++] and [::] are at level 60, and [<$>] is at level 65. We
should remain below those. *)
Notation "'var' x" := (EVar x)
  (at level 10, format "var  x") : expr_scope.
Notation "%#{ Ω } ν" := (EVal Ω ν)
  (at level 15, format "%#{ Ω }  ν") : expr_scope.
Notation "%# ν" := (EVal ∅ ν) (at level 15) : expr_scope.
Notation "#{ Ω } v" := (EVal Ω (inr v))
  (at level 15, format "#{ Ω }  v") : expr_scope.
Notation "#{ Ωs }* vs" := (zip_with (λ Ω v, #{Ω} v) Ωs vs)
  (at level 15, format "#{ Ωs }*  vs") : expr_scope.
Notation "# v" := (EVal ∅ (inr v)) (at level 15) : expr_scope.
Notation "%{ Ω } a" := (EVal Ω (inl a))
  (at level 15, format "%{ Ω }  a") : expr_scope.
Notation "% a" := (EVal ∅ (inl a)) (at level 15) : expr_scope.
Notation ".* e" := (ERtoL e) (at level 24) : expr_scope.
Notation "& e" := (ERofL e) (at level 24) : expr_scope.
Notation "e1 ::={ ass } e2" := (EAssign ass e1 e2)
  (at level 54, format "e1  ::={ ass }  e2", right associativity) : expr_scope.
Infix "::=" := (EAssign Assign) (at level 54, right associativity) : expr_scope.
Notation "'call' e @ es" := (ECall e es)
  (at level 10, es at level 66) : expr_scope.
Notation "'abort' τ" := (EAbort τ) (at level 10) : expr_scope.
Notation "'load' e" := (ELoad e) (at level 10) : expr_scope.
Notation "e %> rs" := (EEltL e rs) (at level 22) : expr_scope.
Notation "e #> rs" := (EEltR e rs) (at level 22) : expr_scope.
Notation "alloc{ τ } e" := (EAlloc τ e)
  (at level 10, format "alloc{ τ }  e") : expr_scope.
Notation "'free' e" := (EFree e) (at level 10) : expr_scope.
Notation ".{ op } e" := (EUnOp op e)
  (at level 35, format ".{ op }  e") : expr_scope.
Notation "e1 .{ op } e2" := (EBinOp op e1 e2)
  (at level 50, format "e1  .{ op }  e2") : expr_scope.
Notation "'if{' e1 } e2 'else' e3" := (EIf e1 e2 e3)
  (at level 56, format "if{ e1 }  e2  'else'  e3") : expr_scope.
Notation "e1 ,, e2" := (EComma e1 e2)
  (at level 58, right associativity, format "e1  ,,  e2") : expr_scope.
Notation "'cast{' τ } e" := (ECast τ e)
  (at level 10, format "'cast{' τ }  e") : expr_scope.
Notation "'cast{' τs }* es" := (zip_with ECast τs es)
  (at level 10, format "'cast{' τs }*  es") : expr_scope.
Notation "#[ r := e ] e'" := (EInsert r e e')
  (at level 10, format "#[ r := e ]  e'") : expr_scope.

Infix "+" := (EBinOp (ArithOp PlusOp))
  (at level 50, left associativity) : expr_scope.
Infix "-" := (EBinOp (ArithOp MinusOp))
  (at level 50, left associativity) : expr_scope.
Infix "*" := (EBinOp (ArithOp MultOp))
  (at level 40, left associativity) : expr_scope.
Infix "/" := (EBinOp (ArithOp DivOp))
  (at level 40, left associativity) : expr_scope.
Infix "==" := (EBinOp (CompOp EqOp)) (at level 52) : expr_scope.
Notation "- e" := (EUnOp NegOp e)
  (at level 35, right associativity) : expr_scope.

#[global] Instance: `{Inj (=) (=) (@EVar K)}.
Proof. by injection 1. Qed.
#[global] Instance: `{Inj2 (=) (=) (=) (λ Ω (v : val K), #{Ω} v)}.
Proof. by injection 1. Qed.
#[global] Instance: `{Inj2 (=) (=) (=) (@EVal K)}.
Proof. by injection 1. Qed.
#[global] Instance: `{Inj (=) (=) (@ELoad K)}.
Proof. by injection 1. Qed.
#[global] Instance: `{Inj (=) (=) (@EFree K)}.
Proof. by injection 1. Qed.

#[global] Instance maybe_EAlloc {K} : Maybe2 (@EAlloc K) := λ e,
  match e with alloc{τ} e => Some (τ,e) | _ => None end.
#[global] Instance maybe_EVal {K} : Maybe2 (@EVal K) := λ e,
  match e with %#{Ω} ν => Some (Ω,ν) | _ => None end.
#[global] Instance maybe_EVal_inl {K} : Maybe2 (λ Ω (p : ptr K), %{Ω} p) := λ e,
  match e with %{Ω} a => Some (Ω,a) | _ => None end.
#[global] Instance maybe_EVal_inr {K} : Maybe2 (λ Ω (v : val K), #{Ω} v) := λ e,
  match e with #{Ω} v => Some (Ω,v) | _ => None end.
#[global] Instance maybe_ECall {K} : Maybe2 (@ECall K) := λ e,
  match e with call e @ es => Some (e,es) | _ => None end.

#[global] Instance assign_eq_dec: EqDecision assign.
Proof. solve_decision. Defined.
#[global] Instance expr_eq_dec {K} `{EqDecision K} :
  EqDecision (expr K).
Proof.
  refine (fix go e1 e2 : Decision (e1 = e2) := let _ : EqDecision (expr K) := go in
  match e1, e2 with
  | var i1, var i2 => cast_if (decide (i1 = i2))
  | %#{Ω1} ν1, %#{Ω2} ν2 =>
     cast_if_and (decide (Ω1 = Ω2)) (decide (ν1 = ν2))
  | .* e1, .* e2 | & e1, & e2 => cast_if (decide (e1 = e2))
  | e1 ::={ass1} e3, e2 ::={ass2} e4 =>
     cast_if_and3 (decide (ass1 = ass2)) (decide (e1 = e2))
       (decide (e3 = e4))
  | call e1 @ es1, call e2 @ es2 => cast_if_and (decide (e1 = e2))
     (decide (es1 = es2))
  | abort τ1, abort τ2 => cast_if (decide (τ1 = τ2))
  | load e1, load e2 => cast_if (decide (e1 = e2))
  | e1 %> rs1, e2 %> rs2 | e1 #> rs1, e2 #> rs2 =>
     cast_if_and (decide (e1 = e2)) (decide (rs1 = rs2))
  | alloc{τ1} e1, alloc{τ2} e2 =>
     cast_if_and (decide (τ1 = τ2)) (decide (e1 = e2))
  | free e1, free e2 => cast_if (decide (e1 = e2))
  | .{op1} e1, .{op2} e2 => cast_if_and (decide (op1 = op2))
     (decide (e1 = e2))
  | e1 .{op1} e3, e2 .{op2} e4 => cast_if_and3 (decide (op1 = op2))
     (decide (e1 = e2)) (decide (e3 = e4))
  | if{e1} e3 else e5, if{e2} e4 else e6 =>
     cast_if_and3 (decide (e1 = e2))
       (decide (e3 = e4)) (decide (e5 = e6))
  | e1,, e3, e2,, e4 =>
     cast_if_and (decide (e1 = e2)) (decide (e3 = e4))
  | cast{τ1} e1, cast{τ2} e2 =>
     cast_if_and (decide (τ1 = τ2)) (decide (e1 = e2))
  | #[r1:=e1] e3, #[r2:=e2] e4 =>
     cast_if_and3 (decide (r1 = r2))
       (decide (e1 = e2)) (decide (e3 = e4))
  | _, _ => right _
  end); congruence.
Defined.

#[global] Instance expr_freeze {K} : Freeze (expr K) :=
  fix go β e {struct e} :=
  let _ : Freeze _ := @go in
  match e with
  | var x => var x
  | %#{Ω} ν => %#{Ω} ν
  | .* e => .* (freeze β e)
  | & e => & (freeze β e)
  | e1 ::={ass} e2 => freeze β e1 ::={ass} freeze β e2
  | call e @ es => call (freeze β e) @ freeze β <$> es
  | load e => load (freeze β e)
  | abort τ => abort τ
  | e %> rs => freeze β e %> freeze β rs
  | e #> rs => freeze β e #> freeze β rs
  | alloc{τ} e => alloc{τ} (freeze β e)
  | free e => free (freeze β e)
  | .{op} e => .{op} (freeze β e)
  | e1 .{op} e2 => (freeze β e1) .{op} freeze β e2
  | if{e1} e2 else e3 => if{freeze β e1} freeze β e2 else freeze β e3
  | e1,, e2 => freeze β e1,, freeze β e2
  | cast{τ} e => cast{τ} (freeze β e)
  | #[r:=e1] e2 => #[freeze β <$> r:=freeze β e1] (freeze β e2)
  end.

(** * Induction principles *)
(** The induction principles that Coq generates for nested inductive types are
too weak. For the case of expressions, the branch of [call e @ es] does not
contain an induction hypothesis for the function arguments [es]. We therefore
define an appropriate induction principle for expressions by hand. *)
Section expr_ind.
  Context {K} (P : expr K → Prop).
  Context (Pvar : ∀ x, P (var x)).
  Context (Pval : ∀ Ω ν, P (%#{Ω} ν)).
  Context (Prtol : ∀ e, P e → P (.* e)).
  Context (Profl : ∀ e, P e → P (& e)).
  Context (Passign : ∀ ass e1 e2, P e1 → P e2 → P (e1 ::={ ass } e2)).
  Context (Pcall : ∀ e es, P e → Forall P es → P (call e @ es)).
  Context (Pabort : ∀ τ, P (abort τ)).
  Context (Pload : ∀ e, P e → P (load e)).
  Context (Peltl : ∀ e rs, P e → P (e %> rs)).
  Context (Peltr : ∀ e rs, P e → P (e #> rs)).
  Context (Palloc : ∀ τ e, P e → P (alloc{τ} e)).
  Context (Pfree : ∀ e, P e → P (free e)).
  Context (Punop : ∀ op e, P e → P (.{op} e)).
  Context (Pbinop : ∀ op e1 e2, P e1 → P e2 → P (e1 .{op} e2)).
  Context (Pif : ∀ e1 e2 e3, P e1 → P e2 → P e3 → P (if{e1} e2 else e3)).
  Context (Pcomma : ∀ e1 e2, P e1 → P e2 → P (e1 ,, e2)).
  Context (Pcast : ∀ τ e, P e → P (cast{τ} e)).
  Context (Pinsert : ∀ r e1 e2, P e1 → P e2 → P (#[r:=e1] e2)).
  Definition expr_ind_alt : ∀ e, P e :=
    fix go e : P e :=
    match e with
    | var x => Pvar x
    | %#{Ω} ν => Pval Ω ν
    | .* e => Prtol _ (go e)
    | & e => Profl _ (go e)
    | e1 ::={_} e2 => Passign _ _ _ (go e1) (go e2)
    | call e @ es => Pcall _ es (go e) $ list_ind (Forall P)
       (Forall_nil_2 _) (λ e _, Forall_cons_2 _ _ _ (go e)) es
    | load e => Pload _ (go e)
    | abort _ => Pabort _
    | e %> rs => Peltl _ _ (go e)
    | e #> rs => Peltr _ _ (go e)
    | alloc{_} e => Palloc _ _ (go e)
    | free e => Pfree _ (go e)
    | .{op} e => Punop op _ (go e)
    | e1 .{op} e2 => Pbinop op _ _ (go e1) (go e2)
    | if{e1} e2 else e3 => Pif _ _ _ (go e1) (go e2) (go e3)
    | e1,, e2 => Pcomma _ _ (go e1) (go e2)
    | cast{τ} e => Pcast _ _ (go e)
    | #[_:=e1] e2 => Pinsert _ _ _ (go e1) (go e2)
    end.
End expr_ind.

(** We also define [size e] giving the number of nodes in an expression. This
measure can be used for well-founded induction on expressions. *)
#[global] Instance expr_size {K} : Size (expr K) :=
  fix go e : nat := let _ : Size _ := go in
  match e with
  | var _ | abort _ => 1 | %#{_} _ => 0
  | .* e | & e | cast{_} e => S (size e)
  | e1 ::={_} e2 | e1 .{_} e2 | e1,, e2 | #[_:=e1] e2 => S (size e1 + size e2)
  | call e @ es => S (size e + sum_list_with size es)
  | load e | e %> _ | e #> _ | alloc{_} e | free e | .{_} e => S (size e)
  | if{e1} e2 else e3 => S (size e1 + size e2 + size e3)
  end.
Lemma expr_wf_ind {K} (P : expr K → Prop)
  (Pind : ∀ e, (∀ e', size e' < size e → P e')%nat → P e) : ∀ e, P e.
Proof.
  assert (∀ n e, size e < n → P e)%nat as help by (induction n; auto with lia).
  intros e. apply (help (S (size e))); lia.
Qed.

#[global] Instance expr_free_vars {K} : Vars (expr K) :=
  fix go e := let _ : Vars _ := @go in
  match e with
  | var n => {[ n ]} | %#{_} _ | abort _ => ∅
  | .* e | & e | cast{_} e => vars e
  | call e @ es => vars e ∪ ⋃ (vars <$> es)
  | alloc{_} e | load e | e %> _ | e #> _ | free e | .{_} e => vars e
  | e1 ::={_} e2 | e1 .{_} e2 | e1,, e2 | #[_:=e1] e2 => vars e1 ∪ vars e2
  | if{e1} e2 else e3 => vars e1 ∪ vars e2 ∪ vars e3
  end.

Global Hint Extern 1 (vars _ = ∅) => assumption : typeclass_instances.
Global Hint Extern 100 (vars _ = ∅) =>
  apply (bool_decide_unpack _); vm_compute; exact I : typeclass_instances.

(** In order to model sequence points, we have to keep track of sets of
locations that cannot be written to or read from. We call such locations locked,
and define a type class [Locks] to collect locks in various data structures. *)
Class Locks A := locks: A → lockset.
Arguments locks {_ _} !_ / : simpl nomatch.

#[global] Instance list_locks `{Locks A} : Locks (list A) :=
  fix go (l : list A) : lockset := let _ : Locks _ := @go in
  match l with [] => ∅ | a :: l => locks a ∪ locks l end.

Lemma locks_nil `{Locks A} : locks [] = ∅.
Proof. done. Qed.
Lemma locks_app `{Locks A} (l1 l2 : list A) :
  locks (l1 ++ l2) = locks l1 ∪ locks l2.
Proof. apply set_eq. induction l1; set_solver. Qed.
Lemma locks_snoc `{Locks A} (l1 : list A) a :
  locks (l1 ++ [a]) = locks l1 ∪ locks a.
Proof. rewrite locks_app. simpl. by rewrite (right_id_L ∅ (∪)). Qed.

#[global] Instance expr_locks {K} : Locks (expr K) :=
  fix go e : lockset := let _ : Locks _ := @go in
  match e with
  | var _ | abort _ => ∅ | %#{Ω} _ => Ω
  | .* e | & e | cast{_} e => locks e
  | call e @ es => locks e ∪ ⋃ (locks <$> es)
  | alloc{_} e | load e | e %> _ | e #> _ | free e | .{_} e => locks e
  | e1 ::={_} e2 | e1 .{_} e2 | e1,, e2 | #[_:=e1] e2 => locks e1 ∪ locks e2
  | if{e1} e2 else e3 => locks e1 ∪ locks e2 ∪ locks e3
  end.
Lemma expr_locks_freeze {K} β (e : expr K) : locks (freeze β e) = locks e.
Proof.
  assert (∀ (es : list (expr K)),
    Forall (λ e, locks (freeze β e) = locks e) es →
    ⋃ (locks <$> (freeze β <$> es)) = ⋃ (locks <$> es)).
  { induction 1; set_solver. }
  induction e using @expr_ind_alt; csimpl; try set_solver; f_equal; auto.
Qed.

(** An expression is pure (or side-effect free) if it does not modify the
memory. Although pure expressions may have sequence points (namely at the
conditional and call expressions), these sequence points are not observable
because pure expressions do not allow any locations to get locked in the
first place. *)
Inductive is_pure {K} : expr K → Prop :=
  | EVar_pure x : is_pure (var x)
  | EVal_pure v : is_pure (%# v)
  | ERtoL_pure e : is_pure e → is_pure (.* e)
  | ERofL_pure e : is_pure e → is_pure (& e)
  | EEltR_pure e rs : is_pure e → is_pure (e %> rs)
  | EEltL_pure e rs : is_pure e → is_pure (e #> rs)
  | EUnOp_pure op e : is_pure e → is_pure (.{op} e)
  | EBinOp_pure op e1 e2 : is_pure e1 → is_pure e2 → is_pure (e1 .{op} e2)
  | EIf_pure e1 e2 e3 :
     is_pure e1 → is_pure e2 → is_pure e3 → is_pure (if{e1} e2 else e3)
  | EComma_pure el er : is_pure el → is_pure er → is_pure (el,, er)
  | ECast_pure τ e : is_pure e → is_pure (cast{τ} e)
  | EInsert_pure r e1 e2 : is_pure e1 → is_pure e2 → is_pure (#[r:=e1] e2).

Section is_pure_ind.
  Context {K} (fs : funset) (P : expr K → Prop).
  Context (Pvar : ∀ x, P (var x)).
  Context (Pval : ∀ v, P (%# v)).
  Context (Prtol : ∀ e, is_pure e → P e → P (.* e)).
  Context (Profl : ∀ e, is_pure e → P e → P (& e)).
  Context (Peltl : ∀ e rs, is_pure e → P e → P (e %> rs)).
  Context (Peltr : ∀ e rs, is_pure e → P e → P (e #> rs)).
  Context (Punop : ∀ op e, is_pure e → P e → P (.{op} e)).
  Context (Pbinop : ∀ op e1 e2,
    is_pure e1 → P e1 → is_pure e2 → P e2 → P (e1 .{op} e2)).
  Context (Pif : ∀ e1 e2 e3,
    is_pure e1 → P e1 → is_pure e2 → P e2 → is_pure e3 → P e3 →
    P (if{e1} e2 else e3)).
  Context (Pcomma : ∀ e1 e2,
    is_pure e1 → P e1 → is_pure e2 → P e2 → P (e1,, e2)).
  Context (Pcast : ∀ τ e, is_pure e → P e → P (cast{τ} e)).
  Context (Pinsert : ∀ r e1 e2,
     is_pure e1 → P e1 → is_pure e2 → P e2 → P (#[r:=e1] e2)).
  Definition is_pure_ind_alt: ∀ e, is_pure e → P e.
  Proof. fix H'2 2; destruct 1; eauto using Forall_impl. Qed.
End is_pure_ind.

#[global] Instance is_pure_dec {K} : ∀ e : expr K, Decision (is_pure e).
Proof.
 refine (
  fix go e :=
  match e return Decision (is_pure e) with
  | var _ => left _ | %#{Ω} _ => cast_if (decide (Ω = ∅))
  | .* e | & e | e %> _ | e #> _ | cast{_} e => cast_if (decide (is_pure e))
  | .{op} e => cast_if (decide (is_pure e))
  | e1 .{_} e2 | e1 ,, e2 | #[_:=e1] e2 =>
     cast_if_and (decide (is_pure e1)) (decide (is_pure e2))
  | if{e1} e2 else e3 => cast_if_and3 (decide (is_pure e1))
      (decide (is_pure e2)) (decide (is_pure e3))
  | _ => right _
  end);
  clear go; first [by subst; constructor | abstract by inversion 1; subst].
Defined.
Lemma is_pure_locks {K} (e : expr K) : is_pure e → locks e = ∅.
Proof.
  assert (∀ (es : list (expr K)) oi,
    Forall (λ e, oi ∉ locks e) es → oi ∉ ⋃ (locks <$> es)).
  { induction 1; set_solver. }
  intros He. apply elem_of_equiv_empty_L. intros oi.
  induction He using @is_pure_ind_alt; set_solver.
Qed.

(** The operation [e↑] increases all De Bruijn indexes of variables in [e]
by one. That means, each variable [var x] in [e] becomes [var (S x)]. *)
Reserved Notation "e ↑" (at level 20, format "e ↑").
Fixpoint expr_lift {K} (e : expr K) : expr K :=
  match e with
  | var x => var (S x)
  | %#{Ω} ν => %#{Ω} ν
  | .* e => .* (e↑)
  | & e => & (e↑)
  | e1 ::={ass} e2 => e1↑ ::={ass} e2↑
  | call e @ es => call e↑ @ expr_lift <$> es
  | abort τ => abort τ
  | load e => load (e↑)
  | e %> rs => e↑ %> rs
  | e #> rs => e↑ #> rs
  | alloc{τ} e => alloc{τ} (e↑)
  | free e => free (e↑)
  | .{op} e => .{op} e↑
  | e1 .{op} e2 => e1↑ .{op} e2↑
  | if{e1} e2 else e3 => if{e1↑} e2↑ else e3↑
  | e1,, e2 => e1↑,, e2↑
  | cast{τ} e => cast{τ} (e↑)
  | #[r:=e1] e2 => #[r:=e1↑] (e2↑)
  end
where "e ↑" := (expr_lift e) : expr_scope.

(** The predicate [is_nf e] states that [e] is in normal form and [is_redex e]
states that [e] is a head redex with respect to the semantics in the file
[smallstep]. *)
Inductive is_nf {K} : expr K → Prop :=
  | EVal_nf Ω ν : is_nf (%#{Ω} ν).
Inductive is_redex {K} : expr K → Prop :=
  | EVar_redex x : is_redex (var x)
  | ERtoL_redex e : is_nf e → is_redex (.* e)
  | ERofL_redex e : is_nf e → is_redex (& e)
  | EAssign_redex ass e1 e2 :
     is_nf e1 → is_nf e2 → is_redex (e1 ::={ass} e2)
  | ECall_redex e es : is_nf e → Forall is_nf es → is_redex (call e @ es)
  | EAbort_redex τ : is_redex (abort τ)
  | ELoad_redex e : is_nf e → is_redex (load e)
  | EEltL_redex e rs : is_nf e → is_redex (e %> rs)
  | EEltR_redex e rs : is_nf e → is_redex (e #> rs)
  | EAlloc_redex τ e : is_nf e → is_redex (alloc{τ} e)
  | EFree_redex e : is_nf e → is_redex (free e)
  | EUnOp_redex op e : is_nf e → is_redex (.{op} e)
  | EBinOp_redex op e1 e2 :
     is_nf e1 → is_nf e2 → is_redex (e1 .{op} e2)
  | EIf_redex e1 e2 e3 : is_nf e1 → is_redex (if{e1} e2 else e3)
  | EComma_redex e1 e2 : is_nf e1 → is_redex (e1,, e2)
  | ECast_redex τ e : is_nf e → is_redex (cast{τ} e)
  | EInsert_redex r e1 e2 :
     is_nf e1 → is_nf e2 → is_redex (#[r:=e1]e2).

#[global] Instance is_nf_dec {K} (e : expr K) : Decision (is_nf e).
Proof.
 refine (match e with %#{_} _ => left _ | _ => right _ end);
  try constructor; abstract (inversion 1).
Defined.
#[global] Instance is_redex_dec {K} (e : expr K) : Decision (is_redex e).
Proof.
 refine
  match e with
  | var _ | abort _ => left _
  | .* e | & e | cast{_} e | load e | e %> _ | e #> _ | alloc{_} e | free e
    | .{_} e | if{e} _ else _ | e ,, _ => cast_if (decide (is_nf e))
  | call e @ es => cast_if_and (decide (is_nf e)) (decide (Forall is_nf es))
  | e1 ::={_} e2 | e1 .{_} e2 | #[_:=e1] e2 =>
     cast_if_and (decide (is_nf e1)) (decide (is_nf e2))
  | _ => right _
  end; first [by constructor | abstract (by inversion 1)].
Defined.

Lemma is_redex_nf {K} (e : expr K) : is_redex e → is_nf e → False.
Proof. destruct 1; inversion 1. Qed.
Lemma EVal_not_redex {K} Ω (ν : lrval K) : ¬is_redex (%#{Ω} ν).
Proof. inversion 1. Qed.
Lemma EVals_nf {K} Ωs (vs : list (val K)) : Forall is_nf (#{Ωs}* vs).
Proof. revert vs. induction Ωs; intros [|??]; repeat constructor; auto. Qed.
Lemma EVals_nf_alt {K} es Ωs (vs : list (val K)) :
  es = #{Ωs}* vs → Forall is_nf es.
Proof. intros ->. by apply EVals_nf. Qed.

Definition maybe_ECall_redex {K} (e : expr K) :
    option (lockset * funname * list (type K) * type K *
            list lockset * list (val K)) :=
  '(e,es) ← maybe2 ECall e;
  '(Ω,p) ← maybe2 (λ Ω p, %{Ω} p) e;
  '(f,τs,τ) ← maybe3 FunPtr p;
  vΩs ← mapM (maybe2 (λ Ω v, #{Ω} v)) es;
  Some (Ω, f, τs, τ, vΩs.*1, vΩs.*2).

Lemma maybe_EAlloc_Some {K} (e : expr K) τ e' :
  maybe2 EAlloc e = Some (τ,e') ↔ e = alloc{τ} e'.
Proof. split. by destruct e; intros; simplify_equality'. by intros ->. Qed.
Lemma maybe_ECall_Some {K} (e : expr K) e' es :
  maybe2 ECall e = Some (e', es) ↔ e = call e' @ es.
Proof. split. by destruct e; intros; simplify_equality'. by intros ->. Qed.
Lemma maybe_ECall_redex_Some_2 {K} Ω f τs τ Ωs (vs : list (val K)) :
  length Ωs = length vs →
  maybe_ECall_redex (call %{Ω} (FunPtr f τs τ) @ #{Ωs}* vs)
  = Some (Ω, f, τs, τ, Ωs, vs).
Proof.
  intros; unfold maybe_ECall_redex; csimpl.
  rewrite zip_with_zip, mapM_fmap_Some by (by intros []); csimpl.
  by rewrite fst_zip, snd_zip by lia.
Qed.
Lemma maybe_ECall_redex_Some {K} (e : expr K) Ω f τs τ Ωs vs :
  maybe_ECall_redex e = Some (Ω, f, τs, τ, Ωs, vs) ↔
    e = call %{Ω} (FunPtr f τs τ) @ #{Ωs}* vs ∧ length Ωs = length vs.
Proof.
  assert (∀ (es : list (expr K)) Ωvs,
    mapM (maybe2 (λ Ω v, #{Ω} v)) es = Some Ωvs → es = #{Ωvs.*1}* (Ωvs.*2))%E.
  { intros es Ωvs. rewrite mapM_Some. induction 1 as [|e']; f_equal'; eauto.
    by destruct e'; repeat (case_match || simplify_option_eq). }
  split; [|intros [-> ?]; eauto using maybe_ECall_redex_Some_2].
  unfold maybe_ECall_redex; csimpl; intros.
  destruct (maybe2 ECall e) as [[e' es]|] eqn:?;
    repeat (case_match || simplify_option_eq).
  rewrite !fmap_length; auto with f_equal.
Qed.

(** * Contexts with one hole *)
(** We define singular expression contexts [ectx_item], and then full expression
(evaluation) contexts [ectx] are lists of expression contexts. These expression
contexts allow us to enforce an evaluation strategy. In particular, for the
conditional we merely allow a hole for the first branch. *)
Inductive ectx_item (K : iType) : iType :=
  | CRtoL : ectx_item K
  | CLtoR : ectx_item K
  | CAssignL : assign → expr K → ectx_item K
  | CAssignR : assign → expr K → ectx_item K
  | CCallL : list (expr K) → ectx_item K
  | CCallR : expr K → list (expr K) → list (expr K) → ectx_item K
  | CLoad : ectx_item K
  | CEltL : ref_seg K → ectx_item K
  | CEltR : ref_seg K → ectx_item K
  | CAlloc : type K → ectx_item K
  | CFree : ectx_item K
  | CUnOp : unop → ectx_item K
  | CBinOpL : binop → expr K → ectx_item K
  | CBinOpR : binop → expr K → ectx_item K
  | CIf : expr K → expr K → ectx_item K
  | CComma : expr K → ectx_item K
  | CCast : type K → ectx_item K
  | CInsertL : ref K → expr K → ectx_item K
  | CInsertR : ref K → expr K → ectx_item K.
Notation ectx K := (list (ectx_item K)).

Bind Scope expr_scope with ectx_item.

Arguments CRtoL {_}.
Arguments CLtoR {_}.
Arguments CAssignL {_} _ _.
Arguments CAssignR {_} _ _.
Arguments CCallL {_} _.
Arguments CCallR {_} _ _ _.
Arguments CLoad {_}.
Arguments CEltL {_} _.
Arguments CEltR {_} _.
Arguments CAlloc {_} _.
Arguments CFree {_}.
Arguments CUnOp {_} _.
Arguments CBinOpL {_} _ _.
Arguments CBinOpR {_}_ _.
Arguments CIf {_} _ _.
Arguments CComma {_} _.
Arguments CCast {_} _.
Arguments CInsertL {_} _ _.
Arguments CInsertR {_} _ _.

Notation ".* □" := CRtoL (at level 24, format ".*  □") : expr_scope.
Notation "& □" := CLtoR (at level 24, format "&  □") : expr_scope.
Notation "□ ::={ ass } e2" := (CAssignL ass e2)
  (at level 54, format "□  ::={ ass }  e2") : expr_scope.
Notation "e1 ::={ ass } □" := (CAssignR ass e1)
  (at level 54, format "e1  ::={ ass }  □") : expr_scope.
Notation "'call' □ @ es" := (CCallL es)
  (at level 10, es at level 66) : expr_scope.
Notation "'call' f @ es1 □ es2" := (CCallR f es1 es2)
  (at level 10, es1 at level 66, es2 at level 66) : expr_scope.
Notation "'load' □" := CLoad (at level 10, format "load  □") : expr_scope.
Notation "□ %> rs" := (CEltL rs)
  (at level 22, format "□ %> rs") : expr_scope.
Notation "□ #> rs" := (CEltR rs)
  (at level 22, format "□ #> rs") : expr_scope.
Notation "alloc{ τ } □" := (CAlloc τ)
  (at level 10, format "alloc{ τ }  □") : expr_scope.
Notation "'free' □" := CFree (at level 10, format "free  □") : expr_scope.
Notation ".{ op } □" := (CUnOp op)
  (at level 35, format ".{ op } □") : expr_scope.
Notation "□ .{ op } e2" := (CBinOpL op e2)
  (at level 50, format "□  .{ op }  e2") : expr_scope.
Notation "e1 .{ op } □" := (CBinOpR op e1)
  (at level 50, format "e1  .{ op }  □") : expr_scope.
Notation "'if{' □ } e2 'else' e3" := (CIf e2 e3)
  (at level 56, format "'if{'  □  }  e2  'else'  e3") : expr_scope.
Notation "□ ,, e2" := (CComma e2)
  (at level 58, format "□  ,,  e2") : expr_scope.
Notation "'cast{' τ } □" := (CCast τ)
  (at level 10, format "'cast{' τ }  □") : expr_scope.
Notation "#[ r := □ ] e2" := (CInsertL r e2)
  (at level 10, format "#[ r := □ ]  e2") : expr_scope.
Notation "#[ r := e1 ] □" := (CInsertR r e1)
  (at level 10, format "#[ r := e1 ]  □") : expr_scope.

#[global] Instance ectx_item_dec `{EqDecision K}: EqDecision (ectx_item K).
Proof. solve_decision. Defined.

(** Substitution is defined in a straightforward way. Using the type class
instances in the file [contexts], it is lifted to full expression contexts. *)
#[global] Instance ectx_item_subst {K} :
    Subst (ectx_item K) (expr K) (expr K) := λ Ei e,
  match Ei with
  | .* □ => .* e
  | & □ => & e
  | □ ::={ass} er => e ::={ass} er | el ::={ass} □ => el ::={ass} e
  | call □ @ es => call e @ es
  | call e' @ es1 □ es2 => call e' @ (reverse es1 ++ e :: es2)
  | load □ => load e
  | □ %> rs => e %> rs
  | □ #> rs => e #> rs
  | alloc{τ} □ => alloc{τ} e
  | free □ => free e
  | .{op} □ => .{op} e
  | □ .{op} e2 => e .{op} e2 | e1 .{op} □ => e1 .{op} e
  | □,, e2 => e ,, e2
  | if{□} e2 else e3 => if{e} e2 else e3
  | cast{τ} □ => cast{τ} e
  | #[r:=□] e2 => #[r:=e] e2 | #[r:=e1] □ => #[r:=e1] e
  end.
#[global] Instance: `{DestructSubst (@ectx_item_subst K)} := {}.

#[global] Instance: `{∀ Ei : ectx_item K, Inj (=) (=) (subst Ei)}.
Proof. by destruct Ei; intros ???; simplify_list_eq. Qed.
Lemma is_nf_ectx_item {K} (Ei : ectx_item K) e : ¬is_nf (subst Ei e).
Proof. destruct Ei; inversion 1. Qed.
Lemma is_nf_ectx {K} (E : ectx K) e : is_nf (subst E e) → E = [].
Proof.
  destruct E using rev_ind; auto.
  rewrite subst_snoc. intros; edestruct @is_nf_ectx_item; eauto.
Qed.
Lemma is_nf_redex_ectx {K} (E : ectx K) e : is_redex e → ¬is_nf (subst E e).
Proof.
  intros ? HEe. rewrite (is_nf_ectx E e) in HEe by done; simpl in HEe.
  eauto using is_redex_nf.
Qed.
Lemma is_redex_ectx_item {K} (Ei : ectx_item K) e :
  is_redex (subst Ei e) → is_nf e.
Proof. destruct Ei; inversion 1; decompose_Forall_hyps; auto. Qed.
Lemma is_redex_ectx {K} (E : ectx K) e :
  is_redex (subst E e) → (E = [] ∧ is_redex e) ∨ (∃ Ei, E = [Ei] ∧ is_nf e).
Proof.
  destruct E as [|Ei E _] using rev_ind; [eauto|]; rewrite subst_snoc; intros.
  feed pose proof (is_redex_ectx_item Ei (subst E e)); auto.
  feed pose proof (is_nf_ectx E e); subst; simpl in *; eauto.
Qed.

#[global] Instance ectx_locks {K} : Locks (ectx_item K) := λ Ei,
  match Ei with
  | .* □ | & □ | cast{_} □ => ∅
  | □ ::={_} e | e ::={_} □ => locks e
  | call □ @ es => ⋃ (locks <$> es)
  | call e @ es1 □ es2 => locks e ∪ ⋃ (locks <$> es1) ∪ ⋃ (locks <$> es2)
  | load □ | □ %> _ | □ #> _ | alloc{_} □ | free □ | .{_} □ => ∅
  | □ .{_} e | e .{_} □ | □,, e | #[_:=□] e | #[_:=e] □ => locks e
  | if{□} e2 else e3 => locks e2 ∪ locks e3
  end.

Lemma ectx_item_is_pure {K} (Ei : ectx_item K) (e : expr K) :
  is_pure (subst Ei e) → is_pure e.
Proof. destruct Ei; simpl; inversion_clear 1; decompose_Forall_hyps; eauto. Qed.
Lemma ectx_is_pure {K} (E : ectx K) e : is_pure (subst E e) → is_pure e.
Proof.
  induction E using rev_ind; rewrite ?subst_snoc; eauto using ectx_item_is_pure.
Qed.
Lemma ectx_item_subst_is_pure {K} (Ei : ectx_item K) (e1 e2 : expr K) :
  is_pure e2 → is_pure (subst Ei e1) → is_pure (subst Ei e2).
Proof.
  destruct Ei; simpl; inversion_clear 2; constructor; decompose_Forall; eauto.
Qed.
Lemma ectx_subst_is_pure {K} (E : ectx K) (e1 e2 : expr K) :
  is_pure e2 → is_pure (subst E e1) → is_pure (subst E e2).
Proof.
  induction E using rev_ind; rewrite ?subst_snoc;
    eauto using ectx_item_subst_is_pure, ectx_item_is_pure.
Qed.
Lemma ectx_item_subst_locks {K} (Ei : ectx_item K) e :
  locks (subst Ei e) = locks Ei ∪ locks e.
Proof.
  apply set_eq. intro. destruct Ei; simpl; try set_solver.
  rewrite fmap_app, fmap_reverse; csimpl.
  rewrite union_list_app_L, union_list_cons, union_list_reverse_L.
  set_solver.
Qed.
Lemma ectx_subst_locks {K} (E : ectx K) e :
  locks (subst E e) = locks E ∪ locks e.
Proof.
  apply set_eq. intros. revert e. induction E as [|Ei E IH]; simpl.
  * set_solver.
  * intros. rewrite IH, ectx_item_subst_locks. set_solver.
Qed.

#[global] Instance ectx_item_size {K} : Size (ectx_item K) := λ Ei,
  match Ei with
  | .* □ | & □ | load □ | □ %> _ | □ #> _ | alloc{_} □
    | free □ | .{_} □ | cast{_} □ => 1
  | □ ::={_} e | e ::={_} □ | □ .{_} e | e .{_} □
    | □,, e | #[_:=□] e | #[_:=e] □  => S (size e)
  | call □ @ es => S (sum_list_with size es)
  | call e @ es1 □ es2 =>
     S (size e + sum_list_with size es1 + sum_list_with size es2)
  | if{□} e2 else e3 => S (size e2 + size e3)
  end.
Lemma ectx_item_subst_size {K} (Ei : ectx_item K) e :
  size (subst Ei e) = (size Ei + size e)%nat.
Proof.
  destruct Ei; simpl; auto with lia.
  rewrite sum_list_with_app, sum_list_with_reverse; simpl; lia.
Qed.
Lemma ectx_subst_size {K} (E : ectx K) e :
  size (subst E e) = (sum_list_with size E + size e)%nat.
Proof.
  revert e. induction E as [|Ei E IH]; intros e; simpl; [done|].
  rewrite IH, ectx_item_subst_size; lia.
Qed.

(** The induction principle [ectx_expr_ind] is used to perform simultaneous
induction on an expression [e] and context [E]. Although a similar result can
be obtained by generalizing over [E] before doing the induction on [e], this
induction principle is more useful together with automation. Automation now
does not have to instantiate the induction hypothesis with the appropriate
context. *)
Section ectx_expr_ind.
  Context {K} (P : ectx K → expr K → Prop).
  Context (Pvar : ∀ E x, P E (var x)).
  Context (Pval : ∀ E Ω ν, P E (%#{Ω} ν)).
  Context (Prtol : ∀ E e, P ((.* □) :: E) e → P E (.* e)).
  Context (Profl : ∀ E e, P ((& □) :: E) e → P E (& e)).
  Context (Passign : ∀ E ass e1 e2,
    P ((□ ::={ass} e2) :: E) e1 → P ((e1 ::={ass} □) :: E) e2 →
    P E (e1 ::={ass} e2)).
  Context (Pcall : ∀ E e es,
    P ((call □ @ es) :: E) e →
    zipped_Forall (λ esl esr, P ((call e @ esl □ esr) :: E)) [] es →
    P E (call e @ es)).
  Context (Pabort : ∀ E τ, P E (abort τ)).
  Context (Pload : ∀ E e, P ((load □) :: E) e → P E (load e)).
  Context (Peltl : ∀ E e rs, P ((□ %> rs) :: E) e → P E (e %> rs)).
  Context (Peltr : ∀ E e rs, P ((□ #> rs) :: E) e → P E (e #> rs)).
  Context (Palloc : ∀ E τ e, P ((alloc{τ} □) :: E) e → P E (alloc{τ} e)).
  Context (Pfree : ∀ E e, P ((free □) :: E) e → P E (free e)).
  Context (Punop : ∀ E op e, P ((.{op} □) :: E) e → P E (.{op} e)).
  Context (Pbinop : ∀ E op e1 e2,
    P ((□ .{op} e2) :: E) e1 → P ((e1 .{op} □) :: E) e2 →
    P E (e1 .{op} e2)).
  Context (Pif : ∀ E e1 e2 e3,
    P ((if{□} e2 else e3) :: E) e1 → P E (if{e1} e2 else e3)).
  Context (Pcomma : ∀ E e1 e2, P ((□,, e2) :: E) e1 → P E (e1,, e2)).
  Context (Pcast : ∀ E τ e, P ((cast{τ} □) :: E) e → P E (cast{τ} e)).
  Context (Pinsert : ∀ E r e1 e2,
    P ((#[r:=□] e2) :: E) e1 → P ((#[r:=e1] □) :: E) e2 → P E (#[r:=e1] e2)).

  Definition ectx_expr_ind : ∀ E e, P E e :=
    fix go E e : P E e :=
    match e with
    | var x => Pvar _ x
    | %#{_} ν => Pval _ _ ν
    | .* e => Prtol _ _ (go _ e)
    | & e => Profl _ _ (go _ e)
    | e1 ::={_} e2 => Passign _ _ _ _ (go _ e1) (go _ e2)
    | call e @ es => Pcall E e es (go _ e)
       (zipped_list_ind _ zipped_Forall_nil
         (λ _ _ e, @zipped_Forall_cons _ (λ _ _, P _) _ _ _ (go _ e)) [] es)
    | abort _ => Pabort _ _
    | load e => Pload _ _ (go _ e)
    | e %> rs => Peltl _ _ _ (go _ e)
    | e #> rs => Peltr _ _ _ (go _ e)
    | alloc{_} e => Palloc _ _ _ (go _ e)
    | free e => Pfree _ _ (go _ e)
    | .{_} e => Punop _ _ _ (go _ e)
    | e1 .{_} e2 => Pbinop _ _ _ _ (go _ e1) (go _ e2)
    | if{e1} _ else _ => Pif _ _ _ _ (go _ e1)
    | e1,, _ => Pcomma _ _ _ (go _ e1)
    | cast{_} e => Pcast _ _ _ (go _ e)
    | #[_:=e1] e2 => Pinsert _ _ _ _ (go _ e1) (go _ e2)
    end.
End ectx_expr_ind.

Ltac ectx_expr_ind E e :=
  repeat match goal with
  | H : context [ E ] |- _ => revert H | H : context [ e ] |- _ => revert H
  end; revert E e;
  match goal with |- ∀ E e, @?P E e => apply (ectx_expr_ind P) end.

(** * Contexts with multiple holes *)
(** We define singular expression contexts indexed by the number of holes. These
contexts are particularly useful to prove some of the Hoare rules in a more
generic way. *)
Inductive ectx_full (K : iType) : nat → iType :=
  | DCVar : nat → ectx_full K 0
  | DCVal : lockset → lrval K → ectx_full K 0
  | DCRtoL : ectx_full K 1
  | DCRofL : ectx_full K 1
  | DCAssign : assign → ectx_full K 2
  | DCCall {n} : ectx_full K (S n)
  | DCAbort : type K → ectx_full K 0
  | DCLoad : ectx_full K 1
  | DCEltL : ref_seg K → ectx_full K 1
  | DCEltR : ref_seg K → ectx_full K 1
  | DCAlloc : type K → ectx_full K 1
  | DCFree : ectx_full K 1
  | DCUnOp : unop → ectx_full K 1
  | DCBinOp : binop → ectx_full K 2
  | DCIf : expr K → expr K → ectx_full K 1
  | DCComma : expr K → ectx_full K 1
  | DCCast : type K → ectx_full K 1
  | DCInsert : ref K → ectx_full K 2.

Arguments DCVar {_} _.
Arguments DCVal {_} _ _.
Arguments DCRtoL {_}.
Arguments DCRofL {_}.
Arguments DCAssign {_} _.
Arguments DCCall {_} _.
Arguments DCAbort {_} _.
Arguments DCLoad {_}.
Arguments DCEltL {_} _.
Arguments DCEltR {_} _.
Arguments DCAlloc {_} _.
Arguments DCFree {_}.
Arguments DCUnOp {_} _.
Arguments DCBinOp {_} _.
Arguments DCIf {_}_ _.
Arguments DCComma {_} _.
Arguments DCCast {_} _.
Arguments DCInsert {_} _.

#[global] Instance ectx_full_subst {K} :
    DepSubst (ectx_full K) (vec (expr K)) (expr K) := λ _ E,
  match E with
  | DCVar x => λ _, var x
  | DCVal Ω ν => λ _, %#{Ω} ν
  | DCRtoL => λ es, .* (es !!! 0%fin)
  | DCRofL => λ es, & (es !!! 0%fin)
  | DCAssign ass => λ es, es !!! 0%fin ::={ass} es !!! 1%fin
  | DCCall _ => λ es, call (es !!! 0%fin) @ tail es
  | DCAbort τ => λ _, abort τ
  | DCLoad => λ es, load (es !!! 0%fin)
  | DCEltL rs => λ es, es !!! 0%fin %> rs
  | DCEltR rs => λ es, es !!! 0%fin #> rs
  | DCAlloc τ => λ es, alloc{τ} (es !!! 0%fin)
  | DCFree => λ es, free (es !!! 0%fin)
  | DCUnOp op => λ es, .{op} es !!! 0%fin
  | DCBinOp op => λ es, es !!! 0%fin .{op} es !!! 1%fin
  | DCIf e2 e3 => λ es, if{es !!! 0%fin} e2 else e3
  | DCComma e2 => λ es, es !!! 0%fin,, e2
  | DCCast τ => λ es, cast{τ} (es !!! 0%fin)
  | DCInsert r => λ es, #[r:=es !!! 0%fin] (es !!! 1%fin)
  end.
#[global] Instance ectx_full_locks {K n} : Locks (ectx_full K n) := λ E,
  match E with
  | DCVal Ω _ => Ω
  | DCIf e1 e2 => locks e1 ∪ locks e2
  | DCComma e => locks e
  | _ => ∅
  end.

Lemma ectx_full_subst_inj {K n} (E : ectx_full K n) es1 es2 :
  depsubst E es1 = depsubst E es2 → es1 = es2.
Proof.
  destruct E; inv_all_vec_fin; simpl; intros; simplify_equality;
    f_equal'; auto using vec_to_list_inj2.
Qed.
Lemma ectx_full_subst_locks {K n} (E : ectx_full K n) (es : vec (expr K) n) :
  locks (depsubst E es) = locks E ∪ ⋃ (locks <$> vec_to_list es).
Proof.
  apply set_eq. intro. destruct E; inv_all_vec_fin; set_solver.
Qed.

(** Given expressions [es] for the holes of the context [E], the function
[ectx_full_to_item E es i] yields a context with exactly one hole for the
[i]th value. The [i]th value in [es] is ignored. *)
Definition ectx_full_to_item {K n} (E : ectx_full K n)
    (es : vec (expr K) n) (i : fin n) : ectx_item K :=
  match E in ectx_full _ n return fin n → vec (expr K) n → ectx_item K with
  | DCVar _  | DCVal _ _ | DCAbort _ => fin_0_inv _
  | DCRtoL => fin_S_inv _ (λ _, .* □) $ fin_0_inv _
  | DCRofL => fin_S_inv _ (λ _, & □) $ fin_0_inv _
  | DCAssign ass =>
     fin_S_inv _ (λ es, □ ::={ass} es !!! 1%fin) $
     fin_S_inv _ (λ es, es !!! 0%fin ::={ass} □) $ fin_0_inv _
  | DCCall _ => fin_S_inv _ (λ _, call □ @ (tail es)) $ λ i (es: vec _ _),
     (call (es !!! 0%fin) @ reverse (take i (tail es)) □ drop (FS i) (tail es))
  | DCLoad => fin_S_inv _ (λ _, load □) $ fin_0_inv _ 
  | DCEltL rs => fin_S_inv _ (λ _, □ %> rs) $ fin_0_inv _
  | DCEltR rs => fin_S_inv _ (λ _, □ #> rs) $ fin_0_inv _
  | DCAlloc τ => fin_S_inv _ (λ _, alloc{τ} □) $ fin_0_inv _
  | DCFree => fin_S_inv _ (λ _, free □) $ fin_0_inv _
  | DCUnOp op => fin_S_inv _ (λ _, .{op} □) $ fin_0_inv _
  | DCBinOp op =>
     fin_S_inv _ (λ es, □ .{op} es !!! 1%fin) $
     fin_S_inv _ (λ es, es !!! 0%fin .{op} □) $ fin_0_inv _
  | DCIf e2 e3 => fin_S_inv _ (λ _, if{□} e2 else e3) $ fin_0_inv _
  | DCComma e2 => fin_S_inv _ (λ _, □,, e2) $ fin_0_inv _
  | DCCast τ => fin_S_inv _ (λ _, cast{τ} □) $ fin_0_inv _
  | DCInsert r =>
     fin_S_inv _ (λ es, #[r:=□] (es !!! 1%fin)) $
     fin_S_inv _ (λ es, #[r:=es !!! 0%fin] □) $ fin_0_inv _
  end i es.

Lemma ectx_full_to_item_insert {K n} (E : ectx_full K n) es i e :
  ectx_full_to_item E (vinsert i e es) i = ectx_full_to_item E es i.
Proof.
  destruct E; inv_all_vec_fin; simpl; try reflexivity.
  rewrite !vec_to_list_insert, take_insert, drop_insert_gt; auto with arith.
Qed.
Lemma ectx_full_to_item_correct {K n} (E : ectx_full K n) es i :
  depsubst E es = subst (ectx_full_to_item E es i) (es !!! i).
Proof.
  destruct E; inv_all_vec_fin; simpl; try reflexivity.
  by rewrite reverse_involutive, <-vec_to_list_take_drop_lookup.
Qed.
Lemma ectx_full_to_item_correct_alt {K n} (E : ectx_full K n) es i e :
  depsubst E (vinsert i e es) = subst (ectx_full_to_item E es i) e.
Proof.
  rewrite (ectx_full_to_item_correct _ _ i).
  by rewrite vlookup_insert, ectx_full_to_item_insert.
Qed.
Lemma ectx_full_item_subst {K n} (E : ectx_full K n) (es : vec _ n)
    (Ei : ectx_item K) (e : expr K) :
  depsubst E es = subst Ei e →
    ∃ i, e = es !!! i ∧ Ei = ectx_full_to_item E es i.
Proof.
  intros H. destruct E, Ei; simpl; simplify_equality'; eauto.
  inv_vec es; simpl; intros e' es ?.
  edestruct (vec_to_list_lookup_middle es) as (i&H1&?&H2); eauto.
  exists (FS i); simplify_equality'. by rewrite <-H1, reverse_involutive.
Qed.
Lemma expr_vec_values {K n} (es : vec (expr K) n) :
  (∃ Ωs νs, es = vzip_with EVal Ωs νs)%E ∨ (∃ i, ¬is_nf (es !!! i)).
Proof.
  destruct (Forall_Exists_dec _ _ (λ e, decide (is_nf e)) es) as [Hes|Hes].
  * left; induction es as [|e ? es IH]; simpl in *; [by eexists [#],[#]|].
    inversion Hes as [|?? [Ω ν]]; destruct IH as (Ωs&νs&->); auto; subst.
    by exists (Ω ::: Ωs), (ν ::: νs).
  * rewrite Exists_vlookup in Hes; eauto.
Qed.
Lemma is_redex_ectx_full {K n} (E : ectx_full K n) (es : vec _ n) :
  is_redex (depsubst E es) → Forall is_nf es.
Proof.
  destruct E; inversion_clear 1; inv_all_vec_fin; repeat constructor; auto.
Qed.
Lemma ectx_full_to_item_locks {K n} (E : ectx_full K n) (es : vec _ n) i :
  locks (ectx_full_to_item E es i) =
    locks E ∪ ⋃ (locks <$> delete (fin_to_nat i) (vec_to_list es)).
Proof.
  apply set_eq. intros b.
  destruct E; inv_all_vec_fin; simpl; try set_solver.
  rewrite fmap_reverse, union_list_reverse.
  rewrite delete_take_drop, fmap_app, union_list_app. set_solver.
Qed.

(** The function [expr_redexes e] computes the set of redexes contained in an
expression [e]. Here, redexes are pairs [(E', e')] where [E'] is an expression
evaluation context, and [e'] an expression with [is_redex e']. *)
Section expr_split.
  Context {K : iType}.

  Definition expr_redexes_go: ectx K → expr K → listset (ectx K * expr K) :=
    fix go E e {struct e} :=
    if decide (is_redex e) then {[ (E, e) ]} else
    match e with
    | var _ | abort _ => ∅ (* impossible *)
    | %#{_} _ => ∅
    | .* e => go (.* □ :: E) e
    | & e => go (& □ :: E) e
    | e1 ::={ass} e2 => go (□ ::={ass} e2 :: E) e1 ∪ go (e1 ::={ass} □ :: E) e2
    | call e @ es =>
       go ((call □ @ es) :: E) e ∪
       ⋃ zipped_map (λ esl esr, go ((call e @ esl □ esr) :: E)) [] es
    | load e => go (load □ :: E) e
    | e %> rs => go (□ %> rs :: E) e
    | e #> rs => go (□ #> rs :: E) e
    | alloc{τ} e => go (alloc{τ} □ :: E) e
    | free e => go (free □ :: E) e
    | .{op} e => go (.{op} □ :: E) e
    | e1 .{op} e2 => go (□ .{op} e2 :: E) e1 ∪ go (e1 .{op} □ :: E) e2
    | if{e1} e2 else e3 => go ((if{□} e2 else e3) :: E) e1
    | e1 ,, e2 => go ((□,, e2) :: E) e1
    | cast{τ} e => go ((cast{τ} □) :: E) e
    | #[r:=e1] e2 => go (#[r:=□] e2 :: E) e1 ∪ go (#[r:=e1] □ :: E) e2
    end.
  Definition expr_redexes : expr K → listset (ectx K * expr K) :=
    expr_redexes_go [].

  Lemma expr_redexes_go_is_redex E e E' e' :
    (E', e') ∈ expr_redexes_go E e → is_redex e'.
  Proof.
    assert (∀ (f : list _ → list _ → expr K → listset (ectx K * expr K)) es,
      (E', e') ∈ ⋃ zipped_map f [] es →
      zipped_Forall (λ esl esr e, (E', e') ∈ f esl esr e → is_redex e') [] es →
      is_redex e').
    { intros f es Hes Hforall.
      rewrite elem_of_union_list in Hes. destruct Hes as (rs&Hes&?).
      rewrite elem_of_zipped_map in Hes. destruct Hes as (?&?&?&?&?); subst.
      apply zipped_Forall_app in Hforall. inversion Hforall; subst. auto. }
    ectx_expr_ind E e;
     simpl; intros; repeat case_decide; set_solver by (eauto; try constructor).
  Qed.
  Lemma expr_redexes_go_sound E e E' e' :
    (E', e') ∈ expr_redexes_go E e → subst E e = subst E' e'.
  Proof.
    assert (∀ g (f : list _ → list _ → expr K → listset (ectx K * expr K))
        (E : ectx K) es,
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
     simpl; intros; repeat case_decide; set_solver by eauto.
  Qed.
  Lemma expr_redexes_go_complete E' E e :
    is_redex e → (E ++ E', e) ∈ expr_redexes_go E' (subst E e).
  Proof.
    intros. revert E'. induction E as [|Ei E IH] using rev_ind; simpl.
    { intros. unfold expr_redexes_go. destruct e; case_decide; set_solver. }
    intros E'. assert (¬is_redex (subst (E ++ [Ei]) e)) as Hredex.
    { intro. destruct (is_redex_ectx (E ++ [Ei]) e) as [[??]|(?&?&?)]; auto.
      * discriminate_list_equality.
      * eauto using is_redex_nf. }
    rewrite subst_snoc in Hredex |- *. rewrite <-(assoc_L (++)).
    destruct Ei; simpl; case_decide; try set_solver.
    rewrite elem_of_union, elem_of_union_list.
    right; eexists (expr_redexes_go _ _).
    rewrite elem_of_zipped_map. split; [|eauto]. eexists (reverse _), _, _.
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
  Lemma expr_redexes_go_is_nf E e : expr_redexes_go E e ≡ ∅ → is_nf e.
  Proof.
    assert (∀ (f : list _ → list _ → expr K →
        listset (ectx K * expr K)) es1 es2,
      (⋃ (zipped_map f es1 es2)) ≡ ∅ →
      zipped_Forall (λ esl esr e, (f esl esr e ≡ ∅) → is_nf e) es1 es2 →
      Forall is_nf es2).
    { intros ???. rewrite empty_union_list.
      induction 2; decompose_Forall_hyps; auto. }
    ectx_expr_ind E e;
      simpl; intros; repeat case_decide; try set_solver;
      match goal with
      | _ => constructor
      | H : ¬is_redex _ |- _ => destruct H; constructor
      end; try set_solver.
  Qed.
  Lemma expr_redexes_is_nf e : expr_redexes e ≡ ∅ → is_nf e.
  Proof. apply expr_redexes_go_is_nf. Qed.
End expr_split.

Lemma is_nf_or_redex `{EqDecision K} e :
  is_nf e ∨ ∃ (E' : ectx K) e', is_redex e' ∧ e = subst E' e'.
Proof.
  destruct (set_choose_or_empty (expr_redexes e)) as [[[E' e'] ?]|?].
  * right. exists E', e'. split.
    + by apply expr_redexes_is_redex with e E'. 
    + by apply expr_redexes_correct.
  * left. by apply expr_redexes_is_nf.
Qed.
Lemma is_nf_is_redex `{EqDecision K} e :
  ¬is_nf e → ∃ (E' : ectx K) e', is_redex e' ∧ e = subst E' e'.
Proof. intros. by destruct (is_nf_or_redex e). Qed.
