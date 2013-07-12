(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** The small step reduction (as defined in the file [smallstep]) traverses
through the program in small steps by moving the focus on the substatement
that is being executed. Uses of non-local control ([goto] and [return]) are
performed in small steps rather than in big steps as well. *)

(** In order to model the concept of focusing on the substatement that is being
executed, this file defines program contexts as an extension of Huet's zipper
data structure. Program contexts extend the zipper data structure by annotating
each block scope variable with its associated memory index, and they furthermore
contain the full call stack of the program. Program contexts can also be seen
as a generalization of continuations (as for example being used in CompCert).
However, there are some notable differences.

- Program contexts implicitly contain the stack, whereas a continuation
  semantics typically stores the stack separately.
- Program contexts also contain the part of the program that has been
  executed, whereas continuations only contain the part that remains to be done.
- Since the complete program is preserved, looping constructs (e.g. while and
  for) do not have to duplicate code.

The fact that program contexts do not throw away the parts of the statement
that have been executed is essential for our treatment of goto. Upon an
invocation of a goto, the semantics traverses through the program context until
the corresponding label has been found. During this traversal it passes all
block scope variables that went out of scope, allowing it to perform required
allocations and deallocations in a natural way. Hence, the point of this
traversal is not so much to search for the label, but much more to incrementally
calculate the required allocations and deallocations. *)

(** In a continuation semantics, upon the use of a goto, one typically computes,
or looks up, the statement and continuation corresponding to the target label.
However, it is not very natural to reconstruct the required allocations and
deallocations from the current and target continuations. *)

Require Import nmap mapset.
Require Export expressions.

(** * Labels and gotos *)
(** We use the type [N] of binary natural numbers for labels, and the
implementation [Nmap] for efficient finite sets, and finite maps indexed by
labels. We define type classes [Gotos] and [Labels] to collect the labels of
gotos respectively the labels of labeled statements. *)
Definition label := N.
Definition labelmap := Nmap.
Notation labelset := (mapset labelmap).

Instance label_dec: ∀ i1 i2 : label, Decision (i1 = i2) := decide_rel (=).
Instance label_fresh_`{FinCollection label C} : Fresh label C := _.
Instance label_fresh_spec `{FinCollection label C} : FreshSpec label C := _.
Instance label_inhabited: Inhabited label := populate 0%N.

Instance labelmap_dec {A} `{∀ a1 a2 : A, Decision (a1 = a2)} :
  ∀ m1 m2 : labelmap A, Decision (m1 = m2) := decide_rel (=).
Instance labelmap_empty {A} : Empty (labelmap A) := @empty (Nmap A) _.
Instance labelmap_lookup {A} : Lookup label A (labelmap A) :=
  @lookup _ _ (Nmap A) _.
Instance labelmap_partial_alter {A} : PartialAlter label A (labelmap A) :=
  @partial_alter _ _ (Nmap A) _.
Instance labelmap_to_list {A} : FinMapToList label A (labelmap A) :=
  @map_to_list _ _ (Nmap A) _.
Instance labelmap_merge: Merge labelmap := @merge Nmap _.
Instance labelmap_fmap: FMap labelmap := λ A B f, @fmap Nmap _ _ f _.
Instance: FinMap label labelmap := _.

Instance labelmap_dom {A} : Dom (labelmap A) labelset := mapset_dom.
Instance: FinMapDom label labelmap labelset := mapset_dom_spec.

Typeclasses Opaque label labelmap.

Class Gotos A := gotos: A → labelset.
Arguments gotos {_ _} !_ / : simpl nomatch.
Class Labels A := labels: A → labelset.
Arguments labels {_ _} !_ / : simpl nomatch.

(** We lift instances of the above type classes to lists. *)
Instance list_gotos `{Gotos A} : Gotos (list A) :=
  fix go (l : list A) : labelset :=
  let _ : Gotos _ := @go in
  match l with
  | [] => ∅
  | a :: l => gotos a ∪ gotos l
  end.
Instance list_labels `{Labels A} : Labels (list A) :=
  fix go (l : list A) : labelset :=
  let _ : Labels _ := @go in
  match l with
  | [] => ∅
  | a :: l => labels a ∪ labels l
  end.

(** * Statements *)
(** The construct [SDo e] executes the expression [e] and ignores the result.
The construct [SBlock c s] opens a new scope with one variable, where [c]
indicates whether that variable is read only or not. Since we use De
Bruijn indexes for variables, it does not contain the name of the variable. *)
Inductive stmt : Type :=
  | SDo : expr → stmt
  | SSkip : stmt
  | SGoto : label → stmt
  | SReturn : expr → stmt
  | SBlock : bool → stmt → stmt
  | SComp : stmt → stmt → stmt
  | SLabel : label → stmt → stmt
  | SWhile : expr → stmt → stmt
  | SIf : expr → stmt → stmt → stmt.
Notation funenv := (funmap stmt).

Instance stmt_eq_dec (s1 s2 : stmt) : Decision (s1 = s2).
Proof. solve_decision. Defined.

(** We use the scope [stmt_scope] for notations of statements. *)
Delimit Scope stmt_scope with S.
Bind Scope stmt_scope with stmt.
Open Scope stmt_scope.

Arguments SBlock _%S _.
Arguments SComp _%S _%S.
Arguments SLabel _ _%S.
Arguments SWhile _%E _%S.
Arguments SIf _%E _%S _%S.

Notation "'do' e" := (SDo e) (at level 10) : stmt_scope.
Notation "'skip'" := SSkip : stmt_scope.
Notation "'goto' l" := (SGoto l) (at level 10) : stmt_scope.
Notation "'ret' e" := (SReturn e) (at level 10) : stmt_scope.
Notation "'blk' @{ c } s" := (SBlock c s)
  (at level 10, format "'blk' @{ c }  s") : stmt_scope.

Notation "s1 ;; s2" := (SComp s1 s2)
  (at level 80, right associativity,
   format "'[' s1  ;;  '/' s2 ']'") : stmt_scope.
Notation "l :; s" := (SLabel l s)
  (at level 81, format "l  :;  s") : stmt_scope.
Notation "'while' '(' e ')' s" := (SWhile e s)
  (at level 10, format "'while'  '(' e ')'  s") : stmt_scope.
Notation "'IF' e 'then' s1 'else' s2" := (SIf e s1 s2) : stmt_scope.

Instance: Injective (=) (=) SDo.
Proof. by injection 1. Qed.
Instance: Injective (=) (=) SGoto.
Proof. by injection 1. Qed.
Instance: Injective (=) (=) SReturn.
Proof. by injection 1. Qed.
Instance: Injective (=) (=) (SBlock c).
Proof. by injection 1. Qed.

Instance stmt_gotos: Gotos stmt :=
  fix go (s : stmt) : labelset :=
  let _ : Gotos _ := @go in
  match s with
  | blk@{_} s => gotos s
  | s1 ;; s2 => gotos s1 ∪ gotos s2
  | _ :; s => gotos s
  | while (_) s => gotos s
  | (IF _ then s1 else s2) => gotos s1 ∪ gotos s2
  | goto l => {[ l ]}
  | _ => ∅
  end.
Instance stmt_labels: Labels stmt :=
  fix go (s : stmt) : labelset :=
  let _ : Labels _ := @go in
  match s with
  | blk@{_} s => labels s
  | s1 ;; s2 => labels s1 ∪ labels s2
  | l :; s => {[ l ]} ∪ labels s
  | while (_) s => labels s
  | (IF _ then s1 else s2) => labels s1 ∪ labels s2
  | _ => ∅
  end.
Instance stmt_locks: Locks stmt :=
  fix go (s : stmt) : indexset :=
  let _ : Locks _ := @go in
  match s with
  | blk@{_} s => locks s
  | s1 ;; s2 => locks s1 ∪ locks s2
  | _ :; s => locks s
  | while (e) s => locks e ∪ locks s
  | (IF e then s1 else s2) => locks e ∪ locks s1 ∪ locks s2
  | do e => locks e
  | ret e => locks e
  | skip => ∅
  | goto _ => ∅
  end.

(** * Program contexts *)
(** We first define the data type [sctx_item] of singular statement contexts. A
pair [(E, s)] consisting of a list of singular statement contexts [E] and a
statement [s] forms a zipper for statements without block scope variables. *)
Inductive sctx_item : Type :=
  | CCompL : stmt → sctx_item
  | CCompR : stmt → sctx_item
  | CLabel : label → sctx_item
  | CWhile : expr → sctx_item
  | CIfL : expr → stmt → sctx_item
  | CIfR : expr → stmt → sctx_item.

Instance sctx_item_eq_dec (E1 E2 : sctx_item) : Decision (E1 = E2).
Proof. solve_decision. Defined.

Bind Scope stmt_scope with sctx_item.
Notation "□ ;; s" := (CCompL s) (at level 80, format "□  ;;  s") : stmt_scope.
Notation "s ;; □" := (CCompR s) (at level 80, format "s  ;;  □") : stmt_scope.
Notation "l :; □" := (CLabel l) (at level 81, format "l  :;  □") : stmt_scope.
Notation "'while' ( e ) □" := (CWhile e)
  (at level 10, format "'while'  '(' e ')'  □") : stmt_scope.
Notation "'IF' e 'then' □ 'else' s2" := (CIfL e s2)
  (at level 200, format "'IF'  e  'then'  □  'else'  s2") : stmt_scope.
Notation "'IF' e 'then' s1 'else' □" := (CIfR e s1)
  (at level 200, format "'IF'  e  'then'  s1  'else'  □") : stmt_scope.

Instance sctx_item_subst: Subst sctx_item stmt stmt := λ E s,
  match E with
  | □ ;; s2 => s ;; s2
  | s1 ;; □ => s1 ;; s
  | l :; □ => l :; s
  | while (e) □ => while (e) s
  | (IF e then □ else s2) => IF e then s else s2
  | (IF e then s1 else □) => IF e then s1 else s
  end.
Instance: DestructSubst sctx_item_subst.

Instance: ∀ E : sctx_item, Injective (=) (=) (subst E).
Proof. destruct E; repeat intro; simpl in *; by simplify_equality. Qed.

Instance sctx_item_gotos: Gotos sctx_item := λ E,
  match E with
  | s2 ;; □ => gotos s2
  | □ ;; s1 => gotos s1
  | l :; □ => ∅
  | while (_) □ => ∅
  | (IF _ then □ else s2) => gotos s2
  | (IF _ then s1 else □) => gotos s1
  end.
Instance sctx_item_labels: Labels sctx_item := λ E,
  match E with
  | s2 ;; □ => labels s2
  | □ ;; s1 => labels s1
  | l :; □ => {[ l ]}
  | while (_) □ => ∅
  | (IF _ then □ else s2) => labels s2
  | (IF _ then s1 else □) => labels s1
  end.

Lemma elem_of_sctx_item_gotos (E : sctx_item) (s : stmt) (l : label) :
  l ∈ gotos (subst E s) ↔ l ∈ gotos E ∨ l ∈ gotos s.
Proof. destruct E; solve_elem_of. Qed.
Lemma sctx_item_gotos_spec (E : sctx_item) (s : stmt) :
  gotos (subst E s) = gotos E ∪ gotos s.
Proof.
  apply elem_of_equiv_L. intros.
  rewrite elem_of_union. by apply elem_of_sctx_item_gotos.
Qed.

Lemma elem_of_sctx_item_labels (E : sctx_item) (s : stmt) (l : label) :
  l ∈ labels (subst E s) ↔ l ∈ labels E ∨ l ∈ labels s.
Proof. destruct E; solve_elem_of. Qed.
Lemma sctx_item_labels_spec (E : sctx_item) (s : stmt) :
  labels (subst E s) = labels E ∪ labels s.
Proof.
  apply elem_of_equiv_L. intros.
  rewrite elem_of_union. by apply elem_of_sctx_item_labels.
Qed.

Instance sctx_item_locks: Locks sctx_item := λ E,
  match E with
  | □ ;; s2 => locks s2
  | s1 ;; □ => locks s1
  | l :; □ => ∅
  | while (e) □ => locks e
  | (IF e then □ else s2) => locks e ∪ locks s2
  | (IF e then s1 else □) => locks e ∪ locks s1
  end.

Lemma sctx_item_subst_locks (E : sctx_item) s :
  locks (subst E s) = locks E ∪ locks s.
Proof. apply elem_of_equiv_L. destruct E; esolve_elem_of. Qed.

(** Next, we define the data type [esctx_item] of expression in statement
contexts. These contexts are used to store the statement to which an expression
that is being executed belongs to. *)
Inductive esctx_item : Type :=
  | CDoE : esctx_item
  | CReturnE : esctx_item
  | CWhileE : stmt → esctx_item
  | CIfE : stmt → stmt → esctx_item.

Instance esctx_item_eq_dec (E1 E2 : esctx_item) : Decision (E1 = E2).
Proof. solve_decision. Defined.

Notation "'do' □" := CDoE (at level 10, format "'do'  □") : stmt_scope.
Notation "'ret' □" := CReturnE (at level 10, format "'ret'  □") : stmt_scope.
Notation "'while' ( □ ) s" := (CWhileE s)
  (at level 10, format "'while'  '(' □ ')'  s") : stmt_scope.
Notation "'IF' □ 'then' s1 'else' s2" := (CIfE s1 s2)
  (at level 200, format "'IF'  □  'then'  s1  'else'  s2") : stmt_scope.

Instance esctx_item_subst: Subst esctx_item expr stmt := λ E e,
  match E with
  | do □ => do e
  | ret □ => ret e
  | while (□) s => while (e) s
  | (IF □ then s1 else s2) => IF e then s1 else s2
  end.
Instance: DestructSubst esctx_item_subst.

Instance: ∀ E : esctx_item, Injective (=) (=) (subst E).
Proof. destruct E; intros ???; simpl in *; by simplify_equality. Qed.

Instance esctx_item_locks: Locks esctx_item := λ E,
  match E with
  | do □ => ∅
  | ret □ => ∅
  | while (□) s => locks s
  | (IF □ then s1 else s2) => locks s1 ∪ locks s2
  end.

Lemma esctx_item_subst_locks (E : esctx_item) e :
  locks (subst E e) = locks E ∪ locks e.
Proof. apply elem_of_equiv_L. destruct E; esolve_elem_of. Qed.

(** Finally, we define the type [ctx_item] to extends [sctx_item] with some
additional singular contexts. These contexts will be used as follows.

- When entering a block, [block s], the context [CBlock b] is appended to the
  head of the program context. It associates the block scope variable with its
  corresponding memory index [b].
- To execute a statement [subst E e] containing an expression [e], the context
  [CExpr e E] is appended to the head of the program context. It stores the
  expression [e] itself and its location [E]. The expression itself is needed
  to restore the statement when execution of the expression is finished. The
  location is needed to determine what to do with the result of the expression.
- Upon a function call, [subst E (call f @ vs)], the context [CFun E] is
  appended to the head of the program context. It contains the location [E]
  of the caller so that it can be restored when the called function [f] returns.
- When a function body is entered, the context [CParams bs] is appended to the
  head of the program context. It contains a list of memory indexes of the
  function parameters.

Program contexts [ctx] are then defined as lists of singular contexts. *)
Inductive ctx_item : Type :=
  | CStmt : sctx_item → ctx_item
  | CBlock : bool → index → ctx_item
  | CExpr : expr → esctx_item → ctx_item
  | CFun : ectx → ctx_item
  | CParams : list index → ctx_item.
Notation ctx := (list ctx_item).

Instance ctx_item_eq_dec (E1 E2 : ctx_item) : Decision (E1 = E2).
Proof. solve_decision. Defined.
Instance ctx_eq_dec (k1 k2 : ctx) : Decision (k1 = k2).
Proof. solve_decision. Defined.

Instance ctx_item_subst: Subst ctx_item stmt stmt := λ E s,
  match E with
  | CStmt E => subst E s
  | CBlock c _ => blk@{c} s
  | _ => s
  end.

Instance: ∀ E : ctx_item, Injective (=) (=) (subst E).
Proof.
  destruct E; intros ???; auto.
  * eapply (injective (subst (CStmt _))); eauto.
  * eapply (injective (SBlock _)); eauto.
Qed.

Instance ctx_item_locks: Locks ctx_item := λ E,
  match E with
  | CStmt s => locks s
  | CBlock _ _ => ∅
  | CExpr e E => locks e ∪ locks E
  | CFun E => locks E
  | CParams _ => ∅
  end.

Inductive ctx_item_or_block : ctx_item → Prop :=
  | ctx_item_or_block_item E : ctx_item_or_block (CStmt E)
  | ctx_item_or_block_block c b : ctx_item_or_block (CBlock c b).

(** Given a context, we can construct a stack using the following erasure
function. We define [get_stack (CFun _ :: k)] as [[]] instead of [getstack k],
as otherwise it would be possible to refer to the local variables of the
calling function. *)
Fixpoint get_stack (k : ctx) : stack :=
  match k with
  | [] => []
  | CStmt _ :: k => get_stack k
  | CExpr _ _ :: k => get_stack k
  | CBlock _ b :: k => b :: get_stack k
  | CFun _ :: _ => []
  | CParams bs :: k => bs ++ get_stack k
  end.

Instance: Proper (proj_relation (=) get_stack ==> (=)) get_stack.
Proof. firstorder. Qed.

Instance: Proper (proj_relation (=) get_stack ==>
  proj_relation (=) get_stack) (k ++).
Proof.
  intros k l1 l2 E. unfold proj_relation in *.
  induction k as [|[] ?]; simpl; intuition congruence.
Qed.

(** * Tactics *)
(** We extend [solve_elem_of] to work better for finite sets involving [gotos]
and [labels]. *)
Ltac unfold_stmt_elem_of := repeat
  match goal with
  | H : context [ _ ∈ gotos (subst _ _) ] |- _ =>
    setoid_rewrite elem_of_sctx_item_gotos in H
  | H : context [ _ ∈ labels (subst _ _) ] |- _ =>
    setoid_rewrite elem_of_sctx_item_labels in H
  | |- context [ _ ∈ gotos (subst _ _) ] =>
    setoid_rewrite elem_of_sctx_item_gotos
  | |- context [ _ ∈ labels (subst _ _) ] =>
    setoid_rewrite elem_of_sctx_item_labels
  end.
Ltac solve_stmt_elem_of := simpl in *; unfold_stmt_elem_of; solve_elem_of.
