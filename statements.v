(* Copyright (c) 2012, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file defines statements and program contexts. Program contexts are
an extension of Huet's zipper (Huet, 1997). They annotate local variable
declarations with their associated memory index, and keep track of the program's
stack. In the operational semantics we will use the program context to traverse
through the statement that is being executed. This approach makes it easy
to keep track of which memory cells should be freed upon uses of non-local
control flow (goto and return). *)
(** Program contexts may be seen as a generalization of continuations (as
for example being used in Compcert's small step semantics). However, there are
some notable differences.
- Program contexts implicitly contain a map assigning memory indexes to local
  variable declarations, so there is no need to keep track of that separately.
- They also do keep track of the part of the statement that has already been
  executed. In a continuation semantics this is thrown away.
- Since the complete statement is being preserved as we do not throw away code,
  looping constructs do not have to duplicate code. *)
Require Export expressions.

(** * Substitution *)
(** We define an operational type class for substitution of the hole of
a context. *)
Class Subst A B C := subst: A → B → C.
Arguments subst {_ _ _ _} !_ _ /.

(** Since contexts are generally defined as lists of singular contexts, this
type class is useful to lift substitution to lists of contexts in a generic
way. *)
Instance list_subst `{Subst A B B} : Subst (list A) B B :=
  fix go (l : list A) (b : B) : B :=
  let _ : Subst _ _ _ := @go in
  match l with
  | [] => b
  | a :: l => subst l (subst a b)
  end.
Lemma list_subst_app `{Subst A B B} (l1 l2 : list A) b :
  subst (l1 ++ l2) b = subst l2 (subst l1 b).
Proof. revert b. induction l1; simpl; auto. Qed.

(** * Function names *)
(** We use Coq's type of binary natural numbers [N] for function names, and the
[Nmap] implementation for efficient finite maps with function names as keys. *)
Definition funname := N.
Definition funmap := Nmap.

Instance funname_eq_dec: ∀ i1 i2 : funname, Decision (i1 = i2) := decide_rel (=).
Instance funmap_empty {A} : Empty (funmap A) := @empty (Nmap A) _.
Instance funmap_lookup: Lookup funname funmap := @lookup _ Nmap _.
Instance funmap_partial_alter: PartialAlter funname funmap :=
  @partial_alter _ Nmap _.
Instance funmap_dom : Dom funname funmap := @dom _ Nmap _.
Instance funmap_merge: Merge funmap := @merge Nmap _.
Instance funmap_fmap: FMap funmap := @fmap Nmap _.
Instance: FinMap funname funmap := _.

(** * Labels and gotos *)
(** We use Coq's type of binary natural numbers [N] for label names. We define
operational type classes to collect free occurrences of labels and labels used
by gotos. *)
Definition label := N.
Class Gotos A := gotos: ∀ `{Empty C} `{Union C} `{Singleton label C}, A → C.
Arguments gotos {_ _ _ _ _ _} !_ /.
Class Labels A := labels: ∀ `{Empty C} `{Union C} `{Singleton label C}, A → C.
Arguments labels {_ _ _ _ _ _} !_ /.

(** We lift instances of the above type classes to lists of contexts. *)
Instance list_gotos `{Gotos A} : Gotos (list A) :=
  fix go `{Empty C} `{Union C} `{Singleton label C} (l : list A) : C :=
  let _ : Gotos _ := @go in
  match l with
  | [] => ∅
  | a :: l => gotos a ∪ gotos l
  end.
Instance list_labels `{Labels A} : Labels (list A) :=
  fix go `{Empty C} `{Union C} `{Singleton label C} (l : list A) : C :=
  let _ : Labels _ := @go in
  match l with
  | [] => ∅
  | a :: l => labels a ∪ labels l
  end.

(** * Statements *)
(** Since expressions cannot perform side effects, we extend function calls to
assign the result: [SCall (Some e) f es] calls [f] with arguments [es] and 
assigns the result to [e]. The constructor [SBlock] represents a local variable
declaration. Since we treat variables in De Bruijn style it does not include a
name of the variable. *)
Inductive stmt : Type :=
  | SAssign : expr → expr → stmt
  | SCall : option expr → funname → list expr → stmt
  | SSkip : stmt
  | SGoto : label → stmt
  | SReturn : option expr → stmt
  | SBlock : stmt → stmt
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

Arguments SBlock _%S.
Arguments SComp _%S _%S.
Arguments SLabel _ _%S.
Arguments SWhile _%E _%S.
Arguments SIf _%E _%S _%S.

Infix "::=" := SAssign (at level 60) : stmt_scope.
Notation "'call' e" := (SCall e) (at level 10) : stmt_scope.
Notation "'skip'" := SSkip : stmt_scope.
Notation "'goto' l" := (SGoto l) (at level 10) : stmt_scope.
Notation "'ret' e" := (SReturn e) (at level 10) : stmt_scope.
Notation "'block' s" := (SBlock s) (at level 10) : stmt_scope.

Infix ";;" := SComp (at level 80, right associativity) : stmt_scope.
Infix ":;" := SLabel (at level 81) : stmt_scope.
Notation "'while' '(' e ')' s" := (SWhile e s)
  (at level 10, format "'while'  '(' e ')'  s") : stmt_scope.
Notation "'IF' e 'then' s1 'else' s2" := (SIf e s1 s2) : stmt_scope.

Instance: Injective (=) (=) SBlock.
Proof. congruence. Qed.

Instance stmt_gotos: Gotos stmt :=
  fix go `{Empty C} `{Union C} `{Singleton label C} (s : stmt) : C :=
  let _ : Gotos _ := @go in
  match s with
  | block s => gotos s
  | s1 ;; s2 => gotos s1 ∪ gotos s2
  | _ :; s => gotos s
  | while (_) s => gotos s
  | (IF _ then s1 else s2) => gotos s1 ∪ gotos s2
  | goto l => {[ l ]}
  | _ => ∅
  end.
Instance stmt_labels: Labels stmt :=
  fix go `{Empty C} `{Union C} `{Singleton label C} (s : stmt) : C :=
  let _ : Labels _ := @go in
  match s with
  | block s => labels s
  | s1 ;; s2 => labels s1 ∪ labels s2
  | l :; s => {[ l ]} ∪ labels s
  | while (_) s => labels s
  | (IF _ then s1 else s2) => labels s1 ∪ labels s2
  | _ => ∅
  end.

(** * Program contexts *)
(** We first define the data type [sctx_item] of singular program contexts for
all constructors of [stmt] that do not require additional annotations. That is,
for all constructors besides local variable declarations [SBlock]. *)
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
Notation "s ;; □" := (CCompL s) (at level 80) : stmt_scope.
Notation "□ ;; s" := (CCompR s) (at level 80) : stmt_scope.
Notation "l :; □" := (CLabel l) (at level 81) : stmt_scope.
Notation "'while' ( e ) □" := (CWhile e)
  (at level 10, format "'while'  '(' e ')'  □") : stmt_scope.
Notation "'IF' e 'then' □ 'else' s2" := (CIfL e s2)
  (at level 200, right associativity) : stmt_scope.
Notation "'IF' e 'then' s1 'else' □" := (CIfR e s1)
  (at level 200, right associativity) : stmt_scope.

Instance sctx_item_subst: Subst sctx_item stmt stmt := λ E s,
  match E with
  | □ ;; s2 => s ;; s2
  | s1 ;; □ => s1 ;; s
  | l :; □ => l :; s
  | while (e) □ => while (e) s
  | (IF e then □ else s2) => IF e then s else s2
  | (IF e then s1 else □) => IF e then s1 else s
  end.

Instance: ∀ E : sctx_item, Injective (=) (=) (subst E).
Proof. destruct E; repeat intro; simpl in *; simplify_equality. Qed.

Instance sctx_item_gotos: Gotos sctx_item := λ _ _ _ _ E,
  match E with
  | s2 ;; □ => gotos s2
  | □ ;; s1 => gotos s1
  | l :; □ => ∅
  | while (_) □ => ∅
  | (IF _ then □ else s2) => gotos s2
  | (IF _ then s1 else □) => gotos s1
  end.
Instance sctx_item_labels: Labels sctx_item := λ _ _ _ _ E,
  match E with
  | s2 ;; □ => labels s2
  | □ ;; s1 => labels s1
  | l :; □ => {[ l ]}
  | while (_) □ => ∅
  | (IF _ then □ else s2) => labels s2
  | (IF _ then s1 else □) => labels s1
  end.

Lemma elem_of_sctx_item_gotos `{Collection label C} (l : label)
    (E : sctx_item) (s : stmt) :
  l ∈ gotos (subst E s) ↔ l ∈ gotos E ∨ l ∈ gotos s.
Proof. destruct E; solve_elem_of. Qed.
Lemma sctx_item_gotos_spec `{Collection label C} (E : sctx_item) (s : stmt) :
  gotos (subst E s) ≡ gotos E ∪ gotos s.
Proof.
  apply elem_of_equiv. intros.
  rewrite elem_of_union. now apply elem_of_sctx_item_gotos.
Qed.

Lemma elem_of_sctx_item_labels `{Collection label C} (l : label)
    (E : sctx_item) (s : stmt) :
  l ∈ labels (subst E s) ↔ l ∈ labels E ∨ l ∈ labels s.
Proof. destruct E; solve_elem_of. Qed.
Lemma sctx_item_labels_spec `{Collection label C} (E : sctx_item) (s : stmt) :
  labels (subst E s) ≡ labels E ∪ labels s.
Proof.
  apply elem_of_equiv. intros.
  rewrite elem_of_union. now apply elem_of_sctx_item_labels.
Qed.

(** Now we define the type [ctx_item] which extends [sctx_item] with the
following singular contexts:
- [CBlock] which contain the memory index of the local variable declaration,
- [CCall] which contain the expression corresponding to the function call so
  it can be restored on return from the called function,
- [CParams] which contains the memory indexes corresponding to the function
  parameters.

Program contexts [ctx] are then defined as lists of singular contexts. *)
Inductive ctx_item : Type :=
  | CItem : sctx_item → ctx_item
  | CBlock : index → ctx_item
  | CCall : option expr → funname → list expr → ctx_item
  | CParams : list index → ctx_item.
Notation ctx := (list ctx_item).
Bind Scope stmt_scope with ctx_item.

Instance ctx_item_eq_dec (E1 E2 : ctx_item) : Decision (E1 = E2).
Proof. solve_decision. Defined.
Instance ctx_eq_dec (k1 k2 : ctx) : Decision (k1 = k2).
Proof. solve_decision. Defined.

(** Given a context, we can construct a stack using the following erasure
function. *)
Fixpoint get_stack (k : ctx) : stack :=
  match k with
  | [] => []
  | CItem _ :: k => get_stack k
  | CBlock b :: k => b :: get_stack k
  | CCall _ _ _ :: _ => []
  | CParams bs :: k => bs ++ get_stack k
  end.

(** * Tactics *)
Ltac simplify_stmt_equality := simpl in *; repeat
  match goal with
  | _ => progress simplify_equality
  | H : @subst sctx_item stmt stmt _ ?E _ = _ |- _ =>
    is_var E; destruct E; simpl in H
  | H : _ = @subst sctx_item stmt stmt _ ?E _ |- _ =>
    is_var E; destruct E; simpl in H
  end.

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
Ltac solve_stmt_elem_of :=
  simpl in *;
  unfold_stmt_elem_of;
  solve_elem_of.
