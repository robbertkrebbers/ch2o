Require Export expressions.

Class Subst A B C := subst: A → B → C.
Arguments subst {_ _ _ _} !_ _ /.

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

Definition label := N.
Class Gotos A := gotos: ∀ `{Empty C} `{Union C} `{Singleton label C}, A → C.
Arguments gotos {_ _ _ _ _ _} !_ /.
Class Labels A := labels: ∀ `{Empty C} `{Union C} `{Singleton label C}, A → C.
Arguments labels {_ _ _ _ _ _} !_ /.

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

Inductive stmt : Type :=
  | SAssign : expr → expr → stmt
  | SCall : option expr → N → list expr → stmt
  | SSkip : stmt
  | SGoto : label → stmt
  | SReturn : option expr → stmt
  | SBlock : stmt → stmt
  | SComp : stmt → stmt → stmt
  | SLabel : label → stmt → stmt
  | SLoop : stmt → stmt
  | SIf : expr → stmt → stmt → stmt.
Notation fenv := (Nmap stmt).

Instance stmt_eq_dec (s1 s2 : stmt) : Decision (s1 = s2).
Proof. solve_decision. Defined.

Delimit Scope stmt_scope with S.
Bind Scope stmt_scope with stmt.
Open Scope stmt_scope.

Arguments SBlock _%S.
Arguments SComp _%S _%S.
Arguments SLabel _ _%S.
Arguments SLoop _%S.
Arguments SIf _ _%S _%S.

Infix "::=" := SAssign (at level 60) : stmt_scope.
Notation "'call' e" := (SCall e) (at level 9) : stmt_scope.
Notation "'skip'" := SSkip : stmt_scope.
Notation "'goto' l" := (SGoto l) (at level 9) : stmt_scope.
Notation "'ret' e" := (SReturn e) (at level 9) : stmt_scope.
Notation "'block' s" := (SBlock s) (at level 9) : stmt_scope.

Infix ";;" := SComp (at level 80, right associativity) : stmt_scope.
Infix ":;" := SLabel (at level 81) : stmt_scope.
Notation "'loop' s" := (SLoop s) (at level 9) : stmt_scope.
Notation "'IF' e 'then' s1 'else' s2" := (SIf e s1 s2) : stmt_scope.

Instance stmt_gotos: Gotos stmt :=
  fix go `{Empty C} `{Union C} `{Singleton label C} (s : stmt) : C :=
  let _ : Gotos _ := @go in
  match s with
  | block s => gotos s
  | s1 ;; s2 => gotos s1 ∪ gotos s2
  | _ :; s => gotos s
  | loop s => gotos s
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
  | loop s => labels s
  | (IF _ then s1 else s2) => labels s1 ∪ labels s2
  | _ => ∅
  end.

Inductive sctx_item : Type :=
  | CCompL : stmt → sctx_item
  | CCompR : stmt → sctx_item
  | CLabel : label → sctx_item
  | CLoop : sctx_item
  | CIfL : expr → stmt → sctx_item
  | CIfR : expr → stmt → sctx_item.

Instance sctx_item_eq_dec (E1 E2 : sctx_item) : Decision (E1 = E2).
Proof. solve_decision. Defined.

Bind Scope stmt_scope with sctx_item.
Notation "s ;; □" := (CCompL s%S) (at level 80) : stmt_scope.
Notation "□ ;; s" := (CCompR s%S) (at level 80) : stmt_scope.
Notation "l :; □" := (CLabel l) (at level 81) : stmt_scope.
Notation "'loop' □" := CLoop (at level 80) : stmt_scope.
Notation "'IF' e 'then' □ 'else' s2" := (CIfL e s2)
  (at level 200, right associativity) : stmt_scope.
Notation "'IF' e 'then' s1 'else' □" := (CIfR e s1)
  (at level 200, right associativity) : stmt_scope.

Instance sctx_item_subst: Subst sctx_item stmt stmt := λ E s,
  match E with
  | □ ;; s2 => s ;; s2
  | s1 ;; □ => s1 ;; s
  | l :; □ => l :; s
  | loop □=> loop s
  | (IF e then □ else s2) => IF e then s else s2
  | (IF e then s1 else □) => IF e then s1 else s
  end.

Instance: Injective (=) (=) SBlock.
Proof. congruence. Qed.
Instance: ∀ E : sctx_item, Injective (=) (=) (subst E).
Proof. destruct E; repeat intro; simpl in *; simplify_eqs. Qed.

Ltac simplify_stmt_eqs := simpl in *; repeat
  match goal with
  | _ => progress simplify_eqs
  | H : @subst sctx_item stmt stmt _ ?E _ = _ |- _ => destruct E; simpl in H
  | H : _ = @subst sctx_item stmt stmt _ ?E _ |- _ => destruct E; simpl in H
  end.

Instance sctx_item_gotos: Gotos sctx_item := λ _ _ _ _ E,
  match E with
  | s2 ;; □ => gotos s2
  | □ ;; s1 => gotos s1
  | l :; □ => ∅
  | loop □ => ∅
  | (IF _ then □ else s2) => gotos s2
  | (IF _ then s1 else □) => gotos s1
  end.
Instance sctx_item_labels: Labels sctx_item := λ _ _ _ _ E,
  match E with
  | s2 ;; □ => labels s2
  | □ ;; s1 => labels s1
  | l :; □ => {[ l ]}
  | loop □ => ∅
  | (IF _ then □ else s2) => labels s2
  | (IF _ then s1 else □) => labels s1
  end.

Lemma elem_of_sctx_item_gotos `{Collection label C} (l : label)
    (E : sctx_item) (s : stmt) :
  l ∈ gotos (subst E s) ↔ l ∈ gotos E ∨ l ∈ gotos s.
Proof. destruct E; simpl; simplify_elem_of. Qed.
Lemma sctx_item_gotos_spec `{Collection label C} (E : sctx_item) (s : stmt) :
  gotos (subst E s) ≡ gotos E ∪ gotos s.
Proof.
  apply elem_of_equiv. intros.
  rewrite elem_of_union. now apply elem_of_sctx_item_gotos.
Qed.

Lemma elem_of_sctx_item_labels `{Collection label C} (l : label)
    (E : sctx_item) (s : stmt) :
  l ∈ labels (subst E s) ↔ l ∈ labels E ∨ l ∈ labels s.
Proof. destruct E; simpl; simplify_elem_of. Qed.
Lemma sctx_item_labels_spec `{Collection label C} (E : sctx_item) (s : stmt) :
  labels (subst E s) ≡ labels E ∪ labels s.
Proof.
  apply elem_of_equiv. intros.
  rewrite elem_of_union. now apply elem_of_sctx_item_labels.
Qed.

Ltac split_stmt_elem_ofs := repeat
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
Ltac simplify_stmt_elem_of := simpl in *; split_stmt_elem_ofs; simplify_elem_of.

Inductive ctx_item : Type :=
  | CItem : sctx_item → ctx_item
  | CBlock : N → ctx_item
  | CCall : option expr → N → list expr → ctx_item
  | CParams : list N → ctx_item.
Notation ctx := (list ctx_item).
Bind Scope stmt_scope with ctx_item.

Instance ctx_item_eq_dec (E1 E2 : ctx_item) : Decision (E1 = E2).
Proof. solve_decision. Defined.
Instance ctx_eq_dec (k1 k2 : ctx) : Decision (k1 = k2).
Proof. solve_decision. Defined.

Fixpoint get_stack (k : ctx) : stack :=
  match k with
  | [] => []
  | CItem _ :: k => get_stack k
  | CBlock b :: k => b :: get_stack k
  | CCall _ _ _ :: _ => []
  | CParams bs :: k => bs ++ get_stack k
  end.
