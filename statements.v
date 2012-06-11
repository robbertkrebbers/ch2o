Require Export expressions.

Definition label := N.

Inductive stmt : Type :=
  | SAssign : expr → expr → stmt
  | SSkip : stmt
  | SGoto : label → stmt
  | SReturn : expr → stmt
  | SBlock : stmt → stmt
  | SComp : stmt → stmt → stmt
  | SLabel : label → stmt → stmt
  | SLoop : stmt → stmt
  | SIf : expr → stmt → stmt → stmt.

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
Notation "'skip'" := SSkip : stmt_scope.
Notation "'goto' l" := (SGoto l) (at level 10) : stmt_scope.
Notation "'ret' e" := (SReturn e) (at level 10) : stmt_scope.

Infix ";;" := SComp (at level 80, right associativity) : stmt_scope.
Infix ":;" := SLabel (at level 81) : stmt_scope.
Notation "'loop' s" := (SLoop s) (at level 10) : stmt_scope.
Notation "'IF' e 'then' s1 'else' s2" := (SIf e s1 s2) : stmt_scope.

Class Gotos A := gotos: ∀ `{Empty C} `{Union C} `{Singleton label C}, A → C.
Arguments gotos {A go C _ _ _} !_ / : rename.
Class Labels A := labels: ∀ `{Empty C} `{Union C} `{Singleton label C}, A → C.
Arguments labels {A go C _ _ _} !_ / : rename.

Instance stmt_gotos: Gotos stmt :=
  fix go `{Empty C} `{Union C} `{Singleton label C} (s : stmt) : C :=
  match s with
  | SBlock s => gotos (go:=@go) s
  | s1 ;; s2 => gotos (go:=@go) s1 ∪ gotos (go:=@go) s2
  | _ :; s => gotos (go:=@go) s
  | loop s => gotos (go:=@go) s
  | (IF _ then s1 else s2) => gotos (go:=@go) s1 ∪ gotos (go:=@go) s2
  | goto l => {{ l }}
  | _ => ∅
  end.
Instance stmt_labels: Labels stmt :=
  fix go `{Empty C} `{Union C} `{Singleton label C} (s : stmt) : C :=
  match s with
  | SBlock s => labels (go:=@go) s
  | s1 ;; s2 => labels (go:=@go) s1 ∪ labels (go:=@go) s2
  | l :; s => {{ l }} ∪ labels (go:=@go) s
  | loop s => labels (go:=@go) s
  | (IF _ then s1 else s2) => labels (go:=@go) s1 ∪ labels (go:=@go) s2
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
Notation "'IF' e 'then' □ 'else' s2" := (CIfL e s2) (at level 200, right associativity) : stmt_scope.
Notation "'IF' e 'then' s1 'else' □" := (CIfR e s1) (at level 200, right associativity) : stmt_scope.

Class Subst A B C := subst: A → B → C.
Arguments subst {A B C go} !_ _ / : rename.

Instance sctx_item_subst: Subst sctx_item stmt stmt := λ E s,
  match E with
  | □ ;; s2 => s ;; s2
  | s1 ;; □ => s1 ;; s
  | l :; □ => l :; s
  | loop □=> loop s
  | (IF e then □ else s2) => IF e then s else s2
  | (IF e then s1 else □) => IF e then s1 else s
  end.

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
  | l :; □ => {{ l }}
  | loop □ => ∅
  | (IF _ then □ else s2) => labels s2
  | (IF _ then s1 else □) => labels s1
  end.

Lemma elem_of_sctx_item_gotos `{Collection label C} (l : label) (E : sctx_item) (s : stmt) :
  l ∈ gotos (subst E s) ↔ l ∈ gotos E ∨ l ∈ gotos s.
Proof. destruct E; simpl; simplify_elem_of. Qed.
Lemma sctx_item_gotos_spec `{Collection label C} (E : sctx_item) (s : stmt) :
  gotos (subst E s) ≡ gotos E ∪ gotos s.
Proof.
  apply elem_of_equiv. intros.
  rewrite elem_of_union. now apply elem_of_sctx_item_gotos.
Qed.

Lemma elem_of_sctx_item_labels `{Collection label C} (l : label) (E : sctx_item) (s : stmt) :
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
  | H : context [ _ ∈ gotos (subst _ _) ] |- _ => setoid_rewrite elem_of_sctx_item_gotos in H
  | H : context [ _ ∈ labels (subst _ _) ] |- _ => setoid_rewrite elem_of_sctx_item_labels in H
  | |- context [ _ ∈ gotos (subst _ _) ] => setoid_rewrite elem_of_sctx_item_gotos
  | |- context [ _ ∈ labels (subst _ _) ] => setoid_rewrite elem_of_sctx_item_labels
  end.

Ltac simplify_stmt_elem_of := simpl in *; split_stmt_elem_ofs; simplify_elem_of.

Inductive ctx_item : Type :=
  | CItem : sctx_item → ctx_item
  | CBlock : N → ctx_item.
Notation ctx := (list ctx_item).
Bind Scope stmt_scope with ctx_item.

Instance ctx_item_eq_dec (E1 E2 : ctx_item) : Decision (E1 = E2).
Proof. solve_decision. Defined.
Instance ctx_eq_dec (k1 k2 : ctx) : Decision (k1 = k2).
Proof. solve_decision. Defined.

Instance ctx_item_subst: Subst ctx_item stmt stmt := λ E s,
  match E with
  | CItem E => subst E s
  | CBlock _ => SBlock s
  end.
Instance ctx_subst: Subst ctx stmt stmt :=
  fix go (k : ctx) (s : stmt) : stmt :=
  match k with
  | [] => s
  | E :: k => subst (go:=@go) k (subst E s)
  end.

Instance ctx_gotos: Gotos ctx :=
  fix go `{Empty C} `{Union C} `{Singleton label C} (k : ctx) : C :=
  match k with
  | [] => ∅
  | CItem E :: k => gotos E ∪ gotos (go:=@go) k
  | CBlock _ :: k => gotos (go:=@go) k
  end%S.
Instance ctx_labels: Labels ctx :=
  fix go `{Empty C} `{Union C} `{Singleton label C} (k : ctx) : C :=
  match k with
  | [] => ∅
  | CItem E :: k => labels E ∪ labels (go:=@go) k
  | CBlock _ :: k => labels (go:=@go) k
  end.

Instance: ∀ k : ctx, Injective (=) (=) (subst k).
Proof. induction k as [|[]]; repeat intro; simpl in *; simplify_eqs. Qed.

Lemma elem_of_ctx_gotos `{Collection label C} (l : label) (E : ctx) (s : stmt) :
  l ∈ gotos (subst E s) ↔ l ∈ gotos E ∨ l ∈ gotos s.
Proof.
  revert s; induction E as [|[]]; simpl.
    simplify_elem_of.
   intros. rewrite IHE, elem_of_sctx_item_gotos. simplify_elem_of.
  intros. now rewrite IHE.
Qed.
Lemma ctx_gotos_spec `{Collection label C} (E : ctx) (s : stmt) :
  gotos (subst E s) ≡ gotos E ∪ gotos s.
Proof.
  apply elem_of_equiv. intros.
  rewrite elem_of_union. now apply elem_of_ctx_gotos.
Qed.

Lemma elem_of_ctx_labels `{Collection label C} (l : label) (E : ctx) (s : stmt) :
  l ∈ labels (subst E s) ↔ l ∈ labels E ∨ l ∈ labels s.
Proof.
  revert s; induction E as [|[]]; simpl.
    simplify_elem_of.
   intros. rewrite IHE, elem_of_sctx_item_labels. simplify_elem_of.
  intros. now rewrite IHE.
Qed.
Lemma ctx_labels_spec `{Collection label C} (E : ctx) (s : stmt) :
  labels (subst E s) ≡ labels E ∪ labels s.
Proof.
  apply elem_of_equiv. intros.
  rewrite elem_of_union. now apply elem_of_ctx_labels.
Qed.

Fixpoint get_stack (k : ctx) : stack :=
  match k with
  | [] => []
  | CItem _ :: k => get_stack k
  | CBlock b :: k => b :: get_stack k
  end.

Lemma get_stack_app k1 k2 :
  get_stack (k1 ++ k2) = get_stack k1 ++ get_stack k2.
Proof. induction k1 as [|[]]; simpl; f_equal; auto. Qed.
