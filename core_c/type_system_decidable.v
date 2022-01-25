(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export type_system.

Local Open Scope expr_scope.
Local Open Scope ctype_scope.

Set Warnings "-fragile-hint-constr".

Section deciders.
Context `{Env K}.
Notation envs := (env K * memenv K * list (type K))%type.

#[global] Instance assign_typed_dec (τ1 τ2 : type K) (ass : assign) :
  Decision (assign_typed τ1 τ2 ass).
Proof.
 refine
  match ass with
  | Assign => cast_if (decide (cast_typed τ2 τ1))
  | PreOp op | PostOp op =>
     match Some_dec (binop_type_of op τ1 τ2) with
     | inleft (σ ↾ _) => cast_if (decide (cast_typed σ τ1))
     | inright _ => right _
     end
  end; repeat first
    [ by subst; econstructor; eauto using binop_type_of_sound
    | by inversion 1; repeat match goal with
      | H : binop_typed _ _ _ _ |- _ => apply binop_type_of_complete in H
      end; simplify_equality'
    | destruct τ1 | destruct τ2 ].
Defined.
#[global] Instance lrval_type_check:
   TypeCheck (env K * memenv K) (lrtype K) (lrval K) := λ ΓΔ ν,
  match ν with
  | inl p => inl <$> type_check ΓΔ p
  | inr v => inr <$> type_check ΓΔ v
  end.
#[global] Instance expr_type_check: TypeCheck envs (lrtype K) (expr K) :=
  fix go Γs e {struct e} := let _ : TypeCheck envs _ _ := @go in
  let '(Γ,Δ,τs) := Γs in
  match e with
  | var n => τ ← τs !! n; Some (inl (TType τ))
  | %#{Ω} ν => guard (✓{Γ,Δ} Ω); type_check (Γ,Δ) ν
  | .* e =>
     τ ← type_check Γs e ≫= maybe inr;
     τp ← maybe (TBase ∘ TPtr) τ;
     Some (inl τp)
  | & e =>
     τp ← type_check Γs e ≫= maybe inl;
     Some (inr (τp.*))
  | e1 ::={ass} e2 =>
     τ1 ← type_check Γs e1 ≫= maybe (inl ∘ TType);
     τ2 ← type_check Γs e2 ≫= maybe inr;
     guard (assign_typed τ1 τ2 ass);
     Some (inr τ1)
  | call e @ es =>
     '(σs,σ) ← (type_check Γs e ≫= maybe inl) ≫= maybe2 TFun;
     σs' ← mapM (λ e, type_check Γs e ≫= maybe inr) es;
     guard ((σs' : list (type K)) = σs); guard (type_complete Γ σ); Some (inr σ)
  | abort τ => guard (✓{Γ} τ); Some (inr τ)
  | load e =>
     τ ← type_check Γs e ≫= maybe (inl ∘ TType);
     guard (type_complete Γ τ);
     Some (inr τ)
  | e %> rs =>
     τ ← type_check Γs e ≫= maybe (inl ∘ TType);
     inl ∘ TType <$> τ !!{Γ} rs
  | e #> rs =>
     τ ← type_check Γs e ≫= maybe inr;
     inr <$> τ !!{Γ} rs
  | alloc{τ} e =>
     _ ← type_check Γs e ≫= maybe (inr ∘ TBase ∘ TInt);
     guard (✓{Γ} τ); Some (inl (TType τ))
  | free e =>
     τp ← type_check Γs e ≫= maybe inl;
     Some (inr voidT)
  | .{op} e =>
     τ ← type_check Γs e ≫= maybe inr;
     inr <$> unop_type_of op τ
  | e1 .{op} e2 =>
     τ1 ← type_check Γs e1 ≫= maybe inr;
     τ2 ← type_check Γs e2 ≫= maybe inr;
     inr <$> binop_type_of op τ1 τ2
  | if{e1} e2 else e3 =>
     τb ← type_check Γs e1 ≫= maybe (inr ∘ TBase); guard (τb ≠ @TVoid K);
     τlr2 ← type_check Γs e2;
     τlr3 ← type_check Γs e3;
     guard (τlr2 = τlr3); Some τlr2
  | e1,, e2 =>
     _ ← type_check Γs e1; type_check Γs e2
  | cast{σ} e =>
     τ ← type_check Γs e ≫= maybe inr;
     guard (cast_typed τ σ); guard (✓{Γ} σ); Some (inr σ)
  | #[r:=e1] e2 =>
     σ ← type_check Γs e1 ≫= maybe inr;
     τ ← type_check Γs e2 ≫= maybe inr;
     σ' ← τ !!{Γ} r;
     guard ((σ':type K) = σ); Some (inr τ)
  end.
#[global] Instance ectx_item_lookup :
    LookupE envs (ectx_item K) (lrtype K) (lrtype K) := λ Γs Ei τlr,
  let '(Γ,Δ,τs) := Γs in
  match Ei, τlr with
  | .* □, inr τ =>
    τp ← maybe (TBase ∘ TPtr) τ;
    Some (inl τp)
  | & □, inl τp => Some (inr (τp.*))
  | □ ::={ass} e2, inl τp1 =>
     τ1 ← maybe TType τp1;
     τ2 ← type_check Γs e2 ≫= maybe inr;
     guard (assign_typed τ1 τ2 ass);
     Some (inr τ1)
  | e1 ::={ass} □, inr τ2 =>
     τ1 ← type_check Γs e1 ≫= maybe (inl ∘ TType);
     guard (assign_typed τ1 τ2 ass);
     Some (inr τ1)
  | call □ @ es, inl τp =>
     '(σs,σ) ← maybe2 TFun τp;
     σs' ← mapM (λ e, type_check Γs e ≫= maybe inr) es;
     guard ((σs : list (type K)) = σs'); guard (type_complete Γ σ); Some (inr σ)
  | call e @ es1 □ es2, inr τ =>
     '(σs,σ) ← (type_check Γs e ≫= maybe inl) ≫= maybe2 TFun;
     σs1 ← mapM (λ e, type_check Γs e ≫= maybe inr) (reverse es1);
     σs2 ← mapM (λ e, type_check Γs e ≫= maybe inr) es2;
     guard ((σs : list (type K)) = σs1 ++ τ :: σs2);
     guard (type_complete Γ σ); Some (inr σ)
  | load □, inl τp =>
     τ ← maybe TType τp;
     guard (type_complete Γ τ);
     Some (inr τ)
  | □ %> rs, inl τp => τ ← maybe TType τp; inl ∘ TType <$> τ !!{Γ} rs
  | □ #> rs, inr τ => inr <$> τ !!{Γ} rs
  | alloc{τ} □, inr τ' =>
     _ ← maybe (TBase ∘ TInt) τ'; guard (✓{Γ} τ); Some (inl (TType τ))
  | free □, inl τp => Some (inr voidT)
  | .{op} □, inr τ => inr <$> unop_type_of op τ
  | □ .{op} e2, inr τ1 =>
     τ2 ← type_check Γs e2 ≫= maybe inr;
     inr <$> binop_type_of op τ1 τ2
  | e1 .{op} □, inr τ2 =>
     τ1 ← type_check Γs e1 ≫= maybe inr;
     inr <$> binop_type_of op τ1 τ2
  | if{□} e2 else e3, inr τ1 =>
     τb ← maybe TBase τ1; guard (τb ≠ @TVoid K);
     τlr2 ← type_check Γs e2;
     τlr3 ← type_check Γs e3;
     guard (τlr2 = τlr3); Some τlr2
  | □ ,, e2, _ => type_check Γs e2
  | cast{σ} □, inr τ => guard (cast_typed τ σ); guard (✓{Γ} σ); Some (inr σ)
  | #[r:=□] e2, inr σ =>
     τ ← type_check Γs e2 ≫= maybe inr;
     σ' ← τ !!{Γ} r;
     guard ((σ':type K) = σ); Some (inr τ)
  | #[r:=e1] □, inr τ =>
     σ ← type_check Γs e1 ≫= maybe inr;
     σ' ← τ !!{Γ} r;
     guard ((σ':type K) = σ); Some (inr τ)
  | _, _ => None
  end.
#[global] Instance ectx_lookup :
    LookupE envs (ectx K) (lrtype K) (lrtype K) :=
  fix go Γs E τlr {struct E} := let _ : LookupE _ _ _ _ := @go in
  match E with [] => Some τlr | Ei :: E => τlr !!{Γs} Ei ≫= lookupE Γs E end.
Definition rettype_union_alt
    (mσ1 mσ2 : option (type K)) : option (option (type K)) :=
  match mσ1, mσ2 with
  | Some σ1, Some σ2 => guard (σ1 = σ2); Some (Some σ1)
  | None, mσ | mσ, None => Some mσ
  end.
#[global] Instance rettype_match_dec (cmσ : rettype K) σ :
  Decision (rettype_match cmσ σ).
Proof.
 refine
  match cmσ with
  | (true,Some σ') => cast_if (decide (σ' = σ))
  | (false,Some σ') => cast_if (decide (σ' = σ ∧ σ = voidT))
  | (true,None) => left _
  | (false,None) => cast_if (decide (σ = voidT))
  end; abstract
    first [by intuition; subst; constructor|inversion 1; subst; intuition].
Defined.
#[global] Instance stmt_type_check: TypeCheck envs (rettype K) (stmt K) :=
  fix go Γs s {struct s} := let _ : TypeCheck envs _ _ := @go in
  let '(Γ,Δ,τs) := Γs in
  match s with
  | skip => Some (false,None)
  | ! e =>
     _ ← type_check Γs e ≫= maybe inr; guard (locks e = ∅); Some (false,None)
  | goto _ | throw _ => Some (true,None)
  | ret e =>
     τ ← type_check Γs e ≫= maybe inr; guard (locks e = ∅); Some (true,Some τ)
  | label _ | scase _ => Some (false,None)
  | local{τ} s => guard (✓{Γ} τ); type_check (Γ,Δ,τ :: τs) s
  | s1 ;; s2 =>
     '(c1,mσ1) ← type_check Γs s1;
     '(c2,mσ2) ← type_check Γs s2;
     mσ ← rettype_union_alt mσ1 mσ2; Some (c2,mσ)
  | catch s => '(c,mσ) ← type_check Γs s; Some (false,mσ)
  | loop s => '(_,mσ) ← type_check Γs s; Some (true,mσ)
  | if{e} s1 else s2 =>
     τb ← type_check Γs e ≫= maybe (inr ∘ TBase); guard (τb ≠ @TVoid K);
     guard (locks e = ∅);
     '(c1,mσ1) ← type_check Γs s1;
     '(c2,mσ2) ← type_check Γs s2;
     mσ ← rettype_union_alt mσ1 mσ2; Some (c1 && c2,mσ)
  | switch{e} s =>
     τi ← type_check Γs e ≫= maybe (inr ∘ TBase ∘ TInt);
     guard (locks e = ∅); '(_,mσ) ← type_check Γs s; Some (false,mσ)
  end%S.
#[global] Instance sctx_item_lookup :
    LookupE envs (sctx_item K) (rettype K) (rettype K) := λ Γs Es τlr,
  match Es, τlr with
  | □ ;; s2, (c1,mσ1) =>
     '(c2,mσ2) ← type_check Γs s2;
     mσ ← rettype_union_alt mσ1 mσ2; Some (c2,mσ)
  | s1 ;; □, (c2,mσ2) =>
     '(c1,mσ1) ← type_check Γs s1;
     mσ ← rettype_union_alt mσ1 mσ2; Some (c2,mσ)
  | catch □, (c,mσ) => Some (false,mσ)
  | loop □, (c,mσ) => Some (true,mσ)
  | if{e} □ else s2, (c1,mσ1) =>
     τb ← type_check Γs e ≫= maybe (inr ∘ TBase); guard (τb ≠ @TVoid K);
     guard (locks e = ∅);
     '(c2,mσ2) ← type_check Γs s2;
     mσ ← rettype_union_alt mσ1 mσ2; Some (c1&&c2,mσ)
  | if{e} s1 else □, (c2,mσ2) =>
     τb ← type_check Γs e ≫= maybe (inr ∘ TBase); guard (τb ≠ @TVoid K);
     guard (locks e = ∅);
     '(c1,mσ1) ← type_check Γs s1;
     mσ ← rettype_union_alt mσ1 mσ2; Some (c1&&c2,mσ)
  | switch{e} □, (c,mσ) =>
     τb ← type_check Γs e ≫= maybe (inr ∘ TBase ∘ TInt);
     guard (locks e = ∅); Some (false,mσ)
  end%S.
#[global] Instance esctx_item_lookup :
    LookupE envs (esctx_item K) (rettype K) (type K) := λ Γs Ee τlr,
  match Ee, τlr with
  | ! □, _ => Some (false,None)
  | ret □, _ => Some (true,Some τlr)
  | if{□} s1 else s2, baseT τb =>
     guard (τb ≠ TVoid);
     '(c1,mσ1) ← type_check Γs s1;
     '(c2,mσ2) ← type_check Γs s2;
     mσ ← rettype_union_alt mσ1 mσ2; Some (c1 && c2,mσ)
  | switch{□} s, intT τi =>
     '(_,mσ) ← type_check Γs s; Some (false,mσ)
  | _, _ => None
  end%S.
#[global] Instance ctx_item_lookup :
    LookupE envs (ctx_item K) (focustype K) (focustype K) := λ Γs Ek τlr,
  let '(Γ,Δ,τs) := Γs in
  match Ek, τlr with
  | CStmt Es, Stmt_type cmσ1 => Stmt_type <$> cmσ1 !!{Γs} Es
  | CLocal o τ, Stmt_type cmσ => guard (Δ ⊢ o : τ); Some (Stmt_type cmσ)
  | CExpr e Ee, Expr_type τ =>
     τ' ← type_check Γs e ≫= maybe inr; guard (locks e = ∅);
     guard (τ = τ'); Stmt_type <$> τ !!{Γs} Ee
  | CFun E, Fun_type f =>
     '(σs,τ) ← Γ !! f; Expr_type <$> inr τ !!{Γs} E ≫= maybe inr
  | CParams f oσs, Stmt_type cmσ =>
     '(σs,σ) ← Γ !! f;
     let os := oσs.*1 in let σs' := oσs.*2 in
     guard (σs' = σs); guard (Δ ⊢* os :* σs); guard (rettype_match cmσ σ);
     Some (Fun_type f)
  | _, _ => None
  end.
#[global] Instance focus_type_check:
    TypeCheck envs (focustype K) (focus K) := λ Γs φ,
  let '(Γ,Δ,τs) := Γs in
  match φ with
  | Stmt d s =>
     cmσ ← type_check Γs s;
     match d, cmσ with
     | ⇈ v, (c,Some τ) =>
        τ' ← type_check (Γ,Δ) v;
        guard ((τ : type K) = τ'); Some (Stmt_type cmσ)
     | ↘, _ | ↗, (false,_) | ↷ _, _ | ↑ _, _ | ↓ _, _ => Some (Stmt_type cmσ)
     | _, _ => None
     end
  | Expr e => Expr_type <$> type_check Γs e ≫= maybe inr
  | Call f vs =>
     '(σs,_) ← Γ !! f;
     σs' ← mapM (type_check (Γ,Δ)) vs;
     guard ((σs : list (type K)) = σs'); Some (Fun_type f)
  | Return f v =>
     '(_,σ) ← Γ !! f;
     σ' ← type_check (Γ,Δ) v;
     guard ((σ : type K) = σ'); Some (Fun_type f)
  | Undef (UndefExpr E e) =>
     Expr_type <$> (type_check Γs e ≫= lookupE Γs E) ≫= maybe inr
  | Undef (UndefBranch Es Ω v) =>
     guard (✓{Γ,Δ} Ω); τ ← type_check (Γ,Δ) v; Stmt_type <$> τ !!{Γs} Es
  end.
End deciders.

Section properties.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types Δ : memenv K.
Implicit Types τ σ : type K.
Notation envs := (env K * memenv K * list (type K))%type.

Ltac simplify :=
  repeat match goal with
  | mcτ : rettype _ |- _ => destruct mcτ
  | _ => progress simplify_option_eq
  | _ => case_match
  end.
Hint Resolve (type_check_sound (V:=val K)) (type_check_sound (V:=ptr K)): core.
Hint Resolve (mapM_type_check_sound (V:=val K)): core.
Hint Immediate (path_type_check_sound (R:=ref_seg _)): core.
Hint Immediate (path_type_check_sound (R:=ref _)): core.
Hint Immediate unop_type_of_sound binop_type_of_sound: core.
#[global] Instance:
  TypeCheckSpec (env K * memenv K) (lrtype K) (lrval K) (✓ ∘ fst).
Proof.
  intros [Γ Δ] ν τlr; split.
  * destruct ν; intros; simplify; typed_constructor; eauto.
  * by destruct 1; simplify; erewrite ?type_check_complete by eauto.
Qed.
Hint Resolve (type_check_sound (V:=lrval K)): core.
#[global] Instance: TypeCheckSpec envs (lrtype K) (expr K) (✓ ∘ fst ∘ fst).
Proof.
  intros [[Γ Δ] τs] e τlr; simpl; split.
  * assert (∀ es σs,
      Forall (λ e, ∀ τlr, type_check (Γ,Δ,τs) e = Some τlr →
        (Γ,Δ,τs) ⊢ e : τlr) es →
      mapM (λ e, type_check (Γ,Δ,τs) e ≫= maybe inr) es = Some σs →
      (Γ,Δ,τs) ⊢* es :* inr <$> σs).
    { intros ??. rewrite mapM_Some.
      induction 2; decompose_Forall_hyps; simplify; constructor; eauto. }
    revert τlr; induction e using @expr_ind_alt;
      intros; simplify; typed_constructor; eauto.
  * assert (∀ es σs,
      Forall2 (λ e τlr, type_check (Γ,Δ,τs) e = Some τlr) es (inr <$> σs) →
      mapM (λ e, type_check (Γ,Δ,τs) e ≫= maybe inr) es = Some σs) as help.
    { intros es σs. rewrite Forall2_fmap_r, mapM_Some.
      induction 1; constructor; simplify_option_eq; eauto. }
    by induction 1 using @expr_typed_ind; simplify_option_eq;
      erewrite ?type_check_complete, ?path_type_check_complete,
        ?assign_type_of_complete, ?unop_type_of_complete,
        ?binop_type_of_complete,?help by eauto; eauto; simplify_option_eq.
Qed.
Hint Resolve (type_check_sound (V:=expr K)): core.
#[global] Instance: PathTypeCheckSpec envs
  (lrtype K) (lrtype K) (ectx_item K) (✓ ∘ fst ∘ fst).
Proof.
  intros [[Γ Δ] τs] Ei τlr; simpl; split.
  * assert (∀ es σs,
      mapM (λ e, type_check (Γ,Δ,τs) e ≫= maybe inr) es = Some σs →
      (Γ,Δ,τs) ⊢* es :* inr <$> σs).
    { intros es σs. rewrite mapM_Some. induction 1; simplify; eauto. }
    destruct τlr, Ei; intros; simplify; typed_constructor; eauto.
  * assert (∀ es σs, (Γ,Δ,τs) ⊢* es :* inr <$> σs →
      mapM (λ e, type_check (Γ,Δ,τs) e ≫= maybe inr) es = Some σs) as help.
    { intros es σs. rewrite Forall2_fmap_r, mapM_Some.
      induction 1; constructor; erewrite ?type_check_complete by eauto; eauto. }
    destruct 1; unfold lookupE; fold lookupE; simplify_option_eq;
      erewrite ?type_check_complete by eauto; simpl;
      erewrite ?path_type_check_complete, ?assign_type_of_complete,
        ?unop_type_of_complete, ?binop_type_of_complete by eauto;
      simplify_option_eq; eauto.
Qed.
Hint Immediate (path_type_check_sound (R:=ectx_item _)): core.
#[global] Instance: PathTypeCheckSpec envs
  (lrtype K) (lrtype K) (ectx K) (✓ ∘ fst ∘ fst).
Proof.
  intros Γs Ei τlr τlr'; split.
  * unfold lookupE. revert τlr.
    induction Ei; intros; simplify; typed_constructor; eauto.
  * unfold lookupE. induction 1; simplify_option_eq;
      erewrite ?path_type_check_complete by eauto; eauto.
Qed.
Hint Immediate (path_type_check_sound (R:=ectx _)): core.
Lemma rettype_union_alt_sound mσ1 mσ2 mσ :
  rettype_union_alt mσ1 mσ2 = Some mσ → rettype_union mσ1 mσ2 mσ.
Proof.
  destruct mσ1, mσ2; intros; simplify_option_eq; constructor; eauto.
Qed.
Hint Immediate rettype_union_alt_sound: core.
Lemma rettype_union_alt_complete mσ1 mσ2 mσ :
  rettype_union mσ1 mσ2 mσ → rettype_union_alt mσ1 mσ2 = Some mσ.
Proof. destruct 1 as [[]| |]; simplify_option_eq; eauto. Qed.
#[global] Instance:
  TypeCheckSpec envs (rettype K) (stmt K) (✓ ∘ fst ∘ fst).
Proof.
  intros [[Γ Δ] τs] s mcτ; simpl; split.
  * revert τs mcτ.
    induction s; intros; simplify; typed_constructor; naive_solver.
  * induction 1;
      repeat match goal with
      | _ : _ ⊢ ?e : _ |- _ => erewrite (type_check_complete _ e) by eauto
      | _ => erewrite rettype_union_alt_complete by eauto
      | _ => progress simplify_option_eq
      end; eauto.
Qed.
Hint Resolve (type_check_sound (V:=stmt K)): core.
#[global] Instance: PathTypeCheckSpec envs
  (type K) (rettype K) (esctx_item K) (✓ ∘ fst ∘ fst).
Proof.
  intros [[Γ Δ] τs] Ee τlr; simpl; split.
  * unfold lookupE; destruct τlr, Ee;
      intros; simplify; typed_constructor; eauto.
  * destruct 1; simplify_option_eq;
      erewrite ?type_check_complete by eauto; simplify_option_eq;
      erewrite ?rettype_union_alt_complete by eauto; eauto.
Qed.
Hint Immediate (path_type_check_sound (R:=esctx_item _)): core.
#[global] Instance: PathTypeCheckSpec envs
  (rettype K) (rettype K) (sctx_item K) (✓ ∘ fst ∘ fst).
Proof.
  intros [[Γ Δ] τs] Es mcτ; simpl; split.
  * destruct mcτ, Es; intros; simplify; typed_constructor; eauto.
  * destruct 1; simplify_option_eq;
      erewrite ?type_check_complete by eauto; simplify_option_eq;
      erewrite ?rettype_union_alt_complete by eauto; eauto.
Qed.
Hint Immediate (path_type_check_sound (R:=sctx_item _)): core.
#[global] Instance: PathTypeCheckSpec envs
  (focustype K) (focustype K) (ctx_item K) (✓ ∘ fst ∘ fst).
Proof.
  intros [[Γ Δ] τs] Ek τf; simpl; split.
  * unfold lookupE; destruct τf, Ek; intros; simplify;
      try match goal with
      | |- context [CParams _ ?oσs] => is_var oσs; rewrite <-(zip_fst_snd oσs)
      end; typed_constructor; eauto.
  * destruct 1;
      repeat match goal with
      | _ => simpl; erewrite fst_zip, snd_zip
         by eauto using Nat.eq_le_incl, Forall2_length, eq_sym
      | _ => progress simplify_option_eq
      | _ => erewrite type_check_complete by eauto
      | _ => erewrite path_type_check_complete by eauto
      end; eauto.
Qed.
#[global] Instance:
  TypeCheckSpec envs (focustype K) (focus K) (✓ ∘ fst ∘ fst).
Proof.
  intros [[Γ Δ] τs] φ τf; simpl; split.
  * unfold type_check; destruct φ, τf;
      intros; simplify; repeat typed_constructor; eauto.
  * destruct 1;
      repeat match goal with
      | _ => progress simplify_option_eq
      | _ => case_match; typed_inversion_all
      | _ => erewrite mapM_type_check_complete by eauto
      | _ => erewrite type_check_complete by eauto
      | _ => erewrite path_type_check_complete by eauto
      end; eauto.
Qed.
End properties.
