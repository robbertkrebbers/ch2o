(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export type_system.
Local Open Scope expr_scope.
Local Open Scope ctype_scope.

Section deciders.
Context `{Env K}.
Notation envs := (env K * memenv K * list (type K))%type.

Definition assign_type_of (τ1 τ2 : type K) (ass : assign) : option (type K) :=
  match ass with
  | Assign => guard (cast_typed τ2 τ1); Some τ1
  | PreOp op => σ ← binop_type_of op τ1 τ2; guard (cast_typed σ τ1); Some τ1
  | PostOp op => σ ← binop_type_of op τ1 τ2; guard (cast_typed σ τ1); Some τ1
  end.
Global Instance expr_type_check: TypeCheck envs (lrtype K) (expr K) :=
  fix go Γs e {struct e} := let _ : TypeCheck envs _ _ := @go in
  let '(Γ,Δ,τs) := Γs in
  match e with
  | var{τ} n => τ' ← τs !! n; guard (τ = τ'); Some (inl τ)
  | #{Ω} v => guard (✓{Γ,Δ} Ω); inr <$> type_check (Γ,Δ) v
  | %{Ω} a =>
     guard (✓{Γ,Δ} Ω); guard (addr_strict Γ a);
     τ ← type_check (Γ,Δ) a ≫= maybe TType;
     Some (inl τ)
  | .* e =>
     τ ← type_check Γs e ≫= maybe inr;
     τ' ← maybe (TBase ∘ TPtr ∘ TType) τ;
     guard (type_complete Γ τ'); Some (inl τ')
  | & e =>
     τ ← type_check Γs e ≫= maybe inl;
     Some (inr (TType τ.*))
  | e1 ::={ass} e2 =>
     τ1 ← type_check Γs e1 ≫= maybe inl;
     τ2 ← type_check Γs e2 ≫= maybe inr;
     inr <$> assign_type_of τ1 τ2 ass
  | call e @ es =>
     '(σs,σ) ← (type_check Γs e ≫= maybe (inr ∘ TBase ∘ TPtr)) ≫= maybe2 TFun;
     σs' ← mapM (λ e, type_check Γs e ≫= maybe inr) es;
     guard ((σs' : list (type K)) = σs); guard (type_complete Γ σ); Some (inr σ)
  | abort τ => guard (✓{Γ} τ); Some (inr τ)
  | load e => inr <$> type_check Γs e ≫= maybe inl
  | e %> rs =>
     τ ← type_check Γs e ≫= maybe inl;
     inl <$> τ !!{Γ} rs
  | e #> rs =>
     τ ← type_check Γs e ≫= maybe inr;
     inr <$> τ !!{Γ} rs
  | alloc{τ} e =>
     _ ← type_check Γs e ≫= maybe (inr ∘ TBase ∘ TInt);
     guard (✓{Γ} τ); Some (inr (TType τ.*))
  | free e =>
     τ' ← type_check Γs e ≫= maybe inl;
     Some (inr voidT)
  | @{op} e =>
     τ ← type_check Γs e ≫= maybe inr;
     inr <$> unop_type_of op τ
  | e1 @{op} e2 =>
     τ1 ← type_check Γs e1 ≫= maybe inr;
     τ2 ← type_check Γs e2 ≫= maybe inr;
     inr <$> binop_type_of op τ1 τ2
  | if{e1} e2 else e3 =>
     _ ← type_check Γs e1 ≫= maybe (inr ∘ TBase);
     τ2 ← type_check Γs e2 ≫= maybe inr;
     τ3 ← type_check Γs e3 ≫= maybe inr;
     guard (τ2 = τ3); Some (inr τ2)
  | e1,, e2 =>
     _ ← type_check Γs e1 ≫= maybe inr;
     inr <$> type_check Γs e2 ≫= maybe inr
  | cast{σ} e =>
     τ ← type_check Γs e ≫= maybe inr;
     guard (cast_typed τ σ); guard (✓{Γ} σ); Some (inr σ)
  | #[r:=e1] e2 =>
     σ ← type_check Γs e1 ≫= maybe inr;
     τ ← type_check Γs e2 ≫= maybe inr;
     σ' ← τ !!{Γ} r;
     guard ((σ':type K) = σ); Some (inr τ)
  end.
Global Instance ectx_item_lookup :
    LookupE envs (ectx_item K) (lrtype K) (lrtype K) := λ Γs Ei τlr,
  let '(Γ,Δ,τs) := Γs in
  match Ei, τlr with
  | .* □, inr τ =>
    τ' ← maybe (TBase ∘ TPtr ∘ TType) τ;
    guard (type_complete Γ τ'); Some (inl τ')
  | & □, inl τ => Some (inr (TType τ.*))
  | □ ::={ass} e2, inl τ1 =>
     τ2 ← type_check Γs e2 ≫= maybe inr;
     inr <$> assign_type_of τ1 τ2 ass
  | e1 ::={ass} □, inr τ2 =>
     τ1 ← type_check Γs e1 ≫= maybe inl;
     inr <$> assign_type_of τ1 τ2 ass
  | call □ @ es, inr τ =>
     '(σs,σ) ← maybe (TBase ∘ TPtr) τ ≫= maybe2 TFun;
     σs' ← mapM (λ e, type_check Γs e ≫= maybe inr) es;
     guard ((σs : list (type K)) = σs'); guard (type_complete Γ σ); Some (inr σ)
  | call e @ es1 □ es2, inr τ =>
     '(σs,σ) ←
       (type_check Γs e ≫= maybe (inr ∘ TBase ∘ TPtr)) ≫= maybe2 TFun;
     σs1 ← mapM (λ e, type_check Γs e ≫= maybe inr) (reverse es1);
     σs2 ← mapM (λ e, type_check Γs e ≫= maybe inr) es2;
     guard ((σs : list (type K)) = σs1 ++ τ :: σs2);
     guard (type_complete Γ σ); Some (inr σ)
  | load □, inl τ => Some (inr τ)
  | □ %> rs, inl τ => inl <$> τ !!{Γ} rs
  | □ #> rs, inr τ => inr <$> τ !!{Γ} rs
  | alloc{τ} □, inr τ' =>
     _ ← maybe (TBase ∘ TInt) τ'; guard (✓{Γ} τ); Some (inr (TType τ.*))
  | free □, inl τ => Some (inr voidT)
  | @{op} □, inr τ => inr <$> unop_type_of op τ
  | □ @{op} e2, inr τ1 =>
     τ2 ← type_check Γs e2 ≫= maybe inr;
     inr <$> binop_type_of op τ1 τ2
  | e1 @{op} □, inr τ2 =>
     τ1 ← type_check Γs e1 ≫= maybe inr;
     inr <$> binop_type_of op τ1 τ2
  | if{□} e2 else e3, inr τ1 =>
     _ ← maybe TBase τ1;
     τ2 ← type_check Γs e2 ≫= maybe inr;
     τ3 ← type_check Γs e3 ≫= maybe inr;
     guard (τ2 = τ3); Some (inr τ2)
  | □ ,, e2, inr τ1 => inr <$> type_check Γs e2 ≫= maybe inr
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
Global Instance ectx_lookup :
    LookupE envs (ectx K) (lrtype K) (lrtype K) :=
  fix go Γs E τlr := let _ : LookupE _ _ _ _ := @go in
  match E with [] => Some τlr | Ei :: E => τlr !!{Γs} Ei ≫= lookupE Γs E end.
Global Instance stmt_type_check: TypeCheck envs (rettype K) (stmt K) :=
  fix go Γs s {struct s} := let _ : TypeCheck envs _ _ := @go in
  let '(Γ,Δ,τs) := Γs in
  match s with
  | skip => Some (false,None)
  | ! e =>
     _ ← type_check Γs e ≫= maybe inr; guard (locks e = ∅); Some (false,None)
  | goto _ | throw _ => Some (true,None)
  | ret e =>
     τ ← type_check Γs e ≫= maybe inr; guard (locks e = ∅); Some (true,Some τ)
  | label _ => Some (false,None)
  | local{τ} s => guard (✓{Γ} τ); type_check (Γ,Δ,τ :: τs) s
  | s1 ;; s2 =>
     '(c1,mσ1) ← type_check Γs s1;
     '(c2,mσ2) ← type_check Γs s2;
     mσ ← rettype_union mσ1 mσ2; Some (c2,mσ)
  | catch s => '(c,mσ) ← type_check Γs s; Some (false,mσ)
  | loop s => '(_,mσ) ← type_check Γs s; Some (true,mσ)
  | if{e} s1 else s2 =>
     _ ← type_check Γs e ≫= maybe (inr ∘ TBase); guard (locks e = ∅);
     '(c1,mσ1) ← type_check Γs s1;
     '(c2,mσ2) ← type_check Γs s2;
     mσ ← rettype_union mσ1 mσ2; Some (c1 && c2,mσ)
  end%S.
Global Instance sctx_item_lookup :
    LookupE envs (sctx_item K) (rettype K) (rettype K) := λ Γs Es τlr,
  match Es, τlr with
  | □ ;; s2, (c1,mσ1) =>
     '(c2,mσ2) ← type_check Γs s2;
     mσ ← rettype_union mσ1 mσ2; Some (c2,mσ)
  | s1 ;; □, (c2,mσ2) =>
     '(c1,mσ1) ← type_check Γs s1;
     mσ ← rettype_union mσ1 mσ2; Some (c2,mσ)
  | catch □, (c,mσ) => Some (false,mσ)
  | loop □, (c,mσ) => Some (true,mσ)
  | if{e} □ else s2, (c1,mσ1) =>
     _ ← type_check Γs e ≫= maybe (inr ∘ TBase); guard (locks e = ∅);
     '(c2,mσ2) ← type_check Γs s2;
     mσ ← rettype_union mσ1 mσ2; Some (c1&&c2,mσ)
  | if{e} s1 else □, (c2,mσ2) =>
     _ ← type_check Γs e ≫= maybe (inr ∘ TBase); guard (locks e = ∅);
     '(c1,mσ1) ← type_check Γs s1;
     mσ ← rettype_union mσ1 mσ2; Some (c1&&c2,mσ)
  end%S.
Global Instance esctx_item_lookup :
    LookupE envs (esctx_item K) (rettype K) (type K) := λ Γs Ee τlr,
  match Ee, τlr with
  | ! □, _ => Some (false,None)
  | ret □, _ => Some (true,Some τlr)
  | if{□} s1 else s2, baseT τb =>
     '(c1,mσ1) ← type_check Γs s1;
     '(c2,mσ2) ← type_check Γs s2;
     mσ ← rettype_union mσ1 mσ2; Some (c1 && c2,mσ)
  | _, _ => None
  end%S.
Global Instance rettype_match_dec (cmσ : rettype K) σ :
    Decision (rettype_match cmσ σ) :=
  match cmσ with
  | (true,Some σ') => decide (σ' = σ)
  | (false,Some _) => right (@id False)
  | (_,None) => decide (σ = voidT)
  end.
Global Instance ctx_item_lookup :
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
     let os := fst <$> oσs in let σs' := snd <$> oσs in
     guard (σs' = σs); guard (Δ ⊢* os :* σs); guard (rettype_match cmσ σ);
     Some (Fun_type f)
  | _, _ => None
  end.
Global Instance focus_type_check:
    TypeCheck envs (focustype K) (focus K) := λ Γs φ,
  let '(Γ,Δ,τs) := Γs in
  match φ with
  | Stmt d s =>
     cmσ ← type_check Γs s;
     match d, cmσ with
     | ⇈ v, (c,Some τ) =>
        τ' ← type_check (Γ,Δ) v;
        guard ((τ : type K) = τ'); Some (Stmt_type cmσ)
     | ↘, _ | ↗, (false,_) | ↷ _, _ | ↑ _, _ => Some (Stmt_type cmσ)
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
Implicit Types o : index.
Implicit Types Δ : memenv K.
Implicit Types m : mem K.
Implicit Types e : expr K.
Implicit Types s : stmt K.
Implicit Types τ σ : type K.
Implicit Types a : addr K.
Implicit Types v : val K.
Implicit Types Ei : ectx_item K.
Implicit Types E : ectx K.
Implicit Types Es : sctx_item K.
Implicit Types Ee : esctx_item K.
Implicit Types Ek : ctx_item K.
Implicit Types k : ctx K.
Implicit Types d : direction K.
Notation envs := (env K * memenv K * list (type K))%type.

Ltac simplify :=
  repeat match goal with
  | mcτ : rettype _ |- _ => destruct mcτ
  | _ => progress simplify_option_equality
  | _ => case_match
  end.
Hint Resolve (type_check_sound (V:=val K)) (type_check_sound (V:=addr K)).
Hint Resolve (mapM_type_check_sound (V:=val K)).
Hint Immediate (path_type_check_sound (R:=ref_seg _)).
Hint Immediate (path_type_check_sound (R:=ref _)).
Hint Immediate unop_type_of_sound binop_type_of_sound.
Arguments rettype_match _ _ _ : simpl never.
Arguments rettype_match_dec _ _ _ _ : simpl never.
Lemma assign_type_of_sound ass τ1 τ2 σ :
  assign_type_of τ1 τ2 ass = Some σ → assign_typed τ1 τ2 ass σ.
Proof.
  destruct ass; intros; simplify_option_equality;
    econstructor; eauto using binop_type_of_sound.
Qed.
Hint Immediate assign_type_of_sound.
Lemma assign_type_of_complete ass τ1 τ2 σ :
  assign_typed τ1 τ2 ass σ → assign_type_of τ1 τ2 ass = Some σ.
Proof.
  by destruct 1; simplify_option_equality;
    erewrite ?binop_type_of_complete by eauto; simplify_option_equality.
Qed.
Global Instance: TypeCheckSpec envs (lrtype K) (expr K) (✓ ∘ fst ∘ fst).
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
      induction 1; constructor; simplify_option_equality; eauto. }
    by induction 1 using @expr_typed_ind; simplify_option_equality;
      erewrite ?type_check_complete, ?path_type_check_complete,
        ?assign_type_of_complete, ?unop_type_of_complete,
        ?binop_type_of_complete,?help by eauto; eauto; simplify_option_equality.
Qed.
Hint Resolve (type_check_sound (V:=expr K)).
Global Instance: PathTypeCheckSpec envs
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
    destruct 1; simplify_option_equality;
      erewrite ?type_check_complete by eauto; simpl;
      erewrite ?path_type_check_complete, ?assign_type_of_complete,
        ?unop_type_of_complete, ?binop_type_of_complete by eauto;
      simplify_option_equality; eauto.
Qed.
Hint Immediate (path_type_check_sound (R:=ectx_item _)).
Global Instance: PathTypeCheckSpec envs
  (lrtype K) (lrtype K) (ectx K) (✓ ∘ fst ∘ fst).
Proof.
  intros Γs Ei τlr τlr'; split.
  * unfold lookupE. revert τlr.
    induction Ei; intros; simplify; typed_constructor; eauto.
  * unfold lookupE. induction 1; simplify_option_equality;
      erewrite ?path_type_check_complete by eauto; eauto.
Qed.
Hint Immediate (path_type_check_sound (R:=ectx _)).
Global Instance:
  TypeCheckSpec envs (rettype K) (stmt K) (✓ ∘ fst ∘ fst).
Proof.
  intros [[Γ Δ] τs] s mcτ; simpl; split.
  * revert τs mcτ.
    induction s; intros; simplify; typed_constructor; naive_solver.
  * induction 1; simplify_option_equality;
      erewrite ?type_check_complete by eauto; eauto.
Qed.
Hint Resolve (type_check_sound (V:=stmt K)).
Global Instance: PathTypeCheckSpec envs
  (type K) (rettype K) (esctx_item K) (✓ ∘ fst ∘ fst).
Proof.
  intros [[Γ Δ] τs] Ee τlr; simpl; split.
  * destruct τlr, Ee; intros; simplify; typed_constructor; eauto.
  * destruct 1; simplify_option_equality;
      erewrite ?type_check_complete by eauto; simplify_option_equality; eauto.
Qed.
Hint Immediate (path_type_check_sound (R:=esctx_item _)).
Global Instance: PathTypeCheckSpec envs
  (rettype K) (rettype K) (sctx_item K) (✓ ∘ fst ∘ fst).
Proof.
  intros [[Γ Δ] τs] Es mcτ; simpl; split.
  * destruct mcτ, Es; intros; simplify; typed_constructor; eauto.
  * destruct 1; simplify_option_equality;
      erewrite ?type_check_complete by eauto; simplify_option_equality; eauto.
Qed.
Hint Immediate (path_type_check_sound (R:=sctx_item _)).
Global Instance: PathTypeCheckSpec envs
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
      | _ => progress simplify_option_equality
      | _ => erewrite type_check_complete by eauto
      | _ => erewrite path_type_check_complete by eauto
      end; eauto.
Qed.
Global Instance:
  TypeCheckSpec envs (focustype K) (focus K) (✓ ∘ fst ∘ fst).
Proof.
  intros [[Γ Δ] τs] φ τf; simpl; split.
  * unfold type_check; destruct φ, τf;
      intros; simplify; repeat typed_constructor; eauto.
  * destruct 1;
      repeat match goal with
      | _ => progress simplify_option_equality
      | _ => case_match; typed_inversion_all
      | _ => erewrite mapM_type_check_complete by eauto
      | _ => erewrite type_check_complete by eauto
      | _ => erewrite path_type_check_complete by eauto
      end; eauto.
Qed.
End properties.
