(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export type_system.
Local Open Scope expr_scope.
Local Open Scope ctype_scope.

Section deciders.
Context `{Env Ti}.
Notation envs := (env Ti * funtypes Ti * memenv Ti * list (type Ti))%type.

Definition assign_type_of (Γ : env Ti)
    (τ1 τ2 : type Ti) (ass : assign) : option (type Ti) :=
  match ass with
  | Assign => guard (cast_typed Γ τ2 τ1); Some τ1
  | PreOp op => σ ← binop_type_of op τ1 τ2; guard (cast_typed Γ σ τ1); Some τ1
  | PostOp op => σ ← binop_type_of op τ1 τ2; guard (cast_typed Γ σ τ1); Some τ1
  end.
Global Instance expr_type_check: TypeCheck envs (lrtype Ti) (expr Ti) :=
  fix go Γs e {struct e} := let _ : TypeCheck envs _ _ := @go in
  let '(Γ,Γf,Γm,τs) := Γs in
  match e with
  | var{τ} n => τ' ← τs !! n; guard (τ = τ'); Some (inl τ)
  | #{Ω} v => guard (✓{Γm} Ω); inr <$> type_check (Γ,Γm) v
  | %{Ω} a =>
     guard (✓{Γm} Ω); guard (addr_strict Γ a);
     τp ← type_check (Γ,Γm) a;
     inl <$> τp
  | .* e =>
     τ ← type_check Γs e ≫= maybe inr;
     τp ← maybe (TBase ∘ TPtr ∘ Some) τ;
     guard (✓{Γ} τp); Some (inl τp)
  | & e =>
     τ ← type_check Γs e ≫= maybe inl;
     Some (inr (Some τ.*))
  | e1 ::={ass} e2 =>
     τ1 ← type_check Γs e1 ≫= maybe inl;
     τ2 ← type_check Γs e2 ≫= maybe inr;
     inr <$> assign_type_of Γ τ1 τ2 ass
  | call f @ es =>
     '(τs,τ) ← Γf !! f;
     τs' ← mapM (λ e, type_check Γs e ≫= maybe inr) es;
     guard ((τs' : list (type Ti)) = τs); Some (inr τ)
  | abort τ => guard (✓{Γ} τ); Some (inr τ)
  | load e => inr <$> type_check Γs e ≫= maybe inl
  | e %> rs =>
     τ ← type_check Γs e ≫= maybe inl;
     guard (ref_seg_offset rs = 0);
     inl <$> τ !!{Γ} rs
  | e #> rs =>
     τ ← type_check Γs e ≫= maybe inr;
     guard (ref_seg_offset rs = 0);
     inr <$> τ !!{Γ} rs
  | alloc{τ} e =>
     _ ← type_check Γs e ≫= maybe (inr ∘ TBase ∘ TInt);
     guard (✓{Γ} τ); Some (inl τ)
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
     guard (cast_typed Γ τ σ); Some (inr σ)
  | #[r:=e1] e2 =>
     σ ← type_check Γs e1 ≫= maybe inr;
     τ ← type_check Γs e2 ≫= maybe inr;
     σ' ← τ !!{Γ} r;
     guard ((σ':type Ti) = σ); Some (inr τ)
  end.
Global Instance ectx_item_lookup :
    LookupE envs (ectx_item Ti) (lrtype Ti) (lrtype Ti) := λ Γs Ei τlr,
  let '(Γ,Γf,Γm,τs) := Γs in
  match Ei, τlr with
  | .* □, inr τ =>
    τp ← maybe (TBase ∘ TPtr ∘ Some) τ;
    guard (✓{Γ} τp); Some (inl τp)
  | & □, inl τ => Some (inr (Some τ.*))
  | □ ::={ass} e2, inl τ1 =>
     τ2 ← type_check Γs e2 ≫= maybe inr;
     inr <$> assign_type_of Γ τ1 τ2 ass
  | e1 ::={ass} □, inr τ2 =>
     τ1 ← type_check Γs e1 ≫= maybe inl;
     inr <$> assign_type_of Γ τ1 τ2 ass
  | call f @ es1 □ es2, inr τ =>
     '(τs,σ) ← Γf !! f;
     τs1 ← mapM (λ e, type_check Γs e ≫= maybe inr) (reverse es1);
     τs2 ← mapM (λ e, type_check Γs e ≫= maybe inr) es2;
     guard ((τs : list (type Ti)) = τs1 ++ τ :: τs2);
     Some (inr σ)
  | load □, inl τ => Some (inr τ)
  | □ %> rs, inl τ =>
     guard (ref_seg_offset rs = 0);
     inl <$> τ !!{Γ} rs
  | □ #> rs, inr τ =>
     guard (ref_seg_offset rs = 0);
     inr <$> τ !!{Γ} rs
  | alloc{τ} □, inr τ' =>
     _ ← maybe (TBase ∘ TInt) τ'; guard (✓{Γ} τ); Some (inl τ)
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
  | cast{σ} □, inr τ => guard (cast_typed Γ τ σ); Some (inr σ)
  | #[r:=□] e2, inr σ =>
     τ ← type_check Γs e2 ≫= maybe inr;
     σ' ← τ !!{Γ} r;
     guard ((σ':type Ti) = σ); Some (inr τ)
  | #[r:=e1] □, inr τ =>
     σ ← type_check Γs e1 ≫= maybe inr;
     σ' ← τ !!{Γ} r;
     guard ((σ':type Ti) = σ); Some (inr τ)
  | _, _ => None
  end.
Global Instance ectx_lookup :
    LookupE envs (ectx Ti) (lrtype Ti) (lrtype Ti) :=
  fix go Γs E τlr := let _ : LookupE _ _ _ _ := @go in
  match E with [] => Some τlr | Ei :: E => τlr !!{Γs} Ei ≫= lookupE Γs E end.
Global Instance stmt_type_check: TypeCheck envs (rettype Ti) (stmt Ti) :=
  fix go Γs s {struct s} := let _ : TypeCheck envs _ _ := @go in
  let '(Γ,Γf,Γm,τs) := Γs in
  match s with
  | skip => Some (false,None)
  | ! e => _ ← type_check Γs e ≫= maybe inr; Some (false,None)
  | goto _ | throw _ => Some (true,None)
  | ret e => τ ← type_check Γs e ≫= maybe inr; Some (true,Some τ)
  | label _ => Some (false,None)
  | local{τ} s =>
     guard (✓{Γ} τ); guard (int_typed (size_of Γ τ) sptrT);
     type_check (Γ,Γf,Γm,τ :: τs) s
  | s1 ;; s2 =>
     '(c1,mσ1) ← type_check Γs s1;
     '(c2,mσ2) ← type_check Γs s2;
     mσ ← rettype_union mσ1 mσ2; Some (c2,mσ)
  | catch s => '(c,mσ) ← type_check Γs s; Some (false,mσ)
  | loop s => '(_,mσ) ← type_check Γs s; Some (true,mσ)
  | if{e} s1 else s2 =>
     _ ← type_check Γs e ≫= maybe (inr ∘ TBase);
     '(c1,mσ1) ← type_check Γs s1;
     '(c2,mσ2) ← type_check Γs s2;
     mσ ← rettype_union mσ1 mσ2; Some (c1 && c2,mσ)
  end%S.
Global Instance sctx_item_lookup :
    LookupE envs (sctx_item Ti) (rettype Ti) (rettype Ti) := λ Γs Es τlr,
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
     _ ← type_check Γs e ≫= maybe (inr ∘ TBase);
     '(c2,mσ2) ← type_check Γs s2;
     mσ ← rettype_union mσ1 mσ2; Some (c1&&c2,mσ)
  | if{e} s1 else □, (c2,mσ2) =>
     _ ← type_check Γs e ≫= maybe (inr ∘ TBase);
     '(c1,mσ1) ← type_check Γs s1;
     mσ ← rettype_union mσ1 mσ2; Some (c1&&c2,mσ)
  end%S.
Global Instance esctx_item_lookup :
    LookupE envs (esctx_item Ti) (rettype Ti) (type Ti) := λ Γs Ee τlr,
  match Ee, τlr with
  | ! □, _ => Some (false,None)
  | ret □, _ => Some (true,Some τlr)
  | if{□} s1 else s2, baseT τb =>
     '(c1,mσ1) ← type_check Γs s1;
     '(c2,mσ2) ← type_check Γs s2;
     mσ ← rettype_union mσ1 mσ2; Some (c1 && c2,mσ)
  | _, _ => None
  end%S.
Global Instance rettype_match_dec (cmσ : rettype Ti) σ :
    Decision (rettype_match cmσ σ) :=
  match cmσ with
  | (true,Some σ') => decide (σ' = σ)
  | (false,Some _) => right (@id False)
  | (_,None) => decide (σ = voidT)
  end.
Global Instance ctx_item_lookup :
    LookupE envs (ctx_item Ti) (focustype Ti) (focustype Ti) := λ Γs Ek τlr,
  let '(Γ,Γf,Γm,τs) := Γs in
  match Ek, τlr with
  | CStmt Es, Stmt_type cmσ1 => Stmt_type <$> cmσ1 !!{Γs} Es
  | CLocal o τ, Stmt_type cmσ => guard (Γm ⊢ o : τ); Some (Stmt_type cmσ)
  | CExpr e Ee, Expr_type τ =>
     τ' ← type_check Γs e ≫= maybe inr;
     guard (τ = τ'); Stmt_type <$> τ !!{Γs} Ee
  | CFun E, Fun_type f =>
     '(σs,τ) ← Γf !! f; Expr_type <$> inr τ !!{Γs} E ≫= maybe inr
  | CParams f oσs, Stmt_type cmσ =>
     '(σs,σ) ← Γf !! f;
     let os := fst <$> oσs in let σs' := snd <$> oσs in
     guard (σs' = σs); guard (Γm ⊢* os :* σs); guard (rettype_match cmσ σ);
     Some (Fun_type f)
  | _, _ => None
  end.
Global Instance focus_type_check:
    TypeCheck envs (focustype Ti) (focus Ti) := λ Γs φ,
  let '(Γ,Γf,Γm,τs) := Γs in
  match φ with
  | Stmt d s =>
     cmσ ← type_check Γs s;
     match d, cmσ with
     | ⇈ v, (c,Some τ) =>
        τ' ← type_check (Γ,Γm) v;
        guard ((τ : type Ti) = τ'); Some (Stmt_type cmσ)
     | ↘, _ | ↗, (false,_) | ↷ _, _ | ↑ _, _ => Some (Stmt_type cmσ)
     | _, _ => None
     end
  | Expr e => Expr_type <$> type_check Γs e ≫= maybe inr
  | Call f vs =>
     '(σs,_) ← Γf !! f;
     σs' ← mapM (type_check (Γ,Γm)) vs;
     guard ((σs : list (type Ti)) = σs'); Some (Fun_type f)
  | Return f v =>
     '(_,σ) ← Γf !! f;
     σ' ← type_check (Γ,Γm) v;
     guard ((σ : type Ti) = σ'); Some (Fun_type f)
  | Undef (UndefExpr E e) =>
     Expr_type <$> (type_check Γs e ≫= lookupE Γs E) ≫= maybe inr
  | Undef (UndefBranch Es Ω v) =>
     guard (✓{Γm} Ω); τ ← type_check (Γ,Γm) v; Stmt_type <$> τ !!{Γs} Es
  end.
End deciders.

Section properties.
Context `{EnvSpec Ti}.
Implicit Types Γ : env Ti.
Implicit Types Γf : funtypes Ti.
Implicit Types o : index.
Implicit Types Γm : memenv Ti.
Implicit Types m : mem Ti.
Implicit Types e : expr Ti.
Implicit Types s : stmt Ti.
Implicit Types τ σ : type Ti.
Implicit Types a : addr Ti.
Implicit Types v : val Ti.
Implicit Types Ei : ectx_item Ti.
Implicit Types E : ectx Ti.
Implicit Types Es : sctx_item Ti.
Implicit Types Ee : esctx_item Ti.
Implicit Types Ek : ctx_item Ti.
Implicit Types k : ctx Ti.
Implicit Types d : direction Ti.
Notation envs := (env Ti * funtypes Ti * memenv Ti * list (type Ti))%type.

Ltac simplify :=
  repeat match goal with
  | mcτ : rettype _ |- _ => destruct mcτ
  | _ => progress simplify_option_equality
  | _ => case_match
  end.
Hint Resolve (type_check_sound (V:=val Ti)) (type_check_sound (V:=addr Ti)).
Hint Resolve (mapM_type_check_sound (V:=val Ti)).
Hint Immediate (path_type_check_sound (R:=ref_seg _)).
Hint Immediate (path_type_check_sound (R:=ref _)).
Hint Immediate unop_type_of_sound binop_type_of_sound.
Arguments rettype_match _ _ _ : simpl never.
Arguments rettype_match_dec _ _ _ _ : simpl never.
Lemma assign_type_of_sound Γ ass τ1 τ2 σ :
  assign_type_of Γ τ1 τ2 ass = Some σ → assign_typed Γ τ1 τ2 ass σ.
Proof.
  destruct ass; intros; simplify_option_equality;
    econstructor; eauto using binop_type_of_sound.
Qed.
Hint Immediate assign_type_of_sound.
Lemma assign_type_of_complete Γ ass τ1 τ2 σ :
  assign_typed Γ τ1 τ2 ass σ → assign_type_of Γ τ1 τ2 ass = Some σ.
Proof.
  by destruct 1; simplify_option_equality;
    erewrite ?binop_type_of_complete by eauto; simplify_option_equality.
Qed.
Global Instance: TypeCheckSpec envs (lrtype Ti) (expr Ti) (✓ ∘ fst ∘ fst ∘ fst).
Proof.
  intros [[[Γ Γf] Γm] τs] e τlr; simpl; split.
  * assert (∀ es σs,
      Forall (λ e, ∀ τlr, type_check (Γ,Γf,Γm,τs) e = Some τlr →
        (Γ,Γf,Γm,τs) ⊢ e : τlr) es →
      mapM (λ e, type_check (Γ,Γf,Γm,τs) e ≫= maybe inr) es = Some σs →
      (Γ,Γf,Γm,τs) ⊢* es :* inr <$> σs).
    { intros ??. rewrite mapM_Some.
      induction 2; decompose_Forall_hyps; simplify; constructor; eauto. }
    revert τlr; induction e using @expr_ind_alt;
      intros; simplify; typed_constructor; eauto.
  * assert (∀ es σs,
      Forall2 (λ e τlr, type_check (Γ,Γf,Γm,τs) e = Some τlr) es (inr <$> σs) →
      mapM (λ e, type_check (Γ,Γf,Γm,τs) e ≫= maybe inr) es = Some σs) as help.
    { intros es σs. rewrite Forall2_fmap_r, mapM_Some.
      induction 1; constructor; simplify_option_equality; eauto. }
    by induction 1 using @expr_typed_ind; simplify_option_equality;
      erewrite ?type_check_complete, ?path_type_check_complete,
        ?assign_type_of_complete, ?unop_type_of_complete,
        ?binop_type_of_complete,?help by eauto; eauto; simplify_option_equality.
Qed.
Hint Resolve (type_check_sound (V:=expr Ti)).
Global Instance: PathTypeCheckSpec envs
  (lrtype Ti) (lrtype Ti) (ectx_item Ti) (✓ ∘ fst ∘ fst ∘ fst).
Proof.
  intros [[[Γ Γf] Γm] τs] Ei τlr; simpl; split.
  * assert (∀ es σs,
      mapM (λ e, type_check (Γ,Γf,Γm,τs) e ≫= maybe inr) es = Some σs →
      (Γ,Γf,Γm,τs) ⊢* es :* inr <$> σs).
    { intros es σs. rewrite mapM_Some. induction 1; simplify; eauto. }
    destruct τlr, Ei; intros; simplify; typed_constructor; eauto.
  * assert (∀ es σs, (Γ,Γf,Γm,τs) ⊢* es :* inr <$> σs →
      mapM (λ e, type_check (Γ,Γf,Γm,τs) e ≫= maybe inr) es = Some σs) as help.
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
  (lrtype Ti) (lrtype Ti) (ectx Ti) (✓ ∘ fst ∘ fst ∘ fst).
Proof.
  intros Γs Ei τlr τlr'; split.
  * unfold lookupE. revert τlr.
    induction Ei; intros; simplify; typed_constructor; eauto.
  * unfold lookupE. induction 1; simplify_option_equality;
      erewrite ?path_type_check_complete by eauto; eauto.
Qed.
Hint Immediate (path_type_check_sound (R:=ectx _)).
Global Instance:
  TypeCheckSpec envs (rettype Ti) (stmt Ti) (✓ ∘ fst ∘ fst ∘ fst).
Proof.
  intros [[[Γ Γf] Γm] τs] s mcτ; simpl; split.
  * revert τs mcτ.
    induction s; intros; simplify; typed_constructor; naive_solver.
  * induction 1; simplify_option_equality;
      erewrite ?type_check_complete by eauto; eauto.
Qed.
Hint Resolve (type_check_sound (V:=stmt Ti)).
Global Instance: PathTypeCheckSpec envs
  (type Ti) (rettype Ti) (esctx_item Ti) (✓ ∘ fst ∘ fst ∘ fst).
Proof.
  intros [[[Γ Γf] Γm] τs] Ee τlr; simpl; split.
  * destruct τlr, Ee; intros; simplify; typed_constructor; eauto.
  * destruct 1; simplify_option_equality;
      erewrite ?type_check_complete by eauto; simplify_option_equality; eauto.
Qed.
Hint Immediate (path_type_check_sound (R:=esctx_item _)).
Global Instance: PathTypeCheckSpec envs
  (rettype Ti) (rettype Ti) (sctx_item Ti) (✓ ∘ fst ∘ fst ∘ fst).
Proof.
  intros [[[Γ Γf] Γm] τs] Es mcτ; simpl; split.
  * destruct mcτ, Es; intros; simplify; typed_constructor; eauto.
  * destruct 1; simplify_option_equality;
      erewrite ?type_check_complete by eauto; simplify_option_equality; eauto.
Qed.
Hint Immediate (path_type_check_sound (R:=sctx_item _)).
Global Instance: PathTypeCheckSpec envs
  (focustype Ti) (focustype Ti) (ctx_item Ti) (✓ ∘ fst ∘ fst ∘ fst).
Proof.
  intros [[[Γ Γf] Γm] τs] Ek τf; simpl; split.
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
  TypeCheckSpec envs (focustype Ti) (focus Ti) (✓ ∘ fst ∘ fst ∘ fst).
Proof.
  intros [[[Γ Γf] Γm] τs] φ τf; simpl; split.
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
