(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export state.
Local Open Scope expr_scope.
Local Open Scope ctype_scope.

Notation funtypes Ti := (funmap (list (type Ti) * type Ti)).
Notation lrtype Ti := (type Ti + type Ti)%type.
Notation rettype Ti := (bool * option (type Ti))%type.
Inductive focus_type (Ti : Set) :=
  | Stmt_type : rettype Ti → focus_type Ti
  | Expr_type : type Ti → focus_type Ti
  | Fun_type : funname → focus_type Ti.
Arguments Stmt_type {_} _.
Arguments Expr_type {_} _.
Arguments Fun_type {_} _.

Section typing.
Context `{IntEnv Ti, PtrEnv Ti}.

Notation envs := (env Ti * funtypes Ti * mem Ti * list (type Ti))%type.

Inductive lrval_typed' (Γ : env Ti) (m : mem Ti) :
    addr Ti + val Ti → lrtype Ti → Prop :=
  | lval_typed a τ :
     (Γ,m) ⊢ a : τ → addr_strict Γ a → lrval_typed' Γ m (inl a) (inl τ)
  | rval_typed v τ : (Γ,m) ⊢ v : τ → lrval_typed' Γ m (inr v) (inr τ).
Global Instance lrval_typed:
  Typed (env Ti * mem Ti) (lrtype Ti) (addr Ti + val Ti) := curry lrval_typed'.

Global Instance funtypes_valid : Valid (env Ti) (funtypes Ti) := λ Γ,
  map_Forall (λ _ τsσ, ✓{Γ}* (τsσ.1) ∧
    Forall (λ τ, int_typed (size_of Γ τ) sptrT) (τsσ.1) ∧ ✓{Γ} (τsσ.2)).

Inductive assign_typed (τ1 : type Ti) : type Ti → assign → type Ti → Prop :=
  | Assign_typed : assign_typed τ1 τ1 Assign τ1
  | PreOp_typed op τ2 :
     binop_typed op τ1 τ2 τ1 → assign_typed τ1 τ2 (PreOp op) τ1
  | PostOp_typed op τ2 :
     binop_typed op τ1 τ2 τ1 → assign_typed τ1 τ2 (PostOp op) τ1.
Definition assign_type_of (τ1 τ2 : type Ti) (ass : assign) : option (type Ti) :=
  match ass with
  | Assign => guard (τ1 = τ2); Some τ1
  | PreOp op => σ ← binop_type_of op τ1 τ2; guard (σ = τ1); Some σ
  | PostOp op => σ ← binop_type_of op τ1 τ2; guard (σ = τ1); Some σ
  end.

Inductive expr_typed' (Γ : env Ti) (Γf : funtypes Ti) (m : mem Ti)
     (τs : list (type Ti)) : expr Ti → lrtype Ti → Prop :=
  | EVar_typed τ n :
     τs !! n = Some τ → expr_typed' Γ Γf m τs (var{τ} n) (inl τ)
  | EVal_typed Ω v τ :
     (Γ,m) ⊢ v : τ → expr_typed' Γ Γf m τs (#{Ω} v) (inr τ)
  | EAddr_typed Ω a τ :
     (Γ,m) ⊢ a : τ → addr_strict Γ a →
     expr_typed' Γ Γf m τs (%{Ω} a) (inl τ)
  | ERtoL_typed e τ :
     expr_typed' Γ Γf m τs e (inr (τ.*)) → expr_typed' Γ Γf m τs (.* e) (inl τ)
  | ERofL_typed e τ :
     expr_typed' Γ Γf m τs e (inl τ) → expr_typed' Γ Γf m τs (& e) (inr (τ.*))
  | EAssign_typed ass e1 e2 τ1 τ2 σ :
     assign_typed τ1 τ2 ass σ →
     expr_typed' Γ Γf m τs e1 (inl τ1) → expr_typed' Γ Γf m τs e2 (inr τ2) →
     expr_typed' Γ Γf m τs (e1 ::={ass} e2) (inr σ)
  | ECall_typed f es σ σs :
     Γf !! f = Some (σs,σ) →
     Forall2 (expr_typed' Γ Γf m τs) es (inr <$> σs) →
     expr_typed' Γ Γf m τs (call f @ es) (inr σ)
  | ELoad_typed e τ :
     expr_typed' Γ Γf m τs e (inl τ) → expr_typed' Γ Γf m τs (load e) (inr τ)
  | EElt_typed e τ n :
     expr_typed' Γ Γf m τs e (inl (τ.[n])) →
     expr_typed' Γ Γf m τs (elt e) (inl τ)
  | EAlloc_typed τ :
     ✓{Γ} τ → int_typed (size_of Γ τ) sptrT →
     expr_typed' Γ Γf m τs (alloc τ) (inl τ)
  | EFree_typed e τ :
     expr_typed' Γ Γf m τs e (inl τ) →
     expr_typed' Γ Γf m τs (free e) (inr voidT)
  | EUnOp_typed op e τ σ :
     unop_typed op τ σ → expr_typed' Γ Γf m τs e (inr τ) →
     expr_typed' Γ Γf m τs (@{op} e) (inr σ)
  | EBinOp_typed op e1 e2 τ1 τ2 σ :
     binop_typed op τ1 τ2 σ → expr_typed' Γ Γf m τs e1 (inr τ1) →
     expr_typed' Γ Γf m τs e2 (inr τ2) →
     expr_typed' Γ Γf m τs (e1 @{op} e2) (inr σ)
  | EIf_typed e1 e2 e3 τb σ :
     expr_typed' Γ Γf m τs e1 (inr (baseT τb)) →
     expr_typed' Γ Γf m τs e2 (inr σ) → expr_typed' Γ Γf m τs e3 (inr σ) →
     expr_typed' Γ Γf m τs (if{e1} e2 else e3) (inr σ)
  | EComma_typed e1 e2 τ1 τ2 :
     expr_typed' Γ Γf m τs e1 (inr τ1) → expr_typed' Γ Γf m τs e2 (inr τ2) →
     expr_typed' Γ Γf m τs (e1 ,, e2) (inr τ2)
  | ECast_typed e τ σ :
     cast_typed Γ τ σ → expr_typed' Γ Γf m τs e (inr τ) →
     expr_typed' Γ Γf m τs (cast{σ} e) (inr σ)
  | EField_typed e c s σs i σ :
     Γ !! s = Some σs → σs !! i = Some σ →
     expr_typed' Γ Γf m τs e (inl (compoundT{c} s)) →
     expr_typed' Γ Γf m τs (e .> i) (inl σ).
Global Instance expr_typed:
  Typed envs (lrtype Ti) (expr Ti) := curry4 expr_typed'.

Section expr_typed_ind.
  Context (Γ : env Ti) (Γf : funtypes Ti) (m : mem Ti) (τs : list (type Ti)).
  Context (P : expr Ti → lrtype Ti → Prop).
  Context (Pvar : ∀ τ n, τs !! n = Some τ → P (var{τ} n) (inl τ)).
  Context (Pval : ∀ Ω v τ, (Γ,m) ⊢ v : τ → P (#{Ω} v) (inr τ)).
  Context (Paddr : ∀ Ω a τ,
    (Γ,m) ⊢ a : τ → addr_strict Γ a → P (%{Ω} a) (inl τ)).
  Context (Prtol : ∀ e τ,
    (Γ,Γf,m,τs) ⊢ e : inr (τ.*) → P e (inr (τ.*)) → P (.* e) (inl τ)).
  Context (Profl : ∀ e τ,
    (Γ,Γf,m,τs) ⊢ e : inl τ → P e (inl τ) → P (& e) (inr (τ.*))).
  Context (Passign : ∀ ass e1 e2 τ1 τ2 σ,
     assign_typed τ1 τ2 ass σ → (Γ,Γf,m,τs) ⊢ e1 : inl τ1 → P e1 (inl τ1) →
     (Γ,Γf,m,τs) ⊢ e2 : inr τ2 → P e2 (inr τ2) → P (e1 ::={ass} e2) (inr σ)).
  Context (Pcall : ∀ f es σ σs,
     Γf !! f = Some (σs,σ) → (Γ,Γf,m,τs) ⊢* es :* inr <$> σs →
     Forall2 P es (inr <$> σs) → P (call f @ es) (inr σ)).
  Context (Pload : ∀ e τ,
    (Γ,Γf,m,τs) ⊢ e : inl τ → P e (inl τ) → P (load e) (inr τ)).
  Context (Pelt : ∀ e τ n,
     (Γ,Γf,m,τs) ⊢ e : inl (τ.[n]) → P e (inl (τ.[n])) → P (elt e) (inl τ)).
  Context (Palloc : ∀ τ,
     ✓{Γ} τ → int_typed (size_of Γ τ) sptrT → P (alloc τ) (inl τ)).
  Context (Pfree : ∀ e τ,
     (Γ,Γf,m,τs) ⊢ e : inl τ → P e (inl τ) → P (free e) (inr voidT)).
  Context (Punop : ∀ op e τ σ,
     unop_typed op τ σ → (Γ,Γf,m,τs) ⊢ e : inr τ → P e (inr τ) → P (@{op} e) (inr σ)).
  Context (Pbinop : ∀ op e1 e2 τ1 τ2 σ,
     binop_typed op τ1 τ2 σ → (Γ,Γf,m,τs) ⊢ e1 : inr τ1 → P e1 (inr τ1) →
     (Γ,Γf,m,τs) ⊢ e2 : inr τ2 → P e2 (inr τ2) → P (e1 @{op} e2) (inr σ)).
  Context (Pif : ∀ e1 e2 e3 τb σ,
     (Γ,Γf,m,τs) ⊢ e1 : inr (baseT τb) → P e1 (inr (baseT τb)) →
     (Γ,Γf,m,τs) ⊢ e2 : inr σ → P e2 (inr σ) →
     (Γ,Γf,m,τs) ⊢ e3 : inr σ → P e3 (inr σ) → P (if{e1} e2 else e3) (inr σ)).
  Context (Pcomma : ∀ e1 e2 τ1 τ2,
     (Γ,Γf,m,τs) ⊢ e1 : inr τ1 → P e1 (inr τ1) →
     (Γ,Γf,m,τs) ⊢ e2 : inr τ2 → P e2 (inr τ2) → P (e1 ,, e2) (inr τ2)).
  Context (Pcast : ∀ e τ σ,
     cast_typed Γ τ σ → (Γ,Γf,m,τs) ⊢ e : inr τ → P e (inr τ) →
     P (cast{σ} e) (inr σ)).
  Context (Pfield : ∀ e c s σs i σ,
     Γ !! s = Some σs → σs !! i = Some σ →
     (Γ,Γf,m,τs) ⊢ e : inl (compoundT{c} s) → P e (inl (compoundT{c} s)) →
     P (e .> i) (inl σ)).
  Lemma expr_typed_ind : ∀ e τ, expr_typed' Γ Γf m τs e τ → P e τ.
  Proof. fix 3; destruct 1; eauto using Forall2_impl. Qed.
End expr_typed_ind.

Inductive ectx_item_typed' (Γ : env Ti) (Γf : funtypes Ti) (m : mem Ti)
     (τs : list (type Ti)) : ectx_item Ti → lrtype Ti → lrtype Ti → Prop :=
  | CRtoL_typed τ : ectx_item_typed' Γ Γf m τs (.* □) (inr (τ.*)) (inl τ)
  | CLtoR_typed τ : ectx_item_typed' Γ Γf m τs (& □) (inl τ) (inr (τ.*))
  | CAssignL_typed ass e2 τ1 τ2 σ :
     assign_typed τ1 τ2 ass σ → (Γ,Γf,m,τs) ⊢ e2 : inr τ2 →
     ectx_item_typed' Γ Γf m τs (□ ::={ass} e2) (inl τ1) (inr σ)
  | CAssignR_typed ass e1 τ1 τ2 σ :
     assign_typed τ1 τ2 ass σ → (Γ,Γf,m,τs) ⊢ e1 : inl τ1 →
     ectx_item_typed' Γ Γf m τs (e1 ::={ass} □) (inr τ2) (inr σ)
  | CCall_typed f es1 es2 σ τs1 τ τs2 :
     Γf !! f = Some (τs1 ++ τ :: τs2, σ) →
     (Γ,Γf,m,τs) ⊢* reverse es1 :* inr <$> τs1 →
     (Γ,Γf,m,τs) ⊢* es2 :* inr <$> τs2 →
     ectx_item_typed' Γ Γf m τs (call f @ es1 □ es2) (inr τ) (inr σ)
  | CLoad_typed τ : ectx_item_typed' Γ Γf m τs (load □) (inl τ) (inr τ)
  | CElt_typed τ n : ectx_item_typed' Γ Γf m τs (elt □) (inl (τ.[n])) (inl τ)
  | CFree_typed τ : ectx_item_typed' Γ Γf m τs (free □) (inl τ) (inr voidT)
  | CUnOp_typed op τ σ :
     unop_typed op τ σ → ectx_item_typed' Γ Γf m τs (@{op} □) (inr τ) (inr σ)
  | CBinOpL_typed op e2 τ1 τ2 σ :
     binop_typed op τ1 τ2 σ → (Γ,Γf,m,τs) ⊢ e2 : inr τ2 →
     ectx_item_typed' Γ Γf m τs (□ @{op} e2) (inr τ1) (inr σ)
  | CBinOpR_typed op e1 τ1 τ2 σ :
     binop_typed op τ1 τ2 σ → (Γ,Γf,m,τs) ⊢ e1 : inr τ1 →
     ectx_item_typed' Γ Γf m τs (e1 @{op} □) (inr τ2) (inr σ)
  | CIf_typed e2 e3 τb σ :
     (Γ,Γf,m,τs) ⊢ e2 : inr σ → (Γ,Γf,m,τs) ⊢ e3 : inr σ →
     ectx_item_typed' Γ Γf m τs (if{□} e2 else e3) (inr (baseT τb)) (inr σ)
  | CComma_typed e2 τ1 τ2 :
     (Γ,Γf,m,τs) ⊢ e2 : inr τ2 →
     ectx_item_typed' Γ Γf m τs (□ ,, e2) (inr τ1) (inr τ2)
  | CCast_typed τ σ :
     cast_typed Γ τ σ →
     ectx_item_typed' Γ Γf m τs (cast{σ} □) (inr τ) (inr σ)
  | CField_typed c s σs i σ :
     Γ !! s = Some σs → σs !! i = Some σ →
     ectx_item_typed' Γ Γf m τs (□ .> i) (inl (compoundT{c} s)) (inl σ).
Global Instance ectx_item_typed: PathTyped envs
  (lrtype Ti) (lrtype Ti) (ectx_item Ti) := curry4 ectx_item_typed'.
Inductive ectx_typed' (Γs : envs) : ectx Ti → lrtype Ti → lrtype Ti → Prop :=
  | ectx_nil_typed_2 τ : ectx_typed' Γs [] τ τ
  | ectx_cons_typed_2 Ei E τ1 τ2 τ3 :
     Γs ⊢ Ei : τ1 ↣ τ2 → ectx_typed' Γs E τ2 τ3 →
     ectx_typed' Γs (Ei :: E) τ1 τ3.
Global Instance ectx_typed:
  PathTyped envs (lrtype Ti) (lrtype Ti) (ectx Ti) := ectx_typed'.

Definition rettype_union
    (mσ1 mσ2 : option (type Ti)) : option (option (type Ti)) :=
  match mσ1, mσ2 with
  | Some σ1, Some σ2 => guard (σ1 = σ2); Some (Some σ1)
  | None, _ => Some mσ2
  | _, None => Some mσ1
  end.
Definition rettype_match (cmσ : rettype Ti) (σ : type Ti) : Prop :=
  match cmσ with
  | (true,Some σ') => σ' = σ
  | (false,Some _) => False
  | (_,None) => σ = voidT
  end.

Inductive stmt_typed' (Γ : env Ti) (Γf : funtypes Ti) (m : mem Ti)
     (τs : list (type Ti)) : stmt Ti → rettype Ti → Prop :=
  | SSkip_typed : stmt_typed' Γ Γf m τs skip (false,None)
  | SDo_typed e τ :
     (Γ,Γf,m,τs) ⊢ e : inr τ → stmt_typed' Γ Γf m τs (! e) (false,None)
  | SGoto_typed l : stmt_typed' Γ Γf m τs (goto l) (true,None)
  | SReturn_typed e τ :
     (Γ,Γf,m,τs) ⊢ e : inr τ → stmt_typed' Γ Γf m τs (ret e) (true,Some τ)
  | SBlock_typed' τ s c mσ :
     ✓{Γ} τ →int_typed (size_of Γ τ) sptrT →
     stmt_typed' Γ Γf m (τ :: τs) s (c,mσ) →
     stmt_typed' Γ Γf m τs (blk{τ} s) (c,mσ)
  | SComp_typed s1 s2 c1 mσ1 c2 mσ2 mσ :
     stmt_typed' Γ Γf m τs s1 (c1,mσ1) → stmt_typed' Γ Γf m τs s2 (c2,mσ2) →
     rettype_union mσ1 mσ2 = Some mσ → stmt_typed' Γ Γf m τs (s1 ;; s2) (c2,mσ)
  | SLabel_typed l : stmt_typed' Γ Γf m τs (label l) (false,None)
  | SWhile_typed e τb s c mσ :
     (Γ,Γf,m,τs) ⊢ e : inr (baseT τb) → stmt_typed' Γ Γf m τs s (c,mσ) →
     stmt_typed' Γ Γf m τs (while{e} s) (false,mσ)
  | SIf_typed e τb s1 s2 c1 mσ1 c2 mσ2 mσ :
     (Γ,Γf,m,τs) ⊢ e : inr (baseT τb) →
     stmt_typed' Γ Γf m τs s1 (c1,mσ1) → stmt_typed' Γ Γf m τs s2 (c2,mσ2) →
     rettype_union mσ1 mσ2 = Some mσ →
     stmt_typed' Γ Γf m τs (if{e} s1 else s2) (c1 && c2, mσ).
Global Instance stmt_typed:
  Typed envs (rettype Ti) (stmt Ti) := curry4 stmt_typed'.

Inductive sctx_item_typed' (Γ : env Ti) (Γf : funtypes Ti) (m : mem Ti)
     (τs : list (type Ti)) : sctx_item Ti → relation (rettype Ti) :=
  | CCompL_typed s2 c1 mσ1 c2 mσ2 mσ :
     (Γ,Γf,m,τs) ⊢ s2 : (c2,mσ2) → rettype_union mσ1 mσ2 = Some mσ →
     sctx_item_typed' Γ Γf m τs (□ ;; s2) (c1,mσ1) (c2,mσ)
  | CCompR_typed s1 c1 mσ1 c2 mσ2 mσ :
     (Γ,Γf,m,τs) ⊢ s1 : (c1,mσ1) → rettype_union mσ1 mσ2 = Some mσ →
     sctx_item_typed' Γ Γf m τs (s1 ;; □) (c2,mσ2) (c2,mσ)
  | CWhile_typed e τb c mσ :
     (Γ,Γf,m,τs) ⊢ e : inr (baseT τb) →
     sctx_item_typed' Γ Γf m τs (while{e} □) (c,mσ) (false,mσ)
  | CIfL_typed e τb s2 c1 mσ1 c2 mσ2 mσ :
     (Γ,Γf,m,τs) ⊢ e : inr (baseT τb) → (Γ,Γf,m,τs) ⊢ s2 : (c2,mσ2) →
     rettype_union mσ1 mσ2 = Some mσ →
     sctx_item_typed' Γ Γf m τs (if{e} □ else s2) (c1,mσ1) (c1&&c2,mσ)
  | CIfR_typed e τb s1 c1 mσ1 c2 mσ2 mσ :
     (Γ,Γf,m,τs) ⊢ e : inr (baseT τb) → (Γ,Γf,m,τs) ⊢ s1 : (c1,mσ1) →
     rettype_union mσ1 mσ2 = Some mσ →
     sctx_item_typed' Γ Γf m τs (if{e} s1 else □) (c2,mσ2) (c1&&c2,mσ).
Global Instance sctx_typed: PathTyped envs (rettype Ti)
  (rettype Ti) (sctx_item Ti) := curry4 sctx_item_typed'.

Inductive esctx_item_typed' (Γ : env Ti) (Γf : funtypes Ti) (m : mem Ti)
     (τs : list (type Ti)) : esctx_item Ti → type Ti → rettype Ti → Prop :=
  | CDoE_typed τ : esctx_item_typed' Γ Γf m τs (! □) τ (false,None)
  | CReturnE_typed τ : esctx_item_typed' Γ Γf m τs (ret □) τ (true,Some τ)
  | CWhileE_typed τb s c mσ :
     (Γ,Γf,m,τs) ⊢ s : (c,mσ) →
     esctx_item_typed' Γ Γf m τs (while{□} s) (baseT τb) (false,mσ)
  | CIfE_typed τb s1 s2 c1 mσ1 c2 mσ2 mσ :
     (Γ,Γf,m,τs) ⊢ s1 : (c1,mσ1) → (Γ,Γf,m,τs) ⊢ s2 : (c2,mσ2) →
     rettype_union mσ1 mσ2 = Some mσ →
     esctx_item_typed' Γ Γf m τs (if{□} s1 else s2)%S (baseT τb) (c1&&c2,mσ).
Global Instance esctx_item_typed: PathTyped envs (type Ti)
  (rettype Ti) (esctx_item Ti) := curry4 esctx_item_typed'.

Inductive ctx_item_typed' (Γ : env Ti) (Γf : funtypes Ti)
      (m : mem Ti) (k : ctx Ti) :
      ctx_item Ti → focus_type Ti → focus_type Ti → Prop :=
  | CStmt_typed Es cmσ1 cmσ2 :
     (Γ,Γf,m,get_stack_types k) ⊢ Es : cmσ1 ↣ cmσ2 →
     ctx_item_typed' Γ Γf m k (CStmt Es) (Stmt_type cmσ1) (Stmt_type cmσ2)
  | CBlock_typed o τ c mσ :
     m ⊢ o : τ →
     ctx_item_typed' Γ Γf m k (CBlock o τ) (Stmt_type (c,mσ)) (Stmt_type (c,mσ))
  | CExpr_typed e Ee τ cmσ :
     (Γ,Γf,m,get_stack_types k) ⊢ e : inr τ →
     (Γ,Γf,m,get_stack_types k) ⊢ Ee : τ ↣ cmσ →
     ctx_item_typed' Γ Γf m k (CExpr e Ee) (Expr_type τ) (Stmt_type cmσ)
  | CFun_typed E f τs τ σ :
     Γf !! f = Some (τs,τ) →
     (Γ,Γf,m,get_stack_types k) ⊢ E : inr τ ↣ inr σ →
     ctx_item_typed' Γ Γf m k (CFun E) (Fun_type f) (Expr_type σ)
  | CParams_typed f τs os cmσ σ :
     Γf !! f = Some (τs, σ) → length os = length τs →
     m ⊢* os :* τs → rettype_match cmσ σ →
     ctx_item_typed' Γ Γf m k (CParams (zip os τs)) (Stmt_type cmσ) (Fun_type f).
Global Instance ctx_item_typed:
  PathTyped (env Ti * funtypes Ti * mem Ti * ctx Ti)
    (focus_type Ti) (focus_type Ti) (ctx_item Ti) := curry4 ctx_item_typed'.
Inductive ctx_typed' (Γs : env Ti * funtypes Ti * mem Ti) :
     ctx Ti → focus_type Ti → focus_type Ti → Prop :=
  | ctx_nil_typed_2 τf : ctx_typed' Γs [] τf τf
  | ctx_cons_typed_2 Ek k τf1 τf2 τf3 :
     (Γs,k) ⊢ Ek : τf1 ↣ τf2 →
     ctx_typed' Γs k τf2 τf3 → ctx_typed' Γs (Ek :: k) τf1 τf3.
Global Instance ctx_typed: PathTyped (env Ti * funtypes Ti * mem Ti)
  (focus_type Ti) (focus_type Ti) (ctx Ti) := ctx_typed'.

Inductive direction_typed' (Γ : env Ti) (m : mem Ti) :
    direction Ti → rettype Ti → Prop :=
  | Down_typed cmτ : direction_typed' Γ m ↘ cmτ
  | Up_typed mτ : direction_typed' Γ m ↗ (false,mτ)
  | Top_typed c v τ : (Γ,m) ⊢ v : τ → direction_typed' Γ m (⇈ v) (c,Some τ)
  | Jump_typed l cmτ : direction_typed' Γ m (↷ l) cmτ.
Global Instance direction_typed:
  Typed (env Ti * mem Ti) (rettype Ti) (direction Ti) := curry direction_typed'.

Inductive focus_typed' (Γ : env Ti) (Γf : funtypes Ti) (m : mem Ti)
    (τs : list (type Ti)) : focus Ti → focus_type Ti → Prop :=
  | Stmt_typed d s cmσ :
     (Γ,Γf,m,τs) ⊢ s : cmσ → (Γ,m) ⊢ d : cmσ →
     focus_typed' Γ Γf m τs (Stmt d s) (Stmt_type cmσ)
  | Expr_typed e τ :
     (Γ,Γf,m,τs) ⊢ e : inr τ → focus_typed' Γ Γf m τs (Expr e) (Expr_type τ)
  | Call_typed f vs σs σ :
     Γf !! f = Some (σs,σ) → (Γ,m) ⊢* vs :* σs →
     focus_typed' Γ Γf m τs (Call f vs) (Fun_type f)
  | Return_typed f σs σ v :
     Γf !! f = Some (σs, σ) →
     (Γ,m) ⊢ v : σ → focus_typed' Γ Γf m τs (Return v) (Fun_type f)
  | Undef_typed e τ :
     (Γ,Γf,m,τs) ⊢ e : inr τ → focus_typed' Γ Γf m τs (Undef e) (Expr_type τ).
Global Instance focus_typed:
  Typed envs (focus_type Ti) (focus Ti) := curry4 focus_typed'.

Global Instance state_valid :
    Valid (env Ti * funtypes Ti) (state Ti) := λ ΓΓf S, ∃ τf,
  let 'State k φ m := S in
  (ΓΓf,m,get_stack_types k) ⊢ φ : τf ∧
  (ΓΓf,m) ⊢ k : τf ↣ Fun_type 0%N ∧
  ✓{ΓΓf.1} m.

Inductive funenv_typed' (Γ : env Ti) (m : mem Ti) :
     funenv Ti → funtypes Ti → Prop :=
  | funenv_empty_typed : funenv_typed' Γ m ∅ ∅
  | funenv_add_typed Γf δ f s cmτ τ τs :
     Γf !! f = None →
     ✓{Γ}* τs → Forall (λ τ, int_typed (size_of Γ τ) sptrT) τs →
     (Γ,Γf,m,τs) ⊢ s : cmτ → rettype_match cmτ τ →
     funenv_typed' Γ m δ Γf → funenv_typed' Γ m (<[f:=s]>δ) (<[f:=(τs,τ)]>Γf).
Global Instance funenv_typed:
  Typed (env Ti * mem Ti) (funtypes Ti) (funenv Ti) := curry funenv_typed'.
End typing.

Section properties.
Context `{EnvSpec Ti}.
Implicit Types Γ : env Ti.
Implicit Types Γf : funtypes Ti.
Implicit Types o : index.
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

Lemma SBlock_typed Γ Γf m τs τ s c mσ :
  ✓{Γ} τ →int_typed (size_of Γ τ) sptrT →
  (Γ,Γf,m,τ :: τs) ⊢ s : (c,mσ) → (Γ,Γf,m,τs) ⊢ blk{τ} s : (c,mσ).
Proof. by constructor. Qed.

Global Instance rettype_match_dec cmσ σ : Decision (rettype_match cmσ σ) :=
  match cmσ with
  | (true,Some σ') => decide (σ' = σ)
  | (false,Some _) => right (@id False)
  | (_,None) => decide (σ = voidT)
  end.
Lemma assign_type_of_correct ass τ1 τ2 σ :
  assign_typed τ1 τ2 ass σ ↔ assign_type_of τ1 τ2 ass = Some σ.
Proof.
  split.
  * by destruct 1; simplify_option_equality;
      erewrite ?(proj1 (binop_type_of_correct _ _ _ _)) by eauto;
      simplify_option_equality.
  * destruct ass; intros; simplify_option_equality; econstructor;
      eapply binop_type_of_correct; eauto.
Qed.

Lemma expr_typed_weaken Γ1 Γ2 Γf1 Γf2 m1 m2 τs1 τs2 e τlr :
  ✓ Γ1 → (Γ1,Γf1,m1,τs1) ⊢ e : τlr → Γ1 ⊆ Γ2 → Γf1 ⊆ Γf2 →
  (∀ o σ, m1 ⊢ o : σ → m2 ⊢ o : σ) → τs1 `prefix_of` τs2 →
  (Γ2,Γf2,m2,τs2) ⊢ e : τlr.
Proof.
  intros ? He ??? [σs ->].
  induction He using @expr_typed_ind; typed_constructor;
    erewrite <-1?size_of_weaken by eauto;
    eauto using val_typed_weaken, addr_typed_weaken, addr_strict_weaken,
    type_valid_weaken, lookup_weaken, lookup_app_l_Some, cast_typed_weaken.
Qed.
Lemma ectx_item_typed_weaken Γ1 Γ2 Γf1 Γf2 m1 m2 τs1 τs2 Ei τlr σlr :
  ✓ Γ1 → (Γ1,Γf1,m1,τs1) ⊢ Ei : τlr ↣ σlr → Γ1 ⊆ Γ2 → Γf1 ⊆ Γf2 →
  (∀ o σ, m1 ⊢ o : σ → m2 ⊢ o : σ) → τs1 `prefix_of` τs2 →
  (Γ2,Γf2,m2,τs2) ⊢ Ei : τlr ↣ σlr.
Proof.
  destruct 2; typed_constructor; eauto using addr_strict_weaken,
    expr_typed_weaken, lookup_weaken, cast_typed_weaken, Forall2_impl.
Qed.
Lemma ectx_typed_weaken Γ1 Γ2 Γf1 Γf2 m1 m2 τs1 τs2 E τlr σlr :
  ✓ Γ1 → (Γ1,Γf1,m1,τs1) ⊢ E : τlr ↣ σlr → Γ1 ⊆ Γ2 → Γf1 ⊆ Γf2 →
  (∀ o σ, m1 ⊢ o : σ → m2 ⊢ o : σ) → τs1 `prefix_of` τs2 →
  (Γ2,Γf2,m2,τs2) ⊢ E : τlr ↣ σlr.
Proof.
  intros ? HE ???. revert τlr HE. induction E; intros; typed_inversion_all;
    typed_constructor; eauto using ectx_item_typed_weaken.
Qed.
Lemma stmt_typed_weaken Γ1 Γ2 Γf1 Γf2 m1 m2 τs1 τs2 s mτ :
  ✓ Γ1 → (Γ1,Γf1,m1,τs1) ⊢ s : mτ → Γ1 ⊆ Γ2 → Γf1 ⊆ Γf2 →
  (∀ o σ, m1 ⊢ o : σ → m2 ⊢ o : σ) → τs1 `prefix_of` τs2 →
  (Γ2,Γf2,m2,τs2) ⊢ s : mτ.
Proof.
  intros ? Hs ???. revert τs2. induction Hs; typed_constructor;
    erewrite <-1?size_of_weaken by eauto;
    eauto using expr_typed_weaken, type_valid_weaken;
    unfold typed, stmt_typed in *; simpl in *; eauto using prefix_of_cons.
Qed.
Lemma sctx_item_typed_weaken Γ1 Γ2 Γf1 Γf2 m1 m2 τs1 τs2 Es mτ mσ :
  ✓ Γ1 → (Γ1,Γf1,m1,τs1) ⊢ Es : mτ ↣ mσ → Γ1 ⊆ Γ2 → Γf1 ⊆ Γf2 →
  (∀ o σ, m1 ⊢ o : σ → m2 ⊢ o : σ) → τs1 `prefix_of` τs2 →
  (Γ2,Γf2,m2,τs2) ⊢ Es : mτ ↣ mσ.
Proof.
  destruct 2; typed_constructor;
    eauto using stmt_typed_weaken, expr_typed_weaken.
Qed.
Lemma esctx_item_typed_weaken Γ1 Γ2 Γf1 Γf2 m1 m2 τs1 τs2 Ee τ mσ :
  ✓ Γ1 → (Γ1,Γf1,m1,τs1) ⊢ Ee : τ ↣ mσ → Γ1 ⊆ Γ2 → Γf1 ⊆ Γf2 →
  (∀ o σ, m1 ⊢ o : σ → m2 ⊢ o : σ) → τs1 `prefix_of` τs2 →
  (Γ2,Γf2,m2,τs2) ⊢ Ee : τ ↣ mσ.
Proof. destruct 2; typed_constructor; eauto using stmt_typed_weaken. Qed.
Lemma ctx_item_typed_weaken Γ1 Γ2 Γf1 Γf2 m1 m2 k Ek τf σf :
  ✓ Γ1 → (Γ1,Γf1,m1,k) ⊢ Ek : τf ↣ σf → Γ1 ⊆ Γ2 → Γf1 ⊆ Γf2 →
  (∀ o σ, m1 ⊢ o : σ → m2 ⊢ o : σ) → (Γ2,Γf2,m2,k) ⊢ Ek : τf ↣ σf.
Proof.
  destruct 2; typed_constructor; eauto using sctx_item_typed_weaken,
    ectx_typed_weaken, esctx_item_typed_weaken, expr_typed_weaken,
    Forall2_impl, lookup_weaken.
Qed.
Lemma ctx_typed_weaken Γ1 Γ2 Γf1 Γf2 m1 m2 k τf σf :
  ✓ Γ1 → (Γ1,Γf1,m1) ⊢ k : τf ↣ σf → Γ1 ⊆ Γ2 → Γf1 ⊆ Γf2 →
  (∀ o σ, m1 ⊢ o : σ → m2 ⊢ o : σ) → (Γ2,Γf2,m2) ⊢ k : τf ↣ σf.
Proof.
  intros ? Hk ???. revert τf Hk. induction k; intros; typed_inversion_all;
    typed_constructor; eauto using ctx_item_typed_weaken.
Qed.
Lemma funenv_typed_weaken Γ1 Γ2 m1 m2 δ Γf :
  ✓ Γ1 → (Γ1,m1) ⊢ δ : Γf → Γ1 ⊆ Γ2 → (∀ o σ, m1 ⊢ o : σ → m2 ⊢ o : σ) →
  (Γ2,m2) ⊢ δ : Γf.
Proof.
  induction 2 as [|Γf δ f s mτ τ τs Hf Hτs Hszs Hs ?? IH];
    typed_constructor; eauto using stmt_typed_weaken, types_valid_weaken.
  clear Hf Hs. induction Hτs; decompose_Forall_hyps'; constructor;
    simpl; erewrite <-1?size_of_weaken by eauto; eauto.
Qed.

Lemma funenv_lookup Γ m Γf δ f τs τ :
  ✓ Γ → (Γ,m) ⊢ δ : Γf → Γf !! f = Some (τs,τ) → ∃ s cmτ,
    δ !! f = Some s ∧
    ✓{Γ}* τs ∧ Forall (λ τ, int_typed (size_of Γ τ) sptrT) τs ∧
    (Γ,Γf,m,τs) ⊢ s : cmτ ∧ rettype_match cmτ τ.
Proof.
  induction 2 as [|Γf δ f' s' mτ' τ' τs' ?????? IH]; intros; [by simpl_map|].
  destruct (decide (f = f')) as [->|?]; simplify_map_equality.
  { exists s' mτ'; split_ands; eauto using stmt_typed_weaken, insert_subseteq. }
  destruct IH as (s&mτ&?&?&?&?&?); auto.
  exists s mτ; split_ands; eauto using stmt_typed_weaken, insert_subseteq.
Qed.
Lemma funenv_lookup_args Γ m Γf δ f τs τ :
  ✓ Γ → (Γ,m) ⊢ δ : Γf → Γf !! f = Some (τs,τ) → ✓{Γ}* τs.
Proof. intros. by destruct (funenv_lookup Γ m Γf δ f τs τ) as (?&?&?&?&_). Qed.
Lemma EVals_typed_inv Γ Γf m τs Ωs vs σs :
  length Ωs = length vs → ✓{Γ}* σs →
  (Γ,Γf,m,τs) ⊢* #{Ωs}* vs :* inr <$> σs → (Γ,m) ⊢* vs :* σs.
Proof.
  rewrite <-Forall2_same_length. intros Hvs.
  revert σs. induction Hvs; intros ? [|????] ?; decompose_Forall_hyps';
    typed_inversion_all; constructor; eauto.
Qed.
Lemma ctx_typed_stack_typed Γ Γf m k τf σf :
  (Γ,Γf,m) ⊢ k : τf ↣ σf → m ⊢* get_stack k :* get_stack_types k.
Proof.
  revert τf. induction k as [|Ek k IH]; intros; typed_inversion_all;
    repeat match goal with
    | H : (_,_,_,_) ⊢ Ek : _ ↣ _ |- _ => typed_inversion H
    end; rewrite ?fst_zip, ?snd_zip by lia; eauto using Forall2_app.
Qed.
Lemma ectx_item_subst_typed Γ Γf m τs Ei e τlr σlr :
  (Γ,Γf,m,τs) ⊢ Ei : τlr ↣ σlr →
  (Γ,Γf,m,τs) ⊢ e : τlr → (Γ,Γf,m,τs) ⊢ subst Ei e : σlr.
Proof.
  destruct 1; simpl; typed_constructor; eauto.
  rewrite ?fmap_app; eauto using Forall2_app, Forall2_cons.
Qed.
Lemma ectx_subst_typed Γ Γf m τs E e τlr σlr :
  (Γ,Γf,m,τs) ⊢ E : τlr ↣ σlr →
  (Γ,Γf,m,τs) ⊢ e : τlr → (Γ,Γf,m,τs) ⊢ subst E e : σlr.
Proof.
  intros HE. revert e. induction HE; simpl; eauto using ectx_item_subst_typed.
Qed.
Lemma ectx_item_subst_typed_rev Γ Γf m τs Ei e σlr :
  (Γ,Γf,m,τs) ⊢ subst Ei e : σlr → ∃ τlr,
    (Γ,Γf,m,τs) ⊢ e : τlr ∧ (Γ,Γf,m,τs) ⊢ Ei : τlr ↣ σlr.
Proof.
  intros He. destruct Ei; simpl; typed_inversion He;
    decompose_Forall_hyps'; simplify_list_fmap_equality;
    eexists; split; eauto; typed_constructor; eauto.
Qed.
Lemma ectx_subst_typed_rev Γ Γf m τs E e σlr :
  (Γ,Γf,m,τs) ⊢ subst E e : σlr → ∃ τlr,
    (Γ,Γf,m,τs) ⊢ e : τlr ∧ (Γ,Γf,m,τs) ⊢ E : τlr ↣ σlr.
Proof.
  revert e. induction E as [|Ei E IH]; simpl; intros e ?.
  { exists σlr. by repeat constructor. }
  edestruct (IH (subst Ei e)) as (τlr1&?&?); auto.
  destruct (ectx_item_subst_typed_rev Γ Γf m τs Ei e τlr1) as (τlr2&?&?); auto.
  exists τlr2; split; auto. typed_constructor; eauto.
Qed.
Lemma sctx_item_subst_typed Γ Γf m τs Es s cmτ cmσ :
  (Γ,Γf,m,τs) ⊢ Es : cmτ ↣ cmσ → (Γ,Γf,m,τs) ⊢ s : cmτ →
  (Γ,Γf,m,τs) ⊢ subst Es s : cmσ.
Proof. destruct 1; simpl; typed_constructor; eauto; esolve_elem_of. Qed.
Lemma sctx_item_subst_typed_rev Γ Γf m τs Es s cmσ :
  (Γ,Γf,m,τs) ⊢ subst Es s : cmσ → ∃ cmτ,
    (Γ,Γf,m,τs) ⊢ s : cmτ ∧ (Γ,Γf,m,τs) ⊢ Es : cmτ ↣ cmσ.
Proof.
  intros Hs. destruct Es; simpl; typed_inversion Hs;
    eexists; split_ands; eauto; try typed_constructor; eauto; esolve_elem_of.
Qed.
Lemma esctx_item_subst_typed Γ Γf m τs Ee e τ cmσ :
  (Γ,Γf,m,τs) ⊢ Ee : τ ↣ cmσ → (Γ,Γf,m,τs) ⊢ e : inr τ →
  (Γ,Γf,m,τs) ⊢ subst Ee e : cmσ.
Proof. destruct 1; simpl; typed_constructor; eauto. Qed.
Lemma esctx_item_subst_typed_rev Γ Γf m τs Ee e cmσ :
  (Γ,Γf,m,τs) ⊢ subst Ee e : cmσ → ∃ τ,
    (Γ,Γf,m,τs) ⊢ e : inr τ ∧ (Γ,Γf,m,τs) ⊢ Ee : τ ↣ cmσ.
Proof.
  intros He. destruct Ee; simpl; typed_inversion He;
    eexists; split_ands; eauto; typed_constructor; eauto.
Qed.
Lemma sctx_item_typed_Some_l Γ Γf m τs Es c1 τ cmτ :
  (Γ,Γf,m,τs) ⊢ Es : (c1, Some τ) ↣ cmτ → ∃ c2, cmτ = (c2, Some τ).
Proof.
  intros HEs. typed_inversion HEs; unfold rettype_union in *;
    repeat case_match; simplify_option_equality; eauto.
Qed.
Lemma Fun_type_stack_types Γ Γf m k f τf :
  (Γ,Γf,m) ⊢ k : Fun_type f ↣ τf → get_stack_types k = [].
Proof. by destruct k as [|[]]; intros; typed_inversion_all. Qed.

Lemma rettype_union_l mσ : rettype_union mσ None = Some mσ.
Proof. by destruct mσ. Qed.
End properties.
