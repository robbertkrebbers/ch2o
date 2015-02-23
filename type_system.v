(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export operations state.
Local Open Scope expr_scope.
Local Open Scope ctype_scope.

Notation lrtype K := (type K + type K)%type.
Definition lrtype_type {K} (τlr : lrtype K) : type K :=
  match τlr with inl τ | inr τ => τ end.
Notation rettype K := (bool * option (type K))%type.
Inductive focustype (K : Set) :=
  | Stmt_type : rettype K → focustype K
  | Expr_type : type K → focustype K
  | Fun_type : funname → focustype K.
Arguments Stmt_type {_} _.
Arguments Expr_type {_} _.
Arguments Fun_type {_} _.

Section typing.
Context `{Env K}.
Notation envs := (env K * memenv K * list (type K))%type.

Global Instance rettype_valid : Valid (env K) (rettype K) := λ Γ mcτ,
  match mcτ.2 with Some τ => ✓{Γ} τ | _ => True end.
Inductive lrval_typed' (Γ : env K) (Δ : memenv K) : lrval K → lrtype K → Prop :=
  | lval_typed a τ :
     (Γ,Δ) ⊢ a : TType τ → addr_strict Γ a → lrval_typed' Γ Δ (inl a) (inl τ)
  | rval_typed v τ : (Γ,Δ) ⊢ v : τ → lrval_typed' Γ Δ (inr v) (inr τ).
Global Instance lrval_typed:
  Typed (env K * memenv K) (lrtype K) (lrval K) := curry lrval_typed'.

Inductive assign_typed (Γ : env K) (τ1 : type K) :
     type K → assign → type K → Prop :=
  | Assign_typed τ2 : cast_typed Γ τ2 τ1 → assign_typed Γ τ1 τ2 Assign τ1
  | PreOp_typed op τ2 σ :
     binop_typed op τ1 τ2 σ → cast_typed Γ σ τ1 →
     assign_typed Γ τ1 τ2 (PreOp op) τ1
  | PostOp_typed op τ2 σ :
     binop_typed op τ1 τ2 σ → cast_typed Γ σ τ1 →
     assign_typed Γ τ1 τ2 (PostOp op) τ1.

Inductive expr_typed' (Γ : env K) (Δ : memenv K)
     (τs : list (type K)) : expr K → lrtype K → Prop :=
  | EVar_typed τ n :
     τs !! n = Some τ → expr_typed' Γ Δ τs (var{τ} n) (inl τ)
  | EVal_typed Ω v τ :
     ✓{Γ,Δ} Ω → (Γ,Δ) ⊢ v : τ → expr_typed' Γ Δ τs (#{Ω} v) (inr τ)
  | EAddr_typed Ω a τ :
     ✓{Γ,Δ} Ω → (Γ,Δ) ⊢ a : TType τ → addr_strict Γ a →
     expr_typed' Γ Δ τs (%{Ω} a) (inl τ)
  | ERtoL_typed e τ :
     expr_typed' Γ Δ τs e (inr (TType τ.*)) →
     type_complete Γ τ → expr_typed' Γ Δ τs (.* e) (inl τ)
  | ERofL_typed e τ :
     expr_typed' Γ Δ τs e (inl τ) →
     expr_typed' Γ Δ τs (& e) (inr (TType τ.*))
  | EAssign_typed ass e1 e2 τ1 τ2 σ :
     assign_typed Γ τ1 τ2 ass σ →
     expr_typed' Γ Δ τs e1 (inl τ1) → expr_typed' Γ Δ τs e2 (inr τ2) →
     expr_typed' Γ Δ τs (e1 ::={ass} e2) (inr σ)
  | ECall_typed e es σ σs :
     expr_typed' Γ Δ τs e (inr ((σs ~> σ).*)) →
     Forall2 (expr_typed' Γ Δ τs) es (inr <$> σs) → type_complete Γ σ →
     expr_typed' Γ Δ τs (call e @ es) (inr σ)
  | EAbort_typed τ :
     ✓{Γ} τ → expr_typed' Γ Δ τs (abort τ) (inr τ)
  | ELoad_typed e τ :
     expr_typed' Γ Δ τs e (inl τ) → expr_typed' Γ Δ τs (load e) (inr τ)
  | EEltL_typed e rs τ σ  :
     expr_typed' Γ Δ τs e (inl τ) → Γ ⊢ rs : τ ↣ σ →
     expr_typed' Γ Δ τs (e %> rs) (inl σ)
  | EEltR_typed e rs τ σ  :
     expr_typed' Γ Δ τs e (inr τ) → Γ ⊢ rs : τ ↣ σ →
     expr_typed' Γ Δ τs (e #> rs) (inr σ)
  | EAlloc_typed τ e τi :
     ✓{Γ} τ → expr_typed' Γ Δ τs e (inr (intT τi)) →
     expr_typed' Γ Δ τs (alloc{τ} e) (inr (TType τ.*))
  | EFree_typed e τ :
     expr_typed' Γ Δ τs e (inl τ) →
     expr_typed' Γ Δ τs (free e) (inr voidT)
  | EUnOp_typed op e τ σ :
     unop_typed op τ σ → expr_typed' Γ Δ τs e (inr τ) →
     expr_typed' Γ Δ τs (@{op} e) (inr σ)
  | EBinOp_typed op e1 e2 τ1 τ2 σ :
     binop_typed op τ1 τ2 σ → expr_typed' Γ Δ τs e1 (inr τ1) →
     expr_typed' Γ Δ τs e2 (inr τ2) →
     expr_typed' Γ Δ τs (e1 @{op} e2) (inr σ)
  | EIf_typed e1 e2 e3 τb σ :
     expr_typed' Γ Δ τs e1 (inr (baseT τb)) →
     expr_typed' Γ Δ τs e2 (inr σ) → expr_typed' Γ Δ τs e3 (inr σ) →
     expr_typed' Γ Δ τs (if{e1} e2 else e3) (inr σ)
  | EComma_typed e1 e2 τ1 τ2 :
     expr_typed' Γ Δ τs e1 (inr τ1) → expr_typed' Γ Δ τs e2 (inr τ2) →
     expr_typed' Γ Δ τs (e1 ,, e2) (inr τ2)
  | ECast_typed e τ σ :
     expr_typed' Γ Δ τs e (inr τ) → cast_typed Γ τ σ → 
     expr_typed' Γ Δ τs (cast{σ} e) (inr σ)
  | EInsert_typed r e1 e2 τ σ :
     Γ ⊢ r : τ ↣ σ →
     expr_typed' Γ Δ τs e1 (inr σ) → expr_typed' Γ Δ τs e2 (inr τ) →
     expr_typed' Γ Δ τs (#[r:=e1]e2) (inr τ).
Global Instance expr_typed:
  Typed envs (lrtype K) (expr K) := curry3 expr_typed'.

Section expr_typed_ind.
  Context (Γ : env K) (Δ : memenv K) (τs : list (type K)).
  Context (P : expr K → lrtype K → Prop).
  Context (Pvar : ∀ τ n, τs !! n = Some τ → P (var{τ} n) (inl τ)).
  Context (Pval : ∀ Ω v τ, ✓{Γ,Δ} Ω → (Γ,Δ) ⊢ v : τ → P (#{Ω} v) (inr τ)).
  Context (Paddr : ∀ Ω a τ,
    ✓{Γ,Δ} Ω → (Γ,Δ) ⊢ a : TType τ → addr_strict Γ a → P (%{Ω} a) (inl τ)).
  Context (Prtol : ∀ e τ,
    (Γ,Δ,τs) ⊢ e : inr (TType τ.*) → P e (inr (TType τ.*)) →
    type_complete Γ τ → P (.* e) (inl τ)).
  Context (Profl : ∀ e τ,
    (Γ,Δ,τs) ⊢ e : inl τ → P e (inl τ) → P (& e) (inr (TType τ.*))).
  Context (Passign : ∀ ass e1 e2 τ1 τ2 σ,
    assign_typed Γ τ1 τ2 ass σ → (Γ,Δ,τs) ⊢ e1 : inl τ1 → P e1 (inl τ1) →
    (Γ,Δ,τs) ⊢ e2 : inr τ2 → P e2 (inr τ2) → P (e1 ::={ass} e2) (inr σ)).
  Context (Pcall : ∀ e es σ σs,
    (Γ,Δ,τs) ⊢ e : inr ((σs ~> σ).*) → P e (inr ((σs ~> σ).*)) →
    (Γ,Δ,τs) ⊢* es :* inr <$> σs → Forall2 P es (inr <$> σs) →
    type_complete Γ σ → P (call e @ es) (inr σ)).
  Context (Pabort : ∀ τ, ✓{Γ} τ → P (abort τ) (inr τ)).
  Context (Pload : ∀ e τ,
    (Γ,Δ,τs) ⊢ e : inl τ → P e (inl τ) → P (load e) (inr τ)).
  Context (Peltl : ∀ e rs τ σ,
    (Γ,Δ,τs) ⊢ e : inl τ → P e (inl τ) → Γ ⊢ rs : τ ↣ σ → P (e %> rs) (inl σ)).
  Context (Peltr : ∀ e rs τ σ,
    (Γ,Δ,τs) ⊢ e : inr τ → P e (inr τ) → Γ ⊢ rs : τ ↣ σ → P (e #> rs) (inr σ)).
  Context (Palloc : ∀ τ e τi,
    ✓{Γ} τ → (Γ,Δ,τs) ⊢ e : inr (intT τi) →
    P e (inr (intT τi)) → P (alloc{τ} e) (inr (TType τ.*))).
  Context (Pfree : ∀ e τ,
    (Γ,Δ,τs) ⊢ e : inl τ → P e (inl τ) → P (free e) (inr voidT)).
  Context (Punop : ∀ op e τ σ,
    unop_typed op τ σ →
    (Γ,Δ,τs) ⊢ e : inr τ → P e (inr τ) → P (@{op} e) (inr σ)).
  Context (Pbinop : ∀ op e1 e2 τ1 τ2 σ,
    binop_typed op τ1 τ2 σ → (Γ,Δ,τs) ⊢ e1 : inr τ1 → P e1 (inr τ1) →
    (Γ,Δ,τs) ⊢ e2 : inr τ2 → P e2 (inr τ2) → P (e1 @{op} e2) (inr σ)).
  Context (Pif : ∀ e1 e2 e3 τb σ,
    (Γ,Δ,τs) ⊢ e1 : inr (baseT τb) → P e1 (inr (baseT τb)) →
    (Γ,Δ,τs) ⊢ e2 : inr σ → P e2 (inr σ) →
    (Γ,Δ,τs) ⊢ e3 : inr σ → P e3 (inr σ) → P (if{e1} e2 else e3) (inr σ)).
  Context (Pcomma : ∀ e1 e2 τ1 τ2,
    (Γ,Δ,τs) ⊢ e1 : inr τ1 → P e1 (inr τ1) →
    (Γ,Δ,τs) ⊢ e2 : inr τ2 → P e2 (inr τ2) → P (e1 ,, e2) (inr τ2)).
  Context (Pcast : ∀ e τ σ,
    (Γ,Δ,τs) ⊢ e : inr τ → P e (inr τ) → cast_typed Γ τ σ →
    P (cast{σ} e) (inr σ)).
  Context (Pinsert : ∀ r e1 e2 τ σ,
    Γ ⊢ r : τ ↣ σ → (Γ,Δ,τs) ⊢ e1 : inr σ → P e1 (inr σ) →
    (Γ,Δ,τs) ⊢ e2 : inr τ → P e2 (inr τ) → P (#[r:=e1]e2) (inr τ)).
  Lemma expr_typed_ind : ∀ e τ, expr_typed' Γ Δ τs e τ → P e τ.
  Proof. fix 3; destruct 1; eauto using Forall2_impl. Qed.
End expr_typed_ind.

Inductive ectx_item_typed' (Γ : env K) (Δ : memenv K)
     (τs : list (type K)) : ectx_item K → lrtype K → lrtype K → Prop :=
  | CRtoL_typed τ :
     type_complete Γ τ →
     ectx_item_typed' Γ Δ τs (.* □) (inr (TType τ.*)) (inl τ)
  | CLtoR_typed τ : ectx_item_typed' Γ Δ τs (& □) (inl τ) (inr (TType τ.*))
  | CAssignL_typed ass e2 τ1 τ2 σ :
     assign_typed Γ τ1 τ2 ass σ → (Γ,Δ,τs) ⊢ e2 : inr τ2 →
     ectx_item_typed' Γ Δ τs (□ ::={ass} e2) (inl τ1) (inr σ)
  | CAssignR_typed ass e1 τ1 τ2 σ :
     assign_typed Γ τ1 τ2 ass σ → (Γ,Δ,τs) ⊢ e1 : inl τ1 →
     ectx_item_typed' Γ Δ τs (e1 ::={ass} □) (inr τ2) (inr σ)
  | CCallL_typed es σs σ :
     (Γ,Δ,τs) ⊢* es :* inr <$> σs → type_complete Γ σ →
     ectx_item_typed' Γ Δ τs (call □ @ es) (inr ((σs ~> σ).*)) (inr σ)
  | CCallR_typed e es1 es2 σ σs1 τ σs2 :
     (Γ,Δ,τs) ⊢ e : inr (((σs1 ++ τ :: σs2) ~> σ).*) →
     (Γ,Δ,τs) ⊢* reverse es1 :* inr <$> σs1 →
     (Γ,Δ,τs) ⊢* es2 :* inr <$> σs2 → type_complete Γ σ →
     ectx_item_typed' Γ Δ τs (call e @ es1 □ es2) (inr τ) (inr σ)
  | CLoad_typed τ : ectx_item_typed' Γ Δ τs (load □) (inl τ) (inr τ)
  | CEltL_typed rs τ σ :
     Γ ⊢ rs : τ ↣ σ → ectx_item_typed' Γ Δ τs (□ %> rs) (inl τ) (inl σ)
  | CEltR_typed rs τ σ :
     Γ ⊢ rs : τ ↣ σ → ectx_item_typed' Γ Δ τs (□ #> rs) (inr τ) (inr σ)
  | CAlloc_typed τ τi :
     ✓{Γ} τ →
     ectx_item_typed' Γ Δ τs (alloc{τ} □) (inr (intT τi)) (inr (TType τ.*))
  | CFree_typed τ : ectx_item_typed' Γ Δ τs (free □) (inl τ) (inr voidT)
  | CUnOp_typed op τ σ :
     unop_typed op τ σ → ectx_item_typed' Γ Δ τs (@{op} □) (inr τ) (inr σ)
  | CBinOpL_typed op e2 τ1 τ2 σ :
     binop_typed op τ1 τ2 σ → (Γ,Δ,τs) ⊢ e2 : inr τ2 →
     ectx_item_typed' Γ Δ τs (□ @{op} e2) (inr τ1) (inr σ)
  | CBinOpR_typed op e1 τ1 τ2 σ :
     binop_typed op τ1 τ2 σ → (Γ,Δ,τs) ⊢ e1 : inr τ1 →
     ectx_item_typed' Γ Δ τs (e1 @{op} □) (inr τ2) (inr σ)
  | CIf_typed e2 e3 τb σ :
     (Γ,Δ,τs) ⊢ e2 : inr σ → (Γ,Δ,τs) ⊢ e3 : inr σ →
     ectx_item_typed' Γ Δ τs (if{□} e2 else e3) (inr (baseT τb)) (inr σ)
  | CComma_typed e2 τ1 τ2 :
     (Γ,Δ,τs) ⊢ e2 : inr τ2 →
     ectx_item_typed' Γ Δ τs (□ ,, e2) (inr τ1) (inr τ2)
  | CCast_typed τ σ :
     cast_typed Γ τ σ → ectx_item_typed' Γ Δ τs (cast{σ} □) (inr τ) (inr σ)
  | CInsertL_typed r e2 τ σ :
     Γ ⊢ r : τ ↣ σ → (Γ,Δ,τs) ⊢ e2 : inr τ →
     ectx_item_typed' Γ Δ τs (#[r:=□] e2) (inr σ) (inr τ)
  | CInsertR_typed r e1 τ σ :
     Γ ⊢ r : τ ↣ σ → (Γ,Δ,τs) ⊢ e1 : inr σ →
     ectx_item_typed' Γ Δ τs (#[r:=e1] □) (inr τ) (inr τ).

Global Instance ectx_item_typed: PathTyped envs
  (lrtype K) (lrtype K) (ectx_item K) := curry3 ectx_item_typed'.
Inductive ectx_typed' (Γs : envs) : ectx K → lrtype K → lrtype K → Prop :=
  | ectx_nil_typed_2 τ : ectx_typed' Γs [] τ τ
  | ectx_cons_typed_2 Ei E τ1 τ2 τ3 :
     Γs ⊢ Ei : τ1 ↣ τ2 → ectx_typed' Γs E τ2 τ3 →
     ectx_typed' Γs (Ei :: E) τ1 τ3.
Global Instance ectx_typed:
  PathTyped envs (lrtype K) (lrtype K) (ectx K) := ectx_typed'.

Definition rettype_union
    (mσ1 mσ2 : option (type K)) : option (option (type K)) :=
  match mσ1, mσ2 with
  | Some σ1, Some σ2 => guard (σ1 = σ2); Some (Some σ1)
  | None, _ => Some mσ2
  | _, None => Some mσ1
  end.
Definition rettype_match (cmσ : rettype K) (σ : type K) : Prop :=
  match cmσ with
  | (true, Some σ') => σ' = σ
  | (false, Some _) => False
  | (_, None) => σ = voidT
  end.

Inductive stmt_typed' (Γ : env K) (Δ : memenv K)
     (τs : list (type K)) : stmt K → rettype K → Prop :=
  | SSkip_typed : stmt_typed' Γ Δ τs skip (false,None)
  | SDo_typed e τ :
     (Γ,Δ,τs) ⊢ e : inr τ → locks e = ∅ → stmt_typed' Γ Δ τs (! e) (false,None)
  | SGoto_typed l : stmt_typed' Γ Δ τs (goto l) (true,None)
  | SThrow_typed n : stmt_typed' Γ Δ τs (throw n) (true,None)
  | SReturn_typed e τ :
     (Γ,Δ,τs) ⊢ e : inr τ → locks e = ∅ →
     stmt_typed' Γ Δ τs (ret e) (true,Some τ)
  | SLabel_typed l : stmt_typed' Γ Δ τs (label l) (false,None)
  | SLocal_typed' τ s c mσ :
     ✓{Γ} τ → stmt_typed' Γ Δ (τ :: τs) s (c,mσ) →
     stmt_typed' Γ Δ τs (local{τ} s) (c,mσ)
  | SComp_typed s1 s2 c1 mσ1 c2 mσ2 mσ :
     stmt_typed' Γ Δ τs s1 (c1,mσ1) → stmt_typed' Γ Δ τs s2 (c2,mσ2) →
     rettype_union mσ1 mσ2 = Some mσ → stmt_typed' Γ Δ τs (s1 ;; s2) (c2,mσ)
  | SCatch_typed s c mσ :
     stmt_typed' Γ Δ τs s (c,mσ) →
     stmt_typed' Γ Δ τs (catch s) (false,mσ)
  | SLoop_typed s c mσ :
     stmt_typed' Γ Δ τs s (c,mσ) →
     stmt_typed' Γ Δ τs (loop s) (true,mσ)
  | SIf_typed e τb s1 s2 c1 mσ1 c2 mσ2 mσ :
     (Γ,Δ,τs) ⊢ e : inr (baseT τb) → locks e = ∅ →
     stmt_typed' Γ Δ τs s1 (c1,mσ1) → stmt_typed' Γ Δ τs s2 (c2,mσ2) →
     rettype_union mσ1 mσ2 = Some mσ →
     stmt_typed' Γ Δ τs (if{e} s1 else s2) (c1 && c2, mσ).
Global Instance stmt_typed:
  Typed envs (rettype K) (stmt K) := curry3 stmt_typed'.

Inductive sctx_item_typed' (Γ : env K) (Δ : memenv K)
     (τs : list (type K)) : sctx_item K → relation (rettype K) :=
  | CCompL_typed s2 c1 mσ1 c2 mσ2 mσ :
     (Γ,Δ,τs) ⊢ s2 : (c2,mσ2) → rettype_union mσ1 mσ2 = Some mσ →
     sctx_item_typed' Γ Δ τs (□ ;; s2) (c1,mσ1) (c2,mσ)
  | CCompR_typed s1 c1 mσ1 c2 mσ2 mσ :
     (Γ,Δ,τs) ⊢ s1 : (c1,mσ1) → rettype_union mσ1 mσ2 = Some mσ →
     sctx_item_typed' Γ Δ τs (s1 ;; □) (c2,mσ2) (c2,mσ)
  | Ccatch_typed c mσ :
     sctx_item_typed' Γ Δ τs (catch □) (c,mσ) (false,mσ)
  | CLoop_typed c mσ :
     sctx_item_typed' Γ Δ τs (loop □) (c,mσ) (true,mσ)
  | CIfL_typed e τb s2 c1 mσ1 c2 mσ2 mσ :
     (Γ,Δ,τs) ⊢ e : inr (baseT τb) → locks e = ∅ →
     (Γ,Δ,τs) ⊢ s2 : (c2,mσ2) → rettype_union mσ1 mσ2 = Some mσ →
     sctx_item_typed' Γ Δ τs (if{e} □ else s2) (c1,mσ1) (c1&&c2,mσ)
  | CIfR_typed e τb s1 c1 mσ1 c2 mσ2 mσ :
     (Γ,Δ,τs) ⊢ e : inr (baseT τb) → locks e = ∅ →
     (Γ,Δ,τs) ⊢ s1 : (c1,mσ1) → rettype_union mσ1 mσ2 = Some mσ →
     sctx_item_typed' Γ Δ τs (if{e} s1 else □) (c2,mσ2) (c1&&c2,mσ).
Global Instance sctx_typed: PathTyped envs (rettype K)
  (rettype K) (sctx_item K) := curry3 sctx_item_typed'.

Inductive esctx_item_typed' (Γ : env K) (Δ : memenv K)
     (τs : list (type K)) : esctx_item K → type K → rettype K → Prop :=
  | CDoE_typed τ : esctx_item_typed' Γ Δ τs (! □) τ (false,None)
  | CReturnE_typed τ : esctx_item_typed' Γ Δ τs (ret □) τ (true,Some τ)
  | CIfE_typed τb s1 s2 c1 mσ1 c2 mσ2 mσ :
     (Γ,Δ,τs) ⊢ s1 : (c1,mσ1) → (Γ,Δ,τs) ⊢ s2 : (c2,mσ2) →
     rettype_union mσ1 mσ2 = Some mσ →
     esctx_item_typed' Γ Δ τs (if{□} s1 else s2)%S (baseT τb) (c1&&c2,mσ).
Global Instance esctx_item_typed: PathTyped envs (type K)
  (rettype K) (esctx_item K) := curry3 esctx_item_typed'.

Inductive ctx_item_typed'
      (Γ : env K) (Δ : memenv K) (τs : list (type K)) :
      ctx_item K → focustype K → focustype K → Prop :=
  | CStmt_typed Es cmσ1 cmσ2 :
     (Γ,Δ,τs) ⊢ Es : cmσ1 ↣ cmσ2 →
     ctx_item_typed' Γ Δ τs (CStmt Es) (Stmt_type cmσ1) (Stmt_type cmσ2)
  | CLocal_typed o τ c mσ :
     Δ ⊢ o : τ →
     ctx_item_typed' Γ Δ τs
       (CLocal o τ) (Stmt_type (c,mσ)) (Stmt_type (c,mσ))
  | CExpr_typed e Ee τ cmσ :
     (Γ,Δ,τs) ⊢ e : inr τ → locks e = ∅ → (Γ,Δ,τs) ⊢ Ee : τ ↣ cmσ →
     ctx_item_typed' Γ Δ τs (CExpr e Ee) (Expr_type τ) (Stmt_type cmσ)
  | CFun_typed E f σs τ σ :
     Γ !! f = Some (σs,τ) → (Γ,Δ,τs) ⊢ E : inr τ ↣ inr σ →
     ctx_item_typed' Γ Δ τs (CFun E) (Fun_type f) (Expr_type σ)
  | CParams_typed f σs os cmσ σ :
     Γ !! f = Some (σs, σ) → Δ ⊢* os :* σs →
     rettype_match cmσ σ → ctx_item_typed'
       Γ Δ τs (CParams f (zip os σs)) (Stmt_type cmσ) (Fun_type f).
Global Instance ctx_item_typed: PathTyped envs (focustype K)
  (focustype K) (ctx_item K) := curry3 ctx_item_typed'.
Inductive ctx_typed' (Γs : env K * memenv K) :
     ctx K → focustype K → focustype K → Prop :=
  | ctx_nil_typed_2 τf : ctx_typed' Γs [] τf τf
  | ctx_cons_typed_2 Ek k τf1 τf2 τf3 :
     (Γs,get_stack_types k) ⊢ Ek : τf1 ↣ τf2 →
     ctx_typed' Γs k τf2 τf3 → ctx_typed' Γs (Ek :: k) τf1 τf3.
Global Instance ctx_typed: PathTyped (env K * memenv K)
  (focustype K) (focustype K) (ctx K) := ctx_typed'.

Inductive direction_typed' (Γ : env K) (Δ : memenv K) :
    direction K → rettype K → Prop :=
  | Down_typed cmτ : direction_typed' Γ Δ ↘ cmτ
  | Up_typed mτ : direction_typed' Γ Δ ↗ (false,mτ)
  | Top_typed c v τ : (Γ,Δ) ⊢ v : τ → direction_typed' Γ Δ (⇈ v) (c,Some τ)
  | Goto_typed l cmτ : direction_typed' Γ Δ (↷ l) cmτ
  | Throw_typed n cmτ : direction_typed' Γ Δ (↑ n) cmτ.
Global Instance direction_typed: Typed (env K * memenv K)
  (rettype K) (direction K) := curry direction_typed'.

Inductive focus_typed' (Γ : env K) (Δ : memenv K)
    (τs : list (type K)) : focus K → focustype K → Prop :=
  | Stmt_typed d s cmσ :
     (Γ,Δ,τs) ⊢ s : cmσ → (Γ,Δ) ⊢ d : cmσ →
     focus_typed' Γ Δ τs (Stmt d s) (Stmt_type cmσ)
  | Expr_typed e τ :
     (Γ,Δ,τs) ⊢ e : inr τ → focus_typed' Γ Δ τs (Expr e) (Expr_type τ)
  | Call_typed f vs σs σ :
     Γ !! f = Some (σs,σ) → (Γ,Δ) ⊢* vs :* σs →
     focus_typed' Γ Δ τs (Call f vs) (Fun_type f)
  | Return_typed f σs σ v :
     Γ !! f = Some (σs, σ) →
     (Γ,Δ) ⊢ v : σ → focus_typed' Γ Δ τs (Return f v) (Fun_type f)
  | UndefExpr_typed E e τlr τ :
     (Γ,Δ,τs) ⊢ e : τlr → (Γ,Δ,τs) ⊢ E : τlr ↣ inr τ →
     focus_typed' Γ Δ τs (Undef (UndefExpr E e)) (Expr_type τ)
  | UndefBranch_typed Es Ω v τ mσ :
     ✓{Γ,Δ} Ω → (Γ,Δ) ⊢ v : τ → (Γ,Δ,τs) ⊢ Es : τ ↣ mσ →
     focus_typed' Γ Δ τs (Undef (UndefBranch Es Ω v)) (Stmt_type mσ).
Global Instance focus_typed:
  Typed envs (focustype K) (focus K) := curry3 focus_typed'.

Global Instance state_typed :
    Typed (env K) funname (state K) := λ Γ S f, ∃ τf,
  let 'State k φ m := S in
  (Γ,'{m},get_stack_types k) ⊢ φ : τf ∧
  (Γ,'{m}) ⊢ k : τf ↣ Fun_type f ∧
  ✓{Γ} m.

Definition funenv_prevalid (Γ : env K) (Δ : memenv K) (δ : funenv K) :=
  map_Forall (λ f s, ∃ τs τ cmτ,
    Γ !! f = Some (τs,τ) ∧ Forall (type_complete Γ) τs ∧
    (Γ,Δ,τs) ⊢ s : cmτ ∧ rettype_match cmτ τ ∧
    gotos s ⊆ labels s ∧ throws_valid 0 s
  ) δ.
Global Instance funenv_valid: Valid (env K * memenv K) (funenv K) := λ ΓΔ δ,
  let (Γ,Δ) := ΓΔ in
  funenv_prevalid Γ Δ δ ∧ dom funset (env_f Γ) ⊆ dom funset δ.
End typing.

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
Implicit Types av : lrval K.
Implicit Types Ei : ectx_item K.
Implicit Types E : ectx K.
Implicit Types Es : sctx_item K.
Implicit Types Ee : esctx_item K.
Implicit Types Ek : ctx_item K.
Implicit Types k : ctx K.
Implicit Types d : direction K.

Lemma lval_typed_inv Γ Δ a τ : (Γ,Δ) ⊢ inl a : inl τ → (Γ,Δ) ⊢ a : TType τ.
Proof. by inversion 1. Qed.
Lemma lval_typed_strict Γ Δ a τ : (Γ,Δ) ⊢ inl a : inl τ → addr_strict Γ a.
Proof. by inversion 1. Qed.
Lemma rval_typed_inv Γ Δ v τ : (Γ,Δ) ⊢ inr v : inr τ → (Γ,Δ) ⊢ v : τ.
Proof. by inversion 1. Qed.
Lemma SLocal_typed Γ Δ τs τ s c mσ :
  ✓{Γ} τ → (Γ,Δ,τ :: τs) ⊢ s : (c,mσ) → (Γ,Δ,τs) ⊢ local{τ} s : (c,mσ).
Proof. by constructor. Qed.
Lemma assign_typed_type_valid Γ τ1 τ2 ass σ :
  assign_typed Γ τ1 τ2 ass σ → ✓{Γ} τ1 → ✓{Γ} σ.
Proof. destruct 1; eauto using cast_typed_type_valid. Qed.
Lemma expr_typed_type_valid Γ Δ τs e τlr :
  ✓ Γ → ✓{Γ}* τs → (Γ,Δ,τs) ⊢ e : τlr → ✓{Γ} (lrtype_type τlr).
Proof.
  induction 3 using @expr_typed_ind; decompose_Forall_hyps;
    eauto 5 using addr_typed_type_valid, val_typed_type_valid,
    type_valid_ptr_type_valid,
    unop_typed_type_valid, binop_typed_type_valid, cast_typed_type_valid,
    TBase_valid, TPtr_valid, TVoid_valid, type_valid_ptr_type_valid,
    assign_typed_type_valid, ref_seg_typed_type_valid,
    TBase_valid_inv, TPtr_valid_inv, TFun_valid_inv_ret, type_complete_valid.
Qed.
Lemma expr_inl_typed_type_valid Γ Δ τs e τ :
  ✓ Γ → ✓{Γ}* τs → (Γ,Δ,τs) ⊢ e : inl τ → ✓{Γ} τ.
Proof. by apply expr_typed_type_valid. Qed.
Lemma expr_inr_typed_type_valid Γ Δ τs e τ :
  ✓ Γ → ✓{Γ}* τs → (Γ,Δ,τs) ⊢ e : inr τ → ✓{Γ} τ.
Proof. by apply expr_typed_type_valid. Qed.
Lemma rettype_true_Some_valid Γ β σ : ✓{Γ} σ → ✓{Γ} (β, Some σ).
Proof. done. Qed.
Lemma rettype_union_type_valid Γ mσ1 mσ2 c1 c2 mσ :
  rettype_union mσ1 mσ2 = Some mσ →
  ✓{Γ} (c1, mσ1) → ✓{Γ} (c2, mσ2) → ✓{Γ} (c2, mσ).
Proof. destruct mσ1, mσ2; intros; simplify_option_equality; eauto. Qed.
Lemma stmt_typed_type_valid Γ Δ τs s mcτ :
  ✓ Γ → ✓{Γ}* τs → (Γ,Δ,τs) ⊢ s : mcτ → ✓{Γ} mcτ.
Proof.
  by induction 3; eauto; eauto using expr_inr_typed_type_valid,
     rettype_union_type_valid, rettype_true_Some_valid.
Qed.
Lemma assign_typed_weaken Γ1 Γ2 ass τ1 τ2 σ :
  ✓ Γ1 → assign_typed Γ1 τ1 τ2 ass σ → Γ1 ⊆ Γ2 → assign_typed Γ2 τ1 τ2 ass σ.
Proof. destruct 2; econstructor; eauto using cast_typed_weaken. Qed.
Lemma expr_typed_weaken Γ1 Γ2 Δ1 Δ2 τs1 τs2 e τlr :
  ✓ Γ1 → (Γ1,Δ1,τs1) ⊢ e : τlr → Γ1 ⊆ Γ2 → Δ1 ⇒ₘ Δ2 →
  τs1 `prefix_of` τs2 → (Γ2,Δ2,τs2) ⊢ e : τlr.
Proof.
  intros ? He ?? [σs ->].
  induction He using @expr_typed_ind; typed_constructor;
    erewrite <-1?size_of_weaken by eauto; eauto using val_typed_weaken,
    assign_typed_weaken, addr_typed_weaken, addr_strict_weaken, lookup_weaken,
    type_valid_weaken, lookup_app_l_Some, cast_typed_weaken, ref_typed_weaken,
    ref_seg_typed_weaken, lockset_valid_weaken, type_complete_weaken.
Qed.
Lemma ectx_item_typed_weaken Γ1 Γ2 Δ1 Δ2 τs1 τs2 Ei τlr σlr :
  ✓ Γ1 → (Γ1,Δ1,τs1) ⊢ Ei : τlr ↣ σlr → Γ1 ⊆ Γ2 →
  Δ1 ⇒ₘ Δ2 → τs1 `prefix_of` τs2 → (Γ2,Δ2,τs2) ⊢ Ei : τlr ↣ σlr.
Proof.
  destruct 2; typed_constructor;
    eauto using type_valid_weaken, addr_strict_weaken, assign_typed_weaken,
    expr_typed_weaken, lookup_weaken, cast_typed_weaken, Forall2_impl,
    ref_seg_typed_weaken, ref_typed_weaken, type_complete_weaken.
Qed.
Lemma ectx_typed_weaken Γ1 Γ2 Δ1 Δ2 τs1 τs2 E τlr σlr :
  ✓ Γ1 → (Γ1,Δ1,τs1) ⊢ E : τlr ↣ σlr → Γ1 ⊆ Γ2 →
  Δ1 ⇒ₘ Δ2 → τs1 `prefix_of` τs2 → (Γ2,Δ2,τs2) ⊢ E : τlr ↣ σlr.
Proof.
  intros ? HE ???. revert τlr HE. induction E; intros; typed_inversion_all;
    typed_constructor; eauto using ectx_item_typed_weaken.
Qed.
Lemma stmt_typed_weaken Γ1 Γ2 Δ1 Δ2 τs1 τs2 s mτ :
  ✓ Γ1 → (Γ1,Δ1,τs1) ⊢ s : mτ → Γ1 ⊆ Γ2 → Δ1 ⇒ₘ Δ2 →
  τs1 `prefix_of` τs2 → (Γ2,Δ2,τs2) ⊢ s : mτ.
Proof.
  intros ? Hs ??. revert τs2. induction Hs; typed_constructor;
    erewrite <-1?size_of_weaken by eauto;
    eauto using expr_typed_weaken, type_valid_weaken;
    unfold typed, stmt_typed in *; simpl in *; eauto using prefix_of_cons.
Qed.
Lemma sctx_item_typed_weaken Γ1 Γ2 Δ1 Δ2 τs1 τs2 Es mτ mσ :
  ✓ Γ1 → (Γ1,Δ1,τs1) ⊢ Es : mτ ↣ mσ → Γ1 ⊆ Γ2 → Δ1 ⇒ₘ Δ2 →
  τs1 `prefix_of` τs2 → (Γ2,Δ2,τs2) ⊢ Es : mτ ↣ mσ.
Proof.
  destruct 2; typed_constructor;
    eauto using stmt_typed_weaken, expr_typed_weaken.
Qed.
Lemma esctx_item_typed_weaken Γ1 Γ2 Δ1 Δ2 τs1 τs2 Ee τ mσ :
  ✓ Γ1 → (Γ1,Δ1,τs1) ⊢ Ee : τ ↣ mσ → Γ1 ⊆ Γ2 → Δ1 ⇒ₘ Δ2 →
  τs1 `prefix_of` τs2 → (Γ2,Δ2,τs2) ⊢ Ee : τ ↣ mσ.
Proof. destruct 2; typed_constructor; eauto using stmt_typed_weaken. Qed.
Lemma ctx_item_typed_weaken Γ1 Γ2 Δ1 Δ2 τs Ek τf σf :
  ✓ Γ1 → (Γ1,Δ1,τs) ⊢ Ek : τf ↣ σf → Γ1 ⊆ Γ2 → Δ1 ⇒ₘ Δ2 →
  (Γ2,Δ2,τs) ⊢ Ek : τf ↣ σf.
Proof.
  destruct 2; typed_constructor; eauto using sctx_item_typed_weaken,
    ectx_typed_weaken, esctx_item_typed_weaken, expr_typed_weaken,
    Forall2_impl, lookup_fun_weaken, memenv_forward_typed.
Qed.
Lemma ctx_typed_weaken Γ1 Γ2 Δ1 Δ2 k τf σf :
  ✓ Γ1 → (Γ1,Δ1) ⊢ k : τf ↣ σf → Γ1 ⊆ Γ2 → Δ1 ⇒ₘ Δ2 →
  (Γ2,Δ2) ⊢ k : τf ↣ σf.
Proof.
  intros ? Hk ??. revert τf Hk. induction k; intros; typed_inversion_all;
    typed_constructor; eauto using ctx_item_typed_weaken.
Qed.
Lemma direction_typed_weaken Γ1 Γ2 Δ1 Δ2 d τf :
  ✓ Γ1 → (Γ1,Δ1) ⊢ d : τf → Γ1 ⊆ Γ2 → Δ1 ⇒ₘ Δ2 → (Γ2,Δ2) ⊢ d : τf.
Proof. destruct 2; typed_constructor; eauto using val_typed_weaken. Qed.
Lemma funenv_prevalid_weaken Γ1 Γ2 Δ1 Δ2 δ :
  ✓ Γ1 → funenv_prevalid Γ1 Δ1 δ → Γ1 ⊆ Γ2 → Δ1 ⇒ₘ Δ2 →
  funenv_prevalid Γ2 Δ2 δ.
Proof.
  intros ? Hδ ?? f s ?. destruct (Hδ f s);
    naive_solver eauto using stmt_typed_weaken, env_valid_args_valid,
    types_valid_weaken, type_valid_weaken, lookup_fun_weaken,
    types_complete_weaken, types_complete_valid.
Qed.
Lemma funenv_valid_weaken Γ Δ1 Δ2 δ :
  ✓ Γ → ✓{Γ,Δ1} δ → Δ1 ⇒ₘ Δ2 → ✓{Γ,Δ2} δ.
Proof. destruct 2; split; simpl in *; eauto using funenv_prevalid_weaken. Qed.
Lemma funenv_prevalid_empty Γ Δ : funenv_prevalid Γ Δ ∅.
Proof. by intros ??; simpl_map. Qed.
Lemma funenv_prevalid_insert Γ Δ δ f s τ τs cmτ :
  funenv_prevalid Γ Δ δ →
  Γ !! f = Some (τs, τ) → Forall (type_complete Γ) τs →
  (Γ,Δ,τs) ⊢ s : cmτ → rettype_match cmτ τ → gotos s ⊆ labels s →
  throws_valid 0 s → funenv_prevalid Γ Δ (<[f:=s]> δ).
Proof. intros ??????? f' s'; rewrite lookup_insert_Some; naive_solver. Qed.
Lemma funenv_lookup Γ Δ δ f τs τ :
  ✓ Γ → ✓{Γ,Δ} δ → Γ !! f = Some (τs,τ) → ∃ s cmτ,
    δ !! f = Some s ∧ Forall (type_complete Γ) τs ∧
    (Γ,Δ,τs) ⊢ s : cmτ ∧ rettype_match cmτ τ ∧
    gotos s ⊆ labels s ∧ throws_valid 0 s.
Proof.
  intros ? [Hδ HΓf] ?; simpl in *. assert (∃ s, δ !! f = Some s) as [s ?].
  { apply elem_of_dom, HΓf, elem_of_dom; eauto. }
  destruct (Hδ f s) as (?&?&?&?&?); simplify_equality; eauto.
Qed.
Lemma funenv_lookup_inv Γ Δ δ f s :
  ✓ Γ → ✓{Γ,Δ} δ → δ !! f = Some s → ∃ τs τ cmτ,
    Γ !! f = Some (τs,τ) ∧ (Γ,Δ,τs) ⊢ s : cmτ ∧ rettype_match cmτ τ ∧
    gotos s ⊆ labels s ∧ throws_valid 0 s.
Proof. intros ? [Hδ _] ?. destruct (Hδ f s); naive_solver. Qed.
Lemma funenv_lookup_gotos Γ Δ δ f s :
  ✓ Γ → ✓{Γ,Δ} δ → δ !! f = Some s → gotos s ⊆ labels s.
Proof.
  intros. by destruct (funenv_lookup_inv Γ Δ δ f s) as (?&?&?&?&?&?&?&?).
Qed.
Lemma funenv_lookup_throws Γ Δ δ f s :
  ✓ Γ → ✓{Γ,Δ} δ → δ !! f = Some s → throws_valid 0 s.
Proof.
  intros. by destruct (funenv_lookup_inv Γ Δ δ f s) as (?&?&?&?&?&?&?&?).
Qed.

Lemma EVals_typed Γ Δ τs Ωs vs σs :
  length Ωs = length vs → ✓{Γ,Δ}* Ωs → (Γ,Δ) ⊢* vs :* σs →
  (Γ,Δ,τs) ⊢* #{Ωs}* vs :* inr <$> σs.
Proof.
  rewrite <-Forall2_same_length. intros Hvs ?. revert σs.
  induction Hvs; intros [|??] ?; decompose_Forall_hyps;
    repeat constructor; auto.
Qed.
Lemma EVals_typed_inv Γ Δ τs Ωs vs σs :
  length Ωs = length vs →
  (Γ,Δ,τs) ⊢* #{Ωs}* vs :* inr <$> σs → (Γ,Δ) ⊢* vs :* σs.
Proof.
  rewrite <-Forall2_same_length. intros Hvs. revert σs.
  induction Hvs; intros [|??] ?; decompose_Forall_hyps;
    typed_inversion_all; constructor; auto.
Qed.
Lemma ctx_typed_stack_typed Γ Δ k τf σf :
  (Γ,Δ) ⊢ k : τf ↣ σf → Δ ⊢* get_stack k :* get_stack_types k.
Proof.
  revert τf. induction k as [|Ek k IH]; intros; typed_inversion_all; eauto;
    repeat match goal with
    | H : (_,_,_) ⊢ Ek : _ ↣ _ |- _ => typed_inversion H
    | H : Forall2 _ ?l ?l' |- _ =>
       unless (length l = length l') by done;
       assert (length l = length l') by eauto using Forall2_length
    end; rewrite ?fst_zip, ?snd_zip by lia; eauto using Forall2_app.
Qed.
Lemma ectx_item_subst_typed Γ Δ τs Ei e τlr σlr :
  (Γ,Δ,τs) ⊢ Ei : τlr ↣ σlr →
  (Γ,Δ,τs) ⊢ e : τlr → (Γ,Δ,τs) ⊢ subst Ei e : σlr.
Proof.
  destruct 1; simpl; typed_constructor; eauto.
  rewrite ?fmap_app; eauto using Forall2_app, Forall2_cons.
Qed.
Lemma ectx_subst_typed Γ Δ τs E e τlr σlr :
  (Γ,Δ,τs) ⊢ E : τlr ↣ σlr →
  (Γ,Δ,τs) ⊢ e : τlr → (Γ,Δ,τs) ⊢ subst E e : σlr.
Proof.
  intros HE. revert e. induction HE; simpl; eauto using ectx_item_subst_typed.
Qed.
Lemma ectx_item_subst_typed_rev Γ Δ τs Ei e σlr :
  (Γ,Δ,τs) ⊢ subst Ei e : σlr →
  ∃ τlr, (Γ,Δ,τs) ⊢ e : τlr ∧ (Γ,Δ,τs) ⊢ Ei : τlr ↣ σlr.
Proof.
  intros He. destruct Ei; typed_inversion He;
    list_simplifier; eexists; split_ands; repeat typed_constructor; eauto.
Qed.
Lemma ectx_subst_typed_rev Γ Δ τs E e σlr :
  (Γ,Δ,τs) ⊢ subst E e : σlr →
  ∃ τlr, (Γ,Δ,τs) ⊢ e : τlr ∧ (Γ,Δ,τs) ⊢ E : τlr ↣ σlr.
Proof.
  revert e. induction E as [|Ei E IH]; simpl; intros e ?.
  { exists σlr. by repeat constructor. }
  edestruct (IH (subst Ei e)) as (τlr1&?&?); auto.
  destruct (ectx_item_subst_typed_rev Γ Δ τs Ei e τlr1) as (τlr2&?&?); auto.
  exists τlr2; split; auto. typed_constructor; eauto.
Qed.
Lemma sctx_item_subst_typed Γ Δ τs Es s cmτ cmσ :
  (Γ,Δ,τs) ⊢ Es : cmτ ↣ cmσ → (Γ,Δ,τs) ⊢ s : cmτ →
  (Γ,Δ,τs) ⊢ subst Es s : cmσ.
Proof. destruct 1; simpl; typed_constructor; eauto; esolve_elem_of. Qed.
Lemma sctx_item_subst_typed_rev Γ Δ τs Es s cmσ :
  (Γ,Δ,τs) ⊢ subst Es s : cmσ →
  ∃ cmτ, (Γ,Δ,τs) ⊢ s : cmτ ∧ (Γ,Δ,τs) ⊢ Es : cmτ ↣ cmσ.
Proof.
  intros Hs. destruct Es; simpl; typed_inversion Hs;
    eexists; split_ands; repeat typed_constructor; eauto.
Qed.
Lemma esctx_item_subst_typed Γ Δ τs Ee e τ cmσ :
  (Γ,Δ,τs) ⊢ Ee : τ ↣ cmσ → (Γ,Δ,τs) ⊢ e : inr τ → locks e = ∅ →
  (Γ,Δ,τs) ⊢ subst Ee e : cmσ.
Proof. destruct 1; simpl; typed_constructor; eauto. Qed.
Lemma esctx_item_subst_typed_rev Γ Δ τs Ee e cmσ :
  (Γ,Δ,τs) ⊢ subst Ee e : cmσ →
  ∃ τ, (Γ,Δ,τs) ⊢ e : inr τ ∧ locks e = ∅ ∧ (Γ,Δ,τs) ⊢ Ee : τ ↣ cmσ.
Proof.
  intros He. destruct Ee; simpl; typed_inversion He;
    eexists; split_ands; repeat typed_constructor; eauto.
Qed.
Lemma sctx_item_typed_Some_l Γ Δ τs Es c1 τ cmτ :
  (Γ,Δ,τs) ⊢ Es : (c1,Some τ) ↣ cmτ → ∃ c2, cmτ = (c2, Some τ).
Proof.
  intros HEs. typed_inversion HEs; unfold rettype_union in *;
    repeat case_match; simplify_option_equality; eauto.
Qed.
Lemma Fun_type_stack_types Γ Δ k f τf :
  (Γ,Δ) ⊢ k : Fun_type f ↣ τf → get_stack_types k = [].
Proof. by destruct k as [|[]]; intros; typed_inversion_all. Qed.
Lemma rettype_union_l mσ : rettype_union mσ None = Some mσ.
Proof. by destruct mσ. Qed.
Lemma rettype_union_r mσ : rettype_union None mσ = Some mσ.
Proof. by destruct mσ. Qed.
Lemma rettype_union_idempotent mσ : rettype_union mσ mσ = Some mσ.
Proof. by destruct mσ; simplify_option_equality. Qed.

Lemma expr_typed_lift Γ Δ τs e τlr :
  (Γ,Δ,τs) ⊢ e↑ : τlr ↔ (Γ,Δ,tail τs) ⊢ e : τlr.
Proof.
  split.
  * assert (∀ es σs,
      Forall (λ e, ∀ τlr, (Γ,Δ,τs) ⊢ e↑ : τlr → (Γ,Δ,tail τs) ⊢ e : τlr) es →
      (Γ,Δ,τs) ⊢* expr_lift <$> es :* inr <$> σs →
      (Γ,Δ,tail τs) ⊢* es :* inr <$> σs).
    { intros es σs. rewrite Forall2_fmap.
      induction 2; decompose_Forall_hyps; eauto. }
    revert τlr. induction e using @expr_ind_alt; csimpl; intros τlr He;
      typed_inversion He; typed_constructor; rewrite ?lookup_tail; eauto.
  * induction 1 using @expr_typed_ind; csimpl;
      typed_constructor; rewrite <-?lookup_tail; eauto.
    by apply Forall2_fmap_l.
Qed.
Lemma expr_typed_var_free Γ Δ τs1 τs2 e τlr :
  vars e = ∅ → (Γ,Δ,τs1) ⊢ e : τlr → (Γ,Δ,τs2) ⊢ e : τlr.
Proof.
  assert (∀ es σs, ⋃ (vars <$> es) = ∅ →
    Forall2 (λ e τlr, vars e = ∅ → (Γ,Δ,τs2) ⊢ e : τlr) es (inr <$> σs) →
    (Γ,Δ,τs2) ⊢* es :* inr <$> σs).
  { induction 2; simplify_equality'; decompose_empty; eauto. }
  induction 2 using @expr_typed_ind; simplify_equality';
    decompose_empty; typed_constructor; eauto.
Qed.
End properties.
