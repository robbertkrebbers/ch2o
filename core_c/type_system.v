(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
From stdpp Require Import fin_map_dom.
Require Export operations state.

Local Open Scope expr_scope.
Local Open Scope ctype_scope.

Notation lrtype K := (ptr_type K + type K)%type.
Notation rettype K := (bool * option (type K))%type.
Inductive focustype (K : iType) : iType :=
  | Stmt_type : rettype K → focustype K
  | Expr_type : type K → focustype K
  | Fun_type : funname → focustype K.
Arguments Stmt_type {_} _.
Arguments Expr_type {_} _.
Arguments Fun_type {_} _.

Section typing.
Context `{Env K}.
Notation envs := (env K * memenv K * list (type K))%type.

#[global] Instance stack_item_valid : Valid (memenv K) (index * type K) := λ Δ oτ,
  Δ ⊢ oτ.1 : oτ.2.
#[global] Instance rettype_valid : Valid (env K) (rettype K) := λ Γ mcτ,
  match mcτ.2 with Some τ => ✓{Γ} τ | _ => True end.

Inductive lrtype_valid' (Γ : env K) : lrtype K → Prop :=
  | ltype_valid τp : ✓{Γ} τp → lrtype_valid' Γ (inl τp)
  | rtype_valid τ : ✓{Γ} τ → lrtype_valid' Γ (inr τ).
#[global] Instance lrtype_valid : Valid (env K) (lrtype K) := lrtype_valid'.
Inductive lrval_typed' (Γ : env K) (Δ : memenv K) : lrval K → lrtype K → Prop :=
  | lval_typed p τp : (Γ,Δ) ⊢ p : τp → lrval_typed' Γ Δ (inl p) (inl τp)
  | rval_typed v τ : (Γ,Δ) ⊢ v : τ → lrval_typed' Γ Δ (inr v) (inr τ).
#[global] Instance lrval_typed:
  Typed (env K * memenv K) (lrtype K) (lrval K) := uncurry lrval_typed'.

Inductive expr_typed' (Γ : env K) (Δ : memenv K)
     (τs : list (type K)) : expr K → lrtype K → Prop :=
  | EVar_typed τ i :
     τs !! i = Some τ → expr_typed' Γ Δ τs (var i) (inl (TType τ))
  | EVal_typed Ω ν τlr :
     ✓{Γ,Δ} Ω → (Γ,Δ) ⊢ ν : τlr → expr_typed' Γ Δ τs (%#{Ω} ν) τlr
  | ERtoL_typed e τp :
     expr_typed' Γ Δ τs e (inr (τp.*)) →
     expr_typed' Γ Δ τs (.* e) (inl τp)
  | ERofL_typed e τp :
     expr_typed' Γ Δ τs e (inl τp) →
     expr_typed' Γ Δ τs (& e) (inr (τp.*))
  | EAssign_typed ass e1 e2 τ1 τ2 :
     assign_typed τ1 τ2 ass →
     expr_typed' Γ Δ τs e1 (inl (TType τ1)) → expr_typed' Γ Δ τs e2 (inr τ2) →
     expr_typed' Γ Δ τs (e1 ::={ass} e2) (inr τ1)
  | ECall_typed e es σ σs :
     expr_typed' Γ Δ τs e (inl (σs ~> σ)) →
     Forall2 (expr_typed' Γ Δ τs) es (inr <$> σs) → type_complete Γ σ →
     expr_typed' Γ Δ τs (call e @ es) (inr σ)
  | EAbort_typed τ :
     ✓{Γ} τ → expr_typed' Γ Δ τs (abort τ) (inr τ)
  | ELoad_typed e τ :
     expr_typed' Γ Δ τs e (inl (TType τ)) → type_complete Γ τ →
     expr_typed' Γ Δ τs (load e) (inr τ)
  | EEltL_typed e rs τ σ  :
     expr_typed' Γ Δ τs e (inl (TType τ)) → Γ ⊢ rs : τ ↣ σ →
     expr_typed' Γ Δ τs (e %> rs) (inl (TType σ))
  | EEltR_typed e rs τ σ  :
     expr_typed' Γ Δ τs e (inr τ) → Γ ⊢ rs : τ ↣ σ →
     expr_typed' Γ Δ τs (e #> rs) (inr σ)
  | EAlloc_typed τ e τi :
     ✓{Γ} τ → expr_typed' Γ Δ τs e (inr (intT τi)) →
     expr_typed' Γ Δ τs (alloc{τ} e) (inl (TType τ))
  | EFree_typed e τp :
     expr_typed' Γ Δ τs e (inl τp) →
     expr_typed' Γ Δ τs (free e) (inr voidT)
  | EUnOp_typed op e τ σ :
     unop_typed op τ σ → expr_typed' Γ Δ τs e (inr τ) →
     expr_typed' Γ Δ τs (.{op} e) (inr σ)
  | EBinOp_typed op e1 e2 τ1 τ2 σ :
     binop_typed op τ1 τ2 σ → expr_typed' Γ Δ τs e1 (inr τ1) →
     expr_typed' Γ Δ τs e2 (inr τ2) →
     expr_typed' Γ Δ τs (e1 .{op} e2) (inr σ)
  | EIf_typed e1 e2 e3 τb σlr :
     expr_typed' Γ Δ τs e1 (inr (baseT τb)) → τb ≠ TVoid →
     expr_typed' Γ Δ τs e2 σlr → expr_typed' Γ Δ τs e3 σlr →
     expr_typed' Γ Δ τs (if{e1} e2 else e3) σlr
  | EComma_typed e1 e2 τlr1 τlr2 :
     expr_typed' Γ Δ τs e1 τlr1 → expr_typed' Γ Δ τs e2 τlr2 →
     expr_typed' Γ Δ τs (e1 ,, e2) τlr2
  | ECast_typed e τ σ :
     expr_typed' Γ Δ τs e (inr τ) → cast_typed τ σ → ✓{Γ} σ →
     expr_typed' Γ Δ τs (cast{σ} e) (inr σ)
  | EInsert_typed r e1 e2 τ σ :
     Γ ⊢ r : τ ↣ σ →
     expr_typed' Γ Δ τs e1 (inr σ) → expr_typed' Γ Δ τs e2 (inr τ) →
     expr_typed' Γ Δ τs (#[r:=e1]e2) (inr τ).
#[global] Instance expr_typed:
  Typed envs (lrtype K) (expr K) := uncurry3 expr_typed'.

Section expr_typed_ind.
  Context (Γ : env K) (Δ : memenv K) (τs : list (type K)).
  Context (P : expr K → lrtype K → Prop).
  Context (Pvar : ∀ τ i, τs !! i = Some τ → P (var i) (inl (TType τ))).
  Context (Pval : ∀ Ω ν τlr, ✓{Γ,Δ} Ω → (Γ,Δ) ⊢ ν : τlr → P (%#{Ω} ν) τlr).
  Context (Prtol : ∀ e τp,
    (Γ,Δ,τs) ⊢ e : inr (τp.*) → P e (inr (τp.*)) → P (.* e) (inl τp)).
  Context (Profl : ∀ e τp,
    (Γ,Δ,τs) ⊢ e : inl τp → P e (inl τp) → P (& e) (inr (τp.*))).
  Context (Passign : ∀ ass e1 e2 τ1 τ2,
    assign_typed τ1 τ2 ass →
    (Γ,Δ,τs) ⊢ e1 : inl (TType τ1) → P e1 (inl (TType τ1)) →
    (Γ,Δ,τs) ⊢ e2 : inr τ2 → P e2 (inr τ2) → P (e1 ::={ass} e2) (inr τ1)).
  Context (Pcall : ∀ e es σ σs,
    (Γ,Δ,τs) ⊢ e : inl (σs ~> σ) → P e (inl (σs ~> σ)) →
    (Γ,Δ,τs) ⊢* es :* inr <$> σs → Forall2 P es (inr <$> σs) →
    type_complete Γ σ → P (call e @ es) (inr σ)).
  Context (Pabort : ∀ τ, ✓{Γ} τ → P (abort τ) (inr τ)).
  Context (Pload : ∀ e τ,
    (Γ,Δ,τs) ⊢ e : inl (TType τ) → type_complete Γ τ →
    P e (inl (TType τ)) → P (load e) (inr τ)).
  Context (Peltl : ∀ e rs τ σ,
    (Γ,Δ,τs) ⊢ e : inl (TType τ) → P e (inl (TType τ)) →
    Γ ⊢ rs : τ ↣ σ → P (e %> rs) (inl (TType σ))).
  Context (Peltr : ∀ e rs τ σ,
    (Γ,Δ,τs) ⊢ e : inr τ → P e (inr τ) → Γ ⊢ rs : τ ↣ σ → P (e #> rs) (inr σ)).
  Context (Palloc : ∀ τ e τi,
    ✓{Γ} τ → (Γ,Δ,τs) ⊢ e : inr (intT τi) →
    P e (inr (intT τi)) → P (alloc{τ} e) (inl (TType τ))).
  Context (Pfree : ∀ e τp,
    (Γ,Δ,τs) ⊢ e : inl τp → P e (inl τp) → P (free e) (inr voidT)).
  Context (Punop : ∀ op e τ σ,
    unop_typed op τ σ →
    (Γ,Δ,τs) ⊢ e : inr τ → P e (inr τ) → P (.{op} e) (inr σ)).
  Context (Pbinop : ∀ op e1 e2 τ1 τ2 σ,
    binop_typed op τ1 τ2 σ → (Γ,Δ,τs) ⊢ e1 : inr τ1 → P e1 (inr τ1) →
    (Γ,Δ,τs) ⊢ e2 : inr τ2 → P e2 (inr τ2) → P (e1 .{op} e2) (inr σ)).
  Context (Pif : ∀ e1 e2 e3 τb σlr,
    (Γ,Δ,τs) ⊢ e1 : inr (baseT τb) → P e1 (inr (baseT τb)) → τb ≠ TVoid →
    (Γ,Δ,τs) ⊢ e2 : σlr → P e2 σlr →
    (Γ,Δ,τs) ⊢ e3 : σlr → P e3 σlr → P (if{e1} e2 else e3) σlr).
  Context (Pcomma : ∀ e1 e2 τlr1 τlr2,
    (Γ,Δ,τs) ⊢ e1 : τlr1 → P e1 τlr1 →
    (Γ,Δ,τs) ⊢ e2 : τlr2 → P e2 τlr2 → P (e1 ,, e2) τlr2).
  Context (Pcast : ∀ e τ σ,
    (Γ,Δ,τs) ⊢ e : inr τ → P e (inr τ) → cast_typed τ σ → ✓{Γ} σ →
    P (cast{σ} e) (inr σ)).
  Context (Pinsert : ∀ r e1 e2 τ σ,
    Γ ⊢ r : τ ↣ σ → (Γ,Δ,τs) ⊢ e1 : inr σ → P e1 (inr σ) →
    (Γ,Δ,τs) ⊢ e2 : inr τ → P e2 (inr τ) → P (#[r:=e1]e2) (inr τ)).
  Lemma expr_typed_ind : ∀ e τ, expr_typed' Γ Δ τs e τ → P e τ.
  Proof. fix H'3 3; destruct 1; eauto using Forall2_impl. Qed.
End expr_typed_ind.

Inductive ectx_item_typed' (Γ : env K) (Δ : memenv K)
     (τs : list (type K)) : ectx_item K → lrtype K → lrtype K → Prop :=
  | CRtoL_typed τp :
     ectx_item_typed' Γ Δ τs (.* □) (inr (τp.*)) (inl τp)
  | CLtoR_typed τp : ectx_item_typed' Γ Δ τs (& □) (inl τp) (inr (τp.*))
  | CAssignL_typed ass e2 τ1 τ2 :
     assign_typed τ1 τ2 ass → (Γ,Δ,τs) ⊢ e2 : inr τ2 →
     ectx_item_typed' Γ Δ τs (□ ::={ass} e2) (inl (TType τ1)) (inr τ1)
  | CAssignR_typed ass e1 τ1 τ2 :
     assign_typed τ1 τ2 ass → (Γ,Δ,τs) ⊢ e1 : inl (TType τ1) →
     ectx_item_typed' Γ Δ τs (e1 ::={ass} □) (inr τ2) (inr τ1)
  | CCallL_typed es σs σ :
     (Γ,Δ,τs) ⊢* es :* inr <$> σs → type_complete Γ σ →
     ectx_item_typed' Γ Δ τs (call □ @ es) (inl (σs ~> σ)) (inr σ)
  | CCallR_typed e es1 es2 σ σs1 τ σs2 :
     (Γ,Δ,τs) ⊢ e : inl ((σs1 ++ τ :: σs2) ~> σ) →
     (Γ,Δ,τs) ⊢* reverse es1 :* inr <$> σs1 →
     (Γ,Δ,τs) ⊢* es2 :* inr <$> σs2 → type_complete Γ σ →
     ectx_item_typed' Γ Δ τs (call e @ es1 □ es2) (inr τ) (inr σ)
  | CLoad_typed τ :
     type_complete Γ τ →
     ectx_item_typed' Γ Δ τs (load □) (inl (TType τ)) (inr τ)
  | CEltL_typed rs τ σ :
     Γ ⊢ rs : τ ↣ σ →
     ectx_item_typed' Γ Δ τs (□ %> rs) (inl (TType τ)) (inl (TType σ))
  | CEltR_typed rs τ σ :
     Γ ⊢ rs : τ ↣ σ → ectx_item_typed' Γ Δ τs (□ #> rs) (inr τ) (inr σ)
  | CAlloc_typed τ τi :
     ✓{Γ} τ →
     ectx_item_typed' Γ Δ τs (alloc{τ} □) (inr (intT τi)) (inl (TType τ))
  | CFree_typed τp : ectx_item_typed' Γ Δ τs (free □) (inl τp) (inr voidT)
  | CUnOp_typed op τ σ :
     unop_typed op τ σ → ectx_item_typed' Γ Δ τs (.{op} □) (inr τ) (inr σ)
  | CBinOpL_typed op e2 τ1 τ2 σ :
     binop_typed op τ1 τ2 σ → (Γ,Δ,τs) ⊢ e2 : inr τ2 →
     ectx_item_typed' Γ Δ τs (□ .{op} e2) (inr τ1) (inr σ)
  | CBinOpR_typed op e1 τ1 τ2 σ :
     binop_typed op τ1 τ2 σ → (Γ,Δ,τs) ⊢ e1 : inr τ1 →
     ectx_item_typed' Γ Δ τs (e1 .{op} □) (inr τ2) (inr σ)
  | CIf_typed e2 e3 τb σlr :
     τb ≠ TVoid → (Γ,Δ,τs) ⊢ e2 : σlr → (Γ,Δ,τs) ⊢ e3 : σlr →
     ectx_item_typed' Γ Δ τs (if{□} e2 else e3) (inr (baseT τb)) σlr
  | CComma_typed e2 τlr1 τlr2 :
     (Γ,Δ,τs) ⊢ e2 : τlr2 → ectx_item_typed' Γ Δ τs (□ ,, e2) τlr1 τlr2
  | CCast_typed τ σ :
     cast_typed τ σ → ✓{Γ} σ →
     ectx_item_typed' Γ Δ τs (cast{σ} □) (inr τ) (inr σ)
  | CInsertL_typed r e2 τ σ :
     Γ ⊢ r : τ ↣ σ → (Γ,Δ,τs) ⊢ e2 : inr τ →
     ectx_item_typed' Γ Δ τs (#[r:=□] e2) (inr σ) (inr τ)
  | CInsertR_typed r e1 τ σ :
     Γ ⊢ r : τ ↣ σ → (Γ,Δ,τs) ⊢ e1 : inr σ →
     ectx_item_typed' Γ Δ τs (#[r:=e1] □) (inr τ) (inr τ).

#[global] Instance ectx_item_typed: PathTyped envs
  (lrtype K) (lrtype K) (ectx_item K) := uncurry3 ectx_item_typed'.
Inductive ectx_typed' (Γs : envs) : ectx K → lrtype K → lrtype K → Prop :=
  | ectx_nil_typed_2 τ : ectx_typed' Γs [] τ τ
  | ectx_cons_typed_2 Ei E τ1 τ2 τ3 :
     Γs ⊢ Ei : τ1 ↣ τ2 → ectx_typed' Γs E τ2 τ3 →
     ectx_typed' Γs (Ei :: E) τ1 τ3.
#[global] Instance ectx_typed:
  PathTyped envs (lrtype K) (lrtype K) (ectx K) := ectx_typed'.

Inductive rettype_union :
      option (type K) → option (type K) → option (type K) → Prop :=
  | rettype_union_idempotent mσ : rettype_union mσ mσ mσ
  | rettype_union_Some_r σ : rettype_union None (Some σ) (Some σ)
  | rettype_union_Some_l σ : rettype_union (Some σ) None (Some σ).
Inductive rettype_match : rettype K → type K → Prop :=
  | rettype_match_true_Some σ : rettype_match (true, Some σ) σ
  | rettype_match_false_Some : rettype_match (false, Some voidT) voidT
  | rettype_match_true_None σ : rettype_match (true, None) σ
  | rettype_match_false_None : rettype_match (false, None) voidT.
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
  | SCase_typed mx : stmt_typed' Γ Δ τs (scase mx) (false,None)
  | SLabel_typed l : stmt_typed' Γ Δ τs (label l) (false,None)
  | SLocal_typed' τ s c mσ :
     ✓{Γ} τ → stmt_typed' Γ Δ (τ :: τs) s (c,mσ) →
     stmt_typed' Γ Δ τs (local{τ} s) (c,mσ)
  | SComp_typed s1 s2 c1 mσ1 c2 mσ2 mσ :
     stmt_typed' Γ Δ τs s1 (c1,mσ1) → stmt_typed' Γ Δ τs s2 (c2,mσ2) →
     rettype_union mσ1 mσ2 mσ → stmt_typed' Γ Δ τs (s1 ;; s2) (c2,mσ)
  | SCatch_typed s c mσ :
     stmt_typed' Γ Δ τs s (c,mσ) →
     stmt_typed' Γ Δ τs (catch s) (false,mσ)
  | SLoop_typed s c mσ :
     stmt_typed' Γ Δ τs s (c,mσ) →
     stmt_typed' Γ Δ τs (loop s) (true,mσ)
  | SIf_typed e τb s1 s2 c1 mσ1 c2 mσ2 mσ :
     (Γ,Δ,τs) ⊢ e : inr (baseT τb) → τb ≠ TVoid → locks e = ∅ →
     stmt_typed' Γ Δ τs s1 (c1,mσ1) → stmt_typed' Γ Δ τs s2 (c2,mσ2) →
     rettype_union mσ1 mσ2 mσ →
     stmt_typed' Γ Δ τs (if{e} s1 else s2) (c1 && c2, mσ)
  | SSwitch_typed e τi s c mσ :
     (Γ,Δ,τs) ⊢ e : inr (intT τi) → locks e = ∅ →
     stmt_typed' Γ Δ τs s (c,mσ) → stmt_typed' Γ Δ τs (switch{e} s) (false,mσ)
     .
#[global] Instance stmt_typed:
  Typed envs (rettype K) (stmt K) := uncurry3 stmt_typed'.

Inductive sctx_item_typed' (Γ : env K) (Δ : memenv K)
     (τs : list (type K)) : sctx_item K → relation (rettype K) :=
  | CCompL_typed s2 c1 mσ1 c2 mσ2 mσ :
     (Γ,Δ,τs) ⊢ s2 : (c2,mσ2) → rettype_union mσ1 mσ2 mσ →
     sctx_item_typed' Γ Δ τs (□ ;; s2) (c1,mσ1) (c2,mσ)
  | CCompR_typed s1 c1 mσ1 c2 mσ2 mσ :
     (Γ,Δ,τs) ⊢ s1 : (c1,mσ1) → rettype_union mσ1 mσ2 mσ →
     sctx_item_typed' Γ Δ τs (s1 ;; □) (c2,mσ2) (c2,mσ)
  | Ccatch_typed c mσ :
     sctx_item_typed' Γ Δ τs (catch □) (c,mσ) (false,mσ)
  | CLoop_typed c mσ :
     sctx_item_typed' Γ Δ τs (loop □) (c,mσ) (true,mσ)
  | CIfL_typed e τb s2 c1 mσ1 c2 mσ2 mσ :
     (Γ,Δ,τs) ⊢ e : inr (baseT τb) → τb ≠ TVoid → locks e = ∅ →
     (Γ,Δ,τs) ⊢ s2 : (c2,mσ2) → rettype_union mσ1 mσ2 mσ →
     sctx_item_typed' Γ Δ τs (if{e} □ else s2) (c1,mσ1) (c1&&c2,mσ)
  | CIfR_typed e τb s1 c1 mσ1 c2 mσ2 mσ :
     (Γ,Δ,τs) ⊢ e : inr (baseT τb) → τb ≠ TVoid → locks e = ∅ →
     (Γ,Δ,τs) ⊢ s1 : (c1,mσ1) → rettype_union mσ1 mσ2 mσ →
     sctx_item_typed' Γ Δ τs (if{e} s1 else □) (c2,mσ2) (c1&&c2,mσ)
  | CSWitch_typed e τi c mσ :
     (Γ,Δ,τs) ⊢ e : inr (intT τi) → locks e = ∅ →
     sctx_item_typed' Γ Δ τs (switch{e} □) (c,mσ) (false,mσ).
#[global] Instance sctx_typed: PathTyped envs (rettype K)
  (rettype K) (sctx_item K) := uncurry3 sctx_item_typed'.

Inductive esctx_item_typed' (Γ : env K) (Δ : memenv K)
     (τs : list (type K)) : esctx_item K → type K → rettype K → Prop :=
  | CDoE_typed τ : esctx_item_typed' Γ Δ τs (! □) τ (false,None)
  | CReturnE_typed τ : esctx_item_typed' Γ Δ τs (ret □) τ (true,Some τ)
  | CIfE_typed τb s1 s2 c1 mσ1 c2 mσ2 mσ :
     τb ≠ TVoid → (Γ,Δ,τs) ⊢ s1 : (c1,mσ1) → (Γ,Δ,τs) ⊢ s2 : (c2,mσ2) →
     rettype_union mσ1 mσ2 mσ →
     esctx_item_typed' Γ Δ τs (if{□} s1 else s2)%S (baseT τb) (c1&&c2,mσ)
  | CSwitchE_typed τi s c mσ :
     (Γ,Δ,τs) ⊢ s : (c,mσ) →
     esctx_item_typed' Γ Δ τs (switch{□} s) (intT τi) (false,mσ).
#[global] Instance esctx_item_typed: PathTyped envs (type K)
  (rettype K) (esctx_item K) := uncurry3 esctx_item_typed'.

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
#[global] Instance ctx_item_typed: PathTyped envs (focustype K)
  (focustype K) (ctx_item K) := uncurry3 ctx_item_typed'.
Inductive ctx_typed' (Γs : env K * memenv K) :
     ctx K → focustype K → focustype K → Prop :=
  | ctx_nil_typed_2 τf : ctx_typed' Γs [] τf τf
  | ctx_cons_typed_2 Ek k τf1 τf2 τf3 :
     (Γs,(locals k).*2) ⊢ Ek : τf1 ↣ τf2 →
     ctx_typed' Γs k τf2 τf3 → ctx_typed' Γs (Ek :: k) τf1 τf3.
#[global] Instance ctx_typed: PathTyped (env K * memenv K)
  (focustype K) (focustype K) (ctx K) := ctx_typed'.

Inductive direction_typed' (Γ : env K) (Δ : memenv K) :
     direction K → rettype K → Prop :=
  | Down_typed cmτ : direction_typed' Γ Δ ↘ cmτ
  | Up_typed mτ : direction_typed' Γ Δ ↗ (false,mτ)
  | Top_typed c v τ : (Γ,Δ) ⊢ v : τ → direction_typed' Γ Δ (⇈ v) (c,Some τ)
  | Goto_typed l cmτ : direction_typed' Γ Δ (↷ l) cmτ
  | Throw_typed n cmτ : direction_typed' Γ Δ (↑ n) cmτ
  | Switch_typed mx cmτ : direction_typed' Γ Δ (↓ mx) cmτ.
#[global] Instance direction_typed: Typed (env K * memenv K)
  (rettype K) (direction K) := uncurry direction_typed'.

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
#[global] Instance focus_typed:
  Typed envs (focustype K) (focus K) := uncurry3 focus_typed'.

#[global] Instance state_typed :
    Typed (env K) (focustype K) (state K) := λ Γ S σf, ∃ τf,
  let 'State k φ m := S in
  (Γ,'{m},(locals k).*2) ⊢ φ : τf ∧
  (Γ,'{m}) ⊢ k : τf ↣ σf ∧
  ✓{Γ} m.

Definition funenv_prevalid (Γ : env K) (Δ : memenv K) (δ : funenv K) :=
  map_Forall (λ f s, ∃ τs τ cmτ,
    Γ !! f = Some (τs,τ) ∧ Forall (type_complete Γ) τs ∧
    (Γ,Δ,τs) ⊢ s : cmτ ∧ rettype_match cmτ τ ∧
    gotos s ⊆ labels s ∧ throws_valid 0 s
  ) δ.
#[global] Instance funenv_valid: Valid (env K * memenv K) (funenv K) := λ ΓΔ δ,
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
Implicit Types es : list (expr K).
Implicit Types s : stmt K.
Implicit Types τ σ : type K.
Implicit Types mτ mσ : option (type K).
Implicit Types τlr : lrtype K.
Implicit Types a : addr K.
Implicit Types v : val K.
Implicit Types ν : lrval K.
Implicit Types Ei : ectx_item K.
Implicit Types E : ectx K.
Implicit Types Es : sctx_item K.
Implicit Types Ee : esctx_item K.
Implicit Types Ek : ctx_item K.
Implicit Types k : ctx K.
Implicit Types d : direction K.

Lemma SLocal_typed Γ Δ τs τ s c mσ :
  ✓{Γ} τ → (Γ,Δ,τ :: τs) ⊢ s : (c,mσ) → (Γ,Δ,τs) ⊢ local{τ} s : (c,mσ).
Proof. by constructor. Qed.

Lemma ltype_valid_inv Γ τp : ✓{Γ} (inl τp) → ✓{Γ} τp.
Proof. by inversion 1. Qed.
Lemma rtype_valid_inv Γ τ : ✓{Γ} (inr τ) → ✓{Γ} τ.
Proof. by inversion 1. Qed.
Lemma lval_typed_inv Γ Δ p τp : (Γ,Δ) ⊢ inl p : inl τp → (Γ,Δ) ⊢ p : τp.
Proof. by inversion 1. Qed.
Lemma rval_typed_inv Γ Δ v τ : (Γ,Δ) ⊢ inr v : inr τ → (Γ,Δ) ⊢ v : τ.
Proof. by inversion 1. Qed.
Lemma lrval_typed_type_valid Γ Δ ν τlr : ✓ Γ → (Γ,Δ) ⊢ ν : τlr → ✓{Γ} τlr.
Proof.
  destruct 2; constructor;
    eauto using val_typed_type_valid, ptr_typed_type_valid.
Qed.
Lemma expr_typed_type_valid Γ Δ τs e τlr :
  ✓ Γ → ✓{Γ}* τs → (Γ,Δ,τs) ⊢ e : τlr → ✓{Γ} τlr.
Proof.
  induction 3 using @expr_typed_ind; decompose_Forall_hyps;
    repeat match goal with
    | H : ✓{_} (inl _) |- _ => valid_inversion H
    | H : ✓{_} (inr _) |- _ => valid_inversion H
    end; try constructor; eauto 5 using lrval_typed_type_valid,
    type_valid_ptr_type_valid, unop_typed_type_valid, binop_typed_type_valid,
    TBase_valid, TPtr_valid, TVoid_valid, type_valid_ptr_type_valid,
    ref_seg_typed_ptr_type_valid, TBase_valid_inv, TPtr_valid_inv,
    TFun_valid_inv_ret, type_complete_valid, assign_typed_type_valid.
Qed.
Lemma expr_inl_typed_type_valid Γ Δ τs e τp :
  ✓ Γ → ✓{Γ}* τs → (Γ,Δ,τs) ⊢ e : inl τp → ✓{Γ} τp.
Proof. eauto using expr_typed_type_valid, ltype_valid_inv. Qed.
Lemma expr_inr_typed_type_valid Γ Δ τs e τ :
  ✓ Γ → ✓{Γ}* τs → (Γ,Δ,τs) ⊢ e : inr τ → ✓{Γ} τ.
Proof. eauto using expr_typed_type_valid, rtype_valid_inv. Qed.
Lemma rettype_true_Some_valid Γ β σ : ✓{Γ} σ → ✓{Γ} (β, Some σ).
Proof. done. Qed.
Lemma rettype_union_type_valid Γ mσ1 mσ2 c1 c2 mσ :
  rettype_union mσ1 mσ2 mσ → ✓{Γ} (c1, mσ1) → ✓{Γ} (c2, mσ2) → ✓{Γ} (c2, mσ).
Proof. destruct 1; eauto. Qed.
Lemma stmt_typed_type_valid Γ Δ τs s mcτ :
  ✓ Γ → ✓{Γ}* τs → (Γ,Δ,τs) ⊢ s : mcτ → ✓{Γ} mcτ.
Proof.
  by induction 3; eauto; eauto using expr_inr_typed_type_valid,
     rettype_union_type_valid, rettype_true_Some_valid.
Qed.

Lemma lrval_typed_weaken Γ1 Γ2 Δ1 Δ2 ν τlr :
  ✓ Γ1 → (Γ1,Δ1) ⊢ ν : τlr → Γ1 ⊆ Γ2 → Δ1 ⇒ₘ Δ2 → (Γ2,Δ2) ⊢ ν : τlr.
Proof.
  destruct 2; typed_constructor; eauto using val_typed_weaken, ptr_typed_weaken.
Qed.
Lemma expr_typed_weaken Γ1 Γ2 Δ1 Δ2 τs1 τs2 e τlr :
  ✓ Γ1 → (Γ1,Δ1,τs1) ⊢ e : τlr → Γ1 ⊆ Γ2 → Δ1 ⇒ₘ Δ2 →
  τs1 `prefix_of` τs2 → (Γ2,Δ2,τs2) ⊢ e : τlr.
Proof.
  intros ? He ?? [σs ->].
  induction He using @expr_typed_ind; typed_constructor;
    erewrite <-1?size_of_weaken by eauto; eauto using lrval_typed_weaken,
    lookup_weaken, type_valid_weaken, lookup_app_l_Some, ref_typed_weaken,
    ref_seg_typed_weaken, lockset_valid_weaken, type_complete_weaken.
Qed.
Lemma exprs_typed_weaken Γ1 Γ2 Δ1 Δ2 τs1 τs2 es τlrs :
  ✓ Γ1 → (Γ1,Δ1,τs1) ⊢* es :* τlrs → Γ1 ⊆ Γ2 → Δ1 ⇒ₘ Δ2 →
  τs1 `prefix_of` τs2 → (Γ2,Δ2,τs2) ⊢* es :* τlrs.
Proof. eauto using Forall2_impl, expr_typed_weaken. Qed.
Lemma ectx_item_typed_weaken Γ1 Γ2 Δ1 Δ2 τs1 τs2 Ei τlr σlr :
  ✓ Γ1 → (Γ1,Δ1,τs1) ⊢ Ei : τlr ↣ σlr → Γ1 ⊆ Γ2 →
  Δ1 ⇒ₘ Δ2 → τs1 `prefix_of` τs2 → (Γ2,Δ2,τs2) ⊢ Ei : τlr ↣ σlr.
Proof.
  destruct 2; typed_constructor; eauto using type_valid_weaken,
    expr_typed_weaken, exprs_typed_weaken, lookup_weaken,
    ref_seg_typed_weaken, ref_typed_weaken, type_complete_weaken.
Qed.
Lemma ectx_typed_weaken Γ1 Γ2 Δ1 Δ2 τs1 τs2 E τlr σlr :
  ✓ Γ1 → (Γ1,Δ1,τs1) ⊢ E : τlr ↣ σlr → Γ1 ⊆ Γ2 →
  Δ1 ⇒ₘ Δ2 → τs1 `prefix_of` τs2 → (Γ2,Δ2,τs2) ⊢ E : τlr ↣ σlr.
Proof.
  intros ? HE ???. revert τlr HE. induction E; intros; typed_inversion_all;
    typed_constructor; eauto using ectx_item_typed_weaken.
Qed.
Lemma stmt_typed_weaken Γ1 Γ2 Δ1 Δ2 τs1 τs2 s cmτ :
  ✓ Γ1 → (Γ1,Δ1,τs1) ⊢ s : cmτ → Γ1 ⊆ Γ2 → Δ1 ⇒ₘ Δ2 →
  τs1 `prefix_of` τs2 → (Γ2,Δ2,τs2) ⊢ s : cmτ.
Proof.
  intros ? Hs ??. revert τs2. induction Hs; typed_constructor;
    erewrite <-1?size_of_weaken by eauto;
    eauto using expr_typed_weaken, type_valid_weaken;
    unfold typed, stmt_typed in *; simpl in *; eauto using prefix_cons.
Qed.
Lemma sctx_item_typed_weaken Γ1 Γ2 Δ1 Δ2 τs1 τs2 Es cmτ cmσ :
  ✓ Γ1 → (Γ1,Δ1,τs1) ⊢ Es : cmτ ↣ cmσ → Γ1 ⊆ Γ2 → Δ1 ⇒ₘ Δ2 →
  τs1 `prefix_of` τs2 → (Γ2,Δ2,τs2) ⊢ Es : cmτ ↣ cmσ.
Proof.
  destruct 2; typed_constructor;
    eauto using stmt_typed_weaken, expr_typed_weaken.
Qed.
Lemma esctx_item_typed_weaken Γ1 Γ2 Δ1 Δ2 τs1 τs2 Ee τ cmσ :
  ✓ Γ1 → (Γ1,Δ1,τs1) ⊢ Ee : τ ↣ cmσ → Γ1 ⊆ Γ2 → Δ1 ⇒ₘ Δ2 →
  τs1 `prefix_of` τs2 → (Γ2,Δ2,τs2) ⊢ Ee : τ ↣ cmσ.
Proof. destruct 2; typed_constructor; eauto using stmt_typed_weaken. Qed.
Lemma ctx_item_typed_weaken Γ1 Γ2 Δ1 Δ2 τs Ek τf σf :
  ✓ Γ1 → (Γ1,Δ1,τs) ⊢ Ek : τf ↣ σf → Γ1 ⊆ Γ2 → Δ1 ⇒ₘ Δ2 →
  (Γ2,Δ2,τs) ⊢ Ek : τf ↣ σf.
Proof.
  destruct 2; typed_constructor; eauto using sctx_item_typed_weaken,
    ectx_typed_weaken, esctx_item_typed_weaken, expr_typed_weaken,
    Forall2_impl, lookup_fun_weaken, index_typed_weaken.
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
Lemma indexes_valid_weaken Δ1 Δ2 ρ : ✓{Δ1}* ρ → Δ1 ⇒ₘ Δ2 → ✓{Δ2}* ρ.
Proof.
  unfold valid, stack_item_valid. induction 1; eauto using index_typed_weaken.
Qed.
Lemma ctx_typed_locals_valid Γ Δ k τf σf :
  (Γ,Δ) ⊢ k : τf ↣ σf → ✓{Δ}* (locals k).
Proof.
  assert (∀ os σs, Δ ⊢* os :* σs → ✓{Δ}* (zip os σs))
    by (induction 1; simpl; eauto).
  induction 1 as [|Ek k ??? []]; naive_solver.
Qed.
Lemma ectx_item_subst_typed Γ Δ τs Ei e τlr σlr :
  (Γ,Δ,τs) ⊢ Ei : τlr ↣ σlr →
  (Γ,Δ,τs) ⊢ e : τlr → (Γ,Δ,τs) ⊢ subst Ei e : σlr.
Proof.
  destruct 1; simpl; typed_constructor; eauto.
  rewrite ?fmap_app; simpl; eauto using Forall2_app, Forall2_cons.
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
    list_simplifier; eexists; split_and ?; repeat typed_constructor; eauto.
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
Proof. destruct 1; simpl; typed_constructor; eauto; set_solver. Qed.
Lemma sctx_item_subst_typed_rev Γ Δ τs Es s cmσ :
  (Γ,Δ,τs) ⊢ subst Es s : cmσ →
  ∃ cmτ, (Γ,Δ,τs) ⊢ s : cmτ ∧ (Γ,Δ,τs) ⊢ Es : cmτ ↣ cmσ.
Proof.
  intros Hs. destruct Es; simpl; typed_inversion Hs;
    eexists; split_and ?; repeat typed_constructor; eauto.
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
    eexists; split_and ?; repeat typed_constructor; eauto.
Qed.
Lemma sctx_item_typed_Some_l Γ Δ τs Es c1 τ cmτ :
  (Γ,Δ,τs) ⊢ Es : (c1,Some τ) ↣ cmτ → ∃ c2, cmτ = (c2, Some τ).
Proof.
  intros HEs. typed_inversion HEs; repeat match goal with
    | H : rettype_union _ _ _ |- _ => inversion_clear H
    end; eauto.
Qed.
Lemma rettype_union_inv_l mτ2 τ1 mτ :
  rettype_union (Some τ1) mτ2 mτ → mτ = Some τ1.
Proof. by inversion_clear 1. Qed.
Lemma rettype_union_inv_r mτ1 τ2 mτ :
  rettype_union mτ1 (Some τ2) mτ → mτ = Some τ2.
Proof. by inversion_clear 1. Qed.
Lemma rettype_union_l mσ : rettype_union mσ None mσ.
Proof. destruct mσ; constructor. Qed.
Lemma rettype_union_r mσ : rettype_union None mσ mσ.
Proof. destruct mσ; constructor. Qed.
Lemma rettype_match_Some_inv c τ1 τ2 : rettype_match (c,Some τ1) τ2 → τ1 = τ2.
Proof. by inversion_clear 1. Qed.
Lemma rettype_match_false_inv mτ τ : rettype_match (false,mτ) τ → τ = voidT.
Proof. by inversion_clear 1. Qed.

Lemma expr_typed_freeze Γ Δ β τs e τlr :
  (Γ,Δ,τs) ⊢ e : τlr → (Γ,Δ,τs) ⊢ freeze β e : τlr.
Proof.
  induction 1 using @expr_typed_ind; csimpl; typed_constructor; eauto;
    by apply ref_seg_typed_freeze ||
    by apply ref_typed_freeze || by apply Forall2_fmap_l.
Qed.
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
  { induction 2; simplify_equality'; set_solver by eauto. }
  induction 2 using @expr_typed_ind; simplify_equality'; typed_constructor; 
  eauto; try (eapply IHexpr_typed'); set_solver by eauto.
Qed.
End properties.
