(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
From stdpp Require Import fin_map_dom.
Require Export type_system_decidable memory_refine.

Local Open Scope expr_scope.
Local Open Scope ctype_scope.

Section refinements.
Context `{Env K}.

Inductive stack_item_refine (f : meminj K) (Δ1 Δ2 : memenv K) :
    (index * type K) → (index * type K) → Prop :=
  mk_stack_item_refine o1 o2 τ :
    Δ1 ⊢ o1 : τ → Δ2 ⊢ o2 : τ → f !! o1 = Some (o2,[]) →
    stack_item_refine f Δ1 Δ2 (o1,τ) (o2,τ).

Inductive lrval_refine' (Γ : env K) (α : bool)
    (f : meminj K) (Δ1 Δ2 : memenv K) : lrval K → lrval K → lrtype K → Prop :=
  | lval_refine p1 p2 τp :
     p1 ⊑{Γ,α,f@Δ1↦Δ2} p2 : τp →
     lrval_refine' Γ α f Δ1 Δ2 (inl p1) (inl p2) (inl τp)
  | rval_refine v1 v2 τ :
     v1 ⊑{Γ,α,f@Δ1↦Δ2} v2 : τ →
     lrval_refine' Γ α f Δ1 Δ2 (inr v1) (inr v2) (inr τ).
#[global] Instance lrval_refine:
  RefineT K (env K) (lrtype K) (lrval K) := lrval_refine'.

Inductive expr_refine' (Γ : env K)
     (τs : list (type K)) (α : bool) (f : meminj K)
     (Δ1 Δ2 : memenv K) : expr K → expr K → lrtype K → Prop :=
  | EVar_refine τ n :
     τs !! n = Some τ →
     expr_refine' Γ τs α f Δ1 Δ2 (var n) (var n) (inl (TType τ))
  | EVal_refine Ω1 Ω2 ν1 ν2 τlr :
     Ω1 ⊑{Γ,α,f@Δ1↦Δ2} Ω2 → ν1 ⊑{Γ,α,f@Δ1↦Δ2} ν2 : τlr →
     expr_refine' Γ τs α f Δ1 Δ2 (%#{Ω1} ν1) (%#{Ω2} ν2) τlr
  | ERtoL_refine e1 e2 τp :
     expr_refine' Γ τs α f Δ1 Δ2 e1 e2 (inr (τp.*)) →
     expr_refine' Γ τs α f Δ1 Δ2 (.* e1) (.* e2) (inl τp)
  | ERofL_refine e1 e2 τp :
     expr_refine' Γ τs α f Δ1 Δ2 e1 e2 (inl τp) →
     expr_refine' Γ τs α f Δ1 Δ2 (& e1) (& e2) (inr (τp.*))
  | EAssign_refine ass e1 e2 e1' e2' τ τ' :
     assign_typed τ τ' ass →
     expr_refine' Γ τs α f Δ1 Δ2 e1 e2 (inl (TType τ)) →
     expr_refine' Γ τs α f Δ1 Δ2 e1' e2' (inr τ') →
     expr_refine' Γ τs α f Δ1 Δ2 (e1 ::={ass} e1') (e2 ::={ass} e2') (inr τ)
  | ECall_refine e1 e2 es1 es2 σ σs :
     expr_refine' Γ τs α f Δ1 Δ2 e1 e2 (inl (σs ~> σ)) →
     Forall3 (expr_refine' Γ τs α f Δ1 Δ2) es1 es2 (inr <$> σs) →
     type_complete Γ σ →
     expr_refine' Γ τs α f Δ1 Δ2 (call e1 @ es1) (call e2 @ es2) (inr σ)
  | EAbort_refine τ :
     ✓{Γ} τ → expr_refine' Γ τs α f Δ1 Δ2 (abort τ) (abort τ) (inr τ)
  | ELoad_refine e1 e2 τ :
     expr_refine' Γ τs α f Δ1 Δ2 e1 e2 (inl (TType τ)) → type_complete Γ τ →
     expr_refine' Γ τs α f Δ1 Δ2 (load e1) (load e2) (inr τ)
  | EEltL_refine e1 e2 rs τ σ  :
     expr_refine' Γ τs α f Δ1 Δ2 e1 e2 (inl (TType τ)) → Γ ⊢ rs : τ ↣ σ →
     expr_refine' Γ τs α f Δ1 Δ2 (e1 %> rs) (e2 %> rs) (inl (TType σ))
  | EEltR_refine e1 e2 rs τ σ  :
     expr_refine' Γ τs α f Δ1 Δ2 e1 e2 (inr τ) → Γ ⊢ rs : τ ↣ σ →
     expr_refine' Γ τs α f Δ1 Δ2 (e1 #> rs) (e2 #> rs) (inr σ)
  | EAlloc_refine τ e1 e2 τi :
     ✓{Γ} τ → expr_refine' Γ τs α f Δ1 Δ2 e1 e2 (inr (intT τi)) →
     expr_refine' Γ τs α f Δ1 Δ2 (alloc{τ} e1) (alloc{τ} e2) (inl (TType τ))
  | EFree_refine e1 e2 τp :
     expr_refine' Γ τs α f Δ1 Δ2 e1 e2 (inl τp) →
     expr_refine' Γ τs α f Δ1 Δ2 (free e1) (free e2) (inr voidT)
  | EUnOp_refine op e1 e2 τ σ :
     unop_typed op τ σ → expr_refine' Γ τs α f Δ1 Δ2 e1 e2 (inr τ) →
     expr_refine' Γ τs α f Δ1 Δ2 (.{op} e1) (.{op} e2) (inr σ)
  | EBinOp_refine op e1 e2 e1' e2' τ τ' σ :
     binop_typed op τ τ' σ → expr_refine' Γ τs α f Δ1 Δ2 e1 e2 (inr τ) →
     expr_refine' Γ τs α f Δ1 Δ2 e1' e2' (inr τ') →
     expr_refine' Γ τs α f Δ1 Δ2 (e1 .{op} e1') (e2 .{op} e2') (inr σ)
  | EIf_refine e1 e2 e1' e2' e1'' e2'' τb σlr :
     expr_refine' Γ τs α f Δ1 Δ2 e1 e2 (inr (baseT τb)) → τb ≠ TVoid →
     expr_refine' Γ τs α f Δ1 Δ2 e1' e2' σlr →
     expr_refine' Γ τs α f Δ1 Δ2 e1'' e2'' σlr →
     expr_refine' Γ τs α f Δ1 Δ2
       (if{e1} e1' else e1'') (if{e2} e2' else e2'') σlr
  | EComma_refine e1 e2 e1' e2' τlr1 τlr2 :
     expr_refine' Γ τs α f Δ1 Δ2 e1 e2 τlr1 →
     expr_refine' Γ τs α f Δ1 Δ2 e1' e2' τlr2 →
     expr_refine' Γ τs α f Δ1 Δ2 (e1 ,, e1') (e2 ,, e2') τlr2
  | ECast_refine e1 e2 τ σ :
     expr_refine' Γ τs α f Δ1 Δ2 e1 e2 (inr τ) → cast_typed τ σ → ✓{Γ} σ →
     expr_refine' Γ τs α f Δ1 Δ2 (cast{σ} e1) (cast{σ} e2) (inr σ)
  | EInsert_refine r e1 e2 e1' e2' τ σ :
     Γ ⊢ r : τ ↣ σ →
     expr_refine' Γ τs α f Δ1 Δ2 e1 e2 (inr σ) →
     expr_refine' Γ τs α f Δ1 Δ2 e1' e2' (inr τ) →
     expr_refine' Γ τs α f Δ1 Δ2 (#[r:=e1]e1') (#[r:=e2]e2') (inr τ).
#[global] Instance expr_refine: RefineT K (env K * list (type K))
    (lrtype K) (expr K) := uncurry expr_refine'.

Section expr_refine_ind.
  Context (Γ : env K) (τs : list (type K)).
  Context (α : bool) (f : meminj K) (Δ1 Δ2 : memenv K).
  Context (P : expr K → expr K → lrtype K → Prop).
  Context (Pvar : ∀ τ i, τs !! i = Some τ → P (var i) (var i) (inl (TType τ))).
  Context (Pval : ∀ Ω1 Ω2 ν1 ν2 τlr,
    Ω1 ⊑{Γ,α,f@Δ1↦Δ2} Ω2 → ν1 ⊑{Γ,α,f@Δ1↦Δ2} ν2 : τlr →
    P (%#{Ω1} ν1) (%#{Ω2} ν2) τlr).
  Context (Prtol : ∀ e1 e2 τp,
    e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : inr (τp.*) →
    P e1 e2 (inr (τp.*)) → P (.* e1) (.* e2) (inl τp)).
  Context (Profl : ∀ e1 e2 τp,
    e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : inl τp →
    P e1 e2 (inl τp) → P (& e1) (& e2) (inr (τp.*))).
  Context (Passign : ∀ ass e1 e2 e1' e2' τ τ',
    assign_typed τ τ' ass →
    e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : inl (TType τ) → P e1 e2 (inl (TType τ)) →
    e1' ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2' : inr τ' → P e1' e2' (inr τ') →
    P (e1 ::={ass} e1') (e2 ::={ass} e2') (inr τ)).
  Context (Pcall : ∀ e1 e2 es1 es2 σ σs,
    e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : inl (σs ~> σ) → P e1 e2 (inl (σs ~> σ)) →
    es1 ⊑{(Γ,τs),α,f@Δ1↦Δ2}* es2 :* inr <$> σs →
    Forall3 P es1 es2 (inr <$> σs) →
    type_complete Γ σ → P (call e1 @ es1) (call e2 @ es2) (inr σ)).
  Context (Pabort : ∀ τ, ✓{Γ} τ → P (abort τ) (abort τ) (inr τ)).
  Context (Pload : ∀ e1 e2 τ,
    e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : inl (TType τ) → P e1 e2 (inl (TType τ)) →
    type_complete Γ τ → P (load e1) (load e2) (inr τ)).
  Context (Peltl : ∀ e1 e2 rs τ σ,
    e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : inl (TType τ) → P e1 e2 (inl (TType τ)) →
    Γ ⊢ rs : τ ↣ σ → P (e1 %> rs) (e2 %> rs) (inl (TType σ))).
  Context (Peltr : ∀ e1 e2 rs τ σ,
    e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : inr τ → P e1 e2 (inr τ) →
    Γ ⊢ rs : τ ↣ σ → P (e1 #> rs) (e2 #> rs) (inr σ)).
  Context (Palloc : ∀ τ e1 e2 τi,
    ✓{Γ} τ → e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : inr (intT τi) →
    P e1 e2 (inr (intT τi)) → P (alloc{τ} e1) (alloc{τ} e2) (inl (TType τ))).
  Context (Pfree : ∀ e1 e2 τp,
    e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : inl τp → P e1 e2 (inl τp) →
    P (free e1) (free e2) (inr voidT)).
  Context (Punop : ∀ op e1 e2 τ σ,
    unop_typed op τ σ → e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : inr τ →
    P e1 e2 (inr τ) → P (.{op} e1) (.{op} e2) (inr σ)).
  Context (Pbinop : ∀ op e1 e2 e1' e2' τ τ' σ,
    binop_typed op τ τ' σ →
    e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : inr τ → P e1 e2 (inr τ) →
    e1' ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2' : inr τ' → P e1' e2' (inr τ') →
    P (e1 .{op} e1') (e2 .{op} e2') (inr σ)).
  Context (Pif : ∀ e1 e2 e1' e2' e1'' e2'' τb σlr,
    e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : inr (baseT τb) →
    P e1 e2 (inr (baseT τb)) → τb ≠ TVoid →
    e1' ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2' : σlr → P e1' e2' σlr →
    e1'' ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2'' : σlr → P e1'' e2'' σlr →
    P (if{e1} e1' else e1'') (if{e2} e2' else e2'') σlr).
  Context (Pcomma : ∀ e1 e2 e1' e2' τlr τlr',
    e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : τlr → P e1 e2 τlr →
    e1' ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2' : τlr' → P e1' e2' τlr' →
    P (e1 ,, e1') (e2 ,, e2') τlr').
  Context (Pcast : ∀ e1 e2 τ σ,
    e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : inr τ → P e1 e2 (inr τ) →
    cast_typed τ σ → ✓{Γ} σ → P (cast{σ} e1) (cast{σ} e2) (inr σ)).
  Context (Pinsert : ∀ r e1 e2 e1' e2' τ σ,
    Γ ⊢ r : τ ↣ σ →
    e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : inr σ→ P e1 e2 (inr σ) →
    e1' ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2' : inr τ → P e1' e2' (inr τ) →
    P (#[r:=e1]e1') (#[r:=e2]e2') (inr τ)).
  Lemma expr_refine_ind : ∀ e1 e2 τ,
    expr_refine' Γ τs α f Δ1 Δ2 e1 e2 τ → P e1 e2 τ.
  Proof. fix H'4 4; destruct 1; eauto using Forall2_impl, Forall3_impl. Qed.
End expr_refine_ind.

Inductive ectx_item_refine' (Γ : env K) (τs: list (type K))
     (α : bool) (f : meminj K) (Δ1 Δ2 : memenv K) :
     ectx_item K → ectx_item K → lrtype K → lrtype K → Prop :=
  | CRtoL_refine τp :
     ectx_item_refine' Γ τs α f Δ1 Δ2 (.* □) (.* □) (inr (τp.*)) (inl τp)
  | CLtoR_refine τp :
     ectx_item_refine' Γ τs α f Δ1 Δ2 (& □) (& □) (inl τp) (inr (τp.*))
  | CAssignL_refine ass e1' e2' τ τ' :
     assign_typed τ τ' ass → e1' ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2' : inr τ' →
     ectx_item_refine' Γ τs α f Δ1 Δ2
       (□ ::={ass} e1') (□ ::={ass} e2') (inl (TType τ)) (inr τ)
  | CAssignR_refine ass e1 e2 τ τ' :
     assign_typed τ τ' ass → e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : inl (TType τ) →
     ectx_item_refine' Γ τs α f Δ1 Δ2
       (e1 ::={ass} □) (e2 ::={ass} □) (inr τ') (inr τ)
  | CCallL_refine es1 es2 σs σ :
     es1 ⊑{(Γ,τs),α,f@Δ1↦Δ2}* es2 :* inr <$> σs → type_complete Γ σ →
     ectx_item_refine' Γ τs α f Δ1 Δ2
       (call □ @ es1) (call □ @ es2) (inl (σs ~> σ)) (inr σ)
  | CCallR_refine e1 e2 es1 es2 es1' es2' σ σs τ σs' :
     e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : inl ((σs ++ τ :: σs') ~> σ) →
     reverse es1 ⊑{(Γ,τs),α,f@Δ1↦Δ2}* reverse es2 :* inr <$> σs →
     es1' ⊑{(Γ,τs),α,f@Δ1↦Δ2}* es2' :* inr <$> σs' → type_complete Γ σ →
     ectx_item_refine' Γ τs α f Δ1 Δ2
       (call e1 @ es1 □ es1') (call e2 @ es2 □ es2') (inr τ) (inr σ)
  | CLoad_refine τ :
     type_complete Γ τ →
     ectx_item_refine' Γ τs α f Δ1 Δ2 (load □) (load □) (inl (TType τ)) (inr τ)
  | CEltL_refine rs τ σ :
     Γ ⊢ rs : τ ↣ σ →
     ectx_item_refine' Γ τs α f Δ1 Δ2
       (□ %> rs) (□ %> rs) (inl (TType τ)) (inl (TType σ))
  | CEltR_refine rs τ σ :
     Γ ⊢ rs : τ ↣ σ →
     ectx_item_refine' Γ τs α f Δ1 Δ2 (□ #> rs) (□ #> rs) (inr τ) (inr σ)
  | CAlloc_refine τ τi :
     ✓{Γ} τ → ectx_item_refine' Γ τs α f Δ1 Δ2
       (alloc{τ} □) (alloc{τ} □) (inr (intT τi)) (inl (TType τ))
  | CFree_refine τp :
     ectx_item_refine' Γ τs α f Δ1 Δ2 (free □) (free □) (inl τp) (inr voidT)
  | CUnOp_refine op τ σ :
     unop_typed op τ σ →
     ectx_item_refine' Γ τs α f Δ1 Δ2 (.{op} □) (.{op} □) (inr τ) (inr σ)
  | CBinOpL_refine op e1' e2' τ τ' σ :
     binop_typed op τ τ' σ → e1' ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2' : inr τ' →
     ectx_item_refine' Γ τs α f Δ1 Δ2
       (□ .{op} e1') (□ .{op} e2') (inr τ) (inr σ)
  | CBinOpR_refine op e1 e2 τ τ' σ :
     binop_typed op τ τ' σ → e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : inr τ →
     ectx_item_refine' Γ τs α f Δ1 Δ2
       (e1 .{op} □) (e2 .{op} □) (inr τ') (inr σ)
  | CIf_refine e1' e2' e1'' e2'' τb σlr :
     τb ≠ TVoid → e1' ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2' : σlr →
     e1'' ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2'' : σlr →
     ectx_item_refine' Γ τs α f Δ1 Δ2
       (if{□} e1' else e1'') (if{□} e2' else e2'') (inr (baseT τb)) σlr
  | CComma_refine e1' e2' τlr τlr' :
     e1' ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2' : τlr' →
     ectx_item_refine' Γ τs α f Δ1 Δ2 (□,, e1') (□,, e2') τlr τlr'
  | CCast_refine τ σ :
     cast_typed τ σ → ✓{Γ} σ → ectx_item_refine' Γ τs α f Δ1 Δ2
       (cast{σ} □) (cast{σ} □) (inr τ) (inr σ)
  | CInsertL_refine r e1' e2' τ σ :
     Γ ⊢ r : τ ↣ σ → e1' ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2' : inr τ →
     ectx_item_refine' Γ τs α f Δ1 Δ2
       (#[r:=□]e1') (#[r:=□]e2') (inr σ) (inr τ)
  | CInsertR_refine r e1 e2 τ σ :
     Γ ⊢ r : τ ↣ σ → e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : inr σ →
     ectx_item_refine' Γ τs α f Δ1 Δ2
       (#[r:=e1]□) (#[r:=e2]□) (inr τ) (inr τ).
#[global] Instance ectx_item_refine: PathRefine K (env K * list (type K))
  (lrtype K) (lrtype K) (ectx_item K) := uncurry ectx_item_refine'.
Inductive ectx_refine' (Γs : env K * list (type K))
     (α : bool) (f : meminj K) (Δ1 Δ2 : memenv K) :
     ectx K → ectx K → lrtype K → lrtype K → Prop :=
  | ectx_nil_refine_2 τ : ectx_refine' Γs α f Δ1 Δ2 [] [] τ τ
  | ectx_cons_refine_2 Ei1 Ei2 E1 E2 τ τ' τ'' :
     Ei1 ⊑{Γs,α,f@Δ1↦Δ2} Ei2 : τ ↣ τ' →
     ectx_refine' Γs α f Δ1 Δ2 E1 E2 τ' τ'' →
     ectx_refine' Γs α f Δ1 Δ2 (Ei1 :: E1) (Ei2 :: E2) τ τ''.
#[global] Instance ectx_refine: PathRefine K (env K * list (type K))
  (lrtype K) (lrtype K) (ectx K) := ectx_refine'.

Inductive stmt_refine' (Γ : env K) (τs : list (type K))
     (α : bool) (f : meminj K) (Δ1 Δ2 : memenv K) :
     stmt K → stmt K → rettype K → Prop :=
  | SSkip_refine : stmt_refine' Γ τs α f Δ1 Δ2 skip skip (false,None)
  | SDo_refine e1 e2 τ :
     e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : inr τ → locks e1 = ∅ → locks e2 = ∅ →
     stmt_refine' Γ τs α f Δ1 Δ2 (! e1) (! e2) (false,None)
  | SGoto_refine l :
     stmt_refine' Γ τs α f Δ1 Δ2 (goto l) (goto l) (true,None)
  | SThrow_refine n :
     stmt_refine' Γ τs α f Δ1 Δ2 (throw n) (throw n) (true,None)
  | SReturn_refine e1 e2 τ :
     e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : inr τ → locks e1 = ∅ → locks e2 = ∅ →
     stmt_refine' Γ τs α f Δ1 Δ2 (ret e1) (ret e2) (true,Some τ)
  | SCase_refine mx :
     stmt_refine' Γ τs α f Δ1 Δ2 (scase mx) (scase mx) (false,None)
  | SLabel_refine l :
     stmt_refine' Γ τs α f Δ1 Δ2 (label l) (label l) (false,None)
  | SLocal_refine' τ s1 s2 c mσ :
     ✓{Γ} τ → stmt_refine' Γ (τ :: τs) α f Δ1 Δ2 s1 s2 (c,mσ) →
     stmt_refine' Γ τs α f Δ1 Δ2 (local{τ} s1) (local{τ} s2) (c,mσ)
  | SComp_refine s1 s2 s1' s2' c1 mσ1 c2 mσ2 mσ :
     stmt_refine' Γ τs α f Δ1 Δ2 s1 s2 (c1,mσ1) →
     stmt_refine' Γ τs α f Δ1 Δ2 s1' s2' (c2,mσ2) →
     rettype_union mσ1 mσ2 mσ →
     stmt_refine' Γ τs α f Δ1 Δ2 (s1 ;; s1') (s2 ;; s2') (c2,mσ)
  | SCatch_refine s1 s2 c mσ :
     stmt_refine' Γ τs α f Δ1 Δ2 s1 s2 (c,mσ) →
     stmt_refine' Γ τs α f Δ1 Δ2 (catch s1) (catch s2) (false,mσ)
  | SLoop_refine s1 s2 c mσ :
     stmt_refine' Γ τs α f Δ1 Δ2 s1 s2 (c,mσ) →
     stmt_refine' Γ τs α f Δ1 Δ2 (loop s1) (loop s2) (true,mσ)
  | SIf_refine e1 e2 τb s1 s2 s1' s2' c1 mσ1 c2 mσ2 mσ :
     e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : inr (baseT τb) → τb ≠ TVoid →
     locks e1 = ∅ → locks e2 = ∅ →
     stmt_refine' Γ τs α f Δ1 Δ2 s1 s2 (c1,mσ1) →
     stmt_refine' Γ τs α f Δ1 Δ2 s1' s2' (c2,mσ2) →
     rettype_union mσ1 mσ2 mσ →
     stmt_refine' Γ τs α f Δ1 Δ2
       (if{e1} s1 else s1') (if{e2} s2 else s2') (c1 && c2, mσ)
  | SSwitch_refine e1 e2 τi s1 s2 c mσ :
     e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : inr (intT τi) →
     locks e1 = ∅ → locks e2 = ∅ →
     stmt_refine' Γ τs α f Δ1 Δ2 s1 s2 (c,mσ) →
     stmt_refine' Γ τs α f Δ1 Δ2 (switch{e1} s1) (switch{e2} s2) (false, mσ).
#[global] Instance stmt_refine: RefineT K (env K * list (type K))
   (rettype K) (stmt K) := uncurry stmt_refine'.

Inductive sctx_item_refine' (Γ : env K) (τs: list (type K))
     (α : bool) (f : meminj K) (Δ1 Δ2 : memenv K) :
     sctx_item K → sctx_item K → relation (rettype K) :=
  | CCompL_refine s1' s2' c mσ c' mσ' mσr :
     s1' ⊑{(Γ,τs),α,f@Δ1↦Δ2} s2' : (c',mσ') → rettype_union mσ mσ' mσr →
     sctx_item_refine' Γ τs α f Δ1 Δ2 (□ ;; s1') (□ ;; s2') (c,mσ) (c',mσr)
  | CCompR_refine s1 s2 c mσ c' mσ' mσr :
     s1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} s2 : (c,mσ) → rettype_union mσ mσ' mσr →
     sctx_item_refine' Γ τs α f Δ1 Δ2 (s1 ;; □) (s2 ;; □) (c',mσ') (c',mσr)
  | Ccatch_refine c mσ :
     sctx_item_refine' Γ τs α f Δ1 Δ2
       (catch □) (catch □) (c,mσ) (false,mσ)
  | CLoop_refine c mσ :
     sctx_item_refine' Γ τs α f Δ1 Δ2 (loop □) (loop □) (c,mσ) (true,mσ)
  | CIfL_refine e1 e2 τb s1' s2' c mσ c' mσ' mσr :
     e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : inr (baseT τb) → τb ≠ TVoid →
     locks e1 = ∅ → locks e2 = ∅ →
     s1' ⊑{(Γ,τs),α,f@Δ1↦Δ2} s2' : (c',mσ') → rettype_union mσ mσ' mσr →
     sctx_item_refine' Γ τs α f Δ1 Δ2
       (if{e1} □ else s1') (if{e2} □ else s2') (c,mσ) (c&&c',mσr)
  | CIfR_refine e1 e2 τb s1 s2 c mσ c' mσ' mσr :
     e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : inr (baseT τb) → τb ≠ TVoid →
     locks e1 = ∅ → locks e2 = ∅ →
     s1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} s2 : (c,mσ) → rettype_union mσ mσ' mσr →
     sctx_item_refine' Γ τs α f Δ1 Δ2
       (if{e1} s1 else □) (if{e2} s2 else □) (c',mσ') (c&&c',mσr)
  | CSwitch_refine e1 e2 τi c mσ :
     e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : inr (intT τi) → locks e1 = ∅ → locks e2 = ∅ →
     sctx_item_refine' Γ τs α f Δ1 Δ2
       (switch{e1} □) (switch{e2} □) (c,mσ) (false,mσ).

#[global] Instance sctx_refine: PathRefine K (env K * list (type K))
  (rettype K) (rettype K) (sctx_item K) := uncurry sctx_item_refine'.

Inductive esctx_item_refine' (Γ : env K) (τs: list (type K))
     (α : bool) (f : meminj K) (Δ1 Δ2 : memenv K) :
     esctx_item K → esctx_item K → type K → rettype K → Prop :=
  | CDoE_refine τ :
     esctx_item_refine' Γ τs α f Δ1 Δ2 (! □) (! □) τ (false,None)
  | CReturnE_refine τ :
     esctx_item_refine' Γ τs α f Δ1 Δ2 (ret □) (ret □) τ (true,Some τ)
  | CIfE_refine τb s1 s2 s1' s2' c mσ c' mσ' mσr :
     τb ≠ TVoid → s1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} s2 : (c,mσ) →
     s1' ⊑{(Γ,τs),α,f@Δ1↦Δ2} s2' : (c',mσ') → rettype_union mσ mσ' mσr →
     esctx_item_refine' Γ τs α f Δ1 Δ2
       (if{□} s1 else s1')%S (if{□} s2 else s2')%S (baseT τb) (c&&c',mσr)
  | CSwitchE_refine τi s1 s2 c mσ :
     s1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} s2 : (c,mσ) →
     esctx_item_refine' Γ τs α f Δ1 Δ2
       (switch{□} s1) (switch{□} s2) (intT τi) (false,mσ).
#[global] Instance esctx_item_refine: PathRefine K (env K * list (type K))
  (type K) (rettype K) (esctx_item K) := uncurry esctx_item_refine'.

Inductive ctx_item_refine' (Γ : env K) (τs: list (type K))
     (α : bool) (f : meminj K) (Δ1 Δ2 : memenv K) :
     ctx_item K → ctx_item K → focustype K → focustype K → Prop :=
  | CStmt_refine Es1 Es2 cmσ cmσ' :
     Es1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} Es2 : cmσ ↣ cmσ' →
     ctx_item_refine' Γ τs α f Δ1 Δ2
       (CStmt Es1) (CStmt Es2) (Stmt_type cmσ) (Stmt_type cmσ')
  | CLocal_refine o1 o2 τ c mσ :
     Δ1 ⊢ o1 : τ → Δ2 ⊢ o2 : τ → f !! o1 = Some (o2,[]) →
     ctx_item_refine' Γ τs α f Δ1 Δ2
       (CLocal o1 τ) (CLocal o2 τ) (Stmt_type (c,mσ)) (Stmt_type (c,mσ))
  | CExpr_refine e1 e2 Ee1 Ee2 τ cmσ :
     e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : inr τ → locks e1 = ∅ → locks e2 = ∅ →
     Ee1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} Ee2 : τ ↣ cmσ →
     ctx_item_refine' Γ τs α f Δ1 Δ2
       (CExpr e1 Ee1) (CExpr e2 Ee2) (Expr_type τ) (Stmt_type cmσ)
  | CFun_refine E1 E2 g σs τ σ :
     Γ !! g = Some (σs,τ) →
     E1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} E2 : inr τ ↣ inr σ →
     ctx_item_refine' Γ τs α f Δ1 Δ2
       (CFun E1) (CFun E2) (Fun_type g) (Expr_type σ)
  | CParams_refine g os1 os2 σs cmσ σ :
     Γ !! g = Some (σs,σ) →
     Δ1 ⊢* os1 :* σs → Δ2 ⊢* os2 :* σs →
     Forall2 (λ o1 o2, f !! o1 = Some (o2,[])) os1 os2 →
     rettype_match cmσ σ →
     ctx_item_refine' Γ τs α f Δ1 Δ2 (CParams g (zip os1 σs))
       (CParams g (zip os2 σs)) (Stmt_type cmσ) (Fun_type g).
#[global] Instance ctx_item_refine: PathRefine K (env K * list (type K))
    (focustype K) (focustype K) (ctx_item K) := uncurry ctx_item_refine'.
Inductive ctx_refine' (Γ : env K) (α : bool)
     (f : meminj K) (Δ1 Δ2 : memenv K) :
     ctx K → ctx K → focustype K → focustype K → Prop :=
  | ctx_nil_refine_2 τf : ctx_refine' Γ α f Δ1 Δ2 [] [] τf τf
  | ctx_cons_refine_2 Ek1 Ek2 k1 k2 τf τf' τf'' :
     Ek1 ⊑{(Γ,(locals k1).*2),α,f@Δ1↦Δ2} Ek2 : τf ↣ τf' →
     ctx_refine' Γ α f Δ1 Δ2 k1 k2 τf' τf'' →
     ctx_refine' Γ α f Δ1 Δ2 (Ek1 :: k1) (Ek2 :: k2) τf τf''.
#[global] Instance ctx_refine: PathRefine K (env K)
  (focustype K) (focustype K) (ctx K) := ctx_refine'.

Inductive direction_refine' (Γ : env K) (α : bool) (f : meminj K)
     (Δ1 Δ2: memenv K) : direction K → direction K → rettype K → Prop :=
  | Down_refine cmτ : direction_refine' Γ α f Δ1 Δ2 ↘ ↘ cmτ
  | Up_refine mτ : direction_refine' Γ α f Δ1 Δ2 ↗ ↗ (false,mτ)
  | Top_refine c v1 v2 τ :
     v1 ⊑{Γ,α,f@Δ1↦Δ2} v2 : τ →
     direction_refine' Γ α f Δ1 Δ2 (⇈ v1) (⇈ v2) (c,Some τ)
  | Goto_refine l cmτ : direction_refine' Γ α f Δ1 Δ2 (↷ l) (↷ l) cmτ
  | Throw_refine n cmτ : direction_refine' Γ α f Δ1 Δ2 (↑ n) (↑ n) cmτ
  | Switch_refine mx cmτ : direction_refine' Γ α f Δ1 Δ2 (↓ mx) (↓ mx) cmτ.
#[global] Instance direction_refine: RefineT K (env K)
  (rettype K) (direction K) := direction_refine'.

Inductive focus_refine' (Γ : env K) (τs : list (type K))
     (α : bool) (f : meminj K) (Δ1 Δ2 : memenv K) :
     focus K → focus K → focustype K → Prop :=
  | Stmt_refine d1 d2 s1 s2 cmσ :
     s1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} s2 : cmσ →
     d1 ⊑{Γ,α,f@Δ1↦Δ2} d2 : cmσ →
     focus_refine' Γ τs α f Δ1 Δ2 (Stmt d1 s1) (Stmt d2 s2) (Stmt_type cmσ)
  | Expr_refine e1 e2 τ :
     e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : inr τ →
     focus_refine' Γ τs α f Δ1 Δ2 (Expr e1) (Expr e2) (Expr_type τ)
  | Call_refine g vs1 vs2 σs σ :
     Γ !! g = Some (σs,σ) →
     vs1 ⊑{Γ,α,f@Δ1↦Δ2}* vs2 :* σs →
     focus_refine' Γ τs α f Δ1 Δ2 (Call g vs1) (Call g vs2) (Fun_type g)
  | Return_refine g σs σ v1 v2 :
     Γ !! g = Some (σs, σ) →
     v1 ⊑{Γ,α,f@Δ1↦Δ2} v2 : σ →
     focus_refine' Γ τs α f Δ1 Δ2 (Return g v1) (Return g v2) (Fun_type g)
  | UndefExpr_refine E1 E2 e1 e2 τlr τ :
     e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : τlr →
     E1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} E2 : τlr ↣ inr τ →
     focus_refine' Γ τs α f Δ1 Δ2
       (Undef (UndefExpr E1 e1)) (Undef (UndefExpr E2 e2)) (Expr_type τ)
  | UndefBranch_refine Es1 Es2 Ω1 Ω2 v1 v2 τ mσ :
     v1 ⊑{Γ,α,f@Δ1↦Δ2} v2 : τ →
     Es1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} Es2 : τ ↣ mσ → Ω1 ⊑{Γ,α,f@Δ1↦Δ2} Ω2 →
     focus_refine' Γ τs α f Δ1 Δ2 (Undef (UndefBranch Es1 Ω1 v1))
       (Undef (UndefBranch Es2 Ω2 v2)) (Stmt_type mσ).
#[global] Instance focus_refine: RefineT K (env K * list (type K))
    (focustype K) (focus K) := uncurry focus_refine'.

Inductive state_refine' (Γ : env K) (α : bool)
     (f : meminj K) : state K → state K → focustype K → Prop :=
  | State_refine k1 φ1 m1 k2 φ2 m2 τf σf :
     φ1 ⊑{(Γ,(locals k1).*2),α,f@'{m1}↦'{m2}} φ2 : τf →
     k1 ⊑{(Γ),α,f@'{m1}↦'{m2}} k2 : τf ↣ σf →
     m1 ⊑{Γ,α,f} m2 →
     state_refine' Γ α f (State k1 φ1 m1) (State k2 φ2 m2) σf
  | Undef_State_refine S1 S2 σf :
     α → Γ ⊢ S1 : σf → Γ ⊢ S2 : σf → is_undef_state S1 →
     state_refine' Γ α f S1 S2 σf.
#[global] Instance state_refine :
  RefineTM K (env K) (focustype K) (state K) := state_refine'.

#[global] Instance funenv_refine:
    Refine K (env K) (funenv K) := λ Γ α f Δ1 Δ2 δ1 δ2, ∀ g,
  match δ1 !! g, δ2 !! g, Γ !! g with
  | Some s1, Some s2, Some (τs,τ) => ∃ cmτ,
     Forall (type_complete Γ) τs ∧
     s1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} s2 : cmτ ∧ rettype_match cmτ τ ∧
     gotos s1 ⊆ labels s1 ∧ throws_valid 0 s1
  | None, None, None => True
  | _, _, _ => False
  end.
End refinements.

Section properties.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types f : meminj K.
Implicit Types α : bool.
Implicit Types o : index.
Implicit Types Δ : memenv K.
Implicit Types m : mem K.
Implicit Types e : expr K.
Implicit Types es : list (expr K).
Implicit Types s : stmt K.
Implicit Types τ σ : type K.
Implicit Types a : addr K.
Implicit Types v : val K.
Implicit Types ν : lrval K.
Implicit Types d : direction K.
Implicit Types Ei : ectx_item K.
Implicit Types E : ectx K.
Implicit Types Es : sctx_item K.
Implicit Types Ee : esctx_item K.
Implicit Types Ek : ctx_item K.
Implicit Types k : ctx K.
Implicit Types φ : focus K.

Ltac solve_length := simplify_equality'; repeat
  match goal with H : Forall2 _ _ _ |- _ => apply Forall2_length in H end; lia.

Lemma EVal_refine_inv_l Γ α f Δ1 Δ2 τs Ωs1 vs1 es2 σs :
  #{Ωs1}* vs1 ⊑{(Γ,τs),α,f@Δ1↦Δ2}* es2 :* inr <$> σs →
  length vs1 = length Ωs1 →
  ∃ Ωs2 vs2, es2 = #{Ωs2}* vs2 ∧ Ωs1 ⊑{Γ,α,f@Δ1↦Δ2}* Ωs2 ∧
    length Ωs2 = length vs2 ∧ vs1 ⊑{Γ,α,f@Δ1↦Δ2}* vs2 :* σs.
Proof.
  rewrite <-Forall2_same_length.
  revert Ωs1 vs1 σs. induction es2 as [|?? IH]; intros ?? [|??];
    inversion 1; destruct 1; intros; simplify_equality'; refine_inversion_all.
  { eexists [], []; repeat constructor. }
  edestruct IH as (?&?&?&?&?&?); eauto. subst.
  eexists (_ :: _), (_ :: _);
    split_and ?; simpl; eauto using Forall3_cons with arith.
Qed.
Lemma EVal_refine_inv_r Γ α f Δ1 Δ2 τs es1 Ωs2 vs2 σs :
  es1 ⊑{(Γ,τs),α,f@Δ1↦Δ2}* #{Ωs2}* vs2 :* inr <$> σs →
  length vs2 = length Ωs2 →
  ∃ Ωs1 vs1, es1 = #{Ωs1}* vs1 ∧ Ωs1 ⊑{Γ,α,f@Δ1↦Δ2}* Ωs2 ∧
    length Ωs1 = length vs1 ∧ vs1 ⊑{Γ,α,f@Δ1↦Δ2}* vs2 :* σs.
Proof.
  rewrite <-Forall2_same_length.
  revert Ωs2 vs2 σs. induction es1 as [|?? IH]; intros ?? [|??];
    inversion 1; destruct 1; intros; simplify_equality'; refine_inversion_all.
  { eexists [], []; repeat constructor. }
  edestruct IH as (?&?&?&?&?&?); eauto. subst.
  eexists (_ :: _), (_ :: _);
    split_and ?; simpl; eauto using Forall3_cons with arith.
Qed.
Lemma ectx_item_subst_refine Γ α f Δ1 Δ2 τs Ei1 Ei2 e1 e2 τlr τlr' :
  Ei1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} Ei2 : τlr ↣ τlr' →
  e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : τlr →
  subst Ei1 e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} subst Ei2 e2 : τlr'.
Proof.
  destruct 1; simpl; refine_constructor; eauto.
  rewrite ?fmap_app; eauto using Forall3_app, Forall3_cons.
Qed.
Lemma ectx_subst_refine Γ α f Δ1 Δ2 τs E1 E2 e1 e2 τlr τlr' :
  E1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} E2 : τlr ↣ τlr' →
  e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : τlr →
  subst E1 e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} subst E2 e2 : τlr'.
Proof.
  intros HE. revert e1 e2.
  induction HE; simpl; eauto using ectx_item_subst_refine.
Qed.
Lemma sctx_item_subst_refine Γ α f Δ1 Δ2 τs Es1 Es2 s1 s2 mcτ mcτ' :
  Es1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} Es2 : mcτ ↣ mcτ' →
  s1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} s2 : mcτ →
  subst Es1 s1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} subst Es2 s2 : mcτ'.
Proof. destruct 1; simpl; refine_constructor; eauto. Qed.
Lemma ectx_item_subst_refine_inv_r Γ α f Δ1 Δ2 τs e1 Ei2 e2 τlr' :
  e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} subst Ei2 e2 : τlr' →
  ∃ e1' Ei1 τlr, e1 = subst Ei1 e1' ∧
    Ei1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} Ei2 : τlr ↣ τlr' ∧
    e1' ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : τlr.
Proof.
  intros He; destruct Ei2; refine_inversion He; list_simplifier;
    try match goal with
    | H : ?E ⊑{_,_,_@_↦_}* reverse _ :* _ |- _ =>
       rewrite <-(reverse_involutive E) in H
    end; by do 3 eexists; split_and ?;
     repeat refine_constructor; simpl; eauto; rewrite ?reverse_involutive.
Qed.
Lemma ectx_subst_refine_inv_r Γ α f Δ1 Δ2 τs e1 E2 e2 τlr' :
  e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} subst E2 e2 : τlr' →
  ∃ e1' E1 τlr, e1 = subst E1 e1' ∧
    E1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} E2 : τlr ↣ τlr' ∧
    e1' ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : τlr.
Proof.
  revert e2. induction E2 as [|Ei2 E2 IH]; intros e2 He; simpl in *.
  { by eexists e1, [], τlr'; split_and ?; repeat refine_constructor. }
  destruct (IH (subst Ei2 e2)) as (e1'&E1&τlr&->&?&?); auto.
  destruct (ectx_item_subst_refine_inv_r Γ α f Δ1 Δ2 τs e1' Ei2 e2 τlr)
    as (e1&Ee1&τlr''&->&?&?); auto.
  exists e1, (Ee1 :: E1), τlr''; split_and ?; repeat refine_constructor; eauto.
Qed.
Lemma esctx_item_subst_refine_inv_r Γ α f Δ1 Δ2 τs s1 Ee2 e2 mcτ :
  s1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} subst Ee2 e2 : mcτ →
  ∃ e1 Ee1 τ, s1 = subst Ee1 e1 ∧ Ee1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} Ee2 : τ ↣ mcτ ∧
    e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : inr τ ∧ locks e1 = ∅ ∧ locks e2 = ∅.
Proof.
  by destruct Ee2; inversion 1; subst;
    do 3 eexists; split_and ?; repeat refine_constructor; eauto.
Qed.
Lemma sctx_item_subst_refine_inv_r Γ α f Δ1 Δ2 τs s1 Es2 s2 mcτ' :
  s1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} subst Es2 s2 : mcτ' →
  ∃ s1' Es1 mcτ, s1 = subst Es1 s1' ∧
    Es1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} Es2 : mcτ ↣ mcτ' ∧
    s1' ⊑{(Γ,τs),α,f@Δ1↦Δ2} s2 : mcτ.
Proof.
  by destruct Es2; inversion 1; subst;
    do 3 eexists; split_and ?; repeat refine_constructor; eauto.
Qed.

Lemma expr_refine_nf_inv Γ α f Δ1 Δ2 τs e1 e2 τlr :
  e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : τlr → is_nf e2 → is_nf e1.
Proof. destruct 1; inversion_clear 1; constructor. Qed.
Lemma exprs_refine_nf_inv Γ α f Δ1 Δ2 τs es1 es2 τlrs :
  es1 ⊑{(Γ,τs),α,f@Δ1↦Δ2}* es2 :* τlrs →
  Forall is_nf es2 → Forall is_nf es1.
Proof. induction 1; inversion_clear 1; eauto using expr_refine_nf_inv. Qed.
Lemma expr_refine_redex_inv Γ α f Δ1 Δ2 τs e1 e2 τlr :
  e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : τlr → is_redex e2 → is_redex e1.
Proof.
  destruct 1; inversion_clear 1;
    constructor; eauto using expr_refine_nf_inv, exprs_refine_nf_inv.
Qed.
Lemma stmt_refine_gotos Γ α f Δ1 Δ2 τs s1 s2 mcτ :
  s1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} s2 : mcτ → gotos s1 = gotos s2.
Proof. induction 1; simpl; auto with f_equal. Qed.
Lemma stmt_refine_labels Γ α f Δ1 Δ2 τs s1 s2 mcτ :
  s1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} s2 : mcτ → labels s1 = labels s2.
Proof. induction 1; simpl; auto with f_equal. Qed.
Lemma stmt_refine_throws_valid Γ α f Δ1 Δ2 τs s1 s2 mcτ n :
  s1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} s2 : mcτ → throws_valid n s1 → throws_valid n s2.
Proof. intros Hs. revert n. induction Hs; naive_solver. Qed.
Lemma stmt_refine_cases Γ α f Δ1 Δ2 τs s1 s2 mcτ :
  s1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} s2 : mcτ → cases s1 = cases s2.
Proof. induction 1; simpl; auto with f_equal. Qed.
Lemma ctx_refine_locals_types Γ α f Δ1 Δ2 k1 k2 τf τf' :
  ✓ Γ → k1 ⊑{Γ,α,f@Δ1↦Δ2} k2 : τf ↣ τf' → (locals k1).*2 = (locals k2).*2.
Proof.
  assert (∀ (os1 os2 : list index) (σs : list (type K)) P,
    Forall2 P os1 os2 → (zip os1 σs).*2 = (zip os2 σs).*2).
  { intros os1 os2 σs P Hos. revert σs.
    induction Hos; intros [|??]; f_equal'; auto. }
  induction 2 as [|??????? []]; simpl; eauto with f_equal.
Qed.
Lemma ctx_refine_locals_refine Γ α f Δ1 Δ2 k1 k2 τf τf' :
  k1 ⊑{Γ,α,f@Δ1↦Δ2} k2 : τf ↣ τf' →
  Forall2 (stack_item_refine f Δ1 Δ2) (locals k1) (locals k2).
Proof.
  assert (∀ os1 os2 σs, Δ1 ⊢* os1 :* σs → Δ2 ⊢* os2 :* σs →
    Forall2 (λ o1 o2, f !! o1 = Some (o2, [])) os1 os2 →
    Forall2 (stack_item_refine f Δ1 Δ2) (zip os1 σs) (zip os2 σs)).
  { intros os1 os2 σs Hos. revert os2.
    induction Hos; intros; decompose_Forall_hyps; repeat constructor; eauto. }
  induction 1 as [|??????? []]; simplify_equality'; repeat constructor; eauto.
Qed.
Lemma sctx_item_catch_refine Γ α f Δ1 Δ2 τs Es1 Es2 s1 s2 mcτ mcτ' :
  Es1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} Es2 : mcτ ↣ mcτ' →
  Es1 = catch □ → Es2 = catch □.
Proof. by destruct 1. Qed.
Lemma sctx_item_switch_refine Γ α f Δ1 Δ2 τs Es1 Es2 s1 s2 mcτ mcτ' :
  Es1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} Es2 : mcτ ↣ mcτ' →
  maybe CSwitch Es2 = None → maybe CSwitch Es1 = None.
Proof. by destruct 1. Qed.
Lemma direction_in_refine_r Γ τs α f Δ1 Δ2 s1 s2 d1 d2 mcτ :
  s1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} s2 : mcτ →
  d1 ⊑{Γ,α,f@Δ1↦Δ2} d2 : mcτ → direction_in d2 s2 → direction_in d1 s1.
Proof.
  by destruct 2; simpl;
    erewrite <-?stmt_refine_labels, <-?stmt_refine_cases by eauto.
Qed.
Lemma direction_out_refine_r Γ τs α f Δ1 Δ2 s1 s2 d1 d2 mcτ :
  s1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} s2 : mcτ →
  d1 ⊑{Γ,α,f@Δ1↦Δ2} d2 : mcτ → direction_out d2 s2 → direction_out d1 s1.
Proof. by destruct 2; simpl; erewrite <-?stmt_refine_labels by eauto. Qed.
Lemma funenv_lookup_refine_r Γ α f Δ1 Δ2 δ1 δ2 g s2 :
  δ1 ⊑{Γ,α,f@Δ1↦Δ2} δ2 → δ2 !! g = Some s2 → ∃ s1 τs τ cmτ,
    δ1 !! g = Some s1 ∧ Γ !! g = Some (τs,τ) ∧
    s1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} s2 : cmτ ∧ rettype_match cmτ τ ∧
    gotos s1 ⊆ labels s1 ∧ throws_valid 0 s1.
Proof. intros Hδ ?; specialize (Hδ g); repeat case_match; naive_solver. Qed.
Lemma state_refine_mem Γ α f S1 S2 σf :
  ¬is_undef_state S1 → S1 ⊑{Γ,α,f} S2 : σf → '{SMem S1} ⊑{Γ,α,f} '{SMem S2}.
Proof. by destruct 2; eauto using cmap_refine_memenv_refine'. Qed.

Lemma lrval_refine_typed_l Γ α f Δ1 Δ2 ν1 ν2 τlr :
  ✓ Γ → ν1 ⊑{Γ,α,f@Δ1↦Δ2} ν2 : τlr → (Γ,Δ1) ⊢ ν1 : τlr.
Proof.
  destruct 2; typed_constructor;
    eauto using val_refine_typed_l, ptr_refine_typed_l.
Qed.
Lemma expr_refine_typed_l Γ α f Δ1 Δ2 τs e1 e2 τlr :
  ✓ Γ → e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : τlr → (Γ,Δ1,τs) ⊢ e1 : τlr.
Proof.
  assert (∀ es1 es2 τlrs,
    Forall3 (λ e1 _ τlr, (Γ,Δ1,τs) ⊢ e1 : τlr) es1 es2 τlrs →
    (Γ,Δ1,τs) ⊢* es1 :* τlrs).
  { induction 1; constructor; eauto. }
  induction 2 using @expr_refine_ind; typed_constructor;
    eauto using lrval_refine_typed_l, locks_refine_valid_l.
Qed.
Lemma exprs_refine_typed_l Γ α f Δ1 Δ2 τs es1 es2 τlrs :
  ✓ Γ → es1 ⊑{(Γ,τs),α,f@Δ1↦Δ2}* es2 :* τlrs →
  (Γ,Δ1,τs) ⊢* es1 :* τlrs.
Proof. induction 2; eauto using expr_refine_typed_l. Qed.
Lemma ectx_item_refine_typed_l Γ α f Δ1 Δ2 τs Ei1 Ei2 τlr τlr' :
  ✓ Γ → Ei1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} Ei2 : τlr ↣ τlr' →
  (Γ,Δ1,τs) ⊢ Ei1 : τlr ↣ τlr'.
Proof.
  destruct 2; typed_constructor;
    eauto using expr_refine_typed_l, exprs_refine_typed_l.
Qed.
Lemma ectx_refine_typed_l Γ α f Δ1 Δ2 τs E1 E2 τlr τlr' :
  ✓ Γ → E1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} E2 : τlr ↣ τlr' →
  (Γ,Δ1,τs) ⊢ E1 : τlr ↣ τlr'.
Proof. induction 2;typed_constructor; eauto using ectx_item_refine_typed_l. Qed.
Lemma stmt_refine_typed_l Γ α f Δ1 Δ2 τs s1 s2 mcτ :
  ✓ Γ → s1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} s2 : mcτ → (Γ,Δ1,τs) ⊢ s1 : mcτ.
Proof. induction 2; typed_constructor; eauto using expr_refine_typed_l. Qed.
Lemma sctx_item_refine_typed_l Γ α f Δ1 Δ2 τs Es1 Es2 mcτ mcτ' :
  ✓ Γ → Es1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} Es2 : mcτ ↣ mcτ' →
  (Γ,Δ1,τs) ⊢ Es1 : mcτ ↣ mcτ'.
Proof.
  destruct 2; typed_constructor;
    eauto using stmt_refine_typed_l, expr_refine_typed_l.
Qed.
Lemma esctx_item_refine_typed_l Γ α f Δ1 Δ2 τs Ee1 Ee2 τlr mcτ :
  ✓ Γ → Ee1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} Ee2 : τlr ↣ mcτ →
  (Γ,Δ1,τs) ⊢ Ee1 : τlr ↣ mcτ.
Proof. destruct 2; typed_constructor; eauto using stmt_refine_typed_l. Qed.
Lemma ctx_item_refine_typed_l Γ α f Δ1 Δ2 τs Ek1 Ek2 τf τf' :
  ✓ Γ → Ek1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} Ek2 : τf ↣ τf' →
  (Γ,Δ1,τs) ⊢ Ek1 : τf ↣ τf'.
Proof.
  destruct 2; typed_constructor; eauto using expr_refine_typed_l,
    esctx_item_refine_typed_l, sctx_item_refine_typed_l, ectx_refine_typed_l.
Qed.
Lemma ctx_refine_typed_l Γ α f Δ1 Δ2 k1 k2 τf τf' :
  ✓ Γ → k1 ⊑{Γ,α,f@Δ1↦Δ2} k2 : τf ↣ τf' → (Γ,Δ1) ⊢ k1 : τf ↣ τf'.
Proof. induction 2; typed_constructor; eauto using ctx_item_refine_typed_l. Qed.
Lemma direction_refine_typed_l Γ α f Δ1 Δ2 d1 d2 τlr :
  ✓ Γ → d1 ⊑{Γ,α,f@Δ1↦Δ2} d2 : τlr → (Γ,Δ1) ⊢ d1 : τlr.
Proof. destruct 2; typed_constructor; eauto using val_refine_typed_l. Qed.
Lemma focus_refine_typed_l Γ α f Δ1 Δ2 τs φ1 φ2 τf :
  ✓ Γ → φ1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} φ2 : τf → (Γ,Δ1,τs) ⊢ φ1 : τf.
Proof.
  induction 2; typed_constructor; eauto using stmt_refine_typed_l,
    direction_refine_typed_l, expr_refine_typed_l, vals_refine_typed_l,
    val_refine_typed_l, ectx_refine_typed_l, esctx_item_refine_typed_l,
    locks_refine_valid_l.
Qed.
Lemma state_refine_typed_l Γ α f S1 S2 σf :
  ✓ Γ → S1 ⊑{Γ,α,f} S2 : σf → Γ ⊢ S1 : σf.
Proof.
  destruct 2; do 2 red; eauto 10 using focus_refine_typed_l,
    ctx_refine_typed_l, cmap_refine_valid_l'.
Qed.
Lemma funenv_refine_typed_l Γ α f Δ1 Δ2 δ1 δ2 :
  ✓ Γ → δ1 ⊑{Γ,α,f@Δ1↦Δ2} δ2 → ✓{Γ,Δ1} δ1.
Proof.
  intros ? Hδ; split.
  * intros g s ?; specialize (Hδ g); destruct (δ2 !! _),
      (Γ !! _) as [[τs τ]|]; simplify_option_eq; try done.
    destruct Hδ as (cmτ&?&?&?&?&?); eauto 20 using stmt_refine_typed_l.
  * rewrite elem_of_subseteq; intros g; rewrite !elem_of_dom.
    intros [[τs τ] ?]; specialize (Hδ g). destruct (δ1 !! g),
      (δ2 !! g); simplify_option_eq; naive_solver.
Qed.

Lemma lrval_refine_typed_r Γ α f Δ1 Δ2 ν1 ν2 τlr :
  ✓ Γ → ν1 ⊑{Γ,α,f@Δ1↦Δ2} ν2 : τlr → (Γ,Δ2) ⊢ ν2 : τlr.
Proof.
  destruct 2; typed_constructor;
    eauto using val_refine_typed_r, ptr_refine_typed_r.
Qed.
Lemma expr_refine_typed_r Γ α f Δ1 Δ2 τs e1 e2 τlr :
  ✓ Γ → e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : τlr → (Γ,Δ2,τs) ⊢ e2 : τlr.
Proof.
  assert (∀ es1 es2 τlrs,
    Forall3 (λ _ e2 τlr, (Γ,Δ2,τs) ⊢ e2 : τlr) es1 es2 τlrs →
    (Γ,Δ2,τs) ⊢* es2 :* τlrs).
  { induction 1; constructor; eauto. }
  induction 2 using @expr_refine_ind; typed_constructor;
    eauto using lrval_refine_typed_r, locks_refine_valid_r.
Qed.
Lemma exprs_refine_typed_r Γ α f Δ1 Δ2 τs es1 es2 τlrs :
  ✓ Γ → es1 ⊑{(Γ,τs),α,f@Δ1↦Δ2}* es2 :* τlrs →(Γ,Δ2,τs) ⊢* es2 :* τlrs.
Proof. induction 2; eauto using expr_refine_typed_r. Qed.
Lemma ectx_item_refine_typed_r Γ α f Δ1 Δ2 τs Ei1 Ei2 τlr τlr' :
  ✓ Γ → Ei1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} Ei2 : τlr ↣ τlr' →
  (Γ,Δ2,τs) ⊢ Ei2 : τlr ↣ τlr'.
Proof.
  destruct 2; typed_constructor;
    eauto using expr_refine_typed_r, exprs_refine_typed_r.
Qed.
Lemma ectx_refine_typed_r Γ α f Δ1 Δ2 τs E1 E2 τlr τlr' :
  ✓ Γ → E1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} E2 : τlr ↣ τlr' →
  (Γ,Δ2,τs) ⊢ E2 : τlr ↣ τlr'.
Proof. induction 2;typed_constructor; eauto using ectx_item_refine_typed_r. Qed.
Lemma stmt_refine_typed_r Γ f α Δ1 Δ2 τs s1 s2 mcτ :
  ✓ Γ → s1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} s2 : mcτ → (Γ,Δ2,τs) ⊢ s2 : mcτ.
Proof. induction 2; typed_constructor; eauto using expr_refine_typed_r. Qed.
Lemma sctx_item_refine_typed_r Γ α f Δ1 Δ2 τs Es1 Es2 mcτ mcτ' :
  ✓ Γ → Es1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} Es2 : mcτ ↣ mcτ' →
  (Γ,Δ2,τs) ⊢ Es2 : mcτ ↣ mcτ'.
Proof.
  destruct 2; typed_constructor;
    eauto using stmt_refine_typed_r, expr_refine_typed_r.
Qed.
Lemma esctx_item_refine_typed_r Γ α f Δ1 Δ2 τs Ee1 Ee2 τlr mcτ :
  ✓ Γ → Ee1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} Ee2 : τlr ↣ mcτ →
  (Γ,Δ2,τs) ⊢ Ee2 : τlr ↣ mcτ.
Proof. destruct 2; typed_constructor; eauto using stmt_refine_typed_r. Qed.
Lemma ctx_item_refine_typed_r Γ α f Δ1 Δ2 τs Ek1 Ek2 τf τf' :
  ✓ Γ → Ek1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} Ek2 : τf ↣ τf' →
  (Γ,Δ2,τs) ⊢ Ek2 : τf ↣ τf'.
Proof.
  destruct 2; typed_constructor; eauto using expr_refine_typed_r,
    esctx_item_refine_typed_r, sctx_item_refine_typed_r, ectx_refine_typed_r.
Qed.
Lemma ctx_refine_typed_r Γ α f Δ1 Δ2 k1 k2 τf τf' :
  ✓ Γ → k1 ⊑{Γ,α,f@Δ1↦Δ2} k2 : τf ↣ τf' → (Γ,Δ2) ⊢ k2 : τf ↣ τf'.
Proof.
  induction 2; typed_constructor; erewrite <-?ctx_refine_locals_types by eauto;
    eauto using ctx_item_refine_typed_r.
Qed.
Lemma direction_refine_typed_r Γ α f Δ1 Δ2 d1 d2 τlr :
  ✓ Γ → d1 ⊑{Γ,α,f@Δ1↦Δ2} d2 : τlr → (Γ,Δ2) ⊢ d2 : τlr.
Proof. destruct 2; typed_constructor; eauto using val_refine_typed_r. Qed.
Lemma focus_refine_typed_r Γ α f Δ1 Δ2 τs φ1 φ2 τf :
  ✓ Γ → φ1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} φ2 : τf → (Γ,Δ2,τs) ⊢ φ2 : τf.
Proof.
  induction 2; typed_constructor; eauto using stmt_refine_typed_r,
    direction_refine_typed_r, expr_refine_typed_r, vals_refine_typed_r,
    val_refine_typed_r, ectx_refine_typed_r, esctx_item_refine_typed_r,
    locks_refine_valid_r.
Qed.
Lemma state_refine_typed_r Γ α f S1 S2 σf :
  ✓ Γ → S1 ⊑{Γ,α,f} S2 : σf → Γ ⊢ S2 : σf.
Proof.
  destruct 2; eauto. eexists; split_and ?;
    erewrite <-?ctx_refine_locals_types by eauto;
    eauto using focus_refine_typed_r, ctx_refine_typed_r, cmap_refine_valid_r'.
Qed.
Lemma funenv_refine_typed_r Γ α f Δ1 Δ2 δ1 δ2 :
  ✓ Γ → δ1 ⊑{Γ,α,f@Δ1↦Δ2} δ2 → ✓{Γ,Δ2} δ2.
Proof.
  intros ? Hδ; split.
  * intros g s ?; specialize (Hδ g); destruct (δ1 !! _),
      (Γ !! _) as [[τs τ]|]; simplify_option_eq; try done.
    destruct Hδ as (cmτ&?&?&?&?&?).
    erewrite <-stmt_refine_labels, <-stmt_refine_gotos by eauto.
    eauto 15 using stmt_refine_typed_r, stmt_refine_throws_valid.
  * rewrite elem_of_subseteq; intros g; rewrite !elem_of_dom.
    intros [[τs τ] ?]; specialize (Hδ g); destruct (δ1 !! _),
      (δ2 !! _); simplify_option_eq; naive_solver.
Qed.

Lemma lrval_refine_id Γ α Δ ν τlr : (Γ,Δ) ⊢ ν : τlr → ν ⊑{Γ,α@Δ} ν : τlr.
Proof. destruct 1; constructor; eauto using val_refine_id, ptr_refine_id. Qed.
Lemma expr_refine_id Γ α Δ τs e τlr :
  (Γ,Δ,τs) ⊢ e : τlr → e ⊑{(Γ,τs),α@Δ} e : τlr.
Proof.
  assert (∀ es τlrs, Forall2 (λ e τlr, e ⊑{(Γ,τs),α@Δ} e : τlr) es τlrs →
    es ⊑{(Γ,τs),α@Δ}* es :* τlrs).
  { induction 1; constructor; eauto. }
  induction 1 using @expr_typed_ind;
    refine_constructor; eauto using locks_refine_id, lrval_refine_id.
Qed.
Lemma exprs_refine_id Γ α Δ τs es τlrs :
  (Γ,Δ,τs) ⊢* es :* τlrs → es ⊑{(Γ,τs),α@Δ}* es :* τlrs.
Proof. induction 1; constructor; eauto using expr_refine_id. Qed.  
Lemma ectx_item_refine_id Γ α Δ τs Ei τlr τlr' :
  (Γ,Δ,τs) ⊢ Ei : τlr ↣ τlr' → Ei ⊑{(Γ,τs),α@Δ} Ei : τlr ↣ τlr'.
Proof.
  destruct 1; refine_constructor; eauto using expr_refine_id, exprs_refine_id.
Qed.
Lemma ectx_refine_id Γ α Δ τs E τlr τlr' :
  (Γ,Δ,τs) ⊢ E : τlr ↣ τlr' → E ⊑{(Γ,τs),α@Δ} E : τlr ↣ τlr'.
Proof. induction 1; refine_constructor; eauto using ectx_item_refine_id. Qed.
Lemma stmt_refine_id Γ α Δ τs s mcσ :
  (Γ,Δ,τs) ⊢ s : mcσ → s ⊑{(Γ,τs),α@Δ} s : mcσ.
Proof. induction 1; refine_constructor; eauto using expr_refine_id. Qed.
Lemma sctx_item_refine_id Γ α Δ τs Es mcσ mcσ' :
  (Γ,Δ,τs) ⊢ Es : mcσ ↣ mcσ' → Es ⊑{(Γ,τs),α@Δ} Es : mcσ ↣ mcσ'.
Proof.
  destruct 1; refine_constructor; eauto using stmt_refine_id, expr_refine_id.
Qed.
Lemma esctx_item_refine_id Γ α Δ τs Ee τlr τlr' :
  (Γ,Δ,τs) ⊢ Ee : τlr ↣ τlr' → Ee ⊑{(Γ,τs),α@Δ} Ee : τlr ↣ τlr'.
Proof. destruct 1; refine_constructor; eauto using stmt_refine_id. Qed.
Lemma ctx_item_refine_id Γ α Δ τs Ek τf τf' :
  (Γ,Δ,τs) ⊢ Ek : τf ↣ τf' → Ek ⊑{(Γ,τs),α@Δ} Ek : τf ↣ τf'.
Proof.
  assert (∀ os, Forall2 (λ o1 o2, @meminj_id K !! o1 = Some (o2, [])) os os).
  { induction os; auto. }
  destruct 1; refine_constructor; eauto using sctx_item_refine_id,
    expr_refine_id, ectx_refine_id, esctx_item_refine_id.
Qed.
Lemma ctx_refine_id Γ α Δ k τf τf' :
  (Γ,Δ) ⊢ k : τf ↣ τf' → k ⊑{Γ,α@Δ} k : τf ↣ τf'.
Proof. induction 1; refine_constructor; eauto using ctx_item_refine_id. Qed.
Lemma direction_refine_id Γ α Δ d cmσ : (Γ,Δ) ⊢ d : cmσ → d ⊑{Γ,α@Δ} d : cmσ.
Proof. destruct 1; refine_constructor; eauto using val_refine_id. Qed.
Lemma focus_refine_id Γ α Δ τs φ τf :
  (Γ,Δ,τs) ⊢ φ : τf → φ ⊑{(Γ,τs),α@Δ} φ : τf.
Proof.
  destruct 1; refine_constructor; eauto using stmt_refine_id,
    direction_refine_id, expr_refine_id, val_refine_id, ectx_refine_id,
    esctx_item_refine_id, vals_refine_id, locks_refine_id.
Qed.
Lemma state_refine_id Γ α S σf : ✓ Γ → Γ ⊢ S : σf → S ⊑{Γ,α} S : σf.
Proof.
  destruct S; intros ? (τf&?&?&?).
  eleft; eauto using cmap_refine_id', ctx_refine_id, focus_refine_id.
Qed.
Lemma funenv_refine_id Γ α Δ δ : ✓ Γ → ✓{Γ,Δ} δ → δ ⊑{Γ,α@Δ} δ.
Proof.
  intros ? [Hδ Hdom] g; specialize (Hdom g); rewrite !elem_of_dom in Hdom.
  destruct (δ !! g) eqn:?; auto.
  * destruct (Hδ g s) as (τs&τ&?&->&?); naive_solver eauto using stmt_refine_id.
  * unfold lookup, env_lookup_fun.
    destruct (env_f Γ !! g). by destruct Hdom; eauto. done.
Qed.

Lemma lrval_refine_compose Γ α1 α2 f1 f2 Δ1 Δ2 Δ3 ν1 ν2 ν3 τlr τlr' :
  ✓ Γ → ν1 ⊑{Γ,α1,f1@Δ1↦Δ2} ν2 : τlr → ν2 ⊑{Γ,α2,f2@Δ2↦Δ3} ν3 : τlr' →
  ν1 ⊑{Γ,α1||α2,f2 ◎ f1@Δ1↦Δ3} ν3 : τlr.
Proof.
  destruct 2; inversion_clear 1; refine_constructor;
    eauto using val_refine_compose, ptr_refine_compose.
Qed.
Lemma expr_refine_compose Γ τs α1 α2 f1 f2 Δ1 Δ2 Δ3 e1 e2 e3 τlr τlr' :
  ✓ Γ → e1 ⊑{(Γ,τs),α1,f1@Δ1↦Δ2} e2 : τlr →
  e2 ⊑{(Γ,τs),α2,f2@Δ2↦Δ3} e3 : τlr' →
  e1 ⊑{(Γ,τs),α1||α2,f2 ◎ f1@Δ1↦Δ3} e3 : τlr.
Proof.
  assert (∀ es1 es2 es3 τlrs τlrs',
    Forall3 (λ e1 e2 τlr, ∀ e3 τlr', e2 ⊑{(Γ,τs),α2,f2@ Δ2↦Δ3} e3 : τlr' →
      e1 ⊑{(Γ,τs),α1||α2,f2 ◎ f1 @ Δ1↦Δ3} e3 : τlr) es1 es2 τlrs →
    es2 ⊑{(Γ,τs),α2,f2@ Δ2↦Δ3}* es3 :* τlrs' →
    es1 ⊑{(Γ,τs),α1||α2,f2 ◎ f1 @ Δ1↦Δ3}* es3 :* τlrs).
  { intros ?? es3 ? τlrs' Hes. revert es3 τlrs'.
    induction Hes; inversion_clear 1; constructor; eauto. }
  intros ? He; revert e3 τlr'.
  induction He using @expr_refine_ind; intros ?? He';
    refine_inversion He'; simplify_type_equality'; refine_constructor;
    eauto using locks_refine_compose, lrval_refine_compose.
Qed.
Lemma exprs_refine_compose
    Γ τs α1 α2 f1 f2 Δ1 Δ2 Δ3 es1 es2 es3 τlrs τlrs' :
  ✓ Γ → es1 ⊑{(Γ,τs),α1,f1@Δ1↦Δ2}* es2 :* τlrs →
  es2 ⊑{(Γ,τs),α2,f2@Δ2↦Δ3}* es3 :* τlrs' →
  es1 ⊑{(Γ,τs),α1||α2,f2 ◎ f1@Δ1↦Δ3}* es3 :* τlrs.
Proof.
  intros ? Hes. revert es3 τlrs'. induction Hes; inversion_clear 1;
    constructor; eauto using expr_refine_compose.
Qed.
Lemma ectx_item_refine_compose
    Γ τs α1 α2 f1 f2 Δ1 Δ2 Δ3 Ei1 Ei2 Ei3 τlr τlr' τlr'' :
  ✓ Γ → Ei1 ⊑{(Γ,τs),α1,f1@Δ1↦Δ2} Ei2 : τlr ↣ τlr' →
  Ei2 ⊑{(Γ,τs),α2,f2@Δ2↦Δ3} Ei3 : τlr ↣ τlr'' →
  Ei1 ⊑{(Γ,τs),α1||α2,f2 ◎ f1@Δ1↦Δ3} Ei3 : τlr ↣ τlr'.
Proof.
  destruct 2; intros HEi'; refine_inversion HEi'; simplify_type_equality;
    repeat match goal with (* no backtracking in refine_constructor... *)
    | H : assign_typed _ ?τ _, _ : _ ⊑{_,_,_@_↦_} ?e2 : _,
      _ : ?e2 ⊑{_,_,_@_↦_} _ : inr ?τ |- _ => clear H
    end; refine_constructor;
    eauto 3 using expr_refine_compose, exprs_refine_compose.
Qed.
Lemma ectx_refine_compose
    Γ τs α1 α2 f1 f2 Δ1 Δ2 Δ3 E1 E2 E3 τlr τlr' τlr'' :
  ✓ Γ → E1 ⊑{(Γ,τs),α1,f1@Δ1↦Δ2} E2 : τlr ↣ τlr' →
  E2 ⊑{(Γ,τs),α2,f2@Δ2↦Δ3} E3 : τlr ↣ τlr'' →
  E1 ⊑{(Γ,τs),α1||α2,f2 ◎ f1@Δ1↦Δ3} E3 : τlr ↣ τlr'.
Proof.
  intros ? HE. revert E3 τlr''.
  induction HE as [|Ei1 Ei2 E1 E2 τlr1 τlr2 τlr3];
    intros E3' τlr3'; inversion_clear 1 as [|? Ei3 ? E3 ? τlr2'];
    refine_constructor; eauto using ectx_item_refine_compose.
  cut (τlr2 = τlr2'); [intros ->; eauto|].
  by eapply (path_typed_unique_r _ Ei2);
    eauto using ectx_item_refine_typed_l, ectx_item_refine_typed_r.
Qed.
Lemma stmt_refine_compose Γ τs α1 α2 f1 f2 Δ1 Δ2 Δ3 s1 s2 s3 mcτ mcτ' :
  ✓ Γ → s1 ⊑{(Γ,τs),α1,f1@Δ1↦Δ2} s2 : mcτ →
  s2 ⊑{(Γ,τs),α2,f2@Δ2↦Δ3} s3 : mcτ' →
  s1 ⊑{(Γ,τs),α1||α2,f2 ◎ f1@Δ1↦Δ3} s3 : mcτ.
Proof.
  intros ? Hs. revert s3 mcτ'.
  induction Hs; intros ?? Hs'; refine_inversion Hs';
    refine_constructor; naive_solver eauto using expr_refine_compose.
Qed.
Lemma sctx_item_refine_compose
    Γ τs α1 α2 f1 f2 Δ1 Δ2 Δ3 Es1 Es2 Es3 mcτ mcτ' mcτ'' :
  ✓ Γ → Es1 ⊑{(Γ,τs),α1,f1@Δ1↦Δ2} Es2 : mcτ ↣ mcτ' →
  Es2 ⊑{(Γ,τs),α2,f2@Δ2↦Δ3} Es3 : mcτ ↣ mcτ'' →
  Es1 ⊑{(Γ,τs),α1||α2,f2 ◎ f1@Δ1↦Δ3} Es3 : mcτ ↣ mcτ'.
Proof.
  destruct 2; intros HEs'; refine_inversion HEs'; refine_constructor;
    eauto using expr_refine_compose, stmt_refine_compose.
Qed.
Lemma esctx_item_refine_compose
    Γ τs α1 α2 f1 f2 Δ1 Δ2 Δ3 Ee1 Ee2 Ee3 τlr mcτ' mcτ'' :
  ✓ Γ → Ee1 ⊑{(Γ,τs),α1,f1@Δ1↦Δ2} Ee2 : τlr ↣ mcτ' →
  Ee2 ⊑{(Γ,τs),α2,f2@Δ2↦Δ3} Ee3 : τlr ↣ mcτ'' →
  Ee1 ⊑{(Γ,τs),α1||α2,f2 ◎ f1@Δ1↦Δ3} Ee3 : τlr ↣ mcτ'.
Proof.
  destruct 2; intros HEe'; refine_inversion HEe';
     refine_constructor; eauto using stmt_refine_compose.
Qed.
Lemma ctx_item_refine_compose
    Γ τs α1 α2 f1 f2 Δ1 Δ2 Δ3 Ek1 Ek2 Ek3 τf τf' τf'' :
  ✓ Γ → Ek1 ⊑{(Γ,τs),α1,f1@Δ1↦Δ2} Ek2 : τf ↣ τf' →
  Ek2 ⊑{(Γ,τs),α2,f2@Δ2↦Δ3} Ek3 : τf ↣ τf'' →
  Ek1 ⊑{(Γ,τs),α1||α2,f2 ◎ f1@Δ1↦Δ3} Ek3 : τf ↣ τf'.
Proof.
  assert (∀ o1 o2 o3, f1 !! o1 = Some (o2,[]) → f2 !! o2 = Some (o3,[]) →
    (f2 ◎ f1) !! o1 = Some (o3,[])).
  { intros o1 o2 o3. rewrite lookup_meminj_compose_Some. naive_solver. }
  assert (∀ os1 os2 os2' os3 (σs : list (type K)),
    Δ2 ⊢* os2 :* σs → Δ2 ⊢* os2' :* σs → zip os2' σs = zip os2 σs →
    Forall2 (λ o1 o2, f1 !! o1 = Some (o2, [])) os1 os2 →
    Forall2 (λ o1 o2, f2 !! o1 = Some (o2, [])) os2' os3 →
    Forall2 (λ o1 o2, (f2 ◎ f1) !! o1 = Some (o2, [])) os1 os3).
  { induction os1; intros; decompose_Forall_hyps; eauto. }
  destruct 2; intros HEk'; refine_inversion HEk'; try refine_constructor;
     eauto using expr_refine_compose, ectx_refine_compose,
     sctx_item_refine_compose, esctx_item_refine_compose.
Qed.
Lemma ctx_refine_compose Γ α1 α2 f1 f2 Δ1 Δ2 Δ3 k1 k2 k3 τf τf' τf'' :
  ✓ Γ → k1 ⊑{Γ,α1,f1@Δ1↦Δ2} k2 : τf ↣ τf' →
  k2 ⊑{Γ,α2,f2@Δ2↦Δ3} k3 : τf ↣ τf'' →
  k1 ⊑{Γ,α1||α2,f2 ◎ f1@Δ1↦Δ3} k3 : τf ↣ τf'.
Proof.
  intros ? Hk. revert k3 τf''.
  induction Hk as [|Ek1 Ek2 k1 k2 τf1 τf2 τf3];
    intros Ek' τf3'; inversion_clear 1 as [|? Ek3 ? k3 ? τf2' ? HEk2].
  { by refine_constructor. }
  erewrite <-ctx_refine_locals_types in HEk2 by eauto.
  refine_constructor; eauto using ctx_item_refine_compose.
  cut (τf2 = τf2'); [intros ->; eauto|].
  by eapply (path_typed_unique_r _ Ek2 τf1);
    eauto using ctx_item_refine_typed_l, ctx_item_refine_typed_r.
Qed.
Lemma direction_refine_compose Γ α1 α2 f1 f2 Δ1 Δ2 Δ3 d1 d2 d3 mcτ mcτ' :
  ✓ Γ → d1 ⊑{Γ,α1,f1@Δ1↦Δ2} d2 : mcτ → d2 ⊑{Γ,α2,f2@Δ2↦Δ3} d3 : mcτ' →
  d1 ⊑{Γ,α1||α2,f2 ◎ f1@Δ1↦Δ3} d3 : mcτ.
Proof.
  destruct 2; inversion_clear 1; refine_constructor;
    eauto using val_refine_compose.
Qed.
Lemma focus_refine_compose Γ τs α1 α2 f1 f2 Δ1 Δ2 Δ3 φ1 φ2 φ3 τf τf' :
  ✓ Γ → φ1 ⊑{(Γ,τs),α1,f1@Δ1↦Δ2} φ2 : τf →
  φ2 ⊑{(Γ,τs),α2,f2@Δ2↦Δ3} φ3 : τf' →
  φ1 ⊑{(Γ,τs),α1||α2,f2 ◎ f1@Δ1↦Δ3} φ3 : τf.
Proof.
  destruct 2 as [| | | |E1 E2 e1 e2 τlr τ|e1 e2 Es1 Es2 v1 v2 τ mτ];
    inversion 1 as [| | | |? E3 ? e3 τlr' τ'|? e3 ? Es3 ? v3 τ' mτ'];
    simplify_equality'.
  * refine_constructor;
      eauto using stmt_refine_compose, direction_refine_compose.
  * refine_constructor; eauto using expr_refine_compose.
  * refine_constructor; eauto using vals_refine_compose.
  * refine_constructor; eauto using val_refine_compose.
  * assert (τlr' = τlr) as ->.
    { by eapply (typed_unique _ e2);
        eauto using expr_refine_typed_l, expr_refine_typed_r. }
    refine_constructor; eauto using expr_refine_compose, ectx_refine_compose.
  * assert (τ' = τ) as ->.
    { by eapply (typed_unique _ v2);
        eauto using val_refine_typed_l, val_refine_typed_r. }
    refine_constructor; eauto using val_refine_compose, expr_refine_compose,
      esctx_item_refine_compose, locks_refine_compose.
Qed.
Lemma state_refine_undef Γ α f S1 S2 h :
  S1 ⊑{Γ,α,f} S2 : h → is_undef_state S2 → is_undef_state S1.
Proof. destruct 1 as [k1 φ1 m1 k2 φ2 m2 τf ? []|]; naive_solver. Qed.
Lemma state_refine_compose Γ α1 α2 f1 f2 S1 S2 S3 h :
  ✓ Γ → S1 ⊑{Γ,α1,f1} S2 : h → S2 ⊑{Γ,α2,f2} S3 : h →
  S1 ⊑{Γ,α1||α2,f2 ◎ f1} S3 : h.
Proof.
  intros ? HS HS'.
  assert (Γ ⊢ S1 : h) by eauto using state_refine_typed_l.
  assert (Γ ⊢ S3 : h) by eauto using state_refine_typed_r.
  inversion HS as [k1 φ1 m1 k2 φ2 m2 τf|]; subst; [|right; eauto].
  inversion HS' as [??? k3 φ3 m3 τf' ? Hk'|]; subst.
  * erewrite <-ctx_refine_locals_types in Hk' by eauto.
    left with τf; eauto using cmap_refine_compose', focus_refine_compose.
    cut (τf = τf'); [intros ->;eauto using ctx_refine_compose|].
    by eapply (typed_unique _ φ2);
      eauto using focus_refine_typed_l, focus_refine_typed_r.
  * right; eauto using state_refine_undef.
Qed.
Lemma funenv_refine_compose Γ α1 α2 f1 f2 Δ1 Δ2 Δ3 δ1 δ2 δ3 :
  ✓ Γ → δ1 ⊑{Γ,α1,f1@Δ1↦Δ2} δ2 → δ2 ⊑{Γ,α2,f2@Δ2↦Δ3} δ3 →
  δ1 ⊑{Γ,α1||α2,f2 ◎ f1@Δ1↦Δ3} δ3.
Proof.
  intros ? Hδ Hδ' h; specialize (Hδ h); specialize (Hδ' h).
  destruct (δ1 !! h) as [s1|], (δ2 !! h) as [s2|], (δ3 !! h) as [s3|],
    (Γ !! h) as [[τs τ]|]; try done.
  destruct Hδ as (cmτ&?&?&?&?&?), Hδ' as (cmτ'&?&?&?&?&?).
  eauto 15 using stmt_refine_compose.
Qed.

Lemma lrval_refine_inverse Γ f Δ1 Δ2 ν1 ν2 τlr :
  ν1 ⊑{Γ,false,f@Δ1↦Δ2} ν2 : τlr →
  ν2 ⊑{Γ,false,meminj_inverse f@Δ2↦Δ1} ν1 : τlr.
Proof.
  destruct 1; constructor; eauto using val_refine_inverse, ptr_refine_inverse.
Qed.
Lemma expr_refine_inverse Γ τs f Δ1 Δ2 e1 e2 τlr :
  e1 ⊑{(Γ,τs),false,f@Δ1↦Δ2} e2 : τlr →
  e2 ⊑{(Γ,τs),false,meminj_inverse f@Δ2↦Δ1} e1 : τlr.
Proof.
  assert (∀ es1 es2 τlrs,
    Forall3 (λ e1 e2 τlr,
      e2 ⊑{(Γ,τs),false,meminj_inverse f@ Δ2↦Δ1} e1 : τlr) es1 es2 τlrs →
    es2 ⊑{(Γ,τs),false,meminj_inverse f@ Δ2↦Δ1}* es1 :* τlrs).
  { induction 1; constructor; eauto. }
  induction 1 using @expr_refine_ind; refine_constructor;
    eauto using lrval_refine_inverse, locks_refine_inverse.
Qed.
Lemma exprs_refine_inverse Γ τs f Δ1 Δ2 es1 es2 τlrs :
  es1 ⊑{(Γ,τs),false,f@Δ1↦Δ2}* es2 :* τlrs →
  es2 ⊑{(Γ,τs),false,meminj_inverse f@Δ2↦Δ1}* es1 :* τlrs.
Proof. induction 1; constructor; eauto using expr_refine_inverse. Qed.
Lemma ectx_item_refine_inverse Γ τs f Δ1 Δ2 Ei1 Ei2 τlr τlr' :
  Ei1 ⊑{(Γ,τs),false,f@Δ1↦Δ2} Ei2 : τlr ↣ τlr' →
  Ei2 ⊑{(Γ,τs),false,meminj_inverse f@Δ2↦Δ1} Ei1 : τlr ↣ τlr'.
Proof.
  destruct 1; refine_constructor;
    eauto using expr_refine_inverse, exprs_refine_inverse.
Qed.
Lemma ectx_refine_inverse Γ τs f Δ1 Δ2 E1 E2 τlr τlr' :
  E1 ⊑{(Γ,τs),false,f@Δ1↦Δ2} E2 : τlr ↣ τlr' →
  E2 ⊑{(Γ,τs),false,meminj_inverse f@Δ2↦Δ1} E1 : τlr ↣ τlr'.
Proof. induction 1; econstructor; eauto using ectx_item_refine_inverse. Qed.
Lemma stmt_refine_inverse Γ τs f Δ1 Δ2 s1 s2 mcτ :
  s1 ⊑{(Γ,τs),false,f@Δ1↦Δ2} s2 : mcτ →
  s2 ⊑{(Γ,τs),false,meminj_inverse f@Δ2↦Δ1} s1 : mcτ.
Proof.
  remember false as α. induction 1; subst;
    refine_constructor; naive_solver eauto using expr_refine_inverse.
Qed.
Lemma sctx_item_refine_inverse Γ τs f Δ1 Δ2 Es1 Es2 mcτ mcτ' :
  Es1 ⊑{(Γ,τs),false,f@Δ1↦Δ2} Es2 : mcτ ↣ mcτ' →
  Es2 ⊑{(Γ,τs),false,meminj_inverse f@Δ2↦Δ1} Es1 : mcτ ↣ mcτ'.
Proof.
  destruct 1; refine_constructor;
    eauto using stmt_refine_inverse, expr_refine_inverse.
Qed.
Lemma esctx_item_refine_inverse Γ τs f Δ1 Δ2 Ee1 Ee2 τlr mcτ' :
  Ee1 ⊑{(Γ,τs),false,f@Δ1↦Δ2} Ee2 : τlr ↣ mcτ' →
  Ee2 ⊑{(Γ,τs),false,meminj_inverse f@Δ2↦Δ1} Ee1 : τlr ↣ mcτ'.
Proof. destruct 1; refine_constructor; eauto using stmt_refine_inverse. Qed.
Lemma ctx_item_refine_inverse Γ τs f Δ1 Δ2 Ek1 Ek2 τf τf' :
  Δ1 ⊑{Γ,false,f} Δ2 → Ek1 ⊑{(Γ,τs),false,f@Δ1↦Δ2} Ek2 : τf ↣ τf' →
  Ek2 ⊑{(Γ,τs),false,meminj_inverse f@Δ2↦Δ1} Ek1 : τf ↣ τf'.
Proof.
  intros ?. assert (∀ os1 os2 σs, Δ1 ⊢* os1 :* σs →
    Forall2 (λ o1 o2, f !! o1 = Some (o2, [])) os1 os2 →
    Forall2 (λ o1 o2, meminj_inverse f !! o1 = Some (o2, [])) os2 os1).
  { intros os1 os2 σs Hos1. revert os2.
    induction Hos1; intros; decompose_Forall_hyps;
      constructor; eauto using lookup_meminj_inverse_2. } 
  destruct 1; refine_constructor; eauto using expr_refine_inverse,
    ectx_refine_inverse, esctx_item_refine_inverse,
    sctx_item_refine_inverse, lookup_meminj_inverse_2.
Qed.
Lemma ctx_refine_inverse Γ f Δ1 Δ2 k1 k2 τf τf' :
  ✓ Γ → Δ1 ⊑{Γ,false,f} Δ2 → k1 ⊑{Γ,false,f@Δ1↦Δ2} k2 : τf ↣ τf' →
  k2 ⊑{Γ,false,meminj_inverse f@Δ2↦Δ1} k1 : τf ↣ τf'.
Proof.
  induction 3; refine_constructor; eauto.
  erewrite <-ctx_refine_locals_types by eauto.
  eauto using ctx_item_refine_inverse.
Qed.
Lemma direction_refine_inverse Γ f Δ1 Δ2 d1 d2 mcτ :
  d1 ⊑{Γ,false,f@Δ1↦Δ2} d2 : mcτ →
  d2 ⊑{Γ,false,meminj_inverse f@Δ2↦Δ1} d1 : mcτ.
Proof. destruct 1; refine_constructor; eauto using val_refine_inverse. Qed.
Lemma focus_refine_inverse Γ τs f Δ1 Δ2 φ1 φ2 τf :
  φ1 ⊑{(Γ,τs),false,f@Δ1↦Δ2} φ2 : τf →
  φ2 ⊑{(Γ,τs),false,meminj_inverse f@Δ2↦Δ1} φ1 : τf.
Proof.
  destruct 1; refine_constructor; eauto using stmt_refine_inverse,
    direction_refine_inverse, expr_refine_inverse, val_refine_inverse,
    vals_refine_inverse, ectx_refine_inverse,
    esctx_item_refine_inverse, locks_refine_inverse.
Qed.
Lemma state_refine_inverse Γ f S1 S2 h :
  ✓ Γ → S1 ⊑{Γ,false,f} S2 : h →
  S2 ⊑{Γ,false,meminj_inverse f} S1 : h.
Proof.
  intros ? [k1 φ1 m1 k2 φ2 m2 τf h' ???|]; [left with τf|done].
  * erewrite <-ctx_refine_locals_types by eauto.
    eauto using focus_refine_inverse.
  * eauto using ctx_refine_inverse, cmap_refine_memenv_refine.
  * eauto using cmap_refine_inverse'.
Qed.
Lemma funenv_refine_inverse Γ f Δ1 Δ2 δ1 δ2 :
  δ1 ⊑{Γ,false,f@Δ1↦Δ2} δ2 →
  δ2 ⊑{Γ,false,meminj_inverse f@Δ2↦Δ1} δ1.
Proof.
  intros Hδ h; specialize (Hδ h); destruct (δ1 !! h) as [s1|],
    (δ2 !! h) as [s2|], (Γ !! h) as [[τs τ]|]; try done.
  destruct Hδ as (cmτ&?&?&?&?&?); exists cmτ; split_and ?; auto.
  * auto using stmt_refine_inverse.
  * by erewrite <-stmt_refine_gotos, <-stmt_refine_labels by eauto.
  * eauto using stmt_refine_throws_valid.
Qed.

Lemma lrval_refine_weaken Γ α α' f f' Δ1 Δ2 Δ1' Δ2' ν1 ν2 τlr :
  ✓ Γ → ν1 ⊑{Γ,α,f@Δ1↦Δ2} ν2 : τlr → (α → α') →
  Δ1' ⊑{Γ,α',f'} Δ2' → Δ1 ⇒ₘ Δ1' → Δ2 ⇒ₘ Δ2' →
  meminj_extend f f' Δ1 Δ2 → ν1 ⊑{Γ,α',f'@Δ1'↦Δ2'} ν2 : τlr.
Proof.
  destruct 2; refine_constructor;
    eauto using ptr_refine_weaken, val_refine_weaken.
Qed.
Lemma expr_refine_weaken Γ α α' f f' Δ1 Δ2 Δ1' Δ2' τs e1 e2 τlr :
  ✓ Γ → e1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} e2 : τlr → (α → α') →
  Δ1' ⊑{Γ,α',f'} Δ2' → Δ1 ⇒ₘ Δ1' → Δ2 ⇒ₘ Δ2' →
  meminj_extend f f' Δ1 Δ2 → e1 ⊑{(Γ,τs),α',f'@Δ1'↦Δ2'} e2 : τlr.
Proof.
  intros ? He; intros. induction He using @expr_refine_ind;
    refine_constructor; eauto using locks_refine_weaken, lrval_refine_weaken.
Qed.
Lemma exprs_refine_weaken Γ α α' f f' Δ1 Δ2 Δ1' Δ2' τs es1 es2 τlrs :
  ✓ Γ → es1 ⊑{(Γ,τs),α,f@Δ1↦Δ2}* es2 :* τlrs → (α → α') →
  Δ1' ⊑{Γ,α',f'} Δ2' → Δ1 ⇒ₘ Δ1' → Δ2 ⇒ₘ Δ2' →
  meminj_extend f f' Δ1 Δ2 →
  es1 ⊑{(Γ,τs),α',f'@Δ1'↦Δ2'}* es2 :* τlrs.
Proof. induction 2; constructor; eauto using expr_refine_weaken. Qed.
Lemma ectx_item_refine_weaken
    Γ α α' f f' Δ1 Δ2 Δ1' Δ2' τs Ei1 Ei2 τlr τlr' :
  ✓ Γ → Ei1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} Ei2 : τlr ↣ τlr' → (α → α') →
  Δ1' ⊑{Γ,α',f'} Δ2' → Δ1 ⇒ₘ Δ1' → Δ2 ⇒ₘ Δ2' →
  meminj_extend f f' Δ1 Δ2 →
  Ei1 ⊑{(Γ,τs),α',f'@Δ1'↦Δ2'} Ei2 : τlr ↣ τlr'.
Proof.
  destruct 2; refine_constructor;
    eauto using expr_refine_weaken, exprs_refine_weaken.
Qed.
Lemma ectx_refine_weaken Γ α α' f f' Δ1 Δ2 Δ1' Δ2' τs E1 E2 τlr τlr' :
  ✓ Γ → E1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} E2 : τlr ↣ τlr' → (α → α') →
  Δ1' ⊑{Γ,α',f'} Δ2' → Δ1 ⇒ₘ Δ1' → Δ2 ⇒ₘ Δ2' →
  meminj_extend f f' Δ1 Δ2 → E1 ⊑{(Γ,τs),α',f'@Δ1'↦Δ2'} E2 : τlr ↣ τlr'.
Proof. induction 2; refine_constructor;eauto using ectx_item_refine_weaken. Qed.
Lemma stmt_refine_weaken Γ α α' f f' Δ1 Δ2 Δ1' Δ2' τs s1 s2 mcτ :
  ✓ Γ → s1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} s2 : mcτ → (α → α') → Δ1' ⊑{Γ,α',f'} Δ2' →
  Δ1 ⇒ₘ Δ1' → Δ2 ⇒ₘ Δ2' → meminj_extend f f' Δ1 Δ2 →
  s1 ⊑{(Γ,τs),α',f'@Δ1'↦Δ2'} s2 : mcτ.
Proof.
  intros ? Hs; intros. induction Hs;
    refine_constructor; naive_solver eauto using expr_refine_weaken.
Qed.
Lemma sctx_item_refine_weaken Γ α α' f f' Δ1 Δ2 Δ1' Δ2' τs Es1 Es2 mcτ mcτ' :
  ✓ Γ → Es1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} Es2 : mcτ ↣ mcτ' → (α → α') →
  Δ1' ⊑{Γ,α',f'} Δ2' → Δ1 ⇒ₘ Δ1' → Δ2 ⇒ₘ Δ2' →
  meminj_extend f f' Δ1 Δ2 →
  Es1 ⊑{(Γ,τs),α',f'@Δ1'↦Δ2'} Es2 : mcτ ↣ mcτ'.
Proof.
  destruct 2; refine_constructor;
    eauto using stmt_refine_weaken, expr_refine_weaken.
Qed.
Lemma esctx_item_refine_weaken
    Γ α α' f f' Δ1 Δ2 Δ1' Δ2' τs Ee1 Ee2 τ mcτ' :
  ✓ Γ → Ee1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} Ee2 : τ ↣ mcτ' → (α → α') →
  Δ1' ⊑{Γ,α',f'} Δ2' → Δ1 ⇒ₘ Δ1' → Δ2 ⇒ₘ Δ2' →
  meminj_extend f f' Δ1 Δ2 → Ee1 ⊑{(Γ,τs),α',f'@Δ1'↦Δ2'} Ee2 : τ ↣ mcτ'.
Proof. destruct 2; refine_constructor; eauto using stmt_refine_weaken. Qed.
Lemma ctx_item_refine_weaken Γ α α' f f' Δ1 Δ2 Δ1' Δ2' τs Ek1 Ek2 τf τf' :
  ✓ Γ → Ek1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} Ek2 : τf ↣ τf' → (α → α') →
  Δ1' ⊑{Γ,α',f'} Δ2' → Δ1 ⇒ₘ Δ1' → Δ2 ⇒ₘ Δ2' →
  meminj_extend f f' Δ1 Δ2 → Ek1 ⊑{(Γ,τs),α',f'@Δ1'↦Δ2'} Ek2 : τf ↣ τf'.
Proof.
  intros ? HEk ?????. assert (∀ os1 os2 σs, Δ1 ⊢* os1 :* σs →
    Forall2 (λ o1 o2, f !! o1 = Some (o2, [])) os1 os2 →
    Forall2 (λ o1 o2, f' !! o1 = Some (o2, [])) os1 os2).
  { intros os1 os2 σs Hos. revert os2.
    induction Hos; intros; decompose_Forall_hyps; constructor;
      eauto using option_eq_1_alt, meminj_extend_left. }
  destruct HEk; refine_constructor; eauto using esctx_item_refine_weaken,
    sctx_item_refine_weaken, expr_refine_weaken, ectx_refine_weaken,
    Forall2_impl, memenv_forward_typed, meminj_extend_left, option_eq_1_alt.
Qed.
Lemma ctx_refine_weaken Γ α α' f f' Δ1 Δ2 Δ1' Δ2' k1 k2 τf τf' :
  ✓ Γ → k1 ⊑{Γ,α,f@Δ1↦Δ2} k2 : τf ↣ τf' → (α → α') →
  Δ1' ⊑{Γ,α',f'} Δ2' → Δ1 ⇒ₘ Δ1' → Δ2 ⇒ₘ Δ2' →
  meminj_extend f f' Δ1 Δ2 → k1 ⊑{Γ,α',f'@Δ1'↦Δ2'} k2 : τf ↣ τf'.
Proof. induction 2; refine_constructor; eauto using ctx_item_refine_weaken. Qed.
Lemma direction_refine_weaken Γ α α' f f' Δ1 Δ2 Δ1' Δ2' d1 d2 mcτ :
  ✓ Γ → d1 ⊑{Γ,α,f@Δ1↦Δ2} d2 : mcτ → (α → α') →
  Δ1' ⊑{Γ,α',f'} Δ2' → Δ1 ⇒ₘ Δ1' → Δ2 ⇒ₘ Δ2' →
  meminj_extend f f' Δ1 Δ2 → d1 ⊑{Γ,α',f'@Δ1'↦Δ2'} d2 : mcτ.
Proof. destruct 2; refine_constructor; eauto using val_refine_weaken. Qed.
Lemma focus_refine_weaken Γ α α' f f' Δ1 Δ2 Δ1' Δ2' τs φ1 φ2 τf :
  ✓ Γ → φ1 ⊑{(Γ,τs),α,f@Δ1↦Δ2} φ2 : τf → (α → α') →
  Δ1' ⊑{Γ,α',f'} Δ2' → Δ1 ⇒ₘ Δ1' → Δ2 ⇒ₘ Δ2' →
  meminj_extend f f' Δ1 Δ2 → φ1 ⊑{(Γ,τs),α',f'@Δ1'↦Δ2'} φ2 : τf.
Proof.
  destruct 2; refine_constructor; eauto using direction_refine_weaken,
    stmt_refine_weaken, expr_refine_weaken, val_refine_weaken,
    vals_refine_weaken, locks_refine_weaken, ectx_refine_weaken,
    esctx_item_refine_weaken.
Qed.
Lemma funenv_refine_weaken Γ α α' f f' Δ1 Δ2 Δ1' Δ2' δ1 δ2 :
  ✓ Γ → δ1 ⊑{Γ,α,f@Δ1↦Δ2} δ2 → (α → α') → Δ1' ⊑{Γ,α',f'} Δ2' →
  Δ1 ⇒ₘ Δ1' → Δ2 ⇒ₘ Δ2' → meminj_extend f f' Δ1 Δ2 →
  δ1 ⊑{Γ,α',f'@Δ1'↦Δ2'} δ2.
Proof.
  intros ? Hδ ????? h; specialize (Hδ h); destruct (δ1 !! h) as [s1|],
    (δ2 !! h) as [s2|], (Γ !! h) as [[τs τ]|]; eauto.
  naive_solver eauto using stmt_refine_weaken.
Qed.
End properties.
