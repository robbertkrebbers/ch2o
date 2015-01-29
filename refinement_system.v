(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export type_system_decidable memory_refine.
Local Open Scope expr_scope.
Local Open Scope ctype_scope.

Section refinements.
Context `{Env Ti}.

Inductive lrval_refine' (Γ : env Ti) (α : bool)
    (f : meminj Ti) (Γm1 Γm2 : memenv Ti) :
    addr Ti + val Ti → addr Ti + val Ti → lrtype Ti → Prop :=
  | lval_refine a1 a2 τ :
     a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : Some τ → addr_strict Γ a1 →
     lrval_refine' Γ α f Γm1 Γm2 (inl a1) (inl a2) (inl τ)
  | rval_refine v1 v2 τ :
     v1 ⊑{Γ,α,f@Γm1↦Γm2} v2 : τ →
     lrval_refine' Γ α f Γm1 Γm2 (inr v1) (inr v2) (inr τ).
Global Instance lrval_refine:
  RefineT Ti (env Ti) (lrtype Ti) (addr Ti + val Ti) := lrval_refine'.

Inductive expr_refine' (Γ : env Ti) (Γf : funtypes Ti)
     (τs : list (type Ti)) (α : bool) (f : meminj Ti)
     (Γm1 Γm2 : memenv Ti) : expr Ti → expr Ti → lrtype Ti → Prop :=
  | EVar_refine τ n :
     τs !! n = Some τ →
     expr_refine' Γ Γf τs α f Γm1 Γm2 (var{τ} n) (var{τ} n) (inl τ)
  | EVal_refine Ω1 Ω2 v1 v2 τ :
     Ω1 ⊑{Γ,α,f@Γm1↦Γm2} Ω2 → v1 ⊑{Γ,α,f@Γm1↦Γm2} v2 : τ →
     expr_refine' Γ Γf τs α f Γm1 Γm2 (#{Ω1} v1) (#{Ω2} v2) (inr τ)
  | EAddr_refine Ω1 Ω2 a1 a2 τ :
     Ω1 ⊑{Γ,α,f@Γm1↦Γm2} Ω2 →
     a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : Some τ → addr_strict Γ a1 →
     expr_refine' Γ Γf τs α f Γm1 Γm2 (%{Ω1} a1) (%{Ω2} a2) (inl τ)
  | ERtoL_refine e1 e2 τ :
     expr_refine' Γ Γf τs α f Γm1 Γm2 e1 e2 (inr (Some τ.*)) → ✓{Γ} τ →
     expr_refine' Γ Γf τs α f Γm1 Γm2 (.* e1) (.* e2) (inl τ)
  | ERofL_refine e1 e2 τ :
     expr_refine' Γ Γf τs α f Γm1 Γm2 e1 e2 (inl τ) →
     expr_refine' Γ Γf τs α f Γm1 Γm2 (& e1) (& e2) (inr (Some τ.*))
  | EAssign_refine ass e1 e2 e1' e2' τ τ' σ :
     assign_typed Γ τ τ' ass σ →
     expr_refine' Γ Γf τs α f Γm1 Γm2 e1 e2 (inl τ) →
     expr_refine' Γ Γf τs α f Γm1 Γm2 e1' e2' (inr τ') →
     expr_refine' Γ Γf τs α f Γm1 Γm2
       (e1 ::={ass} e1') (e2 ::={ass} e2') (inr σ)
  | ECall_refine g es1 es2 σ σs :
     Γf !! g = Some (σs,σ) →
     Forall3 (expr_refine' Γ Γf τs α f Γm1 Γm2) es1 es2 (inr <$> σs) →
     expr_refine' Γ Γf τs α f Γm1 Γm2 (call g @ es1) (call g @ es2) (inr σ)
  | EAbort_refine τ :
     ✓{Γ} τ → expr_refine' Γ Γf τs α f Γm1 Γm2 (abort τ) (abort τ) (inr τ)
  | ELoad_refine e1 e2 τ :
     expr_refine' Γ Γf τs α f Γm1 Γm2 e1 e2 (inl τ) →
     expr_refine' Γ Γf τs α f Γm1 Γm2 (load e1) (load e2) (inr τ)
  | EEltL_refine e1 e2 rs τ σ  :
     expr_refine' Γ Γf τs α f Γm1 Γm2 e1 e2 (inl τ) → Γ ⊢ rs : τ ↣ σ →
     expr_refine' Γ Γf τs α f Γm1 Γm2 (e1 %> rs) (e2 %> rs) (inl σ)
  | EEltR_refine e1 e2 rs τ σ  :
     expr_refine' Γ Γf τs α f Γm1 Γm2 e1 e2 (inr τ) → Γ ⊢ rs : τ ↣ σ →
     expr_refine' Γ Γf τs α f Γm1 Γm2 (e1 #> rs) (e2 #> rs) (inr σ)
  | EAlloc_refine τ e1 e2 τi :
     ✓{Γ} τ → expr_refine' Γ Γf τs α f Γm1 Γm2 e1 e2 (inr (intT τi)) →
     expr_refine' Γ Γf τs α f Γm1 Γm2
       (alloc{τ} e1) (alloc{τ} e2) (inr (Some τ.*))
  | EFree_refine e1 e2 τ :
     expr_refine' Γ Γf τs α f Γm1 Γm2 e1 e2 (inl τ) →
     expr_refine' Γ Γf τs α f Γm1 Γm2 (free e1) (free e2) (inr voidT)
  | EUnOp_refine op e1 e2 τ σ :
     unop_typed op τ σ → expr_refine' Γ Γf τs α f Γm1 Γm2 e1 e2 (inr τ) →
     expr_refine' Γ Γf τs α f Γm1 Γm2 (@{op} e1) (@{op} e2) (inr σ)
  | EBinOp_refine op e1 e2 e1' e2' τ τ' σ :
     binop_typed op τ τ' σ → expr_refine' Γ Γf τs α f Γm1 Γm2 e1 e2 (inr τ) →
     expr_refine' Γ Γf τs α f Γm1 Γm2 e1' e2' (inr τ') →
     expr_refine' Γ Γf τs α f Γm1 Γm2 (e1 @{op} e1') (e2 @{op} e2') (inr σ)
  | EIf_refine e1 e2 e1' e2' e1'' e2'' τb σ :
     expr_refine' Γ Γf τs α f Γm1 Γm2 e1 e2 (inr (baseT τb)) →
     expr_refine' Γ Γf τs α f Γm1 Γm2 e1' e2' (inr σ) →
     expr_refine' Γ Γf τs α f Γm1 Γm2 e1'' e2'' (inr σ) →
     expr_refine' Γ Γf τs α f Γm1 Γm2
       (if{e1} e1' else e1'') (if{e2} e2' else e2'') (inr σ)
  | EComma_refine e1 e2 e1' e2' τ1 τ2 :
     expr_refine' Γ Γf τs α f Γm1 Γm2 e1 e2 (inr τ1) →
     expr_refine' Γ Γf τs α f Γm1 Γm2 e1' e2' (inr τ2) →
     expr_refine' Γ Γf τs α f Γm1 Γm2 (e1 ,, e1') (e2 ,, e2') (inr τ2)
  | ECast_refine e1 e2 τ σ :
     expr_refine' Γ Γf τs α f Γm1 Γm2 e1 e2 (inr τ) → cast_typed Γ τ σ → 
     expr_refine' Γ Γf τs α f Γm1 Γm2 (cast{σ} e1) (cast{σ} e2) (inr σ)
  | EInsert_refine r e1 e2 e1' e2' τ σ :
     Γ ⊢ r : τ ↣ σ →
     expr_refine' Γ Γf τs α f Γm1 Γm2 e1 e2 (inr σ) →
     expr_refine' Γ Γf τs α f Γm1 Γm2 e1' e2' (inr τ) →
     expr_refine' Γ Γf τs α f Γm1 Γm2 (#[r:=e1]e1') (#[r:=e2]e2') (inr τ).

Global Instance expr_refine:
  RefineT Ti (env Ti * funtypes Ti * list (type Ti))
    (lrtype Ti) (expr Ti) := curry3 expr_refine'.

Section expr_refine_ind.
  Context (Γ : env Ti) (Γf : funtypes Ti) (τs : list (type Ti)).
  Context (α : bool) (f : meminj Ti) (Γm1 Γm2 : memenv Ti).
  Context (P : expr Ti → expr Ti → lrtype Ti → Prop).
  Context (Pvar : ∀ τ n,
    τs !! n = Some τ → P (var{τ} n) (var{τ} n) (inl τ)).
  Context (Pval : ∀ Ω1 Ω2 v1 v2 τ,
    Ω1 ⊑{Γ,α,f@Γm1↦Γm2} Ω2 → v1 ⊑{Γ,α,f@Γm1↦Γm2} v2 : τ →
    P (#{Ω1} v1) (#{Ω2} v2) (inr τ)).
  Context (Paddr : ∀ Ω1 Ω2 a1 a2 τ,
    Ω1 ⊑{Γ,α,f@Γm1↦Γm2} Ω2 → a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : Some τ →
    addr_strict Γ a1 → P (%{Ω1} a1) (%{Ω2} a2) (inl τ)).
  Context (Prtol : ∀ e1 e2 τ,
    e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : inr (Some τ.*) →
    P e1 e2 (inr (Some τ.*)) → ✓{Γ} τ → P (.* e1) (.* e2) (inl τ)).
  Context (Profl : ∀ e1 e2 τ,
    e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : inl τ →
    P e1 e2 (inl τ) → P (& e1) (& e2) (inr (Some τ.*))).
  Context (Passign : ∀ ass e1 e2 e1' e2' τ τ' σ,
    assign_typed Γ τ τ' ass σ →
    e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : inl τ → P e1 e2 (inl τ) →
    e1' ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2' : inr τ' → P e1' e2' (inr τ') →
    P (e1 ::={ass} e1') (e2 ::={ass} e2') (inr σ)).
  Context (Pcall : ∀ g es1 es2 σ σs,
    Γf !! g = Some (σs,σ) →
    es1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2}* es2 :* inr <$> σs →
    Forall3 P es1 es2 (inr <$> σs) → P (call g @ es1) (call g @ es2) (inr σ)).
  Context (Pabort : ∀ τ, ✓{Γ} τ → P (abort τ) (abort τ) (inr τ)).
  Context (Pload : ∀ e1 e2 τ,
    e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : inl τ →
    P e1 e2 (inl τ) → P (load e1) (load e2) (inr τ)).
  Context (Peltl : ∀ e1 e2 rs τ σ,
    e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : inl τ → P e1 e2 (inl τ) → Γ ⊢ rs : τ ↣ σ →
    P (e1 %> rs) (e2 %> rs) (inl σ)).
  Context (Peltr : ∀ e1 e2 rs τ σ,
    e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : inr τ → P e1 e2 (inr τ) → Γ ⊢ rs : τ ↣ σ →
    P (e1 #> rs) (e2 #> rs) (inr σ)).
  Context (Palloc : ∀ τ e1 e2 τi,
    ✓{Γ} τ → e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : inr (intT τi) →
    P e1 e2 (inr (intT τi)) → P (alloc{τ} e1) (alloc{τ} e2) (inr (Some τ.*))).
  Context (Pfree : ∀ e1 e2 τ,
    e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : inl τ → P e1 e2 (inl τ) →
    P (free e1) (free e2) (inr voidT)).
  Context (Punop : ∀ op e1 e2 τ σ,
    unop_typed op τ σ → e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : inr τ →
    P e1 e2 (inr τ) → P (@{op} e1) (@{op} e2) (inr σ)).
  Context (Pbinop : ∀ op e1 e2 e1' e2' τ τ' σ,
    binop_typed op τ τ' σ →
    e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : inr τ → P e1 e2 (inr τ) →
    e1' ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2' : inr τ' → P e1' e2' (inr τ') →
    P (e1 @{op} e1') (e2 @{op} e2') (inr σ)).
  Context (Pif : ∀ e1 e2 e1' e2' e1'' e2'' τb σ,
    e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : inr (baseT τb) → P e1 e2 (inr (baseT τb)) →
    e1' ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2' : inr σ → P e1' e2' (inr σ) →
    e1'' ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2'' : inr σ → P e1'' e2'' (inr σ) →
    P (if{e1} e1' else e1'') (if{e2} e2' else e2'') (inr σ)).
  Context (Pcomma : ∀ e1 e2 e1' e2' τ τ',
    e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : inr τ → P e1 e2 (inr τ) →
    e1' ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2' : inr τ' → P e1' e2' (inr τ') →
    P (e1 ,, e1') (e2 ,, e2') (inr τ')).
  Context (Pcast : ∀ e1 e2 τ σ,
    e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : inr τ → P e1 e2 (inr τ) →
    cast_typed Γ τ σ → P (cast{σ} e1) (cast{σ} e2) (inr σ)).
  Context (Pinsert : ∀ r e1 e2 e1' e2' τ σ,
    Γ ⊢ r : τ ↣ σ →
    e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : inr σ→ P e1 e2 (inr σ) →
    e1' ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2' : inr τ → P e1' e2' (inr τ) →
    P (#[r:=e1]e1') (#[r:=e2]e2') (inr τ)).
  Lemma expr_refine_ind : ∀ e1 e2 τ,
    expr_refine' Γ Γf τs α f Γm1 Γm2 e1 e2 τ → P e1 e2 τ.
  Proof. fix 4; destruct 1; eauto using Forall2_impl, Forall3_impl. Qed.
End expr_refine_ind.

Inductive ectx_item_refine' (Γ : env Ti) (Γf : funtypes Ti) (τs: list (type Ti))
     (α : bool) (f : meminj Ti) (Γm1 Γm2 : memenv Ti) :
     ectx_item Ti → ectx_item Ti → lrtype Ti → lrtype Ti → Prop :=
  | CRtoL_refine τ :
     ✓{Γ} τ →
     ectx_item_refine' Γ Γf τs α f Γm1 Γm2
       (.* □) (.* □) (inr (Some τ.*)) (inl τ)
  | CLtoR_refine τ :
     ectx_item_refine' Γ Γf τs α f Γm1 Γm2 (& □) (& □) (inl τ) (inr (Some τ.*))
  | CAssignL_refine ass e1' e2' τ τ' σ :
     assign_typed Γ τ τ' ass σ → e1' ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2' : inr τ' →
     ectx_item_refine' Γ Γf τs α f Γm1 Γm2
       (□ ::={ass} e1') (□ ::={ass} e2') (inl τ) (inr σ)
  | CAssignR_refine ass e1 e2 τ τ' σ :
     assign_typed Γ τ τ' ass σ → e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : inl τ →
     ectx_item_refine' Γ Γf τs α f Γm1 Γm2
       (e1 ::={ass} □) (e2 ::={ass} □) (inr τ') (inr σ)
  | CCall_refine g es1 es2 es1' es2' σ σs τ σs' :
     Γf !! g = Some (σs ++ τ :: σs', σ) →
     reverse es1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2}* reverse es2 :* inr <$> σs →
     es1' ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2}* es2' :* inr <$> σs' →
     ectx_item_refine' Γ Γf τs α f Γm1 Γm2
       (call g @ es1 □ es1') (call g @ es2 □ es2') (inr τ) (inr σ)
  | CLoad_refine τ :
     ectx_item_refine' Γ Γf τs α f Γm1 Γm2 (load □) (load □) (inl τ) (inr τ)
  | CEltL_refine rs τ σ :
     Γ ⊢ rs : τ ↣ σ →
     ectx_item_refine' Γ Γf τs α f Γm1 Γm2 (□ %> rs) (□ %> rs) (inl τ) (inl σ)
  | CEltR_refine rs τ σ :
     Γ ⊢ rs : τ ↣ σ →
     ectx_item_refine' Γ Γf τs α f Γm1 Γm2 (□ #> rs) (□ #> rs) (inr τ) (inr σ)
  | CAlloc_refine τ τi :
     ✓{Γ} τ → ectx_item_refine' Γ Γf τs α f Γm1 Γm2
       (alloc{τ} □) (alloc{τ} □) (inr (intT τi)) (inr (Some τ.*))
  | CFree_refine τ :
     ectx_item_refine' Γ Γf τs α f Γm1 Γm2 (free □) (free □) (inl τ) (inr voidT)
  | CUnOp_refine op τ σ :
     unop_typed op τ σ →
     ectx_item_refine' Γ Γf τs α f Γm1 Γm2 (@{op} □) (@{op} □) (inr τ) (inr σ)
  | CBinOpL_refine op e1' e2' τ τ' σ :
     binop_typed op τ τ' σ → e1' ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2' : inr τ' →
     ectx_item_refine' Γ Γf τs α f Γm1 Γm2
       (□ @{op} e1') (□ @{op} e2') (inr τ) (inr σ)
  | CBinOpR_refine op e1 e2 τ τ' σ :
     binop_typed op τ τ' σ → e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : inr τ →
     ectx_item_refine' Γ Γf τs α f Γm1 Γm2
       (e1 @{op} □) (e2 @{op} □) (inr τ') (inr σ)
  | CIf_refine e1' e2' e1'' e2'' τb σ :
     e1' ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2' : inr σ →
     e1'' ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2'' : inr σ →
     ectx_item_refine' Γ Γf τs α f Γm1 Γm2
       (if{□} e1' else e1'') (if{□} e2' else e2'') (inr (baseT τb)) (inr σ)
  | CComma_refine e1' e2' τ τ' :
     e1' ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2' : inr τ' →
     ectx_item_refine' Γ Γf τs α f Γm1 Γm2 (□,, e1') (□,, e2') (inr τ) (inr τ')
  | CCast_refine τ σ :
     cast_typed Γ τ σ → ectx_item_refine' Γ Γf τs α f Γm1 Γm2
       (cast{σ} □) (cast{σ} □) (inr τ) (inr σ)
  | CInsertL_refine r e1' e2' τ σ :
     Γ ⊢ r : τ ↣ σ → e1' ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2' : inr τ →
     ectx_item_refine' Γ Γf τs α f Γm1 Γm2
       (#[r:=□]e1') (#[r:=□]e2') (inr σ) (inr τ)
  | CInsertR_refine r e1 e2 τ σ :
     Γ ⊢ r : τ ↣ σ → e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : inr σ →
     ectx_item_refine' Γ Γf τs α f Γm1 Γm2
       (#[r:=e1]□) (#[r:=e2]□) (inr τ) (inr τ).
Global Instance ectx_item_refine:
  PathRefine Ti (env Ti * funtypes Ti * list (type Ti)) (lrtype Ti)
    (lrtype Ti) (ectx_item Ti) := curry3 ectx_item_refine'.
Inductive ectx_refine' (Γs : env Ti * funtypes Ti * list (type Ti))
     (α : bool) (f : meminj Ti) (Γm1 Γm2 : memenv Ti) :
     ectx Ti → ectx Ti → lrtype Ti → lrtype Ti → Prop :=
  | ectx_nil_refine_2 τ : ectx_refine' Γs α f Γm1 Γm2 [] [] τ τ
  | ectx_cons_refine_2 Ei1 Ei2 E1 E2 τ τ' τ'' :
     Ei1 ⊑{Γs,α,f@Γm1↦Γm2} Ei2 : τ ↣ τ' →
     ectx_refine' Γs α f Γm1 Γm2 E1 E2 τ' τ'' →
     ectx_refine' Γs α f Γm1 Γm2 (Ei1 :: E1) (Ei2 :: E2) τ τ''.
Global Instance ectx_refine:
  PathRefine Ti (env Ti * funtypes Ti * list (type Ti)) (lrtype Ti)
    (lrtype Ti) (ectx Ti) := ectx_refine'.

Inductive stmt_refine' (Γ : env Ti) (Γf : funtypes Ti) (τs : list (type Ti))
     (α : bool) (f : meminj Ti) (Γm1 Γm2 : memenv Ti) :
     stmt Ti → stmt Ti → rettype Ti → Prop :=
  | SSkip_refine : stmt_refine' Γ Γf τs α f Γm1 Γm2 skip skip (false,None)
  | SDo_refine e1 e2 τ :
     e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : inr τ →
     stmt_refine' Γ Γf τs α f Γm1 Γm2 (! e1) (! e2) (false,None)
  | SGoto_refine l :
     stmt_refine' Γ Γf τs α f Γm1 Γm2 (goto l) (goto l) (true,None)
  | SThrow_refine n :
     stmt_refine' Γ Γf τs α f Γm1 Γm2 (throw n) (throw n) (true,None)
  | SReturn_refine e1 e2 τ :
     e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : inr τ →
     stmt_refine' Γ Γf τs α f Γm1 Γm2 (ret e1) (ret e2) (true,Some τ)
  | SLabel_refine l :
     stmt_refine' Γ Γf τs α f Γm1 Γm2 (label l) (label l) (false,None)
  | SLocal_refine' τ s1 s2 c mσ :
     ✓{Γ} τ → int_typed (size_of Γ τ) sptrT →
     stmt_refine' Γ Γf (τ :: τs) α f Γm1 Γm2 s1 s2 (c,mσ) →
     stmt_refine' Γ Γf τs α f Γm1 Γm2 (local{τ} s1) (local{τ} s2) (c,mσ)
  | SComp_refine s1 s2 s1' s2' c1 mσ1 c2 mσ2 mσ :
     stmt_refine' Γ Γf τs α f Γm1 Γm2 s1 s2 (c1,mσ1) →
     stmt_refine' Γ Γf τs α f Γm1 Γm2 s1' s2' (c2,mσ2) →
     rettype_union mσ1 mσ2 = Some mσ →
     stmt_refine' Γ Γf τs α f Γm1 Γm2 (s1 ;; s1') (s2 ;; s2') (c2,mσ)
  | SCatch_refine s1 s2 c mσ :
     stmt_refine' Γ Γf τs α f Γm1 Γm2 s1 s2 (c,mσ) →
     stmt_refine' Γ Γf τs α f Γm1 Γm2 (catch s1) (catch s2) (false,mσ)
  | SLoop_refine s1 s2 c mσ :
     stmt_refine' Γ Γf τs α f Γm1 Γm2 s1 s2 (c,mσ) →
     stmt_refine' Γ Γf τs α f Γm1 Γm2 (loop s1) (loop s2) (true,mσ)
  | SIf_refine e1 e2 τb s1 s2 s1' s2' c1 mσ1 c2 mσ2 mσ :
     e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : inr (baseT τb) →
     stmt_refine' Γ Γf τs α f Γm1 Γm2 s1 s2 (c1,mσ1) →
     stmt_refine' Γ Γf τs α f Γm1 Γm2 s1' s2' (c2,mσ2) →
     rettype_union mσ1 mσ2 = Some mσ →
     stmt_refine' Γ Γf τs α f Γm1 Γm2
       (if{e1} s1 else s1') (if{e2} s2 else s2') (c1 && c2, mσ).
Global Instance stmt_refine:
  RefineT Ti (env Ti * funtypes Ti * list (type Ti))
   (rettype Ti) (stmt Ti) := curry3 stmt_refine'.

Inductive sctx_item_refine' (Γ : env Ti) (Γf : funtypes Ti) (τs: list (type Ti))
     (α : bool) (f : meminj Ti) (Γm1 Γm2 : memenv Ti) :
     sctx_item Ti → sctx_item Ti → relation (rettype Ti) :=
  | CCompL_refine s1' s2' c mσ c' mσ' mσr :
     s1' ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} s2' : (c',mσ') →
     rettype_union mσ mσ' = Some mσr →
     sctx_item_refine' Γ Γf τs α f Γm1 Γm2 (□ ;; s1') (□ ;; s2') (c,mσ) (c',mσr)
  | CCompR_refine s1 s2 c mσ c' mσ' mσr :
     s1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} s2 : (c,mσ) →
     rettype_union mσ mσ' = Some mσr →
     sctx_item_refine' Γ Γf τs α f Γm1 Γm2 (s1 ;; □) (s2 ;; □) (c',mσ') (c',mσr)
  | Ccatch_refine c mσ :
     sctx_item_refine' Γ Γf τs α f Γm1 Γm2
       (catch □) (catch □) (c,mσ) (false,mσ)
  | CWhile_refine c mσ :
     sctx_item_refine' Γ Γf τs α f Γm1 Γm2 (loop □) (loop □) (c,mσ) (true,mσ)
  | CIfL_refine e1 e2 τb s1' s2' c mσ c' mσ' mσr :
     e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : inr (baseT τb) →
     s1' ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} s2' : (c',mσ') →
     rettype_union mσ mσ' = Some mσr →
     sctx_item_refine' Γ Γf τs α f Γm1 Γm2
       (if{e1} □ else s1') (if{e2} □ else s2') (c,mσ) (c&&c',mσr)
  | CIfR_refine e1 e2 τb s1 s2 c mσ c' mσ' mσr :
     e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : inr (baseT τb) →
     s1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} s2 : (c,mσ) →
     rettype_union mσ mσ' = Some mσr →
     sctx_item_refine' Γ Γf τs α f Γm1 Γm2
       (if{e1} s1 else □) (if{e2} s2 else □) (c',mσ') (c&&c',mσr).
Global Instance sctx_refine:
  PathRefine Ti (env Ti * funtypes Ti * list (type Ti)) (rettype Ti)
    (rettype Ti) (sctx_item Ti) := curry3 sctx_item_refine'.

Inductive esctx_item_refine' (Γ : env Ti) (Γf: funtypes Ti) (τs: list (type Ti))
     (α : bool) (f : meminj Ti) (Γm1 Γm2 : memenv Ti) :
     esctx_item Ti → esctx_item Ti → type Ti → rettype Ti → Prop :=
  | CDoE_refine τ :
     esctx_item_refine' Γ Γf τs α f Γm1 Γm2 (! □) (! □) τ (false,None)
  | CReturnE_refine τ :
     esctx_item_refine' Γ Γf τs α f Γm1 Γm2 (ret □) (ret □) τ (true,Some τ)
  | CIfE_refine τb s1 s2 s1' s2' c mσ c' mσ' mσr :
     s1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} s2 : (c,mσ) →
     s1' ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} s2' : (c',mσ') →
     rettype_union mσ mσ' = Some mσr →
     esctx_item_refine' Γ Γf τs α f Γm1 Γm2
       (if{□} s1 else s1')%S (if{□} s2 else s2')%S (baseT τb) (c&&c',mσr).
Global Instance esctx_item_refine:
  PathRefine Ti (env Ti * funtypes Ti * list (type Ti)) (type Ti)
    (rettype Ti) (esctx_item Ti) := curry3 esctx_item_refine'.

Inductive ctx_item_refine' (Γ : env Ti) (Γf: funtypes Ti) (τs: list (type Ti))
     (α : bool) (f : meminj Ti) (Γm1 Γm2 : memenv Ti) :
     ctx_item Ti → ctx_item Ti → focustype Ti → focustype Ti → Prop :=
  | CStmt_refine Es1 Es2 cmσ cmσ' :
     Es1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} Es2 : cmσ ↣ cmσ' →
     ctx_item_refine' Γ Γf τs α f Γm1 Γm2
       (CStmt Es1) (CStmt Es2) (Stmt_type cmσ) (Stmt_type cmσ')
  | CLocal_refine o1 o2 τ c mσ :
     Γm1 ⊢ o1 : τ → Γm2 ⊢ o2 : τ → f !! o1 = Some (o2,[]) →
     ctx_item_refine' Γ Γf τs α f Γm1 Γm2
       (CLocal o1 τ) (CLocal o2 τ) (Stmt_type (c,mσ)) (Stmt_type (c,mσ))
  | CExpr_refine e1 e2 Ee1 Ee2 τ cmσ :
     e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : inr τ →
     Ee1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} Ee2 : τ ↣ cmσ →
     ctx_item_refine' Γ Γf τs α f Γm1 Γm2
       (CExpr e1 Ee1) (CExpr e2 Ee2) (Expr_type τ) (Stmt_type cmσ)
  | CFun_refine E1 E2 g σs τ σ :
     Γf !! g = Some (σs,τ) →
     E1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} E2 : inr τ ↣ inr σ →
     ctx_item_refine' Γ Γf τs α f Γm1 Γm2
       (CFun E1) (CFun E2) (Fun_type g) (Expr_type σ)
  | CParams_refine g os1 os2 σs cmσ σ :
     Γf !! g = Some (σs,σ) →
     Γm1 ⊢* os1 :* σs → Γm2 ⊢* os2 :* σs →
     Forall2 (λ o1 o2, f !! o1 = Some (o2,[])) os1 os2 →
     rettype_match cmσ σ →
     ctx_item_refine' Γ Γf τs α f Γm1 Γm2 (CParams g (zip os1 σs))
       (CParams g (zip os2 σs)) (Stmt_type cmσ) (Fun_type g).
Global Instance ctx_item_refine:
  PathRefine Ti (env Ti * funtypes Ti * list (type Ti))
    (focustype Ti) (focustype Ti) (ctx_item Ti) := curry3 ctx_item_refine'.
Inductive ctx_refine' (Γs : env Ti * funtypes Ti)
     (α : bool) (f : meminj Ti) (Γm1 Γm2 : memenv Ti) :
     ctx Ti → ctx Ti → focustype Ti → focustype Ti → Prop :=
  | ctx_nil_refine_2 τf : ctx_refine' Γs α f Γm1 Γm2 [] [] τf τf
  | ctx_cons_refine_2 Ek1 Ek2 k1 k2 τf τf' τf'' :
     Ek1 ⊑{(Γs,get_stack_types k1),α,f@Γm1↦Γm2} Ek2 : τf ↣ τf' →
     ctx_refine' Γs α f Γm1 Γm2 k1 k2 τf' τf'' →
     ctx_refine' Γs α f Γm1 Γm2 (Ek1 :: k1) (Ek2 :: k2) τf τf''.
Global Instance ctx_refine: PathRefine Ti (env Ti * funtypes Ti)
  (focustype Ti) (focustype Ti) (ctx Ti) := ctx_refine'.

Inductive direction_refine' (Γ : env Ti) (α : bool) (f : meminj Ti)
     (Γm1 Γm2: memenv Ti) : direction Ti → direction Ti → rettype Ti → Prop :=
  | Down_refine cmτ : direction_refine' Γ α f Γm1 Γm2 ↘ ↘ cmτ
  | Up_refine mτ : direction_refine' Γ α f Γm1 Γm2 ↗ ↗ (false,mτ)
  | Top_refine c v1 v2 τ :
     v1 ⊑{Γ,α,f@Γm1↦Γm2} v2 : τ →
     direction_refine' Γ α f Γm1 Γm2 (⇈ v1) (⇈ v2) (c,Some τ)
  | Goto_refine l cmτ : direction_refine' Γ α f Γm1 Γm2 (↷ l) (↷ l) cmτ
  | Throw_refine n cmτ : direction_refine' Γ α f Γm1 Γm2 (↑ n) (↑ n) cmτ.
Global Instance direction_refine: RefineT Ti (env Ti)
  (rettype Ti) (direction Ti) := direction_refine'.

Inductive focus_refine' (Γ : env Ti) (Γf : funtypes Ti) (τs : list (type Ti))
     (α : bool) (f : meminj Ti) (Γm1 Γm2 : memenv Ti) :
     focus Ti → focus Ti → focustype Ti → Prop :=
  | Stmt_refine d1 d2 s1 s2 cmσ :
     s1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} s2 : cmσ →
     d1 ⊑{Γ,α,f@Γm1↦Γm2} d2 : cmσ →
     focus_refine' Γ Γf τs α f Γm1 Γm2 (Stmt d1 s1) (Stmt d2 s2) (Stmt_type cmσ)
  | Expr_refine e1 e2 τ :
     e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : inr τ →
     focus_refine' Γ Γf τs α f Γm1 Γm2 (Expr e1) (Expr e2) (Expr_type τ)
  | Call_refine g vs1 vs2 σs σ :
     Γf !! g = Some (σs,σ) →
     vs1 ⊑{Γ,α,f@Γm1↦Γm2}* vs2 :* σs →
     focus_refine' Γ Γf τs α f Γm1 Γm2 (Call g vs1) (Call g vs2) (Fun_type g)
  | Return_refine g σs σ v1 v2 :
     Γf !! g = Some (σs, σ) →
     v1 ⊑{Γ,α,f@Γm1↦Γm2} v2 : σ →
     focus_refine' Γ Γf τs α f Γm1 Γm2 (Return g v1) (Return g v2) (Fun_type g)
  | UndefExpr_refine E1 E2 e1 e2 τlr τ :
     e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : τlr →
     E1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} E2 : τlr ↣ inr τ →
     focus_refine' Γ Γf τs α f Γm1 Γm2
       (Undef (UndefExpr E1 e1)) (Undef (UndefExpr E2 e2)) (Expr_type τ)
  | UndefBranch_refine Es1 Es2 Ω1 Ω2 v1 v2 τ mσ :
     v1 ⊑{Γ,α,f@Γm1↦Γm2} v2 : τ →
     Es1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} Es2 : τ ↣ mσ → Ω1 ⊑{Γ,α,f@Γm1↦Γm2} Ω2 →
     focus_refine' Γ Γf τs α f Γm1 Γm2 (Undef (UndefBranch Es1 Ω1 v1))
       (Undef (UndefBranch Es2 Ω2 v2)) (Stmt_type mσ).
Global Instance focus_refine:
  RefineT Ti (env Ti * funtypes Ti * list (type Ti))
    (focustype Ti) (focus Ti) := curry3 focus_refine'.

Inductive state_refine' (Γ : env Ti) (Γf : funtypes Ti) (α : bool)
     (f : meminj Ti) : state Ti → state Ti → funname → Prop :=
  | State_refine k1 φ1 m1 k2 φ2 m2 τf g :
     φ1 ⊑{(Γ,Γf,get_stack_types k1),α,f@'{m1}↦'{m2}} φ2 : τf →
     k1 ⊑{(Γ,Γf),α,f@'{m1}↦'{m2}} k2 : τf ↣ Fun_type g →
     m1 ⊑{Γ,α,f} m2 →
     state_refine' Γ Γf α f (State k1 φ1 m1) (State k2 φ2 m2) g
  | Undef_State_refine S1 S2 g :
     α → (Γ,Γf) ⊢ S1 : g → (Γ,Γf) ⊢ S2 : g → is_undef_state S1 →
     state_refine' Γ Γf α f S1 S2 g.
Global Instance state_refine : RefineTM Ti (env Ti * funtypes Ti)
    funname (state Ti) := curry state_refine'.

Global Instance funenv_refine:
    RefineT Ti (env Ti) (funtypes Ti) (funenv Ti) := λ Γ α f Γm1 Γm2 δ1 δ2 Γf,
  map_Forall3 (λ s1 s2 τsτ, let '(τs,τ) := τsτ in ∃ cmτ,
    ✓{Γ}* τs ∧ Forall (λ τ', int_typed (size_of Γ τ') sptrT) τs ∧ ✓{Γ} τ ∧
    s1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} s2 : cmτ ∧ rettype_match cmτ τ ∧
    gotos s1 ⊆ labels s1 ∧ throws_valid 0 s1
  ) δ1 δ2 Γf.
End refinements.

Section properties.
Context `{EnvSpec Ti}.
Implicit Types Γ : env Ti.
Implicit Types α : bool.
Implicit Types Γf : funtypes Ti.
Implicit Types o : index.
Implicit Types Γm : memenv Ti.
Implicit Types m : mem Ti.
Implicit Types e : expr Ti.
Implicit Types es : list (expr Ti).
Implicit Types s : stmt Ti.
Implicit Types τ σ : type Ti.
Implicit Types a : addr Ti.
Implicit Types v : val Ti.
Implicit Types av : addr Ti + val Ti.
Implicit Types d : direction Ti.
Implicit Types Ei : ectx_item Ti.
Implicit Types E : ectx Ti.
Implicit Types Es : sctx_item Ti.
Implicit Types Ee : esctx_item Ti.
Implicit Types Ek : ctx_item Ti.
Implicit Types k : ctx Ti.
Implicit Types φ : focus Ti.

Ltac solve_length := simplify_equality'; repeat
  match goal with H : Forall2 _ _ _ |- _ => apply Forall2_length in H end; lia.

Lemma EVal_refine_inv_l Γ Γf α f Γm1 Γm2 τs Ωs1 vs1 es2 σs :
  #{Ωs1}* vs1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2}* es2 :* inr <$> σs →
  length vs1 = length Ωs1 →
  ∃ Ωs2 vs2, es2 = #{Ωs2}* vs2 ∧ Ωs1 ⊑{Γ,α,f@Γm1↦Γm2}* Ωs2 ∧
    length Ωs2 = length vs2 ∧ vs1 ⊑{Γ,α,f@Γm1↦Γm2}* vs2 :* σs.
Proof.
  rewrite <-Forall2_same_length.
  revert Ωs1 vs1 σs. induction es2 as [|?? IH]; intros ?? [|??];
    inversion 1; destruct 1; intros; simplify_equality'; refine_inversion_all.
  { eexists [], []; repeat constructor. }
  edestruct IH as (?&?&?&?&?&?); eauto. subst.
  eexists (_ :: _), (_ :: _);
    split_ands; simpl; eauto using Forall3_cons with arith.
Qed.
Lemma EVal_refine_inv_r Γ Γf α f Γm1 Γm2 τs es1 Ωs2 vs2 σs :
  es1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2}* #{Ωs2}* vs2 :* inr <$> σs →
  length vs2 = length Ωs2 →
  ∃ Ωs1 vs1, es1 = #{Ωs1}* vs1 ∧ Ωs1 ⊑{Γ,α,f@Γm1↦Γm2}* Ωs2 ∧
    length Ωs1 = length vs1 ∧ vs1 ⊑{Γ,α,f@Γm1↦Γm2}* vs2 :* σs.
Proof.
  rewrite <-Forall2_same_length.
  revert Ωs2 vs2 σs. induction es1 as [|?? IH]; intros ?? [|??];
    inversion 1; destruct 1; intros; simplify_equality'; refine_inversion_all.
  { eexists [], []; repeat constructor. }
  edestruct IH as (?&?&?&?&?&?); eauto. subst.
  eexists (_ :: _), (_ :: _);
    split_ands; simpl; eauto using Forall3_cons with arith.
Qed.
Lemma ectx_item_subst_refine Γ Γf α f Γm1 Γm2 τs Ei1 Ei2 e1 e2 τlr τlr' :
  Ei1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} Ei2 : τlr ↣ τlr' →
  e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : τlr →
  subst Ei1 e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} subst Ei2 e2 : τlr'.
Proof.
  destruct 1; simpl; refine_constructor; eauto.
  rewrite ?fmap_app; eauto using Forall3_app, Forall3_cons.
Qed.
Lemma ectx_subst_refine Γ Γf α f Γm1 Γm2 τs E1 E2 e1 e2 τlr τlr' :
  E1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} E2 : τlr ↣ τlr' →
  e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : τlr →
  subst E1 e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} subst E2 e2 : τlr'.
Proof.
  intros HE. revert e1 e2.
  induction HE; simpl; eauto using ectx_item_subst_refine.
Qed.
Lemma sctx_item_subst_refine Γ Γf α f Γm1 Γm2 τs Es1 Es2 s1 s2 mcτ mcτ' :
  Es1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} Es2 : mcτ ↣ mcτ' →
  s1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} s2 : mcτ →
  subst Es1 s1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} subst Es2 s2 : mcτ'.
Proof. destruct 1; simpl; refine_constructor; eauto. Qed.
Lemma ectx_item_subst_refine_inv_r Γ Γf α f Γm1 Γm2 τs e1 Ei2 e2 τlr' :
  e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} subst Ei2 e2 : τlr' →
  ∃ e1' Ei1 τlr, e1 = subst Ei1 e1' ∧
    Ei1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} Ei2 : τlr ↣ τlr' ∧
    e1' ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : τlr.
Proof.
  intros He; destruct Ei2; refine_inversion He; list_simplifier;
    try match goal with
    | H : ?E ⊑{_,_,_@_↦_}* reverse _ :* _ |- _ =>
       rewrite <-(reverse_involutive E) in H
    end; by do 3 eexists; split_ands;
     repeat refine_constructor; simpl; eauto; rewrite ?reverse_involutive.
Qed.
Lemma ectx_subst_refine_inv_r Γ Γf α f Γm1 Γm2 τs e1 E2 e2 τlr' :
  e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} subst E2 e2 : τlr' →
  ∃ e1' E1 τlr, e1 = subst E1 e1' ∧
    E1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} E2 : τlr ↣ τlr' ∧
    e1' ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : τlr.
Proof.
  revert e2. induction E2 as [|Ei2 E2 IH]; intros e2 He; simpl in *.
  { by eexists e1, [], τlr'; split_ands; repeat refine_constructor. }
  destruct (IH (subst Ei2 e2)) as (e1'&E1&τlr&->&?&?); auto.
  destruct (ectx_item_subst_refine_inv_r Γ Γf α f Γm1 Γm2 τs e1' Ei2 e2 τlr)
    as (e1&Ee1&τlr''&->&?&?); auto.
  exists e1 (Ee1 :: E1) τlr''; split_ands; repeat refine_constructor; eauto.
Qed.
Lemma esctx_item_subst_refine_inv_r Γ Γf α f Γm1 Γm2 τs s1 Ee2 e2 mcτ :
  s1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} subst Ee2 e2 : mcτ →
  ∃ e1' Ee1 τ, s1 = subst Ee1 e1' ∧
    Ee1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} Ee2 : τ ↣ mcτ ∧
    e1' ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : inr τ.
Proof.
  by destruct Ee2; inversion 1; subst;
    do 3 eexists; split_ands; repeat refine_constructor; eauto.
Qed.
Lemma sctx_item_subst_refine_inv_r Γ Γf α f Γm1 Γm2 τs s1 Es2 s2 mcτ' :
  s1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} subst Es2 s2 : mcτ' →
  ∃ s1' Es1 mcτ, s1 = subst Es1 s1' ∧
    Es1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} Es2 : mcτ ↣ mcτ' ∧
    s1' ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} s2 : mcτ.
Proof.
  by destruct Es2; inversion 1; subst;
    do 3 eexists; split_ands; repeat refine_constructor; eauto.
Qed.

Lemma expr_refine_nf_inv Γ Γf α f Γm1 Γm2 τs e1 e2 τlr :
  e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : τlr → is_nf e2 → is_nf e1.
Proof. destruct 1; inversion_clear 1; constructor. Qed.
Lemma exprs_refine_nf_inv Γ Γf α f Γm1 Γm2 τs es1 es2 τlrs :
  es1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2}* es2 :* τlrs →
  Forall is_nf es2 → Forall is_nf es1.
Proof. induction 1; inversion_clear 1; eauto using expr_refine_nf_inv. Qed.
Lemma expr_refine_redex_inv Γ Γf α f Γm1 Γm2 τs e1 e2 τlr :
  e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : τlr → is_redex e2 → is_redex e1.
Proof.
  destruct 1; inversion_clear 1;
    constructor; eauto using expr_refine_nf_inv, exprs_refine_nf_inv.
Qed.
Lemma stmt_refine_gotos Γ Γf α f Γm1 Γm2 τs s1 s2 mcτ :
  s1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} s2 : mcτ → gotos s1 = gotos s2.
Proof. induction 1; simpl; auto with f_equal. Qed.
Lemma stmt_refine_labels Γ Γf α f Γm1 Γm2 τs s1 s2 mcτ :
  s1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} s2 : mcτ → labels s1 = labels s2.
Proof. induction 1; simpl; auto with f_equal. Qed.
Lemma stmt_refine_labels_elem_of_r Γ Γf α f Γm1 Γm2 τs s1 s2 mcτ :
  s1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} s2 : mcτ → labels s1 = labels s2.
Proof. induction 1; simpl; auto with f_equal. Qed.
Lemma stmt_refine_throws_valid Γ Γf α f Γm1 Γm2 τs s1 s2 mcτ n :
  s1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} s2 : mcτ → throws_valid n s1 → throws_valid n s2.
Proof. intros Hs. revert n. induction Hs; naive_solver. Qed.
Lemma ctx_refine_stack_types Γ α f Γm1 Γm2 Γf k1 k2 τf τf' :
  ✓ Γ → k1 ⊑{(Γ,Γf),α,f@Γm1↦Γm2} k2 : τf ↣ τf' →
  get_stack_types k1 = get_stack_types k2.
Proof.
  assert (∀ (os1 os2 : list index) (σs : list (type Ti)) P,
    Forall2 P os1 os2 → snd <$> zip os1 σs = snd <$> zip os2 σs).
  { intros os1 os2 σs P Hos. revert σs.
    induction Hos; intros [|??]; f_equal'; auto. }
  induction 2 as [|??????? []]; simpl; eauto with f_equal.
Qed.
Lemma ctx_refine_stack Γ Γf α f Γm1 Γm2 k1 k2 τf τf' :
  ✓ Γ → k1 ⊑{(Γ,Γf),α,f@Γm1↦Γm2} k2 : τf ↣ τf' →
  Forall2 (λ o1 o2, f !! o1 = Some (o2, [])) (get_stack k1) (get_stack k2).
Proof.
  induction 2 as [|??????? []]; simpl;
    rewrite ?fst_zip by solve_length; auto using Forall2_app.
Qed.
Lemma sctx_item_catch_refine Γ Γf α f Γm1 Γm2 τs Es1 Es2 s1 s2 mcτ mcτ' :
  Es1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} Es2 : mcτ ↣ mcτ' →
  Es1 = catch □ → Es2 = catch □.
Proof. by destruct 1. Qed.  
Lemma direction_in_refine_r Γ Γf τs α f Γm1 Γm2 s1 s2 d1 d2 mcτ :
  s1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} s2 : mcτ →
  d1 ⊑{Γ,α,f@Γm1↦Γm2} d2 : mcτ → direction_in d2 s2 → direction_in d1 s1.
Proof. by destruct 2; simpl; erewrite <-?stmt_refine_labels by eauto. Qed.
Lemma direction_out_refine_r Γ Γf τs α f Γm1 Γm2 s1 s2 d1 d2 mcτ :
  s1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} s2 : mcτ →
  d1 ⊑{Γ,α,f@Γm1↦Γm2} d2 : mcτ → direction_out d2 s2 → direction_out d1 s1.
Proof. by destruct 2; simpl; erewrite <-?stmt_refine_labels by eauto. Qed.
Lemma funenv_lookup_refine_r Γ α f Γm1 Γm2 δ1 δ2 Γf g s2 :
  δ1 ⊑{Γ,α,f@Γm1↦Γm2} δ2 : Γf → δ2 !! g = Some s2 → ∃ s1 τs τ cmτ,
    δ1 !! g = Some s1 ∧ Γf !! g = Some (τs,τ) ∧
    ✓{Γ}* τs ∧ Forall (λ τ', int_typed (size_of Γ τ') sptrT) τs ∧ ✓{Γ} τ ∧
    s1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} s2 : cmτ ∧ rettype_match cmτ τ ∧
    gotos s1 ⊆ labels s1 ∧ throws_valid 0 s1.
Proof. intros Hδ ?; specialize (Hδ g); repeat case_match; naive_solver. Qed.
Lemma state_refine_mem Γ Γf α f S1 S2 g :
  ¬is_undef_state S1 → S1 ⊑{(Γ,Γf),α,f} S2 : g → '{SMem S1} ⊑{Γ,α,f} '{SMem S2}.
Proof. by destruct 2; eauto using cmap_refine_memenv_refine'. Qed.

Lemma lrval_refine_typed_l Γ α f Γm1 Γm2 av1 av2 τlr :
  ✓ Γ → av1 ⊑{Γ,α,f@Γm1↦Γm2} av2 : τlr → (Γ,Γm1) ⊢ av1 : τlr.
Proof.
  destruct 2; typed_constructor;
    eauto using val_refine_typed_l, addr_refine_typed_l.
Qed.
Lemma expr_refine_typed_l Γ α f Γm1 Γm2 Γf τs e1 e2 τlr :
  ✓ Γ → e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : τlr → (Γ,Γf,Γm1,τs) ⊢ e1 : τlr.
Proof.
  assert (∀ es1 es2 τlrs,
    Forall3 (λ e1 _ τlr, (Γ,Γf,Γm1,τs) ⊢ e1 : τlr) es1 es2 τlrs →
    (Γ,Γf,Γm1,τs) ⊢* es1 :* τlrs).
  { induction 1; constructor; eauto. }
  induction 2 using @expr_refine_ind; typed_constructor;
    eauto using val_refine_typed_l, addr_refine_typed_l, locks_refine_valid_l.
Qed.
Lemma exprs_refine_typed_l Γ α f Γm1 Γm2 Γf τs es1 es2 τlrs :
  ✓ Γ → es1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2}* es2 :* τlrs →
  (Γ,Γf,Γm1,τs) ⊢* es1 :* τlrs.
Proof. induction 2; eauto using expr_refine_typed_l. Qed.
Lemma ectx_item_refine_typed_l Γ α f Γm1 Γm2 Γf τs Ei1 Ei2 τlr τlr' :
  ✓ Γ → Ei1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} Ei2 : τlr ↣ τlr' →
  (Γ,Γf,Γm1,τs) ⊢ Ei1 : τlr ↣ τlr'.
Proof.
  destruct 2; typed_constructor;
    eauto using expr_refine_typed_l, exprs_refine_typed_l.
Qed.
Lemma ectx_refine_typed_l Γ α f Γm1 Γm2 Γf τs E1 E2 τlr τlr' :
  ✓ Γ → E1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} E2 : τlr ↣ τlr' →
  (Γ,Γf,Γm1,τs) ⊢ E1 : τlr ↣ τlr'.
Proof. induction 2;typed_constructor; eauto using ectx_item_refine_typed_l. Qed.
Lemma stmt_refine_typed_l Γ α f Γm1 Γm2 Γf τs s1 s2 mcτ :
  ✓ Γ → s1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} s2 : mcτ → (Γ,Γf,Γm1,τs) ⊢ s1 : mcτ.
Proof. induction 2; typed_constructor; eauto using expr_refine_typed_l. Qed.
Lemma sctx_item_refine_typed_l Γ α f Γm1 Γm2 Γf τs Es1 Es2 mcτ mcτ' :
  ✓ Γ → Es1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} Es2 : mcτ ↣ mcτ' →
  (Γ,Γf,Γm1,τs) ⊢ Es1 : mcτ ↣ mcτ'.
Proof.
  destruct 2; typed_constructor;
    eauto using stmt_refine_typed_l, expr_refine_typed_l.
Qed.
Lemma esctx_item_refine_typed_l Γ α f Γm1 Γm2 Γf τs Ee1 Ee2 τlr mcτ :
  ✓ Γ → Ee1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} Ee2 : τlr ↣ mcτ →
  (Γ,Γf,Γm1,τs) ⊢ Ee1 : τlr ↣ mcτ.
Proof. destruct 2; typed_constructor; eauto using stmt_refine_typed_l. Qed.
Lemma ctx_item_refine_typed_l Γ α f Γm1 Γm2 Γf τs Ek1 Ek2 τf τf' :
  ✓ Γ → Ek1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} Ek2 : τf ↣ τf' →
  (Γ,Γf,Γm1,τs) ⊢ Ek1 : τf ↣ τf'.
Proof.
  destruct 2; typed_constructor; eauto using expr_refine_typed_l,
    esctx_item_refine_typed_l, sctx_item_refine_typed_l, ectx_refine_typed_l.
Qed.
Lemma ctx_refine_typed_l Γ α f Γm1 Γm2 Γf k1 k2 τf τf' :
  ✓ Γ → k1 ⊑{(Γ,Γf),α,f@Γm1↦Γm2} k2 : τf ↣ τf' → (Γ,Γf,Γm1) ⊢ k1 : τf ↣ τf'.
Proof. induction 2; typed_constructor; eauto using ctx_item_refine_typed_l. Qed.
Lemma direction_refine_typed_l Γ α f Γm1 Γm2 d1 d2 τlr :
  ✓ Γ → d1 ⊑{Γ,α,f@Γm1↦Γm2} d2 : τlr → (Γ,Γm1) ⊢ d1 : τlr.
Proof. destruct 2; typed_constructor; eauto using val_refine_typed_l. Qed.
Lemma focus_refine_typed_l Γ α f Γm1 Γm2 Γf τs φ1 φ2 τf :
  ✓ Γ → φ1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} φ2 : τf → (Γ,Γf,Γm1,τs) ⊢ φ1 : τf.
Proof.
  induction 2; typed_constructor; eauto using stmt_refine_typed_l,
    direction_refine_typed_l, expr_refine_typed_l, vals_refine_typed_l,
    val_refine_typed_l, ectx_refine_typed_l, esctx_item_refine_typed_l,
    locks_refine_valid_l.
Qed.
Lemma state_refine_typed_l Γ α f Γf S1 S2 g :
  ✓ Γ → S1 ⊑{(Γ,Γf),α,f} S2 : g → (Γ,Γf) ⊢ S1 : g.
Proof.
  destruct 2; do 2 red; eauto 10 using focus_refine_typed_l,
    ctx_refine_typed_l, cmap_refine_valid_l'.
Qed.
Lemma funenv_refine_typed_l Γ α f Γm1 Γm2 δ1 δ2 Γf :
  ✓ Γ → δ1 ⊑{Γ,α,f@Γm1↦Γm2} δ2 : Γf → (Γ,Γm1) ⊢ δ1 : Γf.
Proof.
  intros ? Hδ; split.
  * intros g s ?; specialize (Hδ g); destruct (δ2 !! _),
      (Γf !! _) as [[τs τ]|]; simplify_option_equality; try done.
    destruct Hδ as (cmτ&?&?&?&?&?&?&?); eauto 15 using stmt_refine_typed_l.
  * rewrite elem_of_subseteq; intros g; rewrite !elem_of_dom.
    intros [[τs τ] ?]; specialize (Hδ g); destruct (δ1 !! _),
      (δ2 !! _); simplify_option_equality; naive_solver.
Qed.

Lemma lrval_refine_typed_r Γ α f Γm1 Γm2 av1 av2 τlr :
  ✓ Γ → av1 ⊑{Γ,α,f@Γm1↦Γm2} av2 : τlr → (Γ,Γm2) ⊢ av2 : τlr.
Proof.
  destruct 2; typed_constructor;
    eauto using val_refine_typed_r, addr_refine_typed_r, addr_strict_refine.
Qed.
Lemma expr_refine_typed_r Γ α f Γm1 Γm2 Γf τs e1 e2 τlr :
  ✓ Γ → e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : τlr → (Γ,Γf,Γm2,τs) ⊢ e2 : τlr.
Proof.
  assert (∀ es1 es2 τlrs,
    Forall3 (λ _ e2 τlr, (Γ,Γf,Γm2,τs) ⊢ e2 : τlr) es1 es2 τlrs →
    (Γ,Γf,Γm2,τs) ⊢* es2 :* τlrs).
  { induction 1; constructor; eauto. }
  induction 2 using @expr_refine_ind; typed_constructor;
    eauto using val_refine_typed_r, addr_refine_typed_r,
    addr_strict_refine, locks_refine_valid_r.
Qed.
Lemma exprs_refine_typed_r Γ α f Γm1 Γm2 Γf τs es1 es2 τlrs :
  ✓ Γ → es1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2}* es2 :* τlrs →(Γ,Γf,Γm2,τs) ⊢* es2 :* τlrs.
Proof. induction 2; eauto using expr_refine_typed_r. Qed.
Lemma ectx_item_refine_typed_r Γ α f Γm1 Γm2 Γf τs Ei1 Ei2 τlr τlr' :
  ✓ Γ → Ei1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} Ei2 : τlr ↣ τlr' →
  (Γ,Γf,Γm2,τs) ⊢ Ei2 : τlr ↣ τlr'.
Proof.
  destruct 2; typed_constructor;
    eauto using expr_refine_typed_r, exprs_refine_typed_r.
Qed.
Lemma ectx_refine_typed_r Γ α f Γm1 Γm2 Γf τs E1 E2 τlr τlr' :
  ✓ Γ → E1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} E2 : τlr ↣ τlr' →
  (Γ,Γf,Γm2,τs) ⊢ E2 : τlr ↣ τlr'.
Proof. induction 2;typed_constructor; eauto using ectx_item_refine_typed_r. Qed.
Lemma stmt_refine_typed_r Γ f α Γm1 Γm2 Γf τs s1 s2 mcτ :
  ✓ Γ → s1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} s2 : mcτ → (Γ,Γf,Γm2,τs) ⊢ s2 : mcτ.
Proof. induction 2; typed_constructor; eauto using expr_refine_typed_r. Qed.
Lemma sctx_item_refine_typed_r Γ α f Γm1 Γm2 Γf τs Es1 Es2 mcτ mcτ' :
  ✓ Γ → Es1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} Es2 : mcτ ↣ mcτ' →
  (Γ,Γf,Γm2,τs) ⊢ Es2 : mcτ ↣ mcτ'.
Proof.
  destruct 2; typed_constructor;
    eauto using stmt_refine_typed_r, expr_refine_typed_r.
Qed.
Lemma esctx_item_refine_typed_r Γ α f Γm1 Γm2 Γf τs Ee1 Ee2 τlr mcτ :
  ✓ Γ → Ee1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} Ee2 : τlr ↣ mcτ →
  (Γ,Γf,Γm2,τs) ⊢ Ee2 : τlr ↣ mcτ.
Proof. destruct 2; typed_constructor; eauto using stmt_refine_typed_r. Qed.
Lemma ctx_item_refine_typed_r Γ α f Γm1 Γm2 Γf τs Ek1 Ek2 τf τf' :
  ✓ Γ → Ek1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} Ek2 : τf ↣ τf' →
  (Γ,Γf,Γm2,τs) ⊢ Ek2 : τf ↣ τf'.
Proof.
  destruct 2; typed_constructor; eauto using expr_refine_typed_r,
    esctx_item_refine_typed_r, sctx_item_refine_typed_r, ectx_refine_typed_r.
Qed.
Lemma ctx_refine_typed_r Γ α f Γm1 Γm2 Γf k1 k2 τf τf' :
  ✓ Γ → k1 ⊑{(Γ,Γf),α,f@Γm1↦Γm2} k2 : τf ↣ τf' → (Γ,Γf,Γm2) ⊢ k2 : τf ↣ τf'.
Proof.
  induction 2; typed_constructor; erewrite <-?ctx_refine_stack_types by eauto;
    eauto using ctx_item_refine_typed_r.
Qed.
Lemma direction_refine_typed_r Γ α f Γm1 Γm2 d1 d2 τlr :
  ✓ Γ → d1 ⊑{Γ,α,f@Γm1↦Γm2} d2 : τlr → (Γ,Γm2) ⊢ d2 : τlr.
Proof. destruct 2; typed_constructor; eauto using val_refine_typed_r. Qed.
Lemma focus_refine_typed_r Γ α f Γm1 Γm2 Γf τs φ1 φ2 τf :
  ✓ Γ → φ1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} φ2 : τf → (Γ,Γf,Γm2,τs) ⊢ φ2 : τf.
Proof.
  induction 2; typed_constructor; eauto using stmt_refine_typed_r,
    direction_refine_typed_r, expr_refine_typed_r, vals_refine_typed_r,
    val_refine_typed_r, ectx_refine_typed_r, esctx_item_refine_typed_r,
    locks_refine_valid_r.
Qed.
Lemma state_refine_typed_r Γ α f Γf S1 S2 g :
  ✓ Γ → S1 ⊑{(Γ,Γf),α,f} S2 : g → (Γ,Γf) ⊢ S2 : g.
Proof.
  destruct 2; eauto. eexists; split_ands;
    erewrite <-?ctx_refine_stack_types by eauto;
    eauto using focus_refine_typed_r, ctx_refine_typed_r, cmap_refine_valid_r'.
Qed.
Lemma funenv_refine_typed_r Γ α f Γm1 Γm2 δ1 δ2 Γf :
  ✓ Γ → δ1 ⊑{Γ,α,f@Γm1↦Γm2} δ2 : Γf → (Γ,Γm2) ⊢ δ2 : Γf.
Proof.
  intros ? Hδ; split.
  * intros g s ?; specialize (Hδ g); destruct (δ1 !! _),
      (Γf !! _) as [[τs τ]|]; simplify_option_equality; try done.
    destruct Hδ as (cmτ&?&?&?&?&?&?&?).
    erewrite <-stmt_refine_labels, <-stmt_refine_gotos by eauto.
    eauto 15 using stmt_refine_typed_r, stmt_refine_throws_valid.
  * rewrite elem_of_subseteq; intros g; rewrite !elem_of_dom.
    intros [[τs τ] ?]; specialize (Hδ g); destruct (δ1 !! _),
      (δ2 !! _); simplify_option_equality; naive_solver.
Qed.

Lemma lrval_refine_id Γ α Γm av τlr : (Γ,Γm) ⊢ av : τlr → av ⊑{Γ,α@Γm} av : τlr.
Proof. destruct 1; constructor; eauto using val_refine_id, addr_refine_id. Qed.
Lemma expr_refine_id Γ α Γm Γf τs e τlr :
  (Γ,Γf,Γm,τs) ⊢ e : τlr → e ⊑{(Γ,Γf,τs),α@Γm} e : τlr.
Proof.
  assert (∀ es τlrs, Forall2 (λ e τlr, e ⊑{(Γ,Γf,τs),α@Γm} e : τlr) es τlrs →
    es ⊑{(Γ,Γf,τs),α@Γm}* es :* τlrs).
  { induction 1; constructor; eauto. }
  induction 1 using @expr_typed_ind; refine_constructor; eauto using
    locks_refine_id, val_refine_id, addr_refine_id.
Qed.
Lemma exprs_refine_id Γ α Γm Γf τs es τlrs :
  (Γ,Γf,Γm,τs) ⊢* es :* τlrs → es ⊑{(Γ,Γf,τs),α@Γm}* es :* τlrs.
Proof. induction 1; constructor; eauto using expr_refine_id. Qed.  
Lemma ectx_item_refine_id Γ α Γm Γf τs Ei τlr τlr' :
  (Γ,Γf,Γm,τs) ⊢ Ei : τlr ↣ τlr' → Ei ⊑{(Γ,Γf,τs),α@Γm} Ei : τlr ↣ τlr'.
Proof.
  destruct 1; refine_constructor; eauto using expr_refine_id, exprs_refine_id.
Qed.
Lemma ectx_refine_id Γ α Γm Γf τs E τlr τlr' :
  (Γ,Γf,Γm,τs) ⊢ E : τlr ↣ τlr' → E ⊑{(Γ,Γf,τs),α@Γm} E : τlr ↣ τlr'.
Proof. induction 1; refine_constructor; eauto using ectx_item_refine_id. Qed.
Lemma stmt_refine_id Γ α Γm Γf τs s mcσ :
  (Γ,Γf,Γm,τs) ⊢ s : mcσ → s ⊑{(Γ,Γf,τs),α@Γm} s : mcσ.
Proof. induction 1; refine_constructor; eauto using expr_refine_id. Qed.
Lemma sctx_item_refine_id Γ α Γm Γf τs Es mcσ mcσ' :
  (Γ,Γf,Γm,τs) ⊢ Es : mcσ ↣ mcσ' → Es ⊑{(Γ,Γf,τs),α@Γm} Es : mcσ ↣ mcσ'.
Proof.
  destruct 1; refine_constructor; eauto using stmt_refine_id, expr_refine_id.
Qed.
Lemma esctx_item_refine_id Γ α Γm Γf τs Ee τlr τlr' :
  (Γ,Γf,Γm,τs) ⊢ Ee : τlr ↣ τlr' → Ee ⊑{(Γ,Γf,τs),α@Γm} Ee : τlr ↣ τlr'.
Proof. destruct 1; refine_constructor; eauto using stmt_refine_id. Qed.
Lemma ctx_item_refine_id Γ α Γm Γf τs Ek τf τf' :
  (Γ,Γf,Γm,τs) ⊢ Ek : τf ↣ τf' → Ek ⊑{(Γ,Γf,τs),α@Γm} Ek : τf ↣ τf'.
Proof.
  assert (∀ os, Forall2 (λ o1 o2, @meminj_id Ti !! o1 = Some (o2, [])) os os).
  { induction os; auto. }
  destruct 1; refine_constructor; eauto using sctx_item_refine_id,
    expr_refine_id, ectx_refine_id, esctx_item_refine_id.
Qed.
Lemma ctx_refine_id Γ α Γm Γf k τf τf' :
  (Γ,Γf,Γm) ⊢ k : τf ↣ τf' → k ⊑{(Γ,Γf),α@Γm} k : τf ↣ τf'.
Proof. induction 1; refine_constructor; eauto using ctx_item_refine_id. Qed.
Lemma direction_refine_id Γ α Γm d cmσ : (Γ,Γm) ⊢ d : cmσ → d ⊑{Γ,α@Γm} d : cmσ.
Proof. destruct 1; refine_constructor; eauto using val_refine_id. Qed.
Lemma focus_refine_id Γ Γf α Γm τs φ τf :
  (Γ,Γf,Γm,τs) ⊢ φ : τf → φ ⊑{(Γ,Γf,τs),α@Γm} φ : τf.
Proof.
  destruct 1; refine_constructor; eauto using stmt_refine_id,
    direction_refine_id, expr_refine_id, val_refine_id, ectx_refine_id,
    esctx_item_refine_id, vals_refine_id, locks_refine_id.
Qed.
Lemma state_refine_id Γ Γf α S g : ✓ Γ → (Γ,Γf) ⊢ S : g → S ⊑{(Γ,Γf),α} S : g.
Proof.
  destruct S; intros ? (τf&?&?&?).
  eleft; eauto using cmap_refine_id', ctx_refine_id, focus_refine_id.
Qed.
Lemma funenv_refine_id Γ α Γm δ Γf : ✓ Γ → (Γ,Γm) ⊢ δ : Γf → δ ⊑{Γ,α@Γm} δ : Γf.
Proof.
  intros ? [Hδ Hdom] g; specialize (Hdom g); rewrite !elem_of_dom in Hdom.
  destruct (δ !! g) eqn:?; auto.
  * destruct (Hδ g s) as (τs&τ&?&->&?); naive_solver eauto using stmt_refine_id.
  * destruct (Γf !! g). by destruct Hdom; eauto. done.
Qed.
Lemma lrval_refine_compose Γ α1 α2 f1 f2 Γm1 Γm2 Γm3 av1 av2 av3 τlr τlr' :
  ✓ Γ → av1 ⊑{Γ,α1,f1@Γm1↦Γm2} av2 : τlr → av2 ⊑{Γ,α2,f2@Γm2↦Γm3} av3 : τlr' →
  av1 ⊑{Γ,α1||α2,f2 ◎ f1@Γm1↦Γm3} av3 : τlr.
Proof.
  destruct 2; inversion_clear 1; refine_constructor;
    eauto using val_refine_compose, addr_refine_compose.
Qed.
Lemma expr_refine_compose Γ Γf τs α1 α2 f1 f2 Γm1 Γm2 Γm3 e1 e2 e3 τlr τlr' :
  ✓ Γ → e1 ⊑{(Γ,Γf,τs),α1,f1@Γm1↦Γm2} e2 : τlr →
  e2 ⊑{(Γ,Γf,τs),α2,f2@Γm2↦Γm3} e3 : τlr' →
  e1 ⊑{(Γ,Γf,τs),α1||α2,f2 ◎ f1@Γm1↦Γm3} e3 : τlr.
Proof.
  assert (∀ es1 es2 es3 τlrs τlrs',
    Forall3 (λ e1 e2 τlr, ∀ e3 τlr', e2 ⊑{(Γ,Γf,τs),α2,f2@ Γm2↦Γm3} e3 : τlr' →
      e1 ⊑{(Γ,Γf,τs),α1||α2,f2 ◎ f1 @ Γm1↦Γm3} e3 : τlr) es1 es2 τlrs →
    es2 ⊑{(Γ,Γf,τs),α2,f2@ Γm2↦Γm3}* es3 :* τlrs' →
    es1 ⊑{(Γ, Γf, τs),α1||α2,f2 ◎ f1 @ Γm1↦Γm3}* es3 :* τlrs).
  { intros ?? es3 ? τlrs' Hes. revert es3 τlrs'.
    induction Hes; inversion_clear 1; constructor; eauto. }
  intros ? He; revert e3 τlr'.
  induction He using @expr_refine_ind; intros ?? He';
    refine_inversion He'; simplify_type_equality'; refine_constructor;
    eauto using locks_refine_compose, val_refine_compose, addr_refine_compose.
Qed.
Lemma exprs_refine_compose
    Γ Γf τs α1 α2 f1 f2 Γm1 Γm2 Γm3 es1 es2 es3 τlrs τlrs' :
  ✓ Γ → es1 ⊑{(Γ,Γf,τs),α1,f1@Γm1↦Γm2}* es2 :* τlrs →
  es2 ⊑{(Γ,Γf,τs),α2,f2@Γm2↦Γm3}* es3 :* τlrs' →
  es1 ⊑{(Γ,Γf,τs),α1||α2,f2 ◎ f1@Γm1↦Γm3}* es3 :* τlrs.
Proof.
  intros ? Hes. revert es3 τlrs'. induction Hes; inversion_clear 1;
    constructor; eauto using expr_refine_compose.
Qed.
Lemma ectx_item_refine_compose
    Γ Γf τs α1 α2 f1 f2 Γm1 Γm2 Γm3 Ei1 Ei2 Ei3 τlr τlr' τlr'' :
  ✓ Γ → Ei1 ⊑{(Γ,Γf,τs),α1,f1@Γm1↦Γm2} Ei2 : τlr ↣ τlr' →
  Ei2 ⊑{(Γ,Γf,τs),α2,f2@Γm2↦Γm3} Ei3 : τlr ↣ τlr'' →
  Ei1 ⊑{(Γ,Γf,τs),α1||α2,f2 ◎ f1@Γm1↦Γm3} Ei3 : τlr ↣ τlr'.
Proof.
  destruct 2; intros HEi'; refine_inversion HEi'; simplify_type_equality;
    refine_constructor; eauto using expr_refine_compose, exprs_refine_compose.
Qed.
Lemma ectx_refine_compose
    Γ Γf τs α1 α2 f1 f2 Γm1 Γm2 Γm3 E1 E2 E3 τlr τlr' τlr'' :
  ✓ Γ → E1 ⊑{(Γ,Γf,τs),α1,f1@Γm1↦Γm2} E2 : τlr ↣ τlr' →
  E2 ⊑{(Γ,Γf,τs),α2,f2@Γm2↦Γm3} E3 : τlr ↣ τlr'' →
  E1 ⊑{(Γ,Γf,τs),α1||α2,f2 ◎ f1@Γm1↦Γm3} E3 : τlr ↣ τlr'.
Proof.
  intros ? HE. revert E3 τlr''.
  induction HE as [|Ei1 Ei2 E1 E2 τlr1 τlr2 τlr3];
    intros E3' τlr3'; inversion_clear 1 as [|? Ei3 ? E3 ? τlr2'];
    refine_constructor; eauto using ectx_item_refine_compose.
  cut (τlr2 = τlr2'); [intros ->; eauto|].
  by eapply (path_typed_unique_r _ Ei2);
    eauto using ectx_item_refine_typed_l, ectx_item_refine_typed_r.
Qed.
Lemma stmt_refine_compose Γ Γf τs α1 α2 f1 f2 Γm1 Γm2 Γm3 s1 s2 s3 mcτ mcτ' :
  ✓ Γ → s1 ⊑{(Γ,Γf,τs),α1,f1@Γm1↦Γm2} s2 : mcτ →
  s2 ⊑{(Γ,Γf,τs),α2,f2@Γm2↦Γm3} s3 : mcτ' →
  s1 ⊑{(Γ,Γf,τs),α1||α2,f2 ◎ f1@Γm1↦Γm3} s3 : mcτ.
Proof.
  intros ? Hs. revert s3 mcτ'.
  induction Hs; intros ?? Hs'; refine_inversion Hs';
    refine_constructor; naive_solver eauto using expr_refine_compose.
Qed.
Lemma sctx_item_refine_compose
    Γ Γf τs α1 α2 f1 f2 Γm1 Γm2 Γm3 Es1 Es2 Es3 mcτ mcτ' mcτ'' :
  ✓ Γ → Es1 ⊑{(Γ,Γf,τs),α1,f1@Γm1↦Γm2} Es2 : mcτ ↣ mcτ' →
  Es2 ⊑{(Γ,Γf,τs),α2,f2@Γm2↦Γm3} Es3 : mcτ ↣ mcτ'' →
  Es1 ⊑{(Γ,Γf,τs),α1||α2,f2 ◎ f1@Γm1↦Γm3} Es3 : mcτ ↣ mcτ'.
Proof.
  destruct 2; intros HEs'; refine_inversion HEs'; refine_constructor;
    eauto using expr_refine_compose, stmt_refine_compose.
Qed.
Lemma esctx_item_refine_compose
    Γ Γf τs α1 α2 f1 f2 Γm1 Γm2 Γm3 Ee1 Ee2 Ee3 τlr mcτ' mcτ'' :
  ✓ Γ → Ee1 ⊑{(Γ,Γf,τs),α1,f1@Γm1↦Γm2} Ee2 : τlr ↣ mcτ' →
  Ee2 ⊑{(Γ,Γf,τs),α2,f2@Γm2↦Γm3} Ee3 : τlr ↣ mcτ'' →
  Ee1 ⊑{(Γ,Γf,τs),α1||α2,f2 ◎ f1@Γm1↦Γm3} Ee3 : τlr ↣ mcτ'.
Proof.
  destruct 2; intros HEe'; refine_inversion HEe';
     refine_constructor; eauto using stmt_refine_compose.
Qed.
Lemma ctx_item_refine_compose
    Γ Γf τs α1 α2 f1 f2 Γm1 Γm2 Γm3 Ek1 Ek2 Ek3 τf τf' τf'' :
  ✓ Γ → Ek1 ⊑{(Γ,Γf,τs),α1,f1@Γm1↦Γm2} Ek2 : τf ↣ τf' →
  Ek2 ⊑{(Γ,Γf,τs),α2,f2@Γm2↦Γm3} Ek3 : τf ↣ τf'' →
  Ek1 ⊑{(Γ,Γf,τs),α1||α2,f2 ◎ f1@Γm1↦Γm3} Ek3 : τf ↣ τf'.
Proof.
  assert (∀ o1 o2 o3, f1 !! o1 = Some (o2,[]) → f2 !! o2 = Some (o3,[]) →
    (f2 ◎ f1) !! o1 = Some (o3,[])).
  { intros o1 o2 o3. rewrite lookup_meminj_compose_Some. naive_solver. }
  assert (∀ os1 os2 os2' os3 (σs : list (type Ti)),
    Γm2 ⊢* os2 :* σs → Γm2 ⊢* os2' :* σs → zip os2' σs = zip os2 σs →
    Forall2 (λ o1 o2, f1 !! o1 = Some (o2, [])) os1 os2 →
    Forall2 (λ o1 o2, f2 !! o1 = Some (o2, [])) os2' os3 →
    Forall2 (λ o1 o2, (f2 ◎ f1) !! o1 = Some (o2, [])) os1 os3).
  { induction os1; intros; decompose_Forall_hyps; eauto. }
  destruct 2; intros HEk'; refine_inversion HEk'; try refine_constructor;
     eauto using expr_refine_compose, ectx_refine_compose,
     sctx_item_refine_compose, esctx_item_refine_compose.
Qed.
Lemma ctx_refine_compose Γ Γf α1 α2 f1 f2 Γm1 Γm2 Γm3 k1 k2 k3 τf τf' τf'' :
  ✓ Γ → k1 ⊑{(Γ,Γf),α1,f1@Γm1↦Γm2} k2 : τf ↣ τf' →
  k2 ⊑{(Γ,Γf),α2,f2@Γm2↦Γm3} k3 : τf ↣ τf'' →
  k1 ⊑{(Γ,Γf),α1||α2,f2 ◎ f1@Γm1↦Γm3} k3 : τf ↣ τf'.
Proof.
  intros ? Hk. revert k3 τf''.
  induction Hk as [|Ek1 Ek2 k1 k2 τf1 τf2 τf3];
    intros Ek' τf3'; inversion_clear 1 as [|? Ek3 ? k3 ? τf2' ? HEk2].
  { by refine_constructor. }
  erewrite <-ctx_refine_stack_types in HEk2 by eauto.
  refine_constructor; eauto using ctx_item_refine_compose.
  cut (τf2 = τf2'); [intros ->; eauto|].
  by eapply (path_typed_unique_r _ Ek2 τf1);
    eauto using ctx_item_refine_typed_l, ctx_item_refine_typed_r.
Qed.
Lemma direction_refine_compose Γ α1 α2 f1 f2 Γm1 Γm2 Γm3 d1 d2 d3 mcτ mcτ' :
  ✓ Γ → d1 ⊑{Γ,α1,f1@Γm1↦Γm2} d2 : mcτ → d2 ⊑{Γ,α2,f2@Γm2↦Γm3} d3 : mcτ' →
  d1 ⊑{Γ,α1||α2,f2 ◎ f1@Γm1↦Γm3} d3 : mcτ.
Proof.
  destruct 2; inversion_clear 1; refine_constructor;
    eauto using val_refine_compose.
Qed.
Lemma focus_refine_compose Γ Γf τs α1 α2 f1 f2 Γm1 Γm2 Γm3 φ1 φ2 φ3 τf τf' :
  ✓ Γ → φ1 ⊑{(Γ,Γf,τs),α1,f1@Γm1↦Γm2} φ2 : τf →
  φ2 ⊑{(Γ,Γf,τs),α2,f2@Γm2↦Γm3} φ3 : τf' →
  φ1 ⊑{(Γ,Γf,τs),α1||α2,f2 ◎ f1@Γm1↦Γm3} φ3 : τf.
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
Lemma state_refine_undef Γ Γf α f S1 S2 h :
  S1 ⊑{(Γ,Γf),α,f} S2 : h → is_undef_state S2 → is_undef_state S1.
Proof.
  destruct 1 as [k1 φ1 m1 k2 φ2 m2 τf|]; [|done].
  inversion 1; subst; refine_inversion_all; constructor.
Qed.
Lemma state_refine_compose Γ Γf α1 α2 f1 f2 S1 S2 S3 h :
  ✓ Γ → S1 ⊑{(Γ,Γf),α1,f1} S2 : h → S2 ⊑{(Γ,Γf),α2,f2} S3 : h →
  S1 ⊑{(Γ,Γf),α1||α2,f2 ◎ f1} S3 : h.
Proof.
  intros ? HS HS'.
  assert ((Γ,Γf) ⊢ S1 : h) by eauto using state_refine_typed_l.
  assert ((Γ,Γf) ⊢ S3 : h) by eauto using state_refine_typed_r.
  inversion HS as [k1 φ1 m1 k2 φ2 m2 τf|]; subst; [|right; eauto].
  inversion HS' as [??? k3 φ3 m3 τf' ? Hk'|]; subst.
  * erewrite <-ctx_refine_stack_types in Hk' by eauto.
    left with τf; eauto using cmap_refine_compose', focus_refine_compose.
    cut (τf = τf'); [intros ->;eauto using ctx_refine_compose|].
    by eapply (typed_unique _ φ2);
      eauto using focus_refine_typed_l, focus_refine_typed_r.
  * right; eauto using state_refine_undef.
Qed.
Lemma funenv_refine_compose Γ α1 α2 f1 f2 Γm1 Γm2 Γm3 δ1 δ2 δ3 Γf :
  ✓ Γ → δ1 ⊑{Γ,α1,f1@Γm1↦Γm2} δ2 : Γf → δ2 ⊑{Γ,α2,f2@Γm2↦Γm3} δ3 : Γf →
  δ1 ⊑{Γ,α1||α2,f2 ◎ f1@Γm1↦Γm3} δ3 : Γf.
Proof.
  intros ? Hδ Hδ' h; specialize (Hδ h); specialize (Hδ' h).
  destruct (δ1 !! h) as [s1|], (δ2 !! h) as [s2|], (δ3 !! h) as [s3|],
    (Γf !! h) as [[τs τ]|]; try done.
  destruct Hδ as (cmτ&?&?&?&?&?&?), Hδ' as (cmτ'&?&?&?&?&?&?).
  eauto 15 using stmt_refine_compose.
Qed.

Lemma lrval_refine_inverse Γ f Γm1 Γm2 av1 av2 τlr :
  av1 ⊑{Γ,false,f@Γm1↦Γm2} av2 : τlr →
  av2 ⊑{Γ,false,meminj_inverse f@Γm2↦Γm1} av1 : τlr.
Proof.
  destruct 1; constructor; eauto using val_refine_inverse,
    addr_refine_inverse, addr_strict_refine.
Qed.
Lemma expr_refine_inverse Γ Γf τs f Γm1 Γm2 e1 e2 τlr :
  e1 ⊑{(Γ,Γf,τs),false,f@Γm1↦Γm2} e2 : τlr →
  e2 ⊑{(Γ,Γf,τs),false,meminj_inverse f@Γm2↦Γm1} e1 : τlr.
Proof.
  assert (∀ es1 es2 τlrs,
    Forall3 (λ e1 e2 τlr,
      e2 ⊑{(Γ,Γf,τs),false,meminj_inverse f@ Γm2↦Γm1} e1 : τlr) es1 es2 τlrs →
    es2 ⊑{(Γ,Γf,τs),false,meminj_inverse f@ Γm2↦Γm1}* es1 :* τlrs).
  { induction 1; constructor; eauto. }
  induction 1 using @expr_refine_ind; refine_constructor;
    eauto using val_refine_inverse, addr_refine_inverse,
    locks_refine_inverse, addr_strict_refine.
Qed.
Lemma exprs_refine_inverse Γ Γf τs f Γm1 Γm2 es1 es2 τlrs :
  es1 ⊑{(Γ,Γf,τs),false,f@Γm1↦Γm2}* es2 :* τlrs →
  es2 ⊑{(Γ,Γf,τs),false,meminj_inverse f@Γm2↦Γm1}* es1 :* τlrs.
Proof. induction 1; constructor; eauto using expr_refine_inverse. Qed.
Lemma ectx_item_refine_inverse Γ Γf τs f Γm1 Γm2 Ei1 Ei2 τlr τlr' :
  Ei1 ⊑{(Γ,Γf,τs),false,f@Γm1↦Γm2} Ei2 : τlr ↣ τlr' →
  Ei2 ⊑{(Γ,Γf,τs),false,meminj_inverse f@Γm2↦Γm1} Ei1 : τlr ↣ τlr'.
Proof.
  destruct 1; refine_constructor;
    eauto using expr_refine_inverse, exprs_refine_inverse.
Qed.
Lemma ectx_refine_inverse Γ Γf τs f Γm1 Γm2 E1 E2 τlr τlr' :
  E1 ⊑{(Γ,Γf,τs),false,f@Γm1↦Γm2} E2 : τlr ↣ τlr' →
  E2 ⊑{(Γ,Γf,τs),false,meminj_inverse f@Γm2↦Γm1} E1 : τlr ↣ τlr'.
Proof. induction 1; econstructor; eauto using ectx_item_refine_inverse. Qed.
Lemma stmt_refine_inverse Γ Γf τs f Γm1 Γm2 s1 s2 mcτ :
  s1 ⊑{(Γ,Γf,τs),false,f@Γm1↦Γm2} s2 : mcτ →
  s2 ⊑{(Γ,Γf,τs),false,meminj_inverse f@Γm2↦Γm1} s1 : mcτ.
Proof.
  remember false as α. induction 1; subst;
    refine_constructor; naive_solver eauto using expr_refine_inverse.
Qed.
Lemma sctx_item_refine_inverse Γ Γf τs f Γm1 Γm2 Es1 Es2 mcτ mcτ' :
  Es1 ⊑{(Γ,Γf,τs),false,f@Γm1↦Γm2} Es2 : mcτ ↣ mcτ' →
  Es2 ⊑{(Γ,Γf,τs),false,meminj_inverse f@Γm2↦Γm1} Es1 : mcτ ↣ mcτ'.
Proof.
  destruct 1; refine_constructor;
    eauto using stmt_refine_inverse, expr_refine_inverse.
Qed.
Lemma esctx_item_refine_inverse Γ Γf τs f Γm1 Γm2 Ee1 Ee2 τlr mcτ' :
  Ee1 ⊑{(Γ,Γf,τs),false,f@Γm1↦Γm2} Ee2 : τlr ↣ mcτ' →
  Ee2 ⊑{(Γ,Γf,τs),false,meminj_inverse f@Γm2↦Γm1} Ee1 : τlr ↣ mcτ'.
Proof. destruct 1; refine_constructor; eauto using stmt_refine_inverse. Qed.
Lemma ctx_item_refine_inverse Γ Γf τs f Γm1 Γm2 Ek1 Ek2 τf τf' :
  Γm1 ⊑{Γ,false,f} Γm2 → Ek1 ⊑{(Γ,Γf,τs),false,f@Γm1↦Γm2} Ek2 : τf ↣ τf' →
  Ek2 ⊑{(Γ,Γf,τs),false,meminj_inverse f@Γm2↦Γm1} Ek1 : τf ↣ τf'.
Proof.
  intros ?. assert (∀ os1 os2 σs, Γm1 ⊢* os1 :* σs →
    Forall2 (λ o1 o2, f !! o1 = Some (o2, [])) os1 os2 →
    Forall2 (λ o1 o2, meminj_inverse f !! o1 = Some (o2, [])) os2 os1).
  { intros os1 os2 σs Hos1. revert os2.
    induction Hos1; intros; decompose_Forall_hyps;
      constructor; eauto using lookup_meminj_inverse_2. } 
  destruct 1; refine_constructor; eauto using expr_refine_inverse,
    ectx_refine_inverse, esctx_item_refine_inverse,
    sctx_item_refine_inverse, lookup_meminj_inverse_2.
Qed.
Lemma ctx_refine_inverse Γ Γf f Γm1 Γm2 k1 k2 τf τf' :
  ✓ Γ → Γm1 ⊑{Γ,false,f} Γm2 → k1 ⊑{(Γ,Γf),false,f@Γm1↦Γm2} k2 : τf ↣ τf' →
  k2 ⊑{(Γ,Γf),false,meminj_inverse f@Γm2↦Γm1} k1 : τf ↣ τf'.
Proof.
  induction 3; refine_constructor; eauto.
  erewrite <-ctx_refine_stack_types by eauto.
  eauto using ctx_item_refine_inverse.
Qed.
Lemma direction_refine_inverse Γ f Γm1 Γm2 d1 d2 mcτ :
  d1 ⊑{Γ,false,f@Γm1↦Γm2} d2 : mcτ →
  d2 ⊑{Γ,false,meminj_inverse f@Γm2↦Γm1} d1 : mcτ.
Proof. destruct 1; refine_constructor; eauto using val_refine_inverse. Qed.
Lemma focus_refine_inverse Γ Γf τs f Γm1 Γm2 φ1 φ2 τf :
  φ1 ⊑{(Γ,Γf,τs),false,f@Γm1↦Γm2} φ2 : τf →
  φ2 ⊑{(Γ,Γf,τs),false,meminj_inverse f@Γm2↦Γm1} φ1 : τf.
Proof.
  destruct 1; refine_constructor; eauto using stmt_refine_inverse,
    direction_refine_inverse, expr_refine_inverse, val_refine_inverse,
    vals_refine_inverse, ectx_refine_inverse,
    esctx_item_refine_inverse, locks_refine_inverse.
Qed.
Lemma state_refine_inverse Γ Γf f S1 S2 h :
  ✓ Γ → S1 ⊑{(Γ,Γf),false,f} S2 : h →
  S2 ⊑{(Γ,Γf),false,meminj_inverse f} S1 : h.
Proof.
  intros ? [k1 φ1 m1 k2 φ2 m2 τf h' ???|]; [left with τf|done].
  * erewrite <-ctx_refine_stack_types by eauto.
    eauto using focus_refine_inverse.
  * eauto using ctx_refine_inverse, cmap_refine_memenv_refine.
  * eauto using cmap_refine_inverse'.
Qed.
Lemma funenv_refine_inverse Γ f Γm1 Γm2 δ1 δ2 Γf :
  δ1 ⊑{Γ,false,f@Γm1↦Γm2} δ2 : Γf →
  δ2 ⊑{Γ,false,meminj_inverse f@Γm2↦Γm1} δ1 : Γf.
Proof.
  intros Hδ h; specialize (Hδ h); destruct (δ1 !! h) as [s1|],
    (δ2 !! h) as [s2|], (Γf !! h) as [[τs τ]|]; try done.
  destruct Hδ as (cmτ&?&?&?&?&?&?&?); exists cmτ; split_ands; auto.
  * auto using stmt_refine_inverse.
  * by erewrite <-stmt_refine_gotos, <-stmt_refine_labels by eauto.
  * eauto using stmt_refine_throws_valid.
Qed.

Lemma expr_refine_weaken Γ Γf α α' f f' Γm1 Γm2 Γm1' Γm2' τs e1 e2 τlr :
  ✓ Γ → e1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} e2 : τlr → (α → α') →
  Γm1' ⊑{Γ,α',f'} Γm2' → Γm1 ⇒ₘ Γm1' → Γm2 ⇒ₘ Γm2' →
  meminj_extend f f' Γm1 Γm2 → e1 ⊑{(Γ,Γf,τs),α',f'@Γm1'↦Γm2'} e2 : τlr.
Proof.
  intros ? He; intros. induction He using @expr_refine_ind;
    refine_constructor; eauto using locks_refine_weaken,
    addr_refine_weaken, val_refine_weaken.
Qed.
Lemma exprs_refine_weaken Γ Γf α α' f f' Γm1 Γm2 Γm1' Γm2' τs es1 es2 τlrs :
  ✓ Γ → es1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2}* es2 :* τlrs → (α → α') →
  Γm1' ⊑{Γ,α',f'} Γm2' → Γm1 ⇒ₘ Γm1' → Γm2 ⇒ₘ Γm2' →
  meminj_extend f f' Γm1 Γm2 →
  es1 ⊑{(Γ,Γf,τs),α',f'@Γm1'↦Γm2'}* es2 :* τlrs.
Proof. induction 2; constructor; eauto using expr_refine_weaken. Qed.
Lemma ectx_item_refine_weaken
    Γ Γf α α' f f' Γm1 Γm2 Γm1' Γm2' τs Ei1 Ei2 τlr τlr' :
  ✓ Γ → Ei1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} Ei2 : τlr ↣ τlr' → (α → α') →
  Γm1' ⊑{Γ,α',f'} Γm2' → Γm1 ⇒ₘ Γm1' → Γm2 ⇒ₘ Γm2' →
  meminj_extend f f' Γm1 Γm2 →
  Ei1 ⊑{(Γ,Γf,τs),α',f'@Γm1'↦Γm2'} Ei2 : τlr ↣ τlr'.
Proof.
  destruct 2; refine_constructor;
    eauto using expr_refine_weaken, exprs_refine_weaken.
Qed.
Lemma ectx_refine_weaken Γ Γf α α' f f' Γm1 Γm2 Γm1' Γm2' τs E1 E2 τlr τlr' :
  ✓ Γ → E1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} E2 : τlr ↣ τlr' → (α → α') →
  Γm1' ⊑{Γ,α',f'} Γm2' → Γm1 ⇒ₘ Γm1' → Γm2 ⇒ₘ Γm2' →
  meminj_extend f f' Γm1 Γm2 → E1 ⊑{(Γ,Γf,τs),α',f'@Γm1'↦Γm2'} E2 : τlr ↣ τlr'.
Proof. induction 2; refine_constructor;eauto using ectx_item_refine_weaken. Qed.
Lemma stmt_refine_weaken Γ Γf α α' f f' Γm1 Γm2 Γm1' Γm2' τs s1 s2 mcτ :
  ✓ Γ → s1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} s2 : mcτ → (α → α') → Γm1' ⊑{Γ,α',f'} Γm2' →
  Γm1 ⇒ₘ Γm1' → Γm2 ⇒ₘ Γm2' → meminj_extend f f' Γm1 Γm2 →
  s1 ⊑{(Γ,Γf,τs),α',f'@Γm1'↦Γm2'} s2 : mcτ.
Proof.
  intros ? Hs; intros. induction Hs;
    refine_constructor; naive_solver eauto using expr_refine_weaken.
Qed.
Lemma sctx_item_refine_weaken Γ Γf α α' f f' Γm1 Γm2 Γm1' Γm2' τs Es1 Es2 mcτ mcτ' :
  ✓ Γ → Es1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} Es2 : mcτ ↣ mcτ' → (α → α') →
  Γm1' ⊑{Γ,α',f'} Γm2' → Γm1 ⇒ₘ Γm1' → Γm2 ⇒ₘ Γm2' →
  meminj_extend f f' Γm1 Γm2 →
  Es1 ⊑{(Γ,Γf,τs),α',f'@Γm1'↦Γm2'} Es2 : mcτ ↣ mcτ'.
Proof.
  destruct 2; refine_constructor;
    eauto using stmt_refine_weaken, expr_refine_weaken.
Qed.
Lemma esctx_item_refine_weaken
    Γ Γf α α' f f' Γm1 Γm2 Γm1' Γm2' τs Ee1 Ee2 τ mcτ' :
  ✓ Γ → Ee1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} Ee2 : τ ↣ mcτ' → (α → α') →
  Γm1' ⊑{Γ,α',f'} Γm2' → Γm1 ⇒ₘ Γm1' → Γm2 ⇒ₘ Γm2' →
  meminj_extend f f' Γm1 Γm2 → Ee1 ⊑{(Γ,Γf,τs),α',f'@Γm1'↦Γm2'} Ee2 : τ ↣ mcτ'.
Proof. destruct 2; refine_constructor; eauto using stmt_refine_weaken. Qed.
Lemma ctx_item_refine_weaken Γ Γf α α' f f' Γm1 Γm2 Γm1' Γm2' τs Ek1 Ek2 τf τf' :
  ✓ Γ → Ek1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} Ek2 : τf ↣ τf' → (α → α') →
  Γm1' ⊑{Γ,α',f'} Γm2' → Γm1 ⇒ₘ Γm1' → Γm2 ⇒ₘ Γm2' →
  meminj_extend f f' Γm1 Γm2 → Ek1 ⊑{(Γ,Γf,τs),α',f'@Γm1'↦Γm2'} Ek2 : τf ↣ τf'.
Proof.
  intros ? HEk ?????. assert (∀ os1 os2 σs, Γm1 ⊢* os1 :* σs →
    Forall2 (λ o1 o2, f !! o1 = Some (o2, [])) os1 os2 →
    Forall2 (λ o1 o2, f' !! o1 = Some (o2, [])) os1 os2).
  { intros os1 os2 σs Hos. revert os2.
    induction Hos; intros; decompose_Forall_hyps; constructor;
      eauto using option_eq_1_alt, meminj_extend_left. }
  destruct HEk; refine_constructor; eauto using esctx_item_refine_weaken,
    sctx_item_refine_weaken, expr_refine_weaken, ectx_refine_weaken,
    Forall2_impl, memenv_forward_typed, meminj_extend_left, option_eq_1_alt.
Qed.
Lemma ctx_refine_weaken Γ Γf α α' f f' Γm1 Γm2 Γm1' Γm2' k1 k2 τf τf' :
  ✓ Γ → k1 ⊑{(Γ,Γf),α,f@Γm1↦Γm2} k2 : τf ↣ τf' → (α → α') →
  Γm1' ⊑{Γ,α',f'} Γm2' → Γm1 ⇒ₘ Γm1' → Γm2 ⇒ₘ Γm2' →
  meminj_extend f f' Γm1 Γm2 → k1 ⊑{(Γ,Γf),α',f'@Γm1'↦Γm2'} k2 : τf ↣ τf'.
Proof. induction 2; refine_constructor; eauto using ctx_item_refine_weaken. Qed.
Lemma direction_refine_weaken Γ α α' f f' Γm1 Γm2 Γm1' Γm2' d1 d2 mcτ :
  ✓ Γ → d1 ⊑{Γ,α,f@Γm1↦Γm2} d2 : mcτ → (α → α') →
  Γm1' ⊑{Γ,α',f'} Γm2' → Γm1 ⇒ₘ Γm1' → Γm2 ⇒ₘ Γm2' →
  meminj_extend f f' Γm1 Γm2 → d1 ⊑{Γ,α',f'@Γm1'↦Γm2'} d2 : mcτ.
Proof. destruct 2; refine_constructor; eauto using val_refine_weaken. Qed.
Lemma focus_refine_weaken Γ Γf α α' f f' Γm1 Γm2 Γm1' Γm2' τs φ1 φ2 τf :
  ✓ Γ → φ1 ⊑{(Γ,Γf,τs),α,f@Γm1↦Γm2} φ2 : τf → (α → α') →
  Γm1' ⊑{Γ,α',f'} Γm2' → Γm1 ⇒ₘ Γm1' → Γm2 ⇒ₘ Γm2' →
  meminj_extend f f' Γm1 Γm2 → φ1 ⊑{(Γ,Γf,τs),α',f'@Γm1'↦Γm2'} φ2 : τf.
Proof.
  destruct 2; refine_constructor; eauto using direction_refine_weaken,
    stmt_refine_weaken, expr_refine_weaken, val_refine_weaken,
    vals_refine_weaken, locks_refine_weaken, ectx_refine_weaken,
    esctx_item_refine_weaken.
Qed.
Lemma funenv_refine_weaken Γ α α' f f' Γm1 Γm2 Γm1' Γm2' δ1 δ2 Γf :
  ✓ Γ → δ1 ⊑{Γ,α,f@Γm1↦Γm2} δ2 : Γf → (α → α') → Γm1' ⊑{Γ,α',f'} Γm2' →
  Γm1 ⇒ₘ Γm1' → Γm2 ⇒ₘ Γm2' → meminj_extend f f' Γm1 Γm2 →
  δ1 ⊑{Γ,α',f'@Γm1'↦Γm2'} δ2 : Γf.
Proof.
  intros ? Hδ ????? h; specialize (Hδ h); destruct (δ1 !! h) as [s1|],
    (δ2 !! h) as [s2|], (Γf !! h) as [[τs τ]|]; eauto.
  naive_solver eauto using stmt_refine_weaken.
Qed.

Lemma ctx_refine_stack_typed_l Γ α f Γm1 Γm2 Γf k1 k2 τf τf' :
  ✓ Γ → k1 ⊑{(Γ,Γf),α,f@Γm1↦Γm2} k2 : τf ↣ τf' →
  Γm1 ⊢* get_stack k1 :* get_stack_types k1.
Proof. eauto using ctx_typed_stack_typed, ctx_refine_typed_l. Qed.
Lemma ctx_refine_stack_typed_r Γ α f Γm1 Γm2 Γf k1 k2 τf τf' :
  ✓ Γ → k1 ⊑{(Γ,Γf),α,f@Γm1↦Γm2} k2 : τf ↣ τf' →
  Γm2 ⊢* get_stack k2 :* get_stack_types k1.
Proof.
  intros. erewrite ctx_refine_stack_types by eauto.
  eauto using ctx_typed_stack_typed, ctx_refine_typed_r.
Qed.
End properties.
