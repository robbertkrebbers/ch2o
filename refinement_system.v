(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export type_system.
Local Open Scope expr_scope.
Local Open Scope ctype_scope.

Section refinements.
Context `{Env Ti}.

Inductive lrval_refine' (Γ : env Ti) (f : mem_inj Ti) (Γm1 Γm2 : memenv Ti) :
    addr Ti + val Ti → addr Ti + val Ti → lrtype Ti → Prop :=
  | lval_refine a1 a2 τ :
     a1 ⊑{Γ,f@Γm1↦Γm2} a2 : τ → addr_strict Γ a1 →
     lrval_refine' Γ f Γm1 Γm2 (inl a1) (inl a2) (inl τ)
  | rval_refine v1 v2 τ :
     v1 ⊑{Γ,f@Γm1↦Γm2} v2 : τ →
     lrval_refine' Γ f Γm1 Γm2 (inr v1) (inr v2) (inr τ).
Global Instance lrval_refine:
  RefineT Ti (env Ti) (lrtype Ti) (addr Ti + val Ti) := lrval_refine'.

Inductive expr_refine' (Γ : env Ti) (Γf : funtypes Ti)
     (τs : list (type Ti)) (f : mem_inj Ti)
     (Γm1 Γm2 : memenv Ti) : expr Ti → expr Ti → lrtype Ti → Prop :=
  | EVar_refine τ n :
     τs !! n = Some τ →
     expr_refine' Γ Γf τs f Γm1 Γm2 (var{τ} n) (var{τ} n) (inl τ)
  | EVal_refine Ω1 Ω2 v1 v2 τ :
     ✓{Γm1} Ω1 → ✓{Γm2} Ω2 → Ω1 ⊑{Γ,f@Γm1↦Γm2} Ω2 → v1 ⊑{Γ,f@Γm1↦Γm2} v2 : τ →
     expr_refine' Γ Γf τs f Γm1 Γm2 (#{Ω1} v1) (#{Ω2} v2) (inr τ)
  | EAddr_refine Ω1 Ω2 a1 a2 τ :
     ✓{Γm1} Ω1 → ✓{Γm2} Ω2 → Ω1 ⊑{Γ,f@Γm1↦Γm2} Ω2 →
     a1 ⊑{Γ,f@Γm1↦Γm2} a2 : τ → addr_strict Γ a1 →
     expr_refine' Γ Γf τs f Γm1 Γm2 (%{Ω1} a1) (%{Ω2} a2) (inl τ)
  | ERtoL_refine e1 e2 τ :
     expr_refine' Γ Γf τs f Γm1 Γm2 e1 e2 (inr (τ.*)) → ✓{Γ} τ →
     expr_refine' Γ Γf τs f Γm1 Γm2 (.* e1) (.* e2) (inl τ)
  | ERofL_refine e1 e2 τ :
     expr_refine' Γ Γf τs f Γm1 Γm2 e1 e2 (inl τ) →
     expr_refine' Γ Γf τs f Γm1 Γm2 (& e1) (& e2) (inr (τ.*))
  | EAssign_refine ass e1 e2 e1' e2' τ τ' σ :
     assign_typed Γ τ τ' ass σ →
     expr_refine' Γ Γf τs f Γm1 Γm2 e1 e2 (inl τ) →
     expr_refine' Γ Γf τs f Γm1 Γm2 e1' e2' (inr τ') →
     expr_refine' Γ Γf τs f Γm1 Γm2 (e1 ::={ass} e1') (e2 ::={ass} e2') (inr σ)
  | ECall_refine g es1 es2 σ σs :
     Γf !! g = Some (σs,σ) →
     Forall3 (expr_refine' Γ Γf τs f Γm1 Γm2) es1 es2 (inr <$> σs) →
     expr_refine' Γ Γf τs f Γm1 Γm2 (call g @ es1) (call g @ es2) (inr σ)
  | ELoad_refine e1 e2 τ :
     expr_refine' Γ Γf τs f Γm1 Γm2 e1 e2 (inl τ) →
     expr_refine' Γ Γf τs f Γm1 Γm2 (load e1) (load e2) (inr τ)
  | EEltL_refine e1 e2 rs τ σ  :
     expr_refine' Γ Γf τs f Γm1 Γm2 e1 e2 (inl τ) →
     Γ ⊢ rs : τ ↣ σ → ref_seg_offset rs = 0 →
     expr_refine' Γ Γf τs f Γm1 Γm2 (e1 %> rs) (e2 %> rs) (inl σ)
  | EEltR_refine e1 e2 rs τ σ  :
     expr_refine' Γ Γf τs f Γm1 Γm2 e1 e2 (inr τ) →
     Γ ⊢ rs : τ ↣ σ → ref_seg_offset rs = 0 →
     expr_refine' Γ Γf τs f Γm1 Γm2 (e1 #> rs) (e2 #> rs) (inr σ)
  | EAlloc_refine τ e1 e2 τi :
     ✓{Γ} τ → expr_refine' Γ Γf τs f Γm1 Γm2 e1 e2 (inr (intT τi)) →
     expr_refine' Γ Γf τs f Γm1 Γm2 (alloc{τ} e1) (alloc{τ} e2) (inl τ)
  | EFree_refine e1 e2 τ :
     expr_refine' Γ Γf τs f Γm1 Γm2 e1 e2 (inl τ) →
     expr_refine' Γ Γf τs f Γm1 Γm2 (free e1) (free e2) (inr voidT)
  | EUnOp_refine op e1 e2 τ σ :
     unop_typed op τ σ → expr_refine' Γ Γf τs f Γm1 Γm2 e1 e2 (inr τ) →
     expr_refine' Γ Γf τs f Γm1 Γm2 (@{op} e1) (@{op} e2) (inr σ)
  | EBinOp_refine op e1 e2 e1' e2' τ τ' σ :
     binop_typed op τ τ' σ → expr_refine' Γ Γf τs f Γm1 Γm2 e1 e2 (inr τ) →
     expr_refine' Γ Γf τs f Γm1 Γm2 e1' e2' (inr τ') →
     expr_refine' Γ Γf τs f Γm1 Γm2 (e1 @{op} e1') (e2 @{op} e2') (inr σ)
  | EIf_refine e1 e2 e1' e2' e1'' e2'' τb σ :
     expr_refine' Γ Γf τs f Γm1 Γm2 e1 e2 (inr (baseT τb)) →
     expr_refine' Γ Γf τs f Γm1 Γm2 e1' e2' (inr σ) →
     expr_refine' Γ Γf τs f Γm1 Γm2 e1'' e2'' (inr σ) →
     expr_refine' Γ Γf τs f Γm1 Γm2
       (if{e1} e1' else e1'') (if{e2} e2' else e2'') (inr σ)
  | EComma_refine e1 e2 e1' e2' τ1 τ2 :
     expr_refine' Γ Γf τs f Γm1 Γm2 e1 e2 (inr τ1) →
     expr_refine' Γ Γf τs f Γm1 Γm2 e1' e2' (inr τ2) →
     expr_refine' Γ Γf τs f Γm1 Γm2 (e1 ,, e1') (e2 ,, e2') (inr τ2)
  | ECast_refine e1 e2 τ σ :
     expr_refine' Γ Γf τs f Γm1 Γm2 e1 e2 (inr τ) → cast_typed Γ τ σ → 
     expr_refine' Γ Γf τs f Γm1 Γm2 (cast{σ} e1) (cast{σ} e2) (inr σ).
Global Instance expr_refine:
  RefineT Ti (env Ti * funtypes Ti * list (type Ti))
    (lrtype Ti) (expr Ti) := curry3 expr_refine'.

Section expr_refine_ind.
  Context (Γ : env Ti) (Γf : funtypes Ti) (τs : list (type Ti)).
  Context (f : mem_inj Ti) (Γm1 Γm2 : memenv Ti).
  Context (P : expr Ti → expr Ti → lrtype Ti → Prop).
  Context (Pvar : ∀ τ n,
    τs !! n = Some τ → P (var{τ} n) (var{τ} n) (inl τ)).
  Context (Pval : ∀ Ω1 Ω2 v1 v2 τ,
    ✓{Γm1} Ω1 → ✓{Γm2} Ω2 → Ω1 ⊑{Γ,f@Γm1↦Γm2} Ω2 → v1 ⊑{Γ,f@Γm1↦Γm2} v2 : τ →
    P (#{Ω1} v1) (#{Ω2} v2) (inr τ)).
  Context (Paddr : ∀ Ω1 Ω2 a1 a2 τ,
    ✓{Γm1} Ω1 → ✓{Γm2} Ω2 → Ω1 ⊑{Γ,f@Γm1↦Γm2} Ω2 → a1 ⊑{Γ,f@Γm1↦Γm2} a2 : τ →
    addr_strict Γ a1 → P (%{Ω1} a1) (%{Ω2} a2) (inl τ)).
  Context (Prtol : ∀ e1 e2 τ,
    e1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2 : inr (τ.*) →
    P e1 e2 (inr (τ.* )) → ✓{Γ} τ → P (.* e1) (.* e2) (inl τ)).
  Context (Profl : ∀ e1 e2 τ,
    e1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2 : inl τ →
    P e1 e2 (inl τ) → P (& e1) (& e2) (inr (τ.*))).
  Context (Passign : ∀ ass e1 e2 e1' e2' τ τ' σ,
    assign_typed Γ τ τ' ass σ →
    e1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2 : inl τ → P e1 e2 (inl τ) →
    e1' ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2' : inr τ' → P e1' e2' (inr τ') →
    P (e1 ::={ass} e1') (e2 ::={ass} e2') (inr σ)).
  Context (Pcall : ∀ g es1 es2 σ σs,
    Γf !! g = Some (σs,σ) →
    es1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2}* es2 :* inr <$> σs →
    Forall3 P es1 es2 (inr <$> σs) → P (call g @ es1) (call g @ es2) (inr σ)).
  Context (Pload : ∀ e1 e2 τ,
    e1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2 : inl τ →
    P e1 e2 (inl τ) → P (load e1) (load e2) (inr τ)).
  Context (Peltl : ∀ e1 e2 rs τ σ,
    e1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2 : inl τ → P e1 e2 (inl τ) →
    Γ ⊢ rs : τ ↣ σ → ref_seg_offset rs = 0 →
    P (e1 %> rs) (e2 %> rs) (inl σ)).
  Context (Peltr : ∀ e1 e2 rs τ σ,
    e1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2 : inr τ → P e1 e2 (inr τ) →
    Γ ⊢ rs : τ ↣ σ → ref_seg_offset rs = 0 →
    P (e1 #> rs) (e2 #> rs) (inr σ)).
  Context (Palloc : ∀ τ e1 e2 τi,
    ✓{Γ} τ → e1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2 : inr (intT τi) →
    P e1 e2 (inr (intT τi)) → P (alloc{τ} e1) (alloc{τ} e2) (inl τ)).
  Context (Pfree : ∀ e1 e2 τ,
    e1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2 : inl τ → P e1 e2 (inl τ) →
    P (free e1) (free e2) (inr voidT)).
  Context (Punop : ∀ op e1 e2 τ σ,
    unop_typed op τ σ → e1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2 : inr τ →
    P e1 e2 (inr τ) → P (@{op} e1) (@{op} e2) (inr σ)).
  Context (Pbinop : ∀ op e1 e2 e1' e2' τ τ' σ,
    binop_typed op τ τ' σ →
    e1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2 : inr τ → P e1 e2 (inr τ) →
    e1' ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2' : inr τ' → P e1' e2' (inr τ') →
    P (e1 @{op} e1') (e2 @{op} e2') (inr σ)).
  Context (Pif : ∀ e1 e2 e1' e2' e1'' e2'' τb σ,
    e1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2 : inr (baseT τb) → P e1 e2 (inr (baseT τb)) →
    e1' ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2' : inr σ → P e1' e2' (inr σ) →
    e1'' ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2'' : inr σ → P e1'' e2'' (inr σ) →
    P (if{e1} e1' else e1'') (if{e2} e2' else e2'') (inr σ)).
  Context (Pcomma : ∀ e1 e2 e1' e2' τ τ',
    e1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2 : inr τ → P e1 e2 (inr τ) →
    e1' ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2' : inr τ' → P e1' e2' (inr τ') →
    P (e1 ,, e1') (e2 ,, e2') (inr τ')).
  Context (Pcast : ∀ e1 e2 τ σ,
    e1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2 : inr τ → P e1 e2 (inr τ) →
    cast_typed Γ τ σ → P (cast{σ} e1) (cast{σ} e2) (inr σ)).
  Lemma expr_refine_ind : ∀ e1 e2 τ,
    expr_refine' Γ Γf τs f Γm1 Γm2 e1 e2 τ → P e1 e2 τ.
  Proof. fix 4; destruct 1; eauto using Forall2_impl, Forall3_impl. Qed.
End expr_refine_ind.

Inductive ectx_item_refine' (Γ : env Ti) (Γf : funtypes Ti) (τs: list (type Ti))
     (f : mem_inj Ti) (Γm1 Γm2 : memenv Ti) :
     ectx_item Ti → ectx_item Ti → lrtype Ti → lrtype Ti → Prop :=
  | CRtoL_refine τ :
     ✓{Γ} τ →
     ectx_item_refine' Γ Γf τs f Γm1 Γm2 (.* □) (.* □) (inr (τ.*)) (inl τ)
  | CLtoR_refine τ :
     ectx_item_refine' Γ Γf τs f Γm1 Γm2 (& □) (& □) (inl τ) (inr (τ.*))
  | CAssignL_refine ass e1' e2' τ τ' σ :
     assign_typed Γ τ τ' ass σ → e1' ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2' : inr τ' →
     ectx_item_refine' Γ Γf τs f Γm1 Γm2
       (□ ::={ass} e1') (□ ::={ass} e2') (inl τ) (inr σ)
  | CAssignR_refine ass e1 e2 τ τ' σ :
     assign_typed Γ τ τ' ass σ → e1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2 : inl τ →
     ectx_item_refine' Γ Γf τs f Γm1 Γm2
       (e1 ::={ass} □) (e2 ::={ass} □) (inr τ') (inr σ)
  | CCall_refine g es1 es2 es1' es2' σ σs τ σs' :
     Γf !! g = Some (σs ++ τ :: σs', σ) →
     reverse es1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2}* reverse es2 :* inr <$> σs →
     es1' ⊑{(Γ,Γf,τs),f@Γm1↦Γm2}* es2' :* inr <$> σs' →
     ectx_item_refine' Γ Γf τs f Γm1 Γm2
       (call g @ es1 □ es1') (call g @ es2 □ es2') (inr τ) (inr σ)
  | CLoad_refine τ :
     ectx_item_refine' Γ Γf τs f Γm1 Γm2 (load □) (load □) (inl τ) (inr τ)
  | CEltL_refine rs τ σ :
     Γ ⊢ rs : τ ↣ σ → ref_seg_offset rs = 0 →
     ectx_item_refine' Γ Γf τs f Γm1 Γm2 (□ %> rs) (□ %> rs) (inl τ) (inl σ)
  | CEltR_refine rs τ σ :
     Γ ⊢ rs : τ ↣ σ → ref_seg_offset rs = 0 →
     ectx_item_refine' Γ Γf τs f Γm1 Γm2 (□ #> rs) (□ #> rs) (inr τ) (inr σ)
  | CAlloc_refine τ τi :
     ✓{Γ} τ → ectx_item_refine' Γ Γf τs f Γm1 Γm2
       (alloc{τ} □) (alloc{τ} □) (inr (intT τi)) (inl τ)
  | CFree_refine τ :
     ectx_item_refine' Γ Γf τs f Γm1 Γm2 (free □) (free □) (inl τ) (inr voidT)
  | CUnOp_refine op τ σ :
     unop_typed op τ σ →
     ectx_item_refine' Γ Γf τs f Γm1 Γm2 (@{op} □) (@{op} □) (inr τ) (inr σ)
  | CBinOpL_refine op e1' e2' τ τ' σ :
     binop_typed op τ τ' σ → e1' ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2' : inr τ' →
     ectx_item_refine' Γ Γf τs f Γm1 Γm2
       (□ @{op} e1') (□ @{op} e2') (inr τ) (inr σ)
  | CBinOpR_refine op e1 e2 τ τ' σ :
     binop_typed op τ τ' σ → e1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2 : inr τ →
     ectx_item_refine' Γ Γf τs f Γm1 Γm2
       (e1 @{op} □) (e2 @{op} □) (inr τ') (inr σ)
  | CIf_refine e1' e2' e1'' e2'' τb σ :
     e1' ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2' : inr σ →
     e1'' ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2'' : inr σ →
     ectx_item_refine' Γ Γf τs f Γm1 Γm2
       (if{□} e1' else e1'') (if{□} e2' else e2'') (inr (baseT τb)) (inr σ)
  | CComma_refine e1' e2' τ τ' :
     e1' ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2' : inr τ' →
     ectx_item_refine' Γ Γf τs f Γm1 Γm2 (□ ,, e1') (□ ,, e2') (inr τ) (inr τ')
  | CCast_refine τ σ :
     cast_typed Γ τ σ → ectx_item_refine' Γ Γf τs f Γm1 Γm2
       (cast{σ} □) (cast{σ} □) (inr τ) (inr σ).
Global Instance ectx_item_refine:
  PathRefine Ti (env Ti * funtypes Ti * list (type Ti)) (lrtype Ti)
    (lrtype Ti) (ectx_item Ti) := curry3 ectx_item_refine'.
Inductive ectx_refine' (Γs : env Ti * funtypes Ti * list (type Ti))
     (f : mem_inj Ti) (Γm1 Γm2 : memenv Ti) :
     ectx Ti → ectx Ti → lrtype Ti → lrtype Ti → Prop :=
  | ectx_nil_refine_2 τ : ectx_refine' Γs f Γm1 Γm2 [] [] τ τ
  | ectx_cons_refine_2 Ei1 Ei2 E1 E2 τ τ' τ'' :
     Ei1 ⊑{Γs,f@Γm1↦Γm2} Ei2 : τ ↣ τ' →
     ectx_refine' Γs f Γm1 Γm2 E1 E2 τ' τ'' →
     ectx_refine' Γs f Γm1 Γm2 (Ei1 :: E1) (Ei2 :: E2) τ τ''.
Global Instance ectx_refine:
  PathRefine Ti (env Ti * funtypes Ti * list (type Ti)) (lrtype Ti)
    (lrtype Ti) (ectx Ti) := ectx_refine'.

Inductive stmt_refine' (Γ : env Ti) (Γf : funtypes Ti) (τs : list (type Ti))
     (f : mem_inj Ti) (Γm1 Γm2 : memenv Ti) :
     stmt Ti → stmt Ti → rettype Ti → Prop :=
  | SSkip_refine : stmt_refine' Γ Γf τs f Γm1 Γm2 skip skip (false,None)
  | SDo_refine e1 e2 τ :
     e1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2 : inr τ →
     stmt_refine' Γ Γf τs f Γm1 Γm2 (! e1) (! e2) (false,None)
  | SGoto_refine l :
     stmt_refine' Γ Γf τs f Γm1 Γm2 (goto l) (goto l) (true,None)
  | SReturn_refine e1 e2 τ :
     e1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2 : inr τ →
     stmt_refine' Γ Γf τs f Γm1 Γm2 (ret e1) (ret e2) (true,Some τ)
  | SBlock_refine' τ s1 s2 c mσ :
     ✓{Γ} τ → int_typed (size_of Γ τ) sptrT →
     stmt_refine' Γ Γf (τ :: τs) f Γm1 Γm2 s1 s2 (c,mσ) →
     stmt_refine' Γ Γf τs f Γm1 Γm2 (blk{τ} s1) (blk{τ} s2) (c,mσ)
  | SComp_refine s1 s2 s1' s2' c1 mσ1 c2 mσ2 mσ :
     stmt_refine' Γ Γf τs f Γm1 Γm2 s1 s2 (c1,mσ1) →
     stmt_refine' Γ Γf τs f Γm1 Γm2 s1' s2' (c2,mσ2) →
     rettype_union mσ1 mσ2 = Some mσ →
     stmt_refine' Γ Γf τs f Γm1 Γm2 (s1 ;; s1') (s2 ;; s2') (c2,mσ)
  | SLabel_refine l :
     stmt_refine' Γ Γf τs f Γm1 Γm2 (label l) (label l) (false,None)
  | SWhile_refine e1 e2 τb s1 s2 c mσ :
     e1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2 : inr (baseT τb) →
     stmt_refine' Γ Γf τs f Γm1 Γm2 s1 s2 (c,mσ) →
     stmt_refine' Γ Γf τs f Γm1 Γm2 (while{e1} s1) (while{e2} s2) (false,mσ)
  | SIf_refine e1 e2 τb s1 s2 s1' s2' c1 mσ1 c2 mσ2 mσ :
     e1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2 : inr (baseT τb) →
     stmt_refine' Γ Γf τs f Γm1 Γm2 s1 s2 (c1,mσ1) →
     stmt_refine' Γ Γf τs f Γm1 Γm2 s1' s2' (c2,mσ2) →
     rettype_union mσ1 mσ2 = Some mσ →
     stmt_refine' Γ Γf τs f Γm1 Γm2
       (if{e1} s1 else s1') (if{e2} s2 else s2') (c1 && c2, mσ).
Global Instance stmt_refine:
  RefineT Ti (env Ti * funtypes Ti * list (type Ti))
   (rettype Ti) (stmt Ti) := curry3 stmt_refine'.

Inductive sctx_item_refine' (Γ : env Ti) (Γf : funtypes Ti) (τs: list (type Ti))
     (f : mem_inj Ti) (Γm1 Γm2 : memenv Ti) :
     sctx_item Ti → sctx_item Ti → relation (rettype Ti) :=
  | CCompL_refine s1' s2' c mσ c' mσ' mσr :
     s1' ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} s2' : (c',mσ') →
     rettype_union mσ mσ' = Some mσr →
     sctx_item_refine' Γ Γf τs f Γm1 Γm2 (□ ;; s1') (□ ;; s2') (c,mσ) (c',mσr)
  | CCompR_refine s1 s2 c mσ c' mσ' mσr :
     s1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} s2 : (c,mσ) →
     rettype_union mσ mσ' = Some mσr →
     sctx_item_refine' Γ Γf τs f Γm1 Γm2 (s1 ;; □) (s2 ;; □) (c',mσ') (c',mσr)
  | CWhile_refine e1 e2 τb c mσ :
     e1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2 : inr (baseT τb) →
     sctx_item_refine' Γ Γf τs f Γm1 Γm2
       (while{e1} □) (while{e2} □) (c,mσ) (false,mσ)
  | CIfL_refine e1 e2 τb s1' s2' c mσ c' mσ' mσr :
     e1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2 : inr (baseT τb) →
     s1' ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} s2' : (c',mσ') →
     rettype_union mσ mσ' = Some mσr →
     sctx_item_refine' Γ Γf τs f Γm1 Γm2
       (if{e1} □ else s1') (if{e2} □ else s2') (c,mσ) (c&&c',mσr)
  | CIfR_refine e1 e2 τb s1 s2 c mσ c' mσ' mσr :
     e1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2 : inr (baseT τb) →
     s1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} s2 : (c,mσ) →
     rettype_union mσ mσ' = Some mσr →
     sctx_item_refine' Γ Γf τs f Γm1 Γm2
       (if{e1} s1 else □) (if{e2} s2 else □) (c',mσ') (c&&c',mσr).
Global Instance sctx_refine:
  PathRefine Ti (env Ti * funtypes Ti * list (type Ti)) (rettype Ti)
    (rettype Ti) (sctx_item Ti) := curry3 sctx_item_refine'.

Inductive esctx_item_refine' (Γ : env Ti) (Γf: funtypes Ti) (τs: list (type Ti))
     (f : mem_inj Ti) (Γm1 Γm2 : memenv Ti) :
     esctx_item Ti → esctx_item Ti → type Ti → rettype Ti → Prop :=
  | CDoE_refine τ :
     esctx_item_refine' Γ Γf τs f Γm1 Γm2 (! □) (! □) τ (false,None)
  | CReturnE_refine τ :
     esctx_item_refine' Γ Γf τs f Γm1 Γm2 (ret □) (ret □) τ (true,Some τ)
  | CWhileE_refine τb s1 s2 c mσ :
     s1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} s2 : (c,mσ) →
     esctx_item_refine' Γ Γf τs f Γm1 Γm2
       (while{□} s1) (while{□} s2) (baseT τb) (false,mσ)
  | CIfE_refine τb s1 s2 s1' s2' c mσ c' mσ' mσr :
     s1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} s2 : (c,mσ) →
     s1' ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} s2' : (c',mσ') →
     rettype_union mσ mσ' = Some mσr →
     esctx_item_refine' Γ Γf τs f Γm1 Γm2
       (if{□} s1 else s1')%S (if{□} s2 else s2')%S (baseT τb) (c&&c',mσr).
Global Instance esctx_item_refine:
  PathRefine Ti (env Ti * funtypes Ti * list (type Ti)) (type Ti)
    (rettype Ti) (esctx_item Ti) := curry3 esctx_item_refine'.

Inductive ctx_item_refine' (Γ : env Ti) (Γf: funtypes Ti) (τs: list (type Ti))
     (f : mem_inj Ti) (Γm1 Γm2 : memenv Ti) :
     ctx_item Ti → ctx_item Ti → focustype Ti → focustype Ti → Prop :=
  | CStmt_refine Es1 Es2 cmσ cmσ' :
     Es1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} Es2 : cmσ ↣ cmσ' →
     ctx_item_refine' Γ Γf τs f Γm1 Γm2
       (CStmt Es1) (CStmt Es2) (Stmt_type cmσ) (Stmt_type cmσ')
  | CBlock_refine o1 o2 τ c mσ :
     Γm1 ⊢ o1 : τ → Γm2 ⊢ o2 : τ → f !! o1 = Some (o2,[]) →
     ctx_item_refine' Γ Γf τs f Γm1 Γm2
       (CBlock o1 τ) (CBlock o2 τ) (Stmt_type (c,mσ)) (Stmt_type (c,mσ))
  | CExpr_refine e1 e2 Ee1 Ee2 τ cmσ :
     e1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2 : inr τ →
     Ee1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} Ee2 : τ ↣ cmσ →
     ctx_item_refine' Γ Γf τs f Γm1 Γm2
       (CExpr e1 Ee1) (CExpr e2 Ee2) (Expr_type τ) (Stmt_type cmσ)
  | CFun_refine E1 E2 g σs τ σ :
     Γf !! g = Some (σs,τ) →
     E1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} E2 : inr τ ↣ inr σ →
     ctx_item_refine' Γ Γf τs f Γm1 Γm2
       (CFun E1) (CFun E2) (Fun_type g) (Expr_type σ)
  | CParams_refine g os1 os2 σs cmσ σ :
     Γf !! g = Some (σs,σ) →
     Γm1 ⊢* os1 :* σs → Γm2 ⊢* os2 :* σs →
     Forall2 (λ o1 o2, f !! o1 = Some (o2,[])) os1 os2 →
     rettype_match cmσ σ →
     ctx_item_refine' Γ Γf τs f Γm1 Γm2 (CParams g (zip os1 σs))
       (CParams g (zip os2 σs)) (Stmt_type cmσ) (Fun_type g).
Global Instance ctx_item_refine:
  PathRefine Ti (env Ti * funtypes Ti * list (type Ti))
    (focustype Ti) (focustype Ti) (ctx_item Ti) := curry3 ctx_item_refine'.
Inductive ctx_refine' (Γs : env Ti * funtypes Ti)
     (f : mem_inj Ti) (Γm1 Γm2 : memenv Ti) :
     ctx Ti → ctx Ti → focustype Ti → focustype Ti → Prop :=
  | ctx_nil_refine_2 τf : ctx_refine' Γs f Γm1 Γm2 [] [] τf τf
  | ctx_cons_refine_2 Ek1 Ek2 k1 k2 τf τf' τf'' :
     Ek1 ⊑{(Γs,get_stack_types k1),f@Γm1↦Γm2} Ek2 : τf ↣ τf' →
     ctx_refine' Γs f Γm1 Γm2 k1 k2 τf' τf'' →
     ctx_refine' Γs f Γm1 Γm2 (Ek1 :: k1) (Ek2 :: k2) τf τf''.
Global Instance ctx_refine: PathRefine Ti (env Ti * funtypes Ti)
  (focustype Ti) (focustype Ti) (ctx Ti) := ctx_refine'.

Inductive direction_refine' (Γ : env Ti) (f : mem_inj Ti) (Γm1 Γm2: memenv Ti) :
     direction Ti → direction Ti → rettype Ti → Prop :=
  | Down_refine cmτ : direction_refine' Γ f Γm1 Γm2 ↘ ↘ cmτ
  | Up_refine mτ : direction_refine' Γ f Γm1 Γm2 ↗ ↗ (false,mτ)
  | Top_refine c v1 v2 τ :
     v1 ⊑{Γ,f@Γm1↦Γm2} v2 : τ →
     direction_refine' Γ f Γm1 Γm2 (⇈ v1) (⇈ v2) (c,Some τ)
  | Jump_refine l cmτ : direction_refine' Γ f Γm1 Γm2 (↷ l) (↷ l) cmτ.
Global Instance direction_refine: RefineT Ti (env Ti)
  (rettype Ti) (direction Ti) := direction_refine'.

Inductive focus_refine' (Γ : env Ti) (Γf : funtypes Ti) (τs : list (type Ti))
     (f : mem_inj Ti) (Γm1 Γm2 : memenv Ti) :
     focus Ti → focus Ti → focustype Ti → Prop :=
  | Stmt_refine d1 d2 s1 s2 cmσ :
     s1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} s2 : cmσ →
     d1 ⊑{Γ,f@Γm1↦Γm2} d2 : cmσ →
     focus_refine' Γ Γf τs f Γm1 Γm2 (Stmt d1 s1) (Stmt d2 s2) (Stmt_type cmσ)
  | Expr_refine e1 e2 τ :
     e1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2 : inr τ →
     focus_refine' Γ Γf τs f Γm1 Γm2 (Expr e1) (Expr e2) (Expr_type τ)
  | Call_refine g vs1 vs2 σs σ :
     Γf !! g = Some (σs,σ) →
     vs1 ⊑{Γ,f@Γm1↦Γm2}* vs2 :* σs →
     focus_refine' Γ Γf τs f Γm1 Γm2 (Call g vs1) (Call g vs2) (Fun_type g)
  | Return_refine g σs σ v1 v2 :
     Γf !! g = Some (σs, σ) →
     v1 ⊑{Γ,f@Γm1↦Γm2} v2 : σ →
     focus_refine' Γ Γf τs f Γm1 Γm2 (Return g v1) (Return g v2) (Fun_type g)
  | UndefExpr_refine E1 E2 e1 e2 τlr τ :
     e1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2 : τlr →
     E1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} E2 : τlr ↣ inr τ →
     focus_refine' Γ Γf τs f Γm1 Γm2
       (Undef (UndefExpr E1 e1)) (Undef (UndefExpr E2 e2)) (Expr_type τ)
  | UndefBranch_refine e1 e2 Es1 Es2 Ω1 Ω2 v1 v2 τ mσ :
     v1 ⊑{Γ,f@Γm1↦Γm2} v2 : τ →
     e1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2 : inr τ →
     Es1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} Es2 : τ ↣ mσ → Ω1 ⊑{Γ,f@Γm1↦Γm2} Ω2 →
     focus_refine' Γ Γf τs f Γm1 Γm2 (Undef (UndefBranch e1 Es1 Ω1 v1))
       (Undef (UndefBranch e2 Es2 Ω2 v2)) (Stmt_type mσ).
Global Instance focus_refine:
  RefineT Ti (env Ti * funtypes Ti * list (type Ti))
    (focustype Ti) (focus Ti) := curry3 focus_refine'.

Global Instance state_refine : RefineTM Ti (env Ti * funtypes Ti)
    funname (state Ti) := λ ΓΓf f S1 S2 g, ∃ τf,
  let 'State k1 φ1 m1 := S1 in let 'State k2 φ2 m2 := S2 in
  φ1 ⊑{(ΓΓf,get_stack_types k1),f@'{m1}↦'{m2}} φ2 : τf ∧
  k1 ⊑{ΓΓf,f@'{m1}↦'{m2}} k2 : τf ↣ Fun_type g ∧
  m1 ⊑{ΓΓf.1,f} m2.
End refinements.

Section properties.
Context `{EnvSpec Ti}.
Implicit Types Γ : env Ti.
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
Implicit Types Ei : ectx_item Ti.
Implicit Types E : ectx Ti.
Implicit Types Es : sctx_item Ti.
Implicit Types Ee : esctx_item Ti.
Implicit Types Ek : ctx_item Ti.
Implicit Types k : ctx Ti.
Implicit Types φ : focus Ti.

Lemma lrval_refine_typed_l Γ f Γm1 Γm2 av1 av2 τlr :
  ✓ Γ → av1 ⊑{Γ,f@Γm1↦Γm2} av2 : τlr → (Γ,Γm1) ⊢ av1 : τlr.
Proof.
  destruct 2; typed_constructor;
    eauto using val_refine_typed_l, addr_refine_typed_l.
Qed.
Lemma expr_refine_typed_l Γ f Γm1 Γm2 Γf τs e1 e2 τlr :
  ✓ Γ → e1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2 : τlr → (Γ,Γf,Γm1,τs) ⊢ e1 : τlr.
Proof.
  assert (∀ es1 es2 τlrs,
    Forall3 (λ e1 _ τlr, (Γ,Γf,Γm1,τs) ⊢ e1 : τlr) es1 es2 τlrs →
    (Γ,Γf,Γm1,τs) ⊢* es1 :* τlrs).
  { induction 1; constructor; eauto. }
  induction 2 using @expr_refine_ind; typed_constructor;
    eauto using val_refine_typed_l, addr_refine_typed_l.
Qed.
Lemma exprs_refine_typed_l Γ f Γm1 Γm2 Γf τs es1 es2 τlrs :
  ✓ Γ → es1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2}* es2 :* τlrs → (Γ,Γf,Γm1,τs) ⊢* es1 :* τlrs.
Proof. induction 2; eauto using expr_refine_typed_l. Qed.
Lemma ectx_item_refine_typed_l Γ f Γm1 Γm2 Γf τs Ei1 Ei2 τlr τlr' :
  ✓ Γ → Ei1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} Ei2 : τlr ↣ τlr' →
  (Γ,Γf,Γm1,τs) ⊢ Ei1 : τlr ↣ τlr'.
Proof.
  destruct 2; typed_constructor;
    eauto using expr_refine_typed_l, exprs_refine_typed_l.
Qed.
Lemma ectx_refine_typed_l Γ f Γm1 Γm2 Γf τs E1 E2 τlr τlr' :
  ✓ Γ → E1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} E2 : τlr ↣ τlr' →
  (Γ,Γf,Γm1,τs) ⊢ E1 : τlr ↣ τlr'.
Proof. induction 2;typed_constructor; eauto using ectx_item_refine_typed_l. Qed.
Lemma stmt_refine_typed_l Γ f Γm1 Γm2 Γf τs s1 s2 mcτ :
  ✓ Γ → s1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} s2 : mcτ → (Γ,Γf,Γm1,τs) ⊢ s1 : mcτ.
Proof. induction 2; typed_constructor; eauto using expr_refine_typed_l. Qed.
Lemma sctx_item_refine_typed_l Γ f Γm1 Γm2 Γf τs Es1 Es2 mcτ mcτ' :
  ✓ Γ → Es1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} Es2 : mcτ ↣ mcτ' →
  (Γ,Γf,Γm1,τs) ⊢ Es1 : mcτ ↣ mcτ'.
Proof.
  destruct 2; typed_constructor;
    eauto using stmt_refine_typed_l, expr_refine_typed_l.
Qed.
Lemma esctx_item_refine_typed_l Γ f Γm1 Γm2 Γf τs Ee1 Ee2 τlr mcτ :
  ✓ Γ → Ee1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} Ee2 : τlr ↣ mcτ →
  (Γ,Γf,Γm1,τs) ⊢ Ee1 : τlr ↣ mcτ.
Proof. destruct 2; typed_constructor; eauto using stmt_refine_typed_l. Qed.
Lemma ctx_item_refine_typed_l Γ f Γm1 Γm2 Γf τs Ek1 Ek2 τf τf' :
  ✓ Γ → Ek1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} Ek2 : τf ↣ τf' →
  (Γ,Γf,Γm1,τs) ⊢ Ek1 : τf ↣ τf'.
Proof.
  destruct 2; typed_constructor; eauto using expr_refine_typed_l,
    esctx_item_refine_typed_l, sctx_item_refine_typed_l, ectx_refine_typed_l.
Qed.
Lemma ctx_refine_typed_l Γ f Γm1 Γm2 Γf k1 k2 τf τf' :
  ✓ Γ → k1 ⊑{(Γ,Γf),f@Γm1↦Γm2} k2 : τf ↣ τf' → (Γ,Γf,Γm1) ⊢ k1 : τf ↣ τf'.
Proof. induction 2; typed_constructor; eauto using ctx_item_refine_typed_l. Qed.
Lemma direction_refine_typed_l Γ f Γm1 Γm2 d1 d2 τlr :
  ✓ Γ → d1 ⊑{Γ,f@Γm1↦Γm2} d2 : τlr → (Γ,Γm1) ⊢ d1 : τlr.
Proof. destruct 2; typed_constructor; eauto using val_refine_typed_l. Qed.
Lemma focus_refine_typed_l Γ f Γm1 Γm2 Γf τs φ1 φ2 τf :
  ✓ Γ → φ1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} φ2 : τf → (Γ,Γf,Γm1,τs) ⊢ φ1 : τf.
Proof.
  induction 2; typed_constructor; eauto using stmt_refine_typed_l,
    direction_refine_typed_l, expr_refine_typed_l, vals_refine_typed_l,
    val_refine_typed_l, ectx_refine_typed_l, esctx_item_refine_typed_l.
Qed.
Lemma state_refine_typed_l Γ f Γf S1 S2 g :
  ✓ Γ → S1 ⊑{(Γ,Γf),f} S2 : g → (Γ,Γf) ⊢ S1 : g.
Proof.
  destruct S1, S2; intros ? (τf&?&?&?); exists τf; split_ands;
    eauto using focus_refine_typed_l, ctx_refine_typed_l, cmap_refine_valid_l'.
Qed.

Lemma lrval_refine_typed_r Γ f Γm1 Γm2 av1 av2 τlr :
  ✓ Γ → av1 ⊑{Γ,f@Γm1↦Γm2} av2 : τlr → (Γ,Γm2) ⊢ av2 : τlr.
Proof.
  destruct 2; typed_constructor;
    eauto using val_refine_typed_r, addr_refine_typed_r, addr_strict_refine.
Qed.
Lemma expr_refine_typed_r Γ f Γm1 Γm2 Γf τs e1 e2 τlr :
  ✓ Γ → e1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2 : τlr → (Γ,Γf,Γm2,τs) ⊢ e2 : τlr.
Proof.
  assert (∀ es1 es2 τlrs,
    Forall3 (λ _ e2 τlr, (Γ,Γf,Γm2,τs) ⊢ e2 : τlr) es1 es2 τlrs →
    (Γ,Γf,Γm2,τs) ⊢* es2 :* τlrs).
  { induction 1; constructor; eauto. }
  induction 2 using @expr_refine_ind; typed_constructor;
    eauto using val_refine_typed_r, addr_refine_typed_r, addr_strict_refine.
Qed.
Lemma exprs_refine_typed_r Γ f Γm1 Γm2 Γf τs es1 es2 τlrs :
  ✓ Γ → es1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2}* es2 :* τlrs → (Γ,Γf,Γm2,τs) ⊢* es2 :* τlrs.
Proof. induction 2; eauto using expr_refine_typed_r. Qed.
Lemma ectx_item_refine_typed_r Γ f Γm1 Γm2 Γf τs Ei1 Ei2 τlr τlr' :
  ✓ Γ → Ei1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} Ei2 : τlr ↣ τlr' →
  (Γ,Γf,Γm2,τs) ⊢ Ei2 : τlr ↣ τlr'.
Proof.
  destruct 2; typed_constructor;
    eauto using expr_refine_typed_r, exprs_refine_typed_r.
Qed.
Lemma ectx_refine_typed_r Γ f Γm1 Γm2 Γf τs E1 E2 τlr τlr' :
  ✓ Γ → E1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} E2 : τlr ↣ τlr' →
  (Γ,Γf,Γm2,τs) ⊢ E2 : τlr ↣ τlr'.
Proof. induction 2;typed_constructor; eauto using ectx_item_refine_typed_r. Qed.
Lemma stmt_refine_typed_r Γ f Γm1 Γm2 Γf τs s1 s2 mcτ :
  ✓ Γ → s1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} s2 : mcτ → (Γ,Γf,Γm2,τs) ⊢ s2 : mcτ.
Proof. induction 2; typed_constructor; eauto using expr_refine_typed_r. Qed.
Lemma sctx_item_refine_typed_r Γ f Γm1 Γm2 Γf τs Es1 Es2 mcτ mcτ' :
  ✓ Γ → Es1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} Es2 : mcτ ↣ mcτ' →
  (Γ,Γf,Γm2,τs) ⊢ Es2 : mcτ ↣ mcτ'.
Proof.
  destruct 2; typed_constructor;
    eauto using stmt_refine_typed_r, expr_refine_typed_r.
Qed.
Lemma esctx_item_refine_typed_r Γ f Γm1 Γm2 Γf τs Ee1 Ee2 τlr mcτ :
  ✓ Γ → Ee1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} Ee2 : τlr ↣ mcτ →
  (Γ,Γf,Γm2,τs) ⊢ Ee2 : τlr ↣ mcτ.
Proof. destruct 2; typed_constructor; eauto using stmt_refine_typed_r. Qed.
Lemma ctx_item_refine_typed_r Γ f Γm1 Γm2 Γf τs Ek1 Ek2 τf τf' :
  ✓ Γ → Ek1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} Ek2 : τf ↣ τf' →
  (Γ,Γf,Γm2,τs) ⊢ Ek2 : τf ↣ τf'.
Proof.
  destruct 2; typed_constructor; eauto using expr_refine_typed_r,
    esctx_item_refine_typed_r, sctx_item_refine_typed_r, ectx_refine_typed_r.
Qed.
Lemma ctx_refine_stack_types Γ f Γm1 Γm2 Γf k1 k2 τf τf' :
  ✓ Γ → k1 ⊑{(Γ,Γf),f@Γm1↦Γm2} k2 : τf ↣ τf' →
  get_stack_types k1 = get_stack_types k2.
Proof.
  assert (∀ (os1 os2 : list index) (σs : list (type Ti)) P,
    Forall2 P os1 os2 → snd <$> zip os1 σs = snd <$> zip os2 σs).
  { intros os1 os2 σs P Hos. revert σs.
    induction Hos; intros [|??]; f_equal'; auto. }
  induction 2 as [|??????? []]; simpl; eauto with f_equal.
Qed.
Lemma ctx_refine_typed_r Γ f Γm1 Γm2 Γf k1 k2 τf τf' :
  ✓ Γ → k1 ⊑{(Γ,Γf),f@Γm1↦Γm2} k2 : τf ↣ τf' → (Γ,Γf,Γm2) ⊢ k2 : τf ↣ τf'.
Proof.
  induction 2; typed_constructor; erewrite <-?ctx_refine_stack_types by eauto;
    eauto using ctx_item_refine_typed_r.
Qed.
Lemma direction_refine_typed_r Γ f Γm1 Γm2 d1 d2 τlr :
  ✓ Γ → d1 ⊑{Γ,f@Γm1↦Γm2} d2 : τlr → (Γ,Γm2) ⊢ d2 : τlr.
Proof. destruct 2; typed_constructor; eauto using val_refine_typed_r. Qed.
Lemma focus_refine_typed_r Γ f Γm1 Γm2 Γf τs φ1 φ2 τf :
  ✓ Γ → φ1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} φ2 : τf → (Γ,Γf,Γm2,τs) ⊢ φ2 : τf.
Proof.
  induction 2; typed_constructor; eauto using stmt_refine_typed_r,
    direction_refine_typed_r, expr_refine_typed_r, vals_refine_typed_r,
    val_refine_typed_r, ectx_refine_typed_r, esctx_item_refine_typed_r.
Qed.
Lemma state_refine_typed_r Γ f Γf S1 S2 g :
  ✓ Γ → S1 ⊑{(Γ,Γf),f} S2 : g → (Γ,Γf) ⊢ S2 : g.
Proof.
  destruct S1, S2; intros ? (τf&?&?&?); exists τf; split_ands;
    erewrite <-?ctx_refine_stack_types by eauto;
    eauto using focus_refine_typed_r, ctx_refine_typed_r, cmap_refine_valid_r'.
Qed.

Lemma lrval_refine_id Γ Γm av τlr : (Γ,Γm) ⊢ av : τlr → av ⊑{Γ@Γm} av : τlr.
Proof. destruct 1; constructor; eauto using val_refine_id, addr_refine_id. Qed.
Lemma expr_refine_id Γ Γm Γf τs e τlr :
  (Γ,Γf,Γm,τs) ⊢ e : τlr → e ⊑{(Γ,Γf,τs)@Γm} e : τlr.
Proof.
  assert (∀ es τlrs, Forall2 (λ e τlr, e ⊑{(Γ,Γf,τs) @ Γm} e : τlr) es τlrs →
    es ⊑{(Γ,Γf,τs)@Γm}* es :* τlrs).
  { induction 1; constructor; eauto. }
  induction 1 using @expr_typed_ind; refine_constructor; eauto using
    locks_refine_id, val_refine_id, addr_refine_id.
Qed.
Lemma exprs_refine_id Γ Γm Γf τs es τlrs :
  (Γ,Γf,Γm,τs) ⊢* es :* τlrs → es ⊑{(Γ,Γf,τs)@Γm}* es :* τlrs.
Proof. induction 1; constructor; eauto using expr_refine_id. Qed.  
Lemma ectx_item_refine_id Γ Γm Γf τs Ei τlr τlr' :
  (Γ,Γf,Γm,τs) ⊢ Ei : τlr ↣ τlr' → Ei ⊑{(Γ,Γf,τs)@Γm} Ei : τlr ↣ τlr'.
Proof.
  destruct 1; refine_constructor; eauto using expr_refine_id, exprs_refine_id.
Qed.
Lemma ectx_refine_id Γ Γm Γf τs E τlr τlr' :
  (Γ,Γf,Γm,τs) ⊢ E : τlr ↣ τlr' → E ⊑{(Γ,Γf,τs)@Γm} E : τlr ↣ τlr'.
Proof. induction 1; refine_constructor; eauto using ectx_item_refine_id. Qed.
Lemma stmt_refine_id Γ Γm Γf τs s mcσ :
  (Γ,Γf,Γm,τs) ⊢ s : mcσ → s ⊑{(Γ,Γf,τs)@Γm} s : mcσ.
Proof. induction 1; refine_constructor; eauto using expr_refine_id. Qed.
Lemma sctx_item_refine_id Γ Γm Γf τs Es mcσ mcσ' :
  (Γ,Γf,Γm,τs) ⊢ Es : mcσ ↣ mcσ' → Es ⊑{(Γ,Γf,τs)@Γm} Es : mcσ ↣ mcσ'.
Proof.
  destruct 1; refine_constructor; eauto using stmt_refine_id, expr_refine_id.
Qed.
Lemma esctx_item_refine_id Γ Γm Γf τs Ee τlr τlr' :
  (Γ,Γf,Γm,τs) ⊢ Ee : τlr ↣ τlr' → Ee ⊑{(Γ,Γf,τs)@Γm} Ee : τlr ↣ τlr'.
Proof. destruct 1; refine_constructor; eauto using stmt_refine_id. Qed.
Lemma ctx_item_refine_id Γ Γm Γf τs Ek τf τf' :
  (Γ,Γf,Γm,τs) ⊢ Ek : τf ↣ τf' → Ek ⊑{(Γ,Γf,τs)@Γm} Ek : τf ↣ τf'.
Proof.
  assert (∀ os, Forall2 (λ o1 o2, @mem_inj_id Ti !! o1 = Some (o2, [])) os os).
  { induction os; auto. }
  destruct 1; refine_constructor; eauto using sctx_item_refine_id,
    expr_refine_id, ectx_refine_id, esctx_item_refine_id.
Qed.
Lemma ctx_refine_id Γ Γm Γf k τf τf' :
  (Γ,Γf,Γm) ⊢ k : τf ↣ τf' → k ⊑{(Γ,Γf)@Γm} k : τf ↣ τf'.
Proof. induction 1; refine_constructor; eauto using ctx_item_refine_id. Qed.
Lemma direction_refine_id Γ Γm d cmσ : (Γ,Γm) ⊢ d : cmσ → d ⊑{Γ@Γm} d : cmσ.
Proof. destruct 1; refine_constructor; eauto using val_refine_id. Qed.
Lemma focus_refine_id Γ Γf Γm τs φ τf :
  (Γ,Γf,Γm,τs) ⊢ φ : τf → φ ⊑{(Γ,Γf,τs)@Γm} φ : τf.
Proof.
  destruct 1; refine_constructor; eauto using stmt_refine_id,
    direction_refine_id, expr_refine_id, val_refine_id, ectx_refine_id,
    esctx_item_refine_id, vals_refine_id, locks_refine_id.
Qed.
Lemma state_refine_id Γ Γf S g :
  ✓ Γ → (Γ,Γf) ⊢ S : g → S ⊑{(Γ,Γf)} S : g.
Proof.
  destruct S; intros ? (τf&?&?&?); exists τf; split_ands;
    auto using cmap_refine_id', ctx_refine_id, focus_refine_id.
Qed.

Lemma lrval_refine_compose Γ f g Γm1 Γm2 Γm3 av1 av2 av3 τlr τlr' :
  ✓ Γ → av1 ⊑{Γ,f@Γm1↦Γm2} av2 : τlr → av2 ⊑{Γ,g@Γm2↦Γm3} av3 : τlr' →
  av1 ⊑{Γ,f ◎ g@Γm1↦Γm3} av3 : τlr.
Proof.
  destruct 2; inversion_clear 1; refine_constructor;
    eauto using val_refine_compose, addr_refine_compose.
Qed.
Lemma expr_refine_compose Γ Γf τs f g Γm1 Γm2 Γm3 e1 e2 e3 τlr τlr' :
  ✓ Γ → e1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} e2 : τlr →
  e2 ⊑{(Γ,Γf,τs),g@Γm2↦Γm3} e3 : τlr' →
  e1 ⊑{(Γ,Γf,τs),f ◎ g@Γm1↦Γm3} e3 : τlr.
Proof.
  assert (∀ es1 es2 es3 τlrs τlrs',
    Forall3 (λ e1 e2 τlr, ∀ e3 τlr', e2 ⊑{(Γ,Γf,τs),g @ Γm2↦Γm3} e3 : τlr' →
      e1 ⊑{(Γ,Γf,τs),f ◎ g @ Γm1↦Γm3} e3 : τlr) es1 es2 τlrs →
    es2 ⊑{(Γ,Γf,τs),g @ Γm2↦Γm3}* es3 :* τlrs' →
    es1 ⊑{(Γ, Γf, τs),f ◎ g @ Γm1↦Γm3}* es3 :* τlrs).
  { intros ?? es3 ? τlrs' Hes. revert es3 τlrs'.
    induction Hes; inversion_clear 1; constructor; eauto. }
  intros ? He; revert e3 τlr'.
  induction He using @expr_refine_ind;  intros ?? He';
    refine_inversion He'; simplify_type_equality'; refine_constructor;
    eauto using locks_refine_compose, val_refine_compose, addr_refine_compose.
Qed.
Lemma exprs_refine_compose Γ Γf τs f g Γm1 Γm2 Γm3 es1 es2 es3 τlrs τlrs' :
  ✓ Γ → es1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2}* es2 :* τlrs →
  es2 ⊑{(Γ,Γf,τs),g@Γm2↦Γm3}* es3 :* τlrs' →
  es1 ⊑{(Γ,Γf,τs),f ◎ g@Γm1↦Γm3}* es3 :* τlrs.
Proof.
  intros ? Hes. revert es3 τlrs'. induction Hes; inversion_clear 1;
    constructor; eauto using expr_refine_compose.
Qed.
Lemma ectx_item_refine_compose
    Γ Γf τs f g Γm1 Γm2 Γm3 Ei1 Ei2 Ei3 τlr τlr' τlr'' :
  ✓ Γ → Ei1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} Ei2 : τlr ↣ τlr' →
  Ei2 ⊑{(Γ,Γf,τs),g@Γm2↦Γm3} Ei3 : τlr ↣ τlr'' →
  Ei1 ⊑{(Γ,Γf,τs),f ◎ g@Γm1↦Γm3} Ei3 : τlr ↣ τlr'.
Proof.
  destruct 2; intros HEi'; refine_inversion HEi'; refine_constructor;
    eauto using expr_refine_compose, exprs_refine_compose.
Qed.
Lemma ectx_refine_compose Γ Γf τs f g Γm1 Γm2 Γm3 E1 E2 E3 τlr τlr' τlr'' :
  ✓ Γ → E1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} E2 : τlr ↣ τlr' →
  E2 ⊑{(Γ,Γf,τs),g@Γm2↦Γm3} E3 : τlr ↣ τlr'' →
  E1 ⊑{(Γ,Γf,τs),f ◎ g@Γm1↦Γm3} E3 : τlr ↣ τlr'.
Proof.
  intros ? HE. revert E3 τlr''.
  induction HE as [|Ei1 Ei2 E1 E2 τlr1 τlr2 τlr3];
    intros E3' τlr3'; inversion_clear 1 as [|? Ei3 ? E3 ? τlr2'];
    refine_constructor; eauto using ectx_item_refine_compose.
  cut (τlr2 = τlr2'); [intros ->; eauto|].
  by eapply (path_typed_unique_r _ Ei2);
    eauto using ectx_item_refine_typed_l, ectx_item_refine_typed_r.
Qed.
Lemma stmt_refine_compose Γ Γf τs f g Γm1 Γm2 Γm3 s1 s2 s3 mcτ mcτ' :
  ✓ Γ → s1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} s2 : mcτ →
  s2 ⊑{(Γ,Γf,τs),g@Γm2↦Γm3} s3 : mcτ' →
  s1 ⊑{(Γ,Γf,τs),f ◎ g@Γm1↦Γm3} s3 : mcτ.
Proof.
  intros ? Hs. revert s3 mcτ'.
  induction Hs; intros ?? Hs'; refine_inversion Hs';
    refine_constructor; naive_solver eauto using expr_refine_compose.
Qed.
Lemma sctx_item_refine_compose
    Γ Γf τs f g Γm1 Γm2 Γm3 Es1 Es2 Es3 mcτ mcτ' mcτ'' :
  ✓ Γ → Es1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} Es2 : mcτ ↣ mcτ' →
  Es2 ⊑{(Γ,Γf,τs),g@Γm2↦Γm3} Es3 : mcτ ↣ mcτ'' →
  Es1 ⊑{(Γ,Γf,τs),f ◎ g@Γm1↦Γm3} Es3 : mcτ ↣ mcτ'.
Proof.
  destruct 2; intros HEs'; refine_inversion HEs'; refine_constructor;
    eauto using expr_refine_compose, stmt_refine_compose.
Qed.
Lemma esctx_item_refine_compose
    Γ Γf τs f g Γm1 Γm2 Γm3 Ee1 Ee2 Ee3 τlr mcτ' mcτ'' :
  ✓ Γ → Ee1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} Ee2 : τlr ↣ mcτ' →
  Ee2 ⊑{(Γ,Γf,τs),g@Γm2↦Γm3} Ee3 : τlr ↣ mcτ'' →
  Ee1 ⊑{(Γ,Γf,τs),f ◎ g@Γm1↦Γm3} Ee3 : τlr ↣ mcτ'.
Proof.
  destruct 2; intros HEe'; refine_inversion HEe';
     refine_constructor; eauto using stmt_refine_compose.
Qed.
Lemma ctx_item_refine_compose Γ Γf τs f g Γm1 Γm2 Γm3 Ek1 Ek2 Ek3 τf τf' τf'' :
  ✓ Γ → Ek1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} Ek2 : τf ↣ τf' →
  Ek2 ⊑{(Γ,Γf,τs),g@Γm2↦Γm3} Ek3 : τf ↣ τf'' →
  Ek1 ⊑{(Γ,Γf,τs),f ◎ g@Γm1↦Γm3} Ek3 : τf ↣ τf'.
Proof.
  assert (∀ o1 o2 o3, f !! o1 = Some (o2,[]) → g !! o2 = Some (o3,[]) →
    (f ◎ g) !! o1 = Some (o3,[])).
  { intros o1 o2 o3. rewrite lookup_mem_inj_compose_Some. naive_solver. }
  assert (∀ os1 os2 os2' os3 (σs : list (type Ti)),
    Γm2 ⊢* os2 :* σs → Γm2 ⊢* os2' :* σs → zip os2' σs = zip os2 σs →
    Forall2 (λ o1 o2, f !! o1 = Some (o2, [])) os1 os2 →
    Forall2 (λ o1 o2, g !! o1 = Some (o2, [])) os2' os3 →
    Forall2 (λ o1 o2, (f ◎ g) !! o1 = Some (o2, [])) os1 os3).
  { induction os1; intros; decompose_Forall_hyps; eauto. }
  destruct 2; intros HEk'; refine_inversion HEk'; try refine_constructor;
     eauto using expr_refine_compose, ectx_refine_compose,
     sctx_item_refine_compose, esctx_item_refine_compose.
Qed.
Lemma ctx_refine_compose Γ Γf f g Γm1 Γm2 Γm3 k1 k2 k3 τf τf' τf'' :
  ✓ Γ → k1 ⊑{(Γ,Γf),f@Γm1↦Γm2} k2 : τf ↣ τf' →
  k2 ⊑{(Γ,Γf),g@Γm2↦Γm3} k3 : τf ↣ τf'' →
  k1 ⊑{(Γ,Γf),f ◎ g@Γm1↦Γm3} k3 : τf ↣ τf'.
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
Lemma direction_refine_compose Γ f g Γm1 Γm2 Γm3 d1 d2 d3 mcτ mcτ' :
  ✓ Γ → d1 ⊑{Γ,f@Γm1↦Γm2} d2 : mcτ → d2 ⊑{Γ,g@Γm2↦Γm3} d3 : mcτ' →
  d1 ⊑{Γ,f ◎ g@Γm1↦Γm3} d3 : mcτ.
Proof.
  destruct 2; inversion_clear 1; refine_constructor;
    eauto using val_refine_compose.
Qed.
Lemma focus_refine_compose Γ Γf τs f g Γm1 Γm2 Γm3 φ1 φ2 φ3 τf τf' :
  ✓ Γ → φ1 ⊑{(Γ,Γf,τs),f@Γm1↦Γm2} φ2 : τf →
  φ2 ⊑{(Γ,Γf,τs),g@Γm2↦Γm3} φ3 : τf' →
  φ1 ⊑{(Γ,Γf,τs),f ◎ g@Γm1↦Γm3} φ3 : τf.
Proof.
  destruct 2 as [| | | |E1 E2 e1 e2 τlr τ|e1 e2 Es1 Es2 ?? v1 v2 τ mτ];
    inversion 1 as [| | | |? E3 ? e3 τlr' τ'|? e3 ? Es3 ?? ? v3 τ' mτ'];
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
Lemma state_refine_compose Γ Γf f g S1 S2 S3 h h' :
  ✓ Γ → S1 ⊑{(Γ,Γf),f} S2 : h → S2 ⊑{(Γ,Γf),g} S3 : h' →
  S1 ⊑{(Γ,Γf),f ◎ g} S3 : h.
Proof.
  destruct S1 as [k1 φ1 m1], S2 as [k2 φ2 m2], S3 as [k3 φ3 m3].
  intros ? (τf&?&?&?) (τf'&Hk'&?&?); exists τf.
  erewrite <-ctx_refine_stack_types in Hk' by eauto.
  assert (τf = τf') as ->.
  { by eapply (typed_unique _ φ2);
      eauto using focus_refine_typed_l, focus_refine_typed_r. }
  eauto 6 using cmap_refine_compose', focus_refine_compose, ctx_refine_compose.
Qed.
End properties.
