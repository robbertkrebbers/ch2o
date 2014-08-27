(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export state.
Local Open Scope expr_scope.
Local Open Scope ctype_scope.

Notation funtypes Ti := (funmap (list (type Ti) * type Ti)).
Notation lrtype Ti := (type Ti + type Ti)%type.
Definition lrtype_type {Ti} (τlr : lrtype Ti) : type Ti :=
  match τlr with inl τ | inr τ => τ end.
Notation rettype Ti := (bool * option (type Ti))%type.
Inductive focustype (Ti : Set) :=
  | Stmt_type : rettype Ti → focustype Ti
  | Expr_type : type Ti → focustype Ti
  | Fun_type : funname → focustype Ti.
Arguments Stmt_type {_} _.
Arguments Expr_type {_} _.
Arguments Fun_type {_} _.

Section typing.
Context `{Env Ti}.

Notation envs := (env Ti * funtypes Ti * memenv Ti * list (type Ti))%type.

Inductive lrval_typed' (Γ : env Ti) (Γm : memenv Ti) :
    addr Ti + val Ti → lrtype Ti → Prop :=
  | lval_typed a τ :
     (Γ,Γm) ⊢ a : τ → addr_strict Γ a → lrval_typed' Γ Γm (inl a) (inl τ)
  | rval_typed v τ : (Γ,Γm) ⊢ v : τ → lrval_typed' Γ Γm (inr v) (inr τ).
Global Instance lrval_typed: Typed (env Ti * memenv Ti) (lrtype Ti)
  (addr Ti + val Ti) := curry lrval_typed'.

Global Instance funtypes_valid : Valid (env Ti) (funtypes Ti) := λ Γ,
  map_Forall (λ _ τsσ, ✓{Γ}* (τsσ.1) ∧
    Forall (λ τ, int_typed (size_of Γ τ) sptrT) (τsσ.1) ∧ ✓{Γ} (τsσ.2)).

Inductive assign_typed (Γ : env Ti) (τ1 : type Ti) :
     type Ti → assign → type Ti → Prop :=
  | Assign_typed τ2 : cast_typed Γ τ2 τ1 → assign_typed Γ τ1 τ2 Assign τ1
  | PreOp_typed op τ2 σ :
     binop_typed op τ1 τ2 σ → cast_typed Γ σ τ1 →
     assign_typed Γ τ1 τ2 (PreOp op) τ1
  | PostOp_typed op τ2 σ :
     binop_typed op τ1 τ2 σ → cast_typed Γ σ τ1 →
     assign_typed Γ τ1 τ2 (PostOp op) τ1.

Inductive expr_typed' (Γ : env Ti) (Γf : funtypes Ti) (Γm : memenv Ti)
     (τs : list (type Ti)) : expr Ti → lrtype Ti → Prop :=
  | EVar_typed τ n :
     τs !! n = Some τ → expr_typed' Γ Γf Γm τs (var{τ} n) (inl τ)
  | EVal_typed Ω v τ :
     ✓{Γm} Ω → (Γ,Γm) ⊢ v : τ → expr_typed' Γ Γf Γm τs (#{Ω} v) (inr τ)
  | EAddr_typed Ω a τ :
     ✓{Γm} Ω → (Γ,Γm) ⊢ a : τ → addr_strict Γ a →
     expr_typed' Γ Γf Γm τs (%{Ω} a) (inl τ)
  | ERtoL_typed e τ :
     expr_typed' Γ Γf Γm τs e (inr (τ.*)) →
     (**i ensure that the type is complete, i.e. no incomplete structs *)
     ✓{Γ} τ →
     expr_typed' Γ Γf Γm τs (.* e) (inl τ)
  | ERofL_typed e τ :
     expr_typed' Γ Γf Γm τs e (inl τ) → expr_typed' Γ Γf Γm τs (& e) (inr (τ.*))
  | EAssign_typed ass e1 e2 τ1 τ2 σ :
     assign_typed Γ τ1 τ2 ass σ →
     expr_typed' Γ Γf Γm τs e1 (inl τ1) → expr_typed' Γ Γf Γm τs e2 (inr τ2) →
     expr_typed' Γ Γf Γm τs (e1 ::={ass} e2) (inr σ)
  | ECall_typed f es σ σs :
     Γf !! f = Some (σs,σ) →
     Forall2 (expr_typed' Γ Γf Γm τs) es (inr <$> σs) →
     expr_typed' Γ Γf Γm τs (call f @ es) (inr σ)
  | ELoad_typed e τ :
     expr_typed' Γ Γf Γm τs e (inl τ) → expr_typed' Γ Γf Γm τs (load e) (inr τ)
  | EEltL_typed e rs τ σ  :
     expr_typed' Γ Γf Γm τs e (inl τ) → Γ ⊢ rs : τ ↣ σ → ref_seg_offset rs = 0 →
     expr_typed' Γ Γf Γm τs (e %> rs) (inl σ)
  | EEltR_typed e rs τ σ  :
     expr_typed' Γ Γf Γm τs e (inr τ) → Γ ⊢ rs : τ ↣ σ → ref_seg_offset rs = 0 →
     expr_typed' Γ Γf Γm τs (e #> rs) (inr σ)
  | EAlloc_typed τ e τi :
     ✓{Γ} τ → expr_typed' Γ Γf Γm τs e (inr (intT τi)) →
     expr_typed' Γ Γf Γm τs (alloc{τ} e) (inl τ)
  | EFree_typed e τ :
     expr_typed' Γ Γf Γm τs e (inl τ) →
     expr_typed' Γ Γf Γm τs (free e) (inr voidT)
  | EUnOp_typed op e τ σ :
     unop_typed op τ σ → expr_typed' Γ Γf Γm τs e (inr τ) →
     expr_typed' Γ Γf Γm τs (@{op} e) (inr σ)
  | EBinOp_typed op e1 e2 τ1 τ2 σ :
     binop_typed op τ1 τ2 σ → expr_typed' Γ Γf Γm τs e1 (inr τ1) →
     expr_typed' Γ Γf Γm τs e2 (inr τ2) →
     expr_typed' Γ Γf Γm τs (e1 @{op} e2) (inr σ)
  | EIf_typed e1 e2 e3 τb σ :
     expr_typed' Γ Γf Γm τs e1 (inr (baseT τb)) →
     expr_typed' Γ Γf Γm τs e2 (inr σ) → expr_typed' Γ Γf Γm τs e3 (inr σ) →
     expr_typed' Γ Γf Γm τs (if{e1} e2 else e3) (inr σ)
  | EComma_typed e1 e2 τ1 τ2 :
     expr_typed' Γ Γf Γm τs e1 (inr τ1) → expr_typed' Γ Γf Γm τs e2 (inr τ2) →
     expr_typed' Γ Γf Γm τs (e1 ,, e2) (inr τ2)
  | ECast_typed e τ σ :
     expr_typed' Γ Γf Γm τs e (inr τ) → cast_typed Γ τ σ → 
     expr_typed' Γ Γf Γm τs (cast{σ} e) (inr σ).
Global Instance expr_typed:
  Typed envs (lrtype Ti) (expr Ti) := curry4 expr_typed'.

Section expr_typed_ind.
  Context (Γ : env Ti) (Γf : funtypes Ti) (Γm : memenv Ti) (τs : list (type Ti)).
  Context (P : expr Ti → lrtype Ti → Prop).
  Context (Pvar : ∀ τ n, τs !! n = Some τ → P (var{τ} n) (inl τ)).
  Context (Pval : ∀ Ω v τ, ✓{Γm} Ω → (Γ,Γm) ⊢ v : τ → P (#{Ω} v) (inr τ)).
  Context (Paddr : ∀ Ω a τ,
    ✓{Γm} Ω → (Γ,Γm) ⊢ a : τ → addr_strict Γ a → P (%{Ω} a) (inl τ)).
  Context (Prtol : ∀ e τ,
    (Γ,Γf,Γm,τs) ⊢ e : inr (τ.*) → P e (inr (τ.*)) → ✓{Γ} τ → P (.* e) (inl τ)).
  Context (Profl : ∀ e τ,
    (Γ,Γf,Γm,τs) ⊢ e : inl τ → P e (inl τ) → P (& e) (inr (τ.*))).
  Context (Passign : ∀ ass e1 e2 τ1 τ2 σ,
    assign_typed Γ τ1 τ2 ass σ → (Γ,Γf,Γm,τs) ⊢ e1 : inl τ1 → P e1 (inl τ1) →
    (Γ,Γf,Γm,τs) ⊢ e2 : inr τ2 → P e2 (inr τ2) → P (e1 ::={ass} e2) (inr σ)).
  Context (Pcall : ∀ f es σ σs,
    Γf !! f = Some (σs,σ) → (Γ,Γf,Γm,τs) ⊢* es :* inr <$> σs →
    Forall2 P es (inr <$> σs) → P (call f @ es) (inr σ)).
  Context (Pload : ∀ e τ,
    (Γ,Γf,Γm,τs) ⊢ e : inl τ → P e (inl τ) → P (load e) (inr τ)).
  Context (Peltl : ∀ e rs τ σ,
    (Γ,Γf,Γm,τs) ⊢ e : inl τ → P e (inl τ) →
    Γ ⊢ rs : τ ↣ σ → ref_seg_offset rs = 0 → P (e %> rs) (inl σ)).
  Context (Peltr : ∀ e rs τ σ,
    (Γ,Γf,Γm,τs) ⊢ e : inr τ → P e (inr τ) →
    Γ ⊢ rs : τ ↣ σ → ref_seg_offset rs = 0 → P (e #> rs) (inr σ)).
  Context (Palloc : ∀ τ e τi,
    ✓{Γ} τ → (Γ,Γf,Γm,τs) ⊢ e : inr (intT τi) →
    P e (inr (intT τi)) → P (alloc{τ} e) (inl τ)).
  Context (Pfree : ∀ e τ,
    (Γ,Γf,Γm,τs) ⊢ e : inl τ → P e (inl τ) → P (free e) (inr voidT)).
  Context (Punop : ∀ op e τ σ,
    unop_typed op τ σ →
    (Γ,Γf,Γm,τs) ⊢ e : inr τ → P e (inr τ) → P (@{op} e) (inr σ)).
  Context (Pbinop : ∀ op e1 e2 τ1 τ2 σ,
    binop_typed op τ1 τ2 σ → (Γ,Γf,Γm,τs) ⊢ e1 : inr τ1 → P e1 (inr τ1) →
    (Γ,Γf,Γm,τs) ⊢ e2 : inr τ2 → P e2 (inr τ2) → P (e1 @{op} e2) (inr σ)).
  Context (Pif : ∀ e1 e2 e3 τb σ,
    (Γ,Γf,Γm,τs) ⊢ e1 : inr (baseT τb) → P e1 (inr (baseT τb)) →
    (Γ,Γf,Γm,τs) ⊢ e2 : inr σ → P e2 (inr σ) →
    (Γ,Γf,Γm,τs) ⊢ e3 : inr σ → P e3 (inr σ) → P (if{e1} e2 else e3) (inr σ)).
  Context (Pcomma : ∀ e1 e2 τ1 τ2,
    (Γ,Γf,Γm,τs) ⊢ e1 : inr τ1 → P e1 (inr τ1) →
    (Γ,Γf,Γm,τs) ⊢ e2 : inr τ2 → P e2 (inr τ2) → P (e1 ,, e2) (inr τ2)).
  Context (Pcast : ∀ e τ σ,
    (Γ,Γf,Γm,τs) ⊢ e : inr τ → P e (inr τ) → cast_typed Γ τ σ →
    P (cast{σ} e) (inr σ)).
  Lemma expr_typed_ind : ∀ e τ, expr_typed' Γ Γf Γm τs e τ → P e τ.
  Proof. fix 3; destruct 1; eauto using Forall2_impl. Qed.
End expr_typed_ind.

Inductive ectx_item_typed' (Γ : env Ti) (Γf : funtypes Ti) (Γm : memenv Ti)
     (τs : list (type Ti)) : ectx_item Ti → lrtype Ti → lrtype Ti → Prop :=
  | CRtoL_typed τ :
     ✓{Γ} τ → ectx_item_typed' Γ Γf Γm τs (.* □) (inr (τ.*)) (inl τ)
  | CLtoR_typed τ : ectx_item_typed' Γ Γf Γm τs (& □) (inl τ) (inr (τ.*))
  | CAssignL_typed ass e2 τ1 τ2 σ :
     assign_typed Γ τ1 τ2 ass σ → (Γ,Γf,Γm,τs) ⊢ e2 : inr τ2 →
     ectx_item_typed' Γ Γf Γm τs (□ ::={ass} e2) (inl τ1) (inr σ)
  | CAssignR_typed ass e1 τ1 τ2 σ :
     assign_typed Γ τ1 τ2 ass σ → (Γ,Γf,Γm,τs) ⊢ e1 : inl τ1 →
     ectx_item_typed' Γ Γf Γm τs (e1 ::={ass} □) (inr τ2) (inr σ)
  | CCall_typed f es1 es2 σ τs1 τ τs2 :
     Γf !! f = Some (τs1 ++ τ :: τs2, σ) →
     (Γ,Γf,Γm,τs) ⊢* reverse es1 :* inr <$> τs1 →
     (Γ,Γf,Γm,τs) ⊢* es2 :* inr <$> τs2 →
     ectx_item_typed' Γ Γf Γm τs (call f @ es1 □ es2) (inr τ) (inr σ)
  | CLoad_typed τ : ectx_item_typed' Γ Γf Γm τs (load □) (inl τ) (inr τ)
  | CEltL_typed rs τ σ :
     Γ ⊢ rs : τ ↣ σ → ref_seg_offset rs = 0 →
     ectx_item_typed' Γ Γf Γm τs (□ %> rs) (inl τ) (inl σ)
  | CEltR_typed rs τ σ :
     Γ ⊢ rs : τ ↣ σ → ref_seg_offset rs = 0 →
     ectx_item_typed' Γ Γf Γm τs (□ #> rs) (inr τ) (inr σ)
  | CAlloc_typed τ τi :
     ✓{Γ} τ → ectx_item_typed' Γ Γf Γm τs (alloc{τ} □) (inr (intT τi)) (inl τ)
  | CFree_typed τ : ectx_item_typed' Γ Γf Γm τs (free □) (inl τ) (inr voidT)
  | CUnOp_typed op τ σ :
     unop_typed op τ σ → ectx_item_typed' Γ Γf Γm τs (@{op} □) (inr τ) (inr σ)
  | CBinOpL_typed op e2 τ1 τ2 σ :
     binop_typed op τ1 τ2 σ → (Γ,Γf,Γm,τs) ⊢ e2 : inr τ2 →
     ectx_item_typed' Γ Γf Γm τs (□ @{op} e2) (inr τ1) (inr σ)
  | CBinOpR_typed op e1 τ1 τ2 σ :
     binop_typed op τ1 τ2 σ → (Γ,Γf,Γm,τs) ⊢ e1 : inr τ1 →
     ectx_item_typed' Γ Γf Γm τs (e1 @{op} □) (inr τ2) (inr σ)
  | CIf_typed e2 e3 τb σ :
     (Γ,Γf,Γm,τs) ⊢ e2 : inr σ → (Γ,Γf,Γm,τs) ⊢ e3 : inr σ →
     ectx_item_typed' Γ Γf Γm τs (if{□} e2 else e3) (inr (baseT τb)) (inr σ)
  | CComma_typed e2 τ1 τ2 :
     (Γ,Γf,Γm,τs) ⊢ e2 : inr τ2 →
     ectx_item_typed' Γ Γf Γm τs (□ ,, e2) (inr τ1) (inr τ2)
  | CCast_typed τ σ :
     cast_typed Γ τ σ → ectx_item_typed' Γ Γf Γm τs (cast{σ} □) (inr τ) (inr σ).
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
  | (true, Some σ') => σ' = σ
  | (false, Some _) => False
  | (_, None) => σ = voidT
  end.

Inductive stmt_typed' (Γ : env Ti) (Γf : funtypes Ti) (Γm : memenv Ti)
     (τs : list (type Ti)) : stmt Ti → rettype Ti → Prop :=
  | SSkip_typed : stmt_typed' Γ Γf Γm τs skip (false,None)
  | SDo_typed e τ :
     (Γ,Γf,Γm,τs) ⊢ e : inr τ → stmt_typed' Γ Γf Γm τs (! e) (false,None)
  | SGoto_typed l : stmt_typed' Γ Γf Γm τs (goto l) (true,None)
  | SReturn_typed e τ :
     (Γ,Γf,Γm,τs) ⊢ e : inr τ → stmt_typed' Γ Γf Γm τs (ret e) (true,Some τ)
  | SBlock_typed' τ s c mσ :
     ✓{Γ} τ →int_typed (size_of Γ τ) sptrT →
     stmt_typed' Γ Γf Γm (τ :: τs) s (c,mσ) →
     stmt_typed' Γ Γf Γm τs (blk{τ} s) (c,mσ)
  | SComp_typed s1 s2 c1 mσ1 c2 mσ2 mσ :
     stmt_typed' Γ Γf Γm τs s1 (c1,mσ1) → stmt_typed' Γ Γf Γm τs s2 (c2,mσ2) →
     rettype_union mσ1 mσ2 = Some mσ → stmt_typed' Γ Γf Γm τs (s1 ;; s2) (c2,mσ)
  | SLabel_typed l : stmt_typed' Γ Γf Γm τs (label l) (false,None)
  | SWhile_typed e τb s c mσ :
     (Γ,Γf,Γm,τs) ⊢ e : inr (baseT τb) → stmt_typed' Γ Γf Γm τs s (c,mσ) →
     stmt_typed' Γ Γf Γm τs (while{e} s) (false,mσ)
  | SIf_typed e τb s1 s2 c1 mσ1 c2 mσ2 mσ :
     (Γ,Γf,Γm,τs) ⊢ e : inr (baseT τb) →
     stmt_typed' Γ Γf Γm τs s1 (c1,mσ1) → stmt_typed' Γ Γf Γm τs s2 (c2,mσ2) →
     rettype_union mσ1 mσ2 = Some mσ →
     stmt_typed' Γ Γf Γm τs (if{e} s1 else s2) (c1 && c2, mσ).
Global Instance stmt_typed:
  Typed envs (rettype Ti) (stmt Ti) := curry4 stmt_typed'.

Inductive sctx_item_typed' (Γ : env Ti) (Γf : funtypes Ti) (Γm : memenv Ti)
     (τs : list (type Ti)) : sctx_item Ti → relation (rettype Ti) :=
  | CCompL_typed s2 c1 mσ1 c2 mσ2 mσ :
     (Γ,Γf,Γm,τs) ⊢ s2 : (c2,mσ2) → rettype_union mσ1 mσ2 = Some mσ →
     sctx_item_typed' Γ Γf Γm τs (□ ;; s2) (c1,mσ1) (c2,mσ)
  | CCompR_typed s1 c1 mσ1 c2 mσ2 mσ :
     (Γ,Γf,Γm,τs) ⊢ s1 : (c1,mσ1) → rettype_union mσ1 mσ2 = Some mσ →
     sctx_item_typed' Γ Γf Γm τs (s1 ;; □) (c2,mσ2) (c2,mσ)
  | CWhile_typed e τb c mσ :
     (Γ,Γf,Γm,τs) ⊢ e : inr (baseT τb) →
     sctx_item_typed' Γ Γf Γm τs (while{e} □) (c,mσ) (false,mσ)
  | CIfL_typed e τb s2 c1 mσ1 c2 mσ2 mσ :
     (Γ,Γf,Γm,τs) ⊢ e : inr (baseT τb) → (Γ,Γf,Γm,τs) ⊢ s2 : (c2,mσ2) →
     rettype_union mσ1 mσ2 = Some mσ →
     sctx_item_typed' Γ Γf Γm τs (if{e} □ else s2) (c1,mσ1) (c1&&c2,mσ)
  | CIfR_typed e τb s1 c1 mσ1 c2 mσ2 mσ :
     (Γ,Γf,Γm,τs) ⊢ e : inr (baseT τb) → (Γ,Γf,Γm,τs) ⊢ s1 : (c1,mσ1) →
     rettype_union mσ1 mσ2 = Some mσ →
     sctx_item_typed' Γ Γf Γm τs (if{e} s1 else □) (c2,mσ2) (c1&&c2,mσ).
Global Instance sctx_typed: PathTyped envs (rettype Ti)
  (rettype Ti) (sctx_item Ti) := curry4 sctx_item_typed'.

Inductive esctx_item_typed' (Γ : env Ti) (Γf : funtypes Ti) (Γm : memenv Ti)
     (τs : list (type Ti)) : esctx_item Ti → type Ti → rettype Ti → Prop :=
  | CDoE_typed τ : esctx_item_typed' Γ Γf Γm τs (! □) τ (false,None)
  | CReturnE_typed τ : esctx_item_typed' Γ Γf Γm τs (ret □) τ (true,Some τ)
  | CWhileE_typed τb s c mσ :
     (Γ,Γf,Γm,τs) ⊢ s : (c,mσ) →
     esctx_item_typed' Γ Γf Γm τs (while{□} s) (baseT τb) (false,mσ)
  | CIfE_typed τb s1 s2 c1 mσ1 c2 mσ2 mσ :
     (Γ,Γf,Γm,τs) ⊢ s1 : (c1,mσ1) → (Γ,Γf,Γm,τs) ⊢ s2 : (c2,mσ2) →
     rettype_union mσ1 mσ2 = Some mσ →
     esctx_item_typed' Γ Γf Γm τs (if{□} s1 else s2)%S (baseT τb) (c1&&c2,mσ).
Global Instance esctx_item_typed: PathTyped envs (type Ti)
  (rettype Ti) (esctx_item Ti) := curry4 esctx_item_typed'.

Inductive ctx_item_typed'
      (Γ : env Ti) (Γf : funtypes Ti) (Γm : memenv Ti) (τs : list (type Ti)) :
      ctx_item Ti → focustype Ti → focustype Ti → Prop :=
  | CStmt_typed Es cmσ1 cmσ2 :
     (Γ,Γf,Γm,τs) ⊢ Es : cmσ1 ↣ cmσ2 →
     ctx_item_typed' Γ Γf Γm τs (CStmt Es) (Stmt_type cmσ1) (Stmt_type cmσ2)
  | CBlock_typed o τ c mσ :
     Γm ⊢ o : τ →
     ctx_item_typed' Γ Γf Γm τs (CBlock o τ) (Stmt_type (c,mσ)) (Stmt_type (c,mσ))
  | CExpr_typed e Ee τ cmσ :
     (Γ,Γf,Γm,τs) ⊢ e : inr τ → (Γ,Γf,Γm,τs) ⊢ Ee : τ ↣ cmσ →
     ctx_item_typed' Γ Γf Γm τs (CExpr e Ee) (Expr_type τ) (Stmt_type cmσ)
  | CFun_typed E f σs τ σ :
     Γf !! f = Some (σs,τ) → (Γ,Γf,Γm,τs) ⊢ E : inr τ ↣ inr σ →
     ctx_item_typed' Γ Γf Γm τs (CFun E) (Fun_type f) (Expr_type σ)
  | CParams_typed f σs os cmσ σ :
     Γf !! f = Some (σs, σ) → Γm ⊢* os :* σs →
     rettype_match cmσ σ → ctx_item_typed'
       Γ Γf Γm τs (CParams f (zip os σs)) (Stmt_type cmσ) (Fun_type f).
Global Instance ctx_item_typed: PathTyped envs (focustype Ti)
  (focustype Ti) (ctx_item Ti) := curry4 ctx_item_typed'.
Inductive ctx_typed' (Γs : env Ti * funtypes Ti * memenv Ti) :
     ctx Ti → focustype Ti → focustype Ti → Prop :=
  | ctx_nil_typed_2 τf : ctx_typed' Γs [] τf τf
  | ctx_cons_typed_2 Ek k τf1 τf2 τf3 :
     (Γs,get_stack_types k) ⊢ Ek : τf1 ↣ τf2 →
     ctx_typed' Γs k τf2 τf3 → ctx_typed' Γs (Ek :: k) τf1 τf3.
Global Instance ctx_typed: PathTyped (env Ti * funtypes Ti * memenv Ti)
  (focustype Ti) (focustype Ti) (ctx Ti) := ctx_typed'.

Inductive direction_typed' (Γ : env Ti) (Γm : memenv Ti) :
    direction Ti → rettype Ti → Prop :=
  | Down_typed cmτ : direction_typed' Γ Γm ↘ cmτ
  | Up_typed mτ : direction_typed' Γ Γm ↗ (false,mτ)
  | Top_typed c v τ : (Γ,Γm) ⊢ v : τ → direction_typed' Γ Γm (⇈ v) (c,Some τ)
  | Jump_typed l cmτ : direction_typed' Γ Γm (↷ l) cmτ.
Global Instance direction_typed: Typed (env Ti * memenv Ti)
  (rettype Ti) (direction Ti) := curry direction_typed'.

Inductive focus_typed' (Γ : env Ti) (Γf : funtypes Ti) (Γm : memenv Ti)
    (τs : list (type Ti)) : focus Ti → focustype Ti → Prop :=
  | Stmt_typed d s cmσ :
     (Γ,Γf,Γm,τs) ⊢ s : cmσ → (Γ,Γm) ⊢ d : cmσ →
     focus_typed' Γ Γf Γm τs (Stmt d s) (Stmt_type cmσ)
  | Expr_typed e τ :
     (Γ,Γf,Γm,τs) ⊢ e : inr τ → focus_typed' Γ Γf Γm τs (Expr e) (Expr_type τ)
  | Call_typed f vs σs σ :
     Γf !! f = Some (σs,σ) → (Γ,Γm) ⊢* vs :* σs →
     focus_typed' Γ Γf Γm τs (Call f vs) (Fun_type f)
  | Return_typed f σs σ v :
     Γf !! f = Some (σs, σ) →
     (Γ,Γm) ⊢ v : σ → focus_typed' Γ Γf Γm τs (Return f v) (Fun_type f)
  | UndefExpr_typed E e τlr τ :
     (Γ,Γf,Γm,τs) ⊢ e : τlr → (Γ,Γf,Γm,τs) ⊢ E : τlr ↣ inr τ →
     focus_typed' Γ Γf Γm τs (Undef (UndefExpr E e)) (Expr_type τ)
  | UndefBranch_typed e Es Ω v τ mσ :
     (Γ,Γm) ⊢ v : τ → (Γ,Γf,Γm,τs) ⊢ e : inr τ → (Γ,Γf,Γm,τs) ⊢ Es : τ ↣ mσ →
     focus_typed' Γ Γf Γm τs (Undef (UndefBranch e Es Ω v)) (Stmt_type mσ).
Global Instance focus_typed:
  Typed envs (focustype Ti) (focus Ti) := curry4 focus_typed'.

Global Instance state_typed :
    Typed (env Ti * funtypes Ti) funname (state Ti) := λ ΓΓf S f, ∃ τf,
  let 'State k φ m := S in
  (ΓΓf,'{m},get_stack_types k) ⊢ φ : τf ∧
  (ΓΓf,'{m}) ⊢ k : τf ↣ Fun_type f ∧
  ✓{ΓΓf.1} m.

Definition funenv_pretyped (Γ : env Ti) (Γm : memenv Ti)
    (δ : funenv Ti) (Γf : funtypes Ti) :=
  map_Forall (λ f s, ∃ τs τ cmτ,
    Γf !! f = Some (τs, τ) ∧
    ✓{Γ}* τs ∧ Forall (λ τ', int_typed (size_of Γ τ') sptrT) τs ∧ ✓{Γ} τ ∧
    (Γ,Γf,Γm,τs) ⊢ s : cmτ ∧ gotos s ⊆ labels s ∧ rettype_match cmτ τ
  ) δ.
Global Instance funenv_typed:
    Typed (env Ti * memenv Ti) (funtypes Ti) (funenv Ti) := λ Γm δ Γf,
  curry funenv_pretyped Γm δ Γf ∧ dom funset Γf ⊆ dom funset δ.

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
     guard (✓{Γm} Ω); guard (addr_strict Γ a); inl <$> type_check (Γ,Γm) a
  | .* e =>
     τ ← type_check Γs e ≫= maybe_inr;
     τp ← maybe_TBase τ ≫= maybe_TPtr;
     guard (✓{Γ} τp); Some (inl τp)
  | & e =>
     τ ← type_check Γs e ≫= maybe_inl;
     Some (inr (τ.*))
  | e1 ::={ass} e2 =>
     τ1 ← type_check Γs e1 ≫= maybe_inl;
     τ2 ← type_check Γs e2 ≫= maybe_inr;
     inr <$> assign_type_of Γ τ1 τ2 ass
  | call f @ es =>
     '(τs,τ) ← Γf !! f;
     τs' ← mapM (λ e, type_check Γs e ≫= maybe_inr) es;
     guard ((τs' : list (type Ti)) = τs); Some (inr τ)
  | load e => inr <$> type_check Γs e ≫= maybe_inl
  | e %> rs =>
     τ ← type_check Γs e ≫= maybe_inl;
     guard (ref_seg_offset rs = 0);
     inl <$> τ !!{Γ} rs
  | e #> rs =>
     τ ← type_check Γs e ≫= maybe_inr;
     guard (ref_seg_offset rs = 0);
     inr <$> τ !!{Γ} rs
  | alloc{τ} e =>
     τ' ← type_check Γs e ≫= maybe_inr; _ ← maybe_TBase τ' ≫= maybe_TInt;
     guard (✓{Γ} τ); Some (inl τ)
  | free e =>
     τ' ← type_check Γs e ≫= maybe_inl;
     Some (inr voidT)
  | @{op} e =>
     τ ← type_check Γs e ≫= maybe_inr;
     inr <$> unop_type_of op τ
  | e1 @{op} e2 =>
     τ1 ← type_check Γs e1 ≫= maybe_inr;
     τ2 ← type_check Γs e2 ≫= maybe_inr;
     inr <$> binop_type_of op τ1 τ2
  | if{e1} e2 else e3 =>
     τ1 ← type_check Γs e1 ≫= maybe_inr; _ ← maybe_TBase τ1;
     τ2 ← type_check Γs e2 ≫= maybe_inr;
     τ3 ← type_check Γs e3 ≫= maybe_inr;
     guard (τ2 = τ3); Some (inr τ2)
  | e1,, e2 =>
     _ ← type_check Γs e1 ≫= maybe_inr;
     inr <$> type_check Γs e2 ≫= maybe_inr
  | cast{σ} e =>
     τ ← type_check Γs e ≫= maybe_inr;
     guard (cast_typed Γ τ σ); Some (inr σ)
  end.
Global Instance ectx_item_lookup :
    LookupE envs (ectx_item Ti) (lrtype Ti) (lrtype Ti) := λ Γs Ei τlr,
  let '(Γ,Γf,Γm,τs) := Γs in
  match Ei, τlr with
  | .* □, inr τ =>
    τp ← maybe_TBase τ ≫= maybe_TPtr;
    guard (✓{Γ} τp); Some (inl τp)
  | & □, inl τ => Some (inr (τ.*))
  | □ ::={ass} e2, inl τ1 =>
     τ2 ← type_check Γs e2 ≫= maybe_inr;
     inr <$> assign_type_of Γ τ1 τ2 ass
  | e1 ::={ass} □, inr τ2 =>
     τ1 ← type_check Γs e1 ≫= maybe_inl;
     inr <$> assign_type_of Γ τ1 τ2 ass
  | call f @ es1 □ es2, inr τ =>
     '(τs,σ) ← Γf !! f;
     τs1 ← mapM (λ e, type_check Γs e ≫= maybe_inr) (reverse es1);
     τs2 ← mapM (λ e, type_check Γs e ≫= maybe_inr) es2;
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
     _ ← maybe_TBase τ' ≫= maybe_TInt; guard (✓{Γ} τ); Some (inl τ)
  | free □, inl τ => Some (inr voidT)
  | @{op} □, inr τ => inr <$> unop_type_of op τ
  | □ @{op} e2, inr τ1 =>
     τ2 ← type_check Γs e2 ≫= maybe_inr;
     inr <$> binop_type_of op τ1 τ2
  | e1 @{op} □, inr τ2 =>
     τ1 ← type_check Γs e1 ≫= maybe_inr;
     inr <$> binop_type_of op τ1 τ2
  | if{□} e2 else e3, inr τ1 =>
     _ ← maybe_TBase τ1;
     τ2 ← type_check Γs e2 ≫= maybe_inr;
     τ3 ← type_check Γs e3 ≫= maybe_inr;
     guard (τ2 = τ3); Some (inr τ2)
  | □ ,, e2, inr τ1 => inr <$> type_check Γs e2 ≫= maybe_inr
  | cast{σ} □, inr τ => guard (cast_typed Γ τ σ); Some (inr σ)
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
  | ! e => _ ← type_check Γs e ≫= maybe_inr; Some (false,None)
  | goto _ => Some (true,None)
  | ret e => τ ← type_check Γs e ≫= maybe_inr; Some (true,Some τ)
  | blk{τ} s =>
     guard (✓{Γ} τ); guard (int_typed (size_of Γ τ) sptrT);
     type_check (Γ,Γf,Γm,τ :: τs) s
  | s1 ;; s2 =>
     '(c1,mσ1) ← type_check Γs s1;
     '(c2,mσ2) ← type_check Γs s2;
     mσ ← rettype_union mσ1 mσ2; Some (c2,mσ)
  | label _ => Some (false,None)
  | while{e} s =>
     τ ← type_check Γs e ≫= maybe_inr; _ ← maybe_TBase τ;
     '(c,mσ) ← type_check Γs s; Some (false,mσ)
  | if{e} s1 else s2 =>
     τ ← type_check Γs e ≫= maybe_inr; _ ← maybe_TBase τ;
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
  | while{e} □, (c,mσ) =>
     τ ← type_check Γs e ≫= maybe_inr; _ ← maybe_TBase τ;
     Some (false,mσ)
  | if{e} □ else s2, (c1,mσ1) =>
     τ ← type_check Γs e ≫= maybe_inr; _ ← maybe_TBase τ;
     '(c2,mσ2) ← type_check Γs s2;
     mσ ← rettype_union mσ1 mσ2; Some (c1&&c2,mσ)
  | if{e} s1 else □, (c2,mσ2) =>
     τ ← type_check Γs e ≫= maybe_inr; _ ← maybe_TBase τ;
     '(c1,mσ1) ← type_check Γs s1;
     mσ ← rettype_union mσ1 mσ2; Some (c1&&c2,mσ)
  end%S.
Global Instance esctx_item_lookup :
    LookupE envs (esctx_item Ti) (rettype Ti) (type Ti) := λ Γs Ee τlr,
  match Ee, τlr with
  | ! □, _ => Some (false,None)
  | ret □, _ => Some (true,Some τlr)
  | while{□} s, baseT τb => '(c,mσ) ← type_check Γs s; Some (false,mσ)
  | if{□} s1 else s2, baseT τb =>
     '(c1,mσ1) ← type_check Γs s1;
     '(c2,mσ2) ← type_check Γs s2;
     mσ ← rettype_union mσ1 mσ2; Some (c1 && c2,mσ)
  | _, _ => None
  end%S.
Global Instance rettype_match_dec cmσ σ : Decision (rettype_match cmσ σ) :=
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
  | CBlock o τ, Stmt_type cmσ => guard (Γm ⊢ o : τ); Some (Stmt_type cmσ)
  | CExpr e Ee, Expr_type τ =>
     τ' ← type_check Γs e ≫= maybe_inr;
     guard (τ = τ'); Stmt_type <$> τ !!{Γs} Ee
  | CFun E, Fun_type f =>
     '(σs,τ) ← Γf !! f; Expr_type <$> inr τ !!{Γs} E ≫= maybe_inr
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
     | ↘, _ | ↗, (false,_) | ↷ _, _ => Some (Stmt_type cmσ)
     | _, _ => None
     end
  | Expr e => Expr_type <$> type_check Γs e ≫= maybe_inr
  | Call f vs =>
     '(σs,_) ← Γf !! f;
     σs' ← mapM (type_check (Γ,Γm)) vs;
     guard ((σs : list (type Ti)) = σs'); Some (Fun_type f)
  | Return f v =>
     '(_,σ) ← Γf !! f;
     σ' ← type_check (Γ,Γm) v;
     guard ((σ : type Ti) = σ'); Some (Fun_type f)
  | Undef (UndefExpr E e) =>
     Expr_type <$> (type_check Γs e ≫= lookupE Γs E) ≫= maybe_inr
  | Undef (UndefBranch e Es Ω v) =>
     τ ← type_check (Γ,Γm) v;
     τ' ← type_check Γs e ≫= maybe_inr;
     guard ((τ : type Ti) = τ'); Stmt_type <$> τ !!{Γs} Es
  end.
End typing.

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

Lemma SBlock_typed Γ Γf Γm τs τ s c mσ :
  ✓{Γ} τ →int_typed (size_of Γ τ) sptrT →
  (Γ,Γf,Γm,τ :: τs) ⊢ s : (c,mσ) → (Γ,Γf,Γm,τs) ⊢ blk{τ} s : (c,mσ).
Proof. by constructor. Qed.
Lemma assign_typed_type_valid Γ τ1 τ2 ass σ :
  assign_typed Γ τ1 τ2 ass σ → ✓{Γ} τ1 → ✓{Γ} σ.
Proof. destruct 1; eauto using cast_typed_type_valid. Qed.
Lemma funtypes_valid_args_valid Γ Γf f τs τ :
  ✓{Γ} Γf → Γf !! f = Some (τs,τ) → ✓{Γ}* τs.
Proof. intros HΓf ?. by apply (HΓf f (τs,τ)). Qed.
Lemma funtypes_valid_type_valid Γ Γf f τs τ :
  ✓{Γ} Γf → Γf !! f = Some (τs,τ) → ✓{Γ} τ.
Proof. intros HΓf ?. by apply (HΓf f (τs,τ)). Qed.
Lemma expr_typed_type_valid Γ Γf Γm τs e τlr :
  ✓ Γ → ✓{Γ} Γf → ✓{Γ}* τs → (Γ,Γf,Γm,τs) ⊢ e : τlr → ✓{Γ} (lrtype_type τlr).
Proof.
  induction 4 using @expr_typed_ind; decompose_Forall_hyps;
    eauto 4 using addr_typed_type_valid, val_typed_type_valid,
    type_valid_ptr_type_valid, funtypes_valid_type_valid,
    unop_typed_type_valid, binop_typed_type_valid, cast_typed_type_valid,
    TBase_valid, TPtr_valid, TVoid_valid, type_valid_ptr_type_valid,
    assign_typed_type_valid, ref_seg_typed_type_valid.
Qed.
Lemma expr_inl_typed_type_valid Γ Γf Γm τs e τ :
  ✓ Γ → ✓{Γ} Γf → ✓{Γ}* τs → (Γ,Γf,Γm,τs) ⊢ e : inl τ → ✓{Γ} τ.
Proof. by apply expr_typed_type_valid. Qed.
Lemma expr_inr_typed_type_valid Γ Γf Γm τs e τ :
  ✓ Γ → ✓{Γ} Γf → ✓{Γ}* τs → (Γ,Γf,Γm,τs) ⊢ e : inr τ → ✓{Γ} τ.
Proof. by apply expr_typed_type_valid. Qed.
Lemma funtypes_valid_weaken Γ1 Γ2 Γf : ✓ Γ1 → ✓{Γ1} Γf → Γ1 ⊆ Γ2 → ✓{Γ2} Γf.
Proof.
  intros ? HΓf ? f [τs τ] Hf. destruct (HΓf f (τs,τ)) as (Hτs&?&?); simpl in *;
    split_ands; eauto using types_valid_weaken, type_valid_weaken.
  clear Hf. induction Hτs; decompose_Forall_hyps; constructor;
    simpl; erewrite <-1?size_of_weaken by eauto; eauto.
Qed.
Lemma assign_typed_weaken Γ1 Γ2 ass τ1 τ2 σ :
  ✓ Γ1 → assign_typed Γ1 τ1 τ2 ass σ → Γ1 ⊆ Γ2 → assign_typed Γ2 τ1 τ2 ass σ.
Proof. destruct 2; econstructor; eauto using cast_typed_weaken. Qed.
Lemma expr_typed_weaken Γ1 Γ2 Γf1 Γf2 Γm1 Γm2 τs1 τs2 e τlr :
  ✓ Γ1 → (Γ1,Γf1,Γm1,τs1) ⊢ e : τlr → Γ1 ⊆ Γ2 → Γf1 ⊆ Γf2 →
  (∀ o σ, Γm1 ⊢ o : σ → Γm2 ⊢ o : σ) → τs1 `prefix_of` τs2 →
  (Γ2,Γf2,Γm2,τs2) ⊢ e : τlr.
Proof.
  intros ? He ??? [σs ->].
  induction He using @expr_typed_ind; typed_constructor;
    erewrite <-1?size_of_weaken by eauto; eauto using val_typed_weaken,
    assign_typed_weaken, addr_typed_weaken, addr_strict_weaken,
    type_valid_weaken, lookup_weaken, lookup_app_l_Some, cast_typed_weaken,
    ref_seg_typed_weaken, lockset_valid_weaken.
Qed.
Lemma ectx_item_typed_weaken Γ1 Γ2 Γf1 Γf2 Γm1 Γm2 τs1 τs2 Ei τlr σlr :
  ✓ Γ1 → (Γ1,Γf1,Γm1,τs1) ⊢ Ei : τlr ↣ σlr → Γ1 ⊆ Γ2 → Γf1 ⊆ Γf2 →
  (∀ o σ, Γm1 ⊢ o : σ → Γm2 ⊢ o : σ) → τs1 `prefix_of` τs2 →
  (Γ2,Γf2,Γm2,τs2) ⊢ Ei : τlr ↣ σlr.
Proof.
  destruct 2; typed_constructor;
    eauto using type_valid_weaken, addr_strict_weaken, assign_typed_weaken,
    expr_typed_weaken, lookup_weaken, cast_typed_weaken, Forall2_impl,
    ref_seg_typed_weaken.
Qed.
Lemma ectx_typed_weaken Γ1 Γ2 Γf1 Γf2 Γm1 Γm2 τs1 τs2 E τlr σlr :
  ✓ Γ1 → (Γ1,Γf1,Γm1,τs1) ⊢ E : τlr ↣ σlr → Γ1 ⊆ Γ2 → Γf1 ⊆ Γf2 →
  (∀ o σ, Γm1 ⊢ o : σ → Γm2 ⊢ o : σ) → τs1 `prefix_of` τs2 →
  (Γ2,Γf2,Γm2,τs2) ⊢ E : τlr ↣ σlr.
Proof.
  intros ? HE ???. revert τlr HE. induction E; intros; typed_inversion_all;
    typed_constructor; eauto using ectx_item_typed_weaken.
Qed.
Lemma stmt_typed_weaken Γ1 Γ2 Γf1 Γf2 Γm1 Γm2 τs1 τs2 s mτ :
  ✓ Γ1 → (Γ1,Γf1,Γm1,τs1) ⊢ s : mτ → Γ1 ⊆ Γ2 → Γf1 ⊆ Γf2 →
  (∀ o σ, Γm1 ⊢ o : σ → Γm2 ⊢ o : σ) → τs1 `prefix_of` τs2 →
  (Γ2,Γf2,Γm2,τs2) ⊢ s : mτ.
Proof.
  intros ? Hs ???. revert τs2. induction Hs; typed_constructor;
    erewrite <-1?size_of_weaken by eauto;
    eauto using expr_typed_weaken, type_valid_weaken;
    unfold typed, stmt_typed in *; simpl in *; eauto using prefix_of_cons.
Qed.
Lemma sctx_item_typed_weaken Γ1 Γ2 Γf1 Γf2 Γm1 Γm2 τs1 τs2 Es mτ mσ :
  ✓ Γ1 → (Γ1,Γf1,Γm1,τs1) ⊢ Es : mτ ↣ mσ → Γ1 ⊆ Γ2 → Γf1 ⊆ Γf2 →
  (∀ o σ, Γm1 ⊢ o : σ → Γm2 ⊢ o : σ) → τs1 `prefix_of` τs2 →
  (Γ2,Γf2,Γm2,τs2) ⊢ Es : mτ ↣ mσ.
Proof.
  destruct 2; typed_constructor;
    eauto using stmt_typed_weaken, expr_typed_weaken.
Qed.
Lemma esctx_item_typed_weaken Γ1 Γ2 Γf1 Γf2 Γm1 Γm2 τs1 τs2 Ee τ mσ :
  ✓ Γ1 → (Γ1,Γf1,Γm1,τs1) ⊢ Ee : τ ↣ mσ → Γ1 ⊆ Γ2 → Γf1 ⊆ Γf2 →
  (∀ o σ, Γm1 ⊢ o : σ → Γm2 ⊢ o : σ) → τs1 `prefix_of` τs2 →
  (Γ2,Γf2,Γm2,τs2) ⊢ Ee : τ ↣ mσ.
Proof. destruct 2; typed_constructor; eauto using stmt_typed_weaken. Qed.
Lemma ctx_item_typed_weaken Γ1 Γ2 Γf1 Γf2 Γm1 Γm2 τs Ek τf σf :
  ✓ Γ1 → (Γ1,Γf1,Γm1,τs) ⊢ Ek : τf ↣ σf → Γ1 ⊆ Γ2 → Γf1 ⊆ Γf2 →
  (∀ o σ, Γm1 ⊢ o : σ → Γm2 ⊢ o : σ) → (Γ2,Γf2,Γm2,τs) ⊢ Ek : τf ↣ σf.
Proof.
  destruct 2; typed_constructor; eauto using sctx_item_typed_weaken,
    ectx_typed_weaken, esctx_item_typed_weaken, expr_typed_weaken,
    Forall2_impl, lookup_weaken.
Qed.
Lemma ctx_typed_weaken Γ1 Γ2 Γf1 Γf2 Γm1 Γm2 k τf σf :
  ✓ Γ1 → (Γ1,Γf1,Γm1) ⊢ k : τf ↣ σf → Γ1 ⊆ Γ2 → Γf1 ⊆ Γf2 →
  (∀ o σ, Γm1 ⊢ o : σ → Γm2 ⊢ o : σ) → (Γ2,Γf2,Γm2) ⊢ k : τf ↣ σf.
Proof.
  intros ? Hk ???. revert τf Hk. induction k; intros; typed_inversion_all;
    typed_constructor; eauto using ctx_item_typed_weaken.
Qed.
Lemma direction_typed_weaken Γ1 Γ2 Γm1 Γm2 d τf :
  ✓ Γ1 → (Γ1,Γm1) ⊢ d : τf → Γ1 ⊆ Γ2 →
  (∀ o σ, Γm1 ⊢ o : σ → Γm2 ⊢ o : σ) → (Γ2,Γm2) ⊢ d : τf.
Proof. destruct 2; typed_constructor; eauto using val_typed_weaken. Qed.
Lemma funenv_pretyped_weaken Γ1 Γ2 Γm1 Γm2 δ Γf1 Γf2 :
  ✓ Γ1 → funenv_pretyped Γ1 Γm1 δ Γf1 → Γ1 ⊆ Γ2 → Γf1 ⊆ Γf2 →
  (∀ o σ, Γm1 ⊢ o : σ → Γm2 ⊢ o : σ) → funenv_pretyped Γ2 Γm2 δ Γf2.
Proof.
  intros ? Hδ ??? f s ?.
  destruct (Hδ f s) as (τs&τ&cmτ&Hf&Hτs&?&?&Hs&?&?); auto.
  exists τs τ cmτ; split_ands; eauto using stmt_typed_weaken,
    types_valid_weaken, type_valid_weaken, lookup_weaken.
  clear Hf Hs. induction Hτs; decompose_Forall_hyps; constructor;
    simpl; erewrite <-1?size_of_weaken by eauto; eauto.
Qed.
Lemma funenv_typed_weaken Γ1 Γ2 Γm1 Γm2 δ Γf :
  ✓ Γ1 → (Γ1,Γm1) ⊢ δ : Γf → Γ1 ⊆ Γ2 → (∀ o σ, Γm1 ⊢ o : σ → Γm2 ⊢ o : σ) →
  (Γ2,Γm2) ⊢ δ : Γf.
Proof. destruct 2; split; simpl in *; eauto using funenv_pretyped_weaken. Qed.
Lemma funtypes_valid_empty Γ : ✓{Γ} ∅.
Proof. by intros ??; simpl_map. Qed.
Lemma funtypes_valid_insert Γ Γf f τs τ :
  ✓{Γ} Γf → ✓{Γ}* τs → Forall (λ τ, int_typed (size_of Γ τ) sptrT) τs →
  ✓{Γ} τ → ✓{Γ} (<[f:=(τs,τ)]>Γf).
Proof.
  intros ??????; rewrite lookup_insert_Some; intros [[<- <-]|[??]]; eauto.
Qed.
Lemma funenv_pretyped_empty Γ Γm Γf : funenv_pretyped Γ Γm ∅ Γf.
Proof. by intros ??; simpl_map. Qed.
Lemma funenv_pretyped_insert Γ Γm δ Γf f s τ τs cmτ :
  funenv_pretyped Γ Γm δ Γf → Γf !! f = Some (τs, τ) →
  ✓{Γ}* τs → Forall (λ τ, int_typed (size_of Γ τ) sptrT) τs → ✓{Γ} τ →
  (Γ,Γf,Γm,τs) ⊢ s : cmτ → gotos s ⊆ labels s → rettype_match cmτ τ →
  funenv_pretyped Γ Γm (<[f:=s]> δ) Γf.
Proof. intros ???????? f' s'; rewrite lookup_insert_Some; naive_solver. Qed.
Lemma funenv_lookup Γ Γm Γf δ f τs τ :
  ✓ Γ → (Γ,Γm) ⊢ δ : Γf → Γf !! f = Some (τs,τ) → ∃ s cmτ,
    δ !! f = Some s ∧
    ✓{Γ}* τs ∧ Forall (λ τ, int_typed (size_of Γ τ) sptrT) τs ∧ ✓{Γ} τ ∧
    (Γ,Γf,Γm,τs) ⊢ s : cmτ ∧ gotos s ⊆ labels s ∧ rettype_match cmτ τ.
Proof.
  intros ? [Hδ HΓf] ?; simpl in *. assert (∃ s, δ !! f = Some s) as [s ?].
  { apply elem_of_dom, HΓf, elem_of_dom; eauto. }
  destruct (Hδ f s) as (?&?&?&?&?); simplify_equality; eauto.
Qed.
Lemma funenv_lookup_inv Γ Γm Γf δ f s :
  ✓ Γ → (Γ,Γm) ⊢ δ : Γf → δ !! f = Some s → ∃ τs τ cmτ,
    Γf !! f = Some (τs,τ) ∧
    ✓{Γ}* τs ∧ Forall (λ τ, int_typed (size_of Γ τ) sptrT) τs ∧ ✓{Γ} τ ∧
    (Γ,Γf,Γm,τs) ⊢ s : cmτ ∧ gotos s ⊆ labels s ∧ rettype_match cmτ τ.
Proof. intros ? [Hδ _] ?. destruct (Hδ f s); naive_solver. Qed.
Lemma funenv_lookup_gotos Γ Γm Γf δ f s :
  ✓ Γ → (Γ,Γm) ⊢ δ : Γf → δ !! f = Some s → gotos s ⊆ labels s.
Proof.
  intros. by destruct (funenv_lookup_inv Γ Γm Γf δ f s) as (?&?&?&?&?&?&?&?&?&?).
Qed.
Lemma funenv_typed_funtypes_valid Γ Γm δ Γf : ✓ Γ → (Γ,Γm) ⊢ δ : Γf → ✓{Γ} Γf.
Proof.
  intros ? HΓf f [τs τ] ?; simpl.
  by destruct (funenv_lookup Γ Γm Γf δ f τs τ) as (?&?&?&?&?&?&?&?&?).
Qed.
Lemma EVals_typed_inv Γ Γf Γm τs Ωs vs σs :
  length Ωs = length vs → ✓{Γ}* σs →
  (Γ,Γf,Γm,τs) ⊢* #{Ωs}* vs :* inr <$> σs → (Γ,Γm) ⊢* vs :* σs.
Proof.
  rewrite <-Forall2_same_length. intros Hvs.
  revert σs. induction Hvs; intros ? [|????] ?; decompose_Forall_hyps;
    typed_inversion_all; constructor; eauto.
Qed.
Lemma ctx_typed_stack_typed Γ Γf Γm k τf σf :
  (Γ,Γf,Γm) ⊢ k : τf ↣ σf → Γm ⊢* get_stack k :* get_stack_types k.
Proof.
  revert τf. induction k as [|Ek k IH]; intros; typed_inversion_all; eauto;
    repeat match goal with
    | H : (_,_,_,_) ⊢ Ek : _ ↣ _ |- _ => typed_inversion H
    | H : Forall2 _ ?l ?l' |- _ =>
       unless (length l = length l') by done;
       assert (length l = length l') by eauto using Forall2_length
    end; rewrite ?fst_zip, ?snd_zip by lia; eauto using Forall2_app.
Qed.
Lemma ectx_item_subst_typed Γ Γf Γm τs Ei e τlr σlr :
  (Γ,Γf,Γm,τs) ⊢ Ei : τlr ↣ σlr →
  (Γ,Γf,Γm,τs) ⊢ e : τlr → (Γ,Γf,Γm,τs) ⊢ subst Ei e : σlr.
Proof.
  destruct 1; simpl; typed_constructor; eauto.
  rewrite ?fmap_app; eauto using Forall2_app, Forall2_cons.
Qed.
Lemma ectx_subst_typed Γ Γf Γm τs E e τlr σlr :
  (Γ,Γf,Γm,τs) ⊢ E : τlr ↣ σlr →
  (Γ,Γf,Γm,τs) ⊢ e : τlr → (Γ,Γf,Γm,τs) ⊢ subst E e : σlr.
Proof.
  intros HE. revert e. induction HE; simpl; eauto using ectx_item_subst_typed.
Qed.
Lemma ectx_item_subst_typed_rev Γ Γf Γm τs Ei e σlr :
  (Γ,Γf,Γm,τs) ⊢ subst Ei e : σlr → ∃ τlr,
    (Γ,Γf,Γm,τs) ⊢ e : τlr ∧ (Γ,Γf,Γm,τs) ⊢ Ei : τlr ↣ σlr.
Proof.
  intros He. destruct Ei; simpl; typed_inversion He;
    decompose_Forall_hyps; simplify_list_fmap_equality;
    eexists; split; eauto; typed_constructor; eauto.
Qed.
Lemma ectx_subst_typed_rev Γ Γf Γm τs E e σlr :
  (Γ,Γf,Γm,τs) ⊢ subst E e : σlr → ∃ τlr,
    (Γ,Γf,Γm,τs) ⊢ e : τlr ∧ (Γ,Γf,Γm,τs) ⊢ E : τlr ↣ σlr.
Proof.
  revert e. induction E as [|Ei E IH]; simpl; intros e ?.
  { exists σlr. by repeat constructor. }
  edestruct (IH (subst Ei e)) as (τlr1&?&?); auto.
  destruct (ectx_item_subst_typed_rev Γ Γf Γm τs Ei e τlr1) as (τlr2&?&?); auto.
  exists τlr2; split; auto. typed_constructor; eauto.
Qed.
Lemma sctx_item_subst_typed Γ Γf Γm τs Es s cmτ cmσ :
  (Γ,Γf,Γm,τs) ⊢ Es : cmτ ↣ cmσ → (Γ,Γf,Γm,τs) ⊢ s : cmτ →
  (Γ,Γf,Γm,τs) ⊢ subst Es s : cmσ.
Proof. destruct 1; simpl; typed_constructor; eauto; esolve_elem_of. Qed.
Lemma sctx_item_subst_typed_rev Γ Γf Γm τs Es s cmσ :
  (Γ,Γf,Γm,τs) ⊢ subst Es s : cmσ → ∃ cmτ,
    (Γ,Γf,Γm,τs) ⊢ s : cmτ ∧ (Γ,Γf,Γm,τs) ⊢ Es : cmτ ↣ cmσ.
Proof.
  intros Hs. destruct Es; simpl; typed_inversion Hs;
    eexists; split_ands; eauto; try typed_constructor; eauto; esolve_elem_of.
Qed.
Lemma esctx_item_subst_typed Γ Γf Γm τs Ee e τ cmσ :
  (Γ,Γf,Γm,τs) ⊢ Ee : τ ↣ cmσ → (Γ,Γf,Γm,τs) ⊢ e : inr τ →
  (Γ,Γf,Γm,τs) ⊢ subst Ee e : cmσ.
Proof. destruct 1; simpl; typed_constructor; eauto. Qed.
Lemma esctx_item_subst_typed_rev Γ Γf Γm τs Ee e cmσ :
  (Γ,Γf,Γm,τs) ⊢ subst Ee e : cmσ → ∃ τ,
    (Γ,Γf,Γm,τs) ⊢ e : inr τ ∧ (Γ,Γf,Γm,τs) ⊢ Ee : τ ↣ cmσ.
Proof.
  intros He. destruct Ee; simpl; typed_inversion He;
    eexists; split_ands; eauto; typed_constructor; eauto.
Qed.
Lemma sctx_item_typed_Some_l Γ Γf Γm τs Es c1 τ cmτ :
  (Γ,Γf,Γm,τs) ⊢ Es : (c1,Some τ) ↣ cmτ → ∃ c2, cmτ = (c2, Some τ).
Proof.
  intros HEs. typed_inversion HEs; unfold rettype_union in *;
    repeat case_match; simplify_option_equality; eauto.
Qed.
Lemma Fun_type_stack_types Γ Γf Γm k f τf :
  (Γ,Γf,Γm) ⊢ k : Fun_type f ↣ τf → get_stack_types k = [].
Proof. by destruct k as [|[]]; intros; typed_inversion_all. Qed.
Lemma Fun_type_labels Γ Γf Γm k f τf :
  (Γ,Γf,Γm) ⊢ k : Fun_type f ↣ τf → labels k = ∅.
Proof. by destruct k as [|[]]; intros; typed_inversion_all. Qed.
Lemma rettype_union_l mσ : rettype_union mσ None = Some mσ.
Proof. by destruct mσ. Qed.

Ltac simplify :=
  repeat match goal with
  | _ : maybe_inl ?τlr = Some _ |- _ => is_var τlr; destruct τlr
  | _ : maybe_inr ?τlr = Some _ |- _ => is_var τlr; destruct τlr
  | _ : maybe_TBase ?τ = Some _ |- _ => is_var τ; destruct τ
  | _ : maybe_TPtr ?τb = Some _ |- _ => is_var τb; destruct τb
  | _ : maybe_TInt ?τb = Some _ |- _ => is_var τb; destruct τb
  | mcτ : rettype _ |- _ => destruct mcτ
  | _ => progress simplify_option_equality
  | _ => case_match
  end.
Hint Resolve (type_check_sound (V:=val Ti)) (type_check_sound (V:=addr Ti)).
Hint Resolve (mapM_type_check_sound (V:=val Ti)).
Hint Immediate (path_type_check_sound (R:=ref_seg _)).
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
      mapM (λ e, type_check (Γ,Γf,Γm,τs) e ≫= maybe_inr) es = Some σs →
      (Γ,Γf,Γm,τs) ⊢* es :* inr <$> σs).
    { intros ??. rewrite mapM_Some.
      induction 2; decompose_Forall_hyps; simplify; constructor; eauto. }
    revert τlr; induction e using @expr_ind_alt; intros; simplify;
      typed_constructor; eauto.
  * assert (∀ es σs,
      Forall2 (λ e τlr, type_check (Γ,Γf,Γm,τs) e = Some τlr) es (inr <$> σs) →
      mapM (λ e, type_check (Γ,Γf,Γm,τs) e ≫= maybe_inr) es = Some σs) as help.
    { intros es σs. rewrite Forall2_fmap_r, mapM_Some.
      induction 1; constructor; simplify_option_equality; eauto. }
    induction 1 using @expr_typed_ind; simplify_option_equality;
      erewrite ?type_check_complete, ?path_type_check_complete,
        ?assign_type_of_complete, ?unop_type_of_complete,
        ?binop_type_of_complete, ?help by eauto; eauto.
Qed.
Hint Resolve (type_check_sound (V:=expr Ti)).
Global Instance: PathTypeCheckSpec envs
  (lrtype Ti) (lrtype Ti) (ectx_item Ti) (✓ ∘ fst ∘ fst ∘ fst).
Proof.
  intros [[[Γ Γf] Γm] τs] Ei τlr; simpl; split.
  * assert (∀ es σs,
      mapM (λ e, type_check (Γ,Γf,Γm,τs) e ≫= maybe_inr) es = Some σs →
      (Γ,Γf,Γm,τs) ⊢* es :* inr <$> σs).
    { intros es σs. rewrite mapM_Some. induction 1; simplify; eauto. }
    destruct τlr, Ei; intros; simplify; typed_constructor; eauto.
  * assert (∀ es σs, (Γ,Γf,Γm,τs) ⊢* es :* inr <$> σs →
      mapM (λ e, type_check (Γ,Γf,Γm,τs) e ≫= maybe_inr) es = Some σs) as help.
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
