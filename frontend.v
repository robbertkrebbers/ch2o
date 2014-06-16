(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Import type_system expression_eval.
Local Open Scope expr_scope.
Local Open Scope ctype_scope.

Inductive cexpr (Ti : Set) :=
  | EVar : nat → cexpr Ti
  | EGlob : nat → cexpr Ti
  | EConst : int_type Ti → Z → cexpr Ti
  | EAddrOf : cexpr Ti → cexpr Ti
  | EDeref : cexpr Ti → cexpr Ti
  | EAssign : assign → cexpr Ti → cexpr Ti → cexpr Ti
  | ECall : funname → list (cexpr Ti) → cexpr Ti
  | EAlloc : type Ti → cexpr Ti
  | EFree : cexpr Ti → cexpr Ti
  | EUnOp : unop → cexpr Ti → cexpr Ti
  | EBinOp : binop → cexpr Ti → cexpr Ti → cexpr Ti
  | EIf : cexpr Ti → cexpr Ti → cexpr Ti → cexpr Ti
  | EComma : cexpr Ti → cexpr Ti → cexpr Ti
  | ECast : type Ti → cexpr Ti → cexpr Ti
  | EField : cexpr Ti → nat → cexpr Ti.
Arguments EVar {_} _.
Arguments EGlob {_} _.
Arguments EConst {_} _ _.
Arguments EAddrOf {_} _.
Arguments EDeref {_} _.
Arguments EAssign {_} _ _ _.
Arguments ECall {_} _ _.
Arguments EAlloc {_} _.
Arguments EFree {_} _.
Arguments EUnOp {_} _ _.
Arguments EBinOp {_} _ _ _.
Arguments EIf {_} _ _ _.
Arguments EComma {_} _ _.
Arguments ECast {_} _ _.
Arguments EField {_} _ _.

Inductive cstmt (Ti : Set) :=
  | SDo : cexpr Ti → cstmt Ti
  | SSkip : cstmt Ti
  | SGoto : labelname → cstmt Ti
  | SBreak : cstmt Ti
  | SContinue : cstmt Ti
  | SReturn : option (cexpr Ti) → cstmt Ti
  | SBlock : type Ti → cstmt Ti → cstmt Ti
  | SComp : cstmt Ti → cstmt Ti → cstmt Ti
  | SLabel : labelname → cstmt Ti → cstmt Ti
  | SWhile : cexpr Ti → cstmt Ti → cstmt Ti
  | SIf : cexpr Ti → cstmt Ti → cstmt Ti → cstmt Ti.
Arguments SDo {_} _.
Arguments SSkip {_}.
Arguments SGoto {_} _.
Arguments SBreak {_}.
Arguments SContinue {_}.
Arguments SReturn {_} _.
Arguments SBlock {_} _ _.
Arguments SComp {_} _ _.
Arguments SLabel {_} _ _.
Arguments SWhile {_} _ _.
Arguments SIf {_} _ _ _.

Record cenv (Ti : Set) := CEnv {
  c_env : list (tag * list (type Ti));
  c_globals : list (type Ti * option (cexpr Ti));
  c_funs : list (funname * list (type Ti) * type Ti * cstmt Ti)
}.
Arguments CEnv {_} _ _ _.
Arguments c_env {_} _.
Arguments c_globals {_} _.
Arguments c_funs {_} _.

Section frontend.
Context `{IntEnv Ti, PtrEnv Ti}.

Definition to_R (eτlr : expr Ti * lrtype Ti) : expr Ti * type Ti :=
  match eτlr with
  | (e, inl τ) =>
    match maybe_TArray τ with
    | Some (τ',_) => (& (elt e), τ'.*) | None => (load e, τ)
    end
  | (e, inr τ) => (e,τ)
  end%E.
Definition to_expr (Γ : env Ti) (Γf : funtypes Ti) (m : mem Ti)
    (τs : list (type Ti)) : cexpr Ti → option (expr Ti * lrtype Ti) :=
  fix go e :=
  match e with
  | EVar n =>
     τ ← τs !! n;
     Some (var{τ} n, inl τ)
  | EGlob n =>
     τ ← type_check m (N.of_nat n : index);
     Some (% (addr_top (N.of_nat n) τ), inl τ)
  | EConst τi x =>
     guard (int_typed x τi);
     Some (# (intV{τi} x), inr (intT τi))
  | EDeref e =>
     '(e',τ) ← to_R <$> go e;
     τp ← maybe_TBase τ ≫= maybe_TPtr;
     Some (.* e', inl τp)
  | EAddrOf e =>
     '(e',τlr) ← go e;
     τ ← maybe_inl τlr;
     Some (& e', inr (τ.*))
  | EAssign ass e1 e2 =>
     '(e1',τlr1) ← go e1;
     τ1 ← maybe_inl τlr1;
     '(e2',τ2) ← to_R <$> go e2;
     σ ← assign_type_of τ1 τ2 ass;
     Some (e1' ::={ass} e2', inr σ)
  | ECall f es =>
     '(τs,σ) ← Γf !! f;
     τses ← fmap to_R <$> mapM go es;
     guard (snd <$> τses = τs);
     Some (call f @ fst <$> τses, inr σ)
  | EAlloc τ =>
     guard (✓{Γ} τ);
     guard (int_typed (size_of Γ τ) sptrT);
     Some (& (alloc τ), inr (τ.*))
  | EFree e =>
     '(e',τ) ← to_R <$> go e;
     _ ← maybe_TBase τ ≫= maybe_TPtr;
     Some (free (.* e'), inr voidT)
  | EUnOp op e =>
     '(e',τ) ← to_R <$> go e;
     σ ← unop_type_of op τ;
     Some (@{op} e', inr σ)
  | EBinOp op e1 e2 =>
     '(e1',τ1) ← to_R <$> go e1;
     '(e2',τ2) ← to_R <$> go e2;
     σ ← binop_type_of op τ1 τ2;
     Some (e1' @{op} e2', inr σ)
  | EIf e1 e2 e3 =>
     '(e1',τ1) ← to_R <$> go e1;
     _ ← maybe_TBase τ1;
     '(e2',τ2) ← to_R <$> go e2;
     '(e3',τ3) ← to_R <$> go e3;
     guard (τ2 = τ3);
     Some (if{e1'} e2' else e3', inr τ3)
  | EComma e1 e2 =>
     '(e1',τ1) ← to_R <$> go e1;
     '(e2',τ2) ← to_R <$> go e2;
     Some (e1',, e2', inr τ2)
  | ECast σ e =>
     '(e',τ) ← to_R <$> go e;
     guard (cast_typed Γ τ σ);
     Some (cast{σ} e', inr σ)
  | EField e i =>
     '(e',τrl) ← go e;
     τ ← maybe_inl τrl;
     '(c,s) ← maybe_TCompound τ;
     σs ← Γ !! s;
     σ ← σs !! i;
     Some (e' .> i, inl σ)
  end%E.

Global Instance cstmt_labels : Labels (cstmt Ti) :=
  fix go s := let _ : Labels _ := @go in
  match s with
  | SBlock _ s => labels s
  | SComp s1 s2 => labels s1 ∪ labels s2
  | SLabel l s => {[ l ]} ∪ labels s
  | SWhile _ s => labels s
  | SIf _ s1 s2 => labels s1 ∪ labels s2
  | _ => ∅
  end.
Fixpoint cstmt_has_break_continue (s : cstmt Ti) : bool :=
  match s with
  | SBreak | SContinue => true
  | SBlock _ s => cstmt_has_break_continue s
  | SComp s1 s2 => cstmt_has_break_continue s1 || cstmt_has_break_continue s2
  | SLabel _ s => cstmt_has_break_continue s
  | SIf _ s1 s2 => cstmt_has_break_continue s1 || cstmt_has_break_continue s2
  | _ => false
  end.
Definition to_while (mLcLb : option (labelname * labelname))
    (e : expr Ti) (s : stmt Ti) : stmt Ti :=
  match mLcLb with
  | Some (Lc,Lb) => while{e} (s ;; label Lc) ;; label Lb
  | None => while{e} s
  end.

Definition to_stmt (Γ : env Ti) (Γf : funtypes Ti) (m : mem Ti) :
    list (type Ti) → labelset → option (labelname * labelname) →
    cstmt Ti → option (stmt Ti * rettype Ti) :=
  fix go τs Ls mLcLb s {struct s} :=
  match s with
  | SDo e => '(e',_) ← to_R <$> to_expr Γ Γf m τs e; Some (! e', (false, None))
  | SSkip => Some (skip, (false, None))
  | SGoto l => Some (goto l, (true, None))
  | SContinue => '(Lc,_) ← mLcLb; Some (goto Lc, (true, None))
  | SBreak => '(_,Lb) ← mLcLb; Some (goto Lb, (true, None))
  | SReturn (Some e) =>
     '(e',τ) ← to_R <$> to_expr Γ Γf m τs e; Some (ret e', (true, Some τ))
  | SReturn None => Some (ret (#voidV), (true, Some voidT))
  | SBlock τ s =>
     guard (✓{Γ} τ);
     guard (int_typed (size_of Γ τ) sptrT);
     '(s',cmσ) ← go (τ :: τs) Ls mLcLb s;
     Some (blk{τ} s', cmσ)
  | SComp s1 s2 =>
     '(s1',cmσ1) ← go τs Ls mLcLb s1; '(s2',cmσ2) ← go τs Ls mLcLb s2;
     mσ ← rettype_union (cmσ1.2) (cmσ2.2);
     Some (s1' ;; s2',(cmσ2.1, mσ))
  | SLabel l s => '(s',cmσ) ← go τs Ls mLcLb s; Some (l :; s', cmσ)
  | SWhile e s =>
     '(e',τ) ← to_R <$> to_expr Γ Γf m τs e; _ ← maybe_TBase τ;
     let (mLcLr',Ls') :=
       if cstmt_has_break_continue s
       then let Lc := fresh Ls in let Lr := fresh ({[ Lc ]} ∪ Ls)
            in (Some (Lc,Lr), {[ Lc ; Lr ]} ∪ Ls)
       else (None,Ls) in
     '(s',cmσ) ← go τs Ls' mLcLr' s; Some (to_while mLcLr' e' s',(false, cmσ.2))
  | SIf e s1 s2 =>
     '(e',τ) ← to_R <$> to_expr Γ Γf m τs e; _ ← maybe_TBase τ;
     '(s1',cmσ1) ← go τs Ls mLcLb s1; '(s2',cmσ2) ← go τs Ls mLcLb s2;
     mσ ← rettype_union (cmσ1.2) (cmσ2.2);
     Some (if{e'} s1' else s2', (cmσ1.1 && cmσ2.1, mσ))%S
  end%T.
Definition to_mem (Γ : env Ti) :
    list (type Ti  * option (cexpr Ti)) → index → mem Ti → option (mem Ti) :=
  fix go G o m_acc :=
  match G with
  | [] => Some m_acc
  | (τ,Some e) :: G =>
     '(e',τ') ← to_R <$> to_expr Γ ∅ m_acc [] e;
     guard (τ = τ');
     guard (int_typed (size_of Γ τ) sptrT);
     v ← ⟦ e' ⟧ Γ ∅ [] m_acc ≫= maybe_inr;
     go G (1 + o)%N (<[addr_top o τ:=v]{Γ}>(mem_alloc Γ o false τ m_acc))
  | (τ,None) :: G =>
     guard (✓{Γ} τ);
     guard (int_typed (size_of Γ τ) sptrT);
     go G (1 + o)%N (<[addr_top o τ:=val_0 Γ τ]{Γ}>(mem_alloc Γ o false τ m_acc))
  end.
Definition to_funs (Γ : env Ti) (m : mem Ti) :
    list (funname * list (type Ti) * type Ti * cstmt Ti) →
    funmap (list (type Ti) * type Ti * stmt Ti) →
    option (funmap (list (type Ti) * type Ti * stmt Ti)) :=
  fix go Γfuns Γacc :=
  match Γfuns with
  | [] => Some Γacc
  | (f,τs,σ,s) :: Γfuns =>
     guard (✓{Γ}* τs);
     guard (Forall (λ τ, int_typed (size_of Γ τ) sptrT) τs);
     '(s',cmσ) ← to_stmt Γ (fst <$> Γacc) m τs (labels s) None s;
     guard (rettype_match cmσ σ);
     guard (Γacc !! f = None);
     go Γfuns (<[f:=((τs,σ),s')]>Γacc)
  end.
Definition to_envs (Θ : cenv Ti) :
    option (env Ti * funtypes Ti * funenv Ti * mem Ti) :=
  guard (list_env_valid (c_env Θ));
  let Γ := map_of_list (c_env Θ) in
  m ← to_mem Γ (c_globals Θ) 0%N ∅;
  Fres ← to_funs Γ m (c_funs Θ) ∅;
  Some (Γ, fst <$> Fres, snd <$> Fres, m).
End frontend.

Section cexpr_ind.
Context {Ti : Set} (P : cexpr Ti → Prop).
Context (Pvar : ∀ i, P (EVar i)).
Context (Pglob : ∀ i, P (EGlob i)).
Context (Pconst : ∀ τi x, P (EConst τi x)).
Context (Paddrof : ∀ ce, P ce → P (EAddrOf ce)).
Context (Pderef : ∀ ce, P ce → P (EDeref ce)).
Context (Passign : ∀ ass ce1 ce2, P ce1 → P ce2 → P (EAssign ass ce1 ce2)).
Context (Pcall : ∀ f ces, Forall P ces → P (ECall f ces)).
Context (Palloc : ∀ τ, P (EAlloc τ)).
Context (Pfree : ∀ ce, P ce → P (EFree ce)).
Context (Punop : ∀ op ce, P ce → P (EUnOp op ce)).
Context (Pbinop : ∀ op ce1 ce2, P ce1 → P ce2 → P (EBinOp op ce1 ce2)).
Context (Pif : ∀ ce1 ce2 ce3, P ce1 → P ce2 → P ce3 → P (EIf ce1 ce2 ce3)).
Context (Pcomma : ∀ ce1 ce2, P ce1 → P ce2 → P (EComma ce1 ce2)).
Context (Pcast : ∀ τ ce, P ce → P (ECast τ ce)).
Context (Pfield : ∀ ce i, P ce → P (EField ce i)).

Definition cexpr_ind_alt : ∀ e, P e :=
  fix go e :=
  match e return P e with
  | EVar _ => Pvar _
  | EGlob _ => Pglob _
  | EConst _ _ => Pconst _ _
  | EAddrOf ec => Paddrof _ (go ec)
  | EDeref ec => Pderef _ (go ec)
  | EAssign _ ec1 ec2 => Passign _ _ _ (go ec1) (go ec2)
  | ECall f es => Pcall _ es $ list_ind (Forall P)
       (Forall_nil_2 _) (λ e _, Forall_cons_2 _ _ _ (go e)) es
  | EAlloc _ => Palloc _
  | EFree ec => Pfree _ (go ec)
  | EUnOp _ ec => Punop _ _ (go ec)
  | EBinOp _ ec1 ec2 => Pbinop _ _ _ (go ec1) (go ec2)
  | EIf ec1 ec2 ec3 => Pif _ _ _ (go ec1) (go ec2) (go ec3)
  | EComma ec1 ec2 => Pcomma _ _ (go ec1) (go ec2)
  | ECast _ ec => Pcast _ _ (go ec)
  | EField ec _ => Pfield _ _ (go ec)
  end.
End cexpr_ind.

Section properties.
Context `{EnvSpec Ti}.
Implicit Types Γ : env Ti.
Implicit Types Γf : funtypes Ti.
Implicit Types o : index.
Implicit Types m : mem Ti.
Implicit Types e : expr Ti.
Implicit Types ce : cexpr Ti.
Implicit Types s : stmt Ti.
Implicit Types τ σ : type Ti.
Implicit Types τlr : lrtype Ti.

Arguments to_R _ _ : simpl never.
Hint Extern 0 (_ ⊢ _ : _) => typed_constructor.

Lemma to_R_typed Γ Γf m τs e e' τlr τ' :
  to_R (e,τlr) = (e',τ') → (Γ,Γf,m,τs) ⊢ e : τlr → (Γ,Γf,m,τs) ⊢ e' : inr τ'.
Proof.
  unfold to_R; intros; destruct τlr as [τl|τr]; simplify_equality'; auto.
  destruct (maybe_TArray τl) as [[τ n]|] eqn:Hτ; simplify_equality'.
  { destruct τl; simplify_equality'. typed_constructor; eauto. }
  by typed_constructor.
Qed.
Lemma to_expr_typed Γ Γf m τs ce e τlr :
  ✓ Γ → ✓{Γ} m → to_expr Γ Γf m τs ce = Some (e,τlr) → (Γ,Γf,m,τs) ⊢ e : τlr.
Proof.
  intros ??. assert (∀ ces eτlrs,
     Forall (λ ce, ∀ e τlr,
       to_expr Γ Γf m τs ce = Some (e,τlr) → (Γ,Γf,m,τs) ⊢ e : τlr) ces →
     mapM (to_expr Γ Γf m τs) ces = Some eτlrs →
     (Γ,Γf,m,τs) ⊢* fst <$> to_R <$> eτlrs :* inr <$> snd <$> to_R <$> eτlrs).
  { intros ces eτlrs. rewrite mapM_Some. induction 2 as [|? [??]];
      decompose_Forall_hyps'; eauto using to_R_typed, surjective_pairing. }
  revert e τlr. induction ce using @cexpr_ind_alt; intros;
    repeat match goal with
    | _ => progress case_match
    | _ : maybe_inl ?τlr = Some _ |- _ => is_var τlr; destruct τlr
    | _ : maybe_TBase ?τ = Some _ |- _ => is_var τ; destruct τ
    | _ : maybe_TPtr ?τb = Some _ |- _ => is_var τb; destruct τb
    | _ : maybe_TCompound ?τ = Some _ |- _ => is_var τ; destruct τ
    | H: assign_type_of _ _ _ = Some _ |- _ => apply assign_type_of_correct in H
    | H: unop_type_of _ _ = Some _ |- _ => apply unop_type_of_correct in H
    | H: binop_type_of _ _ _ = Some _ |- _ => apply binop_type_of_correct in H
    | _ => progress (simplify_option_equality by fail)
    | x : (_ * _)%type |- _ => destruct x
    end; typed_constructor; eauto using to_R_typed,
      index_typed_valid, index_typed_representable,
      addr_top_typed, addr_top_strict.
Qed.
Lemma to_stmt_typed Γ Γf m τs Ls mLcLb cs s cmτ :
  ✓ Γ → ✓{Γ} m → to_stmt Γ Γf m τs Ls mLcLb cs = Some (s,cmτ) →
  (Γ,Γf,m,τs) ⊢ s : cmτ.
Proof.
  intros ??. revert s cmτ τs Ls mLcLb. induction cs; intros;
    repeat match goal with
    | _ => case_match
    | _ : maybe_TBase ?τ = Some _ |- _ => is_var τ; destruct τ
    | _ => progress (simplify_option_equality by fail)
    | x : (_ * _)%type |- _ => destruct x
    end; repeat typed_constructor;
    eauto using to_R_typed, to_expr_typed, rettype_union_l; naive_solver.
Qed.
Lemma to_mem_typed Γ τmes o m m' :
  ✓ Γ → to_mem Γ τmes o m = Some m' → ✓{Γ} m → 
  (∀ o', (o ≤ o')%N → mem_allocable o' m) → ✓{Γ} m'.
Proof.
  intros ?. revert m o m'. induction τmes as [|[τ [ce|]] τmes IH];
    intros m o m' ???; simplify_equality'; auto.
  * destruct (to_expr Γ ∅ m [] ce) as [[e τlr]|] eqn:?; simplify_equality'.
    destruct (to_R (e, τlr)) as [e' τ'] eqn:?.
    repeat case_option_guard; simplify_equality'.
    destruct (⟦ e' ⟧ Γ ∅ [] m) as [[?|v]|] eqn:?; simplify_equality'.
    assert ((Γ,m) ⊢ inr v : inr τ'); [|typed_inversion_all].
    { eapply expr_eval_typed; eauto using to_R_typed, to_expr_typed.
      by intros ?; simplify_map_equality'. }
    eapply IH; eauto using mem_alloc_val_valid.
    intros; eapply mem_alloc_val_allocable. eauto with lia. intros ->; lia.
  * repeat case_option_guard; simplify_equality'.
    eapply IH; eauto using mem_alloc_val_valid, val_0_typed.
    intros; eapply mem_alloc_val_allocable. eauto with lia. intros ->; lia.
Qed.
Lemma to_funs_typed Γ m Γfuns Γacc Γres :
  ✓ Γ → ✓{Γ} m → to_funs Γ m Γfuns Γacc = Some Γres →
  (Γ,m) ⊢ snd <$> Γacc : fst <$> Γacc → (Γ,m) ⊢ snd <$> Γres : fst <$> Γres.
Proof.
  intros ??. revert Γres Γacc. induction Γfuns as [|[[[f τs] τ] cs] Γfuns IH];
    intros Γres Γacc ??; simplify_equality'; auto.
  repeat case_option_guard; simplify_equality'.
  destruct (to_stmt _ _ _ _ _ _ _) as [[s mτ]|] eqn:?; simplify_equality'.
  repeat case_option_guard; simplify_equality'.
  eapply IH; eauto. rewrite !fmap_insert; simpl; typed_constructor; eauto.
  * by rewrite lookup_fmap; simplify_option_equality.
  * eauto using to_stmt_typed.
Qed.
Lemma to_envs_typed Θ Γ Γf δ m :
  to_envs Θ = Some (Γ,Γf,δ,m) → ✓ Γ ∧ (Γ,m) ⊢ δ : Γf ∧ ✓{Γ} m.
Proof.
  unfold to_envs; intros; simplify_option_equality.
  assert (✓ (map_of_list (c_env Θ))) by eauto using env_valid_of_list.
  assert (✓{map_of_list (c_env Θ)} m)
    by eauto using to_mem_typed, cmap_empty_valid, mem_empty_allocable.
  split_ands; auto; eapply to_funs_typed; eauto.
  rewrite !fmap_empty. by typed_constructor.
Qed.
End properties.
