(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Import type_system expression_eval.
Local Open Scope expr_scope.
Local Open Scope ctype_scope.

Inductive cexpr (Ti : Set) : Set :=
  | EVar : N → cexpr Ti
  | EConst : int_type Ti → Z → cexpr Ti
  | ESizeOf : cexpr Ti → cexpr Ti
  | ESizeOfType : type Ti → cexpr Ti
  | EAddrOf : cexpr Ti → cexpr Ti
  | EDeref : cexpr Ti → cexpr Ti
  | EAssign : assign → cexpr Ti → cexpr Ti → cexpr Ti
  | ECall : N → list (cexpr Ti) → cexpr Ti
  | EAlloc : type Ti → cexpr Ti
  | EFree : cexpr Ti → cexpr Ti
  | EUnOp : unop → cexpr Ti → cexpr Ti
  | EBinOp : binop → cexpr Ti → cexpr Ti → cexpr Ti
  | EIf : cexpr Ti → cexpr Ti → cexpr Ti → cexpr Ti
  | EComma : cexpr Ti → cexpr Ti → cexpr Ti
  | EAnd : cexpr Ti → cexpr Ti → cexpr Ti
  | EOr : cexpr Ti → cexpr Ti → cexpr Ti
  | ECast : type Ti → cexpr Ti → cexpr Ti
  | EField : cexpr Ti → nat → cexpr Ti.
Arguments EVar {_} _.
Arguments EConst {_} _ _.
Arguments ESizeOf {_} _.
Arguments ESizeOfType {_} _.
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
Arguments EAnd {_} _ _.
Arguments EOr {_} _ _.
Arguments ECast {_} _ _.
Arguments EField {_} _ _.

Inductive cstmt (Ti : Set) : Set :=
  | SDo : cexpr Ti → cstmt Ti
  | SSkip : cstmt Ti
  | SGoto : labelname → cstmt Ti
  | SBreak : cstmt Ti
  | SContinue : cstmt Ti
  | SReturn : option (cexpr Ti) → cstmt Ti
  | SBlock : N → type Ti → option (cexpr Ti) → cstmt Ti → cstmt Ti
  | SStatic : N → type Ti → option (cexpr Ti) → cstmt Ti → cstmt Ti
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
Arguments SBlock {_} _ _ _ _.
Arguments SStatic {_} _ _ _ _.
Arguments SComp {_} _ _.
Arguments SLabel {_} _ _.
Arguments SWhile {_} _ _.
Arguments SIf {_} _ _ _.

Inductive decl (Ti : Set) : Set :=
  | CompoundDecl : list (type Ti) → decl Ti
  | GlobDecl : type Ti → option (cexpr Ti) → decl Ti
  | FunDecl : list (N * type Ti) → type Ti → cstmt Ti → decl Ti.
Arguments CompoundDecl {_} _.
Arguments GlobDecl {_} _ _.
Arguments FunDecl {_} _ _ _.

Notation var_env Ti := (list (N * (index + type Ti))).

Section frontend.
Context `{IntEnv Ti, PtrEnv Ti}.

Fixpoint lookup_var (m : mem Ti) (x : N)
    (i : nat) (xs : var_env Ti) : option (expr Ti * type Ti) :=
  match xs with
  | [] => None
  | (y,inl o) :: xs =>
     if decide (x = y)
     then τ ← type_check m o; Some (% (addr_top o τ), τ)
     else lookup_var m x i xs
  | (y,inr τ) :: xs =>
     if decide (x = y) then Some (var{τ} i, τ)
     else lookup_var m x (S i) xs
  end.
Definition to_R (eτlr : expr Ti * lrtype Ti) : expr Ti * type Ti :=
  match eτlr with
  | (e, inl τ) =>
    match maybe_TArray τ with
    | Some (τ',_) => (& (elt e), τ'.*) | None => (load e, τ)
    end
  | (e, inr τ) => (e,τ)
  end%E.
Definition to_expr (Γ : env Ti) (Γf : funtypes Ti) (m : mem Ti)
    (xs : var_env Ti) : cexpr Ti → option (expr Ti * lrtype Ti) :=
  fix go ce :=
  match ce with
  | EVar x =>
     '(e,τ) ← lookup_var m x 0 xs; Some (e, inl τ)
  | EConst τi x =>
     guard (int_typed x τi);
     Some (# (intV{τi} x), inr (intT τi))
  | ESizeOf ce =>
     '(_,τlr) ← go ce;
     let sz := size_of Γ (lrtype_type τlr) in
     guard (int_typed sz sptrT);
     Some (# (intV{sptrT} sz), inr sptrT)
  | ESizeOfType τ =>
     let sz := size_of Γ τ in
     guard (int_typed sz sptrT);
     Some (# (intV{sptrT} sz), inr sptrT)
  | EDeref ce =>
     '(e,τ) ← to_R <$> go ce;
     τp ← maybe_TBase τ ≫= maybe_TPtr;
     Some (.* e, inl τp)
  | EAddrOf ce =>
     '(e,τlr) ← go ce;
     τ ← maybe_inl τlr;
     Some (& e, inr (τ.*))
  | EAssign ass ce1 ce2 =>
     '(e1,τlr1) ← go ce1;
     τ1 ← maybe_inl τlr1;
     '(e2,τ2) ← to_R <$> go ce2;
     σ ← assign_type_of Γ τ1 τ2 ass;
     Some (e1 ::={ass} e2, inr σ)
  | ECall f ces =>
     '(τs,σ) ← Γf !! (f : funname);
     τses ← fmap to_R <$> mapM go ces;
     guard (Forall2 (cast_typed Γ) (snd <$> τses) τs);
     Some (call f @ cast{τs}* (fst <$> τses), inr σ)
  | EAlloc τ =>
     guard (✓{Γ} τ);
     guard (int_typed (size_of Γ τ) sptrT);
     Some (& (alloc τ), inr (τ.*))
  | EFree ce =>
     '(e,τ) ← to_R <$> go ce; _ ← maybe_TBase τ ≫= maybe_TPtr;
     Some (free (.* e), inr voidT)
  | EUnOp op ce =>
     '(e,τ) ← to_R <$> go ce;
     σ ← unop_type_of op τ;
     Some (@{op} e, inr σ)
  | EBinOp op ce1 ce2 =>
     '(e1,τ1) ← to_R <$> go ce1;
     '(e2,τ2) ← to_R <$> go ce2;
     σ ← binop_type_of op τ1 τ2;
     Some (e1 @{op} e2, inr σ)
  | EIf ce1 ce2 ce3 =>
     '(e1,τ1) ← to_R <$> go ce1; _ ← maybe_TBase τ1;
     '(e2,τ2) ← to_R <$> go ce2;
     '(e3,τ3) ← to_R <$> go ce3;
     guard (τ2 = τ3);
     Some (if{e1} e2 else e3, inr τ3)
  | EComma ce1 ce2 =>
     '(e1,τ1) ← to_R <$> go ce1;
     '(e2,τ2) ← to_R <$> go ce2;
     Some (e1,, e2, inr τ2)
  | EAnd ce1 ce2 =>
     '(e1,τ1) ← to_R <$> go ce1; _ ← maybe_TBase τ1;
     '(e2,τ2) ← to_R <$> go ce2; _ ← maybe_TBase τ2;
     Some (if{e1} if{e2} #(intV{sintT} 1) else #(intV{sintT} 0)
           else #(intV{sintT} 0), inr sintT)
  | EOr ce1 ce2 =>
     '(e1,τ1) ← to_R <$> go ce1; _ ← maybe_TBase τ1;
     '(e2,τ2) ← to_R <$> go ce2; _ ← maybe_TBase τ2;
     Some (if{e1} #(intV{sintT} 0)
           else (if{e2} #(intV{sintT} 1) else #(intV{sintT} 0)), inr sintT)
  | ECast σ ce =>
     '(e,τ) ← to_R <$> go ce;
     guard (cast_typed Γ τ σ);
     Some (cast{σ} e, inr σ)
  | EField ce i =>
     '(e,τrl) ← go ce;
     τ ← maybe_inl τrl;
     '(c,s) ← maybe_TCompound τ;
     σs ← Γ !! s;
     σ ← σs !! i;
     Some (e .> i, inl σ)
  end%E.

Global Instance cstmt_labels : Labels (cstmt Ti) :=
  fix go cs := let _ : Labels _ := @go in
  match cs with
  | SBlock _ _ _ cs | SStatic _ _ _ cs => labels cs
  | SComp cs1 cs2 => labels cs1 ∪ labels cs2
  | SLabel l cs => {[ l ]} ∪ labels cs
  | SWhile _ cs => labels cs
  | SIf _ cs1 cs2 => labels cs1 ∪ labels cs2
  | _ => ∅
  end.
Fixpoint cstmt_has_continue (cs : cstmt Ti) : bool :=
  match cs with
  | SContinue => true
  | SBlock _ _ _ cs | SStatic _ _ _ cs => cstmt_has_continue cs
  | SComp cs1 cs2 => cstmt_has_continue cs1 || cstmt_has_continue cs2
  | SLabel _ cs => cstmt_has_continue cs
  | SIf _ cs1 cs2 => cstmt_has_continue cs1 || cstmt_has_continue cs2
  | _ => false
  end.
Fixpoint cstmt_has_break (cs : cstmt Ti) : bool :=
  match cs with
  | SBreak => true
  | SBlock _ _ _ cs | SStatic _ _ _ cs => cstmt_has_break cs
  | SComp cs1 cs2 => cstmt_has_break cs1 || cstmt_has_break cs2
  | SLabel _ cs => cstmt_has_break cs
  | SIf _ cs1 cs2 => cstmt_has_break cs1 || cstmt_has_break cs2
  | _ => false
  end.

Definition to_while (e : expr Ti) (con bre : bool) (Ls : labelset) :
    (labelset * option labelname * option labelname * (stmt Ti → stmt Ti)) :=
  match con, bre with
  | true, true =>
     let Lc := fresh Ls in let Lb := fresh ({[ Lc ]} ∪ Ls) in
     ({[ Lc ; Lb ]} ∪ Ls, Some Lc, Some Lb,
      λ s, while{e} (s ;; label Lc) ;; label Lb)
  | true, false =>
     let Lc := fresh Ls in
     ({[ Lc ]} ∪ Ls, Some Lc, None, λ s, while{e} (s ;; label Lc))
  | false, true =>
     let Lb := fresh Ls in
     ({[ Lb ]} ∪ Ls, None, Some Lb, λ s, while{e} s ;; label Lb)
  | false, false =>
     (Ls, None, None, λ s, while{e} s)
  end.
Definition alloc_global (Γ : env Ti) (m : mem Ti) (xs : var_env Ti) (x : N)
    (τ : type Ti) (mce : option (cexpr Ti)) : option (mem Ti * var_env Ti) :=
  match mce with
  | Some ce =>
     '(e,τ') ← to_R <$> to_expr Γ ∅ m xs ce;
     guard (τ = τ');
     guard (int_typed (size_of Γ τ) sptrT);
     v ← ⟦ e ⟧ Γ ∅ [] m ≫= maybe_inr;
     let o := fresh (dom _ m) in
     Some (<[addr_top o τ:=v]{Γ}>(mem_alloc Γ o false τ m), (x,inl o) :: xs)
  | None =>
     guard (✓{Γ} τ);
     guard (int_typed (size_of Γ τ) sptrT);
     let o := fresh (dom _ m) in
     Some (<[addr_top o τ:=val_0 Γ τ]{Γ}>(mem_alloc Γ o false τ m),
           (x,inl o) :: xs)
  end.

Definition to_stmt (Γ : env Ti) (Γf : funtypes Ti) :
    mem Ti → var_env Ti → labelset → option labelname → option labelname →
    cstmt Ti → option (mem Ti * stmt Ti * rettype Ti) :=
  fix go m xs Ls mLc mLb cs {struct cs} :=
  match cs with
  | SDo ce =>
     '(e,_) ← to_R <$> to_expr Γ Γf m xs ce;
     Some (m, !e, (false, None))
  | SSkip => Some (m, skip, (false, None))
  | SGoto l => Some (m, goto l, (true, None))
  | SContinue => Lc ← mLc; Some (m, goto Lc, (true, None))
  | SBreak => Lb ← mLb; Some (m, goto Lb, (true, None))
  | SReturn (Some ce) =>
     '(e,τ) ← to_R <$> to_expr Γ Γf m xs ce;
     Some (m, ret e, (true, Some τ))
  | SReturn None => Some (m, ret (#voidV), (true, Some voidT))
  | SBlock x τ None cs =>
     guard (✓{Γ} τ);
     guard (int_typed (size_of Γ τ) sptrT);
     '(m,s,cmσ) ← go m ((x,inr τ) :: xs) Ls mLc mLb cs;
     Some (m, blk{τ} s, cmσ)
  | SBlock x τ (Some ce) cs =>
     guard (✓{Γ} τ);
     guard (int_typed (size_of Γ τ) sptrT);
     '(e,τ') ← to_R <$> to_expr Γ ∅ m ((x,inr τ) :: xs) ce;
     guard (τ = τ');
     '(m,s,cmσ) ← go m ((x,inr τ) :: xs) Ls mLc mLb cs;
     Some (m, blk{τ} (var{τ} 0 ::= e ;; s), cmσ)
  | SStatic x τ mce cs =>
     '(m,xs) ← alloc_global Γ m xs x τ mce;
     go m xs Ls mLc mLb cs
  | SComp cs1 cs2 =>
     '(m,s1,cmσ1) ← go m xs Ls mLc mLb cs1;
     '(m,s2,cmσ2) ← go m xs Ls mLc mLb cs2;
     mσ ← rettype_union (cmσ1.2) (cmσ2.2);
     Some (m, s1 ;; s2, (cmσ2.1, mσ))
  | SLabel l cs =>
     '(m,s,cmσ) ← go m xs Ls mLc mLb cs; Some (m, l :; s, cmσ)
  | SWhile ce cs =>
     '(e,τ) ← to_R <$> to_expr Γ Γf m xs ce; _ ← maybe_TBase τ;
     let '(Ls,mLc,mLb,Fs) :=
       to_while e (cstmt_has_continue cs) (cstmt_has_break cs) Ls in
     '(m,s,cmσ) ← go m xs Ls mLc mLb cs;
     Some (m, Fs s, (false, cmσ.2))
  | SIf ce cs1 cs2 =>
     '(e,τ) ← to_R <$> to_expr Γ Γf m xs ce; _ ← maybe_TBase τ;
     '(m,s1,cmσ1) ← go m xs Ls mLc mLb cs1;
     '(m,s2,cmσ2) ← go m xs Ls mLc mLb cs2;
     mσ ← rettype_union (cmσ1.2) (cmσ2.2);
     Some (m, if{e} s1 else s2, (cmσ1.1 && cmσ2.1, mσ))%S
  end%T.

Fixpoint to_envs (Θ : list (N * decl Ti)) :
    option (env Ti * funtypes Ti * funenv Ti * mem Ti * var_env Ti) :=
  match Θ with
  | [] => Some (∅,∅,∅,∅,[])
  | (s,CompoundDecl τs) :: Θ =>
     '(Γ,Γf,δ,m,xs) ← to_envs Θ;
     let s : tag := s in
     guard (Γ !! s = None);
     guard (✓{Γ}* τs);
     guard (1 < length τs);
     Some (<[s:=τs]>Γ, Γf, δ, m, xs)
  | (x,GlobDecl τ me) :: Θ =>
     (* todo: we just shadow, that is wrong *)
     '(Γ,Γf,δ,m,xs) ← to_envs Θ;
     '(m,xs) ← alloc_global Γ m xs x τ me;
      Some (Γ, Γf, δ, m, xs)
  | (f,FunDecl ys σ cs) :: Θ =>
     (* todo: functions and globals cannot have the same name *)
     '(Γ,Γf,δ,m,xs) ← to_envs Θ;
     let f : funname := f in
     guard (NoDup (fst <$> ys));
     let τs := snd <$> ys in
     guard (Γf !! f = None);
     guard (✓{Γ}* τs);
     guard (Forall (λ τ, int_typed (size_of Γ τ) sptrT) τs);
     let xs' := (prod_map id inr <$> ys) ++ xs in
     '(m,s,cmσ) ← to_stmt Γ Γf m xs' (labels cs) None None cs;
     guard (rettype_match cmσ σ);
     Some(Γ, <[f:=(τs,σ)]>Γf, <[f:=s]>δ, m, xs)
  end.
End frontend.

Section cexpr_ind.
Context {Ti : Set} (P : cexpr Ti → Prop).
Context (Pvar : ∀ x, P (EVar x)).
Context (Pconst : ∀ τi x, P (EConst τi x)).
Context (Psizeof : ∀ ce, P ce → P (ESizeOf ce)).
Context (Psizeoftype : ∀ τ, P (ESizeOfType τ)).
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
Context (Pand : ∀ ce1 ce2, P ce1 → P ce2 → P (EAnd ce1 ce2)).
Context (Por : ∀ ce1 ce2, P ce1 → P ce2 → P (EOr ce1 ce2)).
Context (Pcast : ∀ τ ce, P ce → P (ECast τ ce)).
Context (Pfield : ∀ ce i, P ce → P (EField ce i)).

Definition cexpr_ind_alt : ∀ e, P e :=
  fix go e :=
  match e return P e with
  | EVar _ => Pvar _
  | EConst _ _ => Pconst _ _
  | ESizeOf ce => Psizeof _ (go ce)
  | ESizeOfType _ => Psizeoftype _
  | EAddrOf ce => Paddrof _ (go ce)
  | EDeref ce => Pderef _ (go ce)
  | EAssign _ ce1 ce2 => Passign _ _ _ (go ce1) (go ce2)
  | ECall f ces => Pcall _ ces $ list_ind (Forall P)
      (Forall_nil_2 _) (λ ce _, Forall_cons_2 _ _ _ (go ce)) ces
  | EAlloc _ => Palloc _
  | EFree ce => Pfree _ (go ce)
  | EUnOp _ ce => Punop _ _ (go ce)
  | EBinOp _ ce1 ce2 => Pbinop _ _ _ (go ce1) (go ce2)
  | EIf ce1 ce2 ce3 => Pif _ _ _ (go ce1) (go ce2) (go ce3)
  | EComma ce1 ce2 => Pcomma _ _ (go ce1) (go ce2)
  | EAnd ce1 ce2 => Pand _ _ (go ce1) (go ce2)
  | EOr ce1 ce2 => Por _ _ (go ce1) (go ce2)
  | ECast _ ce => Pcast _ _ (go ce)
  | EField ce _ => Pfield _ _ (go ce)
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
Hint Extern 1 (int_typed _ _) => by apply int_typed_small.

Fixpoint var_env_stack_types (xs : var_env Ti) : list (type Ti) :=
  match xs with
  | [] => []
  | (_,inr τ) :: xs => τ :: var_env_stack_types xs
  | (_,inl _) :: xs => var_env_stack_types xs
  end.
Lemma var_env_stack_types_app xs1 xs2 :
  var_env_stack_types (xs1 ++ xs2)
  = var_env_stack_types xs1 ++ var_env_stack_types xs2.
Proof. induction xs1 as [|[?[?|?]] ??]; f_equal'; auto. Qed.
Lemma var_env_stack_types_snd (ys : list (N * type Ti)) :
  var_env_stack_types (prod_map id inr <$> ys) = snd <$> ys.
Proof. induction ys; f_equal'; auto. Qed.

Lemma to_R_typed Γ Γf m τs e e' τlr τ' :
  to_R (e,τlr) = (e',τ') → (Γ,Γf,m,τs) ⊢ e : τlr → (Γ,Γf,m,τs) ⊢ e' : inr τ'.
Proof.
  unfold to_R; intros; destruct τlr as [τl|τr]; simplify_equality'; auto.
  destruct (maybe_TArray τl) as [[τ n]|] eqn:Hτ; simplify_equality'.
  { destruct τl; simplify_equality'. typed_constructor; eauto. }
  by typed_constructor.
Qed.
Lemma var_lookup_typed Γ Γf m xs x e τ :
  ✓ Γ → ✓{Γ} m → lookup_var m x 0 xs = Some (e,τ) →
  (Γ,Γf,m,var_env_stack_types xs) ⊢ e : inl τ.
Proof.
  intros ??. cut (∀ τs', lookup_var m x (length τs') xs = Some (e,τ) →
    (Γ,Γf,m,τs' ++ var_env_stack_types xs) ⊢ e : inl τ).
  { intros help. apply (help []). }
  induction xs as [|[x' [o|τ']] xs IH];
    intros τs' ?; simplify_option_equality; eauto 2.
  * typed_constructor; eauto using addr_top_typed, addr_top_strict,
      index_typed_valid, index_typed_representable.
  * typed_constructor. by rewrite list_lookup_middle.
  * rewrite cons_middle, (associative_L (++)). apply (IH (τs' ++ [τ'])).
    rewrite app_length; simpl. by rewrite Nat.add_comm.
Qed.
Lemma to_expr_typed Γ Γf m xs ce e τlr :
  ✓ Γ → ✓{Γ} m → to_expr Γ Γf m xs ce = Some (e,τlr) →
  (Γ,Γf,m,var_env_stack_types xs) ⊢ e : τlr.
Proof.
  intros ??. assert (∀ ces eτlrs,
     Forall (λ ce, ∀ e τlr, to_expr Γ Γf m xs ce = Some (e,τlr) →
       (Γ,Γf,m,var_env_stack_types xs) ⊢ e : τlr) ces →
     mapM (to_expr Γ Γf m xs) ces = Some eτlrs →
     (Γ,Γf,m,var_env_stack_types xs) ⊢*
       fst <$> to_R <$> eτlrs :* inr <$> snd <$> to_R <$> eτlrs).
  { intros ces eτlrs. rewrite mapM_Some. induction 2 as [|? [??]];
      decompose_Forall_hyps'; eauto using to_R_typed, surjective_pairing. }
  revert e τlr. induction ce using @cexpr_ind_alt; intros;
    repeat match goal with
    | _ => progress case_match
    | _ : maybe_inl ?τlr = Some _ |- _ => is_var τlr; destruct τlr
    | _ : maybe_TBase ?τ = Some _ |- _ => is_var τ; destruct τ
    | _ : maybe_TPtr ?τb = Some _ |- _ => is_var τb; destruct τb
    | _ : maybe_TCompound ?τ = Some _ |- _ => is_var τ; destruct τ
    | H: assign_type_of _ _ _ _ = Some _ |- _ =>
       apply assign_type_of_correct in H
    | H: unop_type_of _ _ = Some _ |- _ => apply unop_type_of_correct in H
    | H: binop_type_of _ _ _ = Some _ |- _ => apply binop_type_of_correct in H
    | _ => progress (simplify_option_equality by fail)
    | x : (_ * _)%type |- _ => destruct x
    end; repeat typed_constructor;
    eauto using to_R_typed, var_lookup_typed, ECasts_typed.
Qed.
Lemma alloc_global_typed Γ m xs x τ mce m' xs' :
  ✓ Γ → alloc_global Γ m xs x τ mce = Some (m',xs') →
  ✓{Γ} m → ✓{Γ} m' ∧ (∀ o σ, m ⊢ o : σ → m' ⊢ o : σ)
    ∧ var_env_stack_types xs = var_env_stack_types xs'.
Proof.
  assert (mem_allocable (fresh (dom indexset m)) m).
  { eapply mem_allocable_alt, is_fresh. }
  destruct mce as [ce|]; intros; simplify_equality'.
  * destruct (to_expr Γ ∅ m xs ce) as [[e τlr]|] eqn:?; simplify_equality'.
    destruct (to_R (e, τlr)) as [e' τ'] eqn:?.
    repeat case_option_guard; simplify_equality'.
    destruct (⟦ e' ⟧ Γ ∅ [] m) as [[?|v]|] eqn:?; simplify_equality'.
    assert ((Γ,m) ⊢ inr v : inr τ'); [|typed_inversion_all].
    { eapply (expr_eval_typed_aux Γ ∅ [] (var_env_stack_types xs) ∅);
        eauto using to_R_typed, to_expr_typed, prefix_of_nil.
      by intros ?; simpl_map. }
    split; eauto using mem_alloc_val_valid, index_typed_alloc_val.
  * repeat case_option_guard; simplify_equality'.
    split; eauto using mem_alloc_val_valid, index_typed_alloc_val, val_0_typed.
Qed.
Lemma to_while_typed Γ Γf m τs e con bre Ls Ls' mLc mLb Fs s τb c mσ:
  to_while e con bre Ls = (Ls',mLc,mLb,Fs) →
  (Γ,Γf,m,τs) ⊢ e : inr (baseT τb) →
  (Γ,Γf,m,τs) ⊢ s : (c,mσ) → (Γ,Γf,m,τs) ⊢ Fs s : (false,mσ).
Proof.
  destruct con, bre; intros; simplify_equality';
    repeat typed_constructor; eauto using rettype_union_l.
Qed.
Lemma to_stmt_typed Γ Γf m xs Ls mLc mLb cs m' s cmτ :
  ✓ Γ → ✓{Γ} m → to_stmt Γ Γf m xs Ls mLc mLb cs = Some (m',s,cmτ) →
  (Γ,Γf,m',var_env_stack_types xs) ⊢ s : cmτ
  ∧ ✓{Γ} m' ∧ (∀ o σ, m ⊢ o : σ → m' ⊢ o : σ).
Proof.
  intros ?. revert m m' s cmτ xs Ls mLc mLb. induction cs; intros;
    repeat match goal with
    | _ => case_match
    | _ : maybe_TBase ?τ = Some _ |- _ => is_var τ; destruct τ
    | _ => progress (simplify_option_equality by fail)
    | x : (_ * _)%type |- _ => destruct x
    | IH : ∀ _ _ _ _ _ _ _ _, ✓{Γ} _ → to_stmt _ _ _ _ _ _ _ ?cs = Some _ → _,
      H : to_stmt _ _ _ _ _ _ _ ?cs = Some _ |- _ =>
       destruct (λ Hm, IH _ _ _ _ _ _ _ _ Hm H) as (?&?&?); clear IH; [by auto|]
    | H : to_expr _ _ _ _ _ = Some _ |- _ =>
       apply to_expr_typed in H; [|by auto|by auto];
       eapply to_R_typed in H; [|by eauto]
    | H : alloc_global _ _ _ _ _ _ = Some _ |- _ =>
       apply alloc_global_typed in H; [|by auto|by auto]; destruct H as (?&?&->)
    end; try solve [split_ands; eauto using to_R_typed, to_expr_typed].
  * split_ands; eauto. eapply SBlock_typed; eauto.
    repeat typed_constructor; eauto using expr_typed_weaken, subseteq_empty.
    constructor. by apply cast_typed_self.
  * split_ands; eauto using stmt_typed_weaken.
  * split_ands; eauto using to_while_typed, expr_typed_weaken.
  * split_ands; eauto using stmt_typed_weaken, expr_typed_weaken.
Qed.
Lemma to_envs_typed Θ Γ Γf δ m xs :
  to_envs Θ = Some (Γ,Γf,δ,m,xs) →
  ✓ Γ ∧ (Γ,m) ⊢ δ : Γf ∧ ✓{Γ} m ∧ var_env_stack_types xs = [].
Proof.
  revert Γ Γf δ m xs. induction Θ as [|[x [τs|τ mce|ys σ cs]] Θ IH];
    intros Γ Γf δ m xs ?; simplify_equality'.
  * eauto using env_empty_valid, cmap_empty_valid.
  * destruct (to_envs Θ) as [[[[[Γ2 ?] ?] ?] ?]|]; simplify_option_equality.
    destruct (IH Γ2 Γf δ m xs) as (?&?&?&?); eauto. split_ands; auto.
    + by constructor.
    + eapply funenv_typed_weaken; eauto using insert_subseteq.
    + eapply cmap_valid_weaken; eauto using insert_subseteq.
  * destruct (to_envs Θ) as [[[[[Γ2 Γf2] δ2] m2] xs2]|]; simplify_equality'.
    destruct (alloc_global _ _ _ _ _ _) as [[??]|] eqn:?; simplify_equality'.
    destruct (IH Γ Γf δ m2 xs2) as (?&?&?&?); eauto.
    destruct (alloc_global_typed Γ m2 xs2 x τ mce m xs)
      as (?&?&<-); eauto using funenv_typed_weaken.
  * destruct (to_envs Θ) as [[[[[Γ2 Γf2] δ2] m2] xs2]|]; simplify_equality'.
    repeat case_option_guard; simplify_equality'.
    destruct (to_stmt _ _ _ _ _ _ _ _)
      as [[[m3 s] cmσ]|] eqn:?; simplify_option_equality.
    destruct (IH Γ Γf2 δ2 m2 xs) as (?&?&?&Hxs); eauto.
    destruct (to_stmt_typed Γ Γf2 m2 ((prod_map id inr <$> ys) ++ xs)
      (labels cs) None None cs m s cmσ) as (Hs&?&?); auto.
    rewrite var_env_stack_types_app,
      var_env_stack_types_snd, Hxs, (right_id_L [] (++)) in Hs.
    split_ands; eauto using funenv_typed_weaken.
Qed.
End properties.
