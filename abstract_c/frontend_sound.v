(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Import String stringmap tactics.
Require Export frontend.

Local Open Scope string_scope.
Local Open Scope expr_scope.
Local Open Scope ctype_scope.
Local Open Scope list_scope.

Local Notation M := (error (frontend_state _) string).

Section cexpr_ind.
Context (P : cexpr → Prop) (Q : cinit → Prop) (R : ctype → Prop).
Context (Pvar : ∀ x, P (CEVar x)).
Context (Pconst : ∀ τi x, P (CEConst τi x)).
Context (Pconststring : ∀ zs, P (CEConstString zs)).
Context (Plimit : ∀ cτ li, R cτ → P (CELimit cτ li)).
Context (Paddrof : ∀ ce, P ce → P (CEAddrOf ce)).
Context (Pderef : ∀ ce, P ce → P (CEDeref ce)).
Context (Passign : ∀ ass ce1 ce2, P ce1 → P ce2 → P (CEAssign ass ce1 ce2)).
Context (Pcall : ∀ ce ces, P ce → Forall P ces → P (CECall ce ces)).
Context (Pabort : P CEAbort).
Context (Palloc : ∀ cτ ce, R cτ → P ce → P (CEAlloc cτ ce)).
Context (Pfree : ∀ ce, P ce → P (CEFree ce)).
Context (Punop : ∀ op ce, P ce → P (CEUnOp op ce)).
Context (Pbinop : ∀ op ce1 ce2, P ce1 → P ce2 → P (CEBinOp op ce1 ce2)).
Context (Pif : ∀ ce1 ce2 ce3, P ce1 → P ce2 → P ce3 → P (CEIf ce1 ce2 ce3)).
Context (Pcomma : ∀ ce1 ce2, P ce1 → P ce2 → P (CEComma ce1 ce2)).
Context (Pand : ∀ ce1 ce2, P ce1 → P ce2 → P (CEAnd ce1 ce2)).
Context (Por : ∀ ce1 ce2, P ce1 → P ce2 → P (CEOr ce1 ce2)).
Context (Pcast : ∀ cτ ci, R cτ → Q ci → P (CECast cτ ci)).
Context (Pfield : ∀ ce i, P ce → P (CEField ce i)).
Context (Qsingle : ∀ ce, P ce → Q (CSingleInit ce)).
Context (Qcompound : ∀ inits,
  Forall (λ i, Forall (sum_rect _ (λ _, True) P) (i.1) ∧ Q (i.2)) inits →
  Q (CCompoundInit inits)).
Context (Rvoid : R CTVoid).
Context (Rdef : ∀ x, R (CTDef x)).
Context (Renum : ∀ x, R (CTEnum x)).
Context (Rint : ∀ τi, R (CTInt τi)).
Context (Rptr : ∀ cτ, R cτ → R (CTPtr cτ)).
Context (Rarray : ∀ cτ ce, R cτ → P ce → R (CTArray cτ ce)).
Context (Rcompound : ∀ c x, R (CTCompound c x)).
Context (Rfun : ∀ csτs cτ, Forall (R ∘ snd) csτs → R cτ → R (CTFun csτs cτ)).
Context (Rtypeof : ∀ ce, P ce → R (CTTypeOf ce)).

Let help (cexpr_ind_alt : ∀ ce, P ce) (cinit_ind_alt : ∀ ci, Q ci)
    (inits : list (list (string + cexpr) * cinit)) :
  Forall (λ i, Forall (sum_rect _ (λ _, True) P) (i.1) ∧ Q (i.2)) inits.
Proof.
  induction inits as [|[xces ?]]; repeat constructor; auto.
  induction xces as [|[]]; constructor; simpl; auto.
Defined.
Fixpoint cexpr_ind_alt ce : P ce :=
  match ce return P ce with
  | CEVar _ => Pvar _
  | CEConst _ _ => Pconst _ _
  | CEConstString _ => Pconststring _
  | CELimit cτ li => Plimit _ _ (ctype_ind_alt cτ)
  | CEAddrOf ce => Paddrof _ (cexpr_ind_alt ce)
  | CEDeref ce => Pderef _ (cexpr_ind_alt ce)
  | CEAssign _ ce1 ce2 => Passign _ _ _ (cexpr_ind_alt ce1) (cexpr_ind_alt ce2)
  | CECall _ ces => Pcall _ ces (cexpr_ind_alt _) $ list_ind (Forall P)
      (Forall_nil_2 _) (λ ce _, Forall_cons_2 _ _ _ (cexpr_ind_alt ce)) ces
  | CEAbort => Pabort
  | CEAlloc cτ ce => Palloc _ _ (ctype_ind_alt cτ) (cexpr_ind_alt ce)
  | CEFree ce => Pfree _ (cexpr_ind_alt ce)
  | CEUnOp _ ce => Punop _ _ (cexpr_ind_alt ce)
  | CEBinOp _ ce1 ce2 => Pbinop _ _ _ (cexpr_ind_alt ce1) (cexpr_ind_alt ce2)
  | CEIf ce1 ce2 ce3 =>
     Pif _ _ _ (cexpr_ind_alt ce1) (cexpr_ind_alt ce2) (cexpr_ind_alt ce3)
  | CEComma ce1 ce2 => Pcomma _ _ (cexpr_ind_alt ce1) (cexpr_ind_alt ce2)
  | CEAnd ce1 ce2 => Pand _ _ (cexpr_ind_alt ce1) (cexpr_ind_alt ce2)
  | CEOr ce1 ce2 => Por _ _ (cexpr_ind_alt ce1) (cexpr_ind_alt ce2)
  | CECast cτ ci => Pcast _ _ (ctype_ind_alt cτ) (cinit_ind_alt ci)
  | CEField ce _ => Pfield _ _ (cexpr_ind_alt ce)
  end
with cinit_ind_alt ci : Q ci :=
  match ci with
  | CSingleInit ce => Qsingle _ (cexpr_ind_alt ce)
  | CCompoundInit inits => Qcompound _ (help cexpr_ind_alt cinit_ind_alt inits)
  end
with ctype_ind_alt cτ : R cτ :=
  match cτ with
  | CTVoid => Rvoid
  | CTDef _ => Rdef _
  | CTEnum _ => Renum _
  | CTInt _ => Rint _
  | CTPtr cτ => Rptr _ (ctype_ind_alt cτ)
  | CTArray cτ ce => Rarray _ _ (ctype_ind_alt cτ) (cexpr_ind_alt ce)
  | CTCompound _ _ => Rcompound _ _
  | CTFun csτs _ => Rfun csτs _ (list_ind (Forall (R ∘ snd)) (Forall_nil_2 _)
      (λ csτ _, Forall_cons_2 (R ∘ snd) _ _ (ctype_ind_alt (csτ.2))) csτs)
      (ctype_ind_alt _)
  | CTTypeOf ce => Rtypeof _ (cexpr_ind_alt ce)
  end.
Lemma cexpr_cinit_ctype_ind : (∀ ce, P ce) ∧  (∀ ci, Q ci) ∧ (∀ cτ, R cτ).
Proof. auto using cexpr_ind_alt, cinit_ind_alt, ctype_ind_alt. Qed.
End cexpr_ind.

Section properties.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types o : index.
Implicit Types m : mem K.
Implicit Types e : expr K.
Implicit Types ce : cexpr.
Implicit Types s : stmt K.
Implicit Types τi : int_type K.
Implicit Types τ σ : type K.
Implicit Types cτ : ctype.
Implicit Types τlr : lrtype K.
Implicit Types Δl : local_env K.

Arguments to_R _ _ _ _ : simpl never.
Arguments convert_ptrs _ _ _ : simpl never.
Hint Extern 0 (_ ⊢ _ : _) => typed_constructor: core.
Hint Extern 0 (_ ⊢ _ : _ ↣ _) => typed_constructor: core.
Hint Extern 1 (int_typed _ _) => by apply int_typed_small: core.
Hint Extern 10 (ptr_cast_typed _ _) => constructor: core.
Hint Extern 10 (cast_typed _ _) => constructor: core.
Hint Extern 10 (base_cast_typed _ _) => constructor: core.
Hint Extern 0 (assign_typed _ _ _) => constructor: core.
Hint Immediate lockset_empty_valid: core.
Hint Resolve memenv_subseteq_forward: core.
Hint Immediate rettype_union_l rettype_union_r: core.
Hint Resolve TBase_valid TVoid_valid TInt_valid TArray_valid TFun_ptr_valid: core.
Hint Resolve TPtr_valid TCompound_ptr_valid TCompound_valid TAny_ptr_valid: core.
Hint Resolve TBase_ptr_valid TArray_ptr_valid: core.
Hint Immediate type_complete_valid types_complete_valid: core.
Hint Immediate type_valid_ptr_type_valid: core.
Hint Resolve addr_top_typed addr_top_strict: core.
Hint Extern 10 (_ ⊢ _ : _ ↣ _) => typed_constructor; try lia: core.
Hint Resolve perm_full_valid perm_full_mapped: core.
Hint Extern 1 (@eq lockset _ _) =>
  by simpl; rewrite ?expr_locks_freeze, ?empty_union_L: core.
Hint Extern 0 (rettype_match _ _) => constructor: core.
Hint Immediate rettype_union_idempotent val_0_typed: core.
Arguments rettype_union_alt _ _ _ _ : simpl never.

Definition fun_stmt_valid (Γ : env K) (Δ : memenv K)
    (τs : list (type K)) (τ : type K) (ms : option (stmt K)) : Prop :=
  match ms with
  | Some s => ∃ cmτ,
     Forall (type_complete Γ) τs ∧
     (Γ,Δ,τs) ⊢ s : cmτ ∧ rettype_match cmτ τ ∧
     gotos s ⊆ labels s ∧ throws_valid 0 s
  | None => True
  end.
Definition global_decl_valid (Γ : env K) (Δ : memenv K)
    (x : string) (d : global_decl K) :=
  match d with
  | Global _ o τ _ => Δ ⊢ o : τ ∧ index_alive Δ o
  | Fun _ τs τ ms =>
     Γ !! (x : funname) = Some (τs,τ) ∧ fun_stmt_valid Γ Δ τs τ ms
  | GlobalTypeDef τp => ✓{Γ} τp
  | EnumVal τi z => int_typed z τi
  end.
Record frontend_state_valid' (S : frontend_state K) := {
  to_env_valid : ✓ (to_env S);
  to_mem_valid : ✓{to_env S} (to_mem S);
  to_globals_valid :
    map_Forall (global_decl_valid (to_env S) '{to_mem S}) (to_globals S);
  to_env_included :
    map_Forall (λ t d,
      match d with
      | Compound _ xτs => to_env S !! t = Some (xτs.*2) | _ => True
      end) (to_compounds S);
  to_funs_included :
    map_Forall (λ (f : funname) τsτ, ∃ sto ms,
      to_globals S !! (f : string) = Some (Fun sto (τsτ.1) (τsτ.2) ms)
    ) (env_f (to_env S))
}.
#[global] Instance frontend_state_valid : Valid () (frontend_state K) :=
  λ _, frontend_state_valid'.
Hint Extern 0 (✓ _) => eapply to_env_valid; eassumption: core.
Hint Extern 0 (✓{_} _) => eapply to_mem_valid; eassumption: core.
Hint Extern 0 (global_decl_valid _ _ _ _) => progress simpl: core.
Lemma global_decl_valid_weaken Γ1 Γ2 Δ1 Δ2 x d :
  ✓ Γ1 → global_decl_valid Γ1 Δ1 x d → Γ1 ⊆ Γ2 →
  Δ1 ⊆ Δ2 → global_decl_valid Γ2 Δ2 x d.
Proof.
  destruct d as [|??? []| |];
    naive_solver eauto using ptr_type_valid_weaken, index_typed_weaken,
    stmt_typed_weaken, memenv_subseteq_alive, env_valid_args_valid,
    lookup_fun_weaken, types_complete_weaken, types_complete_valid.
Qed.
Lemma frontend_state_empty_valid : ✓ (∅ : frontend_state K).
Proof.
  split; simpl; auto using env_empty_valid, cmap_empty_valid', map_Forall_empty.
Qed.
Lemma to_globals_lookup S x d :
  ✓ S → to_globals S !! x = Some d →
  global_decl_valid (to_env S) '{to_mem S} x d.
Proof. intros []; eauto. Qed.
Lemma to_funenv_pretyped S :
  ✓ S → funenv_prevalid (to_env S) '{to_mem S} (to_funenv S).
Proof.
  intros [?? HΔg] f s. unfold to_funenv; rewrite lookup_omap, bind_Some.
  intros ([]&Hd&?); specialize (HΔg _ _ Hd); naive_solver.
Qed.
Lemma to_funenv_typed S :
  ✓ S → incomplete_fun_decls S = ∅ → ✓{to_env S,'{to_mem S}} (to_funenv S).
Proof.
  unfold incomplete_fun_decls.
  split. by apply to_funenv_pretyped. by apply empty_difference_subseteq_L.
Qed.

Definition global_decl_forward (d' d : global_decl K) : Prop :=
  match d', d with
  | Global _ o1 τ1 _, Global _ o2 τ2 _=> o1 = o2 ∧ τ1 = τ2
  | Fun _ τs1 τ1 _, Fun _ τs2 τ2 _ => τs1 = τs2 ∧ τ1 = τ2
  | GlobalTypeDef τp1, GlobalTypeDef τp2 => τp1 = τp2
  | EnumVal τi1 x1, EnumVal τi2 x2 => τi1 = τi2 ∧ x1 = x2
  | _, _ => False
  end.
Record frontend_state_subseteq' (S1 S2 : frontend_state K) := {
  to_env_forward : to_env S1 ⊆ to_env S2;
  to_mem_forward : '{to_mem S1} ⊆ '{to_mem S2};
  to_globals_forward :
    map_included global_decl_forward (to_globals S1) (to_globals S2)
}.
#[global] Instance frontend_state_subseteq :
  SubsetEq (frontend_state K) := frontend_state_subseteq'.
Lemma to_env_subseteq S1 S2 : S1 ⊆ S2 → to_env S1 ⊆ to_env S2.
Proof. by intros []. Qed.
Lemma to_mem_subseteq S1 S2 : S1 ⊆ S2 → '{to_mem S1} ⊆ '{to_mem S2}.
Proof. by intros []. Qed.
Hint Immediate to_env_subseteq to_mem_subseteq: core.
#[local] Instance: PreOrder global_decl_forward.
Proof. split. by intros []. intros [] []; naive_solver. Qed.
#[global] Instance: PreOrder ((⊆) : relation (frontend_state K)).
Proof. split; [by split|]. intros ??? [] []; split; etransitivity; eauto. Qed.
Hint Extern 1 (_ ⊆ _) => etransitivity; [eassumption|]: core.
Hint Extern 1 (_ ⊆ _) => etransitivity; [|eassumption]: core.
Hint Extern 1 (map_included global_decl_forward ?S ?S) => reflexivity: core.

Definition local_decl_valid (S : frontend_state K)
    (x : string) (d : local_decl K) :=
  match d with
  | Extern (inl (o,τ)) => '{to_mem S} ⊢ o : τ
  | Extern (inr (τs,τ)) => to_env S !! (x : funname) = Some (τs,τ)
  | Local τ => ✓{to_env S} τ
  | TypeDef τp => ✓{to_env S} τp
  end.
Definition local_env_valid (S : frontend_state K) : local_env K → Prop :=
  Forall (λ xmd,
    match xmd with Some (x,d) => local_decl_valid S x d | None => True end).
Hint Unfold local_env_valid: core.
Lemma local_decl_valid_weaken S1 S2 x d :
  ✓ S1 → local_decl_valid S1 x d → S1 ⊆ S2 → local_decl_valid S2 x d.
Proof.
  destruct 1, 2, d as [[[]|[]]| |]; naive_solver eauto using
    ptr_type_valid_weaken, type_valid_weaken, index_typed_weaken,
    env_valid_args_valid, lookup_fun_weaken.
Qed.
Lemma local_env_valid_subseteq S1 S2 Δl :
  ✓ S1 → local_env_valid S1 Δl → S1 ⊆ S2 → local_env_valid S2 Δl.
Proof.
  unfold local_env_valid.
  induction 2 as [|[[]|]]; constructor; eauto using local_decl_valid_weaken.
Qed.
Lemma local_env_valid_params S (ys : list string) (τs : list (type K)) :
  ✓{to_env S}* τs →
  local_env_valid S (zip_with (λ y τ, Some (y, Local τ)) ys τs).
Proof.
  intros Hτs; revert ys. unfold local_env_valid.
  induction Hτs; intros [|??]; simpl; constructor; auto.
Qed.
Lemma local_env_valid_None S Δl :
  local_env_valid S Δl → local_env_valid S (None :: Δl).
Proof. by constructor. Qed.
Lemma local_env_valid_Some S Δl x d :
  local_env_valid S Δl → local_decl_valid S x d →
  local_env_valid S (Some (x,d) :: Δl).
Proof. by constructor. Qed.
Hint Resolve local_env_valid_None local_env_valid_Some: core.

Fixpoint to_local_types (Δl : local_env K) : list (type K) :=
  match Δl with
  | [] => []
  | Some (_,Local τ) :: Δl => τ :: to_local_types Δl
  | _ :: Δl => to_local_types Δl
  end.
Lemma to_local_types_params (ys : list string) (τs : list (type K)) :
  length ys = length τs →
  to_local_types (zip_with (λ y τ, Some (y, Local τ)) ys τs) = τs.
Proof. rewrite <-Forall2_same_length. induction 1; f_equal'; auto. Qed.
Lemma to_local_types_valid S Δl :
  local_env_valid S Δl → ✓{to_env S}* (to_local_types Δl).
Proof. induction 1 as [|[[? []]|]]; simpl; auto. Qed.
Hint Immediate to_local_types_valid: core.

Lemma lookup_compound_typed S S' t x i τ :
  lookup_compound t x S = mret (M := M) (i,τ) S' → ✓ S →
  ∃ τs, to_env S' !! t = Some τs ∧ τs !! i = Some τ ∧ S = S'.
Proof.
  unfold lookup_compound; intros ? [_ _ _ HΓn _]; error_proceed Γn as S2.
  destruct (to_compounds S !! _) as [[c xτs|]|] eqn:?; error_proceed.
  destruct (list_find _ _) as [[? [y ?]]|] eqn:?; error_proceed.
  destruct (list_find_Some (λ xτ, x = xτ.1) xτs i (y,τ)) as [[Hi [-> _]] _]; auto.
  feed pose proof (HΓn t (Compound c xτs)); auto; simplify_equality'.
  exists (xτs.*2); split_and ?; auto. by rewrite list_lookup_fmap, Hi.
Qed.
Lemma lookup_local_var_typed S τs Δl x e τlr :
  lookup_local_var Δl x (length τs) = Some (e,τlr) → ✓ S → local_env_valid S Δl →
  (to_env S,'{to_mem S},τs ++ to_local_types Δl) ⊢ e : τlr
  ∧ locks e = ∅.
Proof.
  intros He [] HΔl. revert τs He.
  induction HΔl as [|[[x' [[[]|[]]|τ'|]]|] ? Δl ? IH];
    intros τs' ?; simplify_option_eq; simplify_type_equality; eauto 2.
  * eauto 10 using cmap_index_typed_valid.
  * eauto 10.
  * split; [|done]. typed_constructor; by rewrite list_lookup_middle.
  * rewrite cons_middle, (assoc_L (++)). apply (IH (τs' ++ [τ'])).
    rewrite app_length; simpl. by rewrite Nat.add_comm.
Qed.
Lemma lookup_var_typed S S' Δl x e τlr :
  lookup_var Δl x S = mret (M := M) (e,τlr) S' → ✓ S → local_env_valid S Δl →
  (to_env S,'{to_mem S},to_local_types Δl) ⊢ e : τlr ∧ locks e = ∅ ∧ S = S'.
Proof.
  unfold lookup_var; intros ? HS ?.
  destruct (lookup_local_var Δl x 0) as [[??]|] eqn:?; simplify_error_equality.
  { edestruct (lookup_local_var_typed S' []); eauto. }
  destruct (_ !! x) as [d|] eqn:Hd; simplify_equality.
  pose proof (to_globals_valid _ HS x d Hd).
  destruct d as [|sto τs τ ms| |]; simplify_equality'; split; auto.
  * typed_constructor; intuition eauto using index_typed_valid.
  * repeat typed_constructor; naive_solver.
Qed.

Lemma lookup_local_typedef_valid S Δl x τp :
  local_env_valid S Δl → lookup_local_typedef Δl x = Some τp → ✓{to_env S} τp.
Proof.
  induction 1 as [|[[? []]|]]; intros; simplify_option_eq; eauto.
Qed.
Lemma lookup_typedef_valid S Δl x τp S' :
  lookup_typedef Δl x S = mret (M := M) τp S' → ✓ S → local_env_valid S Δl →
  ✓{to_env S} τp ∧ S = S'.
Proof.
  unfold lookup_typedef; intros ? HS ?.
  destruct (lookup_local_typedef Δl x) eqn:?; error_proceed.
  { eauto using lookup_local_typedef_valid. }
  destruct (_ !! x) as [[]|] eqn:Hd; error_proceed.
  split; auto; apply (to_globals_valid _ HS x _ Hd).
Qed.

Lemma to_int_const_typed x cτis τi :
  to_int_const x cτis = Some τi → int_typed x τi.
Proof. intros; induction cτis; simplify_option_eq; auto. Qed.
Hint Immediate to_int_const_typed: core.
Lemma to_string_const_typed Γ Δ zs v n :
  to_string_const zs = Some (v,n) → (Γ,Δ) ⊢ v : charT.[n] ∧ n ≠ 0.
Proof.
  unfold to_string_const; intros; simplify_option_eq; split; [|done].
  typed_constructor; rewrite ?fmap_length, ?app_length; simpl; try lia.
  cut (Forall (λ z, int_typed z charT) (zs ++ [0%Z])); auto using Forall_app_2.
  induction 1; csimpl; eauto.
Qed.
Lemma to_limit_const_typed S S' τ li z τi :
  ✓ S → to_limit_const τ li S = mret (M := M) (z,τi) S' → int_typed z τi ∧ S = S'.
Proof.
  destruct li; intros; repeat (case_match || simplify_error_equality);
    eauto using int_lower_typed, int_upper_typed, int_width_typed.
  edestruct lookup_compound_typed as (?&?&?&?); eauto.
Qed.

Lemma to_R_typed S S' τs e τlr e' τ' :
  to_R e τlr S = mret (M := M) (e',τ') S' → ✓ S →
  (to_env S,'{to_mem S},τs) ⊢ e : τlr → locks e = ∅ →
  ✓{to_env S}* τs →
  (to_env S,'{to_mem S},τs) ⊢ e' : inr τ' ∧ locks e' = ∅ ∧ S' = S.
Proof.
  unfold to_R; intros; destruct τlr as [[τ''| |σs σ]|τ];
    simplify_error_equality; auto.
  destruct (maybe2 TArray τ'') as [[τ n]|] eqn:?;
    simplify_error_equality; split_and ?; repeat typed_constructor; eauto.
   apply Nat.neq_0_lt_0;
    eauto using TArray_ptr_valid_inv_size, expr_inl_typed_type_valid.
Qed.
Lemma to_R_NULL_typed S S' τs σ e τlr e' τ' :
  to_R_NULL σ e τlr S = mret (M := M) (e',τ') S' → ✓ S →
  (to_env S,'{to_mem S},τs) ⊢ e : τlr → locks e = ∅ →
  ✓{to_env S}* τs → ✓{to_env S} (TType σ) →
  (to_env S,'{to_mem S},τs) ⊢ e' : inr τ' ∧ locks e' = ∅ ∧ S' = S.
Proof.
  unfold to_R_NULL; intros ????? Hσ; error_proceed [e'' τ''] as S''.
  destruct (to_R_typed S S'' τs e τlr e'' τ'') as (?&?&->); auto.
  inversion Hσ as [|σb []| | |]; intros;
    repeat case_match; simplify_error_equality; eauto 10.
Qed.
Lemma convert_ptrs_typed Γ m τs e1 τ1 e2 τ2 e1' e2' τ' :
  convert_ptrs (e1,τ1) (e2,τ2) = Some (e1', e2', τ') →
  (Γ,'{m},τs) ⊢ e1 : inr τ1 → locks e1 = ∅ →
  (Γ,'{m},τs) ⊢ e2 : inr τ2 → locks e2 = ∅ → ✓ Γ → ✓{Γ}* τs →
  (Γ,'{m},τs) ⊢ e1' : inr τ' ∧ (Γ,'{m},τs) ⊢ e2' : inr τ'
  ∧ locks e1' = ∅ ∧ locks e2' = ∅.
Proof.
  unfold convert_ptrs; destruct τ1 as [[| |[]]| |], τ2 as [[| |[]]| |];
    intros; simplify_option_eq; split; repeat typed_constructor;
    eauto 12 using TPtr_valid_inv, TBase_valid_inv, expr_inr_typed_type_valid.
Qed.
Lemma to_if_expr_typed Γ m τs e1 τb e2 τ2 e3 τ3 e τlr :
  to_if_expr e1 (e2,τ2) (e3,τ3) = Some (e,τlr) →
  (Γ,'{m},τs) ⊢ e1 : inr (baseT τb) → τb ≠ TVoid → locks e1 = ∅ →
  (Γ,'{m},τs) ⊢ e2 : inr τ2 → locks e2 = ∅ →
  (Γ,'{m},τs) ⊢ e3 : inr τ3 → locks e3 = ∅ → ✓ Γ → ✓{Γ}* τs →
  (Γ,'{m},τs) ⊢ e : τlr ∧ locks e = ∅.
Proof.
  unfold to_if_expr; intros;
    repeat match goal with
    | _ => progress simplify_option_eq
    | _ => case_match
    | x : (_ * _)%type |- _ => destruct x
    | H : convert_ptrs _ _ = Some _ |- _ =>
       eapply convert_ptrs_typed in H; eauto; destruct H as (?&?&?&?)
    end; eauto 10.
Qed.
Lemma to_binop_expr_typed Γ m τs op e1 τ1 e2 τ2 e τlr :
  to_binop_expr op (e1,τ1) (e2,τ2) = Some (e,τlr) →
  (Γ,'{m},τs) ⊢ e1 : inr τ1 → locks e1 = ∅ →
  (Γ,'{m},τs) ⊢ e2 : inr τ2 → locks e2 = ∅ → ✓ Γ → ✓{Γ}* τs →
  (Γ,'{m},τs) ⊢ e : τlr ∧ locks e = ∅.
Proof.
  unfold to_binop_expr; intros;
    repeat match goal with
    | _ => progress simplify_option_eq
    | x : (_ * _)%type |- _ => destruct x
    | H: binop_type_of _ _ _ = Some _ |- _ => apply binop_type_of_sound in H
    | H : convert_ptrs _ _ = Some _ |- _ =>
       eapply convert_ptrs_typed in H; eauto; destruct H as (?&?&?&?)
    end; eauto 10.
Qed.

CoInductive seen {A} (x : A) := Seen : seen x.
Ltac weaken :=
  repeat match goal with
  | H : local_env_valid ?S ?Δl, H2 : ?S ⊆ ?S' |- _ =>
     assert (local_env_valid S' Δl)
       by eauto using local_env_valid_subseteq; clear H
  | H : ✓{to_env ?S1} ?τp, H2 : ?S1 ⊆ ?S2  |- _ =>
     assert (✓{to_env S2} τp) by eauto using ptr_type_valid_weaken; clear H
  | H : ✓{to_env ?S1}* ?τps, H2 : ?S1 ⊆ ?S2  |- _ =>
     assert (✓{to_env S2}* τps) by eauto using ptr_types_valid_weaken; clear H
  | H : ✓{to_env ?S1} ?τ, H2 : ?S1 ⊆ ?S2  |- _ =>
     assert (✓{to_env S2} τ) by eauto using type_valid_weaken; clear H
  | H : ✓{to_env ?S1}* ?τs, H2 : ?S1 ⊆ ?S2  |- _ =>
     assert (✓{to_env S2}* τs) by eauto using types_valid_weaken; clear H
  | H : type_complete (to_env ?S1) ?τ, H2 : ?S1 ⊆ ?S2  |- _ =>
     assert (type_complete (to_env S2) τ)
       by eauto using type_complete_weaken; clear H
  | H : Forall (type_complete (to_env ?S1)) ?τs, H2 : ?S1 ⊆ ?S2  |- _ =>
     assert (Forall (type_complete (to_env S2)) τs)
       by eauto using types_complete_weaken; clear H
  | H : (to_env ?S1,_,?τs) ⊢ ?e : ?τlr, H2 : ?S1 ⊆ ?S2  |- _ =>
     assert ((to_env S2,'{to_mem S2},τs) ⊢ e : τlr)
       by (eapply (expr_typed_weaken (to_env S1)); eauto); clear H
  | H : (to_env ?S1,_,?τs) ⊢ ?s : ?cmτ, H2 : ?S1 ⊆ ?S2  |- _ =>
     assert ((to_env S2,'{to_mem S2},τs) ⊢ s : cmτ)
       by (eapply (stmt_typed_weaken (to_env S1)); eauto); clear H
  | H : '{to_mem ?S1} ⊢ ?o : ?τ, H2 : ?S1 ⊆ ?S2  |- _ =>
     assert ('{to_mem S2} ⊢ o : τ) by eauto using index_typed_weaken; clear H
  | H : index_alive '{to_mem ?S1} ?o, H2 : ?S1 ⊆ ?S2  |- _ =>
     assert (index_alive '{to_mem S2} o)
       by eauto using memenv_subseteq_alive; clear H
  | H : to_env ?S1 !! ?f = Some ?τsτ, H2 : ?S1 ⊆ ?S2  |- _ =>
     assert (to_env S2 !! (f : funname) = Some τsτ)
       by eauto using lookup_fun_weaken; clear H
  | H : to_env ?S1 ⊢ ?r : ?τ ↣ ?σ, H2 : ?S1 ⊆ ?S2  |- _ =>
     assert (to_env S2 ⊢ r : τ ↣ σ) by eauto using ref_typed_weaken; clear H
  | H : (to_env ?S1,_) ⊢ ?v : ?τ, H2 : ?S1 ⊆ ?S2  |- _ =>
     assert ((to_env S2,'{to_mem S2}) ⊢ v : τ)
       by (eapply (val_typed_weaken (to_env S1)); eauto); clear H
  | H : ✓{_} (inl _) |- _ => apply ltype_valid_inv in H
  | H : ✓{_} (inr _) |- _ => apply rtype_valid_inv in H
  | H : ✓{_} (baseT _) |- _ => apply TBase_valid_inv in H
  | H : ✓{_} (_.*)%BT |- _ => apply TPtr_valid_inv in H
  | H : ✓{_} (_ ~> _) |- _ => apply TFun_valid_inv in H; destruct H
  | _ : (?Γ,?Δ,?τs) ⊢ _ : ?τlr |- _ =>
     unless (seen τlr) by assumption;
     assert (✓{Γ} τlr) by eauto using (expr_typed_type_valid Γ Δ τs);
     assert (seen τlr) by constructor
  | _ => progress simplify_equality'
  end.

Lemma insert_object_valid S S' o v γ τ :
  insert_object γ v S = mret (M := M) o S' → ✓ S →
  (to_env S, '{to_mem S}) ⊢ v : τ → sep_valid γ → ¬sep_unmapped γ →
  '{to_mem S'} ⊢ o : τ ∧ index_alive '{to_mem S'} o
  ∧ to_globals S = to_globals S' ∧ ✓ S' ∧ S ⊆ S'.
Proof.
  destruct S as [Γn Γ m Δg]; unfold insert_object;
    intros ? [] ???; error_proceed; simplify_type_equality.
  assert ('{m} ⊆ <[fresh (dom indexset m):=(τ, false)]> '{m}).
  { eapply insert_subseteq, mem_allocable_memenv_of, is_fresh. }
  split_and ?; eauto using mem_alloc_index_typed', mem_alloc_index_alive';
    split; simpl; erewrite ?mem_alloc_memenv_of by eauto;
    eauto using map_Forall_impl, global_decl_valid_weaken.
  eapply mem_alloc_valid'; eauto using val_typed_weaken, mem_alloc_forward'.
Qed.
Lemma update_object_valid S S' o γ v τ :
  update_object o γ v S = mret (M := M) () S' → ✓ S →
  '{to_mem S} ⊢ o : τ → index_alive '{to_mem S} o →
  (to_env S, '{to_mem S}) ⊢ v : τ → sep_valid γ → ¬sep_unmapped γ →
  ✓ S' ∧ S ⊆ S'.
Proof.
  destruct S; unfold update_object; intros ? [] ?????; error_proceed.
  do 2 split; simpl; erewrite ?mem_alloc_alive_memenv_of by eauto;
    eauto using mem_alloc_alive_valid'.
Qed.
Lemma insert_global_decl_valid S S' x d :
  insert_global_decl x d S = mret (M := M) () S' → ✓ S →
  global_decl_valid (to_env S) '{to_mem S} x d → maybe4 Fun d = None →
  (∀ d', to_globals S !! x = Some d' → global_decl_forward d' d) →
  to_globals S' !! x = Some d ∧ ✓ S' ∧ S ⊆ S'.
Proof.
  destruct S as [Γn Γ m Δg]; unfold insert_global_decl;
    intros ? [HΓ Hm HΔg HΓn HΓ'] ???; error_proceed; simplify_map_eq.
  split_and ?; split; simpl; auto using map_Forall_insert_2.
  * intros f τsτ ?. destruct (decide_rel (=) f x); simplify_map_eq; auto.
    destruct (HΓ' x τsτ) as (sto&?&?); auto. exfalso; destruct d; naive_solver.
  * by apply (insert_included _).
Qed.
Lemma insert_fun_None_valid S S' f sto τs τ :
  insert_fun f sto τs τ None S = mret (M := M) () S' → ✓ S →
  to_globals S !! (f : string) = None →
  ✓{to_env S}* (TType <$> τs) → ✓{to_env S} (TType τ) →
  to_env S' !! f = Some (τs,τ) ∧ ✓ S' ∧ S ⊆ S'.
Proof.
  destruct S as [Γn Γ m Δg]; unfold insert_fun;
    intros ? [HΓ Hm HΔg HΓn HΓ'] ???; error_proceed.
  destruct (Γ !! f) as [[τs' τ']|] eqn:Hf; simplify_map_eq.
  { destruct (HΓ' f (τs',τ')); naive_solver. }
  assert (Γ ⊆ <[f:=(τs,τ)]> Γ) by (by apply insert_fun_subseteq).
  split_and ?; split; simpl; eauto using cmap_valid_weaken'.
  * by constructor.
  * apply map_Forall_insert_2; simplify_map_eq;
      eauto using sizes_of_weaken, map_Forall_impl, global_decl_valid_weaken.
  * apply map_Forall_insert_2; simplify_map_eq; eauto.
    unfold lookup, env_lookup_fun in Hf.
    intros f' ??; destruct (decide (f = f')); simplify_map_eq; eauto.
  * apply (insert_included _); congruence.
Qed.
Lemma insert_fun_valid S S' f sto τs τ ms :
  insert_fun f sto τs τ ms S = mret (M := M) () S' → ✓ S → to_env S !! f = Some (τs,τ) →
  fun_stmt_valid (to_env S) '{to_mem S} τs τ ms → ✓ S' ∧ S ⊆ S'.
Proof.
  destruct S as [Γn Γ m Δg]; unfold insert_fun;
    intros ? [HΓ Hm HΔg HΓn HΓ'] Hf ?; error_proceed.
  rewrite insert_fun_id by done.
  destruct (HΓ' f (τs,τ)) as (ms'&?&?); auto.
  do 2 split; simpl; auto using map_Forall_insert_2.
  * intros f' [τs' τ'] ?; unfold lookup, env_lookup_fun in Hf.
    destruct (decide (f = f')); simplify_map_eq; eauto.
    replace τs' with (τs', τ').1; replace τ' with (τs', τ').2; auto.
  * apply (insert_included _); intros [] ?; naive_solver.
Qed.
Lemma insert_compound_valid S S' c t xτs :
  insert_compound c t xτs S = mret (M := M) () S' → ✓ S →
  to_env S !! t = None → ✓{to_env S}* (xτs.*2) → xτs ≠ [] →
  to_env S' !! t = Some (xτs.*2) ∧ ✓ S' ∧ S ⊆ S'.
Proof.
  destruct S as [Γn Γ m Δg]; unfold insert_compound;
    intros ? [HΓ Hm HΔg HΓn HΓ'] ???; error_proceed; simplify_map_eq.
  split_and ?; split; simpl; eauto using env_insert_compound_valid, fmap_nil_inv.
  * eauto using cmap_valid_weaken', insert_compound_subseteq.
  * eapply map_Forall_impl;
      eauto using global_decl_valid_weaken, insert_compound_subseteq.
  * intros t' d ?; destruct (decide (t = t')); simplify_map_eq; auto.
    rewrite lookup_insert_compound_ne by done; by apply HΓn.
  * eauto using insert_compound_subseteq.
Qed.
Lemma insert_enum_valid S S' t τi :
  insert_enum t τi S = mret (M := M) () S' → ✓ S → to_compounds S !! t = None →
  ✓ S' ∧ S ⊆ S'.
Proof.
  destruct S as [Γn Γ m Δg]; unfold insert_enum;
    intros ? [HΓ Hm HΔg HΓn HΓ'] ?; error_proceed.
  do 2 split; simpl; auto using map_Forall_insert_2.
Qed.

Lemma first_init_ref_typed Γ τ r σ :
  first_init_ref Γ τ = Some (r,σ) → ✓{Γ} τ → Γ ⊢ r : τ ↣ σ.
Proof.
  destruct 2 as [| |[]]; simplify_option_eq;
    repeat econstructor; eauto with lia.
Qed.
Fixpoint next_init_ref_typed Γ τ r σ r' σ' :
  next_init_ref Γ r = Some (r',σ') → Γ ⊢ r : τ ↣ σ → Γ ⊢ r' : τ ↣ σ'.
Proof.
  induction 2 as [|????? []];
    repeat (case_match || simplify_option_eq); repeat econstructor; eauto.
Qed.
Lemma to_ref_typed S S' Δl r τ xces σ r' σ' :
  Forall (sum_rect _ (λ _, True) (λ ce, ∀ S S' e τlr,
    to_expr Δl ce S = (mret (e,τlr) : M _) S' → ✓ S → local_env_valid S Δl →
    (to_env S','{to_mem S'},to_local_types Δl) ⊢ e : τlr
    ∧ locks e = ∅ ∧ ✓ S' ∧ S ⊆ S')) xces →
  to_ref (to_expr Δl) r σ xces S = mret (M := M) (r',σ') S' →
  ✓ S → local_env_valid S Δl →
  to_env S ⊢ r : τ ↣ σ → to_env S' ⊢ r' : τ ↣ σ' ∧ ✓ S' ∧ S ⊆ S'.
Proof.
  intros IHxces. revert S r σ. induction IHxces as [|[x|ce] xces IH _ IHxces];
    generalize_errors; intros S r σ ????; simplify_equality'; auto.
  * error_proceed [c s] as ?; error_proceed [i τ'] as S2.
    destruct (lookup_compound_typed S S2 s x i τ') as (τs&?&?&->); auto.
    destruct c; error_proceed; eauto.
  * error_proceed [τ' n] as ?; error_proceed [e τe] as S2.
    error_proceed [|[[| |τi x| |]| | | |]] as ?.
    destruct (IH S S2 e τe) as (_&?&?&?); weaken; auto.
    destruct (IHxces S2 (RArray (Z.to_nat x) τ' n :: r) τ') as (?&?&?); eauto.
Qed.

Lemma to_call_fun_typed Γ Δ τs e τlr e' σs σ :
  to_call_fun e τlr = Some (e',σs,σ) → (Γ,Δ,τs) ⊢ e : τlr → locks e = ∅ →
  (Γ,Δ,τs) ⊢ e' : inl (σs ~> σ) ∧ locks e' = ∅.
Proof.
  destruct τlr as [[]|]; intros;
    simplify_option_eq; eauto using TBase_complete.
Qed.
Lemma to_call_args_typed S S' Δl ces τs es :
  Forall (λ ce, ∀ S S' e τlr,
    to_expr Δl ce S = mret (M := M) (e,τlr) S' → ✓ S → local_env_valid S Δl →
    (to_env S','{to_mem S'},to_local_types Δl) ⊢ e : τlr
    ∧ locks e = ∅ ∧ ✓ S' ∧ S ⊆ S') ces →
  to_call_args (to_expr Δl) ces τs S = mret (M := M) es S' → ✓ S → local_env_valid S Δl →
  ✓{to_env S}* (TType <$> τs) →
  (to_env S','{to_mem S'},to_local_types Δl) ⊢* es :* inr <$> τs
  ∧ ⋃ (locks <$> es) = ∅ ∧ ✓ S' ∧ S ⊆ S'.
Proof.
  intros Hces; revert S S' es τs; induction Hces as [|ce ces IH _ IHces];
    intros S S' es [|τ τs] ????; error_proceed; eauto.
  error_proceed [e τlr] as S2; error_proceed [e' τ'] as S3.
  error_proceed es' as ?; decompose_Forall_hyps.
  destruct (IH S S2 e τlr) as (?&?&?&?); auto; weaken.
  destruct (to_R_NULL_typed S2 S3 (to_local_types Δl) τ e τlr e' τ')
    as (?&?&->); eauto.
  destruct (IHces S2 S' es' τs) as (?&?&?&?); auto; weaken;
    eauto 10 using cast_typed_type_valid.
Qed.
Lemma to_compound_init_typed S S' Δl e τ rs inits e' :
  Forall (λ i,
    Forall (sum_rect _ (λ _, True) (λ ce, ∀ S S' e τlr,
      to_expr Δl ce S = (mret (e,τlr) : M _) S' → ✓ S → local_env_valid S Δl →
      (to_env S','{to_mem S'},to_local_types Δl) ⊢ e : τlr
      ∧ locks e = ∅ ∧ ✓ S' ∧ S ⊆ S')) (i.1) ∧
    (∀ S S' τ e,
      to_init_expr Δl τ (i.2) S = mret (M := M) e S' →
      ✓ S → local_env_valid S Δl → ✓{to_env S} τ →
      (to_env S','{to_mem S'},to_local_types Δl) ⊢ e : inr τ
      ∧ locks e = ∅ ∧ ✓ S' ∧ S ⊆ S')) inits →
  to_compound_init (to_expr Δl) (to_init_expr Δl) τ e rs inits S = mret (M := M) e' S' →
  ✓ S → local_env_valid S Δl → Forall (λ r, ∃ σ, to_env S ⊢ r : τ ↣ σ) rs →
  (to_env S,'{to_mem S},to_local_types Δl) ⊢ e : inr τ → locks e = ∅ →
  (to_env S','{to_mem S'},to_local_types Δl) ⊢ e' : inr τ
  ∧ locks e' = ∅ ∧ ✓ S' ∧ S ⊆ S'.
Proof.
  intros Hinits. revert S S' rs e e'. assert (∀ Γ1 Γ2 rs,
    Forall (λ r, ∃ σ, Γ1 ⊢ r : τ ↣ σ) rs → Γ1 ⊆ Γ2 →
    Forall (λ r, ∃ σ, Γ2 ⊢ r : τ ↣ σ) rs).
  { induction 1 as [|?? [??]]; constructor; eauto using ref_typed_weaken. }
  induction Hinits as [|[xces ci] inits [IHe IHi] _ IH];
    intros S S' rs e e' ??? Hrs ??; error_proceed; eauto.
  destruct (decide (xces = [])); error_proceed; decompose_Forall_hyps; weaken.
  * destruct Hrs as [|r rs [σ ?]]; error_proceed; decompose_Forall_hyps.
    + error_proceed [r σ] as ?; error_proceed e'' as S2.
      assert (to_env S ⊢ r : τ ↣ σ) by auto using first_init_ref_typed.
      destruct (IHi S S2 σ e'')
        as (?&?&?&?); eauto using ref_typed_type_valid; weaken.
      destruct (IH S2 S' [r] (#[r:=e''] e) e') as (?&?&?&?); eauto.
    + error_proceed [r' σ'] as ?; error_proceed e'' as S2.
      assert (to_env S ⊢ r' : τ ↣ σ') by eauto using next_init_ref_typed.
      destruct (IHi S S2 σ' e'')
        as (?&?&?&?); eauto using ref_typed_type_valid; weaken.
      destruct (IH S2 S' (r' :: r :: rs) (#[r':=e''] e) e')
        as (?&?&?&?); eauto 10.
  * error_proceed [r σ] as S2; error_proceed e'' as S3.
    destruct (to_ref_typed S S2 Δl [] τ xces τ r σ) as (?&?&?); auto; weaken.
    destruct (IHi S2 S3 σ e'')
      as (?&?&?&?); eauto using ref_typed_type_valid; weaken.
    destruct (IH S3 S' (r :: rs) (#[r:=e''] e) e') as (?&?&?&?); eauto 10.
Qed.
Definition to_type_type_valid {k} (Γ : env K) : to_type_type k → Prop :=
  match k with to_Type => ✓{Γ} | to_Ptr => ✓{Γ} end.
Lemma convert_fun_arg_type_valid Γ τp τ :
  convert_fun_arg_type τp = Some τ → ✓{Γ} τp → ✓{Γ} (TType τ).
Proof.
  inversion 2; simplify_option_eq; repeat constructor; auto.
  by apply type_valid_ptr_type_valid.
Qed.
Lemma convert_fun_ret_valid Γ τp τ :
  convert_fun_ret_type τp = Some τ → ✓{Γ} τp → ✓{Γ} (TType τ).
Proof. inversion 2; simplify_option_eq; repeat constructor; auto. Qed.
Lemma to_fun_type_valid S S' Δl cτs cτ xτs τ :
  Forall (λ xcτ, ∀ S S' k τk,
    to_type k Δl (xcτ.2) S = mret (M := M) τk S' → ✓ S → local_env_valid S Δl →
    to_type_type_valid (to_env S') τk ∧ ✓ S' ∧ S ⊆ S') cτs →
  (∀ S S' k τk,
    to_type k Δl cτ S = mret (M := M) τk S' → ✓ S → local_env_valid S Δl →
    to_type_type_valid (to_env S') τk ∧ ✓ S' ∧ S ⊆ S') →
  to_fun_type (to_type to_Ptr Δl) cτs cτ S = mret (M := M) (xτs,τ) S' →
  ✓ S → local_env_valid S Δl →
  ✓{to_env S'}* (TType <$> xτs.*2) ∧ ✓{to_env S'} (TType τ) ∧ ✓ S' ∧ S ⊆ S'.
Proof.
  intros IHcτs. revert S cτ τ. assert (∀ S,
    to_fun_type_args (to_type to_Ptr Δl) cτs S = mret (M := M) xτs S' →
    ✓ S → local_env_valid S Δl →
    ✓{to_env S'}* (TType <$> xτs.*2) ∧ ✓ S' ∧ S ⊆ S') as help.
  { revert xτs; induction IHcτs as [|[x cτ] cτs IH _ IHcτs];
      intros xτs S ???; error_proceed; auto.
    error_proceed τp as S2; error_proceed τ as ?; error_proceed xτs' as ?.
    destruct (IH S S2 to_Ptr τp) as (?&?&?); auto; weaken.
    destruct (IHcτs xτs' S2) as (?&?&?); auto; weaken.
    eauto 10 using convert_fun_arg_type_valid. }
  unfold to_fun_type; intros S cτ τ IH ???.
  error_proceed τp as S2; error_proceed τ' as ?.
  destruct (IH S S2 to_Ptr τp) as (?&?&?); auto; weaken.
  destruct (fun_empty_args _); error_proceed; eauto using convert_fun_ret_valid.
  error_proceed τs as ?.
  destruct (help S2) as (?&?&?); weaken; eauto 10 using convert_fun_ret_valid.
Qed.
Lemma to_field_reg_seg_typed Γ c t i τs τ :
  Γ !! t = Some τs → τs !! i = Some τ →
  Γ ⊢ to_field_ref_seg c i t : compoundT{c} t ↣ τ.
Proof. destruct c; eauto. Qed.
Lemma to_expr_type_typed Δl :
  (∀ ce S S' e τlr,
    to_expr Δl ce S = mret (M := M) (e,τlr) S' → ✓ S → local_env_valid S Δl →
    (to_env S','{to_mem S'},to_local_types Δl) ⊢ e : τlr
    ∧ locks e = ∅ ∧ ✓ S' ∧ S ⊆ S') ∧
  (∀ ci S S' τ e,
    to_init_expr Δl τ ci S = mret (M := M) e S' →
    ✓ S → local_env_valid S Δl → ✓{to_env S} τ →
    (to_env S','{to_mem S'},to_local_types Δl) ⊢ e : inr τ
    ∧ locks e = ∅ ∧ ✓ S' ∧ S ⊆ S') ∧
  (∀ cτ S S' k τk,
    to_type k Δl cτ S = mret (M := M) τk S' → ✓ S → local_env_valid S Δl →
    to_type_type_valid (to_env S') τk ∧ ✓ S' ∧ S ⊆ S').
Proof.
  intros; apply cexpr_cinit_ctype_ind; generalize_errors; intros;
    repeat match goal with
    | _ => progress simplify_error_equality || case_match
    | H : _ = Assign ∧ _ |- _ => destruct H
    | x : (_ * _)%type |- _ => destruct x
    | IH : ∀ _ _ _ _, to_expr _ _ _ = _ → _, H : to_expr _ _ _ = _ |- _ =>
       destruct (IH _ _ _ _ H) as (?&?&?&?); auto 1; [clear IH H]; weaken
    | IH : ∀ _ _ _ _, to_init_expr _ _ _ _ = _ → _, H : _ = _ |- _ =>
       destruct (IH _ _ _ _ H) as (?&?&?&?); auto 1; [clear IH H]; weaken
    | IH : ∀ _ _ _ _, _ = _ → _, H : to_type ?k _ _ _ = _ |- _ =>
       destruct (IH _ _ k _ H) as (?&?&?); auto 1; [clear IH H]; weaken
    | H : lookup_var _ _ _ = _ |- _ =>
       apply lookup_var_typed in H; try done; [destruct H as (?&?&->)]
    | H : to_limit_const _ _ _ = _ |- _ =>
       apply to_limit_const_typed in H; try done; [destruct H as [? ->]]
    | H : unop_type_of _ _ = _ |- _ => apply unop_type_of_sound in H
    | H : binop_type_of _ _ _ = _ |- _ => apply binop_type_of_sound in H
    | H : lookup_typedef _ _ _ = _ |- _ =>
       apply lookup_typedef_valid in H; try assumption; [destruct H]
    | H : lookup_compound _ _ _ = _ |- _ =>
       apply lookup_compound_typed in H; auto; destruct H as (?&?&?&->)
    | H : to_call_fun _ _ = _ |- _ =>
       eapply to_call_fun_typed in H; eauto 2; [destruct H]; weaken
    | H : to_call_args _ _ _ _ = _ |- _ =>
       apply to_call_args_typed in H;
         try assumption; [destruct H as (?&?&?&?)]; weaken
    | H : to_fun_type _ _ _ _ = _ |- _ =>
       apply to_fun_type_valid in H;
         try assumption; [destruct H as (?&?&?&?)]; weaken
    | H : to_binop_expr _ _ _ = _ |- _ =>
       eapply to_binop_expr_typed in H; eauto 2; [destruct H]
    | H : to_if_expr _ _ _ = _ |- _ =>
       eapply to_if_expr_typed in H; eauto 2; [destruct H]
    | H : to_R_NULL _ _ _ _ = _ |- _ =>
       eapply to_R_NULL_typed in H; eauto; [destruct H as (?&?&->)]
    | H : to_R _ _ _ = _ |- _ =>
       eapply to_R_typed in H; eauto 2; [destruct H as (?&?&->)]
    | x : to_type_type ?k |- _ => destruct k
    | H : to_string_const _ = Some (?v,?n),
       _ : local_env_valid ?S _ |- _ =>
       assert ((to_env S, '{to_mem S}) ⊢ v : charT.[n] ∧ n ≠ 0) as []
         by eauto using to_string_const_typed;
       clear H; simplify_type_equality
    | H : insert_object _ _ _ = _ |- _ =>
       eapply insert_object_valid in H;
         eauto using perm_readonly_valid, perm_readonly_mapped;
         [destruct H as (?&?&?&?&?)]
    end; eauto 22 using to_compound_init_typed, expr_typed_freeze,
      to_field_reg_seg_typed.
Qed.
Lemma to_expr_typed S S' Δl ce e τlr :
  to_expr Δl ce S = mret (M := M) (e,τlr) S' → ✓ S → local_env_valid S Δl →
  (to_env S','{to_mem S'},to_local_types Δl) ⊢ e : τlr
  ∧ locks e = ∅ ∧ ✓ S' ∧ S ⊆ S'.
Proof. intros. eapply to_expr_type_typed; eauto. Qed.
Lemma to_init_expr_typed S S' Δl ci e τ :
  to_init_expr Δl τ ci S = mret (M := M) e S' →
  ✓ S → local_env_valid S Δl → ✓{to_env S} τ →
  (to_env S','{to_mem S'},to_local_types Δl) ⊢ e : inr τ
  ∧ locks e = ∅ ∧ ✓ S' ∧ S ⊆ S'.
Proof. intros. eapply to_expr_type_typed; eauto. Qed.
Lemma to_type_valid S S' Δl k cτ τk :
  to_type k Δl cτ S = mret (M := M) τk S' → ✓ S → local_env_valid S Δl →
  to_type_type_valid (to_env S') τk ∧ ✓ S' ∧ S ⊆ S'.
Proof. eapply to_expr_type_typed; eauto. Qed.

Lemma to_init_val_typed S S' Δl τ ci v :
  to_init_val Δl τ ci S = mret (M := M) v S' → ✓ S → local_env_valid S Δl →
  ✓{to_env S} τ → (to_env S','{to_mem S'}) ⊢ v : τ ∧ ✓ S' ∧ S ⊆ S'.
Proof.
  unfold to_init_val; intros. error_proceed e as S2; error_proceed [|v'] as S3.
  destruct (to_init_expr_typed S S' Δl ci e τ) as (?&?&?&?); split_and ?; auto.
  eapply rval_typed_inv, (expr_eval_typed_aux _ _ (to_local_types Δl));
    eauto using type_valid_ptr_type_valid, to_init_expr_typed,
    prefix_nil, Forall2_nil.
Qed.
Lemma alloc_global_typed S S' Δl x sto cτ mci d :
  alloc_global Δl x sto cτ mci S = mret (M := M) d S' →
  ✓ S → local_env_valid S Δl →
  local_decl_valid S' x (Extern d) ∧ ✓ S' ∧ S ⊆ S'.
Proof.
  unfold alloc_global; generalize_errors; intros; error_proceed τ' as S2.
  destruct (to_type_valid S S2 Δl to_Ptr cτ τ') as (?&?&?); auto; weaken.
  destruct (_ !! x)
    as [[sto' o' τ'' init|sto' τs' τ ms| |]|] eqn:?; error_proceed.
  * destruct (to_globals_lookup S2 x (Global sto' o' τ'' init)); auto.
    destruct mci as [ci|]; error_proceed; auto.
    error_proceed [] as S3; error_proceed v as S4; error_proceed [] as S5.
    destruct (insert_global_decl_valid S2 S3 x (Global sto o' τ'' true))
      as (?&?&?); weaken; auto; [naive_solver|].
    destruct (to_init_val_typed S3 S4 Δl τ'' ci v) as (?&?&?); auto; weaken.
    destruct (update_object_valid S4 S' o' perm_full v τ''); weaken; eauto 10.
  * error_proceed [] as S3.
    destruct (to_globals_lookup S2 x (Fun sto' τs' τ ms)); auto.
    destruct (insert_fun_valid S2 S' x sto τs' τ ms); weaken; auto.
  * destruct τ' as [τ| |τs τ] eqn:?; error_proceed.
    + destruct mci as [ci|]; error_proceed.
      { error_proceed o' as S3; error_proceed [] as S4;
          error_proceed v as S5; error_proceed [] as S6.
        destruct (insert_object_valid S2 S3 o' (val_new (to_env S2) τ)
          perm_full τ) as (?&?&?&?&?); auto using val_new_typed; weaken.
        destruct (insert_global_decl_valid S3 S4 x (Global sto o' τ true))
          as (?&?&?); weaken; auto with congruence.
        destruct (to_init_val_typed S4 S5 Δl τ ci v) as (?&?&?); auto; weaken.
        destruct (update_object_valid S5 S' o' perm_full v τ); weaken; auto 9. }
      error_proceed o' as S3; error_proceed [] as S4.
      destruct (insert_object_valid S2 S3 o' (val_0 (to_env S2) τ) perm_full τ)
        as (?&?&?&?&?); auto using val_0_typed; weaken.
      destruct (insert_global_decl_valid S3 S' x (Global sto o' τ false))
        as (?&?&?); weaken; auto with congruence.
    + error_proceed [] as S3; weaken.
      destruct (insert_fun_None_valid S2 S' x sto τs τ) as (?&[]); weaken; auto.
Qed.
Lemma alloc_static_typed S S' Δl x cτ mci o τ :
  alloc_static Δl x cτ mci S = mret (M := M) (o,τ) S' →
  ✓ S → local_env_valid S Δl → '{to_mem S'} ⊢ o : τ ∧ ✓ S' ∧ S ⊆ S'.
Proof.
  unfold alloc_static; generalize_errors; intros; error_proceed τ' as S2.
  destruct (to_type_valid S S2 Δl to_Type cτ τ') as (?&?&?); auto.
  destruct mci as [ci|]; error_proceed; auto.
  { error_proceed ? as S3; error_proceed v as S4; error_proceed [] as S5.
    destruct (insert_object_valid S2 S3 o (val_new (to_env S2) τ) perm_full τ)
      as (?&?&?&?&?); auto using val_new_typed; weaken.
    destruct (to_init_val_typed S3 S4 (Some (x, Extern (inl (o,τ))) :: Δl)
      τ ci v) as (?&?&?); auto; weaken.
    destruct (update_object_valid S4 S' o perm_full v τ); weaken; auto 10. }
  error_proceed o' as S3.
  destruct (insert_object_valid S2 S' o' (val_0 (to_env S2) τ') perm_full τ')
    as (?&?&?&?&?); auto using val_0_typed; weaken.
Qed.
Hint Immediate cast_typed_type_valid: core.
Hint Extern 0 (_ !! 0 = _) => reflexivity: core.
Definition rettype_match_aux (cmσ : rettype K) (σ : type K) : Prop :=
  match cmσ with (_, Some σ') => σ' = σ | (_, None) => True end.
Notation break_continue := (option nat * option nat)%type.
Definition break_continue_max (bc : break_continue) :=
  match bc with
  | (Some n, Some n') => S (n + n')
  | (Some n, None) | (None, Some n) => S n
  | (None, None) => 0
  end.
Arguments break_continue_max !_ /.
Lemma to_stmt_typed S S' Δl τ bc cs s cmτ :
  to_stmt τ bc Δl cs S = mret (M := M) (s,cmτ) S' → ✓ S → local_env_valid S Δl →
  ✓{to_env S} (TType τ) →
  (to_env S','{to_mem S'},to_local_types Δl) ⊢ s : cmτ
  ∧ rettype_match_aux cmτ  τ ∧ throws_valid (break_continue_max bc) s
  ∧ ✓ S' ∧ S ⊆ S'.
Proof.
  revert S S' bc Δl s cmτ.
  induction cs; intros; generalize_errors; intros;
    repeat match goal with
    | x : (expr _ * _)%type |- _ => destruct x
    | x : rettype _ |- _ => destruct x
    | H : rettype_union_alt _ _ = _ |- _ =>
       apply rettype_union_alt_sound in H; inversion H
    | IH : ∀ _ _ _ _ _ _, _ = _ → _, H : _ = _ |- _ =>
       destruct (IH _ _ _ _ _ _ H) as (?&?&?&?&?); eauto 2; [clear IH H]; weaken
    | H : to_expr _ _ _ = _ |- _ =>
       apply to_expr_typed in H; eauto 2; [destruct H as (?&?&?&?)]; weaken
    | H : to_init_expr _ _ _ _ = _ |- _ =>
       apply to_init_expr_typed in H; eauto 2; [destruct H as (?&?&?&?)]; weaken
    | H : to_type ?k _ _ _ = _ |- _ =>
       apply (to_type_valid _ _ _ k) in H;
         eauto 2; [destruct H as (?&?&?)]; weaken
    | H : alloc_static _ _ _ _ _ = _ |- _ =>
       apply alloc_static_typed in H; eauto 2; [destruct H as (?&?&?)]; weaken
    | H : alloc_global _ _ _ _ _ _ = _ |- _ =>
       apply alloc_global_typed in H; eauto 2; [destruct H as (?&?&?)]; weaken
    | H : to_R_NULL _ _ _ _ = _ |- _ =>
       eapply to_R_NULL_typed in H; eauto; [destruct H as (?&?&->)]; weaken
    | H : to_R _ _ _ = _ |- _ =>
       eapply to_R_typed in H; eauto 2; [destruct H as (?&?&->)]; weaken
    | _ => progress simplify_error_equality || case_match
    end; split_and ?;
      try match goal with
      | |- context [ break_continue_max ?bc ] =>
         destruct bc as [[] []]; simplify_equality';
          eauto 2 using throws_valid_weaken with lia
      end; eauto 20 using SLocal_typed.
Qed.
Lemma stmt_fix_return_typed Γ Δ f τs σ s cmτ s' cmτ' :
  ✓ Γ → ✓{Γ}* τs → ✓{Γ} σ → stmt_fix_return Γ f σ s cmτ = (s',cmτ') →
  (Γ,Δ,τs) ⊢ s : cmτ → rettype_match_aux cmτ σ → throws_valid 0 s →
  (Γ,Δ,τs) ⊢ s' : cmτ' ∧ rettype_match cmτ' σ ∧ throws_valid 0 s'.
Proof.
  intros. assert (✓{Γ} (false,Some σ)) by eauto using stmt_typed_type_valid.
  destruct cmτ as [[][τ|]]; simplify_option_eq; eauto 10.
Qed.
Lemma to_fun_stmt_typed S S' f mys τs σ cs s :
  to_fun_stmt f mys τs σ cs S = mret (M := M) s S' → ✓ S →
  ✓{to_env S} σ → ✓{to_env S}* τs → length mys = length τs → ∃ cmτ,
  (**i 1.) *) (to_env S','{to_mem S'},τs) ⊢ s : cmτ ∧
  (**i 2.) *) rettype_match cmτ σ ∧
  (**i 3.) *) gotos s ⊆ labels s ∧
  (**i 4.) *) throws_valid 0 s ∧
  (**i 5.) *) ✓ S' ∧ S ⊆ S'.
Proof.
  unfold to_fun_stmt; generalize_errors; intros.
  destruct (mapM id mys) as [ys|] eqn:?; error_proceed.
  assert (length ys = length τs) by (by erewrite <-mapM_length by eauto).
  error_proceed [s' cmτ'] as S2.
  destruct (stmt_fix_return _ _ _ s' _) as [? cmτ] eqn:?; error_proceed.
  destruct (to_stmt_typed S S' (zip_with (λ y τ, Some (y, Local τ)) ys τs)
    σ (None,None) cs s' cmτ') as (Hs&?&?&?&?);
    eauto using local_env_valid_params; weaken.
  rewrite to_local_types_params in Hs by done.
  destruct (stmt_fix_return_typed (to_env S') '{to_mem S'}
    f τs σ s' cmτ' s cmτ) as (?&?&?); eauto 10.
Qed.
Lemma alloc_fun_valid S S' f sto cτ cs :
  alloc_fun f sto cτ cs S = mret (M := M) () S' → ✓ S → ✓ S' ∧ S ⊆ S'.
Proof.
  unfold alloc_fun; generalize_errors; intros.
  error_proceed [cτs cτ'] as ?; error_proceed [xτs τ] as S2.
  destruct (to_fun_type_valid S S2 [] cτs cτ' xτs τ)
    as (?&?&?&?); eauto using Forall_true, to_type_valid.
  destruct (_ !! f) as [[|sto' τs' σ' ms| |]|] eqn:?; error_proceed.
  { error_proceed s as S3.
    destruct (to_globals_lookup S2 f (Fun sto' (xτs.*2) τ None)); auto.
    destruct (to_fun_stmt_typed S2 S3 f (xτs.*1) (xτs.*2) τ cs s)
      as (cmτ&?&?&?&?&?&?); rewrite ?fmap_length; eauto; weaken.
    edestruct (λ sto, insert_fun_valid S3 S' f sto
      (xτs.*2) τ (Some s)); eauto; weaken; eauto 20. }
  error_proceed [] as S3; error_proceed s as S4.
  destruct (insert_fun_None_valid S2 S3 f sto (xτs.*2) τ)
    as (?&?&?); auto; weaken.
  destruct (to_fun_stmt_typed S3 S4 f (xτs.*1) (xτs.*2) τ cs s)
    as (?&?&?&?&?&?&?); rewrite ?fmap_length;
    eauto using types_complete_valid, types_complete_weaken; weaken.
  destruct (insert_fun_valid S4 S' f sto (xτs.*2) τ (Some s));
    auto; weaken; eauto 20.
Qed.
Lemma alloc_enum_valid S S' yces τi z :
  alloc_enum yces τi z S = mret (M := M) () S' → ✓ S → ✓ S' ∧ S ⊆ S'.
Proof.
  revert S z. induction yces as [|[x [ce|]] yces IH];
    intros S z ??; error_proceed; auto.
  * error_proceed [e τe] as S2; error_proceed [?|[[| |τi' z'| |]| | | |]] as ?.
    error_proceed () as S3.
    destruct (to_expr_typed S S2 [] ce e τe) as (?&?&?&?); auto; weaken.
    destruct (insert_global_decl_valid S2 S3 x (EnumVal τi z'))
      as (?&?&?); auto with congruence; weaken.
    destruct (IH S3 (z' + 1)%Z); auto.
  * error_proceed () as S2.
    destruct (insert_global_decl_valid S S2 x (EnumVal τi z))
      as (?&?&?); auto with congruence; weaken.
    destruct (IH S2 (z + 1)%Z); auto.
Qed.
Lemma to_compound_fields_valid S S' t cτs xτs :
  to_compound_fields t cτs S = mret (M := M) xτs S' → ✓ S →
  ✓{to_env S'}* (xτs.*2) ∧ ✓ S' ∧ S ⊆ S'.
Proof.
  revert S xτs.
  induction cτs as [|[x cτ] cτs IH]; intros S xτs ??; error_proceed; auto.
  error_proceed τ as S2; error_proceed xτs' as ?.
  destruct (to_type_valid S S2 [] to_Type cτ τ) as (?&?&?); auto; weaken.
  destruct (IH S2 xτs') as (?&?&?); weaken; auto.
Qed.
Lemma alloc_decls_valid S S' Θ :
  alloc_decls Θ S = mret (M := M) () S' → ✓ S → ✓ S' ∧ S ⊆ S'.
Proof.
  revert S. induction Θ as
    [|[x [c cτs|cτi yces|cτ|stos cτ mci|stos cτ mcs]] Θ IH];
    intros S ??; error_proceed; auto.
  * error_proceed xτs as S2; error_proceed () as S3.
    destruct (to_compound_fields_valid S S2 x cτs xτs) as (?&?&?); auto; weaken.
    destruct (insert_compound_valid S2 S3 c x xτs)as (?&?&?); auto; weaken.
    destruct (IH S3); auto.
  * error_proceed () as S2; error_proceed () as S3.
    destruct (insert_enum_valid S S2 x (to_inttype cτi)); auto.
    destruct (alloc_enum_valid S2 S3 yces (to_inttype cτi) 0); auto.
    destruct (IH S3); auto.
  * error_proceed τp as S2; error_proceed () as S3.
    destruct (to_type_valid S S2 [] to_Ptr cτ τp) as (?&?&?); auto.
    destruct (insert_global_decl_valid S2 S3 x (GlobalTypeDef τp))
      as (?&?&?); auto with congruence.
    destruct (IH S3); auto.
  * error_proceed sto as ?; error_proceed d as S2.
    destruct (alloc_global_typed S S2 [] x sto cτ mci d)as (?&?&?); auto.
    destruct (IH S2); auto.
  * error_proceed sto as ?; error_proceed () as S2.
    destruct (alloc_fun_valid S S2 x sto cτ mcs); auto.
    destruct (IH S2); auto.
Qed.
Lemma alloc_program_valid S Θ :
  alloc_program Θ ∅ = mret (M := M) () S →
  (**i 1.) *) ✓ (to_env S) ∧
  (**i 2.) *) ✓{to_env S,'{to_mem S}} (to_funenv S) ∧
  (**i 3.) *) ✓{to_env S} (to_mem S).
Proof.
  unfold alloc_program; intros; error_proceed () as ?.
  destruct (alloc_decls_valid ∅ S Θ) as [? _];
    eauto using to_funenv_typed, frontend_state_empty_valid.
Qed.
End properties.
