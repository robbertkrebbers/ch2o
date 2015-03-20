(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file defines a denotational semantics [⟦ _ ⟧] for pure expressions as
an expression evaluator. It is parametrized by a map of function names to
denotations. We use this to enable convenient reasoning about pure functions
in our axiomatic semantics. *)
Require Export expressions type_system.
Local Open Scope expr_scope.

(** The type [purefun] represents denotations of pure functions. *)
Definition purefun K := list (val K) → option (val K).
Notation purefuns K := (funmap (purefun K)).

Instance purefuns_valid `{Env K} :
    Valid (env K * memenv K) (purefuns K) := λ ΓΔ,
  map_Forall (λ f F, ∃ τs τ,
    ΓΔ.1 !! f = Some (τs,τ) ∧
    ∀ vs v, F vs = Some v → ΓΔ ⊢* vs :* τs → ΓΔ ⊢ v : τ
  ).

(** * Definition of the semantics *)
Reserved Notation "⟦ e ⟧" (format "⟦  e  ⟧").

Fixpoint expr_eval `{Env K} (e : expr K) (Γ : env K)
    (fs : purefuns K) (ρ : stack K) (m : mem K) : option (lrval K) :=
  match e with
  | var x =>
     '(o,τ) ← ρ !! x;
     Some (inl (addr_top o τ))
  | %#{Ω} ν => guard (Ω = ∅); Some ν
  | .* e =>
     v ← ⟦ e ⟧ Γ fs ρ m ≫= maybe inr;
     a ← maybe (VBase ∘ VPtr ∘ Ptr) v;
     guard (index_alive' m (addr_index a));
     Some (inl a)
  | & e =>
     a ← ⟦ e ⟧ Γ fs ρ m ≫= maybe inl;
     Some (inr (ptrV (Ptr a)))
  | load e =>
     a ← ⟦ e ⟧ Γ fs ρ m ≫= maybe inl;
     guard (mem_forced Γ a m);
     inr <$> m !!{Γ} a
  | e %> rs =>
     a ← ⟦ e ⟧ Γ fs ρ m ≫= maybe inl;
     guard (addr_strict Γ a);
     Some (inl (addr_elt Γ rs a))
  | e #> rs =>
     v ← ⟦ e ⟧ Γ fs ρ m ≫= maybe inr;
     v' ← v !!{Γ} rs;
     Some (inr v')
  | @{op} e =>
     v ← ⟦ e ⟧ Γ fs ρ m ≫= maybe inr;
     guard (val_unop_ok m op v);
     Some (inr (val_unop op v))
  | e1 @{op} e2 =>
     v1 ← ⟦ e1 ⟧ Γ fs ρ m ≫= maybe inr;
     v2 ← ⟦ e2 ⟧ Γ fs ρ m ≫= maybe inr;
     guard (val_binop_ok Γ m op v1 v2);
     Some (inr (val_binop Γ op v1 v2))
  | call e @ es =>
     p ← ⟦ e ⟧ Γ fs ρ m ≫= maybe (inr ∘ VBase ∘ VPtr);
     '(f,_,_) ← maybe3 FunPtr p;
     F ← fs !! f;
     vs ← mapM (λ e, ⟦ e ⟧ Γ fs ρ m ≫= maybe inr) es;
     inr <$> F vs
  | if{e1} e2 else e3 =>
     vb ← ⟦ e1 ⟧ Γ fs ρ m ≫= maybe (inr ∘ VBase);
     guard (base_val_branchable m vb);
     if decide (base_val_is_0 vb) then ⟦ e3 ⟧ Γ fs ρ m else ⟦ e2 ⟧ Γ fs ρ m
  | e1 ,, e2 =>
     _ ← ⟦ e1 ⟧ Γ fs ρ m; ⟦ e2 ⟧ Γ fs ρ m
  | cast{τ} e =>
     v ← ⟦ e ⟧ Γ fs ρ m ≫= maybe inr;
     guard (val_cast_ok Γ m (TType τ) v);
     Some (inr (val_cast (TType τ) v))
  | #[r:=e1] e2 =>
     v1 ← ⟦ e1 ⟧ Γ fs ρ m ≫= maybe inr;
     v2 ← ⟦ e2 ⟧ Γ fs ρ m ≫= maybe inr;
     guard (is_Some (v2 !!{Γ} r));
     Some (inr (val_alter Γ (λ _, v1) r v2))
  | _ => None
  end
where "⟦ e ⟧" := (expr_eval e) : C_scope.

(** * Theorems *)
Section expression_eval.
Context `{EnvSpec K}.
Implicit Types Δ : memenv K.
Implicit Types e : expr K.
Implicit Types a : addr K.
Implicit Types v : val K.
Implicit Types ν : lrval K.
Implicit Types E : ectx K.

Hint Extern 0 (_ ⊢ _ : _) => typed_constructor.

Section expr_eval_ind.
Context (Γ : env K) (fs : purefuns K) (ρ : stack K) (m : mem K).
Context (P : expr K → lrval K → Prop).
Context (Pvar : ∀ τ x o, ρ !! x = Some (o,τ) → P (var x) (inl (addr_top o τ))).
Context (Pval : ∀ ν, P (%# ν) ν).
Context (Prtol : ∀ e a,
  ⟦ e ⟧ Γ fs ρ m = Some (inr (ptrV (Ptr a))) → P e (inr (ptrV (Ptr a))) →
  index_alive' m (addr_index a) → P (.* e) (inl a)).
Context (Profl : ∀ e a,
  ⟦ e ⟧ Γ fs ρ m = Some (inl a) → P e (inl a) → P (&e) (inr (ptrV (Ptr a)))).
Context (Peltl : ∀ e rs a,
  ⟦ e ⟧ Γ fs ρ m = Some (inl a) → P e (inl a) → addr_strict Γ a →
  P (e %> rs) (inl (addr_elt Γ rs a))).
Context (Pload : ∀ e a v,
  ⟦ e ⟧ Γ fs ρ m = Some (inl a) → P e (inl a) → mem_forced Γ a m →
  m !!{Γ} a = Some v → P (load e) (inr v)).
Context (Peltr : ∀ e rs v v',
  ⟦ e ⟧ Γ fs ρ m = Some (inr v) → P e (inr v) →
  v !!{Γ} rs = Some v' → P (e #> rs) (inr v')).
Context (Punop : ∀ op e v,
  ⟦ e ⟧ Γ fs ρ m = Some (inr v) → P e (inr v) →
  val_unop_ok m op v → P (@{op} e) (inr (val_unop op v))).
Context (Pbinop : ∀ op e1 e2 v1 v2,
  ⟦ e1 ⟧ Γ fs ρ m = Some (inr v1) → P e1 (inr v1) →
  ⟦ e2 ⟧ Γ fs ρ m = Some (inr v2) → P e2 (inr v2) →
  val_binop_ok Γ m op v1 v2 →
  P (e1 @{op} e2) (inr (val_binop Γ op v1 v2))).
Context (Pcall : ∀ e f τs τ F es vs v,
  ⟦ e ⟧ Γ fs ρ m = Some (inr (ptrV (FunPtr f τs τ))) →
  P e (inr (ptrV (FunPtr f τs τ))) →
  fs !! f = Some F →
  Forall2 (λ e v, ⟦ e ⟧ Γ fs ρ m = Some (inr v)) es vs →
  Forall2 (λ e v, P e (inr v)) es vs →
  F vs = Some v → P (call e @ es) (inr v)).
Context (Pif1 : ∀ e1 e2 e3 vb ν2,
  ⟦ e1 ⟧ Γ fs ρ m = Some (inr (VBase vb)) → P e1 (inr (VBase vb)) →
  ⟦ e2 ⟧ Γ fs ρ m = Some ν2 → P e2 ν2 →
  base_val_branchable m vb → ¬base_val_is_0 vb → P (if{e1} e2 else e3) ν2).
Context (Pif2 : ∀ e1 e2 e3 vb ν3,
  ⟦ e1 ⟧ Γ fs ρ m = Some (inr (VBase vb)) → P e1 (inr (VBase vb)) →
  ⟦ e3 ⟧ Γ fs ρ m = Some ν3 → P e3 ν3 →
  base_val_branchable m vb → base_val_is_0 vb → P (if{e1} e2 else e3) ν3).
Context (Pcomma : ∀ e1 e2 ν1 ν2,
  ⟦ e1 ⟧ Γ fs ρ m = Some ν1 → P e1 ν1 →
  ⟦ e2 ⟧ Γ fs ρ m = Some ν2 → P e2 ν2 → P (e1,, e2) ν2).
Context (Pcast : ∀ τ e v,
  ⟦ e ⟧ Γ fs ρ m = Some (inr v) → P e (inr v) →
  val_cast_ok Γ m (TType τ) v → P (cast{τ} e) (inr (val_cast (TType τ) v))).
Context (Pinsert : ∀ r e1 e2 v1 v2,
  ⟦ e1 ⟧ Γ fs ρ m = Some (inr v1) → P e1 (inr v1) →
  ⟦ e2 ⟧ Γ fs ρ m = Some (inr v2) → P e2 (inr v2) → is_Some (v2 !!{Γ} r) →
  P (#[r:=e1] e2) (inr (val_alter Γ (λ _, v1) r v2))).
Lemma expr_eval_ind : ∀ e ν, ⟦ e ⟧ Γ fs ρ m = Some ν → P e ν.
Proof.
  assert (∀ e f τs τ F es vs v,
    ⟦ e ⟧ Γ fs ρ m = Some (inr (ptrV (FunPtr f τs τ))) →
    P e (inr (ptrV (FunPtr f τs τ))) →
    Forall (λ e, ∀ ν, ⟦ e ⟧ Γ fs ρ m = Some ν → P e ν) es →
    mapM (λ e, ⟦ e ⟧ Γ fs ρ m ≫= maybe inr) es = Some vs →
    fs !! f = Some F → F vs = Some v → P (call e @ es) (inr v)).
  { intros e f τs τ F es vs v ?? Hes Hvs Hf Hv. apply mapM_Some in Hvs.
    eapply Pcall; eauto; clear Hf Hv; induction Hvs;
      decompose_Forall_hyps; simplify_option_equality; eauto. }
  induction e using @expr_ind_alt; intros;
    repeat first [progress simplify_option_equality | case_match]; eauto.
Qed.
End expr_eval_ind.

Lemma purefuns_empty_valid Γ Δ : ✓{Γ,Δ} ∅.
Proof. done. Qed.
Lemma purefuns_valid_lookup Γ Δ fs f F vs v τs τ :
  ✓{Γ,Δ} fs → fs !! f = Some F → Γ !! f = Some (τs,τ) →
  F vs = Some v → (Γ,Δ) ⊢* vs :* τs → (Γ,Δ) ⊢ v : τ.
Proof.
  intros Hfs ???.
  destruct (Hfs f F) as (τ'&?&?&?); simplify_option_equality; eauto.
Qed.
Lemma EVal_expr_eval Γ fs ρ m v : ⟦ #v ⟧ Γ fs ρ m = Some (inr v).
Proof. done. Qed.
Lemma EVals_expr_eval Γ fs ρ m Ωs vs :
  length Ωs = length vs →
  ⋃ Ωs = ∅ → mapM (λ e, ⟦ e ⟧ Γ fs ρ m ≫= maybe inr) (#{Ωs}* vs) = Some vs.
Proof.
  rewrite empty_union_list_L. rewrite <-Forall2_same_length.
  induction 1; intros; decompose_Forall; simplify_option_equality; auto.
Qed.
Lemma Forall2_expr_eval_val_inv Γ fs ρ m Ωs vs vs' :
  length Ωs = length vs →
  Forall2 (λ e v, ⟦ e ⟧ Γ fs ρ m ≫= maybe inr = Some v) (#{Ωs}* vs) vs' →
  vs = vs'.
Proof.
  rewrite <-Forall2_same_length. intros HΩvs. revert vs'.
  induction HΩvs; simpl; intros; decompose_Forall;
    simplify_option_equality; f_equal; eauto.
Qed.
Lemma expr_eval_typed_aux Γ Δ τs fs ρ m e ν τlr :
  ✓ Γ → ✓{Γ,Δ} m → ⟦ e ⟧ Γ fs ρ m = Some ν → ✓{Γ,Δ} fs → ✓{Δ}* ρ →
  ρ.*2 `prefix_of` τs → (Γ,Δ,τs) ⊢ e : τlr → (Γ,Δ) ⊢ ν : τlr.
Proof.
  intros ?? Hν Hfs ? [τs' ->] He. revert e ν Hν τlr He. assert (∀ es vs σs,
    Forall2 (λ e v, ∀ τlr,
      (Γ,Δ,ρ.*2 ++ τs') ⊢ e : τlr → (Γ,Δ) ⊢ inr v : τlr) es vs →
    (Γ,Δ,ρ.*2 ++ τs') ⊢* es :* inr <$> σs → (Γ,Δ) ⊢* vs :* σs).
  { intros es vs σs Hes. revert σs.
    induction Hes; intros [|??] ?; decompose_Forall_hyps;
      repeat match goal with
      | _ => progress typed_inversion_all
      | H : _ ⊢ ?e : _, H2 : ∀ _, _ ⊢ ?e : _  → _ |- _ => specialize (H2 _ H)
      end; constructor; eauto. }
  apply (expr_eval_ind Γ fs ρ m (λ e _, ∀ τlr, _ ⊢ e : τlr → (_:Prop))); intros;
    repeat match goal with
    | _ => progress typed_inversion_all
    | _ => progress decompose_Forall_hyps
    | H : (?ρ.*2 ++ ?τs) !! ?i = Some ?τ1, H2 : ?ρ !! _ = Some (_,?τ2) |- _ =>
      assert ((ρ.*2 ++ τs) !! i = Some τ) by
        (apply lookup_app_l_Some; by rewrite list_lookup_fmap, H2)
    | H : _ ⊢ ?e : _, H2 : ∀ _, _ ⊢ ?e : _  → _ |- _ => specialize (H2 _ H)
    end; try typed_constructor; eauto using
      val_unop_typed, val_binop_typed, val_cast_typed, addr_top_typed,
      cmap_index_typed_valid, addr_top_strict,
      addr_elt_typed, addr_elt_strict, addr_elt_typed, addr_elt_strict,
      val_lookup_seg_typed, val_alter_const_typed, mem_lookup_typed.
  eapply purefuns_valid_lookup; eauto.
Qed.
Lemma expr_eval_typed Γ Δ fs ρ m e ν τlr :
  ✓ Γ → ✓{Γ,Δ} m → ⟦ e ⟧ Γ fs ρ m = Some ν → ✓{Γ,Δ} fs → ✓{Δ}* ρ →
  (Γ,Δ,ρ.*2) ⊢ e : τlr → (Γ,Δ) ⊢ ν : τlr.
Proof. intros. eapply expr_eval_typed_aux; eauto. Qed.

Lemma expr_eval_weaken Γ1 Γ2 Δ1 fs ρ1 ρ2 m1 m2 e ν τlr :
  ✓ Γ1 → ✓{Γ1,Δ1} m1 → ✓{Γ1,Δ1} fs → ✓{Δ1}* ρ1 →
  (Γ1,Δ1,ρ1.*2) ⊢ e : τlr → ⟦ e ⟧ Γ1 fs ρ1 m1 = Some ν → Γ1 ⊆ Γ2 →
  (∀ o, index_alive ('{m1}) o → index_alive ('{m2}) o) →
  (∀ a v σ, (Γ1,Δ1) ⊢ a : TType σ →
    m1 !!{Γ1} a = Some v → m2 !!{Γ2} a = Some v) →
  (∀ a σ, (Γ1,Δ1) ⊢ a : TType σ →
    mem_forced Γ1 a m1 → is_Some (m1 !!{Γ1} a) → mem_forced Γ2 a m2) →
  ρ1 `prefix_of` ρ2 → ⟦ e ⟧ Γ2 fs ρ2 m2 = Some ν.
Proof.
  intros ???? He Hν ???? [ρ3 ->].
  revert Hν τlr He. assert (∀ es vs σs,
    Forall2 (λ e v, ∀ τlr, (Γ1,Δ1,ρ1.*2) ⊢ e : τlr →
      ⟦ e ⟧ Γ2 fs (ρ1 ++ ρ3) m2 = Some (inr v)) es vs →
    (Γ1,Δ1,ρ1.*2) ⊢* es :* inr <$> σs →
    mapM (λ e, ⟦ e ⟧ Γ2 fs (ρ1 ++ ρ3) m2 ≫= maybe inr) es = Some vs). 
  { intros es vs σs Hes Hes'. apply mapM_Some. revert σs Hes'.
    induction Hes; intros [|??] ?; decompose_Forall_hyps; constructor;
      simplify_option_equality; eauto. }
  revert e ν. apply (expr_eval_ind Γ1 fs ρ1 m1
    (λ e _, ∀ τlr, _ ⊢ e : τlr → (_:Prop))); simpl; intros; typed_inversion_all;
    repeat match goal with
    | H: ⟦ ?e ⟧ Γ1 fs ρ1 m1 = Some ?ν,  _: (Γ1,Δ1,ρ1.*2) ⊢ ?e : ?τlr |- _ =>
      feed pose proof (expr_eval_typed Γ1 Δ1 fs ρ1 m1 e ν τlr); auto;
      clear H
    end; typed_inversion_all; auto.
  * rewrite lookup_app_l by eauto using lookup_lt_Some.
    by simplify_option_equality.
  * by simplify_option_equality by eauto using index_alive_1', index_alive_2'.
  * by simplify_option_equality.
  * simplify_option_equality by eauto using addr_strict_weaken.
    by erewrite <-addr_elt_weaken by eauto.
  * by simplify_option_equality.
  * by simplify_option_equality by eauto using val_lookup_seg_weaken.
  * by simplify_option_equality by eauto using val_unop_ok_weaken.
  * simplify_option_equality by eauto using val_binop_ok_weaken.
    by erewrite <-val_binop_weaken by eauto.
  * by simplify_option_equality.
  * simplify_option_equality by eauto using base_val_branchable_weaken; eauto.
  * simplify_option_equality by eauto using base_val_branchable_weaken; eauto.
  * simplify_option_equality; eauto.
  * by simplify_option_equality by eauto using val_cast_ok_weaken.
  * simplify_option_equality by eauto using val_lookup_weaken_is_Some.
    by erewrite <-val_alter_weaken by eauto.
Qed.
Lemma expr_eval_weaken_empty Γ1 Γ2 Δ1 fs ρ1 ρ2 e ν τlr :
  ✓ Γ1 → ✓{Γ1} Δ1 → ✓{Γ1,Δ1} fs → ✓{Δ1}* ρ1 →
  (Γ1,Δ1,ρ1.*2) ⊢ e : τlr → ⟦ e ⟧ Γ1 fs ρ1 ∅ = Some ν → Γ1 ⊆ Γ2 →
  ρ1 `prefix_of` ρ2 → ⟦ e ⟧ Γ2 fs ρ2 ∅ = Some ν.
Proof.
  intros; eapply expr_eval_weaken; eauto using cmap_empty_valid;
    by intros until 0; rewrite mem_lookup_empty, <-?not_eq_None_Some.
Qed.
Lemma expr_eval_erase Γ fs ρ m e : ⟦ e ⟧ Γ fs ρ (cmap_erase m) = ⟦ e ⟧ Γ fs ρ m.
Proof.
  destruct e using @expr_ind_alt; simpl;
    repeat match goal with
    | H : ⟦ _ ⟧ _ _ _ _ = _ |- _ => rewrite H
    | H : appcontext [index_alive'] |- _ => rewrite index_alive_erase' in H
    | H : appcontext [base_val_branchable] |- _ => rewrite base_val_branchable_erase in H
    | H : appcontext [val_unop_ok] |- _ => rewrite val_unop_ok_erase in H
    | H : appcontext [val_binop_ok] |- _ => rewrite val_binop_ok_erase in H
    | H : appcontext [val_cast_ok] |- _ => rewrite val_cast_ok_erase in H
    | H : appcontext [mem_forced] |- _ => rewrite mem_forced_erase in H
    | _ => apply option_bind_ext_fun; intros
    | _ => case_option_guard; try done
    | _ => rewrite mem_lookup_erase
    | _ => case_match
    end; try done.
  apply option_bind_ext; auto.
  apply Forall_mapM_ext; decompose_Forall; f_equal'; auto.
Qed.

(** Pure expressions without variables do not refer to the stack, so their
semantics is preserved under changes to the stack. *)
Lemma expr_eval_var_free Γ fs ρ1 ρ2 m e :
  vars e = ∅ → ⟦ e ⟧ Γ fs ρ1 m = ⟦ e ⟧ Γ fs ρ2 m.
Proof.
  induction e using expr_ind_alt; simpl; intro; decompose_empty; repeat
    match goal with
    | H : vars _ = ∅ → ⟦ _ ⟧ _ _ _ _ = _ |- _ => rewrite H
    | H : ⋃ _ = ∅ |- _ => rewrite empty_union_list_L in H
    | _ => done
    end.
  apply option_bind_ext_fun; intros [| |f τs τ]; simpl; auto.
  apply option_bind_ext_fun; intros F.
  f_equal; apply Forall_mapM_ext. decompose_Forall; f_equal'; auto.
Qed.

(** Lifting DeBruijn indexes distributes over expression evaluation. *)
Lemma expr_eval_lift Γ fs ρ m e : ⟦ e↑ ⟧ Γ fs ρ m = ⟦ e ⟧ Γ fs (tail ρ) m.
Proof.
  induction e using expr_ind_alt; intros; simpl; repeat
    match goal with
    | H : ⟦ _↑ ⟧ _ _ _ _ = _ |- _ => rewrite H
    end; rewrite <-?lookup_tail; auto.
  apply option_bind_ext_fun; intros [| |f τs τ]; simpl; auto.
  destruct (fs !! _); simpl; [|done].
  f_equal. apply Forall2_mapM_ext. by decompose_Forall; f_equal'.
Qed.

(** The semantics is preserved under substitution. *)
Lemma subst_preserves_expr_eval Γ fs ρ m E e1 e2 :
  ⟦ e1 ⟧ Γ fs ρ m = ⟦ e2 ⟧ Γ fs ρ m →
  ⟦ subst E e1 ⟧ Γ fs ρ m = ⟦ subst E e2 ⟧ Γ fs ρ m.
Proof.
  intros. induction E as [|E' ? IH] using rev_ind; [done |].
  destruct E'; rewrite ?subst_snoc; simpl; rewrite ?IH; auto.
  apply option_bind_ext_fun; intros [| |f τs τ]; simpl; auto.
  destruct (fs !! _); simpl; [|done].
  f_equal. apply Forall2_mapM_ext. by decompose_Forall; f_equal'.
Qed.

(** If an expression has a semantics, then each sub-expression of that
expression has a semantics too. *)
Lemma expr_eval_subst Γ fs ρ m E e ν :
  ⟦ subst E e ⟧ Γ fs ρ m = Some ν ↔
  ∃ ν', ⟦ e ⟧ Γ fs ρ m = Some ν' ∧ ⟦ subst E (%# ν') ⟧ Γ fs ρ m = Some ν.
Proof.
  split; [|by intros (ν'&?&<-); apply subst_preserves_expr_eval].
  revert ν. induction E as [|E' E IH] using rev_ind; simpl; intros ν; eauto.
  setoid_rewrite subst_snoc.
  intros; destruct E';
    repeat match goal with
    | _ => progress simplify_option_equality
    | H : mapM _ _ = Some _ |- _ => apply mapM_Some in H; decompose_Forall_hyps
    | H : ∀ _, Some _ = Some _  → _ |- _ =>
       specialize (H _ eq_refl); destruct H as (?&->&?); eexists; split; eauto
    end; auto.
  erewrite mapM_Some_2
    by (apply Forall2_app, Forall2_cons; simplify_option_equality; eauto).
  by simplify_option_equality.
Qed.
End expression_eval.
