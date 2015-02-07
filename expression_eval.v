(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file defines a denotational semantics [⟦ _ ⟧] for pure expressions as
an expression evaluator. It is parametrized by a map of function names to
denotations. We use this to enable convenient reasoning about pure functions
in our axiomatic semantics. *)
Require Export expressions type_system.
Local Open Scope expr_scope.

(** The type [purefun] represents denotations of pure functions. *)
Definition purefun Ti := list (val Ti) → option (val Ti).
Notation purefuns Ti := (funmap (purefun Ti)).

Instance purefuns_valid `{Env Ti} :
    Valid (env Ti * memenv Ti) (purefuns Ti) := λ ΓΔ,
  map_Forall (λ f F, ∃ τs τ,
    ΓΔ.1 !! f = Some (τs,τ) ∧
    ∀ vs v, F vs = Some v → ΓΔ ⊢* vs :* τs → ΓΔ ⊢ v : τ
  ).

(** * Definition of the semantics *)
Reserved Notation "⟦ e ⟧" (format "⟦  e  ⟧").

Fixpoint expr_eval `{Env Ti} (e : expr Ti) (Γ : env Ti)
    (fs : purefuns Ti) (ρ : stack) (m : mem Ti) : option (addr Ti + val Ti) :=
  match e with
  | var{τ} x =>
     o ← ρ !! x;
     Some (inl (addr_top o τ))
  | #{Ω} v =>
     guard (Ω = ∅); Some (inr v)
  | %{Ω} a =>
     guard (Ω = ∅); Some (inl a)
  | .* e =>
     v ← ⟦ e ⟧ Γ fs ρ m ≫= maybe inr;
     a ← maybe (VBase ∘ VPtr ∘ Ptr) v;
     guard (addr_strict Γ a);
     guard (index_alive' m (addr_index a));
     Some (inl a)
  | & e =>
     a ← ⟦ e ⟧ Γ fs ρ m ≫= maybe inl;
     Some (inr (ptrV (Ptr a)))
  | e %> rs =>
     a ← ⟦ e ⟧ Γ fs ρ m ≫= maybe inl;
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
     v1 ← ⟦ e1 ⟧ Γ fs ρ m ≫= maybe inr;
     match val_true_false_dec m v1 with
     | inleft (left _) => ⟦ e2 ⟧ Γ fs ρ m
     | inleft (right _) => ⟦ e3 ⟧ Γ fs ρ m
     | inright _ => None
     end
  | e1 ,, e2 =>
     _ ← ⟦ e1 ⟧ Γ fs ρ m ≫= maybe inr;
     ⟦ e2 ⟧ Γ fs ρ m
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

Definition lrval_to_expr {Ti} (av : addr Ti + val Ti) : expr Ti :=
  match av with inl a => %a | inr v => #v end.

(** * Theorems *)
Section expression_eval.
Context `{EnvSpec Ti}.
Implicit Types Δ : memenv Ti.
Implicit Types e : expr Ti.
Implicit Types a : addr Ti.
Implicit Types v : val Ti.
Implicit Types av : addr Ti + val Ti.
Implicit Types E : ectx Ti.

Hint Extern 0 (_ ⊢ _ : _) => typed_constructor.

Section expr_eval_ind.
Context (Γ : env Ti) (fs : purefuns Ti) (ρ : stack) (m : mem Ti).
Context (P : expr Ti → addr Ti + val Ti → Prop).
Context (Pvar : ∀ τ x o, ρ !! x = Some o → P (var{τ} x) (inl (addr_top o τ))).
Context (Pval : ∀ v, P (# v) (inr v)).
Context (Paddr : ∀ a, P (% a) (inl a)).
Context (Prtol : ∀ e a,
  ⟦ e ⟧ Γ fs ρ m = Some (inr (ptrV (Ptr a))) → P e (inr (ptrV (Ptr a))) →
  addr_strict Γ a → index_alive' m (addr_index a) → P (.* e) (inl a)).
Context (Profl : ∀ e a,
  ⟦ e ⟧ Γ fs ρ m = Some (inl a) → P e (inl a) → P (&e) (inr (ptrV (Ptr a)))).
Context (Peltl : ∀ e rs a,
  ⟦ e ⟧ Γ fs ρ m = Some (inl a) → P e (inl a) →
  P (e %> rs) (inl (addr_elt Γ rs a))).
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
Context (Pif1 : ∀ e1 e2 e3 v1 av2,
  ⟦ e1 ⟧ Γ fs ρ m = Some (inr v1) → P e1 (inr v1) →
  ⟦ e2 ⟧ Γ fs ρ m = Some av2 → P e2 av2 →
  val_true m v1 → P (if{e1} e2 else e3) av2).
Context (Pif2 : ∀ e1 e2 e3 v1 av3,
  ⟦ e1 ⟧ Γ fs ρ m = Some (inr v1) → P e1 (inr v1) →
  ⟦ e3 ⟧ Γ fs ρ m = Some av3 → P e3 av3 →
  val_false v1 → P (if{e1} e2 else e3) av3).
Context (Pcomma : ∀ e1 e2 v1 av2,
  ⟦ e1 ⟧ Γ fs ρ m = Some (inr v1) → P e1 (inr v1) →
  ⟦ e2 ⟧ Γ fs ρ m = Some av2 → P e2 av2 → P (e1,, e2) av2).
Context (Pcast : ∀ τ e v,
  ⟦ e ⟧ Γ fs ρ m = Some (inr v) → P e (inr v) →
  val_cast_ok Γ m (TType τ) v → P (cast{τ} e) (inr (val_cast (TType τ) v))).
Context (Pinsert : ∀ r e1 e2 v1 v2,
  ⟦ e1 ⟧ Γ fs ρ m = Some (inr v1) → P e1 (inr v1) →
  ⟦ e2 ⟧ Γ fs ρ m = Some (inr v2) → P e2 (inr v2) → is_Some (v2 !!{Γ} r) →
  P (#[r:=e1] e2) (inr (val_alter Γ (λ _, v1) r v2))).
Lemma expr_eval_ind : ∀ e av, ⟦ e ⟧ Γ fs ρ m = Some av → P e av.
Proof.
  assert (∀ e f τs τ F es vs v,
    ⟦ e ⟧ Γ fs ρ m = Some (inr (ptrV (FunPtr f τs τ))) →
    P e (inr (ptrV (FunPtr f τs τ))) →
    Forall (λ e, ∀ av, ⟦ e ⟧ Γ fs ρ m = Some av → P e av) es →
    mapM (λ e, ⟦ e ⟧ Γ fs ρ m ≫= maybe inr) es = Some vs →
    fs !! f = Some F → F vs = Some v → P (call e @ es) (inr v)).
  { intros e f τs τ F es vs v ?? Hes Hvs Hf Hv. apply mapM_Some in Hvs.
    eapply Pcall; eauto; clear Hf Hv; induction Hvs;
      decompose_Forall_hyps; simplify_option_equality; eauto. }
  induction e using @expr_ind_alt; intros;
    repeat match goal with
    | _ => progress simplify_option_equality
    | _ => destruct (val_true_false_dec _ _) as [[[??]|[??]]|[??]]
    end; eauto.
Qed.
End expr_eval_ind.

Lemma expr_eval_lrval Γ fs ρ m av : ⟦ lrval_to_expr av ⟧ Γ fs ρ m = Some av.
Proof. by destruct av. Qed.
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
Lemma expr_eval_typed_aux Γ Δ τs τs' fs ρ m e av τlr :
  ✓ Γ → ✓{Γ,Δ} m → ⟦ e ⟧ Γ fs ρ m = Some av → ✓{Γ,Δ} fs → Δ ⊢* ρ :* τs →
  τs `prefix_of` τs' → (Γ,Δ,τs') ⊢ e : τlr → (Γ,Δ) ⊢ av : τlr.
Proof.
  intros ?? Hav Hfs ? [τs'' ->] He. revert e av Hav τlr He. assert (∀ es vs σs,
    Forall2 (λ e v, ∀ τlr,
      (Γ,Δ,τs ++ τs'') ⊢ e : τlr → (Γ,Δ) ⊢ inr v : τlr) es vs →
    (Γ,Δ,τs ++ τs'') ⊢* es :* inr <$> σs → (Γ,Δ) ⊢* vs :* σs).
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
    | H : (?τs1 ++ ?τs2) !! _ = Some ?τ1, H2 : ?τs1 !! _ = Some ?τ2 |- _ =>
      assert (τ1 = τ2) by (apply (lookup_app_l_Some _ τs2) in H2; congruence);
      clear H
    | H : _ ⊢ ?e : _, H2 : ∀ _, _ ⊢ ?e : _  → _ |- _ => specialize (H2 _ H)
    end; try typed_constructor; eauto using
      val_unop_typed, val_binop_typed, val_cast_typed, addr_top_typed,
      cmap_index_typed_valid, cmap_index_typed_representable, addr_top_strict,
      addr_elt_typed, addr_elt_strict, addr_elt_typed, addr_elt_strict,
      val_lookup_seg_typed, val_alter_const_typed.
  eapply purefuns_valid_lookup; eauto.
Qed.
Lemma expr_eval_typed Γ Δ τs fs ρ m e av τlr :
  ✓ Γ → ✓{Γ,Δ} m → ⟦ e ⟧ Γ fs ρ m = Some av → ✓{Γ,Δ} fs → Δ ⊢* ρ :* τs →
  (Γ,Δ,τs) ⊢ e : τlr → (Γ,Δ) ⊢ av : τlr.
Proof. intros. eapply expr_eval_typed_aux; eauto. Qed.
Lemma expr_eval_typed_l Γ Δ τs fs ρ m e a τ :
  ✓ Γ → ✓{Γ,Δ} m → ⟦ e ⟧ Γ fs ρ m = Some (inl a) → ✓{Γ,Δ} fs → Δ ⊢* ρ :* τs →
  (Γ,Δ,τs) ⊢ e : inl τ → (Γ,Δ) ⊢ a : TType τ.
Proof. 
  intros; by feed inversion (expr_eval_typed Γ Δ τs fs ρ m e (inl a) (inl τ)).
Qed.
Lemma expr_eval_typed_r Γ Δ τs fs ρ m e v τ :
  ✓ Γ → ✓{Γ,Δ} m → ⟦ e ⟧ Γ fs ρ m = Some (inr v) → ✓{Γ,Δ} fs → Δ ⊢* ρ :* τs →
  (Γ,Δ,τs) ⊢ e : inr τ → (Γ,Δ) ⊢ v : τ.
Proof.
  intros; by feed inversion (expr_eval_typed Γ Δ τs fs ρ m e (inr v) (inr τ)).
Qed.

Lemma expr_eval_weaken Γ1 Γ2 Δ1 τs fs ρ1 ρ2 m1 m2 e av τlr :
  ✓ Γ1 → ✓{Γ1,Δ1} m1 → ✓{Γ1,Δ1} fs → Δ1 ⊢* ρ1 :* τs → 
  (Γ1,Δ1,τs) ⊢ e : τlr → ⟦ e ⟧ Γ1 fs ρ1 m1 = Some av → 
  Γ1 ⊆ Γ2 → (∀ o, index_alive ('{m1}) o → index_alive ('{m2}) o) →
  ρ1 `prefix_of` ρ2 → ⟦ e ⟧ Γ2 fs ρ2 m2 = Some av.
Proof.
  intros ???? He Hav ?? [ρ3 ->]. revert Hav τlr He. assert (∀ es vs σs,
    Forall2 (λ e v, ∀ τlr, (Γ1,Δ1,τs) ⊢ e : τlr →
      ⟦ e ⟧ Γ2 fs (ρ1 ++ ρ3) m2 = Some (inr v)) es vs →
    (Γ1,Δ1,τs) ⊢* es :* inr <$> σs →
    mapM (λ e, ⟦ e ⟧ Γ2 fs (ρ1 ++ ρ3) m2 ≫= maybe inr) es = Some vs). 
  { intros es vs σs Hes Hes'. apply mapM_Some. revert σs Hes'.
    induction Hes; intros [|??] ?; decompose_Forall_hyps; constructor;
      simplify_option_equality; eauto. }
  revert e av. apply (expr_eval_ind Γ1 fs ρ1 m1
    (λ e _, ∀ τlr, _ ⊢ e : τlr → (_:Prop))); simpl; intros; typed_inversion_all;
    repeat match goal with
    | H: ⟦ ?e ⟧ Γ1 fs ρ1 m1 = Some ?av,  _: (Γ1,Δ1,τs) ⊢ ?e : ?τlr |- _ =>
      feed pose proof (expr_eval_typed Γ1 Δ1 τs fs ρ1 m1 e av τlr); auto;
      clear H
    end; typed_inversion_all; auto.
  * rewrite lookup_app_l by eauto using lookup_lt_Some.
    by simplify_option_equality.
  * by simplify_option_equality
      by eauto using addr_strict_weaken, index_alive_1', index_alive_2'.
  * by simplify_option_equality.
  * simplify_option_equality. by erewrite <-addr_elt_weaken by eauto.
  * by simplify_option_equality by eauto using val_lookup_seg_weaken.
  * by simplify_option_equality by eauto using val_unop_ok_weaken.
  * simplify_option_equality by eauto using val_binop_ok_weaken.
    by erewrite <-val_binop_weaken by eauto.
  * by simplify_option_equality.
  * simplify_option_equality.
    destruct (val_true_false_dec _ _) as [[[??]|[??]]|[??]];
      naive_solver eauto using val_true_weaken.
  * simplify_option_equality.
    by destruct (val_true_false_dec _ _) as [[[??]|[??]]|[??]]; eauto.
  * simplify_option_equality; eauto.
  * by simplify_option_equality by eauto using val_cast_ok_weaken.
  * simplify_option_equality by eauto using val_lookup_weaken_is_Some.
    by erewrite <-val_alter_weaken by eauto.
Qed.
Lemma expr_eval_erase Γ fs ρ m e : ⟦ e ⟧ Γ fs ρ (cmap_erase m) = ⟦ e ⟧ Γ fs ρ m.
Proof.
  destruct e using @expr_ind_alt; simpl;
    repeat match goal with
    | H : ⟦ _ ⟧ _ _ _ _ = _ |- _ => rewrite H
    | H : appcontext [index_alive'] |- _ => rewrite index_alive_erase' in H
    | H : appcontext [val_true] |- _ => rewrite val_true_erase in H
    | H : appcontext [val_unop_ok] |- _ => rewrite val_unop_ok_erase in H
    | H : appcontext [val_binop_ok] |- _ => rewrite val_binop_ok_erase in H
    | H : appcontext [val_cast_ok] |- _ => rewrite val_cast_ok_erase in H
    | _ => apply option_bind_ext_fun; intros
    | _ => case_option_guard; try done
    | _ => destruct (val_true_false_dec (cmap_erase m) _) as [[[]|[]]|[]]
    | _ => destruct (val_true_false_dec m _) as [[[]|[]]|[]]
    | _ => case_match
    end; try done.
  apply option_bind_ext; auto.
  apply Forall_mapM_ext; decompose_Forall; f_equal'; auto.
Qed.

(** Pure expressions without variables do not refer to the stack, so their
semantics is preserved under changes to the stack. *)
Lemma expr_var_free_stack_indep Γ fs ρ1 ρ2 m e :
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
Lemma expr_eval_subst Γ fs ρ m E e av :
  ⟦ subst E e ⟧ Γ fs ρ m = Some av ↔
  ∃ av', ⟦ e ⟧ Γ fs ρ m = Some av'
       ∧ ⟦ subst E (lrval_to_expr av') ⟧ Γ fs ρ m = Some av.
Proof.
  split.
  * revert av. induction E as [|E' E IH] using rev_ind; simpl; intros av.
    { eauto using expr_eval_lrval. }
    setoid_rewrite subst_snoc.
    intros; destruct E';
      repeat match goal with
      | _ => progress simplify_option_equality
      | H : mapM _ _ = Some _ |- _ =>
         apply mapM_Some in H; decompose_Forall_hyps
      | H : ∀ _, Some _ = Some _  → _ |- _ =>
         specialize (H _ eq_refl); destruct H as (?&->&?); eexists; split; eauto
      end; auto.
    erewrite mapM_Some_2
      by (apply Forall2_app, Forall2_cons; simplify_option_equality; eauto).
    by simplify_option_equality.
  * setoid_rewrite <-(expr_eval_lrval Γ fs ρ m). intros (av'&?&<-).
    by apply subst_preserves_expr_eval.
Qed.
End expression_eval.
