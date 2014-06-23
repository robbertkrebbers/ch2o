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

Instance purefuns_typed `{IntEnv Ti, PtrEnv Ti} :
    Typed (env Ti * mem Ti) (funtypes Ti) (purefuns Ti) := λ Γm,
  map_Forall2 (λ F τsτ, ∀ vs v,
    F vs = Some v → Γm ⊢* vs :* τsτ.1 → Γm ⊢ v : τsτ.2
  ) (λ _, False) (λ _, False).

(** * Definition of the semantics *)
Reserved Notation "⟦ e ⟧" (format "⟦  e  ⟧").

Fixpoint expr_eval `{IntEnv Ti, PtrEnv Ti} (e : expr Ti) (Γ : env Ti)
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
     v ← ⟦ e ⟧ Γ fs ρ m ≫= maybe_inr;
     a ← (maybe_VBase v ≫= maybe_VPtr) ≫= maybe_Ptr;
     guard (addr_strict Γ a);
     Some (inl a)
  | & e =>
     a ← ⟦ e ⟧ Γ fs ρ m ≫= maybe_inl;
     Some (inr (ptrV (Ptr a)))
  | elt e =>
     a ← ⟦ e ⟧ Γ fs ρ m ≫= maybe_inl;
     Some (inl (addr_elt Γ a))
  | @{op} e =>
     v ← ⟦ e ⟧ Γ fs ρ m ≫= maybe_inr;
     guard (val_unop_ok op v);
     Some (inr (val_unop op v))
  | e1 @{op} e2 =>
     v1 ← ⟦ e1 ⟧ Γ fs ρ m ≫= maybe_inr;
     v2 ← ⟦ e2 ⟧ Γ fs ρ m ≫= maybe_inr;
     guard (val_binop_ok Γ m op v1 v2);
     Some (inr (val_binop Γ op v1 v2))
  | call f @ es =>
     F ← fs !! f;
     vs ← mapM (λ e, ⟦ e ⟧ Γ fs ρ m ≫= maybe_inr) es;
     inr <$> F vs
  | if{e1} e2 else e3 =>
     v1 ← ⟦ e1 ⟧ Γ fs ρ m ≫= maybe_inr;
     av2 ← ⟦ e2 ⟧ Γ fs ρ m;
     av3 ← ⟦ e3 ⟧ Γ fs ρ m;
     match val_true_false_dec v1 with
     | inleft (left _) => Some av2
     | inleft (right _) => Some av3
     | inright _ => None
     end
  | e1 ,, e2 =>
     _ ← ⟦ e1 ⟧ Γ fs ρ m ≫= maybe_inr;
     ⟦ e2 ⟧ Γ fs ρ m
  | cast{τ} e =>
     v ← ⟦ e ⟧ Γ fs ρ m ≫= maybe_inr;
     guard (val_cast_ok Γ τ v);
     Some (inr (val_cast τ v))
  | e .> i =>
     a ← ⟦ e ⟧ Γ fs ρ m ≫= maybe_inl;
     Some (inl (addr_field Γ i a))
  | _ => None
  end
where "⟦ e ⟧" := (expr_eval e) : C_scope.

Definition lrval_to_expr {Ti} (av : addr Ti + val Ti) : expr Ti :=
  match av with inl a => %a | inr v => #v end.

(** * Theorems *)
Section expression_eval.
Context `{EnvSpec Ti}.
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
  ⟦ e ⟧ Γ fs ρ m = Some (inr (ptrV (Ptr a))) →
  P e (inr (ptrV (Ptr a))) → addr_strict Γ a → P (.* e) (inl a)).
Context (Profl : ∀ e a,
  ⟦ e ⟧ Γ fs ρ m = Some (inl a) → P e (inl a) → P (&e) (inr (ptrV (Ptr a)))).
Context (Pelt : ∀ e a,
  ⟦ e ⟧ Γ fs ρ m = Some (inl a) → P e (inl a) → P (elt e) (inl (addr_elt Γ a))).
Context (Punop : ∀ op e v,
  ⟦ e ⟧ Γ fs ρ m = Some (inr v) → P e (inr v) →
  val_unop_ok op v → P (@{op} e) (inr (val_unop op v))).
Context (Pbinop : ∀ op e1 e2 v1 v2,
  ⟦ e1 ⟧ Γ fs ρ m = Some (inr v1) → P e1 (inr v1) →
  ⟦ e2 ⟧ Γ fs ρ m = Some (inr v2) → P e2 (inr v2) →
  val_binop_ok Γ m op v1 v2 → P (e1 @{op} e2) (inr (val_binop Γ op v1 v2))).
Context (Pcall : ∀ f F es vs v,
  fs !! f = Some F →
  Forall2 (λ e v, ⟦ e ⟧ Γ fs ρ m = Some (inr v)) es vs →
  Forall2 (λ e v, P e (inr v)) es vs →
  F vs = Some v → P (call f @ es) (inr v)).
Context (Pif1 : ∀ e1 e2 e3 v1 av2 av3,
  ⟦ e1 ⟧ Γ fs ρ m = Some (inr v1) → P e1 (inr v1) →
  ⟦ e2 ⟧ Γ fs ρ m = Some av2 → P e2 av2 →
  ⟦ e3 ⟧ Γ fs ρ m = Some av3 → P e3 av3 →
  val_true v1 → P (if{e1} e2 else e3) av2).
Context (Pif2 : ∀ e1 e2 e3 v1 av2 av3,
  ⟦ e1 ⟧ Γ fs ρ m = Some (inr v1) → P e1 (inr v1) →
  ⟦ e2 ⟧ Γ fs ρ m = Some av2 → P e2 av2 →
  ⟦ e3 ⟧ Γ fs ρ m = Some av3 → P e3 av3 →
  val_false v1 → P (if{e1} e2 else e3) av3).
Context (Pcomma : ∀ e1 e2 v1 av2,
  ⟦ e1 ⟧ Γ fs ρ m = Some (inr v1) → P e1 (inr v1) →
  ⟦ e2 ⟧ Γ fs ρ m = Some av2 → P e2 av2 → P (e1,, e2) av2).
Context (Pcast : ∀ τ e v,
  ⟦ e ⟧ Γ fs ρ m = Some (inr v) → P e (inr v) →
  val_cast_ok Γ τ v → P (cast{τ} e) (inr (val_cast τ v))).
Context (Pfield : ∀ e i a,
  ⟦ e ⟧ Γ fs ρ m = Some (inl a) → P e (inl a) →
  P (e .> i) (inl (addr_field Γ i a))).
Lemma expr_eval_ind : ∀ e av, ⟦ e ⟧ Γ fs ρ m = Some av → P e av.
Proof.
  assert (∀ f F es vs v,
    Forall (λ e, ∀ av, ⟦ e ⟧ Γ fs ρ m = Some av → P e av) es →
    mapM (λ e, ⟦ e ⟧ Γ fs ρ m ≫= maybe_inr) es = Some vs →
    fs !! f = Some F → F vs = Some v → P (call f @ es) (inr v)).
  { intros f F es vs v Hes Hvs Hf Hv. apply mapM_Some in Hvs.
    eapply Pcall; eauto; clear Hf Hv; induction Hvs; decompose_Forall_hyps;
      repeat match goal with
      | _ => progress simplify_option_equality
      | _ : maybe_inr ?va = Some _ |- _ => is_var va; destruct va
      end; eauto. }
  induction e using @expr_ind_alt; intros;
    repeat match goal with
    | _ => progress simplify_option_equality
    | _ : maybe_inl ?va = Some _ |- _ => is_var va; destruct va
    | _ : maybe_inr ?va = Some _ |- _ => is_var va; destruct va
    | _ : maybe_VBase ?v = Some _ |- _ => is_var v; destruct v
    | _ : maybe_VPtr ?vb = Some _ |- _ => is_var vb; destruct vb
    | _ : maybe_Ptr ?p = Some _ |- _ => is_var p; destruct p
    | _ => destruct (val_true_false_dec _) as [[[??]|[??]]|[??]]
    end; eauto.
Qed.
End expr_eval_ind.

Lemma expr_eval_lrval Γ fs ρ m av : ⟦ lrval_to_expr av ⟧ Γ fs ρ m = Some av.
Proof. by destruct av. Qed.
Lemma purefuns_typed_lookup Γ m Γf fs f F vs v τs τ :
  (Γ,m) ⊢ fs : Γf → fs !! f = Some F → Γf !! f = Some (τs,τ) →
  F vs = Some v → (Γ,m) ⊢* vs :* τs → (Γ,m) ⊢ v : τ.
Proof. intros Hfs ???. specialize (Hfs f); simplify_option_equality; eauto. Qed.
Lemma EVal_expr_eval Γ fs ρ m v : ⟦ #v ⟧ Γ fs ρ m = Some (inr v).
Proof. done. Qed.
Lemma EVals_expr_eval Γ fs ρ m Ωs vs :
  length Ωs = length vs →
  ⋃ Ωs = ∅ → mapM (λ e, ⟦ e ⟧ Γ fs ρ m ≫= maybe_inr) (#{Ωs}* vs) = Some vs.
Proof.
  rewrite empty_union_list_L. rewrite <-Forall2_same_length.
  induction 1; intros; decompose_Forall; simplify_option_equality; auto.
Qed.
Lemma Forall2_expr_eval_val_inv Γ fs ρ m Ωs vs vs' :
  length Ωs = length vs →
  Forall2 (λ e v, ⟦ e ⟧ Γ fs ρ m ≫= maybe_inr = Some v) (#{Ωs}* vs) vs' →
  vs = vs'.
Proof.
  rewrite <-Forall2_same_length. intros HΩvs. revert vs'.
  induction HΩvs; simpl; intros; decompose_Forall;
    simplify_option_equality; f_equal; eauto.
Qed.
Lemma expr_eval_typed_aux Γ Γf τs τs' fs ρ m e av τlr :
  ✓ Γ → ✓{Γ} m → ⟦ e ⟧ Γ fs ρ m = Some av → (Γ,m) ⊢ fs : Γf → m ⊢* ρ :* τs →
  τs `prefix_of` τs' → (Γ,Γf,m,τs') ⊢ e : τlr → (Γ,m) ⊢ av : τlr.
Proof.
  intros ?? Hav Hfs ? [τs'' ->] He. revert e av Hav τlr He. assert (∀ es vs σs,
    Forall2 (λ e v, ∀ τlr,
      (Γ,Γf,m,τs ++ τs'') ⊢ e : τlr → (Γ, m) ⊢ inr v : τlr) es vs →
    (Γ,Γf,m,τs ++ τs'') ⊢* es :* inr <$> σs → (Γ,m) ⊢* vs :* σs).
  { intros es vs σs Hes. revert σs.
    induction Hes; intros [|??] ?; decompose_Forall_hyps;
      repeat match goal with
      | _ => progress typed_inversion_all
      | H : _ ⊢ ?e : _, H2 : ∀ _, _ ⊢ ?e : _  → _ |- _ => specialize (H2 _ H)
      end; constructor; eauto. }
  rapply (expr_eval_ind Γ fs ρ m); intros;
    repeat match goal with
    | _ => progress typed_inversion_all
    | _ => progress decompose_Forall_hyps
    | H : (?τs1 ++ ?τs2) !! _ = Some ?τ1, H2 : ?τs1 !! _ = Some ?τ2 |- _ =>
      assert (τ1 = τ2) by (apply (lookup_app_l_Some _ τs2) in H2; congruence);
      clear H
    | H : _ ⊢ ?e : _, H2 : ∀ _, _ ⊢ ?e : _  → _ |- _ => specialize (H2 _ H)
    end; try typed_constructor; eauto using
      val_unop_typed, val_binop_typed, val_cast_typed, addr_top_typed,
      index_typed_valid, index_typed_representable, addr_top_strict,
      addr_elt_typed, addr_elt_strict, addr_field_typed, addr_field_strict.
  eapply purefuns_typed_lookup; eauto.
Qed.
Lemma expr_eval_typed Γ Γf τs fs ρ m e av τlr :
  ✓ Γ → ✓{Γ} m → ⟦ e ⟧ Γ fs ρ m = Some av → (Γ,m) ⊢ fs : Γf → m ⊢* ρ :* τs →
  (Γ,Γf,m,τs) ⊢ e : τlr → (Γ,m) ⊢ av : τlr.
Proof. eauto using expr_eval_typed_aux. Qed.

(** We prove that only pure expressions are given a semantics. The converse
of this property is not true, as pure expressions may still exhibit undefined
behavior, in which case [⟦ e ⟧ Γ fs ρ m] yields [None]. *)
Lemma expr_eval_is_pure Γ fs ρ m e :
  is_Some (⟦ e ⟧ Γ fs ρ m) → is_pure (dom _ fs) e.
Proof.
  intros (av&Hav); revert e av Hav. 
  rapply (expr_eval_ind Γ fs ρ m); intros; simpl; constructor; eauto.
  * apply elem_of_dom; eauto.
  * decompose_Forall; eauto.
Qed.

Lemma expr_eval_weaken Γ1 Γ2 Γf τs fs ρ1 ρ2 m1 m2 e av τlr :
  ✓ Γ1 → ✓{Γ1} m1 → (Γ1,m1) ⊢ fs : Γf → m1 ⊢* ρ1 :* τs →
  (Γ1,Γf,m1,τs) ⊢ e : τlr → ⟦ e ⟧ Γ1 fs ρ1 m1 = Some av →
  Γ1 ⊆ Γ2 → (∀ o : index, index_alive m1 o → index_alive m2 o) →
  ρ1 `prefix_of` ρ2 → ⟦ e ⟧ Γ2 fs ρ2 m2 = Some av.
Proof.
  intros ???? He Hav ?? [ρ3 ->]. revert e av Hav τlr He. assert (∀ es vs σs,
    Forall2 (λ e v, ∀ τlr,
      (Γ1,Γf,m1,τs) ⊢ e : τlr → ⟦ e ⟧ Γ2 fs (ρ1 ++ ρ3) m2 = Some (inr v)) es vs →
    (Γ1,Γf,m1,τs) ⊢* es :* inr <$> σs →
    mapM (λ e, ⟦ e ⟧ Γ2 fs (ρ1 ++ ρ3) m2 ≫= maybe_inr) es = Some vs). 
  { intros es vs σs Hes Hes'. apply mapM_Some. revert σs Hes'.
    induction Hes; intros [|??] ?; decompose_Forall_hyps; constructor;
      simplify_option_equality; eauto. }
  rapply (expr_eval_ind Γ1 fs ρ1 m1); intros; typed_inversion_all;
    repeat match goal with
    | H : ⟦ ?e ⟧ Γ1 fs ρ1 m1 = Some ?av,  _ : (Γ1,Γf,m1,τs) ⊢ ?e : ?τlr |- _ =>
      feed pose proof (expr_eval_typed Γ1 Γf τs fs ρ1 m1 e av τlr); auto;
      clear H
    end; typed_inversion_all; auto.
  * rewrite lookup_app_l by eauto using lookup_lt_Some. by simplify_option_equality.
  * by simplify_option_equality by eauto using addr_strict_weaken.
  * by simplify_option_equality.
  * simplify_option_equality. by erewrite <-addr_elt_weaken by eauto.
  * by simplify_option_equality.
  * simplify_option_equality by eauto using val_binop_ok_weaken.
    by erewrite <-val_binop_weaken by eauto.
  * by simplify_option_equality.
  * simplify_option_equality.
    by destruct (val_true_false_dec _) as [[[??]|[??]]|[??]].
  * simplify_option_equality.
    by destruct (val_true_false_dec _) as [[[??]|[??]]|[??]].
  * simplify_option_equality; eauto.
  * by simplify_option_equality by eauto using val_cast_ok_weaken.
  * simplify_option_equality.
    by erewrite <-addr_field_weaken by eauto.
Qed.

(** Only the denotations of functions that actually appear in an expression
are relevant. *)
Lemma expr_eval_fun_irrel Γ  fs1 fs2 ρ m e :
  (∀ f, f ∈ funs e → fs1 !! f = fs2 !! f) → ⟦ e ⟧ Γ fs1 ρ m = ⟦ e ⟧ Γ fs2 ρ m.
Proof.
  assert (∀ es,
    Forall (λ e, (∀ f, f ∈ funs e → fs1 !! f = fs2 !! f) →
      ⟦ e ⟧ Γ fs1 ρ m = ⟦ e ⟧ Γ fs2 ρ m) es →
    (∀ f, f ∈ ⋃ (funs <$> es) → fs1 !! f = fs2 !! f) →
    mapM (λ e, ⟦ e ⟧ Γ fs1 ρ m ≫= maybe_inr) es
    = mapM (λ e, ⟦ e ⟧ Γ fs2 ρ m ≫= maybe_inr) es) as help.
  { intros es Hes ?. apply Forall_mapM_ext.
    induction Hes as [|e' es He']; csimpl in *; auto.
    constructor; [|solve_elem_of]. by rewrite He' by solve_elem_of. }
  intros Hfs. induction e using expr_ind_alt; simpl in *; auto;
    repeat match goal with
    | _ => progress typed_inversion_all
    | H : _ → ⟦ _ ⟧ _ _ _ _ = ⟦ _ ⟧ _ _ _ _ |- _ => rewrite H by solve_elem_of
    end; auto.
  by rewrite Hfs, help by solve_elem_of.
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
  apply option_bind_ext_fun. intros.
  f_equal. apply Forall_mapM_ext. decompose_Forall; f_equal'; auto.
Qed.

(** Lifting DeBruijn indexes distributes over expression evaluation. *)
Lemma expr_eval_lift Γ fs ρ m e : ⟦ e↑ ⟧ Γ fs ρ m = ⟦ e ⟧ Γ fs (tail ρ) m.
Proof.
  induction e using expr_ind_alt; intros; simpl; repeat
    match goal with
    | H : ⟦ _↑ ⟧ _ _ _ _ = _ |- _ => rewrite H
    end; auto.
  * by rewrite <-lookup_tail.
  * destruct (fs !! _); simpl; [|done].
    f_equal. apply Forall2_mapM_ext. by decompose_Forall; f_equal'.
Qed.

(** The semantics is preserved under substitution. *)
Lemma subst_preserves_expr_eval Γ fs ρ m E e1 e2 :
  ⟦ e1 ⟧ Γ fs ρ m = ⟦ e2 ⟧ Γ fs ρ m →
  ⟦ subst E e1 ⟧ Γ fs ρ m = ⟦ subst E e2 ⟧ Γ fs ρ m.
Proof.
  intros. induction E as [|E' ? IH] using rev_ind; [done |].
  destruct E'; rewrite ?subst_snoc; simpl; rewrite ?IH; auto.
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
      | H : mapM _ _ = Some _ |- _ => apply mapM_Some in H; decompose_Forall_hyps
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
