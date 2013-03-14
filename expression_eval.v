(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file defines a denotational semantics [⟦ _ ⟧] for pure expressions as
an expression evaluator. It is parametrized by a map of function names to
denotations. We use this to enable convenient reasoning about pure functions
in our axiomatic semantics. *)
Require Export fin_map_dom expressions abstract_memory values.

(** The type [purefun] represents denotations of pure functions. *)
Definition purefun := list val → option val.
Notation purefuns := (funmap purefun).

(** * Definition of the semantics *)
Reserved Notation "⟦ e ⟧" (format "⟦  e  ⟧").
Section expression_eval.
Context `{Permissions P}.

Fixpoint expr_eval (e : expr) (δ : purefuns)
    (ρ : stack) (m : mem_ _ P) : option val :=
  match e with
  | var x =>
     b ← ρ !! x;
     Some (ptrc b)%V
  | load e =>
     v ← ⟦ e ⟧ δ ρ m;
     a ← maybe_ptr v;
     m !! a
  | valc@{Ω} v =>
     guard (Ω = ∅); Some v
  | ⊙{op} e =>
     v ← ⟦ e ⟧ δ ρ m;
     eval_unop op v
  | el ⊙{op} er =>
     vl ← ⟦ el ⟧ δ ρ m;
     vr ← ⟦ er ⟧ δ ρ m;
     eval_binop op vl vr
  | call f @ es =>
     F ← δ !! f;
     vs ← mapM (λ e, ⟦ e ⟧ δ ρ m) es;
     F vs
  | (IF e then el else er) =>
     v ← ⟦ e ⟧ δ ρ m;
     vl ← ⟦ el ⟧ δ ρ m;
     vr ← ⟦ er ⟧ δ ρ m;
     Some $ if val_true_false_dec v then vl else vr
  | (cast@{τ} e) =>
     v ← ⟦ e ⟧ δ ρ m;
     eval_cast τ v
  | _ => None
  end%E
where "⟦ e ⟧" := (expr_eval e) : C_scope.

(** * Theorems *)
Lemma expr_eval_val δ ρ m v : ⟦ valc v ⟧ δ ρ m = Some v.
Proof. done. Qed.

Lemma mapM_expr_eval_val δ ρ m Ωs vs :
  same_length Ωs vs →
  ⋃ Ωs = ∅ →
  mapM (λ e, ⟦ e ⟧ δ ρ m) (zip_with EVal Ωs vs) = Some vs.
Proof.
  rewrite empty_union_list_L.
  induction 1; intros; decompose_Forall; simplify_option_equality; auto.
Qed.
Lemma Forall2_expr_eval_val_inv δ ρ m Ωs vs ws:
  same_length Ωs vs →
  Forall2 (λ e v, ⟦ e ⟧ δ ρ m = Some v) (zip_with EVal Ωs vs) ws →
  vs = ws.
Proof.
  intros HΩvs. revert ws.
  induction HΩvs; simpl; intros; decompose_Forall;
    simplify_option_equality; f_equal; eauto.
Qed.

(** We prove that we only give a semantics to pure expressions. The converse
of this property is not true, as pure expressions may still exhibit undefined
behavior. *)
Lemma expr_eval_is_pure δ ρ m e v :
  ⟦ e ⟧ δ ρ m = Some v → is_pure (dom _ δ) e.
Proof.
  revert v. induction e using expr_ind_alt; intros;
    simplify_option_equality;
    try destruct (value_true_false_dec _);
    constructor; eauto.
  * apply elem_of_dom; eauto.
  * decompose_Forall; eauto.
Qed.

(** Evaluation of pure expressions is preserved under extensions of the
memory. *)
Lemma expr_eval_weaken_mem δ ρ m1 m2 e v :
  ⟦ e ⟧ δ ρ m1 = Some v →
  m1 ⊆ m2 →
  ⟦ e ⟧ δ ρ m2 = Some v.
Proof.
  revert v. induction e using expr_ind_alt; intros;
    simplify_option_equality; eauto.
  * erewrite mapM_Some_2; [by eauto|]. decompose_Forall; auto.
  * eapply mem_lookup_weaken; eauto.
Qed.

Lemma expr_eval_weaken_inv δ ρ m1 m2 e v1 v2 :
  ⟦ e ⟧ δ ρ m1 = Some v1 →
  m1 ⊆ m2 →
  ⟦ e ⟧ δ ρ m2 = Some v2 →
  v1 = v2.
Proof.
  intros ? Hm1 Hm2.
  erewrite (expr_eval_weaken_mem _ _ m1 m2) in Hm2 by eauto.
  congruence.
Qed.

Lemma Forall_expr_eval_weaken_inv δ ρ m1 m2 es vs1 vs2 :
  Forall2 (λ e v, ⟦ e ⟧ δ ρ m1 = Some v) es vs1 →
  m1 ⊆ m2 →
  Forall2 (λ e v, ⟦ e ⟧ δ ρ m2 = Some v) es vs2 →
  vs1 = vs2.
Proof.
  intros ? Hm1 ?.
  apply (Forall2_unique (λ e v, ⟦ e ⟧ δ ρ m2 = Some v) es).
  * apply Forall2_impl with (λ e v, ⟦ e ⟧ δ ρ m1 = Some v);
      eauto using expr_eval_weaken_mem.
  * done.
  * congruence.
Qed.

(** Evaluation of pure expressions is preserved under unlocking. *)
Lemma expr_eval_unlock δ Ω ρ m e v :
  ⟦ e ⟧ δ ρ m = Some v →
  ⟦ e ⟧ δ ρ (mem_unlock Ω m) = Some v.
Proof.
  revert v. induction e using expr_ind_alt; intros;
    simplify_option_equality; eauto.
  * erewrite mapM_Some_2; [by eauto |]. decompose_Forall; auto.
  * eapply mem_lookup_unlock; eauto.
Qed.

(** Evaluation of pure expressions is preserved under extensions of the
stack. *)
Lemma expr_eval_weaken_stack δ ρ ρ' m e v :
  ⟦ e ⟧ δ ρ m = Some v →
  ⟦ e ⟧ δ (ρ ++ ρ') m = Some v.
Proof.
  revert v. induction e using expr_ind_alt;
    intros; simplify_option_equality; intuition.
  * rewrite lookup_app_l.
    + by simplify_option_equality.
    + eauto using lookup_lt_length_alt.
  * erewrite mapM_Some_2; [by eauto |]. decompose_Forall; auto.
Qed.

(** Pure expressions without variables do not refer to the stack, so their
semantics is preserved under changes to the stack. *)
Lemma expr_var_free_stack_indep δ ρ1 ρ2 m e :
  vars e ≡ ∅ →
  ⟦ e ⟧ δ ρ1 m = ⟦ e ⟧ δ ρ2 m.
Proof.
  induction e using expr_ind_alt; simpl; intro; decompose_empty; repeat
    match goal with
    | H : vars _ ≡ ∅ → ⟦ _ ⟧ _ _ _ = _ |- _ => rewrite H
    | H : ⋃ _ ≡ ∅ |- _ => rewrite empty_union_list in H
    | _ => done
    end.
  apply option_bind_ext_fun. intros.
  f_equal. apply Forall_mapM_ext. decompose_Forall; auto.
Qed.

(** Pure expressions that are load free do not refer to the memory, so their
semantics is preserved under changes to the memory. *)
Lemma expr_load_free_mem_indep δ ρ m1 m2 e :
  load_free e →
  ⟦ e ⟧ δ ρ m1 = ⟦ e ⟧ δ ρ m2.
Proof.
  induction 1 using load_free_ind_alt; simpl; repeat
    match goal with
    | H : ⟦ _ ⟧ _ _ _ = _ |- _ => rewrite H
    | _ => done
    end.
  apply option_bind_ext_fun. intros. f_equal. by apply Forall_mapM_ext.
Qed.

(** Only the denotations of functions that actually appear in an expression
are relevant. *)
Lemma expr_eval_fun_irrel δ1 δ2 ρ m e :
  (∀ f, f ∈ funs e → δ1 !! f = δ2 !! f) →
  ⟦ e ⟧ δ1 ρ m = ⟦ e ⟧ δ2 ρ m.
Proof.
  assert (∀ f es i (e' : expr), 
    es !! i = Some e' →
    f ∈ funs e' → f ∈ ⋃ (funs <$> es)).
  { intros ???? Hi Hf. apply elem_of_union_list.
    exists (funs e'). split; eauto.
    eapply elem_of_list_fmap_1, elem_of_list_lookup_2; eauto. }
  intros Hfs.
  induction e using expr_ind_alt; simpl in *; try done;
    repeat (apply option_bind_ext; intros); eauto;
    try solve_elem_of.
  apply Forall_mapM_ext. decompose_Forall. esolve_elem_of.
Qed.

(** Lifting DeBruijn indexes distributes over expression evaluation. *)
Lemma expr_eval_lift δ ρ m e :
  ⟦ e↑ ⟧ δ ρ m = ⟦ e ⟧ δ (tail ρ) m.
Proof.
  induction e using expr_ind_alt; intros; simpl; repeat
    match goal with
    | H : ⟦ _↑ ⟧ _ _ _ = _ |- _ => rewrite H
    end; auto.
  * by rewrite <-lookup_tail.
  * destruct (δ !! _); simpl; [|done].
    f_equal. apply Forall2_mapM_ext. by decompose_Forall.
Qed.

(** If an expression has a semantics, then each sub-expression of that
expression has a semantics too. *)
Lemma expr_eval_subst_inv δ ρ m (E : ectx) e v :
  ⟦ subst E e ⟧ δ ρ m = Some v →
  ∃ v', ⟦ e ⟧ δ ρ m = Some v' ∧ ⟦ subst E (valc v')%E ⟧ δ ρ m = Some v.
Proof.
  revert v. induction E as [|E' E IH] using rev_ind;
    simpl; intros v; [eauto |].
  setoid_rewrite subst_snoc.
  intros; destruct E'; simplify_option_equality;
    try solve [edestruct IH as (?&?&?); eauto with simplify_option_equality].
  decompose_Forall. edestruct IH as (?&?&?); eauto.
  eexists; split_ands; eauto.
  erewrite mapM_Some_2; [by eauto |]. decompose_Forall; eauto.
Qed.

Lemma subst_preserves_expr_eval δ ρ m (E : ectx) e1 e2 :
  ⟦ e1 ⟧ δ ρ m = ⟦ e2 ⟧ δ ρ m →
  ⟦ subst E e1 ⟧ δ ρ m = ⟦ subst E e2 ⟧ δ ρ m.
Proof.
  intros. induction E as [|E' ? IH] using rev_ind; [done |].
  destruct E'; rewrite ?subst_snoc; simpl; rewrite ?IH; auto.
  destruct (δ !! _); simpl; [|done].
  f_equal. apply Forall2_mapM_ext. by decompose_Forall.
Qed.
End expression_eval.

Notation "⟦ e ⟧" := (expr_eval e) : C_scope.

(** * Tactics *)
Tactic Notation "simplify_expr_equality" "by" tactic3(tac) := repeat
  match goal with
  | _ => progress simplify_mem_equality by tac
  | _ => progress simplify_option_equality by tac
  | Ht : val_true ?v, Hf : val_false ?v |- _ =>
    destruct (val_true_false v Ht Hf)
  | H : maybe_ptr ?v = Some _ |- _ =>
    apply maybe_ptr_Some in H
  | H : context [ val_true_false_dec ?v ] |- _ =>
    destruct (val_true_false_dec v)
  | |- context [ val_true_false_dec ?v ] =>
    destruct (val_true_false_dec v)
  | H1: ⟦ ?e ⟧ ?δ ?ρ ?m1 = Some ?v1, H2: ⟦ ?e ⟧ ?δ ?ρ ?m2 = Some ?v2 |- _ =>
    let H3 := fresh in
    feed pose proof (expr_eval_weaken_inv ρ m1 m2 e v1 v2) as H3;
      [done | by tac | done | ];
    clear H2; symmetry in H3
  end.
Tactic Notation "simplify_expr_equality" :=
  simplify_expr_equality by eauto with simpl_mem.
