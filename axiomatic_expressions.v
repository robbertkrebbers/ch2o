(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export axiomatic.
Require Import axiomatic_graph type_system_decidable.
Require Import expression_eval_smallstep.
Require Import assignments_separation expression_eval_separation.
Local Open Scope ctype_scope.

Section axiomatic_expressions.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types o : index.
Implicit Types Δ : memenv K.
Implicit Types δ : funenv K.
Implicit Types m : mem K.
Implicit Types e : expr K.
Implicit Types τ σ : type K.
Implicit Types a : addr K.
Implicit Types v : val K.
Implicit Types ν : lrval K.
Implicit Types k : ctx K.
Implicit Types φ : focus K.
Implicit Types S : state K.
Implicit Types Pd : dassert K.

Hint Extern 1 (_ ⊥ _) => solve_mem_disjoint.
Hint Extern 1 (⊥ _) => solve_mem_disjoint.
Hint Extern 1 (sep_valid _) => solve_mem_disjoint.

Hint Immediate cmap_valid_memenv_valid.
Hint Resolve cmap_empty_valid cmap_erased_empty mem_locks_empty.
Hint Resolve cmap_union_valid_2 cmap_erased_union cmap_erase_valid.

Hint Immediate ax_disjoint_expr_compose_diagram.
Hint Immediate ax_expr_disjoint_compose_diagram.
Hint Immediate ax_expr_funframe_emp.
Hint Immediate ax_disjoint_compose_diagram.

Hint Immediate val_new_typed perm_full_mapped.
Hint Resolve mem_alloc_valid mem_free_valid.
Hint Immediate lockset_empty_valid.
Hint Extern 0 (_ ⊢ _ : _) => typed_constructor.
Hint Extern 0 (unframe ax_disjoint_cond _ _ _ _ _ _ _) => by constructor.
Hint Extern 0 (focus_locks_valid _ _) => by constructor.

(** ** Basic rules *)
Lemma ax_expr_weaken Γ δ P P' A Q Q' e :
  P ⊆{Γ} P' → (∀ ν, Q' ν ⊆{Γ} Q ν) →
  Γ\ δ\ A ⊨ₑ {{ P' }} e {{ Q' }} → Γ\ δ\ A ⊨ₑ {{ P }} e {{ Q }}.
Proof.
  intros HP HQ Hax Δ n ρ m τlr ????????.
  apply ax_weaken with (ax_expr_cond ρ A) (ax_expr_post Q' τlr); auto.
  destruct 3; constructor; auto. apply HQ; eauto using indexes_valid_weaken.
Qed.
Lemma ax_expr_weaken_pre Γ δ A P P' Q e :
  P ⊆{Γ} P' →
  Γ\ δ\ A ⊨ₑ {{ P' }} e {{ Q }} → Γ\ δ\ A ⊨ₑ {{ P }} e {{ Q }}.
Proof. eauto using ax_expr_weaken. Qed.
Lemma ax_expr_weaken_post Γ δ A P Q Q' e :
  (∀ ν, Q' ν ⊆{Γ} Q ν) →
  Γ\ δ\ A ⊨ₑ {{ P }} e {{ Q' }} → Γ\ δ\ A ⊨ₑ {{ P }} e {{ Q }}.
Proof. eauto using ax_expr_weaken. Qed.
Lemma ax_expr_frame_r Γ δ B A P Q e :
  Γ\ δ\ B ⊨ₑ {{ P }} e {{ λ ν, Q ν }} →
  Γ\ δ\ B ⊨ₑ {{ P ★ A }} e {{ λ ν, Q ν ★ A }}.
Proof.
  intros Hax Δ n ρ m τlr ?? Hlocks ???? (m1&m2&?&?&?&?).
  destruct (cmap_erase_union_inv m m1 m2)
    as (m1'&m2'&->&?&->&->); simplify_mem_disjoint_hyps; auto.
  rewrite mem_locks_union in Hlocks by auto; decompose_empty.
  apply ax_frame with (ax_expr_cond ρ B) (ax_expr_post Q τlr);
    eauto using ax_expr_cond_frame_diagram_simple.
  { apply Hax; eauto using ax_expr_funframe_weaken, @sep_union_subseteq_l. }
  intros Δ' φ' m' ????; destruct 1 as [ν Ω ????]; constructor; eauto.
  { rewrite mem_locks_union by auto. esolve_elem_of. }
  exists (cmap_erase m) (cmap_erase m2'); split_ands;
    eauto using cmap_erase_union, assert_weaken.
  by rewrite <-!cmap_erase_disjoint_le.
Qed.
Lemma ax_expr_frame_l Γ δ B A P Q e :
  Γ\ δ\ B ⊨ₑ {{ P }} e {{ λ ν, Q ν }} →
  Γ\ δ\ B ⊨ₑ {{ A ★ P }} e {{ λ ν, A ★ Q ν }}.
Proof.
  setoid_rewrite (commutative (R:=(≡{Γ})) (★)%A A). apply ax_expr_frame_r.
Qed.
Lemma ax_expr_exist_pre {A} Γ δ (B : assert K) (P : A → assert K) Q e :
  (∀ x, Γ\ δ\ B ⊨ₑ {{ P x }} e {{ Q }}) →
  Γ\ δ\ B ⊨ₑ {{ ∃ x, P x }} e {{ Q }}.
Proof. intros Hax Δ n k m τlr HΓ Hd ????? [x Hpre]. by apply (Hax x). Qed.
Lemma ax_expr_funframe_r Γ δ B A P Q e :
  Γ\ δ\ A ★ B ⊨ₑ {{ P }} e {{ λ ν, Q ν }} →
  Γ\ δ\ B ⊨ₑ {{ P ★ A }} e {{ λ ν, Q ν ★ A }}.
Proof.
  cut (∀ n Δ ρ k φ m τlr,
    ✓ Γ → ✓{Δ}* ρ →
    ax_graph (ax_expr_cond ρ (A ★ B)) (ax_expr_post Q τlr) Γ δ Δ ρ n k φ m →
    (k = [] → ∀ mA,
      ⊥ [m; mA] → ✓{Γ,Δ} mA → cmap_erased mA → mem_locks mA = ∅ →
      assert_holds A Γ Δ ρ mA →
      ax_graph (ax_expr_cond ρ B)
         (ax_expr_post (λ ν, Q ν ★ A) τlr)%A Γ δ Δ ρ n k φ (m ∪ mA)) ∧
    (k ≠ [] →
      ax_graph (ax_expr_cond ρ B)
               (ax_expr_post (λ ν, Q ν ★ A)%A τlr) Γ δ Δ ρ n k φ m)).
  { intros help Hax Δ n ρ m' τlr HΓ ? Hm ??? (mB&?&?&?&?&?)
      (m&mA&?&?&?&?); simplify_equality.
    destruct (cmap_erase_union_inv_r m' m mA)
      as (m''&->&?&->&?); simplify_mem_disjoint_hyps; auto.
    rewrite mem_locks_union in Hm by auto; decompose_empty.
    refine (proj1 (help n Δ ρ [] (Expr e) m'' τlr _ _ _ ) _ mA _ _ _ _ _); auto.
    apply Hax; auto. exists (mA ∪ mB); split_ands; eauto.
    * rewrite mem_locks_union by auto. by apply empty_union_L.
    * exists mA mB; split_ands; auto. }
  clear P. intros n. induction n as [|n]; [repeat constructor|].
  intros Δ ρ k φ m τlr ??;
    inversion 1 as [|??? [ν ?????]|???? Hred Hstep]; subst.
  { split; [|done]; intros _ mA ? HmA ??; do 2 constructor; auto.
    { rewrite mem_locks_union by auto; esolve_elem_of. }
    rewrite cmap_erase_union.
    exists (cmap_erase m) (cmap_erase mA); split_ands; auto.
    + by rewrite <-!cmap_erase_disjoint_le.
    + by rewrite cmap_erased_spec by done. }
  split.
  * intros -> mA ?????; apply ax_further.
    { intros Δ' ???? Hframe; inversion_clear Hframe as [mB mf|];
        simplify_equality; simplify_mem_disjoint_hyps.
      rewrite <-!(sep_associative m), (sep_commutative mA),
        <-(sep_associative mf), (sep_associative m) by auto.
      eapply Hred, ax_frame_in_expr; eauto.
      + rewrite mem_locks_union by auto. by apply empty_union_L.
      + exists mA mB; split_ands; eauto using assert_weaken. }
    intros Δ' ?? S' ?? Hframe p ?; inversion_clear Hframe as [mB mf|];
      simplify_equality; simplify_mem_disjoint_hyps.
    feed inversion (Hstep Δ' (m ∪ mA ∪ mf ∪ mB) (InExpr mf (mA ∪ mB)) S')
      as [? Δ'' k' φ' m' ?? Hunframe]; subst; auto.
    { constructor; auto.
      + by rewrite <-!(sep_associative m), (sep_commutative mA),
          <-(sep_associative mf), (sep_associative m) by auto.
      + rewrite mem_locks_union by auto. by apply empty_union_L.
      + exists mA mB; split_ands; eauto using assert_weaken. }
    inversion Hunframe as [| |m''|]; subst; simplify_mem_disjoint_hyps.
    + apply mk_ax_next with Δ'' (m' ∪ mA); auto using focus_locks_valid_union.
      - apply ax_unframe_expr_to_expr; auto.
        by rewrite <-!(sep_associative m'),
          (sep_commutative mA mf), !sep_associative by auto.
      - refine (proj1 (IHn _ _ _ _ _ _ _ _ _) _ _ _ _ _ _ _);
          eauto using assert_weaken, indexes_valid_weaken.
    + apply mk_ax_next with Δ'' (m'' ∪ mA ∪ mB); auto.
      - apply ax_unframe_expr_to_fun with (m'' ∪ mA); auto.
        by rewrite <-!(sep_associative m''),
          (sep_commutative mA mf), !sep_associative by auto.
      - by rewrite <-sep_associative by auto.
      - refine (proj2 (IHn _ _ _ _ _ _ _ _ _) _);
          eauto using indexes_valid_weaken.
        by rewrite <-sep_associative by auto.
  * intros ?; apply ax_further.
    { intros Δ' ???? Hframe; inversion_clear Hframe as [|mf]; simplify_equality.
      eapply Hred, ax_frame_in_fun; eauto. }
    intros Δ' ?? S' ?? Hframe p ?;
      inversion_clear Hframe as [|mf]; simplify_equality.
    feed inversion (Hstep Δ' (m ∪ mf) (InFun mf) S')
      as [? Δ'' k' φ' m' ?? Hunframe]; subst; auto.
    { by apply ax_frame_in_fun. }
    inversion Hunframe as [|?????? HmAmB (mA&mB&?&?&?&?)| |];
      subst; simplify_mem_disjoint_hyps.
    + rewrite mem_locks_union in HmAmB by auto; decompose_empty.
      apply mk_ax_next with Δ'' (m' ∪ mA); auto using focus_locks_valid_union.
      - eapply ax_unframe_fun_to_expr with mB;
          eauto 3 using cmap_erased_subseteq, @sep_union_subseteq_r'.
        by rewrite <-!(sep_associative m'),
          (sep_commutative mA mf), !sep_associative by auto.
      - refine (proj1 (IHn _ _ _ _ _ _ _ _ _) _ _ _ _ _ _ _); eauto using
          indexes_valid_weaken, cmap_erased_subseteq, @sep_union_subseteq_l'.
    + apply mk_ax_next with Δ'' m'; auto; [by apply ax_unframe_fun_to_fun|].
      refine (proj2 (IHn _ _ _ _ _ _ _ _ _) _);
        eauto using indexes_valid_weaken.
Qed.
Lemma ax_expr_funframe_l Γ δ B A P Q e :
  Γ\ δ\ A ★ B ⊨ₑ {{ P }} e {{ λ ν, Q ν }} →
  Γ\ δ\ B ⊨ₑ {{ A ★ P }} e {{ λ ν, A ★ Q ν }}.
Proof.
  intros. setoid_rewrite (commutative (R:=(≡{Γ})) (★)%A A).
  by apply ax_expr_funframe_r.
Qed.

(** ** Structural rules *)
Lemma ax_expr_base Γ δ A P Q e ν :
  P ⊆{Γ} (Q ν ∧ e ⇓ ν)%A →
  Γ\ δ\ A ⊨ₑ {{ P }} e {{ Q }}.
Proof.
  intros HPQ Δ n ρ m τlr HΓ ??? He Hm HA HP.
  destruct (HPQ Γ Δ ρ (cmap_erase m)) as [HQ (τlr'&?&?)]; auto.
  assert (τlr' = τlr) by (by simplify_type_equality'); subst.
  cut (∀ Δ' e',
    Δ ⇒ₘ Δ' → locks e' = ∅ → ⟦ e' ⟧ Γ ρ m = Some ν → (Γ,Δ',ρ.*2) ⊢ e' : τlr →
    ax_graph (ax_expr_cond ρ A)
      (ax_expr_post Q τlr) Γ δ Δ' ρ n [] (Expr e') m).
  { intros help. apply (help Δ); rewrite <-1?expr_eval_erase; auto. }
  assert (✓{Γ,Δ} (cmap_erase m)) by eauto.
  clear HPQ HP He. induction n as [|n IH]; [by constructor |].
  intros Δ' e' ? He' Heval ?. destruct (decide (is_nf e')) as [Hnf|Hnf].
  { inversion Hnf; simplify_option_equality; typed_inversion_all.
    apply ax_done; split; eauto using lrval_typed_weaken, assert_weaken. }
  apply ax_further.
  { intros Δ''; inversion_clear 3 as [mA mf|]; simplify_equality.
    destruct (is_nf_is_redex e') as (E&e''&?&->); auto.
    destruct (expr_eval_subst_ehstep Γ ρ (m ∪ mf ∪ mA) E e'' ν)
      as (e2&?&?); auto; try solve_rcred.
    eapply expr_eval_subseteq with Δ'' m τlr;
      eauto using indexes_valid_weaken, @sep_union_subseteq_l_transitive,
      @sep_union_subseteq_l', expr_typed_weaken. }
  intros Δ'' ??; inversion_clear 3 as [mA mf|]; intros p; simplify_equality'.
  pattern S'. apply (rcstep_focus_inv _ _ _ _ _ _ p); clear p; try done.
  * intros E e1 e2 m2 -> p ?.
    rewrite expr_eval_subst in Heval; destruct Heval as (ν'&?&?).
    destruct (ectx_subst_typed_rev Γ Δ'' (ρ.*2) E e1 τlr)
      as (τlr''&?&?); eauto using expr_typed_weaken.
    rewrite ectx_subst_locks in He'; decompose_empty.
    assert (⟦ e1 ⟧ Γ ρ (m ∪ mf ∪ mA) = Some ν').
    { eapply expr_eval_subseteq with Δ'' m τlr'';
        eauto using indexes_valid_weaken, @sep_union_subseteq_l_transitive,
        @sep_union_subseteq_l', expr_typed_weaken. }
    assert (locks (subst E e2) = ∅).
    { erewrite ectx_subst_locks, ehstep_expr_eval_locks by eauto.
      esolve_elem_of. }
    assert (m ∪ mf ∪ mA = m2) by eauto using ehstep_expr_eval_mem; subst.
    apply mk_ax_next with Δ'' m; auto.
    { apply ax_unframe_expr_to_expr; auto. }
    { esolve_elem_of. }
    apply IH; eauto 7 using
      ectx_subst_typed, ehstep_expr_eval_typed, indexes_valid_weaken.
    by erewrite (subst_preserves_expr_eval _ _ _ _ _ (%# ν')%E)
      by (simplify_option_equality; eauto using ehstep_expr_eval).
  * intros E Ω f τs Ωs vs ? -> ?.
    rewrite expr_eval_subst in Heval;
      destruct Heval as (?&?&?); simplify_option_equality.
  * intros E e1 -> ? []; simpl; rewrite <-sep_associative by auto.
    apply expr_eval_subst_ehsafe with E ν; auto.
    eapply expr_eval_subseteq with Δ'' m τlr;
      eauto using indexes_valid_weaken, @sep_union_subseteq_l_transitive,
      @sep_union_subseteq_l', expr_typed_weaken.
Qed.
Lemma ax_rtol Γ δ A P Q1 Q2 e :
  (∀ v, Q1 (inr v) ⊆{Γ} (∃ a, Q2 (inl a) ∧ .*#v ⇓ inl a)%A) →
  Γ\ δ\ A ⊨ₑ {{ P }} e {{ Q1 }} →
  Γ\ δ\ A ⊨ₑ {{ P }} .* e {{ Q2 }}.
Proof.
  intros HQ Hax Δ n ρ m [τ|] ??? He1e2 He ???; typed_inversion_all.
  apply (ax_expr_compose_1 Γ δ n A Q1 _ Δ DCRtoL e ρ m (inr (TType τ.*))); auto.
  { esolve_elem_of. }
  clear dependent m; intros Δ' Ω [|v] m ?????; typed_inversion_all.
  destruct (HQ v Γ Δ' ρ (cmap_erase m))
    as (a&?&[τ'|]&?&?); eauto using indexes_valid_weaken;
    simplify_option_equality; typed_inversion_all.
  assert (TType τ' = TType τ); [|simplify_equality].
  { by apply typed_unique with (Γ,Δ') a. }
  apply ax_further_pred.
  { intros Δ'' ???? Hframe; inversion_clear Hframe as [mA mf|];
      simplify_equality; simplify_mem_disjoint_hyps.
    assert (index_alive' (m ∪ mf ∪ mA) (addr_index a)).
    { apply cmap_subseteq_index_alive' with m;
        eauto using @sep_union_subseteq_l_transitive, @sep_union_subseteq_l'.
      by rewrite <-index_alive_erase'. }
    solve_rcred. }
  intros Δ'' ?? S' ?? Hframe p _; inversion_clear Hframe as [mA mf|];
    simplify_equality; simplify_mem_disjoint_hyps.
  assert (index_alive' (m ∪ mf ∪ mA) (addr_index a)).
  { apply cmap_subseteq_index_alive' with m;
      eauto using @sep_union_subseteq_l_transitive, @sep_union_subseteq_l'.
    by rewrite <-index_alive_erase'. }
  inv_rcstep p; [inv_ehstep|exfalso; eauto with cstep].
  apply mk_ax_next with Δ'' m; auto.
  { constructor; auto. }
  { esolve_elem_of. }
  apply ax_done; constructor; eauto using addr_typed_weaken,
    assert_weaken, indexes_valid_weaken.
Qed.
Lemma ax_rofl Γ δ A P Q1 Q2 e :
  (∀ a, Q1 (inl a) ⊆{Γ} Q2 (inr (ptrV (Ptr a)))) →
  Γ\ δ\ A ⊨ₑ {{ P }} e {{ Q1 }} →
  Γ\ δ\ A ⊨ₑ {{ P }} & e {{ Q2 }}.
Proof.
  intros HQ Hax Δ n ρ m [τ|] ??? He1e2 He ???; typed_inversion_all.
  apply (ax_expr_compose_1 Γ δ n A Q1 _ Δ DCRofL e ρ m (inl τ)); auto.
  { esolve_elem_of. }
  clear dependent m; intros Δ' Ω [a|] m ?????; typed_inversion_all.
  apply ax_further_pred; [intros; solve_rcred|].
  intros Δ'' ?? S' ?? Hframe p _; inversion_clear Hframe as [mA mf|];
    simplify_equality; simplify_mem_disjoint_hyps.
  inv_rcstep p; [inv_ehstep|exfalso; eauto with cstep].
  apply mk_ax_next with Δ'' m; auto.
  { constructor; auto. } 
  { esolve_elem_of. }
  apply ax_done; constructor; eauto 7 using addr_typed_weaken.
  apply HQ; eauto using assert_weaken, indexes_valid_weaken.
Qed.
Lemma ax_load Γ δ A P Q1 Q2 e :
  (∀ a, Q1 (inl a) ⊆{Γ} (∃ v, Q2 (inr v) ∧ load (%a) ⇓ inr v)%A) →
  Γ\ δ\ A ⊨ₑ {{ P }} e {{ Q1 }} →
  Γ\ δ\ A ⊨ₑ {{ P }} load e {{ Q2 }}.
Proof.
  intros HQ Hax Δ n ρ m [|τ] ?????? HA HP; typed_inversion_all.
  apply (ax_expr_compose_1 Γ δ n A Q1 _ Δ DCLoad e ρ m (inl τ)); auto.
  { esolve_elem_of. }
  clear dependent m. intros Δ' Ω [a|] m ?????; typed_inversion_all.
  destruct (HQ a Γ Δ' ρ (cmap_erase m))
    as (v&?&?&_&?); eauto using indexes_valid_weaken; simplify_option_equality.
  assert (m !!{Γ} a = Some v) by (by rewrite <-mem_lookup_erase).
  apply ax_further_pred.
  { intros Δ'' ???? Hframe;
      inversion_clear Hframe as [mf mA|]; simplify_equality.
    assert ((m ∪ mA ∪ mf) !!{Γ} a = Some v).
    { apply mem_lookup_subseteq with Δ'' m;
        eauto using @sep_union_subseteq_l_transitive, @sep_union_subseteq_l'. }
    solve_rcred. }
  intros Δ'' ?? S' ?? Hframe p _;
    inversion_clear Hframe as [mf mA|]; simplify_equality.
  assert ((m ∪ mA ∪ mf) !!{Γ} a = Some v).
  { apply mem_lookup_subseteq with Δ'' m;
      eauto using @sep_union_subseteq_l_transitive, @sep_union_subseteq_l'. }
  inv_rcstep p; [inv_ehstep; simplify_equality|exfalso; eauto with cstep].
  erewrite <-sep_associative, mem_force_union by eauto.
  rewrite mem_forced_force by (by rewrite <-mem_forced_erase).
  rewrite sep_associative by auto.
  apply mk_ax_next with Δ'' m; simpl; auto.
  { constructor; auto. }
  apply ax_done; constructor; eauto using mem_lookup_typed,
    assert_weaken, indexes_valid_weaken, addr_typed_weaken.
Qed.
Definition assign_assert (va v : val K)
    (ass : assign) (τ : type K) (va' v' : val K) : assert K :=
  match ass with
  | Assign => cast{τ} (#v) ⇓ inr va' ∧ cast{τ} (#v) ⇓ inr v'
  | PreOp op =>
     cast{τ} (#va @{op} #v) ⇓ inr va' ∧ cast{τ} (#va @{op} #v) ⇓ inr v'
  | PostOp op => cast{τ} (#va @{op} #v) ⇓ inr va' ∧ #va ⇓ inr v'
  end%A.

Lemma ax_assign Γ δ A P1 P2 Q1 Q2 Q ass e1 e2 μ x τ :
  Some Writable ⊆ perm_kind x →
  (∀ a v, (Q1 (inl a) ★ Q2 (inr v))%A ⊆{Γ} (∃ va v' va',
    (%a ↦{μ,x} #va : τ ★
    (%a ↦{μ,perm_lock x} # (freeze true va') : τ -★ Q (inr v'))) ∧
    assign_assert va v ass τ va' v')%A) →
  Γ\ δ\ A ⊨ₑ {{ P1 }} e1 {{ Q1 }} → Γ\ δ\ A ⊨ₑ {{ P2 }} e2 {{ Q2 }} →
  Γ\ δ\ A ⊨ₑ {{ P1 ★ P2 }} e1 ::={ass} e2 {{ Q }}.
Proof.
  intros Hx HQ Hax1 Hax2 Δ n ρ m
    [|τ1] ?? Hlock He ??? HP; [typed_inversion_all|].
  assert (Some Readable ⊆ perm_kind x)by (by transitivity (Some Writable)).
  assert (∃ τ2, (Γ, Δ, ρ.*2) ⊢ e1 : inl τ1 ∧
    (Γ, Δ, ρ.*2) ⊢ e2 : inr τ2 ∧ assign_typed τ1 τ2 ass)
    as (τ2&?&?&?) by (typed_inversion_all; eauto); clear He.
  destruct HP as (m1'&m2'&Hm12&Hm12'&?&?).
  destruct (cmap_erase_union_inv m m1' m2') as (m1&m2&->&?&->&->); auto;
    simplify_mem_disjoint_hyps; clear Hm12 Hm12'.
  rewrite mem_locks_union in Hlock by auto; simpl in *; decompose_empty.
  apply (ax_expr_compose_2 Γ δ n A Q1 Q2 _ Δ (DCAssign ass) e1 e2 ρ m1 m2
    (inl τ1) (inr τ2)); eauto using ax_expr_funframe_weaken,
    @sep_union_subseteq_l', @sep_union_subseteq_r'.
  { esolve_elem_of. }
  { esolve_elem_of. }
  clear dependent m1 m2; intros Δ' Ω1 Ω2 [a'|] [|v] m1' m2'
    ??????????; typed_inversion_all.
  destruct (HQ a' v Γ Δ' ρ (cmap_erase (m1' ∪ m2')))
    as (?&v'&va'&(m1&m2''&?&?&(a&va&?&?&?&?&?)&HQ')&Hass);
    eauto 6 using indexes_valid_weaken; clear HQ.
  { rewrite cmap_erase_union.
    exists (cmap_erase m1') (cmap_erase m2'); split_ands; auto.
    by rewrite <-!cmap_erase_disjoint_le. }
  destruct (cmap_erase_union_inv_l (m1' ∪ m2') m1 m2'')
    as (m2&Hm&?&Hm'&->); auto; rewrite Hm in *;
    simplify_option_equality; typed_inversion_all.
  assert (✓{Γ,Δ'} (m1 ∪ m2)) by (rewrite <-Hm; eauto).
  assert (TType τ = TType τ1); simplify_equality'.
  { eapply typed_unique with (Γ,Δ') a; eauto. }
  assert (✓{Γ,Δ'} (m1 ∪ m2)) by (rewrite <-Hm; eauto).
  simplify_mem_disjoint_hyps.
  assert (∀ mA mf, ⊥ [m1; m2; mA; mf] → mem_writable Γ a (m1 ∪ m2 ∪ mA ∪ mf)).
  { intros; eapply mem_writable_subseteq with Δ' m1;
      eauto using mem_writable_singleton,
      @sep_union_subseteq_l_transitive, @sep_union_subseteq_l'. }
  assert (∀ mA mf, ⊥ [m1; m2; mA; mf] →
    assign_sem Γ (m1 ∪ m2 ∪ mA ∪ mf) a v ass va' v').
  { clear HQ'; intros mA mf ?.
    eapply assign_sem_subseteq with Δ' (cmap_erase (m1 ∪ m2)) τ1 τ2;
      eauto using @sep_union_subseteq_l_transitive, cmap_erase_subseteq_l.
    destruct ass; destruct Hass as [(?&_&?) (?&_&?)];
      simplify_option_equality; econstructor; simplify_type_equality; eauto.
    * rewrite mem_lookup_erase; eapply mem_lookup_subseteq with Δ' m1;
        eauto using mem_lookup_singleton, @sep_union_subseteq_l.
    * rewrite mem_lookup_erase; eapply mem_lookup_subseteq with Δ' m1;
        eauto using mem_lookup_singleton, @sep_union_subseteq_l. }
  apply ax_further_pred.
  { intros Δ'' ???? Hframe;
      inversion_clear Hframe as [mf mA|]; simplify_equality; solve_rcred. }
  intros Δ'' ?? S' ?? Hframe p _; inversion_clear Hframe as [mf mA|];
    simplify_equality; simplify_mem_disjoint_hyps.
  inv_rcstep p; [inv_ehstep; simplify_equality|exfalso; eauto 6 with cstep].
  match goal with
  | Hass : assign_sem _ ?m _ _ _ ?va'' ?v'' |- _ =>
    destruct (assign_sem_deterministic Γ m a v ass va'' va' v'' v');
      auto; subst; clear Hass
  end.
  assert ((Γ,Δ'') ⊢ va' : τ1 ∧ (Γ,Δ'') ⊢ v' : τ1) as [].
  { eapply (assign_preservation _ _ (m1 ∪ m2 ∪ mA ∪ mf));
      eauto using addr_typed_weaken, val_typed_weaken. }
  assert (⊥ [<[a:=va']{Γ}> m1; m2; mA; mf]).
  { by rewrite <-mem_insert_disjoint_le
      by eauto using mem_writable_singleton, addr_typed_weaken. }
  assert (✓{Γ,Δ''} (<[a:=va']{Γ}> m1)).
  { eauto using mem_insert_valid, mem_writable_singleton, addr_typed_weaken. }
  assert (mem_writable Γ a (<[a:=va']{Γ}> m1)).
  { eauto 6 using mem_insert_writable,
      mem_writable_singleton, addr_typed_weaken. }
  assert (⊥ [mem_lock Γ a (<[a:=va']{Γ}> m1); m2; mA; mf]).
  { by rewrite <-mem_lock_disjoint_le by eauto using addr_typed_weaken. }
  assert (mem_locks (mem_lock Γ a (<[a:=va']{Γ}> m1) ∪ m2)
    = lock_singleton Γ a ∪ mem_locks m1' ∪ mem_locks m2').
  { erewrite mem_locks_union, mem_locks_lock, mem_locks_insert
      by eauto using mem_writable_singleton, addr_typed_weaken.
    rewrite <-!(associative_L (∪)), <-mem_locks_union, Hm,
      mem_locks_union by auto; clear; solve_elem_of. }
  rewrite <-!(sep_associative m1) by auto.
  erewrite mem_insert_union, mem_lock_union
    by eauto using mem_writable_singleton, addr_typed_weaken.
  rewrite !sep_associative by auto.
  apply mk_ax_next with Δ'' (mem_lock Γ a (<[a:=va']{Γ}> m1) ∪ m2); simpl; auto.
  { constructor; auto. }
  { by apply reflexive_eq. } 
  { rewrite <-!sep_associative by auto; auto using mem_lock_valid. }
  apply ax_done; constructor; auto.
  rewrite cmap_erase_union,
    mem_erase_lock, mem_erase_insert, cmap_erased_spec by done.
  eapply HQ'; rewrite <-?cmap_erase_disjoint_le;
    eauto using cmap_erase_valid, mem_lock_valid.
  exists a (freeze true va'); split_ands;
    eauto using addr_typed_weaken, val_typed_weaken, val_typed_freeze.
  eauto using mem_lock_singleton, mem_insert_singleton, mem_singleton_weaken.
Qed.
Lemma ax_eltl Γ δ A P Q1 Q2 e rs :
  (∀ a, Q1 (inl a) ⊆{Γ} (∃ a', Q2 (inl a') ∧ %a %> rs ⇓ inl a')%A) →
  Γ\ δ\ A ⊨ₑ {{ P }} e {{ Q1 }} →
  Γ\ δ\ A ⊨ₑ {{ P }} e %> rs {{ Q2 }}.
Proof.
  intros HQ Hax Δ n ρ m [σ|] ??? He ????; [|typed_inversion_all].
  assert (∃ τ, (Γ, Δ, ρ.*2) ⊢ e : inl τ ∧ Γ ⊢ rs : τ ↣ σ) as (τ&?&?)
    by (typed_inversion_all; eauto); clear He.
  apply (ax_expr_compose_1 Γ δ n A Q1 _ Δ (DCEltL rs) e ρ m (inl τ)); auto.
  { esolve_elem_of. }
  clear dependent m; intros Δ' Ω [a|] m ?????; typed_inversion_all.
  destruct (HQ a Γ Δ' ρ (cmap_erase m))
    as (?&?&?&_&?); eauto using indexes_valid_weaken; simplify_option_equality.
  apply ax_further_pred; [intros; solve_rcred|].
  intros Δ'' ?? S' ?? Hframe p _; inversion_clear Hframe as [mA mf|];
    simplify_equality; simplify_mem_disjoint_hyps.
  inv_rcstep p; [inv_ehstep|exfalso; eauto with cstep].
  apply mk_ax_next with Δ'' m; auto.
  { constructor; auto. }
  { esolve_elem_of. }
  apply ax_done; constructor; eauto using assert_weaken, addr_typed_weaken,
    indexes_valid_weaken, addr_elt_typed, addr_elt_strict.
Qed.
Lemma ax_eltr Γ δ A P Q1 Q2 e rs :
  (∀ v, Q1 (inr v) ⊆{Γ} (∃ v', Q2 (inr v') ∧ #v #> rs ⇓ inr v')%A) →
  Γ\ δ\ A ⊨ₑ {{ P }} e {{ Q1 }} →
  Γ\ δ\ A ⊨ₑ {{ P }} e #> rs {{ Q2 }}.
Proof.
  intros HQ Hax Δ n ρ m [|σ] ??? He ????; [typed_inversion_all|].
  assert (∃ τ, (Γ, Δ, ρ.*2) ⊢ e : inr τ ∧ Γ ⊢ rs : τ ↣ σ) as (τ&?&?)
    by (typed_inversion_all; eauto); clear He.
  apply (ax_expr_compose_1 Γ δ n A Q1 _ Δ (DCEltR rs) e ρ m (inr τ)); auto.
  { esolve_elem_of. }
  clear dependent m; intros Δ' Ω [|v] m ?????; typed_inversion_all.
  destruct (HQ v Γ Δ' ρ (cmap_erase m))
    as (v'&?&?&_&?); eauto using indexes_valid_weaken; simplify_option_equality.
  apply ax_further_pred; [intros; solve_rcred|].
  intros Δ'' ?? S' ?? Hframe p _; inversion_clear Hframe as [mA mf|];
    simplify_equality; simplify_mem_disjoint_hyps.
  inv_rcstep p; [inv_ehstep; simplify_equality'|exfalso; eauto with cstep].
  apply mk_ax_next with Δ'' m; auto.
  { constructor; auto. }
  { esolve_elem_of. }
  apply ax_done; constructor; eauto using assert_weaken,
    indexes_valid_weaken, val_typed_weaken, val_lookup_seg_typed.
Qed.
Lemma ax_insert Γ δ A P1 P2 Q1 Q2 R e1 e2 r :
  (∀ v1 v2,
    (Q1 (inr v1) ★ Q2 (inr v2))%A ⊆{Γ} (∃ v',
      R (inr v') ∧ #[r:=#v1] (#v2) ⇓ inr v')%A) →
  Γ\ δ\ A ⊨ₑ {{ P1 }} e1 {{ Q1 }} →
  Γ\ δ\ A ⊨ₑ {{ P2 }} e2 {{ Q2 }} →
  Γ\ δ\ A ⊨ₑ {{ P1 ★ P2 }} #[r:=e1] e2 {{ R }}.
Proof.
  intros HQ Hax1 Hax2 Δ n ρ m [|τ] ?? Hlocks He ??? HP; [typed_inversion_all|].
  assert (∃ σ, (Γ, Δ, ρ.*2) ⊢ e1 : inr σ ∧
    (Γ, Δ, ρ.*2) ⊢ e2 : inr τ ∧ Γ ⊢ r : τ ↣ σ) as (σ&?&?&?)
    by (typed_inversion_all; eauto); clear He.
  destruct HP as (m1'&m2'&?&?&?&?).
  destruct (cmap_erase_union_inv m m1' m2')
    as (m1&m2&->&?&->&->); simplify_mem_disjoint_hyps; auto.
  rewrite mem_locks_union in Hlocks by auto; simpl in *; decompose_empty.
  apply (ax_expr_compose_2 Γ δ n A Q1 Q2 _ Δ (DCInsert r)
    e1 e2 ρ m1 m2 (inr σ) (inr τ)); eauto using ax_expr_funframe_weaken,
    @sep_union_subseteq_l', @sep_union_subseteq_r'.
  { esolve_elem_of. }
  { esolve_elem_of. }
  clear dependent m1 m2; intros Δ' Ω1 Ω2 [|v1] [|v2] m1 m2
    ??????????; typed_inversion_all.
  destruct (HQ v1 v2 Γ Δ' ρ (cmap_erase (m1 ∪ m2)))
    as (v'&?&?&_&?); eauto 6 using indexes_valid_weaken.
  { rewrite cmap_erase_union.
    exists (cmap_erase m1) (cmap_erase m2); split_ands; auto.
    by rewrite <-!cmap_erase_disjoint_le. }
  simplify_option_equality.
  apply ax_further_pred; [intros; solve_rcred|].
  intros Δ'' ?? S' ?? Hframe p _; inversion_clear Hframe as [mA mf|];
    simplify_equality; simplify_mem_disjoint_hyps.
  inv_rcstep p; [inv_ehstep; simplify_equality'|exfalso; eauto with cstep].
  rewrite <-mem_locks_union by auto.
  apply mk_ax_next with Δ'' (m1 ∪ m2); auto.
  { constructor; auto. }
  { simpl. by rewrite mem_locks_union by auto. }
  apply ax_done; constructor; eauto using assert_weaken,
    indexes_valid_weaken, val_typed_weaken, val_alter_const_typed.
Qed.
Lemma ax_alloc Γ δ A P Q1 Q2 e τ :
  ¬alloc_can_fail →
  (∀ o vb,
    Q1 (inr (VBase vb)) ⊆{Γ} (∃ n τi,
      ⌜ vb = (intV{τi} n)%B ∧ Z.to_nat n ≠ 0 ⌝ ★
      (% (addr_top o (τ.[Z.to_nat n])) ↦{true,perm_full} - : (τ.[Z.to_nat n]) -★
        Q2 (inr (ptrV (Ptr (addr_top_array o τ n))))))%A) →
  Γ\ δ\ A ⊨ₑ {{ P }} e {{ Q1 }} →
  Γ\ δ\ A ⊨ₑ {{ P }} alloc{τ} e {{ Q2 }}.
Proof.
  intros ? HQ Hax Δ n ρ m τlr ??? He ????.
  assert (∃ τi, (Γ,Δ,ρ.*2) ⊢ e : inr (intT τi) ∧
    ✓{Γ} τ ∧ τlr = inr (TType τ.*)) as (τi&?&?&->)
    by (typed_inversion_all; eauto); clear He.
  apply (ax_expr_compose_1 Γ δ n A Q1 _ Δ
    (DCAlloc τ) e ρ m (inr (intT τi))); auto.
  { esolve_elem_of. }
  clear dependent m; intros Δ' Ω [|[vb| | | |]] m ?????; typed_inversion_all.
  destruct (HQ (fresh ∅) vb Γ Δ' ρ (cmap_erase m))
    as (n'&τi'&_&_&_&_&[[-> ?] _]&_); eauto using indexes_valid_weaken;
    typed_inversion_all.
  apply ax_further_pred; [intros; solve_rcred|].
  intros Δ'' ?? S' ?? Hframe p Hdom; inversion_clear Hframe as [mA mf|];
    simplify_equality; simplify_mem_disjoint_hyps.
  assert (∃ o,
    S' = State [] (Expr (#{mem_locks m} ptrV (Ptr (addr_top_array o τ n'))))
      (mem_alloc Γ o true perm_full (val_new Γ (τ.[Z.to_nat n']))
      (m ∪ mf ∪ mA)) ∧ o ∉ dom indexset (m ∪ mf ∪ mA))
      as (o&->&Ho); [|simplify_equality'; clear p].
  { inv_rcstep p; [inv_ehstep; by eauto|exfalso; eauto with cstep]. }
  assert (Δ'' !! o = None); [|clear Hdom].
  { rewrite mem_dom_alloc in Hdom. apply not_elem_of_dom; esolve_elem_of. }
  rewrite <-sep_associative, cmap_dom_union,
    not_elem_of_union in Ho by auto; destruct Ho.
  assert (✓{Γ} (τ.[Z.to_nat n'])) by eauto using TArray_valid.
  assert (
    mem_alloc Γ o true perm_full (val_new Γ (τ.[Z.to_nat n'])) m ⊥ mf ∪ mA)
    by eauto using (mem_alloc_disjoint _ Δ'); simplify_mem_disjoint_hyps.
  apply mk_ax_next with (<[o:=(τ.[Z.to_nat n'],false)]>Δ'')
    (mem_alloc Γ o true perm_full (val_new Γ (τ.[Z.to_nat n'])) m);
    eauto using mem_alloc_forward, mem_alloc_forward_least.
  { rewrite <-sep_associative, !mem_alloc_union, sep_associative by auto.
    constructor; auto. }
  { simpl. by erewrite (mem_locks_alloc _ Δ'') by eauto. }
  apply ax_done; constructor; eauto 8 using addr_top_array_typed,
    mem_alloc_index_typed, (mem_locks_alloc _ Δ'').
  destruct (mem_alloc_singleton Γ Δ'' m o true perm_full
    (val_new Γ (τ.[Z.to_nat n'])) (τ.[Z.to_nat n']))
    as (m'&Hm'&?&?); auto using val_new_frozen.
  rewrite Hm' in *; simplify_mem_disjoint_hyps; clear Hm'.
  erewrite cmap_erase_union, mem_erase_singleton by eauto.
  destruct (HQ o (intV{τi} n')%B Γ Δ' ρ (cmap_erase m))
    as (n''&τi''&_&m''&Hm''&?&[[? _] ->]&HQ2); eauto using indexes_valid_weaken.
  rewrite sep_left_id in Hm'' by auto; simplify_equality'.
  eapply HQ2; eauto using mem_alloc_forward, indexes_valid_weaken; clear HQ2.
  { by eapply mem_singleton_valid;
      eauto using mem_alloc_memenv_valid, mem_alloc_index_alive. }
  { eauto using mem_alloc_orig_valid. }
  { by rewrite <-cmap_erase_disjoint_le. }
  eexists _, (addr_top o (τ.[Z.to_nat n''])), (val_new Γ (τ.[Z.to_nat n'']));
    split_ands; eauto using addr_top_typed, mem_alloc_index_typed.
Qed.
Lemma ax_free Γ δ A P Q1 Q2 e τ :
  (∀ a,
    Q1 (inl a) ⊆{Γ} (∃ n,
      ⌜ addr_is_top_array a ⌝ ★
      % addr_top (addr_index a) (τ.[n]) ↦{true,perm_full} - : (τ.[n]) ★
      Q2 (inr voidV))%A) →
  Γ\ δ\ A ⊨ₑ {{ P }} e {{ Q1 }} →
  Γ\ δ\ A ⊨ₑ {{ P }} free e {{ Q2 }}.
Proof.
  intros HQ Hax Δ n ρ m τlr ??? He ????.
  assert (∃ τ', (Γ,Δ,ρ.*2) ⊢ e : inl τ' ∧ τlr = inr voidT) as (τ'&?&->)
    by (typed_inversion_all; eauto); clear He.
  apply (ax_expr_compose_1 Γ δ n A Q1 _ Δ DCFree e ρ m (inl τ')); auto.
  { esolve_elem_of. }
  clear dependent m; intros Δ' Ω [a|] m ?????; typed_inversion_all.
  destruct (HQ a Γ Δ' ρ (cmap_erase m))
    as (n'&?&?&Hm'&?&[Ha' ->]&m1&m2'&?&?&(ν&a'&v&_&?&?&?&?)&?);
    eauto using indexes_valid_weaken.
  rewrite sep_left_id in Hm' by auto;
    simplify_option_equality; typed_inversion_all.
  destruct (cmap_erase_union_inv_l m m1 m2')
    as (m2&->&Hm12'&_&->); auto; simplify_mem_disjoint_hyps.
  assert (∀ mf mA, ⊥ [m1; m2; mf; mA] → mem_freeable a (m1 ∪ m2 ∪ mf ∪ mA)).
  { split; eauto using (mem_freeable_perm_singleton _ Δ').
    eapply mem_freeable_perm_subseteq; eauto using mem_freeable_perm_singleton,
      @sep_union_subseteq_l', @sep_union_subseteq_l_transitive. }
  apply ax_further_pred.
  { intros Δ'' ???? Hframe; inversion_clear Hframe as [mA mf|];
      simplify_equality; simplify_mem_disjoint_hyps; solve_rcred. }
  intros Δ'' ?? S' ?? Hframe p _; inversion_clear Hframe as [mA mf|];
    simplify_equality; simplify_mem_disjoint_hyps.
  inv_rcstep p; [inv_ehstep|exfalso; eauto with cstep].
  match goal with H : mem_freeable _ _ |- _ => destruct H end.
  assert (mem_freeable_perm (addr_index a) true m1)
    by eauto using mem_freeable_perm_singleton.
  assert (⊥ [mem_free (addr_index a) m1; m2; mf; mA])
    by (by rewrite <-mem_free_disjoint_le by eauto).
  apply mk_ax_next with
    (alter (prod_map id (λ _, true)) (addr_index a) Δ'')
    (mem_free (addr_index a) (m1 ∪ m2));
    eauto using mem_free_forward, mem_free_forward_least.
  { erewrite <-!(sep_associative m1), !mem_free_union by eauto.
    rewrite !sep_associative by eauto; constructor; auto. }
  { simpl. by erewrite mem_locks_free
      by eauto using mem_freeable_perm_subseteq, @sep_union_subseteq_l'. }
  apply ax_done; constructor; eauto.
  { by erewrite mem_locks_free
      by eauto using mem_freeable_perm_subseteq, @sep_union_subseteq_l'. }
  erewrite mem_free_union, cmap_erase_union, mem_free_singleton, sep_left_id
    by eauto using mem_freeable_perm_singleton.
  eauto using assert_weaken, mem_free_forward, indexes_valid_weaken.
Qed.
Lemma ax_unop Γ δ A P Q1 Q2 op e :
  (∀ v, Q1 (inr v) ⊆{Γ} (∃ v', Q2 (inr v') ∧ @{op} #v ⇓ inr v')%A) →
  Γ\ δ\ A ⊨ₑ {{ P }} e {{ Q1 }} →
  Γ\ δ\ A ⊨ₑ {{ P }} @{op} e {{ Q2 }}.
Proof.
  intros HQ Hax Δ n ρ m [|σ] ??? He ?? HA HP; [typed_inversion_all|].
  assert (∃ τ, (Γ, Δ, ρ.*2) ⊢ e : inr τ ∧ unop_typed op τ σ)
    as (τ&?&?) by (typed_inversion_all; eauto); clear He.
  apply (ax_expr_compose_1 Γ δ n A Q1 _ Δ (DCUnOp op) e ρ m (inr τ)); auto.
  { esolve_elem_of. }
  clear dependent m. intros Δ' Ω [a|] m ?????; typed_inversion_all.
  destruct (HQ v Γ Δ' ρ (cmap_erase m))
    as (v'&?&?&_&?); eauto using indexes_valid_weaken; simplify_option_equality.
  assert (val_unop_ok m op v) by (by rewrite <-val_unop_ok_erase).
  apply ax_further_pred.
  { intros Δ'' ???? Hframe;
      inversion_clear Hframe as [mf mA|]; simplify_equality.
    assert (val_unop_ok (m ∪ mA ∪ mf) op v).
    { eapply val_unop_ok_weaken with m; eauto using cmap_subseteq_index_alive,
        @sep_union_subseteq_l_transitive, @sep_union_subseteq_l'. }
    solve_rcred. }
  intros Δ'' ?? S' ?? Hframe p _;
    inversion_clear Hframe as [mf mA|]; simplify_equality.
  assert (val_unop_ok (m ∪ mA ∪ mf) op v).
  { eapply val_unop_ok_weaken with m; eauto using cmap_subseteq_index_alive,
      @sep_union_subseteq_l_transitive, @sep_union_subseteq_l'. }
  inv_rcstep p; [inv_ehstep; simplify_equality|exfalso; eauto with cstep].
  apply mk_ax_next with Δ'' m; simpl; auto.
  { constructor; auto. }
  apply ax_done; constructor; eauto using mem_lookup_typed,
    indexes_valid_weaken, assert_weaken, val_unop_typed, val_typed_weaken.
Qed.
Lemma ax_binop Γ δ A P1 P2 Q1 Q2 R op e1 e2 :
  (∀ v1 v2,
    (Q1 (inr v1) ★ Q2 (inr v2))%A ⊆{Γ} (∃ v,
      R (inr v) ∧ # v1 @{op} # v2 ⇓ inr v)%A) →
  Γ\ δ\ A ⊨ₑ {{ P1 }} e1 {{ Q1 }} →
  Γ\ δ\ A ⊨ₑ {{ P2 }} e2 {{ Q2 }} →
  Γ\ δ\ A ⊨ₑ {{ P1 ★ P2 }} e1 @{op} e2 {{ R }}.
Proof.
  intros HQ Hax1 Hax2 Δ n ρ m [|σ] ?? Hlock He ?? HA HP; [typed_inversion_all|].
  assert (∃ τ1 τ2, (Γ, Δ, ρ.*2) ⊢ e1 : inr τ1 ∧
    (Γ, Δ, ρ.*2) ⊢ e2 : inr τ2 ∧ binop_typed op τ1 τ2 σ)
    as (τ1&τ2&?&?&?) by (typed_inversion_all; eauto); clear He.
  destruct HP as (m1'&m2'&?&?&?&?).
  destruct (cmap_erase_union_inv m m1' m2')
    as (m1&m2&->&?&->&->); simplify_mem_disjoint_hyps; auto.
  rewrite mem_locks_union in Hlock by auto; simpl in *; decompose_empty.
  apply (ax_expr_compose_2 Γ δ n A Q1 Q2 _ Δ (DCBinOp op) e1 e2 ρ m1 m2
    (inr τ1) (inr τ2)); eauto using ax_expr_funframe_weaken,
    @sep_union_subseteq_l', @sep_union_subseteq_r'.
  { esolve_elem_of. }
  { esolve_elem_of. }
  clear dependent m1 m2; intros Δ' Ω1 Ω2 [|v1] [|v2] m1 m2
    ??????????; typed_inversion_all.
  destruct (HQ v1 v2 Γ Δ' ρ (cmap_erase (m1 ∪ m2)))
    as (v'&?&?&_&?); eauto 6 using indexes_valid_weaken.
  { rewrite cmap_erase_union.
    exists (cmap_erase m1) (cmap_erase m2); split_ands; auto.
    by rewrite <-!cmap_erase_disjoint_le. }
  simplify_option_equality.
  assert (val_binop_ok Γ (m1 ∪ m2) op v1 v2)
    by (by rewrite <-val_binop_ok_erase).
  apply ax_further_pred.
  { intros Δ'' ???? Hframe;
      inversion_clear Hframe as [mf mA|]; simplify_equality.
    assert (val_binop_ok Γ (m1 ∪ m2 ∪ mA ∪ mf) op v1 v2).
    { eapply val_binop_ok_weaken with Γ Δ' (m1 ∪ m2) τ1 τ2;
        eauto 4 using cmap_subseteq_index_alive,
        @sep_union_subseteq_l_transitive, @sep_union_subseteq_l'. }
    solve_rcred. }
  intros Δ'' ?? S' ?? Hframe p _;
    inversion_clear Hframe as [mf mA|]; simplify_equality.
  assert (val_binop_ok Γ (m1 ∪ m2 ∪ mA ∪ mf) op v1 v2).
  { eapply val_binop_ok_weaken with Γ Δ' (m1 ∪ m2) τ1 τ2;
      eauto 4 using cmap_subseteq_index_alive,
      @sep_union_subseteq_l_transitive, @sep_union_subseteq_l'. }
  inv_rcstep p; [inv_ehstep; simplify_equality|exfalso; eauto with cstep].
  rewrite <-mem_locks_union by auto.
  apply mk_ax_next with Δ'' (m1 ∪ m2); simpl; auto.
  { constructor; auto. }
  apply ax_done; constructor; eauto using mem_lookup_typed,
    indexes_valid_weaken, assert_weaken, val_binop_typed, val_typed_weaken.
Qed.
Lemma ax_cast Γ δ A P Q1 Q2 σ e :
  (∀ v, Q1 (inr v) ⊆{Γ} (∃ v', Q2 (inr v') ∧ cast{σ} (#v) ⇓ inr v')%A) →
  Γ\ δ\ A ⊨ₑ {{ P }} e {{ Q1 }} →
  Γ\ δ\ A ⊨ₑ {{ P }} cast{σ} e {{ Q2 }}.
Proof.
  intros HQ Hax Δ n ρ m [|σ'] ??? He ?? HA HP; [typed_inversion_all|].
  assert (∃ τ, (Γ, Δ, ρ.*2) ⊢ e : inr τ ∧ cast_typed τ σ ∧ ✓{Γ} σ ∧ σ' = σ)
    as (τ&?&?&?&->) by (typed_inversion_all; eauto); clear He.
  apply (ax_expr_compose_1 Γ δ n A Q1 _ Δ (DCCast σ) e ρ m (inr τ)); auto.
  { esolve_elem_of. }
  clear dependent m. intros Δ' Ω [a|] m ?????; typed_inversion_all.
  destruct (HQ v Γ Δ' ρ (cmap_erase m))
    as (v'&?&_&_&?); eauto using indexes_valid_weaken; simplify_option_equality.
  assert (val_cast_ok Γ m (TType σ) v) by (by rewrite <-val_cast_ok_erase).
  apply ax_further_pred.
  { intros Δ'' ???? Hframe;
      inversion_clear Hframe as [mf mA|]; simplify_equality.
    assert (val_cast_ok Γ (m ∪ mA ∪ mf) (TType σ) v).
    { eapply val_cast_ok_weaken with Γ Δ' m τ;
        eauto using cmap_subseteq_index_alive,
        @sep_union_subseteq_l_transitive, @sep_union_subseteq_l'. }
    solve_rcred. }
  intros Δ'' ?? S' ?? Hframe p _;
    inversion_clear Hframe as [mf mA|]; simplify_equality.
  assert (val_cast_ok Γ (m ∪ mA ∪ mf) (TType σ) v).
  { eapply val_cast_ok_weaken with Γ Δ' m τ;
      eauto using cmap_subseteq_index_alive,
      @sep_union_subseteq_l_transitive, @sep_union_subseteq_l'. }
  inv_rcstep p; [inv_ehstep; simplify_equality|exfalso; eauto with cstep].
  apply mk_ax_next with Δ'' m; simpl; auto.
  { constructor; auto. }
  apply ax_done; constructor; eauto using mem_lookup_typed,
    indexes_valid_weaken, assert_weaken, val_cast_typed, val_typed_weaken.
Qed.
Lemma ax_expr_if Γ δ A P P' P1 P2 Q e e1 e2 :
  (∀ vb, P' (inr (VBase vb)) ⊆{Γ} (@{NotOp} #VBase vb ⇓ -)%A) →
  (∀ vb, ¬base_val_is_0 vb → P' (inr (VBase vb)) ⊆{Γ} (P1 ○)%A) →
  (∀ vb, base_val_is_0 vb → P' (inr (VBase vb)) ⊆{Γ} (P2 ○)%A) →
  Γ\ δ\ A ⊨ₑ {{ P }} e {{ P' }} →
  Γ\ δ\ A ⊨ₑ {{ P1 }} e1 {{ Q }} → Γ\ δ\ A ⊨ₑ {{ P2 }} e2 {{ Q }} →
  Γ\ δ\ A ⊨ₑ {{ P }} if{e} e1 else e2 {{ Q }}.
Proof.
  intros HP' HP1 HP2 Hax Hax1 Hax2 Δ n ρ m τlr ??? He ????;
    simpl in *; decompose_empty.
  assert (∃ τb, (Γ,Δ,ρ.*2) ⊢ e : inr (baseT τb) ∧ τb ≠ voidT%BT ∧
    (Γ,Δ,ρ.*2) ⊢ e1 : τlr ∧ (Γ,Δ,ρ.*2) ⊢ e2 : τlr)
    as (τb&?&?&?&?) by (typed_inversion_all; eauto); clear He.
  apply (ax_expr_compose_1 Γ δ n A
    P' _ Δ (DCIf e1 e2) e ρ m (inr (baseT τb))); auto.
  { esolve_elem_of. }
  { esolve_elem_of. }
  clear dependent m; intros Δ' Ω [|[vb| | | |]] m ?????; typed_inversion_all.
  assert (base_val_branchable m vb).
  { rewrite <-base_val_branchable_erase.
    by destruct (HP' vb Γ Δ' ρ (cmap_erase m)) as (?&?&?&?);
      eauto using indexes_valid_weaken; simplify_option_equality. }
  apply ax_further_pred.
  { intros Δ'' m'' ? _ _ Hframe;
      inversion_clear Hframe as [mf mA|]; simplify_equality.
    assert (base_val_branchable (m ∪ mA ∪ mf) vb).
    { eapply base_val_branchable_weaken; eauto using cmap_subseteq_index_alive,
        @sep_union_subseteq_l_transitive, @sep_union_subseteq_l. }
    destruct (decide (base_val_is_0 vb)); solve_rcred. }
  intros Δ''' ?? S' ?? Hframe p _; inversion_clear Hframe as [mA mf|];
    simplify_equality; simplify_mem_disjoint_hyps.
  assert (⊥ [mem_unlock_all m; mf; mA])
    by (rewrite <-mem_unlock_all_disjoint_le; auto).
  assert (base_val_branchable (m ∪ mf ∪ mA) vb).
  { eapply base_val_branchable_weaken; eauto using cmap_subseteq_index_alive,
      @sep_union_subseteq_l_transitive, @sep_union_subseteq_l. }
  inv_rcstep p; [inv_ehstep|].
  * rewrite !mem_unlock_union, <-mem_unlock_all_spec
      by (rewrite ?mem_locks_union by auto; solve_elem_of).
    apply mk_ax_next with Δ''' (mem_unlock_all m); auto.
    { constructor; auto. }
    { esolve_elem_of. }
    { eauto using mem_unlock_all_valid. }
    apply Hax1; rewrite ?mem_erase_unlock_all;
      eauto 8 using mem_unlock_all_valid, indexes_valid_weaken,
      mem_locks_unlock_all, expr_typed_weaken.
    + exists mA; split_ands; eauto.
    + eapply HP1; eauto using indexes_valid_weaken, assert_weaken.
  * rewrite !mem_unlock_union, <-mem_unlock_all_spec
      by (rewrite ?mem_locks_union by auto; solve_elem_of).
    apply mk_ax_next with Δ''' (mem_unlock_all m); auto.
    { constructor; auto. }
    { esolve_elem_of. }
    { eauto using mem_unlock_all_valid. }
    apply Hax2; rewrite ?mem_erase_unlock_all;
      eauto 8 using mem_unlock_all_valid, indexes_valid_weaken,
      mem_locks_unlock_all, expr_typed_weaken.
    + exists mA; split_ands; eauto.
    + eapply HP2; eauto using indexes_valid_weaken, assert_weaken.
  * destruct (decide (base_val_is_0 vb)); exfalso; eauto with cstep.
Qed.
Lemma ax_expr_comma Γ δ A P P' Q e1 e2 :
  Γ\ δ\ A ⊨ₑ {{ P }} e1 {{ λ _, P' ○ }} →
  Γ\ δ\ A ⊨ₑ {{ P' }} e2 {{ Q }} →
  Γ\ δ\ A ⊨ₑ {{ P }} e1 ,, e2 {{ Q }}.
Proof.
  intros Hax1 Hax2 Δ n ρ m τlr2 ??? He1e2 He ???.
  assert (∃ τlr1, (Γ, Δ, ρ.*2) ⊢ e1 : τlr1 ∧ (Γ, Δ, ρ.*2) ⊢ e2 : τlr2)
    as (τlr1&?&?) by (typed_inversion_all; eauto); clear He1e2.
  simpl in He; decompose_empty.
  apply (ax_expr_compose_1 Γ δ n A
    (λ _, P' ○)%A _ Δ (DCComma e2) e1 ρ m τlr1); auto.
  { esolve_elem_of. }
  clear dependent m; intros Δ' Ω ν m ?????; simplify_equality'.
  apply ax_further_pred; [intros; solve_rcred|].
  intros Δ'' ?? S' ?? Hframe p _; inversion_clear Hframe as [mA mf|];
    simplify_equality; simplify_mem_disjoint_hyps.
  inv_rcstep p; [inv_ehstep|exfalso; eauto with cstep].
  rewrite !mem_unlock_union, <-mem_unlock_all_spec
    by (rewrite ?mem_locks_union by auto; solve_elem_of).
  assert (⊥ [mem_unlock_all m; mf; mA])
    by (rewrite <-mem_unlock_all_disjoint_le; auto).
  apply mk_ax_next with Δ'' (mem_unlock_all m); auto.
  { constructor; auto. }
  { esolve_elem_of. }
  { eauto using mem_unlock_all_valid. }
  apply Hax2; rewrite ?mem_erase_unlock_all;
    eauto 7 using mem_unlock_all_valid, indexes_valid_weaken,
    mem_locks_unlock_all, expr_typed_weaken, assert_weaken.
  exists mA; split_ands; eauto.
Qed.
End axiomatic_expressions.
