(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
From stdpp Require Import fin_map_dom.
Require Export axiomatic.
Require Import axiomatic_graph type_system_decidable.

Local Open Scope ctype_scope.

Section axiomatic_statements.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types Δ : memenv K.
Implicit Types δ : funenv K.
Implicit Types e : expr K.
Implicit Types s : stmt K.
Implicit Types τ σ : type K.
Implicit Types a : addr K.
Implicit Types v : val K.
Implicit Types ν : lrval K.
Implicit Types Pd : dassert K.

Hint Extern 1 (_ ## _) => solve_mem_disjoint: core.
Hint Extern 1 (## _) => solve_mem_disjoint: core.
Hint Extern 1 (sep_valid _) => solve_mem_disjoint: core.
Hint Extern 1 (_ ≤ _) => lia: core.

Hint Immediate cmap_valid_memenv_valid: core.
Hint Resolve cmap_empty_valid cmap_erased_empty mem_locks_empty: core.
Hint Resolve cmap_union_valid_2 cmap_erased_union cmap_erase_valid: core.

Hint Immediate ax_disjoint_expr_compose_diagram: core.
Hint Immediate ax_expr_disjoint_compose_diagram: core.
Hint Immediate ax_expr_invariant_emp ax_disjoint_compose_diagram: core.

Hint Immediate val_new_typed perm_full_mapped lockset_empty_valid: core.
Hint Resolve mem_alloc_valid mem_free_valid: core.
Hint Extern 0 (_ ⊢ _ : _) => typed_constructor: core.
Hint Extern 0 (unframe ax_disjoint_cond _ _ _ _ _ _ _ _ _) => by constructor: core.
Hint Extern 0 (focus_locks_valid _ _) => by constructor: core.

(** ** Basic rules *)
Lemma ax_stmt_weaken_packed Γ δ Pd Pd' s :
  (∀ d, direction_in d s → Pd' d ⊆{Γ,δ} Pd d) →
  (∀ d, direction_out d s → Pd d ⊆{Γ,δ} Pd' d) →
  Γ\ δ\ Pd ⊨ₚ s → Γ\ δ\ Pd' ⊨ₚ s.
Proof.
  intros Hin Hout Hax Γ' Δ δ' n ρ d m cmτ ??????????.
  apply ax_weaken with ax_disjoint_cond (ax_stmt_post Pd s cmτ) n; auto.
  { eapply Hax, Hin; eauto. }
  destruct 2; constructor; auto.
  apply Hout; eauto using indexes_valid_weaken, funenv_valid_weaken.
Qed.
Lemma ax_stmt_weaken Γ δ R R' J J' T T' C C' P P' Q Q' s :
  (∀ v, R v ⊆{Γ,δ} R' v) →
  (∀ l, l ∉ labels s → J l ⊆{Γ,δ} J' l) →
  (∀ l, l ∈ labels s → J' l ⊆{Γ,δ} J l) →
  (∀ n, T n ⊆{Γ,δ} T' n) →
  (∀ mx, mx ∈ cases s → C' mx ⊆{Γ,δ} C mx) →
  P' ⊆{Γ,δ} P →
  Q ⊆{Γ,δ} Q' →
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ P }} s {{ Q }} →
  Γ\ δ\ R'\ J'\ T'\ C' ⊨ₛ {{ P' }} s {{ Q' }}.
Proof. intros until 7.
  by apply ax_stmt_weaken_packed; intros []; simpl; auto; intros []. Qed.
Lemma ax_stmt_weaken_pre Γ δ R J T C P P' Q s :
  P' ⊆{Γ,δ} P →
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ P }} s {{ Q }} →
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ P' }} s {{ Q }}.
Proof. intro. by apply ax_stmt_weaken_packed; intros []. Qed.
Lemma ax_stmt_weaken_post Γ δ R J T C P Q Q' s :
  Q ⊆{Γ,δ} Q' →
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ P }} s {{ Q }} →
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ P }} s {{ Q' }}.
Proof. intro. by apply ax_stmt_weaken_packed; intros []. Qed.
Lemma ax_stmt_packed_frame Γ δ A Pd s :
  Γ\ δ\ Pd ⊨ₚ s → Γ\ δ\ (@fmap _ (@directed_fmap K) _ _ (assert_sep A) Pd) ⊨ₚ s.
Proof.
  intros Hax Γ' Δ δ' n ρ d m cmτ ????? Hlocks ???.
  rewrite directed_fmap_spec; destruct 1 as (m1&m2&?&?&?&?).
  destruct (cmap_erase_union_inv m m1 m2)
    as (m1'&m2'&->&?&->&->); simplify_mem_disjoint_hyps; auto.
  rewrite mem_locks_union in Hlocks by auto; decompose_empty.
  rewrite sep_commutative by auto.
  apply ax_frame with ax_disjoint_cond (ax_stmt_post Pd s cmτ);
    eauto using ax_disjoint_cond_frame_diagram.
  intros Δ' n' φ' m' ?????; inversion_clear 1; constructor; auto.
  { rewrite mem_locks_union by auto. by apply empty_union_L. }
  rewrite directed_fmap_spec, sep_commutative, cmap_erase_union by auto.
  exists (cmap_erase m1'), (cmap_erase m'); split_and ?;eauto using assert_weaken.
  rewrite <-!cmap_erase_disjoint_le; auto.
Qed.
Lemma ax_stmt_frame_r Γ δ A R J T C P Q s :
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ P }} s {{ Q }} →
  Γ\ δ\ (λ v, R v ★ A)\ (λ l, J l ★ A)\ (λ n, T n ★ A)\ (λ mx, C mx ★ A) ⊨ₛ
    {{ P ★ A }} s {{ Q ★ A }}.
Proof.
  setoid_rewrite <-(comm (R:=(≡{Γ,δ})) (★)%A A).
  apply ax_stmt_packed_frame.
Qed.
Lemma ax_stmt_frame_l Γ δ A R J T C P Q s :
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ P }} s {{ Q }} →
  Γ\ δ\ (λ v, A ★ R v)\ (λ l, A ★ J l)\ (λ n, A ★ T n)\ (λ mx, A ★ C mx) ⊨ₛ
    {{ A ★ P }} s {{ A ★ Q }}.
Proof. apply ax_stmt_packed_frame. Qed.
Lemma ax_stmt_exist_pre `{!Inhabited A} Γ δ R J T C (P : A → assert K) Q s :
  (∀ x, Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ P x }} s {{ Q }}) →
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ ∃ x, P x }} s {{ Q }}.
Proof.
  intros Hax Γ' Δ δ' n ρ [] m cmτ ????????? Hpre; try done.
  * destruct Hpre as [x Hpre].
    apply ax_weaken with ax_disjoint_cond (ax_stmt_post
      (dassert_pack (P x) Q R J T C) s cmτ) n; auto; [eapply Hax; eauto|].
    destruct 2 as [[]]; constructor; auto. by exists x.
  * destruct (_ : Inhabited A) as [x].
    apply ax_weaken with ax_disjoint_cond (ax_stmt_post
      (dassert_pack (P x) Q R J T C) s cmτ) n; auto; [eapply Hax; eauto|].
    destruct 2 as [[]]; constructor; auto. by exists x.
  * destruct (_ : Inhabited A) as [x].
    apply ax_weaken with ax_disjoint_cond (ax_stmt_post
      (dassert_pack (P x) Q R J T C) s cmτ) n; auto; [eapply Hax; eauto|].
    destruct 2 as [[]]; constructor; auto. by exists x.
Qed.
Lemma ax_stmt_Prop_pre_packed Γ δ A Pd s :
  (∀ d, direction_in d s → Pd d ⊆{Γ,δ} (⌜ A ⌝ ★ True)%A) →
  (A → Γ\ δ\ Pd ⊨ₚ s) → Γ\ δ\ Pd ⊨ₚ s.
Proof.
  intros Hin Hax Γ' Δ δ' n ρ [] m ?????????? Hpre; try done;
    edestruct (λ d H, Hin d H Γ' Δ δ' ρ n (cmap_erase m))
    as (_&_&_&_&[? _]&_); eauto; eapply Hax; eauto.
Qed.
Lemma ax_stmt_Prop_pre Γ δ A R J T C P Q s :
  (∀ l, l ∈ labels s → J l ⊆{Γ,δ} (⌜ A ⌝ ★ True)%A) →
  (∀ mx, mx ∈ cases s → C mx ⊆{Γ,δ} (⌜ A ⌝ ★ True)%A) →
  (A → Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ P }} s {{ Q }}) →
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ ⌜ A ⌝ ★ P }} s {{ Q }}.
Proof.
  intros ?? Hax. apply (ax_stmt_Prop_pre_packed _ _ A).
  * intros [] ?; simpl in *; try by auto.
    by apply assert_sep_preserving, assert_True_intro.
  * intros. rewrite assert_Prop_l by done. by apply Hax.
Qed.

(** ** Structural rules *)
Lemma ax_do Γ δ R J T C P Q e :
  Γ\ δ\ emp ⊨ₑ {{ P }} e {{ λ _, Q ◊ }} →
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ P }} !e {{ Q }}.
Proof.
  intros Hax Γ' Δ δ' n ρ [] m cmτ ????????? He;
    typed_inversion_all; try by decompose_elem_of.
  apply ax_further; [intros; solve_rcred|].
  intros Δ' n' ? mf S' ??? (?&?&?) p _; subst; inv_rcstep p.
  econstructor; try (by eauto); [set_solver|].
  clear dependent mf S'.
  eapply (ax_compose_cons (ax_expr_cond ρ emp));
    eauto using funenv_valid_weaken.
  { apply Hax; eauto using expr_typed_weaken,
      indexes_valid_weaken, assert_weaken, funenv_valid_weaken. }
  intros Δ'' n'' m' φ' [[|v] ???] ???; typed_inversion_all.
  apply ax_further; [intros; solve_rcred|].
  intros Δ''' n''' ? mf S' ??? (?&?&?) p _; inv_rcstep p.
  rewrite mem_unlock_union, <-mem_unlock_all_spec; [|auto|set_solver].
  eapply mk_ax_next; try by eauto.
  { split. done. by rewrite <-mem_unlock_all_disjoint_le by auto. }
  { apply cmap_union_valid_2; auto using mem_unlock_all_valid.
    by rewrite <-sep_disjoint_list_double, <-mem_unlock_all_disjoint_le. }
  clear dependent m mf φ' v S'.
  apply ax_done; constructor; auto using mem_locks_unlock_all.
  rewrite mem_erase_unlock_all; simpl.
  eauto 6 using assert_weaken, mem_unlock_all_valid, indexes_valid_weaken.
Qed.
Lemma ax_skip Γ δ R J T C P : Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ P }} skip {{ P }}.
Proof.
  intros Γ' Δ δ' n k [] m cmτ ??????????;
    typed_inversion_all; try by decompose_elem_of.
  apply ax_further; [intros; solve_rcred|].
  intros Δ' n' m' mf S' ??? (?&?&?) p _; subst; inv_rcstep p.
  eapply mk_ax_next; try by eauto.
  apply ax_done; constructor; eauto using assert_weaken.
Qed.
Lemma ax_ret Γ δ R J T C P Q1 Q2 e :
  (∀ v, Q1 (inr v) ⊆{Γ,δ} (R v ◊)%A) →
  Γ\ δ\ emp ⊨ₑ {{ P }} e {{ Q1 }} →
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ P }} ret e {{ Q2 }}.
Proof.
  intros HQ Hax Γ' Δ δ' n ρ [] m cmτ ??????????;
    typed_inversion_all; try by decompose_elem_of.
  apply ax_further; [intros; solve_rcred|].
  intros Δ' n' ? mf S' ??? (?&?&?) p _; subst; inv_rcstep p.
  econstructor; try (by eauto); [set_solver|].
  clear dependent mf S'; eapply (ax_compose_cons (ax_expr_cond ρ emp));
    eauto using funenv_valid_weaken.
  { apply Hax; eauto using expr_typed_weaken,
      indexes_valid_weaken, assert_weaken, funenv_valid_weaken. }
  intros Δ'' n'' m' φ' [[|v] ???] ???; typed_inversion_all.
  apply ax_further; [intros; solve_rcred|].
  intros Δ''' n''' ? mf S' ??? (?&?&?) p _; subst; inv_rcstep p.
  rewrite mem_unlock_union, <-mem_unlock_all_spec; [|auto|set_solver].
  eapply mk_ax_next; try by eauto.
  { split. done. by rewrite <-mem_unlock_all_disjoint_le by auto. }
  { apply cmap_union_valid_2; auto using mem_unlock_all_valid.
    by rewrite <-sep_disjoint_list_double, <-mem_unlock_all_disjoint_le. }
  apply ax_done; constructor;
    eauto using mem_locks_unlock_all, val_typed_weaken.
  rewrite mem_erase_unlock_all; simpl.
  eapply HQ; eauto 6 using assert_weaken,
    mem_unlock_all_valid, indexes_valid_weaken, funenv_valid_weaken.
Qed.
Lemma ax_throw Γ δ R J T C Q i :
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ T i }} throw i {{ Q }}.
Proof.
  intros Γ' Δ δ' n k [] m cmτ ??????????; simplify_equality'; try set_solver.
  apply ax_further; [intros; solve_rcred|].
  intros Δ' n' m' mf S' ??? (?&?&?) p _; subst; inv_rcstep p.
  eapply mk_ax_next; try by eauto.
  apply ax_done; constructor; eauto using assert_weaken.
Qed.
Lemma ax_catch Γ δ R J T C P Q s :
  Γ\ δ\ R\ J\ nat_rect (λ _, _) Q (λ i _, T i)\ C ⊨ₛ {{ P }} s {{ Q }} →
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ P }} catch s {{ Q }}.
Proof.
  intros Hax Γ' Δ δ' n ρ d m cmτ ??????????; typed_inversion_all.
  apply ax_further; [intros; solve_rcred|].
  intros Δ' n' ? mf ???? (->&?&?) p _.
  assert (S' = State [CStmt (catch □)] (Stmt d s) (m ∪ mf))
    by inv_rcstep p; subst; clear p.
  apply mk_ax_next with Δ' m; auto.
  eapply ax_compose_cons; eauto using funenv_valid_weaken.
  { eapply Hax; eauto using indexes_valid_weaken,
      stmt_typed_weaken, funenv_valid_weaken.
    by destruct d as [| | | |[]| ]; eauto using assert_weaken. }
  clear dependent d m mf.
  intros Δ'' n'' φ m' [d m ??] ???; clear m'; apply ax_further.
  { destruct d as [| | | |[]| ]; done || intros; solve_rcred. }
  intros Δ''' n''' ? mf S' ??? (->&?&?) p _.
  assert (∃ d', S' = State [] (Stmt d' (catch s)) (m ∪ mf)
    ∧ assert_holds ((dassert_pack P Q R J T C) d')
        Γ' Δ''' δ' ρ n''' (cmap_erase m)
    ∧ direction_out d' s ∧ (Γ',Δ''') ⊢ d' : (false,mσ)) as (d'&->&?&?&?).
  { inv_rcstep p; typed_inversion_all; eexists; split_and ?;
      eauto using assert_weaken, indexes_valid_weaken, val_typed_weaken. }
  econstructor; eauto. apply ax_done; constructor; auto.
Qed.
Lemma ax_goto Γ δ R J T C Q l :
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ J l }} goto l {{ Q }}.
Proof.
  intros Γ' Δ δ' n k [] m cmτ ??????????; simplify_equality'; try set_solver.
  apply ax_further; [intros; solve_rcred|].
  intros Δ' n' m' mf S' ??? (?&?&?) p _; subst; inv_rcstep p.
  eapply mk_ax_next; try by eauto.
  apply ax_done; constructor; eauto using assert_weaken. set_solver.
Qed.
Lemma ax_label Γ δ R J T C l :
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ J l }} label l {{ J l }}.
Proof.
  intros Γ' Δ δ' n k [] m cmτ ??????????;
    simplify_equality'; typed_inversion_all; try set_solver.
  * apply ax_further; [intros; solve_rcred|].
    intros Δ' n' m' mf S' ??? (?&?&?) p _; subst; inv_rcstep p.
    eapply mk_ax_next; try by eauto.
    apply ax_done; constructor; eauto using assert_weaken.
  * apply ax_further; [intros; solve_rcred|].
    intros Δ' n' m' mf S' ??? (?&?&?) p _; subst; inv_rcstep p.
    eapply mk_ax_next; try by eauto.
    apply ax_done; constructor; eauto using assert_weaken.
Qed.
Lemma ax_case Γ δ R J T C mx :
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ C mx }} scase mx {{ C mx }}.
Proof.
  intros Γ' Δ δ' n k [] m cmτ ??????????;
    simplify_equality'; typed_inversion_all; try by decompose_elem_of.
  * apply ax_further; [intros; solve_rcred|].
    intros Δ' n' m' mf S' ??? (?&?&?) p _; subst; inv_rcstep p.
    eapply mk_ax_next; try by eauto.
    apply ax_done; constructor; eauto using assert_weaken.
  * apply ax_further; [intros; solve_rcred|].
    intros Δ' n' m' mf S' ??? (?&?&?) p _; subst; inv_rcstep p.
    eapply mk_ax_next; try by eauto.
    apply ax_done; constructor; eauto using assert_weaken.
Qed.
Lemma ax_localP Γ δ Pd s τ :
  Γ\ δ\ (@fmap _ (@directed_fmap K) _ _ (λ P, var O ↦{false,perm_full} - : τ ★ P↑)%A Pd) ⊨ₚ s →
  Γ\ δ\ Pd ⊨ₚ local{τ} s.
Proof.
  intros Hax Γ' Δ δ' n ρ d m cmτ ????? Hm ????; typed_inversion_all.
  change (stmt_typed' Γ' Δ (τ :: ρ.*2))
    with (typed (Γ',Δ,(τ :: ρ.*2)) : stmt K → _ → Prop) in *.
  apply ax_further; [intros; solve_rcred|].
  intros Δ' n' ? mf ???? (->&?&?) p Hdom.
  assert (∃ o, S' = State [CLocal o τ] (Stmt d s)
      (mem_alloc Γ' o false perm_full (val_new Γ' τ) (m ∪ mf)) ∧
    o ∉ dom indexset (m ∪ mf)) as (o&->&Ho) by (inv_rcstep p; eauto);
    simplify_equality'; clear p.
  assert (Δ' !! o = None); [|clear Hdom].
  { rewrite mem_dom_alloc in Hdom. apply not_elem_of_dom; set_solver. }
  rewrite cmap_dom_union, not_elem_of_union in Ho; destruct Ho.
  assert (mem_alloc Γ' o false perm_full (val_new Γ' τ) m ## mf)
    by eauto using (mem_alloc_disjoint _ Δ').
  apply mk_ax_next with (<[o:=(τ,false)]>Δ')
    (mem_alloc Γ' o false perm_full (val_new Γ' τ) m);
    eauto using mem_alloc_forward, mem_alloc_forward_least.
  { rewrite mem_alloc_union by done; constructor; auto. }
  assert (✓{Γ',<[o:=(τ, false)]> Δ'} δ').
  { eauto using funenv_valid_weaken, mem_alloc_forward. }
  eapply ax_compose_cons; eauto.
  { eapply Hax; eauto.
    { by erewrite (mem_locks_alloc _ Δ') by auto. }
    { eauto using stmt_typed_weaken, mem_alloc_forward. }
    { constructor; eauto using indexes_valid_weaken, mem_alloc_forward.
      by apply mem_alloc_index_typed. }
    destruct (mem_alloc_singleton_alt Γ' Δ' m o false perm_full
      (val_new Γ' τ) τ) as (m'&->&?&?); auto using val_new_frozen;
      simplify_mem_disjoint_hyps.
    erewrite cmap_erase_union, directed_fmap_spec, mem_erase_singleton by eauto.
    exists m', (cmap_erase m); split_and ?; csimpl;
      eauto using assert_weaken, mem_alloc_forward.
    { by rewrite <-cmap_erase_disjoint_le. }
    eexists _, (addr_top o τ), (val_new Γ' τ); split_and ?; simpl; eauto. }
  clear dependent d m mf; intros Δ'' n'' φ m' [d m ?? Hlocks HPd] ???; clear m'.
  assert (Δ ⇒ₘ Δ'') by eauto using mem_alloc_forward.
  assert (Δ'' ⊢ o : τ)
    by eauto using memenv_forward_typed, mem_alloc_index_typed.
  apply ax_further; [intros; solve_rcred|].
  intros Δ''' n''' ? mf S' ??? (->&?&?) p _.
  assert (S' = State [] (Stmt d (local{τ} s)) (mem_free o (m ∪ mf)))
    by (by inv_rcstep p); subst; clear p.
  rewrite directed_fmap_spec in HPd; destruct HPd as (m1&m2&?&?&Hm1&?).
  destruct (cmap_erase_union_inv_l m m1 m2)
    as (m2'&->&Hm12'&_&->); auto; simplify_mem_disjoint_hyps; clear Hm12'.
  rewrite mem_locks_union in Hlocks by auto; decompose_empty.
  destruct Hm1 as (?&a&v&_&?&_&?&?); simplify_option_eq.
  assert (mem_freeable_perm o false m1)
    by eauto using mem_freeable_perm_singleton.
  apply mk_ax_next with
    (alter (prod_map id (λ _, true)) o Δ''') (mem_free o (m1 ∪ m2'));
    eauto using mem_free_forward, mem_free_forward_least.
  { erewrite !mem_free_union
      by eauto using mem_freeable_perm_subseteq, @sep_union_subseteq_l'.
    constructor; auto.
    rewrite <-sep_disjoint_le_union, <-mem_free_disjoint_le by eauto; auto. }
  { intros ?. eapply mem_free_forward_least; eauto using @sep_union_subseteq_l',
      mem_freeable_perm_subseteq, @sep_union_subseteq_l_transitive. }
  apply ax_done; constructor; eauto.
  { eauto using direction_typed_weaken, mem_free_forward. }
  { erewrite mem_locks_free, mem_locks_union
      by eauto using mem_freeable_perm_subseteq, @sep_union_subseteq_l'.
    by erewrite (mem_locks_singleton_empty _ _ _ _ _ perm_full),
      (left_id_L ∅ (∪)) by eauto. }
  erewrite mem_free_union, cmap_erase_union, mem_free_singleton by eauto.
  rewrite sep_left_id by auto.
  eauto using assert_weaken, mem_free_forward, indexes_valid_weaken.
Qed.
Lemma ax_local Γ δ R J T C P Q s τ :
  Γ\ δ\ (λ v, var O ↦{false,perm_full} - : τ ★ R v↑)\
      (λ l, var O ↦{false,perm_full} - : τ ★ J l↑)\
      (λ i, var O ↦{false,perm_full} - : τ ★ T i↑)\
      (λ mx, var O ↦{false,perm_full} - : τ ★ C mx↑) ⊨ₛ
    {{ var O ↦{false,perm_full} - : τ ★ P↑ }} s
    {{ var O ↦{false,perm_full} - : τ ★ Q↑ }} →
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ P }} local{τ} s {{ Q }}.
Proof. intros. by apply ax_localP. Qed.
Lemma ax_comp Γ δ R J T C P P' Q s1 s2 :
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ P }} s1 {{ P' }} →
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ P' }} s2 {{ Q }} →
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ P }} s1 ;; s2 {{ Q }}.
Proof.
  intros Hax1 Hax2 Γ' Δ δ' n ρ d m cmτ ???; revert Δ d m.
  induction n as [[|n] IH] using lt_wf_ind; [constructor|].
  intros Δ d m ???? Hs ??.
  assert (∃ mτ c1 mτ1 c2 mτ2, cmτ = (c2,mτ) ∧ (Γ',Δ,ρ.*2) ⊢ s1 : (c1,mτ1) ∧
    (Γ',Δ,ρ.*2) ⊢ s2 : (c2,mτ2) ∧ rettype_union mτ1 mτ2 mτ)
    as (mτ&c1&mτ1&c2&mτ2&->&?&?&?) by (typed_inversion_all; eauto 10); clear Hs.
  assert (∀ Δ' n' m d,
    Δ ⇒ₘ Δ' → n' ≤ n → ✓{Γ',Δ'} m → mem_locks m = ∅ →
    direction_in d s2 →
    assert_holds ((dassert_pack P' Q R J T C) d) Γ' Δ' δ' ρ n' (cmap_erase m) →
    ax_graph ax_disjoint_cond
      (ax_stmt_post (dassert_pack P Q R J T C) (s1 ;; s2) (c2,mτ))
      Γ' δ' Δ' ρ n' [CStmt (s1 ;; □)] (Stmt d s2) m).
  { clear dependent m d. intros Δ' n' m d ??????.
    eapply ax_compose_cons; eauto using funenv_valid_weaken.
    { eapply Hax2; eauto using indexes_valid_weaken,
        stmt_typed_weaken, assert_weaken, funenv_valid_weaken. }
    clear dependent d m; intros Δ'' n'' φ m' [d m ??] ???; clear m'.
    apply ax_further; [intros; solve_rcred|].
    intros Δ''' n''' ? mf S' ??? (->&?&?) p _.
    assert (S' = State [] (Stmt d (s1 ;; s2)) (m ∪ mf) ∧
      (Γ', Δ''') ⊢ d : (c2,mτ) ∧
      (direction_out d (s1 ;; s2) ∨
       ∃ l, d = ↷ l ∧ l ∈ labels s1 ∧ l ∉ labels s2)) as (->&?&[?|(l'&->&?)]).
    { inv_rcstep p; typed_inversion_all;
        erewrite ?(rettype_union_inv_r _ _ _), ?not_elem_of_union by eauto;
        try match goal with
        | H : ?l ∉ labels s2 |- _ => destruct (decide (l ∈ labels s1))
        end; naive_solver eauto using val_typed_weaken. }
    { econstructor; eauto. apply ax_done; constructor; auto.
      by destruct d; eauto using assert_weaken, indexes_valid_weaken. }
    econstructor; eauto.
    eapply IH;
      eauto using assert_weaken, indexes_valid_weaken, funenv_valid_weaken.
    * set_solver.
    * typed_constructor; eauto using stmt_typed_weaken. }
  apply ax_further; [intros; solve_rcred|].
  intros Δ' n' ? mf ???? (->&?&?) p _.
  assert ((∃ l, d = ↷ l ∧ l ∈ labels s2 ∧
      S' = State [CStmt (s1 ;; □)] (Stmt d s2) (m ∪ mf)) ∨
    (∃ mx, d = ↓ mx ∧ mx ∈ cases s2 ∧
      S' = State [CStmt (s1 ;; □)] (Stmt d s2) (m ∪ mf)) ∨
    S' = State [CStmt (□ ;; s2)] (Stmt d s1) (m ∪ mf) ∧ direction_in d s1)
    as [(l&->&?&->)|[(mx&->&?&->)|[-> ?]]] by (inv_rcstep p; eauto 10); clear p.
  { apply mk_ax_next with Δ' m; eauto using assert_weaken. }
  { apply mk_ax_next with Δ' m; eauto using assert_weaken. }
  apply mk_ax_next with Δ' m; auto.
  eapply ax_compose_cons; eauto using funenv_valid_weaken.
  { eapply Hax1; eauto using indexes_valid_weaken,
      stmt_typed_weaken, funenv_valid_weaken.
    by destruct d; eauto using assert_weaken. }
  clear dependent d m mf; intros Δ'' n'' φ m' [d m ??] ???; clear m'.
  apply ax_further; [intros; solve_rcred|].
  intros Δ''' n''' ? mf S' ??? (->&?&?) p _.
  assert ((S' = State [] (Stmt d (s1 ;; s2)) (m ∪ mf) ∧
    (Γ', Δ''') ⊢ d : (c2,mτ) ∧
    (d ≠ ↗ ∧ direction_out d (s1 ;; s2) ∨
     ∃ l, d = ↷ l ∧ l ∉ labels s1 ∧ l ∈ labels s2)) ∨
    d = ↗ ∧ S' = State [CStmt (s1 ;; □)] (Stmt ↘ s2) (m ∪ mf))
    as [(->&?&[[??]|(l'&->&?)])|[-> ->]].
  { inv_rcstep p; typed_inversion_all;
      erewrite ?(rettype_union_inv_l _ _ _), ?not_elem_of_union by eauto;
      try match goal with
      | H : ?l ∉ labels s1 |- _ => destruct (decide (l ∈ labels s2))
      end; naive_solver eauto using val_typed_weaken. }
  { econstructor; eauto. apply ax_done; constructor; auto.
    by destruct d; eauto using assert_weaken, indexes_valid_weaken. }
  { econstructor; eauto.
    eapply IH; eauto using assert_weaken,
      indexes_valid_weaken, funenv_valid_weaken.
    * set_solver.
    * typed_constructor; eauto using stmt_typed_weaken. }
  econstructor; eauto 10 using assert_weaken, indexes_valid_weaken.
Qed.
Lemma ax_loop Γ δ R J T C P s :
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ P }} s {{ P }} →
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ P }} loop s {{ False }}.
Proof.
  intros Hax Γ' Δ δ' n ρ d m cmτ ???; revert Δ d m.
  induction n as [[|n] IH] using lt_wf_ind; [constructor|].
  intros Δ d m ???????; typed_inversion_all.
  apply ax_further; [intros; solve_rcred|].
  intros Δ' n' ? mf S' ??? (->&?&?) p _.
  assert (S' = State [CStmt (loop □)] (Stmt d s) (m ∪ mf))
    by inv_rcstep p; subst; clear p.
  apply mk_ax_next with Δ' m; auto.
  eapply ax_compose_cons; eauto using funenv_valid_weaken.
  { eapply Hax; eauto using indexes_valid_weaken,
      stmt_typed_weaken, funenv_valid_weaken.
    destruct d; naive_solver eauto using assert_weaken, indexes_valid_weaken. }
  clear dependent d m mf; intros Δ'' n'' φ' m' [d m ??] ???; clear m'.
  apply ax_further; [intros; solve_rcred|].
  intros Δ''' n''' ? mf S' ??? (->&?&?) p _.
  assert (d ≠ ↗ ∧ S' = State [] (Stmt d (loop s)) (m ∪ mf) ∧
      (Γ', Δ''') ⊢ d : (true, mσ) ∨
    d = ↗ ∧ S' = State [] (Stmt ↘ (loop s)) (m ∪ mf))
    as [(?&->&?)|[-> ->]].
  { inv_rcstep; typed_inversion_all; eauto 8 using val_typed_weaken. }
  { econstructor; eauto. apply ax_done; constructor; auto.
    by destruct d; eauto using assert_weaken, indexes_valid_weaken. }
  econstructor; eauto.
  eapply IH; eauto using assert_weaken,
    indexes_valid_weaken, funenv_valid_weaken, stmt_typed_weaken.
Qed.
Lemma ax_if Γ δ R J T C P P' P1 P2 Q e s1 s2 :
  (∀ vb, P' (inr (VBase vb)) ⊆{Γ,δ} (.{NotOp} #VBase vb ⇓ -)%A) →
  (∀ vb, ¬base_val_is_0 vb → P' (inr (VBase vb)) ⊆{Γ,δ} (P1 ◊)%A) →
  (∀ vb, base_val_is_0 vb → P' (inr (VBase vb)) ⊆{Γ,δ} (P2 ◊)%A) →
  Γ\ δ\ emp ⊨ₑ {{ P }} e {{ P' }} →
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ P1 }} s1 {{ Q }} →
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ P2 }} s2 {{ Q }} →
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ P }} if{e} s1 else s2 {{ Q }}.
Proof.
  intros HP' HP1 HP2 Hax Hax1 Hax2 Γ' Δ δ' n ρ d m cmτ ??? Hδ Hm Hlock Hd Hs.
  assert (∃ τb mτ c1 mτ1 c2 mτ2, cmτ = (c1&&c2, mτ) ∧
    (Γ',Δ,ρ.*2) ⊢ e : inr (baseT τb) ∧ locks e = ∅ ∧
    (Γ',Δ,ρ.*2) ⊢ s1 : (c1,mτ1) ∧ (Γ',Δ,ρ.*2) ⊢ s2 : (c2,mτ2) ∧
    rettype_union mτ1 mτ2 mτ) as (τb&mτ&c1&mτ1&c2&mτ2&->&He&?&Hs1&Hs2&?)
    by (typed_inversion_all; eauto 20); clear Hs.
  revert Δ d m Hδ Hm Hlock Hd He Hs1 Hs2.
  induction n as [[|n] IH] using lt_wf_ind; [constructor|].
  intros Δ d m; intros; apply ax_further; [intros; solve_rcred|].
  intros Δ' n' ? mf S' ??? (->&?&?) p _.
  assert ((d ≠ ↘ ∧ direction_in d s2 ∧
      S' = State [CStmt (if{e} s1 else □)] (Stmt d s2) (m ∪ mf)) ∨
    (d ≠ ↘ ∧ direction_in d s1 ∧
      S' = State [CStmt (if{e} □ else s2)] (Stmt d s1) (m ∪ mf)) ∨
    d = ↘ ∧ S' = State [CExpr e (if{□} s1 else s2)] (Expr e) (m ∪ mf))
    as [(?&?&->)|[(?&?&->)|[-> ->]]] by (inv_rcstep p; eauto 10); clear p.
  { apply mk_ax_next with Δ' m; eauto.
    eapply ax_compose_cons; eauto using funenv_valid_weaken.
    { destruct d; done || eapply Hax2; eauto using indexes_valid_weaken,
        stmt_typed_weaken, assert_weaken, funenv_valid_weaken. }
    clear dependent d m mf; intros Δ'' n'' φ m' [d m ??] ???; clear m'.
    apply ax_further; [intros; solve_rcred|].
    intros Δ''' n''' ? mf S' ??? (->&?&?) p _.
    assert (S' = State [] (Stmt d (if{e} s1 else s2)) (m ∪ mf) ∧
      (Γ', Δ''') ⊢ d : (c1 && c2, mτ) ∧
      (direction_out d (if{e} s1 else s2) ∨
       ∃ l, d = ↷ l ∧ l ∈ labels s1 ∧ l ∉ labels s2)) as (->&?&[?|(l&->&?&?)]).
    { inv_rcstep p; typed_inversion_all; erewrite ?(rettype_union_inv_r _ _ _),
        ?andb_false_r, ?not_elem_of_union by eauto;
        try match goal with
        | H : ?l ∉ labels s2 |- _ => destruct (decide (l ∈ labels s1))
        end; naive_solver eauto using val_typed_weaken. }
    { econstructor; eauto. apply ax_done; constructor; auto.
      by destruct d; eauto using assert_weaken, indexes_valid_weaken. }
    econstructor; eauto.
    eapply IH; eauto using assert_weaken, funenv_valid_weaken,
      expr_typed_weaken, stmt_typed_weaken, indexes_valid_weaken.
    set_solver. }
  { apply mk_ax_next with Δ' m; eauto.
    eapply ax_compose_cons; eauto using funenv_valid_weaken.
    { destruct d; done || eapply Hax1; eauto using indexes_valid_weaken,
        stmt_typed_weaken, assert_weaken, funenv_valid_weaken. }
    clear dependent d m mf; intros Δ'' n'' φ m' [d m ??] ???; clear m'.
    apply ax_further; [intros; solve_rcred|].
    intros Δ''' n''' ? mf S' ??? (->&?&?) p _.
    assert (S' = State [] (Stmt d (if{e} s1 else s2)) (m ∪ mf) ∧
      (Γ', Δ''') ⊢ d : (c1 && c2, mτ) ∧
      (direction_out d (if{e} s1 else s2) ∨
       ∃ l, d = ↷ l ∧ l ∉ labels s1 ∧ l ∈ labels s2)) as (->&?&[?|(l&->&?&?)]).
    { inv_rcstep p; typed_inversion_all; erewrite ?(rettype_union_inv_l _ _ _),
        ?andb_false_r, ?not_elem_of_union by eauto;
        try match goal with
        | H : ?l ∉ labels s1 |- _ => destruct (decide (l ∈ labels s2))
        end; naive_solver eauto using val_typed_weaken. }
    { econstructor; eauto. apply ax_done; constructor; auto.
      by destruct d; eauto using assert_weaken, indexes_valid_weaken. }
    econstructor; eauto.
    eapply IH; eauto using assert_weaken, funenv_valid_weaken,
      expr_typed_weaken, stmt_typed_weaken, indexes_valid_weaken.
    set_solver. }
  apply mk_ax_next with Δ' m; eauto; [set_solver|].
  eapply (ax_compose_cons (ax_expr_cond ρ emp));
    eauto using funenv_valid_weaken.
  { apply Hax; eauto using expr_typed_weaken,
      indexes_valid_weaken, assert_weaken, funenv_valid_weaken. }
  clear dependent m mf.
  intros Δ'' n'' φ m' [[|[vb| | | |]] Ω m] ???; clear m'; typed_inversion_all.
  assert (base_val_branchable m vb).
  { rewrite <-base_val_branchable_erase.
    by destruct (HP' vb Γ' Δ'' δ' ρ n'' (cmap_erase m)) as (?&?&?&?);
      eauto using indexes_valid_weaken, funenv_valid_weaken;
      simplify_option_eq. }
  apply ax_further.
  { intros ?? m'' ? _ _ _ _. destruct (decide (base_val_branchable m'' vb)),
      (decide (base_val_is_0 vb)); solve_rcred. }
  intros Δ''' n''' ? mf S' ??? (?&?&?) p _; subst; inv_rcstep p; clear S'.
  * rewrite mem_unlock_union, <-mem_unlock_all_spec; [|auto|set_solver].
    eapply mk_ax_next with Δ''' (mem_unlock_all _); eauto.
    { split. by rewrite <-?mem_unlock_all_disjoint_le; auto.
             by rewrite <-?mem_unlock_all_disjoint_le; auto. }
    { apply cmap_union_valid_2; auto using mem_unlock_all_valid.
      by rewrite <-sep_disjoint_list_double, <-mem_unlock_all_disjoint_le. }
    eapply ax_compose_cons;
      eauto using mem_unlock_all_valid, funenv_valid_weaken.
    { eapply Hax1; eauto using indexes_valid_weaken, stmt_typed_weaken,
        mem_unlock_all_valid, mem_locks_unlock_all, funenv_valid_weaken.
      rewrite mem_erase_unlock_all; simpl.
      eapply HP1;
        eauto using assert_weaken, indexes_valid_weaken, funenv_valid_weaken. }
    clear dependent φ m mf; intros Δ'''' n'''' φ m' [d m ??] ???; clear m'.
    apply ax_further; [intros; solve_rcred|].
    intros Δ''''' n''''' ? mf S' ??? (->&?&?) p _.
    assert (✓{Δ''''}* ρ) by eauto 8 using indexes_valid_weaken.
    inv_rcstep p; typed_inversion_all;
      erewrite ?(rettype_union_inv_l _ _ _) by eauto;
      econstructor; eauto; try solve [apply ax_done; constructor;
        eauto using assert_weaken, val_typed_weaken].
    destruct (decide (l ∈ labels s2)).
    { apply IH; eauto 10 using expr_typed_weaken,funenv_valid_weaken,
        stmt_typed_weaken, assert_weaken, indexes_valid_weaken.
      set_solver. }
    apply ax_done; constructor; eauto using assert_weaken; set_solver.
  * rewrite mem_unlock_union, <-mem_unlock_all_spec; [|auto|set_solver].
    eapply mk_ax_next with Δ''' (mem_unlock_all _); eauto.
    { split. by rewrite <-?mem_unlock_all_disjoint_le by auto.
             by rewrite <-?mem_unlock_all_disjoint_le by auto. }
    { apply cmap_union_valid_2; auto using mem_unlock_all_valid.
      by rewrite <-sep_disjoint_list_double, <-mem_unlock_all_disjoint_le. }
    eapply ax_compose_cons;
      eauto using mem_unlock_all_valid, funenv_valid_weaken.
    { eapply Hax2; eauto using indexes_valid_weaken, stmt_typed_weaken,
        mem_unlock_all_valid, mem_locks_unlock_all, funenv_valid_weaken.
      rewrite mem_erase_unlock_all; simpl.
      eapply HP2;
        eauto using assert_weaken, indexes_valid_weaken, funenv_valid_weaken. }
    clear dependent φ m mf; intros Δ'''' n'''' φ m' [d m ??] ???; clear m'.
    apply ax_further; [intros; solve_rcred|].
    intros Δ''''' n'''''' ? mf S' ??? (->&?&?) p _.
    assert (✓{Δ''''}* ρ) by eauto 8 using indexes_valid_weaken.
    inv_rcstep p; typed_inversion_all;
      erewrite ?(rettype_union_inv_r _ _ _), ?andb_false_r by eauto;
      econstructor; eauto; try solve [apply ax_done; constructor;
        eauto using assert_weaken, val_typed_weaken].
    destruct (decide (l ∈ labels s1)).
    { apply IH; eauto 10 using expr_typed_weaken, funenv_valid_weaken,
        stmt_typed_weaken, assert_weaken, indexes_valid_weaken.
      set_solver. }
    apply ax_done; constructor; eauto using assert_weaken; set_solver.
  * exfalso; assert (m ⊆ m ∪ mf) by eauto using @sep_union_subseteq_l.
    eauto using base_val_branchable_weaken, cmap_subseteq_index_alive.
Qed.
Lemma ax_switch Γ δ R J T C C' P P' P'' Q e s :
  (∀ vb, P' (inr (VBase vb)) ⊆{Γ,δ} (.{NotOp} #VBase vb ⇓ -)%A) →
  (∀ z τi, Some z ∈ cases s → P' (inr (intV{τi} z)) ⊆{Γ,δ} (C (Some z) ◊)%A) →
  (∀ z τi, Some z ∉ cases s → None ∈ cases s →
    P' (inr (intV{τi} z)) ⊆{Γ,δ} (C None ◊)%A) →
  (∀ z τi, Some z ∉ cases s → None ∉ cases s →
    P' (inr (intV{τi} z)) ⊆{Γ,δ} (Q ◊)%A) →
  Γ\ δ\ emp ⊨ₑ {{ P }} e {{ P' }} →
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ P'' }} s {{ Q }} →
  Γ\ δ\ R\ J\ T\ C' ⊨ₛ {{ P }} switch{e} s {{ Q }}.
Proof.
  intros HP' HSome HNone HQ Hax Hax' Γ' Δ δ' n ρ d m cmτ ??? Hδ Hm Hlock Hd Hs.
  assert (∃ τi mτ c, cmτ = (false,mτ) ∧ (Γ',Δ,ρ.*2) ⊢ e : inr (intT τi) ∧
    locks e = ∅ ∧ (Γ',Δ,ρ.*2) ⊢ s : (c,mτ)) as (τi&mτ&c&->&He&?&Hs')
    by (typed_inversion_all; eauto 20); clear Hs.
  intros ? HP; apply ax_further; [intros; solve_rcred|].
  intros Δ' n' ? mf S' ??? (->&?&?) p _.
  assert ((∃ l, d = ↷ l ∧ l ∈ labels s ∧
      S' = State [CStmt (switch{e} □)] (Stmt (↷ l) s) (m ∪ mf)) ∨
    d = ↘ ∧ S' = State [CExpr e (switch{□} s)] (Expr e) (m ∪ mf))
    as [(l&->&?&->)|[-> ->]] by (inv_rcstep p; eauto 10); clear p.
  { apply mk_ax_next with Δ' m; eauto.
    eapply ax_compose_cons; eauto using funenv_valid_weaken.
    { eapply Hax'; eauto using indexes_valid_weaken,
        stmt_typed_weaken, assert_weaken, funenv_valid_weaken. }
    clear dependent l m mf; intros Δ'' n'' φ m' [d m ??] ???; clear m'.
    apply ax_further; [intros; solve_rcred|].
    intros Δ''' n''' ? mf S' ??? (->&?&?) p _.
    assert (S' = State [] (Stmt d (switch{e} s)) (m ∪ mf) ∧
      (Γ', Δ'') ⊢ d : (false, mτ) ∧ (direction_out d (switch{e} s)))
      as (->&?&?) by (inv_rcstep p; typed_inversion_all; eauto).
    apply mk_ax_next with Δ''' m; eauto.
    apply ax_done; constructor; eauto using direction_typed_weaken.
    by destruct d; eauto using assert_weaken, indexes_valid_weaken. }
  apply mk_ax_next with Δ' m; eauto; [set_solver|].
  eapply (ax_compose_cons (ax_expr_cond ρ emp));
    eauto using funenv_valid_weaken.
  { apply Hax; eauto using expr_typed_weaken,
      indexes_valid_weaken, assert_weaken, funenv_valid_weaken. }
  clear dependent m mf.
  intros Δ'' n'' φ m' [[|[vb| | | |]] Ω m] ???; clear m'; typed_inversion_all.
  assert (base_val_branchable m vb).
  { rewrite <-base_val_branchable_erase.
    by destruct (HP' vb Γ' Δ'' δ' ρ n'' (cmap_erase m)) as (?&?&?&?);
      eauto using indexes_valid_weaken, funenv_valid_weaken;
      simplify_option_eq. }
  destruct vb as [| |? z| |]; typed_inversion_all; try done.
  apply ax_further.
  { intros ?? m'' ? _ _ _ _. destruct (decide (Some z ∈ cases s)),
      (decide (None ∈ cases s)); solve_rcred. }
  intros Δ''' n''' ? mf S' ??? (->&?&?) p _.
  assert (∃ k φ, S' = State k φ (mem_unlock (mem_locks m) (m ∪ mf)) ∧
    (k = [] ∧ φ = Stmt ↗ (switch{e} s) ∧ Some z ∉ cases s ∧ None ∉ cases s ∨
    ∃ mz, k = [CStmt (switch{e} □)] ∧ φ = Stmt (↓mz) s ∧ mz ∈ cases s ∧
      (mz = Some z ∨ mz = None ∧ Some z ∉ cases s)))
    as (k&φ'&->&Hφ) by (inv_rcstep p; eauto 20).
  rewrite mem_unlock_union, <-mem_unlock_all_spec; [|auto|set_solver].
  apply mk_ax_next with Δ''' (mem_unlock_all m); eauto.
  { split; by rewrite <-?mem_unlock_all_disjoint_le by auto. }
  { by destruct Hφ as [(->&->&_)|(mz&->&->&_)]. }
  { by destruct Hφ as [(->&->&_)|(mz&->&->&_)]. }
  { apply cmap_union_valid_2; auto using mem_unlock_all_valid.
    by rewrite <-sep_disjoint_list_double, <-mem_unlock_all_disjoint_le. }
  destruct Hφ as [(->&->&?&?)|(mz&->&->&?&Hmz)].
  { apply ax_done; constructor; simpl; eauto using mem_locks_unlock_all.
    rewrite mem_erase_unlock_all; simpl; eapply HQ;
      eauto using assert_weaken, indexes_valid_weaken, funenv_valid_weaken. }
  eapply ax_compose_cons;
    eauto using mem_unlock_all_valid, funenv_valid_weaken.
  { eapply Hax'; eauto using indexes_valid_weaken, stmt_typed_weaken,
      mem_unlock_all_valid, mem_locks_unlock_all, funenv_valid_weaken.
    rewrite mem_erase_unlock_all; simpl.
    destruct Hmz as [->|[-> ?]]; [eapply HSome|eapply HNone];
      eauto using assert_weaken, indexes_valid_weaken, funenv_valid_weaken. }
  clear dependent φ m mf; intros Δ'''' n'''' φ m' [d m ??] ???; clear m'.
  apply ax_further; [intros; solve_rcred|].
  intros Δ''''' n''''' ? mf S' ??? (->&?&?) p _.
  assert (✓{Δ''''}* ρ) by eauto 8 using indexes_valid_weaken.
  inv_rcstep p; typed_inversion_all; econstructor; eauto; solve
    [apply ax_done; constructor; eauto using assert_weaken, val_typed_weaken].
Qed.
End axiomatic_statements.
