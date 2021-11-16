(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export restricted_smallstep memory_separation type_system.

Record ax_frame_cond (K : iType) `{Env K} (A : iType) : Type := {
  frame :
    env K → memenv K → funenv K → ctx K → nat →
    focus K → mem K → mem K → A → Prop;
  unframe :
    env K → memenv K → funenv K → ctx K → nat →
    focus K → mem K → mem K → A → Prop;
  frame_valid Γ Δ δ k n φ m m' a :
    ✓ Γ → frame Γ Δ δ k n φ m m' a → ✓{Γ,Δ} m → ✓{Γ,Δ} m';
  unframe_valid Γ Δ δ k n φ m m' a :
    ✓ Γ → unframe Γ Δ δ k n φ m m' a → ✓{Γ,Δ} m' → ✓{Γ,Δ} m
}.
Arguments frame {_ _ _} _ _ _ _ _ _ _ _ _ _.
Arguments unframe {_ _ _} _ _ _ _ _ _ _ _ _ _.

Record ax_assert (K : iType) `{Env K} : Type := {
  ax_assert_holds :
    env K → memenv K → funenv K → stack K → nat → focus K → mem K → Prop;
  ax_assert_weaken Γ1 Γ2 Δ1 Δ2 δ1 δ2 ρ n n' φ m :
    ✓ Γ1 → ✓{Γ1,Δ1} δ1 → ✓{Γ1,Δ1} m → ✓{Δ1}* ρ →
    ax_assert_holds Γ1 Δ1 δ1 ρ n φ m →
    Γ1 ⊆ Γ2 → Δ1 ⇒ₘ Δ2 → δ1 ⊆ δ2 → n' ≤ n →
    ax_assert_holds Γ2 Δ2 δ2 ρ n' φ m;
  ax_assert_nf Γ Δ δ ρ n φ m m' :
    ax_assert_holds Γ Δ δ ρ n φ m → nf (rcstep Γ δ ρ) (State [] φ m')
}.
Arguments ax_assert_holds {_ _} _ _ _ _ _ _ _ _.
Arguments ax_assert_nf {_ _} _ _ _ _ _ _ _ _ _ _ _.

Section ax_graph.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types Δ : memenv K.
Implicit Types m : mem K.

Hint Extern 1 (_ ## _) => solve_sep_disjoint: core.
Hint Extern 1 (## _) => solve_sep_disjoint: core.
Hint Extern 1 (_ ≤ _) => lia: core.

Section basics.
  Context {A} (F: ax_frame_cond K A) (P: ax_assert K) (Γ: env K) (δ: funenv K).

  Definition focus_locks_valid (φ : focus K) (m : mem K) :=
    match φ with Expr e => locks e ⊆ mem_locks m | _ => True end.
  Inductive ax_graph (Δ : memenv K) (ρ : stack K) :
       nat → ctx K → focus K → mem K → Prop :=
    | ax_O k φ m : ax_graph Δ ρ 0 k φ m
    | ax_done n φ m :
       ax_assert_holds P Γ Δ δ ρ n φ m → ax_graph Δ ρ n [] φ m
    | ax_further n k φ m :
       (∀ Δ' n' m' a,
         ✓{Γ,Δ'} m → Δ ⇒ₘ Δ' → n' < n →
         frame F Γ Δ' δ k (S n') φ m m' a →
         red (rcstep Γ δ ρ) (State k φ m')) →
       (∀ Δ' n' m' a S',
         ✓{Γ,Δ'} m → Δ ⇒ₘ Δ' → n' < n →
         frame F Γ Δ' δ k (S n') φ m m' a →
         Γ\ δ\ ρ ⊢ₛ State k φ m' ⇒ S' →
         dom indexset (SMem S') ∖ dom indexset m' ∩ dom indexset Δ' = ∅ →
         ax_next Δ' ρ n' a S') →
       ax_graph Δ ρ n k φ m
  with ax_next (Δ : memenv K) (ρ : stack K) : nat → A → state K → Prop :=
    | mk_ax_next Δ' k n φ m m' a :
       unframe F Γ Δ' δ k (S n) φ m m' a →
       maybe Undef φ = None →
       focus_locks_valid φ m →
       ✓{Γ,Δ'} m' → Δ ⇒ₘ Δ' →
       (∀ Δ'', ✓{Γ,Δ''} m' → Δ ⇒ₘ Δ'' → Δ' ⇒ₘ Δ'') →
       ax_graph Δ' ρ n k φ m →
       ax_next Δ ρ n a (State k φ m').
  Lemma focus_locks_valid_union φ m1 m2 :
    ## [m1; m2] → focus_locks_valid φ m1 → focus_locks_valid φ (m1 ∪ m2).
  Proof.
    intros; destruct φ; simpl; auto.
    rewrite mem_locks_union by auto; set_solver.
  Qed.
  Lemma ax_further_alt Δ ρ n k φ m :
    (∀ Δ' n' m' a,
      ✓{Γ,Δ'} m → Δ ⇒ₘ Δ' → n' < n →
      frame F Γ Δ' δ k (S n') φ m m' a →
      red (rcstep Γ δ ρ) (State k φ m') ∧
      ∀ S',
        Γ\ δ\ ρ ⊢ₛ State k φ m' ⇒ S' →
        dom indexset (SMem S') ∖ dom indexset m' ∩ dom indexset Δ' = ∅ →
        ax_next Δ' ρ n' a S') →
    ax_graph Δ ρ n k φ m.
  Proof. intros; apply ax_further; naive_solver. Qed.
  Lemma ax_graph_weaken Δ Δ' ρ n n' k φ m :
    ✓ Γ → ✓{Γ,Δ} δ → ✓{Γ,Δ} m → ✓{Δ}* ρ →
    ax_graph Δ ρ n k φ m → Δ ⇒ₘ Δ' → n' ≤ n →
    ax_graph Δ' ρ n' k φ m.
  Proof.
    intros ???? Hax ??. destruct Hax as [k φ m|n2 φ m|n2 k φ m Hred Hstep].
    * replace n' with 0 by lia. constructor.
    * apply ax_done; eauto using ax_assert_weaken.
    * constructor; eauto with arith.
  Qed.
  Lemma ax_step Δ ρ n k φ m m' a S' :
    ✓{Γ,Δ} m → frame F Γ Δ δ k (S n) φ m m' a →
    Γ\ δ\ ρ ⊢ₛ State k φ m' ⇒ S' →
    dom indexset (SMem S') ∖ dom indexset m' ∩ dom indexset Δ = ∅ →
    ax_graph Δ ρ (S n) k φ m → ax_next Δ ρ n a S'.
  Proof.
    inversion 5; subst; eauto.
    destruct (ax_assert_nf P Γ Δ δ ρ (S n) φ m m'); eauto.
  Qed.
  Lemma ax_step_undef Δ ρ n k φ m m' a k' Su m'' :
    ✓{Γ,Δ} m → frame F Γ Δ δ k (S n) φ m m' a →
    Γ\ δ\ ρ ⊢ₛ State k φ m' ⇒ State k' (Undef Su) m'' →
    dom indexset m'' ∖ dom indexset m' ∩ dom indexset Δ = ∅ →
    ¬ax_graph Δ ρ (S n) k φ m.
  Proof.
    intros ?? p ? Hax.
    by feed inversion (ax_step Δ ρ n k φ m m' a (State k' (Undef Su) m'')).
  Qed.
  Lemma ax_red Δ ρ n k φ m m' a :
    ✓{Γ,Δ} m → frame F Γ Δ δ k (S n) φ m m' a →
    ¬ax_assert_holds P Γ Δ δ ρ (S n) φ m →
    ax_graph Δ ρ (S n) k φ m →
    red (rcstep Γ δ ρ) (State k φ m').
  Proof. by inversion 4; subst; eauto. Qed.
End basics.

(** The predicate [ax] can be composed. This property is used to prove the
structural Hoare rules. *)
Definition ax_compose_diagram {A B} (F : ax_frame_cond K A)
    (G : ax_frame_cond K B) (Γ : env K) (k2 : ctx K) := ∀ Δ δ k1 n φ m m' b,
  ✓{Γ,Δ} δ → ✓{Γ,Δ} m →
  frame G Γ Δ δ (k1 ++ k2) n φ m m' b → ∃ a,
  (**i 1.) *) frame F Γ Δ δ k1 n φ m m' a ∧
  (**i 2.) *) ∀ Δ' k1' φ' m2 m2',
    ✓{Γ,Δ'} m2' → Δ ⇒ₘ Δ' →
    unframe F Γ Δ' δ k1' n φ' m2 m2' a →
    unframe G Γ Δ' δ (k1' ++ k2) n φ' m2 m2' b.
Lemma ax_compose_diagram_diag {A} (F : ax_frame_cond K A) Γ :
  ax_compose_diagram F F Γ [].
Proof.
  intros Δ δ k1 n φ m m' a; rewrite (right_id_L [] (++)); exists a; split; auto.
  by intros; rewrite (right_id_L [] (++)).
Qed.
Lemma ax_compose {A B} (F : ax_frame_cond K A) (G : ax_frame_cond K B)
    (P Q : ax_assert K) Γ δ Δ n φ ρ k1 k2 m :
  ✓ Γ → ✓{Γ,Δ} δ →
  ax_compose_diagram F G Γ k2 →
  ✓{Γ,Δ} m →
  ax_graph F P Γ δ Δ (rlocals ρ k2) n k1 φ m →
  (∀ Δ' n' φ' m',
    ax_assert_holds P Γ Δ' δ (rlocals ρ k2) n' φ' m' →
    ✓{Γ,Δ'} m' → Δ ⇒ₘ Δ' → n' ≤ n →
    ax_graph G Q Γ δ Δ' ρ n' k2 φ' m') →
  ax_graph G Q Γ δ Δ ρ n (k1 ++ k2) φ m.
Proof.
  intros ?. revert Δ m k1 φ.
  induction n as [[|n] IH] using lt_wf_ind; [intros; apply ax_O|].
  intros Δ m k1 φ ? HF ? Hax Hnext.
  inversion Hax as [| |???? Hred Hstep]; subst; eauto.
  apply ax_further_alt; intros Δ' n' m'' b ????.
  destruct (HF Δ' δ k1 (S n') φ m m'' b) as (a&?&?);
    eauto using funenv_valid_weaken.
  split; [eauto using rcred_app|intros [k' φ' m'] p ?].
  destruct (cstep_app_suffix_of Γ δ ρ k1 k2 φ m'' (State k' φ' m'))
    as [k3 ?]; simplify_equality'; eauto.
  feed inversion (Hstep Δ' n' m'' a (State k3 φ' m'))
    as [Δ'' n'' k'' φ'' m2' m2 b']; subst; auto using rcstep_app_inv.
  econstructor; eauto 10 using unframe_valid, funenv_valid_weaken.
Qed.
Lemma ax_compose_cons {A B} (F : ax_frame_cond K A) (G : ax_frame_cond K B)
    (P Q : ax_assert K) Γ δ Δ n φ ρ Ek m :
  ✓ Γ → ✓{Γ,Δ} δ →
  ax_compose_diagram F G Γ [Ek] →
  ✓{Γ,Δ} m →
  ax_graph F P Γ δ Δ (rlocals ρ [Ek]) n [] φ m →
  (∀ Δ' n' φ' m',
    ax_assert_holds P Γ Δ' δ (rlocals ρ [Ek]) n' φ' m' →
    ✓{Γ,Δ'} m' → Δ ⇒ₘ Δ' → n' ≤ n →
    ax_graph G Q Γ δ Δ' ρ n' [Ek] φ' m') →
  ax_graph G Q Γ δ Δ ρ n [Ek] φ m.
Proof. intros ?; by apply ax_compose. Qed.

(** The predicates [ax] satisfies an abstract version of the frame, weaken, and
conjunction rule. These abstract versions are used to prove the concrete rules
for both the expression and statement judgment. *)
Definition ax_frame_diagram {A B} (F: ax_frame_cond K A) (G: ax_frame_cond K B)
    (Γ : env K) (mf : mem K) := ∀ Δ δ k n φ m m' b,
  ✓{Γ,Δ} δ → ## [m; mf] → ✓{Γ,Δ} m → ✓{Γ,Δ} mf →
  frame G Γ Δ δ k n φ (m ∪ mf) m' b → ∃ a,
  (**i 1.) *) frame F Γ Δ δ k n φ m m' a ∧
  (**i 2.) *) ∀ Δ' k' φ' m2 m2',
    unframe F Γ Δ' δ k' n φ' m2 m2' a →
    ✓{Γ,Δ'} m2' → Δ ⇒ₘ Δ' →
    unframe G Γ Δ' δ k' n φ' (m2 ∪ mf) m2' b ∧ ## [m2; mf].
Lemma ax_frame_diagram_empty {A} (F : ax_frame_cond K A) Γ :
  ✓ Γ → ax_frame_diagram F F Γ ∅.
Proof.
  intros ???????? a ???? Ha; exists a.
  rewrite sep_right_id in Ha by solve_sep_disjoint.
  split; auto; intros Δ' k' φ' m2 m2' ???.
  assert (sep_valid m2) by eauto using cmap_valid_sep_valid, unframe_valid.
  split; auto. by rewrite sep_right_id.
Qed.
Lemma ax_frame {A B}(F : ax_frame_cond K A) (G : ax_frame_cond K B)
    (P Q : ax_assert K) Γ δ Δ ρ n k φ m mf :
  ✓ Γ → ✓{Γ,Δ} δ →
  ax_frame_diagram F G Γ mf →
  ## [m; mf] → ✓{Γ,Δ} m → ✓{Γ,Δ} mf →
  ax_graph F P Γ δ Δ ρ n k φ m →
  (∀ Δ' n' φ' m',
    ## [m'; mf] → ✓{Γ,Δ'} m' → ✓{Γ,Δ'} mf → Δ ⇒ₘ Δ' → n' ≤ n →
    ax_assert_holds P Γ Δ' δ ρ n' φ' m' →
    ax_assert_holds Q Γ Δ' δ ρ n' φ' (m' ∪ mf)) →
  ax_graph G Q Γ δ Δ ρ n k φ (m ∪ mf).
Proof.
  intros ? Hδ HFG. revert Δ m k φ Hδ.
  induction n as [[|n] IH] using lt_wf_ind; [intros; apply ax_O|].
  intros Δ m k φ ???? Hax HPQ.
  inversion Hax as [| |???? Hred Hstep]; subst; eauto using ax_done.
  apply ax_further_alt; intros Δ' n' m' a.
  rewrite cmap_union_valid by auto; intros [??] ???.
  destruct (HFG Δ' δ k (S n') φ m m' a) as (b&?&Hunframe);
    eauto using funenv_valid_weaken.
  split; [eauto|intros ? p ?].
  feed inversion (Hstep Δ' n' m' b S')
    as [Δ'' k' ? φ' m2' m2 ? τf']; subst; auto.
  destruct (Hunframe Δ'' k' φ' m2' m2 τf'); trivial.
  apply mk_ax_next with Δ'' (m2' ∪ mf);
    eauto 11 using @cmap_valid_subseteq, @sep_union_subseteq_r,
    unframe_valid, focus_locks_valid_union, funenv_valid_weaken.
Qed.

Lemma ax_weaken {A} (F G : ax_frame_cond K A)
    (P Q : ax_assert K) Γ δ Δ ρ n n' k φ m :
  ✓ Γ → ✓{Γ,Δ} δ → ✓{Γ,Δ} m → ✓{Δ}* ρ →
  ax_graph F P Γ δ Δ ρ n k φ m →
  n' ≤ n →
  (∀ Δ' k' n' φ' m2 m2' a,
    ✓{Γ,Δ'} m2 →
    frame G Γ Δ' δ k' n' φ' m2 m2' a →
    Δ ⇒ₘ Δ' → n' ≤ n →
    frame F Γ Δ' δ k' n' φ' m2 m2' a) →
  (∀ Δ' k' n' φ' m2 m2' a,
    ✓{Γ,Δ'} m2' →
    unframe F Γ Δ' δ k' n' φ' m2 m2' a →
    Δ ⇒ₘ Δ' → n' ≤ n →
    unframe G Γ Δ' δ k' n' φ' m2 m2' a) →
  (∀ Δ' n' φ' m',
    ✓{Γ,Δ'} m' →
    ax_assert_holds P Γ Δ' δ ρ n' φ' m' →
    Δ ⇒ₘ Δ' → n' ≤ n →
    ax_assert_holds Q Γ Δ' δ ρ n' φ' m') →
  ax_graph G Q Γ δ Δ ρ n' k φ m.
Proof.
  intros ?; revert Δ k n' φ m.
  induction n as [[|n] IH] using lt_wf_ind; intros Δ k n' φ m ??? Hax ????.
  { replace n' with 0 by lia. by intros; apply ax_O. }
  inversion Hax as [| |???? Hred Hstep]; subst; eauto using ax_done.
  { apply ax_done. eapply ax_assert_weaken with _ _ _ (S n); eauto. }
  apply ax_further; eauto.
  { intros Δ' n'' m' a ????; eapply (Hred Δ' n'' m' a); eauto. }
  intros Δ' n'' m' a S' ???? p ?.
  feed inversion (Hstep Δ' n'' m' a S'); subst; eauto.
  econstructor; eauto.
  eapply (IH n''); eauto using unframe_valid,
    indexes_valid_weaken, funenv_valid_weaken.
Qed.

(** The standard framing condition that just adds an arbitrary frame to the
memory before each step and takes it off after. *)
Program Definition ax_disjoint_cond : ax_frame_cond K (mem K) := {|
  frame Γ Δ δ k n φ m m' mf := m' = m ∪ mf ∧ ✓{Γ,Δ} mf ∧ ## [m; mf];
  unframe Γ Δ δ k n φ m m' mf := m' = m ∪ mf ∧ ## [m; mf]
|}.
Next Obligation. 
  simpl; intros ??????????[HU [? ?]]?; rewrite HU. 
  by auto using cmap_union_valid_2. 
Qed.
Next Obligation. 
  simpl. intros ??????????[HU?]HF. rewrite HU in HF.
  by eauto using cmap_valid_subseteq, @sep_union_subseteq_l. 
Qed.
Lemma ax_disjoint_cond_frame_diagram Γ mf :
  ✓ Γ → ax_frame_diagram ax_disjoint_cond ax_disjoint_cond Γ mf.
Proof.
  intros ? Δ δ k n φ m m' mf' ???? (->&?&?). exists (mf ∪ mf'); split.
  { split; split_and ?; eauto using cmap_union_valid_2.
    by rewrite sep_associative by auto. }
  intros Δ' k' φ' m2 m2' [-> ?] ??; split; eauto.
  split; split_and ?; eauto. by rewrite sep_associative by auto.
Qed.
Lemma ax_disjoint_compose_diagram Γ Ek :
  ax_compose_diagram ax_disjoint_cond ax_disjoint_cond Γ [Ek].
Proof.
  intros Δ δ k n φ m ? mf ?? (->&?&?); exists mf; split_and ?; eauto. by split.
Qed.
End ax_graph.
