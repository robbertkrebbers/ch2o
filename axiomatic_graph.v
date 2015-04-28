(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export restricted_smallstep memory_separation type_system.
Local Hint Extern 1 (_ ⊥ _) => solve_sep_disjoint.
Local Hint Extern 1 (⊥ _) => solve_sep_disjoint.

Record ax_frame_cond (K : Set) `{Env K} (A : Type) : Type := {
  frame : env K → memenv K → ctx K → focus K → mem K → mem K → A → Prop;
  unframe : env K → memenv K → ctx K → focus K → mem K → mem K → A → Prop;
  frame_valid Γ Δ k φ m m' a :
    ✓ Γ → frame Γ Δ k φ m m' a → ✓{Γ,Δ} m → ✓{Γ,Δ} m';
  unframe_valid Γ Δ k φ m m' a :
    ✓ Γ → unframe Γ Δ k φ m m' a → ✓{Γ,Δ} m' → ✓{Γ,Δ} m
}.
Arguments frame {_ _ _} _ _ _ _ _ _ _ _.
Arguments unframe {_ _ _} _ _ _ _ _ _ _ _.

Record ax_assert (K : Set) `{Env K} : Type := {
  ax_assert_holds : env K → memenv K → stack K → focus K → mem K → Prop;
  ax_assert_weaken Γ1 Γ2 Δ1 Δ2 ρ φ m :
    ✓ Γ1 → ✓{Γ1,Δ1} m → ✓{Δ1}* ρ →
    ax_assert_holds Γ1 Δ1 ρ φ m →
    Γ1 ⊆ Γ2 → Δ1 ⇒ₘ Δ2 →
    ax_assert_holds Γ2 Δ2 ρ φ m;
  ax_assert_nf Γ δ Δ ρ φ m m' :
    ax_assert_holds Γ Δ ρ φ m → nf (rcstep Γ δ ρ) (State [] φ m')
}.
Arguments ax_assert_holds {_ _} _ _ _ _ _ _.
Arguments ax_assert_nf {_ _} _ _ _ _ _ _ _ _ _ _.

Section ax_graph.
Context `{EnvSpec K}.
Implicit Types Γ : env K.

Section basics.
  Context {A} (F: ax_frame_cond K A) (P: ax_assert K) (Γ: env K) (δ: funenv K).

  Definition focus_locks_valid (φ : focus K) (m : mem K) :=
    match φ with Expr e => locks e ⊆ mem_locks m | _ => True end.
  Inductive ax_graph (Δ : memenv K) (ρ : stack K) :
       nat → ctx K → focus K → mem K → Prop :=
    | ax_O k φ m : ax_graph Δ ρ 0 k φ m
    | ax_done n φ m :
       ax_assert_holds P Γ Δ ρ φ m → ax_graph Δ ρ n [] φ m
    | ax_further n k φ m :
       (∀ Δ' m' a,
         ✓{Γ,Δ'} m → Δ ⇒ₘ Δ' →
         frame F Γ Δ' k φ m m' a →
         red (rcstep Γ δ ρ) (State k φ m')) →
       (∀ Δ' m' a S',
         ✓{Γ,Δ'} m → Δ ⇒ₘ Δ' →
         frame F Γ Δ' k φ m m' a →
         Γ\ δ\ ρ ⊢ₛ State k φ m' ⇒ S' →
         dom indexset (SMem S') ∖ dom indexset m' ∩ dom indexset Δ' = ∅ →
         ax_next Δ' ρ n a S') →
       ax_graph Δ ρ (S n) k φ m
  with ax_next (Δ : memenv K) (ρ : stack K) : nat → A → state K → Prop :=
    | mk_ax_next n Δ' k φ m m' a :
       unframe F Γ Δ' k φ m m' a →
       maybe Undef φ = None →
       focus_locks_valid φ m →
       ✓{Γ,Δ'} m' → Δ ⇒ₘ Δ' →
       (∀ Δ'', ✓{Γ,Δ''} m' → Δ ⇒ₘ Δ'' → Δ' ⇒ₘ Δ'') →
       ax_graph Δ' ρ n k φ m →
       ax_next Δ ρ n a (State k φ m').
  Lemma focus_locks_valid_union φ m1 m2 :
    ⊥ [m1; m2] → focus_locks_valid φ m1 → focus_locks_valid φ (m1 ∪ m2).
  Proof.
    intros; destruct φ; simpl; auto.
    rewrite mem_locks_union by auto; solve_elem_of.
  Qed.
  Lemma ax_graph_weaken Δ Δ' ρ n k φ m :
    ✓ Γ → ✓{Γ,Δ} m → ✓{Δ}* ρ →
    ax_graph Δ ρ n k φ m → Δ ⇒ₘ Δ' → ax_graph Δ' ρ n k φ m.
  Proof. destruct 4; constructor; eauto using ax_assert_weaken. Qed.
  Lemma ax_further_pred Δ ρ n k φ m :
    (∀ Δ' m' a,
      ✓{Γ,Δ'} m → Δ ⇒ₘ Δ' →
      frame F Γ Δ' k φ m m' a →
      red (rcstep Γ δ ρ) (State k φ m')) →
    (∀ Δ' m' a S',
      ✓{Γ,Δ'} m → Δ ⇒ₘ Δ' →
      frame F Γ Δ' k φ m m' a →
      Γ\ δ\ ρ ⊢ₛ State k φ m' ⇒ S' →
      dom indexset (SMem S') ∖ dom indexset m' ∩ dom indexset Δ' = ∅ →
      ax_next Δ' ρ (pred n) a S') →
    ax_graph Δ ρ n k φ m.
  Proof. destruct n; econstructor (by eauto). Qed.
  Lemma ax_further_pred_alt Δ ρ n k φ m :
    (∀ Δ' m' a,
      ✓{Γ,Δ'} m → Δ ⇒ₘ Δ' →
      frame F Γ Δ' k φ m m' a →
      red (rcstep Γ δ ρ) (State k φ m') ∧
      ∀ S',
        Γ\ δ\ ρ ⊢ₛ State k φ m' ⇒ S' →
        dom indexset (SMem S') ∖ dom indexset m' ∩ dom indexset Δ' = ∅ →
        ax_next Δ' ρ (pred n) a S') →
    ax_graph Δ ρ n k φ m.
  Proof. intros; apply ax_further_pred; naive_solver. Qed.
  Lemma ax_S Δ ρ n k φ m (Hax : ax_graph Δ ρ (S n) k φ m) : ax_graph Δ ρ n k φ m
  with ax_next_S Δ ρ n a S' (Hax : ax_next Δ ρ (S n) a S') : ax_next Δ ρ n a S'.
  Proof.
    * inversion Hax; subst; [by apply ax_done|destruct n; [apply ax_O |]].
      apply ax_further; eauto.
    * inversion Hax; subst; econstructor; eauto.
  Qed.
  Lemma ax_plus_l Δ ρ n1 n2 k φ m :
    ax_graph Δ ρ (n1 + n2) k φ m → ax_graph Δ ρ n2 k φ m.
  Proof. induction n1; simpl; auto using ax_S. Qed.
  Lemma ax_next_plus_l Δ ρ n1 n2 a S' :
    ax_next Δ ρ (n1 + n2) a S' → ax_next Δ ρ n2 a S'.
  Proof. induction n1; simpl; auto using ax_next_S. Qed.
  Lemma ax_le Δ ρ n1 n2 k φ m :
    ax_graph Δ ρ n2 k φ m → n1 ≤ n2 → ax_graph Δ ρ n1 k φ m.
  Proof.
    intros Hax ?. rewrite (Minus.le_plus_minus n1 n2), plus_comm in Hax by done.
    eauto using ax_plus_l.
  Qed.
  Lemma ax_next_le Δ ρ n1 n2 a S :
    ax_next Δ ρ n2 a S → n1 ≤ n2 → ax_next Δ ρ n1 a S.
  Proof.
    intros Hax ?. rewrite (Minus.le_plus_minus n1 n2), plus_comm in Hax;
      eauto using ax_next_plus_l.
  Qed.
  Lemma ax_pred Δ ρ n k φ m :
    ax_graph Δ ρ n k φ m → ax_graph Δ ρ (pred n) k φ m.
  Proof. intros. eauto using ax_le with arith. Qed.
  Lemma ax_step Δ ρ n k φ m m' a S' :
    ✓{Γ,Δ} m → frame F Γ Δ k φ m m' a →
    Γ\ δ\ ρ ⊢ₛ State k φ m' ⇒ S' →
    dom indexset (SMem S') ∖ dom indexset m' ∩ dom indexset Δ = ∅ →
    ax_graph Δ ρ (S n) k φ m → ax_next Δ ρ n a S'.
  Proof.
    inversion 5; subst; eauto. destruct (ax_assert_nf P Γ δ Δ ρ φ m m'); eauto.
  Qed.
  Lemma ax_step_undef Δ ρ n k φ m m' a k' Su m'' :
    ✓{Γ,Δ} m → frame F Γ Δ k φ m m' a →
    Γ\ δ\ ρ ⊢ₛ State k φ m' ⇒ State k' (Undef Su) m'' →
    dom indexset m'' ∖ dom indexset m' ∩ dom indexset Δ = ∅ →
    ¬ax_graph Δ ρ (S n) k φ m.
  Proof.
    intros ?? p ? Hax.
    by feed inversion (ax_step Δ ρ n k φ m m' a (State k' (Undef Su) m'')).
  Qed.
  Lemma ax_red Δ ρ n k φ m m' a :
    ✓{Γ,Δ} m → frame F Γ Δ k φ m m' a →
    ¬ax_assert_holds P Γ Δ ρ φ m →
    ax_graph Δ ρ (S n) k φ m →
    red (rcstep Γ δ ρ) (State k φ m').
  Proof. by inversion 4; subst; eauto. Qed.
End basics.

(** The predicate [ax] can be composed. This property is used to prove the
structural Hoare rules. *)
Definition ax_compose_diagram {A B} (F : ax_frame_cond K A)
    (G : ax_frame_cond K B) (Γ : env K) (k2 : ctx K) := ∀ Δ k1 φ m m' b,
  ✓{Γ,Δ} m →
  frame G Γ Δ (k1 ++ k2) φ m m' b → ∃ a,
  (** 1.) *) frame F Γ Δ k1 φ m m' a ∧
  (** 2.) *) ∀ Δ' k1' φ' m2 m2',
    ✓{Γ,Δ'} m2' → Δ ⇒ₘ Δ' →
    unframe F Γ Δ' k1' φ' m2 m2' a →
    unframe G Γ Δ' (k1' ++ k2) φ' m2 m2' b.
Lemma ax_compose_diagram_diag {A} (F : ax_frame_cond K A) Γ :
  ax_compose_diagram F F Γ [].
Proof.
  intros Δ k1 φ m m' a; rewrite (right_id_L [] (++)); exists a; split; auto.
  by intros; rewrite (right_id_L [] (++)).
Qed.
Lemma ax_compose {A B} (F : ax_frame_cond K A) (G : ax_frame_cond K B)
    (P Q : ax_assert K) Γ δ Δ n φ ρ k1 k2 m :
  ✓ Γ →
  ax_compose_diagram F G Γ k2 →
  ✓{Γ,Δ} m →
  ax_graph F P Γ δ Δ (rlocals ρ k2) n k1 φ m →
  (∀ Δ' φ' m',
    ax_assert_holds P Γ Δ' (rlocals ρ k2) φ' m' →
    ✓{Γ,Δ'} m' → Δ ⇒ₘ Δ' →
    ax_graph G Q Γ δ Δ' ρ n k2 φ' m') →
  ax_graph G Q Γ δ Δ ρ n (k1 ++ k2) φ m.
Proof.
  intros ?. revert Δ m k1 φ; induction n as [|n IH]; [intros; apply ax_O|].
  intros Δ m k1 φ HF ? Hax Hnext.
  inversion Hax as [| |???? Hred Hstep]; subst; eauto.
  apply ax_further.
  { intros Δ' m'' a ???.
    destruct (HF Δ' k1 φ m m'' a) as (b&?&_); eauto using rcred_app. }
  intros Δ' m'' a [k' φ' m'] ??? p ?.
  destruct (HF Δ' k1 φ m m'' a) as (b&?&?); auto.
  destruct (cstep_app_suffix_of Γ δ ρ k1 k2 φ m'' (State k' φ' m'))
    as [k3 ?]; simplify_equality'; eauto.
  feed inversion (Hstep Δ' m'' b (State k3 φ' m'))
    as [n' Δ'' k'' φ'' m2' m2 a']; subst; auto using rcstep_app_inv.
  econstructor; eauto 10 using ax_S, unframe_valid.
Qed.
Lemma ax_compose_cons {A B} (F : ax_frame_cond K A) (G : ax_frame_cond K B)
    (P Q : ax_assert K) Γ δ Δ n φ ρ Ek m :
  ✓ Γ →
  ax_compose_diagram F G Γ [Ek] →
  ✓{Γ,Δ} m →
  ax_graph F P Γ δ Δ (rlocals ρ [Ek]) n [] φ m →
  (∀ Δ' φ' m',
    ax_assert_holds P Γ Δ' (rlocals ρ [Ek]) φ' m' →
    ✓{Γ,Δ'} m' → Δ ⇒ₘ Δ' →
    ax_graph G Q Γ δ Δ' ρ n [Ek] φ' m') →
  ax_graph G Q Γ δ Δ ρ n [Ek] φ m.
Proof. intros ?; by apply ax_compose. Qed.

(** The predicates [ax] satisfies an abstract version of the frame, weaken, and
conjunction rule. These abstract versions are used to prove the concrete rules
for both the expression and statement judgment. *)
Definition ax_frame_diagram {A B} (F: ax_frame_cond K A) (G: ax_frame_cond K B)
    (Γ : env K) (mf : mem K) := ∀ Δ k φ m m' b,
  ⊥ [m; mf] → ✓{Γ,Δ} m → ✓{Γ,Δ} mf →
  frame G Γ Δ k φ (m ∪ mf) m' b → ∃ a,
  (** 1.) *) frame F Γ Δ k φ m m' a ∧
  (** 2.) *) ∀ Δ' k' φ' m2 m2',
    unframe F Γ Δ' k' φ' m2 m2' a →
    ✓{Γ,Δ'} m2' → Δ ⇒ₘ Δ' →
    unframe G Γ Δ' k' φ' (m2 ∪ mf) m2' b ∧ ⊥ [m2; mf].
Lemma ax_frame_diagram_empty {A} (F : ax_frame_cond K A) Γ :
  ✓ Γ → ax_frame_diagram F F Γ ∅.
Proof.
  intros ?????? a ??? Ha; exists a.
  rewrite sep_right_id in Ha by solve_sep_disjoint.
  split; auto; intros Δ' k' φ' m2 m2' ???.
  assert (sep_valid m2) by eauto using cmap_valid_sep_valid, unframe_valid.
  split; auto. by rewrite sep_right_id.
Qed.
Lemma ax_frame {A B}(F : ax_frame_cond K A) (G : ax_frame_cond K B)
    (P Q : ax_assert K) Γ δ Δ ρ n k φ m mf :
  ✓ Γ →
  ax_frame_diagram F G Γ mf →
  ⊥ [m; mf] → ✓{Γ,Δ} m → ✓{Γ,Δ} mf →
  ax_graph F P Γ δ Δ ρ n k φ m →
  (∀ Δ' φ' m',
    ⊥ [m'; mf] → ✓{Γ,Δ'} m' → ✓{Γ,Δ'} mf → Δ ⇒ₘ Δ' →
    ax_assert_holds P Γ Δ' ρ φ' m' →
    ax_assert_holds Q Γ Δ' ρ φ' (m' ∪ mf)) →
  ax_graph G Q Γ δ Δ ρ n k φ (m ∪ mf).
Proof.
  intros ? HFG. revert Δ m k φ. induction n as [|n IH]; [constructor |].
  intros Δ m k φ ??? Hax HPQ.
  inversion Hax as [| |???? Hred Hstep]; subst; eauto using ax_done.
  apply ax_further.
  { intros Δ' m' a; rewrite cmap_union_valid by auto; intros [??] ??.
    destruct (HFG Δ' k φ m m' a) as (b&?&_); eauto. }
  intros Δ' m' a S'; rewrite cmap_union_valid by auto; intros [??] ?? p ?.
  destruct (HFG Δ' k φ m m' a) as (b&?&Hunframe); auto.
  feed inversion (Hstep Δ' m' b S') as [? Δ'' k' φ' m2' m2 ? τf']; subst; auto.
  destruct (Hunframe Δ'' k' φ' m2' m2 τf'); trivial.
  apply mk_ax_next with Δ'' (m2' ∪ mf); eauto 10 using @cmap_valid_subseteq,
    @sep_union_subseteq_r, unframe_valid, focus_locks_valid_union.
Qed.

Lemma ax_weaken {A} (F G: ax_frame_cond K A) (P Q: ax_assert K) Γ δ Δ ρ n k φ m:
  ✓ Γ →
  ✓{Γ,Δ} m →
  ax_graph F P Γ δ Δ ρ n k φ m →
  (∀ Δ' k' φ' m2 m2' a,
    ✓{Γ,Δ'} m2 → Δ ⇒ₘ Δ' →
    frame G Γ Δ' k' φ' m2 m2' a →
    frame F Γ Δ' k' φ' m2 m2' a) →
  (∀ Δ' k' φ' m2 m2' a,
    ✓{Γ,Δ'} m2' → Δ ⇒ₘ Δ' →
    unframe F Γ Δ' k' φ' m2 m2' a →
    unframe G Γ Δ' k' φ' m2 m2' a) →
  (∀ Δ' φ' m',
    ✓{Γ,Δ'} m' → Δ ⇒ₘ Δ' →
    ax_assert_holds P Γ Δ' ρ φ' m' → ax_assert_holds Q Γ Δ' ρ φ' m') →
  ax_graph G Q Γ δ Δ ρ n k φ m.
Proof.
  intros ?; revert Δ k φ m. induction n as [|n]; [constructor |].
  intros Δ k φ m ? Hax ???.
  inversion Hax as [| |???? Hred Hstep]; subst; eauto using ax_done.
  apply ax_further; eauto; intros Δ' m' a S' ??? p ?.
  feed inversion (Hstep Δ' m' a S'); subst; eauto.
  econstructor; eauto 15 using unframe_valid.
Qed.

(** The standard framing condition that just adds an arbitrary frame to the
memory before each step and takes it off after. *)
Program Definition ax_disjoint_cond : ax_frame_cond K (mem K) := {|
  frame Γ Δ k φ m m' mf := m' = m ∪ mf ∧ ✓{Γ,Δ} mf ∧ ⊥ [m; mf];
  unframe Γ Δ k φ m m' mf := m' = m ∪ mf ∧ ⊥ [m; mf]
|}.
Next Obligation. auto using cmap_union_valid_2. Qed.
Next Obligation. eauto using cmap_valid_subseteq, @sep_union_subseteq_l. Qed.
Lemma ax_disjoint_cond_frame_diagram Γ mf :
  ✓ Γ → ax_frame_diagram ax_disjoint_cond ax_disjoint_cond Γ mf.
Proof.
  intros ? Δ k φ m m' mf' ??? (->&?&?). exists (mf ∪ mf'); split.
  { split; split_ands; eauto using cmap_union_valid_2.
    by rewrite sep_associative by auto. }
  intros Δ' k' φ' m2 m2' [-> ?] ??; split; eauto.
  split; split_ands; eauto. by rewrite sep_associative by auto.
Qed.
Lemma ax_disjoint_compose_diagram Γ Ek :
  ax_compose_diagram ax_disjoint_cond ax_disjoint_cond Γ [Ek].
Proof.
  intros Δ k φ m ? mf ? (->&?&?); exists mf; split_ands; eauto. by split.
Qed.
End ax_graph.
