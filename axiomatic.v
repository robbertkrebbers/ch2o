(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file defines an axiomatic semantics (in the form of shallow embedding
of a separation logic) for our language. This axiomatic semantics has two
judgments: one for statements and one for expressions. Statement judgment are
sextuples of the shape [Γ\ δ\ R\ J\ T ⊨ₛ {{ P }} s {{ Q }}] where:

- [s] is a statement, and [P] and [Q] are assertions called the pre- and
  postcondition of [s], respectively.
- [R] is a function that gives the returning condition for a return value.
  That means, [R v] has to hold to execute a [return e] where execution of [e]
  yields the value [v].
- [J] is a function that gives the jumping condition for each goto. That means,
  [J l] has to hold to execute a [goto l].
- [T] is a function that gives the jumping condition for each throw.

The assertions [P], [Q], [R], [J] and [T] correspond to the four directions [↘],
[↗], [⇈], [↷] and [↑] in which traversal through a statement can be performed.
We therefore treat the sextuple as a triple [Γ\ Pd ⊨ₚ s] where [Pd] is a
function from directions to assertions such that [Pd ↘ = P], [Pd ↗ = Q],
[Pd (⇈ v) = R v], [P (↷ l) = J l], and [P (↑ n) = T n] *)

(** Expression judgments are quintuples [Γ\ δ\ A ⊨ₑ {{ P }} e {{ Q }}]. As
usual, [P] and [Q] are the pre- and postcondition of [e]. However, whereas the
precondition is just an assertion, the postcondition is a function from values
to assertions. It ensures that if execution of [e] yields a value [v], then
[Q v] holds. The environment [A] can be used to "frame" writable memory that is
being shared by all function calls. *)
Require Export assertions.
Require Import expression_eval_smallstep axiomatic_graph.
Local Open Scope nat_scope.
Local Obligation Tactic := idtac.

Ltac simplify_mem_disjoint_hyps :=
  simplify_sep_disjoint_hyps;
  repeat match goal with
  | H : ✓{_} (_ ∪ _) |- _ =>
     rewrite cmap_union_valid in H by auto; destruct H
  end.
Ltac solve_mem_disjoint :=
  repeat match goal with
  | H : ✓{_} _ |- _ => apply cmap_valid_sep_valid in H
  end; solve_sep_disjoint.

Local Hint Extern 1 (_ ⊥ _) => solve_mem_disjoint.
Local Hint Extern 1 (⊥ _) => solve_mem_disjoint.
Local Hint Extern 1 (sep_valid _) => solve_mem_disjoint.

(** ** Directed assertions *)
(** The statement judgment will be of the shape [Γ\ δ\ Pd ⊨ₚ s] where [Pd] is
a function from directions to assertions taking the pre- and post, returning,
and jumping condition together. We generalize this idea slightly, and define
the type [directed A] as functions [direction → A]. *)
Definition directed_pack {K A} (P : A) (Q : A) (R : val K → A)
    (J : labelname → A) (T : nat → A) (C : option Z → A) : direction K → A :=
  direction_rect _ (λ _, A) P Q R J T C.

(** This hideous definition of [fmap] makes [f <$> directed_pack P Q R J]
convertable with [directed_pack (f P) (f Q) (f ∘ R) (f ∘ J)]. *)
Instance directed_fmap {K} : FMap (direction K →) := λ A B f Pd d,
  match d with
  | ↘ => f (Pd ↘)
  | ↗ => f (Pd ↗)
  | ⇈ v => f (Pd (⇈ v))
  | ↷ l => f (Pd (↷ l))
  | ↑ n => f (Pd (↑ n))
  | ↓ mx => f (Pd (↓ mx))
  end.

Notation dassert K := (direction K → assert K).
Notation dassert_pack P Q R J T C :=
  (@directed_pack _ (assert _) P%A Q%A R%A J%A T%A C%A).
Definition dassert_pack_top `{Env K}
    (P : assert K) (R : val K → assert K) : dassert K :=
  dassert_pack P (R voidV) R (λ _, False%A) (λ _, False%A) (λ _, False%A).

(** ** The Hoare judgment for statements *)
(** Now the interpretation of the statement Hoare judgment is just taking all
of the previously defined notions together. We require both the program and
the memory to contain no locks at the start. Also, we require all locks to be
released in the end, as each statement that contains an expression always has
a sequence point in the end. *)
Inductive ax_stmt_post' `{Env K} (Pd : dassert K) (s : stmt K) (Γ : env K)
    (Δ : memenv K) (ρ : stack K) (n : nat) : focus K → mem K → Prop :=
  mk_ax_stmt_post d m :
    direction_out d s →
    mem_locks m = ∅ →
    assert_holds (Pd d) Γ Δ ρ n (cmap_erase m) →
    ax_stmt_post' Pd s Γ Δ ρ n (Stmt d s) m.
Program Definition ax_stmt_post `{Env K}
    (Pd : dassert K) (s : stmt K) : ax_assert K := {|
  ax_assert_holds := ax_stmt_post' Pd s
|}.
Next Obligation.
  intros ?? Pd s Γ1 Γ2 Δ1 Δ2 ρ n φ m ????; destruct 1 as [d m' ???];
    constructor; eauto using assert_weaken, cmap_erase_valid.
Qed.
Next Obligation.
  intros ?? Pd s Γ δ Δ n ρ φ m m' [d m'' ???] [? p]; inv_rcstep.
Qed.
Definition ax_stmt_packed `{EnvSpec K} (Γ : env K) (δ : funenv K)
    (Pd : dassert K) (s : stmt K) : Prop := ∀ Δ n ρ d m cmτ,
  ✓ Γ →
  ✓{Γ,Δ} m →
  mem_locks m = ∅ →
  direction_in d s →
  (Γ,Δ,ρ.*2) ⊢ s : cmτ →
  ✓{Δ}* ρ →
  assert_holds (Pd d) Γ Δ ρ n (cmap_erase m) →
  ax_graph ax_disjoint_cond (ax_stmt_post Pd s) Γ δ Δ ρ n [] (Stmt d s) m.
Instance: Params (@ax_stmt_packed) 5.
Notation "Γ \ δ \ P ⊨ₚ s" :=
  (ax_stmt_packed Γ δ P%A s)
  (at level 74, δ at next level, P at next level, s at next level,
   format "Γ \  δ \  P  ⊨ₚ  '[' s ']'").

Definition ax_stmt `{EnvSpec K} (Γ : env K) (δ : funenv K) R J T C P s Q :=
  Γ\ δ\ dassert_pack P Q R J T C ⊨ₚ s.
Definition ax_stmt_top `{EnvSpec K} (Γ : env K) (δ : funenv K) P s Q :=
  Γ\ δ\ dassert_pack_top P Q ⊨ₚ s.
Instance: Params (@ax_stmt) 5.
Instance: Params (@ax_stmt_top) 5.
Notation "Γ \ δ \ R \ J \ T \ C ⊨ₛ {{ P }} s {{ Q }}" :=
  (ax_stmt Γ δ R%A J%A T%A C%A P%A s Q%A)
  (at level 74, δ at next level, R at next level,
   J at next level, T at next level, C at next level,
   format "Γ \  δ \  R \  J \  T \  C  ⊨ₛ  '[' {{  P  }} '/'  s  '/' {{  Q  }} ']'").
Notation "Γ \ δ ⊨ₛ {{ P }} s {{ Q }}" :=
  (ax_stmt_top Γ δ P%A s%S Q%A)
  (at level 74, δ at next level,
   format "Γ \  δ  ⊨ₛ  '[' {{  P  }} '/'  s  '/' {{  Q  }} ']'").

(** ** The Hoare judgment for expressions *)
(** The interpretation of the expression judgment is defined similarly as the
interpretation of the judgment for statements. At the start, we require both
the expression and the memory to be lock free. In the end, the locks in the
memory should exactly match the annotated locations in the final expression
that remain to be unlocked. The latter is important, as an unlock operation at
a sequence point thereby corresponds to unlocking everything. *)
Inductive ax_expr_frame (K : Set) : Set :=
  InExpr (mf mA : mem K) | InFun (mf : mem K).
Arguments InExpr {_} _ _.
Arguments InFun {_} _.

Inductive ax_expr_cond_frame `{Env K}
     (ρ : stack K) (A : assert K) (Γ : env K) (Δ : memenv K) (k : ctx K) 
     (n : nat) (φ : focus K) (m m' : mem K) : ax_expr_frame K → Prop :=
  | ax_frame_in_expr mA mf :
     m' = m ∪ mf ∪ mA → ✓{Γ,Δ} mf → ✓{Γ,Δ} mA →
     ⊥ [m; mf; mA] → k = [] → cmap_erased mA → mem_locks mA = ∅ →
     assert_holds A Γ Δ ρ n mA →
     ax_expr_cond_frame ρ A Γ Δ k n φ m m' (InExpr mf mA)
  | ax_frame_in_fun mf :
     m' = m ∪ mf → ✓{Γ,Δ} mf →
     ⊥ [m; mf] → k ≠ [] →
     ax_expr_cond_frame ρ A Γ Δ k n φ m m' (InFun mf).
Inductive ax_expr_cond_unframe `{Env K}
     (ρ : stack K) (A : assert K) (Γ : env K) (Δ : memenv K) (k : ctx K)
     (n : nat) (φ : focus K) (m m' : mem K) : ax_expr_frame K → Prop :=
  | ax_unframe_expr_to_expr mA mf :
     m' = m ∪ mf ∪ mA → ⊥ [m; mf; mA] → k = [] →
     ax_expr_cond_unframe ρ A Γ Δ k n φ m m' (InExpr mf mA)
  | ax_unframe_fun_to_expr mA mf :
     m' = m ∪ mf ∪ mA → ⊥ [m; mf; mA] → k = [] →
     cmap_erased mA → mem_locks mA = ∅ →
     assert_holds A Γ Δ ρ n mA → 
     ax_expr_cond_unframe ρ A Γ Δ k n φ m m' (InFun mf)
  | ax_unframe_expr_to_fun m'' mA mf :
     m = m'' ∪ mA → m' = m'' ∪ mf ∪ mA → ⊥ [m''; mf; mA] → k ≠ [] →
     ax_expr_cond_unframe ρ A Γ Δ k n φ m m' (InExpr mf mA)
  | ax_unframe_fun_to_fun mf :
     m' = m ∪ mf → ⊥ [m; mf] → k ≠ [] →
     ax_expr_cond_unframe ρ A Γ Δ k n φ m m' (InFun mf).
Program Definition ax_expr_cond `{EnvSpec K} (ρ : stack K)
    (A : assert K) : ax_frame_cond K (ax_expr_frame K) := {|
  frame := ax_expr_cond_frame ρ A;
  unframe := ax_expr_cond_unframe ρ A
|}.
Next Obligation.
  intros ??? ρ A Γ Δ k n φ m m' ??;
    destruct 1; subst; auto using cmap_union_valid_2.
Qed.
Next Obligation.
  intros ??? ρ A Γ Δ k n φ m m' ??; destruct 1; subst;
    rewrite ?cmap_union_valid; intuition.
Qed.

Definition ax_expr_funframe `{Env K} (Γ : env K) (Δ : memenv K)
    (A : assert K) (ρ : stack K) (n : nat) (m : mem K) := ∃ mA,
  ⊥ [mA; m] ∧ ✓{Γ,Δ} mA ∧ cmap_erased mA ∧ mem_locks mA = ∅ ∧
  assert_holds A Γ Δ ρ n mA.
Inductive ax_expr_post' `{Env K} (Q : lrval K → assert K)
    (τlr : lrtype K) (Γ : env K) (Δ : memenv K) (ρ : stack K)
    (n : nat) : focus K → mem K → Prop :=
  mk_ax_expr_post ν Ω m :
    (Γ,Δ) ⊢ ν : τlr →
    mem_locks m = Ω →
    assert_holds (Q ν) Γ Δ ρ n (cmap_erase m) →
    ax_expr_post' Q τlr Γ Δ ρ n (Expr (%#{Ω} ν)) m.
Program Definition ax_expr_post `{EnvSpec K}
    (Q : lrval K → assert K) (τlr : lrtype K) : ax_assert K := {|
  ax_assert_holds := ax_expr_post' Q τlr
|}.
Next Obligation.
  intros ??? Q τlr Γ1 Γ2 Δ1 Δ2 ρ n φ m ????; destruct 1; constructor;
    eauto using assert_weaken, cmap_erase_valid, lrval_typed_weaken.
Qed.
Next Obligation.
  intros ??? Q τlr Γ δ Δ ρ n φ m m' [d m'' ???] [? p]; inv_rcstep.
Qed.
Definition ax_expr `{EnvSpec K} (Γ : env K) (δ : funenv K) (A P : assert K)
    (e : expr K) (Q : lrval K → assert K) : Prop := ∀ Δ n ρ m τlr,
  ✓ Γ →
  ✓{Γ,Δ} m →
  mem_locks m = ∅ →
  (Γ,Δ,ρ.*2) ⊢ e : τlr →
  locks e = ∅ →
  ✓{Δ}* ρ →
  ax_expr_funframe Γ Δ A ρ n m →
  assert_holds P Γ Δ ρ n (cmap_erase m) →
  ax_graph (ax_expr_cond ρ A) (ax_expr_post Q τlr) Γ δ Δ ρ n [] (Expr e) m.
Instance: Params (@ax_expr) 5.
Notation "Γ \ δ \ A ⊨ₑ {{ P }} e {{ Q }}" :=
  (ax_expr Γ δ A%A P%A e Q%A)
  (at level 74, δ at next level, A at next level,
  format "Γ \  δ \  A  ⊨ₑ  '[' {{  P  }} '/'  e  '/' {{  Q  }} ']'").

Section axiomatic.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types o : index.
Implicit Types Δ : memenv K.
Implicit Types δ : funenv K.
Implicit Types m : mem K.
Implicit Types e : expr K.
Implicit Types s : stmt K.
Implicit Types τ σ : type K.
Implicit Types a : addr K.
Implicit Types v : val K.
Implicit Types ν : lrval K.
Implicit Types k : ctx K.
Implicit Types d : direction K.
Implicit Types φ : focus K.
Implicit Types S : state K.

Hint Immediate cmap_valid_memenv_valid.
Hint Resolve cmap_empty_valid cmap_erased_empty mem_locks_empty.
Hint Resolve cmap_union_valid_2 cmap_erase_valid.
Hint Extern 1 (_ ≤ _) => omega.

Global Instance directed_pack_proper `{!@Equivalence A R} :
  Proper (R ==> R ==> pointwise_relation _ R ==> pointwise_relation _ R ==>
    pointwise_relation _ R ==> pointwise_relation _ R ==>
    pointwise_relation _ R) (@directed_pack K A).
Proof. intros ?????????????????? []; simplify_equality'; auto. Qed.
Lemma directed_fmap_spec {A B} (f : A → B) (P : direction K → A) d :
  (f <$> P) d = f (P d).
Proof. by destruct d. Qed.
Global Instance ax_stmt_packed_proper Γ δ : Proper
  (pointwise_relation _ (≡{Γ}) ==> (=) ==> iff) (ax_stmt_packed Γ δ).
Proof.
  cut (Proper (pointwise_relation _ (≡{Γ}) ==> (=) ==> impl)
              (ax_stmt_packed Γ δ)).
  { intros help. by split; apply help. }
  intros Pd Qd HPQ ?? -> Hax ?????????????.
  eapply ax_weaken with ax_disjoint_cond (ax_stmt_post Pd y) n; eauto.
  { eapply Hax, HPQ; eauto. }
  destruct 2; constructor; auto. eapply HPQ; eauto using indexes_valid_weaken.
Qed.
Lemma ax_stmt_top_unfold Γ δ P (Q : val _ → assert _) s :
  Γ\ δ ⊨ₛ {{ P }} s {{ Q }} ↔
  Γ\ δ \ Q \ (λ _, False)\ (λ _, False)\ (λ _, False) ⊨ₛ {{ P }} s {{ Q voidV }}.
Proof. done. Qed.
Global Instance ax_stmt_proper Γ δ :
  Proper (pointwise_relation _ (≡{Γ}) ==> pointwise_relation _ (≡{Γ}) ==>
     pointwise_relation _ (≡{Γ}) ==> pointwise_relation _ (≡{Γ}) ==>
     (≡{Γ}) ==> (=) ==> (≡{Γ}) ==> iff) (ax_stmt Γ δ).
Proof.
  intros ?? HR ?? HJ ?? HT ?? HC ?? HP ?? -> ?? HQ.
  unfold ax_stmt. by rewrite HR, HJ, HT, HC, HP, HQ.
Qed.
Global Instance ax_stmt_top_proper Γ δ :
  Proper ((≡{Γ}) ==> (=) ==> pointwise_relation _ (≡{Γ}) ==> iff)
         (ax_stmt_top Γ δ).
Proof.
  intros ?? HP ?? -> ?? HQ.
  unfold ax_stmt_top, dassert_pack_top. by rewrite HP, HQ.
Qed.

Lemma ax_expr_funframe_emp Γ Δ ρ n m : ✓{Γ,Δ} m → ax_expr_funframe Γ Δ emp ρ n m.
Proof. by eexists ∅; split_ands; eauto. Qed.
Hint Resolve ax_expr_funframe_emp.
Lemma ax_expr_funframe_weaken Γ Δ A ρ n1 n2 m1 m2 :
  ✓ Γ → ✓{Δ}* ρ →
  ax_expr_funframe Γ Δ A ρ n1 m2 → m1 ⊆ m2 → n2 ≤ n1 →
  ax_expr_funframe Γ Δ A ρ n2 m1.
Proof.
  intros ?? (mA&?&?&?&?&?) Hm12; exists mA; split_ands; eauto using assert_weaken.
  by rewrite <-(sep_subseteq_disjoint_le m1) by eauto.
Qed.
Lemma ax_disjoint_expr_compose_diagram Γ ρ A Ek :
  ax_compose_diagram ax_disjoint_cond (ax_expr_cond ρ A) Γ [Ek].
Proof.
  intros Δ k n φ a m m' ?; simpl. destruct 1; subst; [discriminate_list_equality|].
  exists mf; split_ands; auto; intros Δ' k' φ' m2 m2' ?? [-> ?].
  constructor; trivial; intro; discriminate_list_equality.
Qed.
Hint Resolve ax_disjoint_expr_compose_diagram.
Lemma ax_expr_disjoint_compose_diagram Γ ρ k :
  ax_compose_diagram (ax_expr_cond ρ emp%A) ax_disjoint_cond Γ k.
Proof.
  intros Δ k' φ n m m' mf ? (->&?&?); simpl; destruct (decide (k' = [])) as [->|].
  * exists (InExpr mf ∅). split.
    { by constructor; rewrite ?sep_right_id by auto;
        eauto using mem_locks_empty, cmap_empty_valid, cmap_erased_empty. }
    intros Δ' k'' φ' m2 m2' ??; inversion 1; subst;
      rewrite ?sep_right_id by auto; auto.
  * exists (InFun mf); split; [by constructor|].
    intros Δ' k'' φ' m2 m2' ??; inversion 1 as [|mA mf' ????? [??]| | ]; subst;
      rewrite ?sep_right_id by auto; auto.
Qed.
Hint Resolve ax_expr_disjoint_compose_diagram.
Lemma ax_expr_cond_frame_diagram_simple Γ ρ B mf :
  ax_frame_diagram (ax_expr_cond ρ B) (ax_expr_cond ρ B) Γ mf.
Proof.
  intros Δ k φ n m m' ?; destruct 4 as [mA mf'|mf']; subst.
  * simplify_mem_disjoint_hyps; exists (InExpr (mf ∪ mf') mA); split.
    { constructor; auto. by rewrite sep_associative by auto. }
    intros Δ' k' φ' m2 m2'.
    inversion 1 as [| |m''|]; intros; simplify_mem_disjoint_hyps; subst.
    + split; auto. apply ax_unframe_expr_to_expr; auto.
      by rewrite sep_associative by auto.
    + split; auto. apply ax_unframe_expr_to_fun with (m'' ∪ mf); auto.
      - by rewrite <-!sep_associative, (sep_commutative mA) by auto.
      - by rewrite sep_associative by auto.
  * simplify_mem_disjoint_hyps; exists (InFun (mf ∪ mf')); split.
    { constructor; auto. by rewrite sep_associative by auto. }
    intros Δ' k' φ' m2 m2'.
    inversion 1 as [|mA| |]; intros; simplify_mem_disjoint_hyps; subst.
    + split; auto. apply ax_unframe_fun_to_expr with mA; auto.
      by rewrite sep_associative by auto.
    + split; auto. apply ax_unframe_fun_to_fun; auto.
      by rewrite sep_associative by auto.
Qed.
Hint Resolve ax_expr_cond_frame_diagram_simple.

Global Instance ax_expr_proper Γ δ :
  Proper ((≡{Γ}) ==> (≡{Γ}) ==> (=) ==> pointwise_relation _ (≡{Γ}) ==> iff)
         (ax_expr Γ δ).
Proof.
  cut (Proper ((≡{Γ}) ==> (≡{Γ}) ==> (=) ==>
    pointwise_relation _ (≡{Γ}) ==> impl) (ax_expr Γ δ)).
  { intros help. by split; apply help. }
  intros A1 A2 HA P1 P2 HP ?? -> Q1 Q2 HQ Hax ??????????? (?&?&?&?&?&?) ?.
  eapply ax_weaken with (ax_expr_cond ρ A1) (ax_expr_post Q1 τlr) n; eauto.
  * apply Hax, HP; eauto.
    econstructor; split_ands; eauto. apply HA; eauto.
  * destruct 2; constructor; auto. apply HA; eauto using indexes_valid_weaken.
  * destruct 2; subst; simplify_mem_disjoint_hyps;
     econstructor (first [by eauto|apply HA; eauto using indexes_valid_weaken]).
  * destruct 2; constructor; auto. apply HQ; eauto using indexes_valid_weaken.
Qed.

Lemma ax_expr_post_expr_nf Γ Q Δ ρ n m e τlr :
  ax_expr_post' Q τlr Γ Δ ρ n (Expr e) m → is_nf e.
Proof. by inversion 1. Qed.
Lemma ax_expr_lrval Γ δ A (P : lrval K → assert K) Δ ρ n ν Ω m τlr :
  ✓{Γ,Δ} m → ax_expr_funframe Γ Δ A ρ n m →
  ax_graph (ax_expr_cond ρ A)
    (ax_expr_post P τlr) Γ δ Δ ρ (S n) [] (Expr (%#{Ω} ν)%E) m →
  assert_holds (P ν) Γ Δ ρ (S n) (cmap_erase m)
  ∧ mem_locks m = Ω ∧ (Γ,Δ) ⊢ ν : τlr.
Proof.
  intros ? (mA&?&?&?&?&?);
    inversion 1 as [|??? [??????]|???? Hred]; subst; try by auto.
  destruct (Hred Δ n (m ∪ mA) (InExpr ∅ mA)); auto.
  * constructor; eauto using assert_weaken. by rewrite sep_right_id by auto.
  * inv_rcstep.
Qed.

(** The lemma [ax_expr_compose] is used to prove the structural Hoare rules for
expressions. It is proven by chasing all (interleaved) reduction paths for the
compound expression. This is done step-wise by distinguishing the following
cases:

- All subexpressions are values.
- Some subexpression contains a redex that is not a function call.
- Some subexpression contains a redex that is a function call. In this case we
  use the lemma [ax_call_compose]. *)
Lemma ax_call_compose Γ δ A P Q (E : ectx K) E' ρ Δ n φ k m1 m2 :
  ✓ Γ → locks E' ⊆ locks E ∪ mem_locks m2 →
  ⊥ [m1; m2] → ✓{Γ,Δ} m1 → ✓{Γ,Δ} m2 →
  ax_graph (ax_expr_cond ρ A) P Γ δ Δ ρ n (k ++ [CFun E]) φ m1 →
  (∀ Δ' n' m1' e',
    ⊥ [m1'; m2] → ✓{Γ,Δ'} m1' → ✓{Γ,Δ'} m2 →
    locks (subst E e') ⊆ mem_locks m1' →
    ax_expr_funframe Γ Δ' A ρ n' (m1' ∪ m2) →
    ax_graph (ax_expr_cond ρ A) P Γ δ Δ' ρ n' [] (Expr (subst E e')) m1' →
    Δ ⇒ₘ Δ' → n' ≤ n →
    ax_graph (ax_expr_cond ρ A) Q Γ δ Δ' ρ n' []
      (Expr (subst E' e')) (m1' ∪ m2)) →
  ax_graph (ax_expr_cond ρ A) Q Γ δ Δ ρ n (k ++ [CFun E']) φ (m1 ∪ m2).
Proof.
  intros ? HE; revert Δ k φ m1.
  induction n as [[|n] IH] using lt_wf_ind;
    intros Δ k φ m1 ??? Hax Hnext; [apply ax_O |].
  inversion Hax as [| |???? Hred Hstep];
    clear Hax; subst; try discriminate_list_equality.
  apply ax_further.
  { intros Δ' n' m' a ??? Hframe; inversion_clear Hframe;
      subst; try discriminate_list_equality; simplify_mem_disjoint_hyps.
    destruct (Hred Δ' n' (m1 ∪ m2 ∪ mf) (InFun (m2 ∪ mf))) as [S' p]; auto.
    { rewrite <-sep_associative by auto; constructor; auto.
      intro; discriminate_list_equality. }
    apply (rcstep_call_inv _ _ _ E E' _ _ _ _ _ p); intros; subst; eauto. }
  intros Δ' n' ?? S' ??? Hframe p;
    inversion_clear Hframe as [mA mf|mf]; subst;
    try discriminate_list_equality; simplify_mem_disjoint_hyps.
  pattern S'; apply (rcstep_call_inv _ _ _ _ E _ _ _ _ _ p).
  * intros k' φ' m' p' ?.
    feed inversion (Hstep Δ' n' (m1 ∪ m2 ∪ mf) (InFun (m2 ∪ mf))
      (State (k' ++ [CFun E]) φ' m')) as [Δ'' ?? ? m1' ?? Hunframe];
      subst; trivial.
    { rewrite <-sep_associative by auto. constructor; auto.
      intro; discriminate_list_equality. }
    inversion_clear Hunframe as [|mA| |]; subst;
      try discriminate_list_equality; simplify_mem_disjoint_hyps.
    apply mk_ax_next with Δ'' (m1' ∪ m2), IH;
      eauto 6 using focus_locks_valid_union.
    rewrite sep_associative by auto. constructor; auto.
    intro; discriminate_list_equality.
  * intros f v -> -> p' ?.
    feed inversion (Hstep Δ' n' (m1 ∪ m2 ∪ mf) (InFun (m2 ∪ mf))
      (State [] (Expr (subst E (# v)%E))
      (m1 ∪ m2 ∪ mf))) as [Δ'' ??? m1' ?? Hunframe _ Hlocks];
      subst; trivial.
    { rewrite <-sep_associative by auto. constructor; auto. }
    inversion_clear Hunframe as [|mA ? Hm| |];
      simplify_equality'; simplify_mem_disjoint_hyps.
    assert (m1 = m1' ∪ mA); [|subst; simplify_mem_disjoint_hyps].
    { apply sep_cancel_r with (m2 ∪ mf); auto.
      rewrite <-(sep_associative m1'), (sep_commutative mA) by auto.
      by rewrite sep_associative, (sep_associative m1') by auto. }
    apply mk_ax_next with Δ'' (m1' ∪ m2); auto.
    + apply ax_unframe_fun_to_expr with mA; auto.
      by rewrite !sep_associative in Hm by auto.
    + simpl; rewrite mem_locks_union by auto; revert Hlocks HE; clear.
      rewrite !ectx_subst_locks; esolve_elem_of.
    + eapply Hnext; eauto. exists mA; auto.
Qed.
Lemma ax_expr_compose Γ δ {vn} A (Ps : vec (vassert K) vn) (Q : vassert K)
    Δ (E : ectx_full K vn) (es : vec (expr K) vn) (ρ : stack K) n
    (ms : vec (mem K) vn) (τlrs : vec (lrtype K) vn) σlr :
  ✓ Γ → locks E = ∅ → ✓{Δ}* ρ →
  ⊥ ms → (∀ i, ✓{Γ,Δ} (ms !!! i)) →
  ax_expr_funframe Γ Δ A ρ n (⋃ ms) →
  (∀ i, locks (es !!! i) ⊆ mem_locks (ms !!! i)) →
  (∀ i, ax_graph (ax_expr_cond ρ A) (ax_expr_post (Ps !!! i) (τlrs !!! i))
      Γ δ Δ ρ n [] (Expr (es !!! i)) (ms !!! i)) →
  (∀ Δ' n' (Ωs : vec _ vn) (νs : vec _ vn) (ms' : vec _ vn),
    ⊥ ms' → (∀ i, ✓{Γ,Δ'} (ms' !!! i)) → Δ ⇒ₘ Δ' → n' ≤ n →
    (∀ i, (Γ,Δ') ⊢ νs !!! i : τlrs !!! i) →
    (∀ i, mem_locks (ms' !!! i) = Ωs !!! i) →
    (∀ i,
      assert_holds ((Ps !!! i) (νs !!! i)) Γ Δ' ρ n' (cmap_erase (ms' !!! i))) →
    ax_graph (ax_expr_cond ρ A) (ax_expr_post Q σlr) Γ δ Δ' ρ n' []
       (Expr (depsubst E (vzip_with EVal Ωs νs)%E)) (⋃ ms')) →
  ax_graph (ax_expr_cond ρ A) (ax_expr_post Q σlr) Γ δ Δ ρ n []
    (Expr (depsubst E es)) (⋃ ms).
Proof.
  intros ? HE. revert Δ es ms.
  induction n as [[|n] IH] using lt_wf_ind; [intros; apply ax_O |].
  intros Δ es ms Hρ Hms Hms' HA Hes Hax1 Hax2.
  destruct (expr_vec_values es) as [(Ωs&νs&->)|[i Hi]].
  { apply Hax2; auto;
      intros i; specialize (Hax1 i); rewrite vlookup_zip_with in Hax1;
      (eapply ax_expr_lrval; [| |eauto]);
      eauto using ax_expr_funframe_weaken, @sep_subseteq_lookup. }
  apply ax_further_alt.
  intros Δ' n' m' a ??? Hframe; inversion_clear Hframe as [mA mf ??? Hm|];
    simplify_equality'; simplify_mem_disjoint_hyps.
  split; [|intros S' p].
  { rewrite (ectx_full_to_item_correct _ _ i); apply (rcred_ectx _ _ [_]).
    assert (⊥ (ms !!! i :: delete (i:nat) (ms:list _) ++ [mf;mA])).
    { by rewrite app_comm_cons, sep_disjoint_equiv_delete. }
    eapply (ax_red (ax_expr_cond ρ A) (ax_expr_post (Ps !!! i) (τlrs !!! i)))
      with Δ' n' (ms !!! i) (InExpr (⋃ delete (i:nat) (ms:list _) ∪ mf) mA).
    { eauto using cmap_union_list_lookup_valid. }
    { econstructor; auto 1.
      { by rewrite sep_associative, sep_union_delete by auto. }
      apply cmap_union_valid_2; auto.
      apply cmap_union_list_valid, Forall_delete, Forall_vlookup;
        eauto using cmap_union_list_lookup_valid. }
    { simpl; contradict Hi; eauto using ax_expr_post_expr_nf. }
    eauto using ax_graph_weaken.  }
  pattern S'; apply (rcstep_expr_depsubst_inv _ _ _ _ _ _ _ _ p); clear p.
  * clear i Hi; intros i e' m2 p' ?.
    assert (⊥ (ms !!! i :: delete (i:nat) (ms:list _) ++ [mf;mA])).
    { by rewrite app_comm_cons, sep_disjoint_equiv_delete. }
    feed inversion (ax_step (ax_expr_cond ρ A)
      (ax_expr_post (Ps !!! i) (τlrs !!! i))
      Γ δ Δ' ρ n' [] (Expr (es !!! i)) (ms !!! i)
      (ms !!! i ∪ ⋃ delete (i:nat) (ms:list _) ∪ mf ∪ mA)
      (InExpr (⋃ delete (i:nat) (ms:list _) ∪ mf) mA)
      (State [] (Expr e') m2)) as [Δ'' ? n'' ? m ?? Hunframe _]; subst; auto.
    { eauto using cmap_union_list_lookup_valid. }
    { constructor; rewrite ?sep_associative by auto; auto.
      apply cmap_union_valid_2; auto.
      apply cmap_union_list_valid, Forall_delete, Forall_vlookup;
        eauto using cmap_union_list_lookup_valid. }
    { by rewrite sep_union_delete by done. }
    { by rewrite sep_union_delete by done. }
    { eauto using ax_graph_weaken. }
    clear Hm.
    inversion_clear Hunframe; simplify_equality; simplify_mem_disjoint_hyps.
    apply mk_ax_next with Δ'' (m ∪ ⋃ delete (i:nat) (ms:list _)); simpl; auto.
    { constructor; auto. by rewrite sep_associative by auto. }
    { rewrite ectx_full_subst_locks, HE, (left_id_L ∅ (∪)).
      rewrite <-sep_union_insert by auto.
      rewrite mem_locks_union_list by (rewrite sep_disjoint_equiv_insert; auto).
      apply union_list_preserving, Forall2_fmap, Forall2_vlookup.
      intros j; destruct (decide (i = j)); subst; [by rewrite !vlookup_insert|].
      by rewrite !vlookup_insert_ne. }
    rewrite <-sep_union_insert by auto.
    assert (⊥ (mf :: mA :: vinsert i m ms)).
    { rewrite sep_disjoint_equiv_insert; auto. }
    apply IH; auto.
    + eauto using indexes_valid_weaken.
    + intros j. destruct (decide (i = j)); subst; [by rewrite !vlookup_insert|].
      rewrite vlookup_insert_ne by done.
      eauto using cmap_union_list_delete_lookup_valid.
    + exists mA; split_ands; eauto using assert_weaken, indexes_valid_weaken.
    + intros j; destruct (decide (i = j)); subst; [by rewrite !vlookup_insert|].
      by rewrite !vlookup_insert_ne.
    + intros j; destruct (decide (i = j)); subst; [by rewrite !vlookup_insert|].
      rewrite !vlookup_insert_ne by done.
      apply ax_graph_weaken with Δ (S n); eauto.
  * clear i Hi. intros i E' Ω f τs τ Ωs vs ? Hesi p ?.
    assert (Ω ∪ ⋃ Ωs ⊆ mem_locks (ms !!! i)) as HΩ.
    { transitivity (locks (es !!! i)); [|done].
      rewrite Hesi, ectx_subst_locks; simpl.
      rewrite fmap_zip_with_l by auto; clear; solve_elem_of. }
    assert (⊥ (mf :: mA :: ms !!! i :: delete (i:nat) (ms:list _))).
    { rewrite sep_disjoint_equiv_delete by auto; auto. }
    assert (⊥ (mf :: mA ::
      mem_unlock (Ω ∪ ⋃ Ωs) (ms !!! i) :: delete (i:nat) (ms:list _))).
    { rewrite <-mem_unlock_disjoint_le by auto; auto. }
    feed inversion (ax_step (ax_expr_cond ρ A)
      (ax_expr_post (Ps !!! i) (τlrs !!! i))
      Γ δ Δ' ρ n' [] (Expr (es !!! i)) (ms !!! i)
      (⋃ ms ∪ mf ∪ mA) (InExpr (⋃ delete (i:nat) (ms:list _) ∪ mf) mA)
      (State [CFun E'] (Call f vs) (mem_unlock (Ω ∪ ⋃ Ωs) (⋃ ms ∪ mf ∪ mA))))
      as [Δ'' ? n'' ? m ?? Hunframe _ ? Hm']; trivial; subst.
    { eauto using cmap_union_list_lookup_valid. }
    { constructor; auto.
      { by rewrite sep_associative, sep_union_delete by auto. }
      apply cmap_union_valid_2; auto.
      apply cmap_union_list_valid, Forall_delete, Forall_vlookup;
        eauto using cmap_union_list_lookup_valid. }
    { eauto using ax_graph_weaken, cmap_union_list_lookup_valid. }
    apply mk_ax_next with Δ''
      (mem_unlock (Ω ∪ ⋃ Ωs) (ms !!! i) ∪ ⋃ delete (i:nat) (ms:list _) ∪ mA);
      simpl; auto.
    { rewrite <-(sep_union_delete ms i), !mem_unlock_union by (by auto
         || rewrite !mem_locks_union by auto; revert HΩ; clear; solve_elem_of).
      eapply ax_unframe_expr_to_fun; eauto. }
    inversion_clear Hunframe as [|m''| |];
      simplify_equality'; simplify_mem_disjoint_hyps.
    assert (mem_unlock (Ω ∪ ⋃ Ωs) (ms !!! i) = m''); subst.
    { apply sep_cancel_r with (⋃ delete (i:nat) (ms:list _) ∪ mf ∪ mA); auto.
      rewrite <-mem_unlock_union, (sep_associative m'') by auto.
      by rewrite !(sep_associative (ms !!! i)), sep_union_delete by auto. }
    rewrite <-(sep_union_delete ms i), !mem_unlock_union in Hm' by
      (by auto || rewrite !mem_locks_union by auto; revert HΩ; solve_elem_of).
    simplify_mem_disjoint_hyps.
    rewrite (sep_commutative _ mA), sep_associative by auto.
    apply ax_call_compose with
      (P:=ax_expr_post (Ps !!! i) (τlrs !!! i)) (k:=[]) (E:=E'); auto.
    { rewrite locks_snoc. apply union_preserving_l.
      rewrite ectx_full_to_item_locks, HE, (left_id_L ∅ (∪)).
      rewrite mem_locks_union_list by solve_mem_disjoint.
      apply union_list_preserving, Forall2_fmap, Forall2_delete.
      apply Forall2_vlookup; auto. }
    { by rewrite (sep_commutative mA) by auto. }
    intros Δ''' n''' m' e' ????? HmA ? Hax; simplify_mem_disjoint_hyps.
    rewrite <-sep_union_insert by auto.
    rewrite subst_snoc, <-ectx_full_to_item_correct_alt.
    apply IH; auto.
    + eauto using indexes_valid_weaken.
    + rewrite sep_disjoint_equiv_insert; auto.
    + intros j; destruct (decide (i = j)); subst; [by rewrite !vlookup_insert|].
      rewrite vlookup_insert_ne by done.
      eauto using cmap_union_list_delete_lookup_valid.
    + by rewrite sep_union_insert by auto.
    + intros j; destruct (decide (i = j)); subst; [by rewrite !vlookup_insert|].
      by rewrite !vlookup_insert_ne by done.
    + intros j; destruct (decide (i = j)); subst; [by rewrite !vlookup_insert|].
      rewrite !vlookup_insert_ne by done.
      apply ax_graph_weaken with Δ (S n); eauto.
  * rewrite Forall_vlookup; naive_solver.
  * clear i Hi. intros i E' e ? p ?.
    destruct (ax_step_undef (ax_expr_cond ρ A)
      (ax_expr_post (Ps !!! i) (τlrs !!! i)) Γ δ Δ' ρ n' [] (Expr (es !!! i))
      (ms !!! i) (⋃ ms ∪ mf ∪ mA)
      (InExpr (⋃ delete (i:nat) (ms:list _) ∪ mf) mA) [] (UndefExpr E' e)
      (⋃ ms ∪ mf ∪ mA));
      eauto using cmap_union_list_lookup_valid, ax_graph_weaken.
    assert (⊥ (mf :: mA :: ms !!! i :: delete (i:nat) (ms:list _))).
    { rewrite sep_disjoint_equiv_delete; auto. }
    constructor; auto.
    { by rewrite sep_associative, sep_union_delete by auto. }
    apply cmap_union_valid_2; auto.
    apply cmap_union_list_valid, Forall_delete, Forall_vlookup;
      eauto using cmap_union_list_lookup_valid.
Qed.
Lemma ax_expr_compose_1 Γ δ A P Q Δ (E : ectx_full K 1) e ρ n m τlr σlr :
  ✓ Γ → locks E = ∅ → ✓{Δ}* ρ → ✓{Γ,Δ} m →
  ax_expr_funframe Γ Δ A ρ n m →
  locks e ⊆ mem_locks m →
  ax_graph (ax_expr_cond ρ A) (ax_expr_post P τlr) Γ δ Δ ρ n [] (Expr e) m →
  (∀ Δ' n' Ω ν m',
    ✓{Γ,Δ'} m' → Δ ⇒ₘ Δ' → n' ≤ n → (Γ,Δ') ⊢ ν : τlr → mem_locks m' = Ω →
    assert_holds (P ν) Γ Δ' ρ n' (cmap_erase m') →
    ax_graph (ax_expr_cond ρ A) (ax_expr_post Q σlr) Γ δ Δ' ρ n' []
       (Expr (depsubst E [# %#{Ω} ν]%E)) m') →
  ax_graph (ax_expr_cond ρ A) (ax_expr_post Q σlr) Γ δ Δ ρ n []
    (Expr (depsubst E [# e])) m.
Proof.
  intros ??????? Hax. rewrite <-(sep_right_id m) by auto.
  apply (ax_expr_compose Γ δ A [# P]%A _ Δ E [# e] ρ n [# m] [# τlr]); simpl;
    rewrite ?sep_right_id by auto; auto; try (by intros; inv_all_vec_fin).
  intros Δ' n' Ωs νs ms' ? Hm' ?? Hν Hlocks Hax'; inv_all_vec_fin; simpl.
  apply Hax; simpl; rewrite ?sep_right_id by auto; auto;
    apply (Hm' 0%fin) || apply (Hν 0%fin) ||
    apply (Hlocks 0%fin) || apply (Hax' 0%fin).
Qed.
Lemma ax_expr_compose_2 Γ δ A P1 P2 Q Δ
    (E : ectx_full K 2) e1 e2 ρ n m1 m2 τlr1 τlr2 σlr :
  ✓ Γ → locks E = ∅ → ✓{Δ}* ρ → ⊥ [m1; m2] → ✓{Γ,Δ} m1 → ✓{Γ,Δ} m2 →
  ax_expr_funframe Γ Δ A ρ n (m1 ∪ m2) →
  locks e1 ⊆ mem_locks m1 → locks e2 ⊆ mem_locks m2 →
  ax_graph (ax_expr_cond ρ A) (ax_expr_post P1 τlr1) Γ δ Δ ρ n [] (Expr e1) m1 →
  ax_graph (ax_expr_cond ρ A) (ax_expr_post P2 τlr2) Γ δ Δ ρ n [] (Expr e2) m2 →
  (∀ Δ' n' Ω1 Ω2 ν1 ν2 m1' m2',
    ⊥ [m1';m2'] → ✓{Γ,Δ'} m1' → ✓{Γ,Δ'} m2' → Δ ⇒ₘ Δ' → n' ≤ n →
    (Γ,Δ') ⊢ ν1 : τlr1 → (Γ,Δ') ⊢ ν2 : τlr2 →
    mem_locks m1' = Ω1 → mem_locks m2' = Ω2 →
    assert_holds (P1 ν1) Γ Δ' ρ n' (cmap_erase m1') →
    assert_holds (P2 ν2) Γ Δ' ρ n' (cmap_erase m2') →
    ax_graph (ax_expr_cond ρ A) (ax_expr_post Q σlr) Γ δ Δ' ρ n' []
       (Expr (depsubst E [# %#{Ω1} ν1; %#{Ω2} ν2]%E)) (m1' ∪ m2')) →
  ax_graph (ax_expr_cond ρ A) (ax_expr_post Q σlr) Γ δ Δ ρ n []
    (Expr (depsubst E [# e1; e2])) (m1 ∪ m2).
Proof.
  intros ??????????? Hax. rewrite <-(sep_right_id m2) by auto.
  apply (ax_expr_compose Γ δ A [# P1; P2]%A Q Δ E
    [# e1; e2] ρ n [# m1; m2] [# τlr1; τlr2] σlr); simpl;
    rewrite ?sep_right_id by auto; auto; try (by intros; inv_all_vec_fin).
  intros Δ' n' Ωs νs ms' ? Hm' ?? Hν Hlocks Hax'; inv_all_vec_fin; simpl.
  apply Hax; simpl; rewrite ?sep_right_id by auto; auto;
    repeat match goal with
    | H : ∀ _ : fin _, _ |- _ => apply (H 0%fin)
    | H : ∀ _ : fin _, _ |- _ => apply (H 1%fin)
    end.
Qed.
End axiomatic.
