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
Require Import axiomatic_graph.
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
Local Hint Extern 1 (_ ## _) => solve_mem_disjoint: core.
Local Hint Extern 1 (## _) => solve_mem_disjoint: core.
Local Hint Extern 1 (sep_valid _) => solve_mem_disjoint: core.
Local Hint Extern 1 (_ ⊆ _) => etransitivity; [eassumption|]: core.
Local Hint Extern 1 (_ ≤ _) => lia: core.

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
#[global] Instance directed_fmap {K} : FMap (direction K →.) := λ A B f Pd d,
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
Inductive ax_stmt_post' `{Env K} (Pd : dassert K) (s : stmt K) (cmτ : rettype K)
    (Γ : env K) (Δ : memenv K) (δ : funenv K)
    (ρ : stack K) (n : nat) : focus K → mem K → Prop :=
  mk_ax_stmt_post d m :
    direction_out d s → (Γ,Δ) ⊢ d : cmτ →
    mem_locks m = ∅ →
    assert_holds (Pd d) Γ Δ δ ρ n (cmap_erase m) →
    ax_stmt_post' Pd s cmτ Γ Δ δ ρ n (Stmt d s) m.
Program Definition ax_stmt_post `{EnvSpec K} (Pd : dassert K)
    (s : stmt K) (cmτ : rettype K) : ax_assert K := {|
  ax_assert_holds := ax_stmt_post' Pd s cmτ
|}.
Next Obligation.
  intros ??? Pd s cmτ Γ1 Γ2 Δ1 Δ2 δ1 δ2 ρ n n' φ m ????;
    destruct 1 as [d m' ????]; constructor;
    eauto using direction_typed_weaken, assert_weaken, cmap_erase_valid.
Qed.
Next Obligation.
  intros ??? Pd s cmτ Γ Δ δ n ρ φ m m' [d m'' ????] [? p]; inv_rcstep; set_solver.
Qed.
Definition ax_stmt_packed `{EnvSpec K} (Γ : env K) (δ : funenv K)
    (Pd : dassert K) (s : stmt K) : Prop := ∀ Γ' Δ δ' n ρ d m cmτ,
  ✓ Γ' → Γ ⊆ Γ' → δ ⊆ δ' →
  ✓{Γ',Δ} δ' →
  ✓{Γ',Δ} m →
  mem_locks m = ∅ →
  direction_in d s →
  (Γ',Δ,ρ.*2) ⊢ s : cmτ →
  ✓{Δ}* ρ →
  assert_holds (Pd d) Γ' Δ δ' ρ n (cmap_erase m) →
  ax_graph ax_disjoint_cond (ax_stmt_post Pd s cmτ) Γ' δ' Δ ρ n [] (Stmt d s) m.
#[global] Instance: Params (@ax_stmt_packed) 5 := {}.
Notation "Γ \ δ \ P ⊨ₚ s" :=
  (ax_stmt_packed Γ δ P%A s)
  (at level 74, δ at next level, P at next level, s at next level,
   format "Γ \  δ \  P  ⊨ₚ  '[' s ']'") : C_scope.

Definition ax_stmt `{EnvSpec K} (Γ : env K) (δ : funenv K) R J T C P s Q :=
  Γ\ δ\ dassert_pack P Q R J T C ⊨ₚ s.
Definition ax_stmt_top `{EnvSpec K} (Γ : env K) (δ : funenv K) P s Q :=
  Γ\ δ\ dassert_pack_top P Q ⊨ₚ s.
#[global] Instance: Params (@ax_stmt) 5 := {}.
#[global] Instance: Params (@ax_stmt_top) 5 := {}.
Notation "Γ \ δ \ R \ J \ T \ C ⊨ₛ {{ P } } s {{ Q } }" :=
  (ax_stmt Γ δ R%A J%A T%A C%A P%A s Q%A)
  (at level 74, δ at next level, R at next level,
   J at next level, T at next level, C at next level,
   format "Γ \  δ \  R \  J \  T \  C  ⊨ₛ  '[' {{  P  } } '/'  s  '/' {{  Q  } } ']'") : C_scope.
Notation "Γ \ δ ⊨ₛ {{ P } } s {{ Q } }" :=
  (ax_stmt_top Γ δ P%A s%S Q%A)
  (at level 74, δ at next level,
   format "Γ \  δ  ⊨ₛ  '[' {{  P  } } '/'  s  '/' {{  Q  } } ']'") : C_scope.

(** ** The Hoare judgment for expressions *)
(** The interpretation of the expression judgment is defined similarly as the
interpretation of the judgment for statements. At the start, we require both
the expression and the memory to be lock free. In the end, the locks in the
memory should exactly match the annotated locations in the final expression
that remain to be unlocked. The latter is important, as an unlock operation at
a sequence point thereby corresponds to unlocking everything. *)
Inductive ax_expr_frame (K : iType) : iType :=
  InExpr (mf mA : mem K) | InFun (mf : mem K).
Arguments InExpr {_} _ _.
Arguments InFun {_} _.

Inductive ax_expr_cond_frame `{Env K}
     (ρ : stack K) (A : assert K) (Γ : env K)
     (Δ : memenv K) (δ : funenv K) (k : ctx K)
     (n : nat) (φ : focus K) (m m' : mem K) : ax_expr_frame K → Prop :=
  | ax_frame_in_expr mA mf :
     m' = m ∪ mf ∪ mA → ✓{Γ,Δ} mf → ✓{Γ,Δ} mA →
     ## [m; mf; mA] → k = [] → cmap_erased mA → mem_locks mA = ∅ →
     assert_holds A Γ Δ δ ρ n mA →
     ax_expr_cond_frame ρ A Γ Δ δ k n φ m m' (InExpr mf mA)
  | ax_frame_in_fun mf :
     m' = m ∪ mf → ✓{Γ,Δ} mf →
     ## [m; mf] → k ≠ [] →
     ax_expr_cond_frame ρ A Γ Δ δ k n φ m m' (InFun mf).
Inductive ax_expr_cond_unframe `{Env K}
     (ρ : stack K) (A : assert K) (Γ : env K)
     (Δ : memenv K) (δ : funenv K) (k : ctx K)
     (n : nat) (φ : focus K) (m m' : mem K) : ax_expr_frame K → Prop :=
  | ax_unframe_expr_to_expr mA mf :
     m' = m ∪ mf ∪ mA → ## [m; mf; mA] → k = [] →
     ax_expr_cond_unframe ρ A Γ Δ δ k n φ m m' (InExpr mf mA)
  | ax_unframe_fun_to_expr mA mf :
     m' = m ∪ mf ∪ mA → ## [m; mf; mA] → k = [] →
     cmap_erased mA → mem_locks mA = ∅ →
     assert_holds A Γ Δ δ ρ n mA → 
     ax_expr_cond_unframe ρ A Γ Δ δ k n φ m m' (InFun mf)
  | ax_unframe_expr_to_fun m'' mA mf :
     m = m'' ∪ mA → m' = m'' ∪ mf ∪ mA → ## [m''; mf; mA] → k ≠ [] →
     ax_expr_cond_unframe ρ A Γ Δ δ k n φ m m' (InExpr mf mA)
  | ax_unframe_fun_to_fun mf :
     m' = m ∪ mf → ## [m; mf] → k ≠ [] →
     ax_expr_cond_unframe ρ A Γ Δ δ k n φ m m' (InFun mf).
Program Definition ax_expr_cond `{EnvSpec K} (ρ : stack K)
    (A : assert K) : ax_frame_cond K (ax_expr_frame K) := {|
  frame := ax_expr_cond_frame ρ A;
  unframe := ax_expr_cond_unframe ρ A
|}.
Next Obligation.
  intros ??? ρ A Γ Δ δ k n φ m m' ??;
    destruct 1; subst; auto using cmap_union_valid_2.
Qed.
Next Obligation.
  intros ??? ρ A Γ Δ δ k n φ m m' ??; destruct 1; subst;
    rewrite ?cmap_union_valid; intuition.
Qed.

Definition ax_expr_invariant `{Env K} (A : assert K)
    (Γ : env K) (Δ : memenv K) (δ : funenv K)
    (ρ : stack K) (n : nat) (m : mem K) := ∃ mA,
  ## [mA; m] ∧ ✓{Γ,Δ} mA ∧ cmap_erased mA ∧ mem_locks mA = ∅ ∧
  assert_holds A Γ Δ δ ρ n mA.
Inductive ax_expr_post' `{Env K} (Q : lrval K → assert K)
    (τlr : lrtype K) (Γ : env K) (Δ : memenv K)
    (δ : funenv K) (ρ : stack K) (n : nat) : focus K → mem K → Prop :=
  mk_ax_expr_post ν Ω m :
    (Γ,Δ) ⊢ ν : τlr →
    mem_locks m = Ω →
    assert_holds (Q ν) Γ Δ δ ρ n (cmap_erase m) →
    ax_expr_post' Q τlr Γ Δ δ ρ n (Expr (%#{Ω} ν)) m.
Program Definition ax_expr_post `{EnvSpec K}
    (Q : lrval K → assert K) (τlr : lrtype K) : ax_assert K := {|
  ax_assert_holds := ax_expr_post' Q τlr
|}.
Next Obligation.
  intros ??? Q τlr Γ1 Γ2 Δ1 Δ2 δ1 δ2 ρ n φ m ?????; destruct 1; constructor;
    eauto using assert_weaken, cmap_erase_valid, lrval_typed_weaken.
Qed.
Next Obligation.
  intros ??? Q τlr Γ Δ δ ρ n φ m m' [d m'' ???] [? p]; inv_rcstep.
Qed.
Definition ax_expr `{EnvSpec K} (Γ : env K) (δ : funenv K) (A P : assert K)
    (e : expr K) (Q : lrval K → assert K) : Prop := ∀ Γ' Δ δ' n ρ m τlr,
  ✓ Γ' → Γ ⊆ Γ' → δ ⊆ δ' →
  ✓{Γ',Δ} δ' →
  ✓{Γ',Δ} m →
  mem_locks m = ∅ →
  (Γ',Δ,ρ.*2) ⊢ e : τlr →
  locks e = ∅ →
  ✓{Δ}* ρ →
  ax_expr_invariant A Γ' Δ δ' ρ n m →
  assert_holds P Γ' Δ δ' ρ n (cmap_erase m) →
  ax_graph (ax_expr_cond ρ A) (ax_expr_post Q τlr) Γ' δ' Δ ρ n [] (Expr e) m.
#[global] Instance: Params (@ax_expr) 5 := {}.
Notation "Γ \ δ \ A ⊨ₑ {{ P } } e {{ Q } }" :=
  (ax_expr Γ δ A%A P%A e Q%A)
  (at level 74, δ at next level, A at next level,
  format "Γ \  δ \  A  ⊨ₑ  '[' {{  P  } } '/'  e  '/' {{  Q  } } ']'") : C_scope.

(** ** Function specifications *)
Inductive fassert (K : Type) `{Env K} := FAssert {
  fcommon : Type;
  fpre : fcommon → list (val K) → assert K;
  fpost : fcommon → list (val K) → val K → assert K;
  fpre_stack_indep c vs : StackIndep (fpre c vs);
  fpost_stack_indep c vs v : StackIndep (fpost c vs v)
}.
Arguments fcommon {_ _} _.
Arguments fpre {_ _} _ _ _.
Arguments fpost {_ _} _ _ _ _.
#[global] Existing Instance fpre_stack_indep.
#[global] Existing Instance fpost_stack_indep.

Inductive ax_fun_post' `{Env K}
    (f : funname) (τ : type K) (P : val K → assert K)
    (Γ : env K) (Δ : memenv K) (δ : funenv K)
    (ρ : stack K) (n : nat) : focus K → mem K → Prop :=
  mk_ax_fun_post v m :
    (Γ,Δ) ⊢ v : τ →
    mem_locks m = ∅ →
    assert_holds (P v) Γ Δ δ ρ n (cmap_erase m) →
    ax_fun_post' f τ P Γ Δ δ ρ n (Return f v) m.
Program Definition ax_fun_post `{EnvSpec K} (f : funname) (τ : type K)
    (P : val K → assert K) : ax_assert K := {|
  ax_assert_holds := ax_fun_post' f τ P 
|}.
Next Obligation.
  intros ??? f τ Pf Γ1 Γ2 Δ1 Δ2 δ1 δ2 ρ n n' φ ?????; destruct 1 as [v m];
    constructor; eauto using assert_weaken, cmap_erase_valid, val_typed_weaken.
Qed.
Next Obligation.
  intros ??? f τ Pf Γ Δ δ n ρ φ m m' [v m'' ??] [? p]; inv_rcstep.
Qed.
Program Definition assert_fun `{EnvSpec K} (f : funname)
    (Pf : fassert K) (τs : list (type K)) (τ : type K) : assert K := {|
  assert_holds Γ Δ δ ρ n m :=
    m = ∅ ∧
    Γ !! f = Some (τs,τ) ∧
    ∀ Γ' Δ' δ' n' c vs m',
      Γ ⊆ Γ' → ✓ Γ' → Δ ⇒ₘ Δ' → δ ⊆ δ' → n' ≤ n →
      ✓{Γ',Δ'} δ' →
      ✓{Γ',Δ'} m' →
      mem_locks m' = ∅ →
      (Γ',Δ') ⊢* vs :* τs →
      assert_holds (fpre Pf c vs) Γ' Δ' δ' [] n' (cmap_erase m') →
      ax_graph ax_disjoint_cond
        (ax_fun_post f τ (fpost Pf c vs)) Γ' δ' Δ' [] n' [] (Call f vs) m'
|}.
Next Obligation. naive_solver eauto using lookup_fun_weaken. Qed.

Section axiomatic.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types Δ : memenv K.
Implicit Types δ : funenv K.
Implicit Types m : mem K.
Implicit Types e : expr K.
Implicit Types s : stmt K.

Hint Immediate cmap_valid_memenv_valid: core.
Hint Resolve cmap_empty_valid cmap_erased_empty mem_locks_empty: core.
Hint Resolve cmap_union_valid_2 cmap_erase_valid: core.

#[global] Instance directed_pack_proper `{!@Equivalence A R} :
  Proper (R ==> R ==> pointwise_relation _ R ==> pointwise_relation _ R ==>
    pointwise_relation _ R ==> pointwise_relation _ R ==>
    pointwise_relation _ R) (@directed_pack K A).
Proof. intros ?????????????????? []; simplify_equality'; auto. Qed.
Lemma directed_fmap_spec {A B} (f : A → B) (P : direction K → A) d :
  (@fmap _ (@directed_fmap K) _ _ f P) d = f (P d).
Proof. by destruct d. Qed.
#[global] Instance ax_stmt_packed_proper Γ δ : Proper
  (pointwise_relation _ (≡{Γ,δ}) ==> (=) ==> iff) (ax_stmt_packed Γ δ).
Proof.
  cut (Proper (pointwise_relation _ (≡{Γ,δ}) ==> (=) ==> impl)
              (ax_stmt_packed Γ δ)).
  { intros help. by split; apply help. }
  intros Pd Qd HPQ ?? -> Hax ??????????????????.
  eapply ax_weaken with ax_disjoint_cond (ax_stmt_post Pd _ _) n; eauto.
  { eapply Hax, HPQ; eauto. }
  destruct 2; constructor; auto.
  eapply HPQ; eauto using indexes_valid_weaken, funenv_valid_weaken.
Qed.
Lemma ax_stmt_top_unfold Γ δ P (Q : val _ → assert _) s :
  Γ\ δ ⊨ₛ {{ P }} s {{ Q }} ↔
  Γ\ δ\ Q\ (λ _, False)\ (λ _, False)\ (λ _, False) ⊨ₛ {{ P }} s {{ Q voidV }}.
Proof. done. Qed.
#[global] Instance ax_stmt_proper Γ δ :
  Proper (pointwise_relation _ (≡{Γ,δ}) ==> pointwise_relation _ (≡{Γ,δ}) ==>
     pointwise_relation _ (≡{Γ,δ}) ==> pointwise_relation _ (≡{Γ,δ}) ==>
     (≡{Γ,δ}) ==> (=) ==> (≡{Γ,δ}) ==> iff) (ax_stmt Γ δ).
Proof.
  intros ?? HR ?? HJ ?? HT ?? HC ?? HP ?? -> ?? HQ.
  unfold ax_stmt. by rewrite HR, HJ, HT, HC, HP, HQ.
Qed.
#[global] Instance ax_stmt_top_proper Γ δ :
  Proper ((≡{Γ,δ}) ==> (=) ==> pointwise_relation _ (≡{Γ,δ}) ==> iff)
         (ax_stmt_top Γ δ).
Proof.
  intros ?? HP ?? -> ?? HQ.
  unfold ax_stmt_top, dassert_pack_top. by rewrite HP, HQ.
Qed.

Lemma ax_expr_invariant_emp Γ Δ δ ρ n m :
  ✓{Γ,Δ} m → ax_expr_invariant emp Γ Δ δ ρ n m.
Proof. by eexists ∅; split_and ?; eauto. Qed.
Hint Resolve ax_expr_invariant_emp: core.
Lemma ax_expr_invariant_weaken Γ Δ δ A ρ n1 n2 m1 m2 :
  ✓ Γ → ✓{Δ}* ρ →
  ax_expr_invariant A Γ Δ δ ρ n1 m2 → m1 ⊆ m2 → n2 ≤ n1 →
  ax_expr_invariant A Γ Δ δ ρ n2 m1.
Proof.
  intros ?? (mA&?&?&?&?&?) Hm12.
  exists mA; split_and ?; eauto using assert_weaken.
  by rewrite <-(sep_subseteq_disjoint_le m1) by eauto.
Qed.
Lemma ax_disjoint_expr_compose_diagram Γ ρ A Ek :
  ax_compose_diagram ax_disjoint_cond (ax_expr_cond ρ A) Γ [Ek].
Proof.
  intros Δ δ k n φ a m m' ??; simpl.
  destruct 1; subst; [discriminate_list_equality|].
  exists mf; split_and ?; auto; intros Δ' k' φ' m2 m2' ?? [-> ?].
  constructor; trivial; intro; discriminate_list_equality.
Qed.
Lemma ax_expr_disjoint_compose_diagram Γ ρ k :
  ax_compose_diagram (ax_expr_cond ρ emp%A) ax_disjoint_cond Γ k.
Proof.
  intros Δ δ k' φ n m m' mf ?? (->&?&?); simpl.
  destruct (decide (k' = [])) as [->|].
  * exists (InExpr mf ∅). split.
    { by constructor; rewrite ?sep_right_id by auto;
        eauto using mem_locks_empty, cmap_empty_valid, cmap_erased_empty. }
    intros Δ' k'' φ' m2 m2' ??; inversion 1; subst;
      rewrite ?sep_right_id by auto; auto.
  * exists (InFun mf); split; [by constructor|].
    intros Δ' k'' φ' m2 m2' ??; inversion 1 as [|mA mf' ????? [??]| | ]; subst;
      rewrite ?sep_right_id by auto; auto.
Qed.
Lemma ax_expr_cond_frame_diagram_simple Γ ρ B mf :
  ax_frame_diagram (ax_expr_cond ρ B) (ax_expr_cond ρ B) Γ mf.
Proof.
  intros Δ δ k φ n m m' ??; destruct 4 as [mA mf'|mf']; subst.
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
#[global] Instance ax_expr_proper Γ δ :
  Proper ((≡{Γ,δ}) ==> (≡{Γ,δ}) ==> (=) ==>
          pointwise_relation _ (≡{Γ,δ}) ==> iff) (ax_expr Γ δ).
Proof.
  cut (Proper ((≡{Γ,δ}) ==> (≡{Γ,δ}) ==> (=) ==>
    pointwise_relation _ (≡{Γ,δ}) ==> impl) (ax_expr Γ δ)).
  { intros help. by split; apply help. }
  intros A1 A2 HA P1 P2 HP ?? -> Q1 Q2 HQ Hax ???????????????? (?&?&?&?&?&?) ?.
  eapply ax_weaken with (ax_expr_cond ρ A1) (ax_expr_post Q1 τlr) n; eauto.
  * apply Hax, HP; eauto.
    econstructor; split_and ?; eauto. apply HA; eauto.
  * destruct 2; constructor; auto.
    apply HA; eauto using indexes_valid_weaken, funenv_valid_weaken.
  * destruct 2; subst; simplify_mem_disjoint_hyps; econstructor; first
     [by eauto|apply HA;eauto using indexes_valid_weaken, funenv_valid_weaken].
  * destruct 2; constructor; auto.
    apply HQ; eauto using indexes_valid_weaken, funenv_valid_weaken.
Qed.
End axiomatic.
