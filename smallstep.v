(* Copyright (c) 2012, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This files defines a small step operational semantics for our language. It
is a binary relation on execution states, and computation of our language is
defined as the reflexive transitive closure of this relation. This file also
defines tactics to automatically perform and invert reduction steps, and it
proves some important properties. *)
Require Export state ars.

(** * Small step reduction *)
(** Small step reduction works by moving the focus on the substatement that is
being executed. Each step the focused statement is executed, after which the
focus is moved to the next statement or the direction is changed. *)
Reserved Notation "δ ⊢ S1 '⇒s' S2" (at level 80, S2 at level 70).

Reserved Infix "⇒" (at level 70).
Inductive cstep (δ : funenv) : relation state :=
  | cstep_in_assign k e1 a e2 v m :
     ⟦ e1 ⟧ (get_stack k) m = Some (ptr a)%V →
     ⟦ e2 ⟧ (get_stack k) m = Some v →
     is_writable m a →
     δ ⊢ State k (Stmt ↘ (e1 ::= e2)) m
      ⇒s State k (Stmt ↗ (e1 ::= e2)) (<[a:=v]>m)
  | cstep_in_call k f e es vs m :
     Forall2 (λ e v, ⟦ e ⟧ (get_stack k) m = Some v) es vs →
     δ ⊢ State k (Stmt ↘ (SCall e f es)) m
      ⇒s State (CCall e f es :: k) (Call f vs) m
  | cstep_in_skip k m :
     δ ⊢ State k (Stmt ↘ (skip)) m
      ⇒s State k (Stmt ↗ (skip)) m
  | cstep_goto l k m :
     δ ⊢ State k (Stmt ↘ (goto l)) m
      ⇒s State k (Stmt (↷ l) (goto l)) m
  | cstep_in_return_None k m :
     δ ⊢ State k (Stmt ↘ (ret None)) m
      ⇒s State k (Stmt (⇈ None) (ret None)) m
  | cstep_in_return_Some k e v m :
     ⟦ e ⟧ (get_stack k) m = Some v →
     δ ⊢ State k (Stmt ↘ (ret (Some e))) m
      ⇒s State k (Stmt (⇈ (Some v)) (ret (Some e))) m

  | cstep_in_block k b v s m :
     is_free m b →
     δ ⊢ State k (Stmt ↘ (block s)) m
      ⇒s State (CBlock b :: k) (Stmt ↘ s) (<[b:=v]>m)
  | cstep_in_comp k s1 s2 m :
     δ ⊢ State k (Stmt ↘ (s1 ;; s2)) m
      ⇒s State (CItem (□ ;; s2) :: k) (Stmt ↘ s1) m
  | cstep_in_while1 k e s v m :
     ⟦ e ⟧ (get_stack k) m = Some v →
     value_true v →
     δ ⊢ State k (Stmt ↘ (while (e) s)) m
      ⇒s State (CItem (while (e) □) :: k) (Stmt ↘ s) m
  | cstep_in_while2 k e s v m :
     ⟦ e ⟧ (get_stack k) m = Some v →
     value_false v →
     δ ⊢ State k (Stmt ↘ (while (e) s)) m
      ⇒s State k (Stmt ↗ (while (e) s)) m
  | cstep_in_if1 k e s1 s2 v m :
     ⟦ e ⟧ (get_stack k) m = Some v →
     value_true v →
     δ ⊢ State k (Stmt ↘ (IF e then s1 else s2)) m
      ⇒s State (CItem (IF e then □ else s2) :: k) (Stmt ↘ s1) m
  | cstep_in_if2 k e s1 s2 v m :
     ⟦ e ⟧ (get_stack k) m = Some v →
     value_false v →
     δ ⊢ State k (Stmt ↘ (IF e then s1 else s2)) m
      ⇒s State (CItem (IF e then s1 else □) :: k) (Stmt ↘ s2) m
  | cstep_in_label k l s m :
     δ ⊢ State k (Stmt ↘ (l :; s)) m
      ⇒s State (CItem (l :; □) :: k) (Stmt ↘ s) m

  | cstep_out_block k b s m :
     δ ⊢ State (CBlock b :: k) (Stmt ↗ s) m
      ⇒s State k (Stmt ↗ (block s)) (delete b m)
  | cstep_out_comp1 k s1 s2 m :
     δ ⊢ State (CItem (□ ;; s2) :: k) (Stmt ↗ s1) m
      ⇒s State (CItem (s1 ;; □) :: k) (Stmt ↘ s2) m
  | cstep_out_comp2 k s1 s2 m :
     δ ⊢ State (CItem (s1 ;; □) :: k) (Stmt ↗ s2) m
      ⇒s State k (Stmt ↗ (s1 ;; s2)) m
  | cstep_out_loop k e s m :
     δ ⊢ State (CItem (while (e) □) :: k) (Stmt ↗ s) m
      ⇒s State k (Stmt ↘ (while (e) s)) m
  | cstep_out_if1 k e s1 s2 m :
     δ ⊢ State (CItem (IF e then □ else s2) :: k) (Stmt ↗ s1) m
      ⇒s State k (Stmt ↗ (IF e then s1 else s2)) m
  | cstep_out_if2 k e s1 s2 m :
     δ ⊢ State (CItem (IF e then s1 else □) :: k) (Stmt ↗ s2) m
      ⇒s State k (Stmt ↗ (IF e then s1 else s2)) m
  | cstep_out_label k s l m :
     δ ⊢ State (CItem (l :; □) :: k) (Stmt ↗ s) m
      ⇒s State k (Stmt ↗ (l :; s)) m

  | cstep_alloc_params k f s m1 bs vs m2 :
     δ !! f = Some s →
     alloc_params m1 bs vs m2 →
     δ ⊢ State k (Call f vs) m1
      ⇒s State (CParams bs :: k) (Stmt ↘ s) m2
  | cstep_free_params k s m bs :
     δ ⊢ State (CParams bs :: k) (Stmt ↗ s) m
      ⇒s State k (Return None) (delete_list bs m)
  | cstep_free_params_top k v s m bs :
     δ ⊢ State (CParams bs :: k) (Stmt (⇈ v) s) m
      ⇒s State k (Return v) (delete_list bs m)

  | cstep_return_None k v f es m :
     δ ⊢ State (CCall None f es :: k) (Return v) m
      ⇒s State k (Stmt ↗ (call f @ es)) m
  | cstep_return_Some k v e a f es m :
     ⟦ e ⟧ (get_stack k) m = Some (ptr a)%V →
     is_writable m a →
     δ ⊢ State (CCall (Some e) f es :: k) (Return (Some v)) m
      ⇒s State k (Stmt ↗ (e ::= call f @ es)) (<[a:=v]>m)

  | cstep_top_block v k b s m :
     δ ⊢ State (CBlock b :: k) (Stmt (⇈ v) s) m
      ⇒s State k (Stmt (⇈ v) (block s)) (delete b m)
  | cstep_top_item v E k s m :
     δ ⊢ State (CItem E :: k) (Stmt (⇈ v) s) m
      ⇒s State k (Stmt (⇈ v) (subst E s)) m

  | cstep_label_here l k s m :
     δ ⊢ State k (Stmt (↷ l) (l :; s)) m
      ⇒s State (CItem (l :; □) :: k) (Stmt ↘ s) m
  | cstep_label_block_down l k b v s m :
     l ∈ labels s →
     is_free m b →
     δ ⊢ State k (Stmt (↷ l) (block s)) m
      ⇒s State (CBlock b :: k) (Stmt (↷ l) s) (<[b:=v]>m)
  | cstep_label_block_up l k b s m : 
     (**i Not [l ∈ labels k] so as to avoid it going back and forth between 
     double occurrences of labels. *)
     l ∉ labels s →
     δ ⊢ State (CBlock b :: k) (Stmt (↷ l) s) m
      ⇒s State k (Stmt (↷l) (block s)) (delete b m)
  | cstep_label_down l E k s m :
     l ∈ labels s →
     δ ⊢ State k (Stmt (↷ l) (subst E s)) m
      ⇒s State (CItem E :: k) (Stmt (↷ l) s) m
  | cstep_label_up l E k s m :
     l ∉ labels s →
     δ ⊢ State (CItem E :: k) (Stmt (↷ l) s) m
      ⇒s State k (Stmt (↷ l) (subst E s)) m
where "δ ⊢ S1 ⇒s S2" := (cstep δ S1%S S2%S) : C_scope.
Notation "( δ ⇒s)" := (cstep δ) (only parsing) : C_scope.

(** The reflexive transitive closure. *)
Notation "δ ⊢ S1 ⇒s* S2" := (rtc (δ ⇒s) S1 S2)
  (at level 80, S2 at level 70) : C_scope.
Notation "( δ ⇒s*)" := (rtc (δ ⇒s)) (only parsing) : C_scope.

(** Reduction paths of bounded length. *)
Notation "δ ⊢ S1 ⇒s^ n S2" := (bsteps (δ ⇒s) n S1 S2)
  (at level 80, n at level 1, S2 at level 70) : C_scope.
Notation "( δ ⇒s^ n )" := (bsteps (δ ⇒s) n) (only parsing) : C_scope.

(** * Restricting small step reduction *)
(** Reduction in our language consists of moving the focus on the substatement
that is being executed. Often (and in particular for the soundness proofs of
our axiomatic semantics) we want to restrict this movement: we want the focus
to remain below a certain point. A reduction [δ ⊢ S1 ⇒s{ k } S2] is only
allowed if [S2]'s program context is below [k]. *)
Definition cstep_in_ctx δ k : relation state := λ S1 S2,
  δ ⊢ S1 ⇒s S2 ∧ suffix_of k (SCtx S2).

Notation "δ ⊢ S1 ⇒s{ k } S2" := (cstep_in_ctx δ k S1 S2)
  (at level 80, S2 at level 70, k at level 80,
  format "δ  ⊢  S1  '⇒s{' k '}'  S2") : C_scope.
Notation "( δ ⇒s{ k })" := (cstep_in_ctx δ k) (only parsing) : C_scope.
Notation "δ ⊢ S1 ⇒s{ k }* S2" := (rtc (δ ⇒s{k}) S1 S2)
  (at level 80, S2 at level 70, k at level 80,
  format "δ  ⊢  S1  '⇒s{' k '}*'  S2") : C_scope.
Notation "( δ  ⇒s{ k }*)" := (rtc (δ ⇒s{k})) (only parsing) : C_scope.
Notation "δ ⊢ S1 ⇒s{ k }^ n S2" := (bsteps (δ ⇒s{k}) n S1 S2)
  (at level 80, S2 at level 70, k at level 80, n at level 1,
  format "δ  ⊢  S1  '⇒s{' k '}^' n  S2") : C_scope.
Notation "( δ ⇒s{ k }^ n )" := (bsteps (δ ⇒s{k}) n) (only parsing) : C_scope.

Instance cstep_subrel_suffix_of δ k1 k2 :
  PropHolds (suffix_of k1 k2) → subrelation (δ ⇒s{k2}) (δ ⇒s{k1}).
Proof. intros ? S1 S2 [??]. split. done. by transitivity k2. Qed.
Instance cstep_subrel δ k : subrelation (δ ⇒s{k}) (δ ⇒s).
Proof. firstorder. Qed.
Instance cstep_subrel_nil δ : subrelation (δ ⇒s) (δ ⇒s{ [] }).
Proof. intros S1 S2 ?. split. done. solve_suffix_of. Qed.

(** * Tactics *)
(** We implement some tactics to perform and to invert reduction steps. We
define a hint database [cstep] that is used by these tactics. *)
Hint Resolve expr_eval_weaken_mem expr_eval_weaken_stack : cstep.
Hint Resolve finmap_subseteq_union_l finmap_subseteq_union_r : cstep.
Hint Resolve Forall2_impl : cstep.
Hint Extern 0 (is_writable _ _) => red; eauto with mem : cstep.

(** The small step semantics is non-determistic on entering a block or calling
a function: variables are given a memory cell that has an unspecified free
index and is initialized with an unspecified value. The following lemmas
are deterministic variants that will be included in the [cstep] hint database
to automatically perform reduction steps. *)
Lemma cstep_in_block_fresh δ k s m :
  let b := fresh_index m in
  δ ⊢ State k (Stmt ↘ (block s)) m
   ⇒s State (CBlock b :: k) (Stmt ↘ s) (<[b:=int 0]>m)%V.
Proof. constructor. apply is_free_fresh_index. Qed.

Lemma cstep_label_block_down_fresh δ l k s m :
  l ∈ labels s →
  let b := fresh_index m in
  δ ⊢ State k (Stmt (↷ l) (block s)) m
   ⇒s State (CBlock b :: k) (Stmt (↷ l) s) (<[b:=int 0]>m)%V.
Proof. constructor. done. apply is_free_fresh_index. Qed.

Lemma cstep_alloc_params_fresh δ k f s m vs :
  δ !! f = Some s →
  let bs := fresh_indexes m (length vs) in
  δ ⊢ State k (Call f vs) m
   ⇒s State (CParams bs :: k) (Stmt ↘ s) (insert_list (zip bs vs) m).
Proof.
  constructor. done. apply alloc_params_insert_list.
  intuition auto with mem.
  apply same_length_length. by rewrite fresh_indexes_length.
Qed.

Hint Resolve cstep_in_block_fresh
  cstep_label_block_down_fresh cstep_alloc_params_fresh : cstep.

(** The [quote_stmt s] tactic yields a list of possible ways to quote [s]
using [subst] for the top-level constructor. *)
Ltac quote_stmt s :=
  match s with
  | ?s1 ;; ?s2 => constr:[subst (s1 ;; □) s2; subst (□ ;; s2) s1]
  | ?l :; ?s => constr:[subst (l :; □) s]
  | while (?e) ?s => constr:[subst (while (e) □) s]
  | IF ?e then ?s1 else ?s2 =>
    constr:[subst (IF e then s1 else □) s2; subst (IF e then □ else s2) s1]
  end.

(** The [do_cstep] tactic solves goals of the shape [δ ⊢ S1 ⇒s S2] by applying
a reduction rule or by using the [cstep] hint database. Goals of the shape
[δ ⊢ S1 ⇒s{k} S2] are solved similarly but using [solve_suffix_of] to solve the
side condition [suffix_of k (SCtx S2)]. This tactic either fails or proves
the goal. *)
Ltac do_cstep :=
  match goal with
  | |- ?δ ⊢ State ?k (Stmt ?d ?s) ?m ⇒s ?S => iter
    (fun s' => change (δ ⊢ State k (Stmt d s') m ⇒s S); do_cstep)
    (quote_stmt s)
  | |- _ ⊢ _ ⇒s _ => econstructor (solve [intuition eauto with cstep])
  | |- _ ⊢ _ ⇒s{_} _ => split; [ do_cstep | simpl; solve_suffix_of ]
  | |- _ => solve [intuition eauto with cstep]
  end.

(** The [do_csteps] tactic extends the previous tactic to the reflexive
transitive closure and to reductions of a bounded length. *)
Ltac do_csteps :=
  match goal with
  | |- _ ⊢ _ ⇒s* _ => apply rtc_refl
  | |- _ ⊢ _ ⇒s* _ => eapply rtc_l; [do_cstep | do_csteps]
  | |- _ ⊢ _ ⇒s{_}* _ => apply rtc_refl
  | |- _ ⊢ _ ⇒s{_}* _ => eapply rtc_l; [do_cstep | do_csteps]
  | |- _ ⊢ _ ⇒s^_ _ => apply bsteps_refl
  | |- _ ⊢ _ ⇒s^(S _) _ => eapply bsteps_l; [do_cstep | do_csteps]
  | |- _ ⊢ _ ⇒s{_}^(S _) _ => apply bsteps_S; do_csteps
  | |- _ ⊢ _ ⇒s{_}^_ _ => apply bsteps_refl
  | |- _ ⊢ _ ⇒s{_}^(S _) _ => eapply bsteps_l; [do_cstep | do_csteps]
  | |- _ ⊢ _ ⇒s{_}^(S _) _ => apply bsteps_S; do_csteps
  | |- _ => solve [intuition eauto with cstep]
  end.

(** The [solve_cred] tactic solves goals of the shape [red (δ⇒s) S] and
[red (δ⇒s{k}) S] by performing case distinctions on [S] and using the
[do_cstep] tactic to perform the actual step. *)
Ltac solve_cred :=
  repeat match goal with
  | H : down _ _ |- _ => progress simpl in H
  | H : up _ _ |- _ => progress simpl in H
  | |- red (_⇒s) (State _ (Stmt ?d _) _) =>
    is_var d; destruct d; try contradiction
  | |- red (_⇒s{_}) (State _ (Stmt ?d _) _) =>
    is_var d; destruct d; try contradiction
  | H : ?l ∈ _ |- red (_⇒s) (State _ (Stmt (↷ ?l) _) _) =>
    progress decompose_elem_of H
  | H : ?l ∈ _ |- red (_⇒s{_}) (State _ (Stmt (↷ ?l) _) _) =>
    progress decompose_elem_of H
  end;
  match goal with
  | H : red (_ ⇒s{_}) ?S |- red (_ ⇒s{_}) ?S =>
    by apply (red_subrel _ _ _ _ H)
  | |- red (_⇒s) _ => eexists; do_cstep
  | |- red (_⇒s{_}) _ => eexists; do_cstep
  | |- _ => solve [intuition eauto with cstep]
  end.

Ltac solve_cnf :=
  match goal with
  | H : nf (_ ⇒s) _ |- _ => destruct H; solve_cred
  | H : nf (_ ⇒s{_}) _ |- _ => destruct H; solve_cred
  end.

Ltac inv_cstep H :=
  match type of H with
  | _ ⊢ _ ⇒s _ =>
    inversion H; clear H;
    simplify_stmt_equality; try contradiction
  | _ ⊢ _ ⇒s{_} _ =>
    let H1 := fresh in
    let H2 := fresh in
    destruct H as [H1 H2];
    inv_cstep H1;
    simpl in H2; simplify_suffix_of
  end.
Tactic Notation "inv_cstep" hyp(H) := inv_cstep H.
Tactic Notation "inv_cstep" :=
  match goal with
  | H : _ ⊢ _ ⇒s _ |- _ => inv_cstep H
  | H : _ ⊢ _ ⇒s{_} _ |- _ => inv_cstep H
  end.

Tactic Notation "inv_csteps" hyp(H) "as" simple_intropattern(H2) :=
  let H' := fresh in rename H into H';
  inversion H' as H2; clear H'; subst.
Tactic Notation "inv_csteps" hyp(H) := inv_csteps H as [].

Tactic Notation "last_cstep" hyp(H) :=
  inv_csteps H; [| solve [inv_cstep]].

(** * Theorems *)
Section smallstep_properties.
Context (δ : funenv).
(** ** Preservation of statements *)
(** We prove that the traversal performed by the reduction semantics is sound.
That means, if [δ ⊢ State k (Stmt d1 s1) m1 ⇒s{k}* State k (Stmt d2 s2) m2],
then [s1 = s2]. Due to the precense of function calls, it is not clear how to
prove this directly. We therfore first prove that reduction preserves well
formed program contexts, and use the theorem [ctx_wf_unique] to obtain the
required result. *)
Lemma cstep_preserves_wf k s S1 S2 :
  δ ⊢ S1 ⇒s{k} S2 →
  ctx_wf δ k s (SCtx S1) (SFoc S1) →
  ctx_wf δ k s (SCtx S2) (SFoc S2).
Proof.
  intros p.
  inv_cstep; try solve [inversion 1; subst;
      first [ assumption || solve_suffix_of || econstructor; eauto]].
  * inversion 1; subst. solve_suffix_of.
    match goal with
    | H : ctx_wf _ _ _ _ (Call_ _) |- _ => inversion H; subst
    end. solve_suffix_of. done.
  * inversion 1; subst. solve_suffix_of.
    match goal with
    | H : ctx_wf _ _ _ _ (Call_ _) |- _ => inversion H; subst
    end. solve_suffix_of. done.
Qed.

Lemma cstep_rtc_preserves_wf k s S1 S2 :
  δ ⊢ S1 ⇒s{k}* S2 →
  ctx_wf δ k s (SCtx S1) (SFoc S1) →
  ctx_wf δ k s (SCtx S2) (SFoc S2).
Proof. induction 1; eauto using cstep_preserves_wf. Qed.

Lemma cteps_rtc_preserves_stmt k d1 s1 m1 d2 s2 m2 :
  δ ⊢ State k (Stmt d1 s1) m1 ⇒s{k}* State k (Stmt d2 s2) m2 →
  s1 = s2.
Proof.
  pose proof (ctx_wf_start δ k (Stmt d1 s1)).
  intros p. apply (ctx_wf_unique δ k (Stmt d1 s1) k). done.
  apply (cstep_rtc_preserves_wf k (Stmt d1 s1)) in p; intuition.
Qed.

Lemma cstep_bsteps_preserves_stmt n k d1 s1 m1 d2 s2 m2 :
  δ ⊢ State k (Stmt d1 s1) m1 ⇒s{k}^n State k (Stmt d2 s2) m2 →
  s1 = s2.
Proof. eauto using cteps_rtc_preserves_stmt, bsteps_rtc. Qed.

(** ** Cutting reduction paths *)
(** Given a reduction path, we can cut of the maximal prefix that is restricted
by a more restricted program context. The lemma [cstep_subctx_cut] will be an
important tool to prove the rules of our axiomatic semantics. *)
Lemma cstep_subctx_step_or_nf k S1 S2 :
  δ ⊢ S1 ⇒s S2 →
  suffix_of k (SCtx S1) →
  suffix_of k (SCtx S2) ∨ nf (δ⇒s{k}) S1.
Proof.
  intros. destruct (decide (suffix_of k (SCtx S2))).
  * tauto.
  * inv_cstep; simpl in *; try solve_suffix_of;
      right; intros [??]; inv_cstep; solve_stmt_elem_of.
Qed.

Lemma cstep_subctx_cut n l k S1 S3 :
    δ ⊢ S1 ⇒s{k}^n S3 →
    suffix_of (l ++ k) (SCtx S1) →
  δ ⊢ S1 ⇒s{l ++ k}^n S3
   ∨
  ∃ S2, δ ⊢ S1 ⇒s{l ++ k}^n S2
    ∧ nf (δ⇒s{l ++ k}) S2 ∧ δ ⊢ S2 ⇒s{k}^n S3.
Proof.
  intros p ?. induction p as [ n S1 | n S1 S2 S3 [p1 ?] p2].
  * left. by auto with ars.
  * destruct (cstep_subctx_step_or_nf (l ++ k) S1 S2); auto.
    + destruct IHp2 as [? | [S2' ?]]; auto.
      - left. do_csteps.
      - right. exists S2'. intuition; do_csteps.
    + right. exists S1. intuition; do_csteps.
Qed.
End smallstep_properties.
