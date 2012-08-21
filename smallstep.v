Require Export state.

Reserved Notation "δ ⊢ S1 '⇒s' S2" (at level 80, S2 at level 70).

Reserved Infix "⇒" (at level 70).
Inductive cstep (δ : fenv) : relation state :=
  | cstep_in_assign k e1 a e2 v m :
     ⟦ e1 ⟧ (get_stack k) m = Some a → 
     ⟦ e2 ⟧ (get_stack k) m = Some v →
     is_writable m a →
     δ ⊢ State k (Stmt In (e1 ::= e2)) m
      ⇒s State k (Stmt Out (e1 ::= e2)) (<[a:=v]>m)
  | cstep_in_call k f e es vs m :
     Forall2 (λ e v, ⟦ e ⟧ (get_stack k) m = Some v) es vs →
     δ ⊢ State k (Stmt In (call e f es)) m
      ⇒s State (CCall e f es :: k) (Call f vs) m
  | cstep_in_skip k m :
     δ ⊢ State k (Stmt In (skip)) m
      ⇒s State k (Stmt Out (skip)) m
  | cstep_goto l k m :
     δ ⊢ State k (Stmt In (goto l)) m
      ⇒s State k (Stmt (Jump l) (goto l)) m
  | cstep_in_return_None k m :
     δ ⊢ State k (Stmt In (ret None)) m
      ⇒s State k (Stmt (Top None) (ret None)) m
  | cstep_in_return_Some k e v m :
     ⟦ e ⟧ (get_stack k) m = Some v →
     δ ⊢ State k (Stmt In (ret (Some e))) m
      ⇒s State k (Stmt (Top (Some v)) (ret (Some e))) m

  | cstep_in_block k b v s m :
     is_free m b →
     δ ⊢ State k (Stmt In (block s)) m
      ⇒s State (CBlock b :: k) (Stmt In (s)) (<[b:=v]>m)
  | cstep_in_comp k s1 s2 m :
     δ ⊢ State k (Stmt In (s1 ;; s2)) m
      ⇒s State (CItem (□ ;; s2) :: k) (Stmt In (s1)) m
  | cstep_in_loop k s m :
     δ ⊢ State k (Stmt In (loop s)) m
      ⇒s State (CItem (loop □) :: k) (Stmt In (s)) m
  | cstep_in_if1 k e s1 s2 v m :
     ⟦ e ⟧ (get_stack k) m = Some v →
     val_true v →
     δ ⊢ State k (Stmt In (IF e then s1 else s2)) m
      ⇒s State (CItem (IF e then □ else s2) :: k) (Stmt In (s1)) m
  | cstep_in_if2 k e s1 s2 v m :
     ⟦ e ⟧ (get_stack k) m = Some v →
     val_false v →
     δ ⊢ State k (Stmt In (IF e then s1 else s2)) m
      ⇒s State (CItem (IF e then s1 else □) :: k) (Stmt In (s2)) m
  | cstep_in_label k l s m :
     δ ⊢ State k (Stmt In (l :; s)) m
      ⇒s State (CItem (l :; □) :: k) (Stmt In (s)) m

  | cstep_out_block k b s m :
     δ ⊢ State (CBlock b :: k) (Stmt Out (s)) m
      ⇒s State k (Stmt Out (block s)) (delete b m)
  | cstep_out_comp1 k s1 s2 m :
     δ ⊢ State (CItem (□ ;; s2) :: k) (Stmt Out (s1)) m
      ⇒s State (CItem (s1 ;; □) :: k) (Stmt In (s2)) m
  | cstep_out_comp2 k s1 s2 m :
     δ ⊢ State (CItem (s1 ;; □) :: k) (Stmt Out (s2)) m
      ⇒s State k (Stmt Out (s1 ;; s2)) m
  | cstep_out_loop k s m :
     δ ⊢ State (CItem (loop □) :: k) (Stmt Out (s)) m
      ⇒s State k (Stmt In (loop s)) m
     (* not ... ⇒ (CItem (loop □) :: k) s m so as to force the
      loop to go out of the context *)
  | cstep_out_if1 k e s1 s2 m :
     δ ⊢ State (CItem (IF e then □ else s2) :: k) (Stmt Out (s1)) m
      ⇒s State k (Stmt Out (IF e then s1 else s2)) m
  | cstep_out_if2 k e s1 s2 m :
     δ ⊢ State (CItem (IF e then s1 else □) :: k) (Stmt Out (s2)) m
      ⇒s State k (Stmt Out (IF e then s1 else s2)) m
  | cstep_out_label k s l m :
     δ ⊢ State (CItem (l :; □) :: k) (Stmt Out (s)) m
      ⇒s State k (Stmt Out (l :; s)) m

  | cstep_alloc_params k f s m1 bs vs m2 :
     δ !! f = Some s →
     alloc_params m1 bs vs m2 →
     δ ⊢ State k (Call f vs) m1
      ⇒s State (CParams bs :: k) (Stmt In s) m2
  | cstep_free_params k s m bs :
     δ ⊢ State (CParams bs :: k) (Stmt Out s) m
      ⇒s State k (Return None) (delete_list bs m)
  | cstep_free_params_top k v s m bs :
     δ ⊢ State (CParams bs :: k) (Stmt (Top v) s) m
      ⇒s State k (Return v) (delete_list bs m)

  | cstep_return_None k v f es m :
     δ ⊢ State (CCall None f es :: k) (Return v) m
      ⇒s State k (Stmt Out (call None f es)) m
  | cstep_return_Some k v e a f es m :
     ⟦ e ⟧ (get_stack k) m = Some a →
     is_writable m a →
     δ ⊢ State (CCall (Some e) f es :: k) (Return (Some v)) m
      ⇒s State k (Stmt Out (call (Some e) f es)) (<[a:=v]>m)

  | cstep_top_block v k b s m :
     δ ⊢ State (CBlock b :: k) (Stmt (Top v) s) m
      ⇒s State k (Stmt (Top v) (block s)) (delete b m)
  | cstep_top_item v E k s m :
     δ ⊢ State (CItem E :: k) (Stmt (Top v) s) m
      ⇒s State k (Stmt (Top v) (subst E s)) m

  | cstep_label_here l k s m :
     δ ⊢ State k (Stmt (Jump l) (l :; s)) m
      ⇒s State (CItem (l :; □) :: k) (Stmt In (s)) m
  | cstep_label_block_down l k b v s m :
     l ∈ labels s →
     is_free m b →
     δ ⊢ State k (Stmt (Jump l) (block s)) m
      ⇒s State (CBlock b :: k) (Stmt (Jump l) s) (<[b:=v]>m)
  | cstep_label_block_up l k b s m :
     (* not l ∈ labels k so as to avoid it going back and forth
       between double occurences of labels *)
     l ∉ labels s →
     δ ⊢ State (CBlock b :: k) (Stmt (Jump l) s) m
      ⇒s State k (Stmt (Jump l) (block s)) (delete b m)
  | cstep_label_down l E k s m :
     l ∈ labels s →
     δ ⊢ State k (Stmt (Jump l) (subst E s)) m
      ⇒s State (CItem E :: k) (Stmt (Jump l) s) m
  | cstep_label_up l E k s m :
     l ∉ labels s →
     δ ⊢ State (CItem E :: k) (Stmt (Jump l) s) m
      ⇒s State k (Stmt (Jump l) (subst E s)) m
where "δ ⊢ S1 ⇒s S2" := (cstep δ S1%S S2%S) : stmt_scope.
Notation "( δ ⇒s)" := (cstep δ) (only parsing) : stmt_scope.

Notation "δ ⊢ S1 ⇒s* S2" := (rtc (δ ⇒s) S1 S2)
  (at level 80, S2 at level 70) : stmt_scope.
Notation "( δ ⇒s*)" := (rtc (δ ⇒s)) (only parsing) : stmt_scope.
Notation "δ ⊢ S1 ⇒s^ n S2" := (bsteps (δ ⇒s) n S1 S2)
  (at level 80, n at level 1, S2 at level 70) : stmt_scope.
Notation "( δ ⇒s^ n )" := (bsteps (δ ⇒s) n) (only parsing) : stmt_scope.

Definition cstep_in_ctx δ k : relation state := λ S1 S2,
  δ ⊢ S1 ⇒s S2 ∧ suffix_of k (SCtx S2).

Notation "δ ⊢ S1 ⇒s{ k } S2" := (cstep_in_ctx δ k S1 S2)
  (at level 80, S2 at level 70, k at level 80,
  format "δ  ⊢  S1  '⇒s{' k '}'  S2") : stmt_scope.
Notation "( δ ⇒s{ k })" := (cstep_in_ctx δ k) (only parsing) : stmt_scope.
Notation "δ ⊢ S1 ⇒s{ k }* S2" := (rtc (δ ⇒s{k}) S1 S2) 
  (at level 80, S2 at level 70, k at level 80,
  format "δ  ⊢  S1  '⇒s{' k '}*'  S2") : stmt_scope.
Notation "( δ  ⇒s{ k }*)" := (rtc (δ ⇒s{k})) (only parsing) : stmt_scope.
Notation "δ ⊢ S1 ⇒s{ k }^ n S2" := (bsteps (δ ⇒s{k}) n S1 S2)
  (at level 80, S2 at level 70, k at level 80, n at level 1,
  format "δ  ⊢  S1  '⇒s{' k '}^' n  S2") : stmt_scope.
Notation "( δ ⇒s{ k }^ n )" := (bsteps (δ ⇒s{k}) n) (only parsing) : stmt_scope.

Instance cstep_subrel_suffix_of δ k1 k2 :
  PropHolds (suffix_of k1 k2) → subrelation (δ ⇒s{k2}) (δ ⇒s{k1}).
Proof. intros ? S1 S2 [??]. split. easy. now transitivity k2. Qed.
Instance cstep_subrel δ k : subrelation (δ ⇒s{k}) (δ ⇒s).
Proof. firstorder. Qed.
Instance cstep_subrel_nil δ : subrelation (δ ⇒s) (δ ⇒s{ [] }).
Proof. intros S1 S2 ?. red. auto with list. Qed.

Hint Resolve expr_eval_weaken_mem expr_eval_weaken_stack : cstep.
Hint Resolve mem_subseteq_union_l mem_subseteq_union_r : cstep.
Hint Resolve Forall2_impl : cstep.

Lemma cstep_in_block_fresh δ k s m :
  let b := fresh_block m in
  δ ⊢ State k (Stmt In (block s)) m
   ⇒s State (CBlock b :: k) (Stmt In (s)) (<[b:=0%N]>m).
Proof. constructor. apply is_free_fresh_block. Qed.

Lemma cstep_label_block_down_fresh δ l k s m :
  l ∈ labels s →
  let b := fresh_block m in
  δ ⊢ State k (Stmt (Jump l) (block s)) m
   ⇒s State (CBlock b :: k) (Stmt (Jump l) s) (<[b:=0%N]>m).
Proof. constructor. easy. apply is_free_fresh_block. Qed.

Lemma cstep_alloc_params_fresh δ k f s m vs :
  δ !! f = Some s →
  let bs := fresh_blocks m (length vs) in
  δ ⊢ State k (Call f vs) m
   ⇒s State (CParams bs :: k) (Stmt In s) (insert_list (zip bs vs) m).
Proof.
  constructor. easy. apply alloc_params_insert_list.
  intuition auto with mem.
  apply same_length_length. now rewrite fresh_blocks_length.
Qed.

Hint Resolve cstep_in_block_fresh
  cstep_label_block_down_fresh cstep_alloc_params_fresh : cstep.

Ltac do_cstep :=
  match goal with
  | |- ?δ ⊢ State ?k (Stmt ?d (?s1 ;; ?s2)) ?m ⇒s ?S =>
    change (δ ⊢ State k (Stmt d (subst (s1 ;; □) s2)) m ⇒s S); do_cstep
  | |- ?δ ⊢ State ?k (Stmt ?d (?s1 ;; ?s2)) ?m ⇒s ?S =>
    change (δ ⊢ State k (Stmt d (subst (□ ;; s2) s1)) m ⇒s S); do_cstep
  | |- ?δ ⊢ State ?k (Stmt ?d (?l :; ?s)) ?m ⇒s ?S =>
    change (δ ⊢ State k (Stmt d (subst (l :; □) s)) m ⇒s S); do_cstep
  | |- ?δ ⊢ State ?k (Stmt ?d (loop ?s)) ?m ⇒s ?S =>
    change (δ ⊢ State k (Stmt d (subst (loop □) s)) m ⇒s S); do_cstep
  | |- ?δ ⊢ State ?k (Stmt ?d (IF ?e then ?s1 else ?s2)) ?m ⇒s ?S =>
    change (δ ⊢ State k (Stmt d (subst (IF e then s1 else □) s2)) m ⇒s S); do_cstep
  | |- ?δ ⊢ State ?k (Stmt ?d (IF ?e then ?s1 else ?s2)) ?m ⇒s ?S =>
    change (δ ⊢ State k (Stmt d (subst (IF e then □ else s2) s1)) m ⇒s S); do_cstep
  | |- _ ⊢ _ ⇒s _ => econstructor (do_cstep)
  | |- _ => solve [intuition eauto with cstep]
  | |- _ ⊢ _ ⇒s{_} _ => split; [ do_cstep | simpl; eauto with list ]
  | |- _ ⊢ _ ⇒s* _ => eapply rtc_once; do_cstep
  | |- _ ⊢ _ ⇒s{_}* _ => eapply rtc_once; do_cstep
  end.

Ltac do_csteps :=
  match goal with
  | |- _ => progress eauto
  | |- _ => reflexivity
  | |- _ ⊢ _ ⇒s* _ => simpl; etransitivity; [ do_cstep | do_csteps ]
  | |- _ ⊢ _ ⇒s{_}* _ => simpl; etransitivity; [ do_cstep | do_csteps ]
  | |- _ ⊢ _ ⇒s{_}^_ _ => simpl; econstructor (do_cstep)
  | |- _ ⊢ _ ⇒s{_}^(S _) _ => apply bsteps_S; do_csteps
  end.

Ltac solve_cred :=
  match goal with
  | |- _ => solve [intuition eauto with cstep]
  | H : red (_ ⇒s{_}) ?S |- red (_ ⇒s{_}) ?S => now apply (red_subrel _ _ _ _ H)
  | |- red (_⇒s) ?S => is_var S; destruct S; simpl in *; subst; solve_cred
  | |- red (_⇒s{_}) ?S => is_var S; destruct S; simpl in *; subst; solve_cred
  | |- red (_⇒s) (State _ (Stmt ?d _) _) =>
    is_var d; destruct d; simpl in *; try contradiction; solve_cred
  | |- red (_⇒s{_}) (State _ (Stmt ?d _) _) =>
    is_var d; destruct d; simpl in *; try contradiction; solve_cred
  | |- red (_⇒s) _ => eexists; do_cstep
  | |- red (_⇒s{_}) _ => eexists; do_cstep
  end.

Ltac solve_cnf :=
  match goal with
  | H : nf (_ ⇒s) _ |- _ => destruct H; solve_cnf
  | H : nf (_ ⇒s{_}) _ |- _ => destruct H; solve_cnf
  end.

Ltac inv_cstep H :=
  match type of H with
  | _ ⊢ _ ⇒s _ =>
    inversion H; clear H; simplify_stmt_eqs; try contradiction
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

Section smallstep_properties.
Context (δ : fenv).

Lemma cstep_preserves_wf k_start s_start k S1 S2 :
  suffix_of k_start k →
  δ ⊢ S1 ⇒s{k} S2 →
  ctx_wf δ k_start s_start (SCtx S1) (SLoc S1) →
  ctx_wf δ k_start s_start (SCtx S2) (SLoc S2).
Proof.
  intros ? p.
  inv_cstep; try solve [inversion 1; subst;
      try discriminate_suffix_of; try econstructor; eauto].
  * inversion 1; subst. discriminate_suffix_of.
    match goal with
    | H : ctx_wf _ _ _ _ (Call_ _) |- _ => inversion H; subst
    end. discriminate_suffix_of. easy.
  * inversion 1; subst. discriminate_suffix_of.
    match goal with
    | H : ctx_wf _ _ _ _ (Call_ _) |- _ => inversion H; subst
    end. discriminate_suffix_of. easy.
Qed.

Lemma cstep_rtc_preserves_wf k_start s_start k S1 S2 :
  suffix_of k_start k →
  δ ⊢ S1 ⇒s{k}* S2 →
  ctx_wf δ k_start s_start (SCtx S1) (SLoc S1) →
  ctx_wf δ k_start s_start (SCtx S2) (SLoc S2).
Proof. induction 2; eauto using cstep_preserves_wf. Qed.

Lemma cteps_rtc_preserves_stmt k d1 s1 m1 d2 s2 m2 :
  δ ⊢ State k (Stmt d1 s1) m1 ⇒s{k}* State k (Stmt d2 s2) m2 →
  s1 = s2.
Proof.
  pose proof (ctx_wf_start δ k (Stmt d1 s1)).
  intros p. apply (ctx_wf_unique δ k (Stmt d1 s1) k). easy.
  apply (cstep_rtc_preserves_wf k (Stmt d1 s1)) in p; intuition.
Qed.

Lemma cstep_bsteps_preserves_stmt n k d1 s1 m1 d2 s2 m2 :
  δ ⊢ State k (Stmt d1 s1) m1 ⇒s{k}^n State k (Stmt d2 s2) m2 →
  s1 = s2.
Proof. eauto using cteps_rtc_preserves_stmt, bsteps_rtc. Qed.

Lemma cstep_subctx_step_or_nf k S1 S2 :
  δ ⊢ S1 ⇒s S2 →
  suffix_of k (SCtx S1) →
  suffix_of k (SCtx S2) ∨ nf (δ⇒s{k}) S1.
Proof.
  intros. destruct (decide (suffix_of k (SCtx S2))).
  * tauto.
  * inv_cstep; simpl in *; auto with list; right;
      intros [??]; inv_cstep; simplify_stmt_elem_of.
Qed.

Lemma cstep_subctx_cut n l k S1 S3 :
    δ ⊢ S1 ⇒s{k}^n S3 → 
    suffix_of (l ++ k) (SCtx S1) → 
  (δ ⊢ S1 ⇒s{l ++ k}^n S3)
   ∨
  (∃ S2, 
    δ ⊢ S1 ⇒s{l ++ k}^n S2
    ∧ nf (δ⇒s{l ++ k}) S2 ∧ δ ⊢ S2 ⇒s{k}^n S3).
Proof.
  intros p ?. induction p as [ n S1 | n S1 S2 S3 [p1 ?] p2].
  * left. now auto with trs.
  * destruct (cstep_subctx_step_or_nf (l ++ k) S1 S2); auto.
    + destruct IHp2 as [? | [S2' ?]]; auto.
      - left. do_csteps.
      - right. exists S2'. intuition; do_csteps.
    + right. exists S1. intuition; do_csteps.
Qed.
End smallstep_properties.
