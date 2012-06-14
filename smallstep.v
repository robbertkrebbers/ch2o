Require Export statements trs.

Inductive direction :=
 | In : direction
 | Out : direction
 | Return : option N → direction
 | Goto : label → direction.

Instance direction_eq_dec (d1 d2 : direction) : Decision (d1 = d2).
Proof. solve_decision. Defined.

Inductive state := State {
  SDir : direction;
  SCtx : ctx;
  SStmt : stmt;
  SMem : mem
}.
Add Printing Constructor state.

Instance state_eq_dec (S1 S2 : state) : Decision (S1 = S2).
Proof. solve_decision. Defined.

Reserved Infix "⇨" (at level 70).
Inductive cstep: relation state :=
  | cstep_assign k e1 a e2 v m :
     ⟦ e1 ⟧ (get_stack k) m = Some a → 
     ⟦ e2 ⟧ (get_stack k) m = Some v →
     is_writable a m →
     State In k (e1 ::= e2) m ⇨ State Out k (e1 ::= e2) (<[a := v]>m)
  | cstep_skip k m :
     State In k skip m ⇨ State Out k skip m
  | cstep_goto l k m :
     State In k (goto l) m ⇨ State (Goto l) k (goto l) m
  | cstep_return k e v m :
     ⟦ e ⟧ (get_stack k) m = Some v →
     State In k (ret e) m ⇨ State (Return (Some v)) k (ret e) m 

  | cstep_in_block k b v s m :
     is_free b m → State In k (SBlock s) m ⇨ State In (CBlock b :: k) s (<[b:=v]>m)
  | cstep_in_comp k s1 s2 m :
     State In k (s1 ;; s2) m ⇨ State In (CItem (□ ;; s2) :: k) s1 m
  | cstep_in_loop k s m :
     State In k (loop s) m ⇨ State In (CItem (loop □) :: k) s m
  | cstep_in_if1 k e s1 s2 v m :
     ⟦ e ⟧ (get_stack k) m = Some v → val_true v → 
     State In k (IF e then s1 else s2) m ⇨ State In (CItem (IF e then □ else s2) :: k) s1 m
  | cstep_in_if2 k e s1 s2 v m :
     ⟦ e ⟧ (get_stack k) m = Some v → val_false v → 
     State In k (IF e then s1 else s2) m ⇨ State In (CItem (IF e then s1 else □) :: k) s2 m
  | cstep_in_label k l s m :
     State In k (l :; s) m ⇨ State In (CItem (l :; □) :: k) s m

  | cstep_out_block k b s m :
     State Out (CBlock b :: k) s m ⇨ State Out k (SBlock s) (delete b m)
  | cstep_out_comp1 k s1 s2 m :
     State Out (CItem (□ ;; s2) :: k) s1 m ⇨ State In (CItem (s1 ;; □) :: k) s2 m
  | cstep_out_comp2 k s1 s2 m :
     State Out (CItem (s1 ;; □) :: k) s2 m ⇨ State Out k (s1 ;; s2) m
  | cstep_out_loop k s m :
     State Out (CItem (loop □) :: k) s m ⇨ State In k (loop s) m
     (* not ... ⇨ (CItem (loop □) :: k) s m so we force the loop to go out of the context *)
  | cstep_out_if1 k e s1 s2 m :
     State Out (CItem (IF e then □ else s2) :: k) s1 m ⇨ State Out k (IF e then s1 else s2) m
  | cstep_out_if2 k e s1 s2 m :
     State Out (CItem (IF e then s1 else □) :: k) s2 m ⇨ State Out k (IF e then s1 else s2) m
  | cstep_out_label k s l m :
     State Out (CItem (l :; □) :: k) s m ⇨ State Out k (l :; s) m

  | cstep_ret_block v k b s m :
     State (Return v) (CBlock b :: k) s m ⇨ State (Return v) k (SBlock s) (delete b m)
  | cstep_ret_item v E k s m :
     State (Return v) (CItem E :: k) s m ⇨ State (Return v) k (subst E s) m

  | cstep_label_here l k s m :
     State (Goto l) k (l :; s) m ⇨ State In (CItem (l :; □) :: k) s m
  | cstep_label_block_down l k b v s m :
     l ∈ labels s → is_free b m → State (Goto l) k (SBlock s) m ⇨ State (Goto l) (CBlock b :: k) s (<[b:=v]> m)
  | cstep_label_block_up l k b s m :
     (* not l ∈ labels k to avoid it going back and forth between double occurences of labels *)
     l ∉ labels s → State (Goto l) (CBlock b :: k) s m ⇨ State (Goto l) k (SBlock s) (delete b m)
  | cstep_label_down l E k s m :
     l ∈ labels s → State (Goto l) k (subst E s) m ⇨ State (Goto l) (CItem E :: k) s m
  | cstep_label_up l E k s m :
     l ∉ labels s → State (Goto l) (CItem E :: k) s m ⇨ State (Goto l) k (subst E s) m
where "S1 ⇨ S2" := (cstep S1%S S2%S) : stmt_scope.
Notation "(⇨)" := cstep (only parsing) : stmt_scope.

Infix "⇨*" := (rtc (⇨)) (at level 70) : stmt_scope.
Notation "(⇨*)" := (rtc (⇨)) (only parsing) : stmt_scope.
Notation "S1 ⇨^ n S2" := (nsteps (⇨) n S1 S2) (at level 70, n at level 1) : stmt_scope.
Notation "(⇨^ n )" := (nsteps (⇨) n) (only parsing) : stmt_scope.

Definition cstep_in_ctx k : relation state := λ S1 S2, S1 ⇨ S2 ∧ suffix_of k (SCtx S2).

Notation "S1 ⇨{ k } S2" := (cstep_in_ctx k S1 S2) (at level 70, format "S1  '⇨{' k '}'  S2") : stmt_scope.
Notation "(⇨{ k })" := (cstep_in_ctx k) (only parsing) : stmt_scope.
Notation "S1 ⇨{ k }* S2" := (rtc (⇨{k}) S1 S2) (at level 70, format "S1  '⇨{' k '}*'  S2") : stmt_scope.
Notation "(⇨{ k }*)" := (rtc (⇨{k})) (only parsing) : stmt_scope.
Notation "S1 ⇨{ k }^ n S2" := (nsteps (⇨{k}) n S1 S2) (at level 70, n at level 1, format "S1  '⇨{' k '}^' n  S2") : stmt_scope.
Notation "(⇨{ k }^ n )" := (nsteps (⇨{k}) n) (only parsing) : stmt_scope.

Instance cstep_subrel_suffix_of k1 k2 : PropHolds (suffix_of k1 k2) → subrelation (⇨{k2}) (⇨{k1}).
Proof. intros ? S1 S2 [??]. split. easy. now transitivity k2. Qed.
Instance cstep_subrel k : subrelation (⇨{k}) (⇨).
Proof. firstorder. Qed.
Instance cstep_subrel_nil : subrelation (⇨) (⇨{[]}).
Proof. intros S1 S2 ?. red. auto with list. Qed.

Hint Resolve fresh_block_is_free : cstep.
Hint Resolve expr_eval_weaken_mem expr_eval_weaken_stack : cstep.
Hint Resolve mem_subseteq_union_l mem_subseteq_union_r : cstep.

Ltac do_cstep :=
  match goal with
  | |- State ?d ?k (?s1 ;; ?s2) ?m ⇨ ?S => change (State d k (subst (s1 ;; □) s2) m ⇨ S); do_cstep
  | |- State ?d ?k (?s1 ;; ?s2) ?m ⇨ ?S => change (State d k (subst (□ ;; s2) s1) m ⇨ S); do_cstep
  | |- State ?d ?k (?l :; ?s) ?m ⇨ ?S => change (State d k (subst (l :; □) s) m ⇨ S); do_cstep
  | |- State ?d ?k (loop ?s) ?m ⇨ ?S => change (State d k (subst (loop □) s) m ⇨ S); do_cstep
  | |- State ?d ?k (IF ?e then ?s1 else ?s2) ?m ⇨ ?S => change (State d k (subst (IF e then s1 else □) s2) m ⇨ S); do_cstep
  | |- State ?d ?k (IF ?e then ?s1 else ?s2) ?m ⇨ ?S => change (State d k (subst (IF e then □ else s2) s1) m ⇨ S); do_cstep
  | |- State In _ (SBlock _) _ ⇨ _ => eapply cstep_in_block with (v:=0); do_cstep
  | |- State (Goto _) _ (SBlock _) _ ⇨ _ => eapply cstep_label_block_down with (v:=0); do_cstep
  | |- _ ⇨ _ => econstructor (do_cstep)
  | |- _ => solve [intuition eauto with cstep]
  | |- _ ⇨{_} _ => split; [ do_cstep | simpl; eauto with list ]
  | |- _ ⇨* _ => eapply rtc_once; do_cstep
  | |- _ ⇨{_}* _ => eapply rtc_once; do_cstep
  end.

Ltac do_csteps :=
  match goal with
  | |- _ => progress eauto
  | |- _ => reflexivity
  | |- _ ⇨* _ => simpl; etransitivity; [ do_cstep | do_csteps ]
  | |- _ ⇨{_}* _ => simpl; etransitivity; [ do_cstep | do_csteps ]
  | |- _ ⇨{_}^_ _ => simpl; econstructor; [ do_cstep | do_csteps ]
  end.

Ltac solve_cnf :=
  match goal with
  | |- _ => solve [intuition eauto with cstep]
  | H : nf (⇨) _ |- _ => destruct H; solve_cnf
  | H : nf (⇨{_}) _ |- _ => destruct H; solve_cnf
  | H : red (⇨{_}) ?S |- red (⇨{_}) ?S => now apply (red_subrel _ _ _ _ H)
  | |- red (⇨) ?S => is_var S; destruct S; simpl in *; subst; solve_cnf
  | |- red (⇨{_}) ?S => is_var S; destruct S; simpl in *; subst; solve_cnf
  | |- red (⇨) (State ?d _ _ _) => is_var d; destruct d; simpl in *; try contradiction; solve_cnf
  | |- red (⇨{_}) (State ?d _ _ _) => is_var d; destruct d; simpl in *; try contradiction; solve_cnf
  | |- red (⇨) _ => eexists; do_cstep
  | |- red (⇨{_}) _ => eexists; do_cstep
  end.

Ltac inv_cstep H :=
  match type of H with
  | _ ⇨ _ => inversion H; clear H; simplify_stmt_eqs; try contradiction
  | _ ⇨{_} _ =>
    let H1 := fresh in
    let H2 := fresh in
    destruct H as [H1 H2];
    inv_cstep H1;
    simpl in H2; simplify_suffix_of
  end.
Tactic Notation "inv_cstep" hyp(H) := inv_cstep H.

Tactic Notation "inv_cstep" :=
  match goal with
  | H : _ ⇨ _ |- _ => inv_cstep H
  | H : _ ⇨{_} _ |- _ => inv_cstep H
  end.
Tactic Notation "inv_csteps" hyp(H) "as" simple_intropattern(H2) :=
  let H' := fresh in rename H into H';
  inversion H' as H2; clear H'; subst.
Tactic Notation "inv_csteps" hyp(H) := inv_csteps H as [].

Lemma cstep_preserves_ctx_stmt S1 S2 :
  S1 ⇨ S2 → subst (SCtx S1) (SStmt S1) = subst (SCtx S2) (SStmt S2).
Proof. intros. inv_cstep. Qed.

Lemma csteps_preserve_ctx_stmt S1 S2 :
  S1 ⇨* S2 → subst (SCtx S1) (SStmt S1) = subst (SCtx S2) (SStmt S2).
Proof.
  induction 1.
   reflexivity.
  etransitivity; [ eapply cstep_preserves_ctx_stmt |]; eauto.
Qed.

Lemma csteps_preserve_stmt d1 k1 s1 m1 d2 s2 m2 :
  State d1 k1 s1 m1 ⇨* State d2 k1 s2 m2 → s1 = s2.
Proof.
  intros p. apply (injective (subst k1)).
  apply (csteps_preserve_ctx_stmt _ _ p).
Qed.

Lemma csteps_preserve_gotos S1 S2 :
  S1 ⇨* S2 → gotos (SCtx S1) ∪ gotos (SStmt S1) ≡ gotos (SCtx S2) ∪ gotos (SStmt S2).
Proof. intros. now erewrite <-!ctx_gotos_spec, csteps_preserve_ctx_stmt by eauto. Qed.
Lemma csteps_preserve_labels S1 S2 :
  S1 ⇨* S2 → labels (SCtx S1) ∪ labels (SStmt S1) ≡ labels (SCtx S2) ∪ labels (SStmt S2).
Proof. intros. now erewrite <-!ctx_labels_spec, csteps_preserve_ctx_stmt by eauto. Qed.

Lemma elem_of_stmt_labels_red l k s m :
  l ∈ labels s → red (⇨) (State (Goto l) k s m).
Proof. destruct s; simplify_elem_of; solve_cnf. Qed.
Hint Resolve elem_of_stmt_labels_red : cstep.

Lemma cstep_weaken_ctx k d1 k1 s1 m1 d2 k2 s2 m2 :
  State d1 k1 s1 m1 ⇨ State d2 k2 s2 m2 →
  State d1 (k1 ++ k) s1 m1 ⇨ State d2 (k2 ++ k) s2 m2.
Proof.
  intros. inv_cstep; econstructor 
    (solve [erewrite ?get_stack_app, ?expr_eval_weaken_stack; eauto]).
Qed.

Lemma csteps_weaken_ctx k d1 k1 s1 m1 d2 k2 s2 m2 :
  State d1 k1 s1 m1 ⇨* State d2 k2 s2 m2 →
  State d1 (k1 ++ k) s1 m1 ⇨* State d2 (k2 ++ k) s2 m2.
Proof.
  intros p. generalize_rtc p. induction p as [|? [d2 k2 s2 m2]]; intros; simplify_eqs.
   reflexivity.
  eauto using cstep_weaken_ctx with trs.
Qed.

Lemma cstep_subctx_step_or_nf k S1 S2 :
  S1 ⇨ S2 → 
  suffix_of k (SCtx S1) →
  suffix_of k (SCtx S2) ∨ nf (⇨{k}) S1.
Proof.
  intros. destruct (decide (suffix_of k (SCtx S2))).
   tauto.
  inv_cstep; simpl in *; auto with list; right; intros [??]; inv_cstep; simplify_stmt_elem_of.
Qed.

Lemma cstep_subctx_cut l k n S1 S3 :
    S1 ⇨{k}^n S3 → 
    suffix_of (l ++ k) (SCtx S1) → 
  (S1 ⇨{l ++ k}* S3)
   ∨
  (∃ n' S2, S1 ⇨{l ++ k}* S2 ∧ nf (⇨{l ++ k}) S2 ∧ S2 ⇨{k}^n' S3 ∧ n' ≤ n).
Proof.
  intros p ?. induction p as [ S1 | n S1 S2 S3 [p1 ?] p2].
   now left.
  destruct (cstep_subctx_step_or_nf (l ++ k) S1 S2); auto.
   destruct IHp2 as [? | [n' [S2' ?]]]; auto.
    left. do_csteps.
   right. exists n' S2'. intuition eauto with trs. do_csteps.
  right. exists (S n) S1. intuition eauto with trs. do_csteps.
Qed.

Definition down (d : direction) (s : stmt) : Prop :=
  match d with
  | In => True
  | Goto l => l ∈ labels s
  | _ => False
  end.
Definition up (d : direction) (s : stmt) : Prop :=
  match d with
  | Out => True
  | Return _ => True
  | Goto l => l ∉ labels s
  | _ => False
  end.

Hint Extern 0 (down _ _) => simpl; constructor.
Hint Extern 0 (up _ _) => simpl; constructor.

Lemma not_down_up d s : ¬down d s → up d s.
Proof. destruct d; intuition. Qed.

Definition down_up_dec d s : {down d s} + {up d s} :=
  match d with
  | In => left I
  | Out => right I
  | Goto l => decide_rel (∈) l (labels s)
  | Return _ => right I
  end.
