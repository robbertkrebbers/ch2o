Require Import Omega.
Require Export assertions smallstep.

Local Open Scope nat_scope.

Definition dassert := direction → assert.
Definition dassert_pack (Ψ : (label → assert) * (option N → assert)) 
    (P : assert) (Q: assert) : direction → assert :=
  direction_rect (λ _, assert) P Q (snd Ψ) (fst Ψ).

Instance: Proper 
  (prod_relation (pointwise_relation _ (≡)) (pointwise_relation _ (≡)) ==>
    (≡) ==> (≡) ==> (=) ==> (≡)) dassert_pack.
Proof. intros ?????????? d ?. subst. destruct d; firstorder. Qed.

Definition dassert_map (f : assert → assert) (P : dassert) : dassert :=
  direction_rect (λ _, assert) (f (P In)) (f (P Out)) (λ v, f (P (Return v))) (λ l, f (P (Goto l))).
Lemma dassert_map_spec f P d : dassert_map f P d = f (P d).
Proof. now destruct d. Qed.

Inductive ax_conclusion (P : dassert) (k : ctx) (mr : mem) (S : state) : Prop :=
  | ax_further ml :
     mem_disjoint ml mr →
     SMem S = ml ∪ mr →
     red (⇨{k}) S →
     ax_conclusion P k mr S
  | ax_done ml :
     mem_disjoint ml mr →
     SMem S = ml ∪ mr →
     SCtx S = k →
     up (SDir S) (SStmt S) →
     P (SDir S) (get_stack k) ml →
     ax_conclusion P k mr S.

Definition ax (s : stmt) (P : dassert) := ∀ d k ml mr S',
    mem_disjoint ml mr →
    State d k s (ml ∪ mr) ⇨{k}* S' →
    down d s →
    P d (get_stack k) ml →
  ax_conclusion P k mr S'.
Notation "Ψ ⊢ ⦃ P ⦄ s ⦃ Q ⦄" := (ax s%S (dassert_pack Ψ%A P%A Q%A)) (at level 80).

Lemma ax_split s P (Hax : ax s P) l n d k ml mr S'' :
    mem_disjoint ml mr →
    State d (l ++ k) s (ml ∪ mr) ⇨{k}^n S'' →
    down d s →
    P d (get_stack l ++ get_stack k) ml →
  (∃ ml'',
    mem_disjoint ml'' mr
    ∧ SMem S'' = ml'' ∪ mr
    ∧ red (⇨{l ++ k}) S'')
  ∨ (∃ n' d' ml',
    mem_disjoint ml' mr
    ∧ State d' (l ++ k) s (ml' ∪ mr) ⇨{k}^n' S''
    ∧ n' ≤ n
    ∧ up d' s ∧ P d' (get_stack l ++ get_stack k) ml').
Proof.
  intros ? p1 Hdown HP.
  rewrite <-get_stack_app in *.
  destruct (cstep_subctx_cut l k _ _ _ p1)
    as [? | [n' [S' [p2 [p3 [??]]]]]]; eauto with list.
   destruct (Hax d (l ++ k) ml mr S'') as [ml'' | ml'']; auto.
    left. exists ml''. now auto.
   destruct S'' as [d'' k'' s'' m'']; simpl in *.
   right. exists 0 d'' ml''.
   assert (s = s''); subst.
    eapply csteps_preserve_stmt.
    now apply (rtc_subrel (⇨{l ++ k}) (⇨) _); eauto.
   now intuition.
  right. destruct (Hax d (l ++ k) ml mr S') as [ml' | ml']; auto.
   exists n' (SDir S') ml'. now auto.
  destruct S' as [d' k' s' m']; simpl in *.
  assert (s = s'); subst.
   eapply csteps_preserve_stmt.
   now apply (rtc_subrel (⇨{l ++ k}) (⇨) _); eauto.
  exists n' d' ml'. now auto.
Qed.

Lemma ax_sound s P d m d' k' s' m' :
  ax s P →
    State d [] s m ⇨* State d' k' s' m' →
    nf (⇨) (State d' k' s' m') →
    down d s →
    P d [] m →
  k' = [] 
  ∧ up d' s' 
  ∧ P d' [] m'.
Proof.
  intros Hax p Hnf ??.
  destruct (Hax d [] m ∅ (State d' k' s' m')) as [m'' | m'']; auto.
  * auto with mem.
  * rewrite (right_id ∅ _). now apply (rtc_subrel (⇨) (⇨{[]}) _).
  * destruct Hnf. now apply (red_subrel (⇨{[]}) _ _).
  * simpl in *. subst. rewrite (right_id ∅ _). now auto.
Qed.

Lemma ax_weak Ψ P Q s : 
  Ψ ⊢ ⦃ P ⦄ s ⦃ Q ⦄ → ∀ P' Q', P' ⊆ P → Q ⊆ Q' → Ψ ⊢ ⦃ P' ⦄ s ⦃ Q' ⦄.
Proof.
  intros Hax P' Q' HP HQ d k ml mr S' ????.
  destruct (Hax d k ml mr S') as [ml' | ml']; auto.
    now destruct d; intuition.
   now left with ml'.
  right with ml'; auto. destruct (SDir S'); intuition.
Qed.

Lemma ax_frame_packed A Ppack s :
  ax s Ppack → ax s (dassert_map (λ P, P * A)%A Ppack).
Proof.
  intros Hax d k m1 m4 S' ???.
  rewrite dassert_map_spec.
  intros [m2 [m3 [? [? [??]]]]]. subst.
  destruct (Hax d k m2 (m3 ∪ m4) S') as [ml2' | ml2']; auto.
     solve_mem_disjoint.
    now rewrite (associative _).
   left with (ml2' ∪ m3); auto.
    solve_mem_disjoint.
   now rewrite <-(associative _).
  right with (ml2' ∪ m3); auto.
    solve_mem_disjoint.
   now rewrite <-(associative _).
  rewrite dassert_map_spec.
  exists ml2' m3. intuition. solve_mem_disjoint.
Qed.

Lemma ax_frame J R A P Q s :
  (J,R) ⊢ ⦃ P ⦄ s ⦃ Q ⦄ → (λ l, J l * A, λ v, R v * A) ⊢ ⦃ P * A ⦄ s ⦃ Q * A ⦄.
Proof. apply ax_frame_packed. Qed.

Lemma ax_and Ψ P Q Q' s :
  Ψ ⊢ ⦃ P ⦄ s ⦃ Q ⦄ → Ψ ⊢ ⦃ P ⦄ s ⦃ Q' ⦄ → Ψ ⊢ ⦃ P ⦄ s ⦃ Q ∧ Q' ⦄.
Proof.
  intros Hax1 Hax2 d k ml mr S' ??? Hpre.
  destruct (Hax1 d k ml mr S') as [ml' | ml']; auto.
    now destruct d; intuition.
   now left with ml'.
  destruct (Hax2 d k ml mr S') as [ml'' | ml'']; auto.
    now destruct d; intuition.
   now left with ml'.
  assert (ml' = ml''); subst.
   now apply mem_union_cancel_l with mr; intuition congruence.
  right with ml''; auto.
  destruct (SDir S'); intuition auto. now split.
Qed.

Lemma ax_skip Ψ P : Ψ ⊢ ⦃ P ⦄ skip ⦃ P ⦄.
Proof.
  intros d k ml mr S' ? p ??. inv_csteps p as [ | ???? p].
   left with ml; auto. solve_cnf.
  inv_cstep. inv_csteps p; simpl in *.
   now right with ml.
  inv_cstep.
Qed.

Lemma ax_goto Ψ Q l : Ψ ⊢ ⦃ fst Ψ l ⦄ goto l ⦃ Q ⦄.
Proof.
  intros d k ml mr S' ? p ??. inv_csteps p as [ | ???? p].
   left with ml; auto. solve_cnf.
  inv_cstep. inv_csteps p; simpl in *.
   right with ml; auto. simplify_elem_of.
  inv_cstep.
Qed.

Lemma ax_return Ψ e Q : Ψ ⊢ ⦃ ∃ v, e⇓v ∧ snd Ψ (Some v) ⦄ ret e ⦃ Q ⦄.
Proof.
  intros d k ml mr S' ? p ? Hpre.
  destruct d; try contradiction.
  destruct Hpre as [v [??]]. simplify_assert_expr.
  inv_csteps p as [| ???? p ]; simpl in *.
   left with ml; auto. solve_cnf.
  inv_cstep. inv_csteps p; simpl in *.
   simplify_assert_expr.
   now right with ml.
  inv_cstep.
Qed.

Lemma ax_assign Ψ e1 e2 (Q : assert) :
  Ψ ⊢ ⦃ ∃ a v, e1⇓a ∧ e2⇓v ∧ load a⇓- ∧ <[a:=v]>Q ⦄ e1 ::= e2 ⦃ Q ⦄.
Proof.
  intros d k ml mr S' ? p ? Hpre.
  destruct d; try contradiction.
  inv_csteps p as [| ???? p ]; simpl in *.
   left with ml; auto.
   destruct Hpre as [a [v [? [? [[??] ?]]]]].
   simplify_assert_expr.
   assert (is_writable a (ml ∪ mr)).
    do 2 red. eauto with mem.
   solve_cnf.
  inv_cstep. inv_csteps p; simpl in *.
   destruct Hpre as [a' [v' [? [? [[??] ?]]]]].
   simplify_assert_expr.
   right with (<[a:=v]>ml); auto.
    now eauto with mem.
   now rewrite mem_union_insert_l.
  inv_cstep.
Qed.

Lemma ax_loop Ψ P Q s : Ψ ⊢ ⦃ P ⦄ s ⦃ P ⦄ → Ψ ⊢ ⦃ P ⦄ loop s ⦃ Q ⦄.
Proof.
  intros Hax d k ml mr S5 Hdisjoint p1.
  revert d ml Hdisjoint p1.
  assert (∀ n d ml,
      mem_disjoint ml mr →
      State d (CItem (loop □) :: k) s (ml ∪ mr) ⇨{k}^n S5 →
      down d s →
      dassert_pack Ψ P P d (get_stack k) ml →
    ax_conclusion (dassert_pack Ψ P Q) k mr S5).
   induction n as [n1 IH] using lt_wf_ind.
   intros d1 ml1 ? p1 ??.
   edestruct (ax_split s _ Hax [CItem (loop □)])
     as [[ml2 [? [??]]] | [n' [d2 [ml2 [? [p2 ?]]]]]]; simpl in *; eauto.
    left with ml2; auto. solve_cnf.
   inv_csteps p2 as [| n3 ? S3 ? p2 p3]; simpl in *.
    left with ml2; auto. solve_cnf.
   { inv_cstep p2; try solve [simplify_stmt_elem_of].
   * inv_csteps p3 as [| n4 ? S4 ? p3 p4]; simpl in *.
       left with ml2; auto. solve_cnf.
      inv_cstep. eapply (IH n4); intuition eauto. omega.
   * inv_csteps p3; simpl in *. now right with ml2. inv_cstep.
   * inv_csteps p3; simpl in *. now right with ml2. inv_cstep. }
  intros d ml ? p ??.
  destruct (rtc_nsteps p) as [n pn]. inv_csteps pn; simpl in*.
   left with ml; auto. solve_cnf.
  inv_cstep; eauto.
Qed.

Lemma ax_label Ψ l s Q :
  Ψ ⊢ ⦃ fst Ψ l ⦄ s ⦃ Q ⦄ → Ψ ⊢ ⦃ fst Ψ l ⦄ l :; s ⦃ Q ⦄.
Proof.
  intros Hax d k ml mr S5 Hdisjoint p1.
  revert d ml Hdisjoint p1.
  assert (∀ n d ml,
      mem_disjoint ml mr →
      State d (CItem (l :; □) :: k) s (ml ∪ mr) ⇨{k}^n S5 →
      down d s →
      dassert_pack Ψ (fst Ψ l) Q d (get_stack k) ml →
    ax_conclusion (dassert_pack Ψ (fst Ψ l) Q) k mr S5).
   induction n as [n1 IH] using lt_wf_ind.
   intros d1 ml1 ? p1 ??.
   edestruct (ax_split s _ Hax [CItem (l :; □)])
     as [[ml2 [? [??]]] | [n' [d2 [ml2 [? [p2 ?]]]]]]; simpl in *; eauto.
    left with ml2; auto. solve_cnf.
   inv_csteps p2 as [| n3 ? S3 ? p2 p3]; simpl in *.
    left with ml2; auto. solve_cnf.
   { inv_cstep p2; try solve [simplify_stmt_elem_of].
   * inv_csteps p3; simpl in *. now right with ml2. inv_cstep.
   * inv_csteps p3; simpl in *. now right with ml2. inv_cstep.
   * match goal with
     | _ : State (Goto ?l') _ _ _ ⇨{_}^_ _ |- _ => destruct (decide (l' = l))
     end; simpl in *; subst.
    + inv_csteps p3 as [| n4 ? S4 ? p3 p4]; simpl in *.
         left with ml2; auto. solve_cnf.
        inv_cstep. eapply (IH n4); intuition eauto. omega.
    + inv_csteps p3; simpl in *. right with ml2; simplify_elem_of. inv_cstep. }
  intros d ml ? p ??.
  destruct (rtc_nsteps p) as [n pn]. inv_csteps pn; simpl in *.
   left with ml; auto.
   destruct d; simplify_elem_of; solve_cnf. 
  inv_cstep; eauto.
Qed.

Lemma ax_comp Ψ sl sr P P' Q :
  Ψ ⊢ ⦃ P ⦄ sl ⦃ P' ⦄ → 
  Ψ ⊢ ⦃ P' ⦄ sr ⦃ Q ⦄ →
  Ψ ⊢ ⦃ P ⦄ sl ;; sr ⦃ Q ⦄.
Proof.
  intros Haxl Haxr d k ml mr S5 Hdisjoint p1.
  revert d ml Hdisjoint p1.
  assert (∀ n d ml,
    mem_disjoint ml mr →
    (State d (CItem (□ ;; sr) :: k) sl (ml ∪ mr) ⇨{k}^n S5
      ∧ down d sl
      ∧ dassert_pack Ψ P P' d (get_stack k) ml)
    ∨ (State d (CItem (sl ;; □) :: k) sr (ml ∪ mr) ⇨{k}^n S5
      ∧ down d sr
      ∧ dassert_pack Ψ P' Q d (get_stack k) ml) →
    ax_conclusion (dassert_pack Ψ P Q) k mr S5).
   induction n as [n IH] using lt_wf_ind.
   intros d1 ml1 ? [[p1 [??]] | [p1 [??]]].
    edestruct (ax_split sl _ Haxl [CItem (□ ;; sr)])
      as [[ml2 [? [??]]] | [n' [d2 [ml2 [? [p2 ?]]]]]]; simpl in *; eauto.
     left with ml2; auto. solve_cnf.
    inv_csteps p2 as [| n3 ? S3 ? p2 p3]; simpl in *.
     left with ml2; auto. solve_cnf.
    { inv_cstep p2; try solve [simplify_stmt_elem_of].
    * eapply (IH n3); intuition eauto.
    * inv_csteps p3; simpl in *. now right with ml2. inv_cstep.
    * match goal with
     | _ : State (Goto ?l') _ _ _ ⇨{_}^_ _ |- _ => destruct (decide (l ∈ labels sr))
     end; simpl in *; subst.
     + inv_csteps p3 as [| n4 ? S4 ? p3 p4]; simpl in *.
          left with ml2; auto. solve_cnf.
         inv_cstep. eapply (IH n4); intuition eauto. omega.
     + inv_csteps p3; simpl in *. right with ml2; simplify_elem_of. inv_cstep. }
   edestruct (ax_split sr _ Haxr [CItem (sl ;; □)])
     as [[ml2 [? [??]]] | [n' [d2 [ml2 [? [p2 ?]]]]]]; simpl in *; eauto.
    left with ml2; auto. solve_cnf.
   inv_csteps p2 as [| n3 ? S3 ? p2 p3]; simpl in *.
    left with ml2; auto. solve_cnf.
   { inv_cstep p2; try solve [simplify_stmt_elem_of].
   * inv_csteps p3; simpl in *. now right with ml2. inv_cstep.
   * inv_csteps p3; simpl in *. now right with ml2. inv_cstep.
   * match goal with
    | _ : State (Goto ?l') _ _ _ ⇨{_}^_ _ |- _ => destruct (decide (l ∈ labels sl))
    end; simpl in *; subst.
    + inv_csteps p3 as [| n4 ? S4 ? p3 p4]; simpl in *.
         left with ml2; auto. solve_cnf.
        inv_cstep. eapply (IH n4); intuition eauto. omega.
    + inv_csteps p3; simpl in *. right with ml2; simplify_elem_of. inv_cstep. }
  intros d ml ? p ??.
  destruct (rtc_nsteps p) as [n pn]. inv_csteps pn; simpl in *.
   left with ml; auto.
   destruct d; simplify_elem_of; solve_cnf. 
  inv_cstep; eauto.
Qed.

Lemma ax_if Ψ e sl sr P Q :
  Ψ ⊢ ⦃ P ∧ ∃ v, e⇓v ∧ ⌜ val_true v ⌝ ⦄ sl ⦃ Q ⦄ → 
  Ψ ⊢ ⦃ P ∧ ∃ v, e⇓v ∧ ⌜ val_false v ⌝ ⦄ sr ⦃ Q ⦄ → 
  Ψ ⊢ ⦃ P ∧ e⇓- ⦄ IF e then sl else sr ⦃ Q ⦄.
Proof.
  intros Haxl Haxr d k ml mr S5 Hdisjoint p1.
  revert d ml Hdisjoint p1.
  assert (∀ n d ml,
    mem_disjoint ml mr →
    (State d (CItem (IF e then □ else sr) :: k) sl (ml ∪ mr) ⇨{k}^n S5
      ∧ down d sl
      ∧ dassert_pack Ψ (P ∧ ∃ v, e⇓v ∧ ⌜ val_true v ⌝)%A Q d (get_stack k) ml)
    ∨ (State d (CItem (IF e then sl else □) :: k) sr (ml ∪ mr) ⇨{k}^n S5
      ∧ down d sr
      ∧ dassert_pack Ψ (P ∧ ∃ v, e⇓v ∧ ⌜ val_false v ⌝)%A Q d (get_stack k) ml) →
    ax_conclusion (dassert_pack Ψ (P ∧ e⇓-)%A Q) k mr S5) as help.
   induction n as [n IH] using lt_wf_ind.
   intros d1 ml1 ? [[p1 [??]] | [p1 [??]]].
    edestruct (ax_split sl _ Haxl [CItem (IF e then □ else sr)])
      as [[ml2 [? [??]]] | [n' [d2 [ml2 [? [p2 ?]]]]]]; simpl in *; eauto.
     left with ml2; auto. solve_cnf.
    inv_csteps p2 as [| n3 ? S3 ? p2 p3]; simpl in *.
     left with ml2; auto. solve_cnf.
    { inv_cstep p2; try solve [simplify_stmt_elem_of].
    * inv_csteps p3; simpl in *. now right with ml2. inv_cstep.
    * inv_csteps p3; simpl in *. now right with ml2. inv_cstep.
    * match goal with
     | _ : State (Goto ?l') _ _ _ ⇨{_}^_ _ |- _ => destruct (decide (l ∈ labels sr))
     end; simpl in *; subst.
     + inv_csteps p3 as [| n4 ? S4 ? p3 p4]; simpl in *.
          left with ml2; auto. solve_cnf.
         inv_cstep. eapply (IH n4); intuition eauto. omega.
     + inv_csteps p3; simpl in *. right with ml2; simplify_elem_of. inv_cstep. }
   edestruct (ax_split sr _ Haxr [CItem (IF e then sl else □)])
     as [[ml2 [? [??]]] | [n' [d2 [ml2 [? [p2 ?]]]]]]; simpl in *; eauto.
    left with ml2; auto. solve_cnf.
   inv_csteps p2 as [| n3 ? S3 ? p2 p3]; simpl in *.
    left with ml2; auto. solve_cnf.
   { inv_cstep p2; try solve [simplify_stmt_elem_of].
   * inv_csteps p3; simpl in *. now right with ml2. inv_cstep.
   * inv_csteps p3; simpl in *. now right with ml2. inv_cstep.
   * match goal with
    | _ : State (Goto ?l') _ _ _ ⇨{_}^_ _ |- _ => destruct (decide (l ∈ labels sl))
    end; simpl in *; subst.
    + inv_csteps p3 as [| n4 ? S4 ? p3 p4]; simpl in *.
         left with ml2; auto. solve_cnf.
        inv_cstep. eapply (IH n4); intuition eauto. omega.
    + inv_csteps p3; simpl in *. right with ml2; simplify_elem_of. inv_cstep. }
  intros d ml ? p ? Hpre.
  destruct (rtc_nsteps p) as [n pn].
  destruct d; simpl in *; try contradiction.
  * destruct Hpre as [? [v ?]].
     inv_csteps pn; simpl in *.
      left with ml; auto.
      destruct (val_true_false_dec v); solve_cnf.
     inv_cstep; simplify_assert_expr; eapply help; eauto;
       [left | right]; clear help Haxl Haxr; solve_assert.
  * inv_csteps pn; simpl in *.
      left with ml; auto. simplify_elem_of; solve_cnf.
     inv_cstep; eauto.
Qed.

Lemma ax_block_packed Ppack s :
  ax s (dassert_map (λ P, P↑* (O↦ -))%A Ppack) → ax (SBlock s) Ppack.
Proof.
  intros Hax d k ml mr S5 Hdisjoint p1.
  revert d ml Hdisjoint p1.
  assert (∀ n d ml b v,
      mem_disjoint ml mr →
      is_free b (ml ∪ mr) →
      State d (CBlock b :: k) s (<[b:=v]>(ml ∪ mr)) ⇨{k}^n S5 →
      down d s →
      Ppack d (get_stack k) ml →
    ax_conclusion Ppack k mr S5).
   intros n d1 ml1 b v Hdisjoint Hfree p1 ??.
   rewrite mem_union_insert_l in p1.
   red in Hfree. rewrite mem_union_None_iff in Hfree. destruct Hfree.
   assert (mem_disjoint (<[ b:=v ]>ml1) mr).
    apply mem_disjoint_insert_l; auto.
   clear Hdisjoint.
   edestruct (ax_split s _ Hax [CBlock b])
     as [[ml2 [? [??]]] | [n' [d2 [ml2 [? [p2 [? [? Hpost]]]]]]]]; simpl in *; eauto.
     rewrite dassert_map_spec.
     apply assert_alloc; auto.
    left with ml2; auto. solve_cnf.
   rewrite dassert_map_spec in Hpost.
   apply assert_free in Hpost.
   assert (delete b (ml2 ∪ mr) = delete b ml2 ∪ mr).
    now rewrite mem_union_delete, (delete_lookup_None mr).
   inv_csteps p2 as [| n3 ? S3 ? p2 p3]; simpl in *.
    left with ml2; auto. solve_cnf.
   { inv_cstep p2; try solve [simplify_stmt_elem_of].
   * inv_csteps p3; simpl in *. right with (delete b ml2); auto with mem. inv_cstep.
   * inv_csteps p3; simpl in *. right with (delete b ml2); auto with mem. inv_cstep.
   * inv_csteps p3; simpl in *. right with (delete b ml2); auto with mem. inv_cstep. }
  intros d ml ? p ? Hpre.
  destruct (rtc_nsteps p) as [n pn].
  inv_csteps pn; simpl in *.
   left with ml; auto. solve_cnf.
  inv_cstep; eauto.
Qed.

Lemma ax_block J R P Q s :
  (λ l, J l↑ * (O↦ -), λ v, R v↑ * (O↦ -)) ⊢ ⦃ P↑ * (O↦ -) ⦄ s ⦃ Q↑ * (O↦ -) ⦄ →
  (J,R) ⊢ ⦃ P ⦄ SBlock s ⦃ Q ⦄.
Proof. intros. now apply ax_block_packed. Qed.
