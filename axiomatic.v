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

Definition ax (s : stmt) (P : direction → assert) := ∀ A d k m d' k' s' m',
    State d k s m ⇨{k}* State d' k' s' m' →
    nf (⇨{k}) (State d' k' s' m') →
    down d s →
    (A * P d)%A (get_stack k) m →
  k' = k ∧ up d' s' ∧ (A * P d')%A (get_stack k) m'.
Notation "Ψ ⊢ ⦃ P ⦄ s ⦃ Q ⦄" := (ax s%S (dassert_pack Ψ%A P%A Q%A)) (at level 80).

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
  destruct (Hax emp%A d [] m d' k' s' m') as [? [??]].
      now apply (rtc_subrel (⇨) (⇨{[]}) _).
     now apply (nf_subrel (⇨{[]}) (⇨) _).
    easy.
   now apply assert_sep_left_id_2.
  intuition. now apply assert_sep_left_id_1.
Qed.

Lemma ax_weak Ψ P Q s : 
  Ψ ⊢ ⦃ P ⦄ s ⦃ Q ⦄ → ∀ P' Q', P' ⊆ P → Q ⊆ Q' → Ψ ⊢ ⦃ P' ⦄ s ⦃ Q' ⦄.
Proof.
  intros Hax P' Q' HP HQ A d k m d' k' s' m' ????.
  destruct (Hax A d k m d' k' s' m'); auto.
   destruct d; simpl in *; intuition. now rewrite <-HP.
  destruct d'; simpl in *; intuition. now rewrite <-HQ.
Qed.

Lemma ax_frame J R A P Q s :
  (J,R) ⊢ ⦃ P ⦄ s ⦃ Q ⦄ → (λ l, A * J l, λ v, A * R v) ⊢ ⦃ A * P ⦄ s ⦃ A * Q ⦄.
Proof.
  intros Hax B d k m d' k' s' m' ????.
  destruct (Hax (B * A)%A d k m d' k' s' m'); auto.
   destruct d; simpl in *; intuition; now rewrite <-(associative _).
  destruct d'; simpl in *; intuition; now rewrite (associative _).
Qed.

Lemma ax_and Ψ P Q Q' s :
  Ψ ⊢ ⦃ P ⦄ s ⦃ Q ⦄ → Ψ ⊢ ⦃ P ⦄ s ⦃ Q' ⦄ → Ψ ⊢ ⦃ P ⦄ s ⦃ Q ∧ Q' ⦄.
Proof.
  intros Hax Hax' B d k m d' k' s' m' ??? Hpre.
  destruct Hpre as [m1 [m2 [? [? [??]]]]].
  (* The Separation judgment does not directly say that the splitting of the
   memory before and after are the same. However, by extending the frame
   condition with an equality on the memory we do get that result *)
  destruct (Hax (Assert $ λ ρ m, m = m1 ∧ B ρ m) d k m d' k' s' m')
     as [? [? [m1' [m2' [? [? [[??] ?]]]]]]]; auto.
   exists m1 m2; destruct d; intuition.
  destruct (Hax' (Assert $ λ ρ m, m = m1 ∧ B ρ m) d k m d' k' s' m')
     as [_ [_ [m1'' [m2'' [? [? [[??] ?]]]]]]]; auto.
   exists m1 m2; destruct d; intuition.
  assert (m2'' = m2'); subst.
   apply mem_union_cancel_r with m1; auto; now symmetry.
  intuition. exists m1 m2'. intuition.
  destruct d'; intuition. now split.
Qed.

Lemma ax_skip Ψ P : Ψ ⊢ ⦃ P ⦄ skip ⦃ P ⦄.
Proof.
  intros A d k m d' k' s' m' p ???. inv_csteps p as [ | ???? p].
   solve_cnf.
  inv_cstep. inv_csteps p.
   intuition.
  inv_cstep.
Qed.

Lemma ax_goto Ψ Q l : Ψ ⊢ ⦃ fst Ψ l ⦄ goto l ⦃ Q ⦄.
Proof.
  intros A d k m d' k' s' m' p ???. inv_csteps p as [ |???? p].
   solve_cnf.
  inv_cstep. inv_csteps p.
   intuition simplify_elem_of.
  inv_cstep.
Qed.

Lemma ax_return Ψ e Q : Ψ ⊢ ⦃ ∃ v, e⇓v ∧ snd Ψ (Some v) ⦄ ret e ⦃ Q ⦄.
Proof.
  intros A d k m d' k' s' m' p ?? Hpre.
  destruct d; try contradiction.
  destruct Hpre as [m1 [m2 [? [? [? [v [??]]]]]]]; subst.
  inv_csteps p as [| ???? p ].
   simplify_assert_expr. solve_cnf.
  inv_cstep. inv_csteps p.
   intuition eauto. simplify_assert_expr. solve_assert.
  inv_cstep.
Qed.

Lemma ax_assign Ψ e1 e2 (Q : assert) :
  Ψ ⊢ ⦃ ∃ a v, e1⇓a ∧ e2⇓v ∧ load a⇓- ∧ <[a:=v]>Q ⦄ e1 ::= e2 ⦃ Q ⦄.
Proof.
  intros A d k m d' k' s' m' p ?? Hpre.
  destruct d; try contradiction.
  inv_csteps p as [| ???? p ].
   destruct Hpre as [m1 [m2 [? [? [? [a [v [? [? [[??] ?]]]]]]]]]]; subst.
   assert (is_writable a (m1 ∪ m2)).
     do 2 red. eauto with mem.
   simplify_assert_expr. solve_cnf.
  inv_cstep. inv_csteps p.
   intuition. simpl in *. eapply assert_assign; eauto.
  inv_cstep.
Qed.

Lemma ax_split s P :
  ax s P → ∀ l n A d k m S',
    State d (l ++ k) s m ⇨{k}^n S' →
    nf (⇨{k}) S' →
    down d s →
    (A * P d)%A (get_stack l ++ get_stack k) m →
  ∃ n' d' m',
    State d' (l ++ k) s m' ⇨{k}^n' S'
    ∧ up d' s
    ∧ (A * P d')%A (get_stack l ++ get_stack k) m'
    ∧ n' ≤ n.
Proof.
  intros Hax l n A d k m S' p1 Hnf Hdown HP.
  rewrite <-get_stack_app in *.
  destruct (cstep_subctx_cut l k _ _ _ p1) as [n' [[d' k' s' m'] ?]]; eauto with list.
  destruct (Hax A d (l ++ k) m d' k' s' m'); intuition.
  assert (s = s'); subst.
   eapply csteps_preserve_stmt.
   apply (rtc_subrel (⇨{l ++ k}) (⇨) _); eauto.
  exists n' d' m'. intuition.
Qed.

Lemma ax_loop Ψ P Q s : Ψ ⊢ ⦃ P ⦄ s ⦃ P ⦄ → Ψ ⊢ ⦃ P ⦄ loop s ⦃ Q ⦄.
Proof.
  intros Hax A d k m d5 k5 s5 m5 p Hnf. revert d m p.
  assert (∀ n d m,
    State d (CItem (loop □) :: k) s m ⇨{k}^n State d5 k5 s5 m5 →
    down d s →
    (A * dassert_pack Ψ P P d)%A (get_stack k) m →
      k5 = k ∧ up d5 s5 ∧ (A * dassert_pack Ψ P Q d5)%A (get_stack k) m5
   ).
   induction n as [n IH] using lt_wf_ind.
   intros d1 m1 p1 ??.
   edestruct (ax_split _ _ Hax [CItem (loop □)])
     as [n' [d2 [m2 [p2 [? [??]]]]]]; simpl in *; eauto.
   inv_csteps p2 as [| n'' ? S3 ? p2 p3].
    solve_cnf.
   { inv_cstep p2; try solve [simplify_stmt_elem_of].
   * inv_csteps p3 as [| n''' ? S4 ? p3 p4].
       solve_cnf.
      inv_cstep. eapply (IH n'''); eauto. omega.
   * inv_csteps p3; eauto. inv_cstep.
   * inv_csteps p3; eauto. inv_cstep. }
  intros d m p ??.
  destruct (rtc_nsteps p) as [n pn]. inv_csteps pn.
   solve_cnf.
  inv_cstep; eauto.
Qed.

Lemma ax_label Ψ l s Q :
  Ψ ⊢ ⦃ fst Ψ l ⦄ s ⦃ Q ⦄ → Ψ ⊢ ⦃ fst Ψ l ⦄ l :; s ⦃ Q ⦄.
Proof.
  intros Hax A d k m d5 k5 s5 m5 p Hnf. revert d m p.
  assert (∀ n d m,
    State d (CItem (l :; □) :: k) s m ⇨{k}^n State d5 k5 s5 m5 →
    down d s →
    (A * dassert_pack Ψ (fst Ψ l) Q d)%A (get_stack k) m →
      k5 = k ∧ up d5 s5 ∧ (A * dassert_pack Ψ (fst Ψ l) Q d5)%A (get_stack k) m5
   ).
   induction n as [n IH] using lt_wf_ind.
   intros d1 m1 p1 ??.
   edestruct (ax_split _ _ Hax [CItem (l :; □)])
     as [n' [d2 [m2 [p2 [? [??]]]]]]; simpl in *; eauto.
   inv_csteps p2 as [| n'' ? S3 ? p2 p3].
    solve_cnf.
   { inv_cstep p2; try solve [simplify_stmt_elem_of].
   * inv_csteps p3; eauto. inv_cstep.
   * inv_csteps p3; eauto. inv_cstep.
   * match goal with
     | _ : State (Goto ?l') _ _ _ ⇨{_}^_ _ |- _ => destruct (decide (l' = l))
     end; simpl in *; subst.
    + inv_csteps p3 as [| n''' ? S4 ? p3 p4].
         solve_cnf.
        inv_cstep. eapply (IH n'''); eauto. omega.
    + inv_csteps p3. simplify_elem_of. inv_cstep. }
  intros d m p ??.
  destruct (rtc_nsteps p) as [n pn]. inv_csteps pn.
   destruct d5; try contradiction; simpl in *; simplify_elem_of; solve_cnf.
  inv_cstep; eauto.
Qed.

Lemma ax_comp Ψ sl sr P P' Q :
  Ψ ⊢ ⦃ P ⦄ sl ⦃ P' ⦄ → 
  Ψ ⊢ ⦃ P' ⦄ sr ⦃ Q ⦄ →
  Ψ ⊢ ⦃ P ⦄ sl ;; sr ⦃ Q ⦄.
Proof.
  intros Haxl Haxr A d k m d5 k5 s5 m5 p Hnf. revert d m p.
  assert (∀ n d m,
    (State d (CItem (□ ;; sr) :: k) sl m ⇨{k}^n State d5 k5 s5 m5 
      ∧ down d sl
      ∧ (A * dassert_pack Ψ P P' d)%A (get_stack k) m)
    ∨ (State d (CItem (sl ;; □) :: k) sr m ⇨{k}^n State d5 k5 s5 m5
      ∧ down d sr
      ∧ (A * dassert_pack Ψ P' Q d)%A (get_stack k) m) →
    k5 = k ∧ up d5 s5 ∧ (A * dassert_pack Ψ P Q d5)%A (get_stack k) m5
   ).
   induction n as [n IH] using lt_wf_ind.
   intros d1 m1 [[p1 [??]] | [p1 [??]]].
    edestruct (ax_split _ _ Haxl [CItem (□ ;; sr)])
      as [n' [d2 [m2 [p2 [? [??]]]]]]; simpl in *; eauto.
    inv_csteps p2 as [| n'' ? S3 ? p2 p3].
     solve_cnf.
    { inv_cstep p2; try solve [simplify_stmt_elem_of].
    * eapply (IH n''); eauto.
    * inv_csteps p3; eauto. inv_cstep.
    * match goal with
      | _ : State (Goto ?l') _ _ _ ⇨{_}^_ _ |- _ => destruct (decide (l ∈ labels sr))
      end; simpl in *; subst.
     + inv_csteps p3 as [| n''' ? S4 ? p3 p4].
          solve_cnf.
         inv_cstep. eapply (IH n'''); eauto. omega.
     + inv_csteps p3. simplify_elem_of. inv_cstep. }
   edestruct (ax_split _ _ Haxr [CItem (sl ;; □)])
     as [n' [d2 [m2 [p2 [? [??]]]]]]; simpl in *; eauto.
   inv_csteps p2 as [| n'' ? S3 ? p2 p3].
    solve_cnf.
   { inv_cstep p2; try solve [simplify_stmt_elem_of].
   * inv_csteps p3; eauto. inv_cstep.
   * inv_csteps p3; eauto. inv_cstep.
   * match goal with
     | _ : State (Goto ?l') _ _ _ ⇨{_}^_ _ |- _ => destruct (decide (l ∈ labels sl))
     end; simpl in *; subst.
    + inv_csteps p3 as [| n''' ? S4 ? p3 p4].
         solve_cnf.
        inv_cstep. eapply (IH n'''); eauto. omega.
    + inv_csteps p3. simplify_elem_of. inv_cstep. }
  intros d m p ??.
  destruct (rtc_nsteps p) as [n pn]. inv_csteps pn.
   destruct d5; try contradiction; simpl in *; simplify_elem_of; solve_cnf.
  inv_cstep; eauto.
Qed.

Lemma ax_if Ψ e sl sr P Q :
  Ψ ⊢ ⦃ P ∧ ∃ v, e⇓v ∧ ⌜ val_true v ⌝ ⦄ sl ⦃ Q ⦄ → 
  Ψ ⊢ ⦃ P ∧ ∃ v, e⇓v ∧ ⌜ val_false v ⌝ ⦄ sr ⦃ Q ⦄ → 
  Ψ ⊢ ⦃ P ∧ e⇓- ⦄ IF e then sl else sr ⦃ Q ⦄.
Proof.
  intros Haxl Haxr A d k m d5 k5 s5 m5 p Hnf. revert d m p.
  assert (∀ n d m,
    (State d (CItem (IF e then □ else sr) :: k) sl m ⇨{k}^n State d5 k5 s5 m5 
      ∧ down d sl
      ∧ (A * dassert_pack Ψ (P ∧ ∃ v, e⇓v ∧ ⌜ val_true v ⌝) Q d)%A (get_stack k) m)
    ∨ (State d (CItem (IF e then sl else □) :: k) sr m ⇨{k}^n State d5 k5 s5 m5
      ∧ down d sr
      ∧ (A * dassert_pack Ψ (P ∧ ∃ v, e⇓v ∧ ⌜ val_false v ⌝) Q d)%A (get_stack k) m) →
    k5 = k ∧ up d5 s5 ∧ (A * dassert_pack Ψ (P ∧ e⇓-) Q d5)%A (get_stack k) m5
   ) as help.
   induction n as [n IH] using lt_wf_ind.
   intros d1 m1 [[p1 [??]] | [p1 [??]]].
    edestruct (ax_split _ _ Haxl [CItem (IF e then □ else sr)])
      as [n' [d2 [m2 [p2 [? [??]]]]]]; simpl in *; eauto.
    inv_csteps p2 as [| n'' ? S3 ? p2 p3].
     solve_cnf.
    { inv_cstep p2; try solve [simplify_stmt_elem_of].
    * inv_csteps p3; eauto. inv_cstep.
    * inv_csteps p3; eauto. inv_cstep.
    * match goal with
      | _ : State (Goto ?l') _ _ _ ⇨{_}^_ _ |- _ => destruct (decide (l ∈ labels sr))
      end; simpl in *; subst.
     + inv_csteps p3 as [| n''' ? S4 ? p3 p4].
          solve_cnf.
         inv_cstep. eapply (IH n'''); eauto. omega.
     + inv_csteps p3. simplify_elem_of. inv_cstep. }
   edestruct (ax_split _ _ Haxr [CItem (IF e then sl else □)])
     as [n' [d2 [m2 [p2 [? [??]]]]]]; simpl in *; eauto.
   inv_csteps p2 as [| n'' ? S3 ? p2 p3].
    solve_cnf.
   { inv_cstep p2; try solve [simplify_stmt_elem_of].
   * inv_csteps p3; eauto. inv_cstep.
   * inv_csteps p3; eauto. inv_cstep.
   * match goal with
     | _ : State (Goto ?l') _ _ _ ⇨{_}^_ _ |- _ => destruct (decide (l ∈ labels sl))
     end; simpl in *; subst.
    + inv_csteps p3 as [| n''' ? S4 ? p3 p4].
         solve_cnf.
        inv_cstep. eapply (IH n'''); eauto. omega.
    + inv_csteps p3. simplify_elem_of. inv_cstep. }
  intros d m p ? Hpre.
  destruct (rtc_nsteps p) as [n pn].
  destruct d; simpl in *; try contradiction.
  * destruct Hpre as [m1 [m2 [? [? [? [? [v ?]]]]]]]; subst.
     inv_csteps pn.
      destruct (val_true_false_dec v); solve_cnf.
     inv_cstep; simplify_assert_expr;
      eapply help; [left | right]; clear help Haxl Haxr; intuition eauto; solve_assert.
  * inv_csteps pn.
      simplify_elem_of; solve_cnf.
     inv_cstep; eauto.
Qed.

Lemma ax_block_packed Ppack s :
  ax s (dassert_map (λ P, P↑* (O↦ -))%A Ppack) → ax (SBlock s) Ppack.
Proof.
  intros Hax A d k m d5 k5 s5 m5 p Hnf. revert d m p.
  assert (∀ n d m b v,
    is_free b m →
    State d (CBlock b :: k) s (<[b:=v]>m) ⇨{k}^n State d5 k5 s5 m5 →
    down d s →
    (A * Ppack d)%A (get_stack k) m →
      k5 = k ∧ up d5 s5 ∧ (A * Ppack d5)%A (get_stack k) m5
   ).
   intros n d1 m1 b v ? p1 ??.
   edestruct (ax_split _ _ Hax [CBlock b] n (assert_inc_stack A))
     as [n' [d3 [m3 [p3 [? [Hpost ?]]]]]]; simpl in *; eauto.
    rewrite dassert_map_spec.
    rewrite (associative assert_sep), <-assert_inc_stack_sep_distr.
    now apply assert_alloc.
   rewrite dassert_map_spec in Hpost.
   rewrite (associative assert_sep), <-assert_inc_stack_sep_distr in Hpost.
   apply assert_free in Hpost.
   inv_csteps p3 as [| ???? p3 p4].
    solve_cnf.
   { inv_cstep p3; try solve [simplify_stmt_elem_of].
   * inv_csteps p4. intuition. inv_cstep.
   * inv_csteps p4. intuition. inv_cstep.
   * inv_csteps p4. intuition. inv_cstep. }
  intros d m p ? Hpre.
  destruct (rtc_nsteps p) as [n pn].
  inv_csteps pn.
   solve_cnf.
  inv_cstep; eauto.
Qed.

Lemma ax_block J R P Q s :
  (λ l, J l↑ * (O↦ -), λ v, R v↑ * (O↦ -)) ⊢ ⦃ P↑ * (O↦ -) ⦄ s ⦃ Q↑ * (O↦ -) ⦄ →
  (J,R) ⊢ ⦃ P ⦄ SBlock s ⦃ Q ⦄.
Proof. intros. now apply ax_block_packed. Qed.
