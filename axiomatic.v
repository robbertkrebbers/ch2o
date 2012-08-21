Require Export assertions smallstep.
Local Open Scope nat_scope.

Section axiomatic.
Context (δ : fenv).

Definition ax_loc := stack → mem → location → Prop.

Inductive ax_path (Ploc : ax_loc) (k : ctx) (mr : mem) : state → Prop :=
  | ax_further ml' loc' k' :
     mem_disjoint ml' mr →
     red (δ⇒s{k}) (State k' loc' (ml' ∪ mr)) →
     ax_path Ploc k mr (State k' loc' (ml' ∪ mr))
  | ax_done ml' loc' :
     Ploc (get_stack k) ml' loc' →
     mem_disjoint ml' mr →
     ax_path Ploc k mr (State k loc' (ml' ∪ mr)).

Definition ax (n : nat) (Ploc : ax_loc) (loc : location)
    (k : ctx) (ml mr : mem) (S' : state) : Prop :=
  mem_disjoint ml mr →
  δ ⊢ State k loc (ml ∪ mr) ⇒s{k}^n S' →
  ax_path Ploc k mr S'.

Lemma ax_weaken n1 n2 Pd loc k ml mr S :
  n1 ≤ n2 → ax n2 Pd loc k ml mr S → ax n1 Pd loc k ml mr S.
Proof. unfold ax. eauto using bsteps_weaken. Qed.

Inductive ax_splitting (n : nat) (Ploc : ax_loc)
     (loc : location) (l k : ctx) (ml mr : mem) : state → Prop :=
  | ax_splitting_further k'' loc'' ml'' :
     mem_disjoint ml'' mr →
     red (δ⇒s{l ++ k}) (State k'' loc'' (ml'' ∪ mr)) →
     ax_splitting n Ploc loc l k ml mr (State k'' loc'' (ml'' ∪ mr))
  | ax_splitting_done ml' loc' S'' :
     Ploc (get_stack (l ++ k)) ml' loc' →
     mem_disjoint ml' mr →
     δ ⊢ State (l ++ k) loc (ml ∪ mr) ⇒s{l ++ k}^n
         State (l ++ k) loc' (ml' ∪ mr) →
     δ ⊢ State (l ++ k) loc' (ml' ∪ mr) ⇒s{k}^n S'' →
     ax_splitting n Ploc loc l k ml mr S''.

Lemma ax_split n Ploc loc l k ml mr S'' :
  (∀ S, ax n Ploc loc (l ++ k) ml mr S) →
  mem_disjoint ml mr →
  δ ⊢ State (l ++ k) loc (ml ∪ mr) ⇒s{k}^n S'' →
  ax_splitting n Ploc loc l k ml mr S''.
Proof.
  intros Hax ? p1.
  destruct (cstep_subctx_cut δ n l k _ _ p1) as [p | [S' [p2 [p3 ?]]]].
  * eauto with list.
  * feed destruct (Hax S'') as [ml'' | ml'' loc'' P]; auto.
    + now left.
    + now right with ml'' loc''; intuition.
  * feed destruct (Hax S') as [ml' | ml' loc' P]; auto.
    + contradiction.
    + now right with ml' loc'.
Qed.

Record fassert := FAssert {
  fcommon : Type;
  fpre : fcommon → list N → assert;
  fpost : fcommon → list N → option N → assert;
  fpre_stack_indep c vs : StackIndep (fpre c vs);
  fpost_stack_indep c vs mv : StackIndep (fpost c vs mv)
}.
Add Printing Constructor fassert.
Existing Instance fpre_stack_indep.
Existing Instance fpost_stack_indep.
Notation fassert_env := (Nmap fassert).

Definition fpre_call (Pf : fassert)
  (c : fcommon Pf) : list expr → assert := assert_call (fpre Pf c).
Definition fpost_call (Pf : fassert)
  (c : fcommon Pf) : assert := (∃ vs mv, fpost Pf c vs mv)%A.

Inductive ax_fun_loc (Pf : fassert) (c : fcommon Pf) (vs : list N)
    (ρ : stack) (m : mem) : location → Prop :=
  | make_lassert_fun v :
     fpost Pf c vs v ρ m →
     ax_fun_loc Pf c vs ρ m (Return v).
Definition ax_funs (n : nat) (Δ : fassert_env) : Prop :=
  ∀ f Pf c vs ml mr k S',
    Δ !! f = Some Pf →
    fpre Pf c vs (get_stack k) ml →
    ax n (ax_fun_loc Pf c vs) (Call f vs) k ml mr S'.

Lemma ax_funs_weaken n1 n2 Δ :
  n1 ≤ n2 → ax_funs n2 Δ → ax_funs n1 Δ.
Proof. unfold ax_funs. eauto using ax_weaken. Qed.

Lemma ax_funs_S n Δ :
  ax_funs (S n) Δ → ax_funs n Δ.
Proof. apply ax_funs_weaken. auto with arith. Qed.
Hint Resolve ax_funs_S : ax.

Definition dassert := direction → assert.
Definition dassert_pack (P : assert) (Q : assert) (R : option N → assert)
  (J : label → assert) : dassert := direction_rect (λ _, assert) P Q R J.
Definition dassert_pack_top (P : assert) (R : option N → assert) : dassert :=
  dassert_pack P (R None) R (λ _, False%A).

Lemma dassert_pack_proper: Proper 
  ((≡) ==> (≡) ==> pointwise_relation _ (≡) ==> pointwise_relation _ (≡)
     ==> (=) ==> (≡)) dassert_pack.
Proof. intros ????????????? [] ?; subst; firstorder. Qed.

Definition dassert_map (f : assert → assert) (Pd : dassert) : dassert := λ d,
  match d with
  | In => f (Pd In)
  | Out => f (Pd Out)
  | Top mv => f (Pd (Top mv))
  | Jump l => f (Pd (Jump l))
  end.
Lemma dassert_map_spec f P d : dassert_map f P d = f (P d).
Proof. now destruct d. Qed.

Inductive ax_stmt_loc (Pd : dassert)
    (ρ : stack) (m : mem) : location → Prop :=
  | make_lassert_stmt d s :
     up d s →
     Pd d ρ m →
     ax_stmt_loc Pd ρ m (Stmt d s).
Definition ax_stmt (Δ : fassert_env) s (Pd : dassert) : Prop :=
  ∀ n k d ml mr S',
    ax_funs n Δ →
    down d s →
    Pd d (get_stack k) ml →
    ax n (ax_stmt_loc Pd) (Stmt d s) k ml mr S'.

Notation "Δ ; J ; R ⊢ {{ P }} s {{ Q }}" :=
  (ax_stmt Δ s%S (dassert_pack P%A Q%A R%A J%A))
  (J at level 10, R at level 10, at level 80, Q at next level,
   format "Δ ;  J ;  R  ⊢  {{  P  }}  s  {{  Q  }}").
Notation "Δ ⊢ {{ P }} s {{ R }}" :=
  (ax_stmt Δ s%S (dassert_pack_top P%A R%A))
  (J at level 10, at level 80, Q at next level, 
   format "Δ  ⊢  {{  P  }}  s  {{  R  }}").

Lemma ax_stmt_sound s Pd d m d' k' s' m' :
  ax_stmt ∅ s Pd →
    down d s →
    Pd d [] m →
    δ ⊢ State [] (Stmt d s) m ⇒s* State k' (Stmt d' s') m' →
    nf (δ⇒s) (State k' (Stmt d' s') m') →
  k' = [] 
  ∧ up d' s' 
  ∧ Pd d' [] m'.
Proof.
  intros Hax ?? p Hnf.
  apply rtc_bsteps in p. destruct p as [n p].
  feed inversion (Hax n [] d m ∅ (State k' (Stmt d' s') m'))
    as [|?? [d'' s'' ??]]; simplify_eqs; auto with mem.
  * repeat intro. simplify_map.
  * rewrite (right_id_eq ∅ _).
    now eapply (bsteps_subrel (δ⇒s) (δ⇒s{ [] }) _).
  * destruct Hnf. now apply (red_subrel (δ⇒s{ [] }) _ _).
  * rewrite (right_id_eq ∅ _). now auto.
Qed.

Lemma ax_stmt_weak_packed Δ Pd Pd' s :
  (∀ d, down d s → (Pd' d → Pd d)%A) →
  (∀ d, up d s → (Pd d → Pd' d)%A) →
  ax_stmt Δ s Pd →
  ax_stmt Δ s Pd'.
Proof.
  intros Hdown Hup Hax n k d ml mr S' ???? p.
  feed destruct (Hax n k d ml mr S') as [|ml' ? [????]]; auto.
  * apply Hdown; auto.
  * now left.
  * right.
    + constructor; auto.
      apply Hup; auto.
      now erewrite cstep_bsteps_preserves_stmt by eauto.
    + easy.
Qed.

Lemma ax_stmt_weak_pre Δ J R P P' Q s : 
  P' ⊆ P →
  Δ; J; R ⊢ {{ P }} s {{ Q }} →
  Δ; J; R ⊢ {{ P' }} s {{ Q }}.
Proof. intro. apply ax_stmt_weak_packed; intros []; solve_assert. Qed.
Lemma ax_stmt_weak_post Δ J R P Q Q' s : 
  Q ⊆ Q' →
  Δ; J; R ⊢ {{ P }} s {{ Q }} →
  Δ; J; R ⊢ {{ P }} s {{ Q' }}.
Proof. intro. apply ax_stmt_weak_packed; intros []; solve_assert. Qed.

Lemma ax_stmt_frame_packed Δ A Pd s :
  ax_stmt Δ s Pd →
  ax_stmt Δ s (dassert_map (λ P, P * A)%A Pd).
Proof.
  intros Hax n k d ml mr S' ?? Hpre ? p.
  rewrite dassert_map_spec in Hpre.
  destruct Hpre as [m2 [m3 [? [? [??]]]]]; subst.
  feed destruct (Hax n k d m2 (m3 ∪ mr) S') as [|ml2' ? []]; auto.
  * now simplify_mem_disjoint.
  * now rewrite (associative_eq _).
  * rewrite (associative_eq _). left.
    + now simplify_mem_disjoint.
    + now rewrite <-(associative_eq _).
  * rewrite (associative_eq _). right.
    + constructor; auto.
      rewrite dassert_map_spec.
      exists ml2' m3. intuition. now simplify_mem_disjoint.
    + now simplify_mem_disjoint.
Qed.

Lemma ax_stmt_frame Δ J R A P Q s :
  Δ; J; R ⊢ {{ P }} s {{ Q }} →
  Δ; (λ l, J l * A); (λ v, R v * A) ⊢ {{ P * A }} s {{ Q * A }}.
Proof. apply ax_stmt_frame_packed. Qed.

Lemma ax_stmt_and Δ J R P Q Q' s :
  Δ; J; R ⊢ {{ P }} s {{ Q }} →
  Δ; J; R ⊢ {{ P }} s {{ Q' }} →
  Δ; J; R ⊢ {{ P }} s {{ Q ∧ Q' }}.
Proof.
  intros Hax1 Hax2 n k d ml mr S' ???? p.
  feed destruct (Hax1 n k d ml mr S') as [|ml' ? [d' s' ??]]; auto.
    now destruct d; intuition.
   now left.
  feed inversion (Hax2 n k d ml mr (State k (Stmt d' s') (ml' ∪ mr)))
      as [|ml'' ? [d'' s'' ??]]; auto.
    now destruct d; intuition.
   now left.
  simplify_eqs. right.
  * constructor; auto.
    assert (ml' = ml'').
    { now apply mem_union_cancel_l with mr. }
    subst. destruct d'; intuition auto. now split.
  * easy.
Qed.

Lemma ax_call J R Δ f es Pf (c : fcommon Pf) :
  Δ !! f = Some Pf →
  Δ; J; R ⊢ {{ fpre_call Pf c es }} call None f es {{ fpost_call Pf c }}.
Proof.
  intros Hf n k d ml mr S' HΔ ? Hpre ? p.

  destruct d; try contradiction.
  apply assert_call_correct in Hpre.
  destruct Hpre as [vs [??]].

  inv_csteps p as [| n' ??? p1 p2].
  { left. easy. solve_cred. }
  inv_cstep p1.
  simplify_assert_expr.

  feed destruct (ax_split (S n')
    (ax_fun_loc Pf c vs)
    (Call f vs)
    [CCall None f es] k
    ml mr S') as [ml' | ml' ?? [? Hpost] ? _ p3].

  * intros. apply HΔ. easy. now apply (stack_indep (get_stack k)).
  * easy.
  * now apply bsteps_S.

  * left. easy. now apply (red_subrel (δ⇒s{CCall None f es :: k}) _ _).
  * inv_csteps p3 as [| n'' ??? p3 p4 ].
    { left. easy. solve_cred. }
    inv_cstep p3. last_cstep p4.
    right.
    + constructor; auto.
      eexists _,_. apply (stack_indep []), Hpost.
    + easy.
Qed.

Lemma ax_new_fun Δ f Pf sf Pd s :
  δ !! f = Some sf →
  (∀ c vs,
    <[f:=Pf]>Δ ⊢ {{ Π imap (λ i v, var i ↦ val v) vs * fpre Pf c vs }}
     sf
    {{ λ v, Π imap (λ i _, var i ↦ -) vs * fpost Pf c vs v }}) →
  ax_stmt (<[f:=Pf]>Δ) s Pd →
  ax_stmt Δ s Pd.
Proof.
  intros Hf Haxf. revert s.
  cut (∀ n c vs ml mr m' k bs S',
   ax_funs n (<[f:=Pf]> Δ) →
   mem_disjoint ml mr →
   alloc_params (ml ∪ mr) bs vs m' →
   (fpre Pf c vs) (get_stack k) ml →
   δ ⊢ State (CParams bs :: k) (Stmt In sf) m' ⇒s{k}^n S' →
   ax_path (ax_fun_loc Pf c vs) k mr S').

  { intros help s Hax n k d ml mr S' HΔ.
    eapply Hax. clear d s Pd k ml mr S' Hax.
   induction n as [n IH] using lt_wf_ind.
   intros f' Pf' c vs ml mr k S' ??? p.

   destruct (decide (f' = f)); simplify_map; [| eapply HΔ; eauto ].
   inv_csteps p as [| n' ??? p1 p2].
   { left. easy. solve_cred. }

   inv_cstep p1.
   apply (ax_funs_weaken n') in HΔ; [| omega].
   eapply help; eauto. congruence. }

  intros n c vs ml mr m' k bs S3 ?? Hparams Hpre p1.

  apply alloc_params_insert_list in Hparams.
  destruct Hparams as [? [??]]; subst.
  rewrite mem_insert_list_union, (associative_eq (∪)) in p1.
  simplify_is_free.

  feed destruct (ax_split n
    (ax_stmt_loc (dassert_pack_top
      (Π imap (λ i v, var i ↦ val v) vs * fpre Pf c vs)
      (λ mv, Π imap (λ i _, var i ↦ -) vs * fpost Pf c vs mv)))%A
    (Stmt In sf)
    [CParams bs] k
    (list_to_map (zip bs vs) ∪ ml)
    mr S3) as [ml' | ml' ? S2 [??? Hpost] ? _ p2].

  * intros. apply Haxf; auto.
    simpl. rewrite <-mem_insert_list_union.
    apply assert_alloc_params_alt; auto.
  * simplify_mem_disjoint.
    apply mem_disjoint_list_to_map_zip_l; eauto with mem.
  * easy.

  * left. easy. now apply (red_subrel (δ⇒s{CParams bs :: k}) _ _).
  * inv_csteps p2 as [| n3 ? S3 ? p2 p3 ].
    { left. easy. solve_cred. }
    inv_cstep p2.
    + last_cstep p3.
      rewrite mem_union_delete_list, (delete_list_notin mr)
       by now apply is_free_list_free.
      right.
      - constructor. apply assert_free_params with vs; eauto with mem.
      - now auto with mem.
    + last_cstep p3.
      rewrite mem_union_delete_list, (delete_list_notin mr)
       by now apply is_free_list_free.
      right.
      - constructor. apply assert_free_params with vs; eauto with mem.
      - now auto with mem.
Qed.

Lemma ax_skip Δ J R P : Δ; J; R ⊢ {{ P }} skip {{ P }}.
Proof.
  intros n k d ml mr S' ???? p.
  inv_csteps p as [| ???? p1 p2].
  { left. easy. solve_cred. }
  inv_cstep p1. last_cstep p2.
  right. now constructor. easy.
Qed.

Lemma ax_goto Δ J R Q l : Δ; J; R ⊢ {{ J l }} goto l {{ Q }}.
Proof.
  intros n k d ml mr S' ???? p.
  inv_csteps p as [| ???? p1 p2].
  { left. easy. solve_cred. }
  inv_cstep p1. last_cstep p2.
  right. constructor; simplify_elem_of. easy.
Qed.

Lemma ax_return_None Δ J R Q :
  Δ; J; R ⊢ {{ R None }} ret None {{ Q }}.
Proof.
  intros n k d ml mr S' ???? p.
  inv_csteps p as [| ???? p1 p2 ].
  { left. easy. solve_cred. }
  inv_cstep p1. last_cstep p2.
  right. now constructor. easy.
Qed.

Lemma ax_return_Some Δ J R e Q :
  Δ; J; R ⊢ {{ ∃ v, e⇓v ∧ R (Some v) }} ret (Some e) {{ Q }}.
Proof.
  intros n k d ml mr S' ?? Hpre ? p.
  destruct d; try contradiction.
  destruct Hpre as [v [??]]. simplify_assert_expr.
  inv_csteps p as [| ???? p1 p2 ].
  { left. easy. solve_cred. }
  inv_cstep p1. last_cstep p2.
  simplify_assert_expr.
  right. now constructor. easy.
Qed.

Lemma ax_assign Δ J R e1 e2 Q :
  Δ; J; R ⊢ {{ ∃ a v, e1⇓a ∧ e2⇓v ∧ load (val a)⇓- ∧ <[a:=v]>Q }} e1 ::= e2 {{ Q }}.
Proof.
  intros n k d ml mr S' ?? Hpre ? p.
  destruct d; try contradiction.
  inv_csteps p as [| ???? p1 p2 ].
  { left. easy. destruct Hpre as [a [v [? [? [[??] ?]]]]].
    simplify_assert_expr.
    assert (is_writable (ml ∪ mr) a).
    { do 2 red. eauto with mem. }
    solve_cred. }
  inv_cstep p1. last_cstep p2.
  destruct Hpre as [a' [v' [? [? [[??] ?]]]]].
  simplify_assert_expr.
  rewrite mem_union_insert_l.
  right.
  * now constructor.
  * simplify_mem_disjoint. eapply mem_disjoint_Some_l; eauto.
Qed.

Lemma ax_block_packed Δ Pd s :
  ax_stmt Δ s (dassert_map (λ P, var O ↦ - * P↑)%A Pd) →
  ax_stmt Δ (block s) Pd.
Proof.
  intros Hax n k d ml mr S5. revert n d ml.
  cut (∀ n d ml b v,
   ax_funs n Δ →
   mem_disjoint ml mr →
   is_free (ml ∪ mr) b →
   δ ⊢ State (CBlock b :: k) (Stmt d s) (<[b:=v]>(ml ∪ mr)) ⇒s{k}^n S5 →
   down d s →
   Pd d (get_stack k) ml →
   ax_path (ax_stmt_loc Pd) k mr S5).

  { intros help n d ml ???? p.
    inv_csteps p as [| n' ??? p1 p2].
    { left. easy. solve_cred. }
    inv_cstep p1; eapply (help n'); eauto with ax. }

  intros n1 d1 ml1 b v ??? p1 ? Hpre.
  simplify_is_free.
  rewrite mem_union_insert_l in p1.

  feed destruct (ax_split n1
    (ax_stmt_loc (dassert_map (λ P, var O ↦ - * P↑)%A Pd))
    (Stmt d1 s) [CBlock b] k (<[b:=v]>ml1) mr S5)
    as [ml2 | ml2 ? S5 [d2 s2 ? Hpost] ? p p2]; auto.

  * intros. apply Hax; auto. 
    rewrite dassert_map_spec. now apply assert_alloc.
  * simplify_mem_disjoint.

  * left. easy. solve_cred.
  * apply cstep_bsteps_preserves_stmt in p. subst s2.
    rewrite dassert_map_spec in Hpost. simpl in Hpost.
    apply assert_free in Hpost.
    inv_csteps p2 as [| n3 ? S3 ? p2 p3].
    { left. easy. solve_cred. }

    inv_cstep p2; try solve [simplify_stmt_elem_of].
    + last_cstep p3. rewrite mem_union_delete, (delete_notin mr).
      right. now constructor. simplify_mem_disjoint. easy.
    + last_cstep p3. rewrite mem_union_delete, (delete_notin mr).
      right. now constructor. simplify_mem_disjoint. easy.
    + last_cstep p3. rewrite mem_union_delete, (delete_notin mr).
      right. now constructor. simplify_mem_disjoint. easy.
Qed.

Lemma ax_block Δ J R P Q s :
  Δ; (λ l, var O ↦ - * J l↑); (λ v, var O ↦ - * R v↑) ⊢
    {{ var O ↦ - * P↑ }} s {{ var O ↦ - * Q↑ }} →
  Δ; J; R ⊢ {{ P }} SBlock s {{ Q }}.
Proof. intros. now apply ax_block_packed. Qed.

Lemma ax_label Δ J R l s Q :
  Δ; J; R ⊢ {{ J l }} s {{ Q }} →
  Δ; J; R ⊢ {{ J l }} l :; s {{ Q }}.
Proof.
  intros Hax n k d ml mr S5. revert n d ml.
  cut (∀ n d ml,
   ax_funs n Δ →
   mem_disjoint ml mr →
   δ ⊢ State (CItem (l :; □) :: k) (Stmt d s) (ml ∪ mr) ⇒s{k}^n S5 →
   down d s →
   dassert_pack (J l) Q R J d (get_stack k) ml →
   ax_path (ax_stmt_loc (dassert_pack (J l) Q R J)) k mr S5).

  { intros help n d ml ???? p.
    inv_csteps p as [| n' ??? p1 p2].
    { left. easy. destruct d; simplify_elem_of; solve_cred. }
    inv_cstep p1; eapply (help n'); eauto with ax. }

  induction n as [n1 IH] using lt_wf_ind.
  intros d1 ml1 ?? p1 ??.

  feed destruct (ax_split n1
    (ax_stmt_loc (dassert_pack (J l) Q R J))
    (Stmt d1 s) [CItem (l :;□)] k ml1 mr S5)
    as [ml2 | ml2 ? S5 [d2 s2 ??] ? p p2]; auto.
  { left. easy. solve_cred. }

  apply cstep_bsteps_preserves_stmt in p. subst s2.
  inv_csteps p2 as [| n3 ? S3 ? p2 p3].
  { left. easy. solve_cred. }

  inv_cstep p2; try solve [simplify_stmt_elem_of].
  * last_cstep p3. eright. constructor. easy. easy. easy.
  * last_cstep p3. eright. constructor. easy. easy. easy.
  * match goal with
    | _ : ?l' ∉ labels s |- _ => destruct (decide (l' = l))
    end; subst.
    + inv_csteps p3 as [| n4 ? S4 ? p3 p4].
      { left. easy. solve_cred. }
      inv_cstep p3. eapply (IH n4); eauto with ax.
    + last_cstep p3. right. constructor; simplify_elem_of. easy.
Qed.

Lemma ax_loop Δ J R P Q s :
  Δ; J; R ⊢ {{ P }} s {{ P }} →
  Δ; J; R ⊢ {{ P }} loop s {{ Q }}.
Proof.
  intros Hax n k d ml mr S5. revert n d ml.
  cut (∀ n d ml,
   ax_funs n Δ →
   mem_disjoint ml mr →
   δ ⊢ State (CItem (loop □) :: k) (Stmt d s) (ml ∪ mr) ⇒s{k}^n S5 →
   down d s →
   dassert_pack P P R J d (get_stack k) ml →
   ax_path (ax_stmt_loc (dassert_pack P Q R J)) k mr S5).

  { intros help n d ml ???? p.
    inv_csteps p as [| n' ??? p1 p2].
    { left. easy. solve_cred. }
    inv_cstep; eapply (help n'); eauto with ax. }

  induction n as [n1 IH] using lt_wf_ind.
  intros d1 ml1 ?? p1 ??.

  feed destruct (ax_split n1
    (ax_stmt_loc (dassert_pack P P R J))
    (Stmt d1 s) [CItem (loop □)] k ml1 mr S5)
    as [ml2 | ml2 ? S5 [d2 s2 ??] ? p p2]; auto.
  { left. easy. solve_cred. }

  apply cstep_bsteps_preserves_stmt in p. subst s2.
  inv_csteps p2 as [| n3 ? S3 ? p2 p3].
  { left. easy. solve_cred. }
  inv_cstep p2; try solve [simplify_stmt_elem_of].
  * inv_csteps p3 as [| n4 ? S4 ? p3 p4].
    { left. easy. solve_cred. }
    inv_cstep p3. eapply (IH n4); eauto with ax.
  * last_cstep p3. right. now constructor. easy.
  * last_cstep p3. right. now constructor. easy.
Qed.

Lemma ax_comp Δ J R sl sr P P' Q :
  Δ; J; R ⊢ {{ P }} sl {{ P' }} → 
  Δ; J; R ⊢ {{ P' }} sr {{ Q }} →
  Δ; J; R ⊢ {{ P }} sl ;; sr {{ Q }}.
Proof.
  intros Haxl Haxr n k d ml mr S5. revert n d ml.
  cut (∀ n d ml,
   ax_funs n Δ →
   mem_disjoint ml mr →
   (δ ⊢ State (CItem (□ ;; sr) :: k) (Stmt d sl) (ml ∪ mr) ⇒s{k}^n S5
     ∧ down d sl
     ∧ dassert_pack P P' R J d (get_stack k) ml)
   ∨ (δ ⊢ State (CItem (sl ;; □) :: k) (Stmt d sr) (ml ∪ mr) ⇒s{k}^n S5
     ∧ down d sr
     ∧ dassert_pack P' Q R J d (get_stack k) ml) →
   ax_path (ax_stmt_loc (dassert_pack P Q R J)) k mr S5).

  { intros help n d ml ???? p.
    inv_csteps p as [| n' ??? p1 p2].
    { left. easy. destruct d; simplify_elem_of; solve_cred. }
    inv_cstep; eapply (help n'); eauto with ax. }

  induction n as [n1 IH] using lt_wf_ind.
  intros d1 ml1 ?? [[p1 [??]] | [p1 [??]]].

  * feed destruct (ax_split n1
      (ax_stmt_loc (dassert_pack P P' R J))
      (Stmt d1 sl) [CItem (□;;sr)] k ml1 mr S5)
      as [ml2 | ml2 ? S5 [d2 s2 ??] ? p p2]; auto.
    { left. easy. solve_cred. }

    apply cstep_bsteps_preserves_stmt in p. subst s2.
    inv_csteps p2 as [| n3 ? S3 ? p2 p3].
    { left. easy. solve_cred. }

    inv_cstep p2; try solve [simplify_stmt_elem_of].
    + eapply (IH n3); intuition eauto with ax.
    + last_cstep p3. right. now constructor. easy.
    + match goal with
      | _ : ?l ∉ labels sl |- _ => destruct (decide (l ∈ labels sr))
      end; subst.
      - inv_csteps p3 as [| n4 ? S4 ? p3 p4].
        { left. easy. solve_cred. }
        inv_cstep p3. eapply (IH n4); intuition eauto with ax.
      - last_cstep p3. right. constructor; simplify_elem_of. easy.

  * feed destruct (ax_split n1
      (ax_stmt_loc (dassert_pack P' Q R J))
      (Stmt d1 sr) [CItem (sl;;□)] k ml1 mr S5)
      as [ml2 | ml2 ? S5 [d2 s2 ??] ? p p2]; auto.
    { left. easy. solve_cred. }

    apply cstep_bsteps_preserves_stmt in p. subst s2.
    inv_csteps p2 as [| n3 ? S3 ? p2 p3].
    { left. easy. solve_cred. }

    inv_cstep p2; try solve [simplify_stmt_elem_of].
    + last_cstep p3. right. now constructor. easy.
    + last_cstep p3. right. now constructor. easy.
    + match goal with
      | _ : ?l ∉ labels sr |- _ => destruct (decide (l ∈ labels sl))
      end; subst.
      - inv_csteps p3 as [| n4 ? S4 ? p3 p4].
        { left. easy. solve_cred. }
        inv_cstep p3. eapply (IH n4); intuition eauto with ax.
      - last_cstep p3. right. constructor; simplify_elem_of. easy.
Qed.

Lemma ax_if Δ J R e sl sr P Q :
  Δ; J; R ⊢ {{ P ∧ ∃ v, e⇓v ∧ ⌜ val_true v ⌝ }} sl {{ Q }} → 
  Δ; J; R ⊢ {{ P ∧ ∃ v, e⇓v ∧ ⌜ val_false v ⌝ }} sr {{ Q }} → 
  Δ; J; R ⊢ {{ P ∧ e⇓- }} IF e then sl else sr {{ Q }}.
Proof.
  intros Haxl Haxr n k d ml mr S5. revert n d ml.
  cut (∀ n d ml,
   ax_funs n Δ →
   mem_disjoint ml mr →
   (δ ⊢ State (CItem (IF e then □ else sr) :: k) (Stmt d sl) (ml ∪ mr) ⇒s{k}^n S5
     ∧ down d sl
     ∧ dassert_pack (P ∧ ∃ v, e⇓v ∧ ⌜val_true v⌝)%A Q R J d (get_stack k) ml)
   ∨ (δ ⊢ State (CItem (IF e then sl else □) :: k) (Stmt d sr) (ml ∪ mr) ⇒s{k}^n S5
     ∧ down d sr
     ∧ dassert_pack (P ∧ ∃ v, e⇓v ∧ ⌜val_false v⌝)%A Q R J d (get_stack k) ml) →
   ax_path (ax_stmt_loc (dassert_pack (P ∧ e⇓-)%A Q R J)) k mr S5).

  { intros help n [] ml ?? Hpre ? p; try contradiction.
    * destruct Hpre as [? [v ?]].
      inv_csteps p as [| n' ??? p1 p2].
      { left. easy. destruct (val_true_false_dec v); solve_cred. }
      inv_cstep; simplify_assert_expr; eapply (help n');
        eauto with ax; [left|right]; intuition eauto.
      + split. easy. exists v. now split.
      + split. easy. exists v. now split.
    * inv_csteps p as [| n' ??? p1 p2].
      { left. easy. simplify_elem_of; solve_cred. }
      inv_cstep; eapply (help n'); eauto with ax. }

  induction n as [n1 IH] using lt_wf_ind.
  intros d1 ml1 ?? [[p1 [??]] | [p1 [??]]].

  * feed destruct (ax_split n1
      (ax_stmt_loc (dassert_pack (P ∧ ∃ v, e⇓v ∧ ⌜val_true v⌝)%A Q R J))
      (Stmt d1 sl) [CItem (IF e then □ else sr)] k ml1 mr S5)
      as [ml2 | ml2 ? S5 [d2 s2 ??] ? p p2]; auto.
    { left. easy. solve_cred. }

    apply cstep_bsteps_preserves_stmt in p. subst s2.
    inv_csteps p2 as [| n3 ? S3 ? p2 p3].
    { left. easy. solve_cred. }

    inv_cstep p2; try solve [simplify_stmt_elem_of].
    + last_cstep p3. right. now constructor. easy.
    + last_cstep p3. right. now constructor. easy.
    + match goal with
      | _ : ?l ∉ labels sl |- _ => destruct (decide (l ∈ labels sr))
      end; subst.
      - inv_csteps p3 as [| n4 ? S4 ? p3 p4].
        { left. easy. solve_cred. }
        inv_cstep p3. eapply (IH n4); intuition eauto with ax.
      - last_cstep p3. right. constructor; simplify_elem_of. easy.

  * feed destruct (ax_split n1
      (ax_stmt_loc (dassert_pack (P ∧ ∃ v, e⇓v ∧ ⌜val_false v⌝)%A Q R J))
      (Stmt d1 sr) [CItem (IF e then sl else □)] k ml1 mr S5)
      as [ml2 | ml2 ? S5 [d2 s2 ??] ? p p2]; auto.
    { left. easy. solve_cred. }

    apply cstep_bsteps_preserves_stmt in p. subst s2.
    inv_csteps p2 as [| n3 ? S3 ? p2 p3].
    { left. easy. solve_cred. }

    inv_cstep p2; try solve [simplify_stmt_elem_of].
    + last_cstep p3. right. now constructor. easy.
    + last_cstep p3. right. now constructor. easy.
    + match goal with
      | _ : ?l ∉ labels sr |- _ => destruct (decide (l ∈ labels sl))
      end; subst.
      - inv_csteps p3 as [| n4 ? S4 ? p3 p4].
        { left. easy. solve_cred. }
        inv_cstep p3. eapply (IH n4); intuition eauto with ax.
      - last_cstep p3. right. constructor; simplify_elem_of. easy.
Qed.
End axiomatic.
