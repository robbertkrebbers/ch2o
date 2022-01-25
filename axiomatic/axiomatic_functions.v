(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
From Coq Require Import Program.Tactics.
From stdpp Require Import fin_map_dom.
Require Export axiomatic.
Require Import axiomatic_graph axiomatic_expressions_help.

Local Open Scope ctype_scope.

Section axiomatic_functions.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types Δ : memenv K.
Implicit Types δ : funenv K.
Implicit Types e : expr K.
Implicit Types τ σ : type K.
Implicit Types a : addr K.
Implicit Types v : val K.

Arguments assert_holds _ _ _ _ _ _ _ _ _ : simpl never.

Hint Extern 1 (_ ## _) => solve_mem_disjoint: core.
Hint Extern 1 (## _) => solve_mem_disjoint: core.
Hint Extern 1 (sep_valid _) => solve_mem_disjoint: core.
Hint Extern 1 (_ ≤ _) => lia: core.

Hint Resolve Forall_app_2: core.
Hint Immediate memenv_subseteq_forward cmap_valid_memenv_valid: core.
Hint Resolve cmap_empty_valid cmap_erased_empty mem_locks_empty: core.
Hint Resolve cmap_union_valid_2 cmap_erased_union cmap_erase_valid: core.

Hint Immediate ax_disjoint_expr_compose_diagram: core.
Hint Immediate ax_expr_disjoint_compose_diagram: core.
Hint Immediate ax_disjoint_compose_diagram: core.

Hint Immediate val_new_typed perm_full_mapped lockset_empty_valid: core.
Hint Resolve mem_alloc_valid mem_free_valid: core.
Hint Extern 0 (_ ⊢ _ : _) => typed_constructor: core.
Hint Extern 0 (unframe ax_disjoint_cond _ _ _ _ _ _ _) => by constructor: core.
Hint Extern 0 (focus_locks_valid _ _) => by constructor: core.

Definition imap2_go {A B C} (f : nat → A → B → C) :
    nat → list A → list B → list C:=
  fix go (n : nat) (l : list A) (k : list B) :=
  match l, k with
  | [], _ |_, [] => [] | x :: l, y :: k => f n x y :: go (S n) l k
  end.

Lemma assert_alloc_params P Γ Δ δ ρ n m mf os vs τs :
  StackIndep P → ✓ Γ → ✓{Γ,Δ} δ → ✓{Γ,Δ} m → m ## mf → ✓{Δ}* ρ →
  (Γ,Δ) ⊢* vs :* τs → length os = length vs →
  Forall_fresh (dom indexset (m ∪ mf)) os →
  (dom indexset (mem_alloc_list Γ os vs (m ∪ mf)) ∖ dom indexset (m ∪ mf))
    ∩ dom indexset Δ = ∅ →
  assert_holds P Γ Δ δ [] n (cmap_erase m) → ∃ Δ',
  (**i 1.) *) Δ ⊆ Δ' ∧
  (**i 2.) *) (∀ Δ'',
    ✓{Γ,Δ''} (mem_alloc_list Γ os vs m) → Δ ⇒ₘ Δ'' → Δ' ⇒ₘ Δ'') ∧
  (**i 3.) *) ✓{Δ'}* (zip os τs) ∧
  (**i 4.) *) ✓{Γ,Δ'} (mem_alloc_list Γ os vs m) ∧
  (**i 5.) *) mem_alloc_list Γ os vs m ## mf ∧
  (**i 6.) *) mem_alloc_list Γ os vs (m ∪ mf) = mem_alloc_list Γ os vs m ∪ mf ∧
  (**i 7.) *) assert_holds
    (Π imap2_go (λ i v τ,
      var i ↦{false,perm_full} #freeze true v : τ) (length ρ) vs τs ★ P)%A
    Γ Δ' δ (ρ ++ zip os τs) n (cmap_erase (mem_alloc_list Γ os vs m)).
Proof.
  intros ??; rewrite <-Forall2_same_length; intros Hδ Hm Hmmf Hρ Hvs Hos.
  revert Δ ρ τs Hδ Hm Hρ Hvs; induction Hos as [|o v os vs _ ? IH];
    intros Δ ρ [|τ τs]; inversion_clear 5; intros Hdom ?; decompose_Forall_hyps.
  { exists Δ; split_and ?; auto. rewrite (right_id_L [] _).
    rapply (proj2 (left_id (R:=(≡{Γ,δ})) emp (★) P)%A);
      eauto using stack_indep_spec. }
  rewrite mem_dom_alloc in Hdom.
  assert (Δ !! o = None).
  { apply not_elem_of_dom; clear IH; set_solver. }
  assert (Δ ⊆ <[o:=(τ,false)]>Δ) by (by apply insert_subseteq).
  assert (✓{Γ}(<[o:=(τ,false)]>Δ)) by eauto 3 using mem_alloc_memenv_valid,
    cmap_valid_memenv_valid, val_typed_type_valid.
  assert (<[o:=(τ,false)]> Δ ⊢ o : τ) by (by apply mem_alloc_index_typed).
  destruct (IH (<[o:=(τ,false)]>Δ) (ρ ++ [(o,τ)]) τs)
    as (Δ'&?&Hleast&?&?&?&->&HP);
    eauto using assert_weaken, Forall2_impl, val_typed_weaken,
    cmap_valid_weaken, indexes_valid_weaken, funenv_valid_weaken; clear IH.
  { rewrite mem_dom_alloc_list in Hdom |- * by eauto using Forall2_length.
    rewrite dom_insert_L; set_solver. }
  assert (Δ ⊆ Δ') by (by transitivity (<[o:=(τ, false)]> Δ)).
  assert (o ∉ dom indexset m ∧ o ∉ dom indexset mf) as [??].
  { by rewrite <-not_elem_of_union, <-cmap_dom_union. }
  assert (o ∉ dom indexset (mem_alloc_list Γ os vs m)).
  { by rewrite mem_dom_alloc_list, not_elem_of_union, elem_of_list_to_set
      by eauto using Forall2_length. }
  assert (Δ' ⊢ o : τ)
    by eauto using memenv_forward_typed, memenv_subseteq_forward.
  assert (✓{Γ,Δ'} (mem_alloc Γ o false perm_full v (mem_alloc_list Γ os vs m))).
  { eapply mem_alloc_alive_valid; eauto using val_typed_weaken,
      memenv_subseteq_alive, mem_alloc_index_alive. }
  exists Δ'; split_and ?; eauto using mem_alloc_disjoint, mem_alloc_union.
  { intros Δ'' ??; transitivity (<[o:=(τ,false)]> Δ').
    { by rewrite (insert_id Δ' o (τ,false))
        by (by apply lookup_weaken with (<[o:=(τ,false)]> Δ); simpl_map). }
    eapply mem_alloc_forward_least, Hleast;
      eauto using val_typed_weaken, mem_alloc_valid_inv.
    destruct (mem_alloc_valid_index_inv Γ Δ'' (mem_alloc_list Γ os vs m) o
      false perm_full v) as [[??] [??]]; auto; simplify_type_equality.
    rewrite <-(insert_id Δ'' o (τ,false)) by done.
    by apply mem_alloc_memenv_compat. }
  eapply assert_entails_spec with (_ ★ (_ ★ _))%A;
    eauto using indexes_valid_weaken, funenv_valid_weaken.
  { by rewrite (assoc (★)%A). }
  rewrite <-(assoc_L (++)), app_length, Nat.add_1_r in HP.
  destruct (mem_alloc_singleton Γ Δ' (mem_alloc_list Γ os vs m) o
    false perm_full v τ) as (m'&->&?&?); eauto using val_typed_weaken,
    memenv_subseteq_alive, mem_alloc_index_alive;
    simplify_mem_disjoint_hyps.
  erewrite cmap_erase_union, mem_erase_singleton by eauto.
  exists m', (cmap_erase (mem_alloc_list Γ os vs m)); split_and ?; csimpl;
    eauto using assert_weaken, mem_alloc_forward.
  { by rewrite <-cmap_erase_disjoint_le. }
  eexists (addr_top o τ), (freeze true v); split_and ?; auto.
  * typed_constructor. by rewrite fmap_app,
      fmap_cons, list_lookup_middle by (by rewrite fmap_length).
  * by simpl; rewrite list_lookup_middle by done.
  * typed_constructor; eauto using val_typed_weaken, val_typed_freeze.
Qed.
Lemma assert_free_params P Γ Δ δ ρ n m mf os τs :
  StackIndep P → ✓ Γ → ✓{Γ,Δ} δ → ✓{Γ,Δ} (m ∪ mf) → m ## mf →
  ✓{Δ}* ρ → ✓{Δ}* (zip os τs) →
  assert_holds (Π imap_go (λ i τ, var i ↦{false,perm_full} - : τ)
    (length ρ) τs ★ P)%A Γ Δ δ (ρ ++ zip os τs) n (cmap_erase m) →
  length os = length τs → NoDup os → ∃ Δ',
  (**i 1.) *) Δ ⇒ₘ Δ' ∧
  (**i 2.) *) (∀ Δ'', ✓{Γ,Δ''} (foldr mem_free m os) → Δ ⇒ₘ Δ'' → Δ' ⇒ₘ Δ'') ∧
  (**i 3.) *) ✓{Γ,Δ'} (foldr mem_free m os ∪ mf) ∧
  (**i 5.) *) foldr mem_free m os ## mf ∧
  (**i 4.) *) foldr mem_free (m ∪ mf) os = foldr mem_free m os ∪ mf ∧
  (**i 6.) *) mem_locks (foldr mem_free m os) = mem_locks m ∧
  (**i 7.) *) assert_holds P Γ Δ' δ ρ n (cmap_erase (foldr mem_free m os)).
Proof.
  intros ?? Hδ Hm Hmmf Hρ Hoτs HP; rewrite <-Forall2_same_length; intros Hos.
  revert Δ ρ m Hρ Hoτs Hδ Hm Hmmf HP.
  induction Hos as [|o τ os τs ? _ IH]; intros Δ ρ m ????? HP;
    inversion_clear 1; decompose_Forall_hyps; simplify_mem_disjoint_hyps.
  { rewrite (right_id_L [] _) in HP; exists Δ; split_and ?; auto.
    eapply assert_entails_spec with (_ ★ _)%A; eauto.
    by rewrite (left_id emp%A (★)%A). }
  assert (assert_holds (var (length ρ) ↦{false,perm_full} - : τ ★
    Π imap_go (λ i τ, (var i ↦{false,perm_full} - : τ)%A) (S (length ρ)) τs ★ P)
    Γ Δ δ (ρ ++ (o, τ) :: zip os τs) n (cmap_erase m))
    as (m1&m2'&?&?&(?&?&v&_&Heval&_&?&?)&?); csimpl in *; [|clear HP].
  { eapply assert_entails_spec with ((_ ★ _) ★ _)%A; eauto.
    by rewrite (assoc (★)%A). }
  rewrite list_lookup_middle in Heval by done; simplify_option_eq.
  destruct (cmap_erase_union_inv_l m m1 m2') as (m2&->&?&_&->); auto.
  simplify_mem_disjoint_hyps.
  assert (mem_freeable_perm o false m1)
    by eauto using mem_freeable_perm_singleton.
  assert (mem_freeable_perm o false (m1 ∪ m2))
    by eauto using mem_freeable_perm_subseteq, @sep_union_subseteq_l.
  destruct (IH (alter (prod_map id (λ _, true)) o Δ) (ρ ++ [(o,τ)])
    (mem_free o (m1 ∪ m2))) as (Δ'&?&Hleast&?&?&?&Hlocks&?);
    eauto using indexes_valid_weaken, mem_free_forward,
      mem_free_disjoint, funenv_valid_weaken.
  { erewrite <-mem_free_union by eauto; eauto. }
  { erewrite mem_free_union, cmap_erase_union, mem_free_singleton,
      sep_left_id, <-(assoc_L (++)), app_length, Nat.add_1_r by eauto.
    eauto 10 using assert_weaken, mem_free_forward. }
  simplify_mem_disjoint_hyps.
  assert (Δ ⇒ₘ Δ').
  { transitivity (alter (prod_map id (λ _, true)) o Δ);
      auto using mem_free_forward. }
  rewrite !mem_free_foldr_free; exists Δ'; split_and ?; auto.
  * intros Δ'' Hvalid ?; apply Hleast; auto.
    assert (∀ τ', Δ'' !! o = Some (τ',false) → False).
    { intros τ' ?; destruct (mem_free_valid_index_inv Γ Δ''
        (foldr mem_free (m1 ∪ m2) os) false o); rewrite ?mem_free_foldr_free;
        auto using mem_freeable_perm_foldr_free.
      by exists τ'. }
    rewrite <-(alter_id (prod_map id (λ _, true)) Δ'' o)
      by (intros [? []] ?; naive_solver); eauto using mem_free_memenv_compat.
  * by erewrite mem_free_union by eauto.
  * by erewrite Hlocks, mem_locks_free by eauto.
  * apply stack_indep_spec with (ρ ++ [(o, τ)]);
      eauto using indexes_valid_weaken, funenv_valid_weaken.
Qed.
Lemma assert_fun_intro Γ δ (f : funname) Pf s τs τ :
  Γ !! f = Some (τs,τ) →
  δ !! f = Some s →
  (∀ c vs,
    Γ\ δ ⊨ₛ {{ Π imap2_go (λ i v τ,
                 var i ↦{false,perm_full} #freeze true v : τ) 0 vs τs ★
               fpre Pf c vs }}
              s
            {{ λ v, Π imap_go (λ i τ, var i ↦{false,perm_full} - : τ) 0 τs ★
                    fpost Pf c vs v }}) →
  emp%A ⊆{Γ,δ} assert_fun f Pf τs τ.
Proof.
  intros ?? Hf Γ1 Δ1 δ1 ρ n1 m ?????? [_ ->].
  split_and !; eauto using lookup_fun_weaken.
  intros Γ2 Δ2 δ2 n2 c vs m ??????????.
  apply ax_further_alt; intros Δ3 n3 ? mf ??? (->&?&?).
  assert (✓{Δ2}* ρ) by eauto using indexes_valid_weaken.
  assert (δ2 !! f = Some s).
  { apply lookup_weaken with δ; auto. by transitivity δ1. }
  clear dependent Δ1 n1.
  split; [solve_rcred|intros S p Hdom].
  assert (∃ os, Forall_fresh (dom indexset (m ∪ mf)) os ∧
    length os = length vs ∧
    S = State [CParams f (zip os (type_of <$> vs))]
              (Stmt ↘ s) (mem_alloc_list Γ2 os vs (m ∪ mf)))
    as (os&?&?&->) by (inv_rcstep p; eauto);
    clear p; simplify_type_equality'.
  erewrite fmap_type_of by eauto.
  destruct (assert_alloc_params (fpre Pf c vs) Γ2 Δ3 δ2 [] n3 m mf os vs τs)
    as (Δ4&?&?&?&?&?&->&Hpre); eauto using Forall2_impl, val_typed_weaken,
    assert_weaken, indexes_valid_weaken, funenv_valid_weaken.
  apply mk_ax_next with Δ4 (mem_alloc_list Γ2 os vs m); auto.
  { constructor; auto. }
  { eauto using cmap_union_valid_2, cmap_valid_weaken. }
  { intros; simplify_mem_disjoint_hyps; eauto. }
  destruct (funenv_lookup Γ2 Δ2 δ2 f τs τ) as (?&τlr&?&?&?&?&?&?);
    eauto using lookup_fun_weaken; simplify_equality.
  assert (length os = length τs).
  { erewrite <-(Forall2_length _ _ τs) by eauto; lia. }
  assert (NoDup os)
    by (by apply Forall_fresh_NoDup with (dom indexset (m ∪ mf))).
  eapply ax_compose_cons with ax_disjoint_cond _;
    eauto using funenv_valid_weaken.
  { eapply Hf, Hpre; eauto using funenv_valid_weaken.
    * by transitivity Γ1.
    * by transitivity δ1.
    * assert (Forall_fresh (dom indexset m) os).
      { eapply Forall_fresh_subseteq; eauto.
        rewrite cmap_dom_union; set_solver. }
      by erewrite mem_locks_alloc_list by eauto.
    * simpl; rewrite snd_zip by lia; eauto using stmt_typed_weaken. }
  clear dependent m mf; intros Δ5 n4 ? m; destruct 1; intros.
  apply ax_further_alt; intros Δ6 n5 ? mf ??? (->&?&?).
  split; [solve_rcred|intros S p _].
  assert (∃ v, S = State [] (Return f v) (foldr mem_free (m ∪ mf) os) ∧
    assert_holds (Π imap_go (λ i τ, (var i ↦{false,perm_full} - : τ)%A) 0 τs
      ★ fpost Pf c vs v) Γ2 Δ5 δ2 (zip os τs) n4 (cmap_erase m) ∧
    (Γ2,Δ5) ⊢ v : τ) as (v&->&?&?).
  { inv_rcstep; typed_inversion_all;
      match goal with H : rettype_match _ _ |- _ => inversion H; subst end;
      eexists; split_and ?; rewrite ?fst_zip by auto; eauto. }
  clear dependent p d.
  destruct (assert_free_params (fpost Pf c vs v) Γ2 Δ6 δ2 [] n5 m mf os τs)
    as (Δ7&?&?&?&?&->&?&?); eauto using assert_weaken,
    indexes_valid_weaken, funenv_valid_weaken.
  apply mk_ax_next with Δ7 (foldr mem_free m os); auto.
  { constructor; auto. }
  { intros; simplify_mem_disjoint_hyps; eauto. }
  apply ax_done; constructor; eauto using val_typed_weaken with congruence.
Qed.
Lemma ax_call {vn} Γ δ A Pf P Q (Ps: vec (assert K) vn) (Qs: vec (vassert K) vn) R e (es : vec (expr K) vn) τs τ c :
  (∀ p vs,
    (A ★ Q (inl p) ★ Π vzip_with (λ Q v, Q (inr v)) Qs vs)%A ⊆{Γ,δ} (∃ f,
      ⌜ p = FunPtr f τs τ ⌝ ★ ▷ (assert_fun f Pf τs τ) ★ fpre Pf c vs ★
      (∀ vret, fpost Pf c vs vret -★ (A ★ R (inr vret))))%A) →
  Γ\ δ \ A ⊨ₑ {{ P }} e {{ λ ν, (Q ν) ◊ }} →
  (∀ i, Γ\ δ\ A ⊨ₑ {{ Ps !!! i }} es !!! i {{ λ ν, ((Qs !!! i) ν) ◊ }}) →
  Γ\ δ \ A ⊨ₑ {{ P ★ Π Ps }} call e @ es {{ R }}.
Proof.
  intros HQ Hax1 Hax2 Γ' Δ δ' n ρ m τlr ?????? He ??? HP.
  assert (∃ τ (τs : vec _ vn), τlr = inr τ ∧
    (Γ',Δ,ρ.*2) ⊢ e : inl (τs ~> τ) ∧
    ∀ i, (Γ',Δ,ρ.*2) ⊢ es !!! i : inr (τs !!! i))
    as (τ'&τs'&->&?&?); [|clear He].
  { assert (∃ τ τs, τlr = inr τ ∧ (Γ',Δ,ρ.*2) ⊢ e : inl (τs ~> τ) ∧
      (Γ',Δ,ρ.*2) ⊢* es :* inr <$> τs) as (τ'&τs'&->&?&Hes)
      by (typed_inversion_all; eauto).
    assert (vn = length τs') by (by erewrite <-fmap_length,
      <-Forall2_length, vec_to_list_length by eauto); subst vn.
    exists τ', (list_to_vec τs'). rewrite ?vec_to_list_to_vec.
    by rewrite Forall2_fmap_r, <-(vec_to_list_to_vec τs'),
      Forall2_vlookup in Hes. }
  destruct HP as (m1'&m2&Hm&Hm'&?&HPs).
  destruct (cmap_erase_union_inv_r m m1' m2)
    as (m1&->&?&->&?); simplify_mem_disjoint_hyps; auto; clear Hm Hm'.
  rewrite assert_Forall_holds_vec in HPs; destruct HPs as (ms&->&?&?).
  repeat match goal with
    | _ => progress simpl in *
    | H : mem_locks (_ ∪ _) = ∅ |- _ => rewrite mem_locks_union in H by auto
    | H : mem_locks (⋃ _) = ∅ |- _ => rewrite mem_locks_union_list in H by auto
    | H : ✓{_} (⋃ _) |- _ =>
       rewrite <-cmap_union_list_valid, Forall_vlookup in H by eauto
    | H : _ ∪ _ = ∅ |- _ => apply empty_union_L in H; destruct H
    | H : ⋃ _ = ∅ |- _ =>
       rewrite empty_union_list_L, Forall_fmap, Forall_vlookup in H
    end.
  apply (ax_expr_compose Γ' δ' A ((λ ν, Q ν ◊)%A ::: vmap (λ Q ν, Q ν ◊)%A Qs) R
    Δ (DCCall vn) (e ::: es) ρ n
    (m1 ::: ms) (inl (τs' ~> τ') ::: vmap inr τs')); auto.
  { intros i; inv_fin i; eauto. }
  { intros i; inv_fin i; set_solver. }
  { intros i; inv_fin i; simpl.
    { eauto using ax_expr_invariant_weaken, @sep_union_subseteq_l'. }
    intros i; rewrite vlookup_map; eapply Hax2; eauto.
    * by rewrite vlookup_map.
    * eapply ax_expr_invariant_weaken; eauto.
      by apply sep_union_subseteq_r_transitive, (sep_subseteq_lookup ms).
    * by rewrite cmap_erased_spec
        by eauto using cmap_erased_subseteq, (sep_subseteq_lookup ms). }
  clear dependent m1 ms e es P Ps; intros Δ' n' νs ms.
  inv_vec νs; intros ν νs; inv_vec ms; intros m ms.
  intros ? Hms ?? Hνs HQs;
    repeat match goal with
    | H : ∀ i : fin (S _), _ |- _ =>
       pose proof (H 0%fin); specialize (λ i, H (FS i)); simpl in *
    | H : assert_holds _ _ _ _ _ _ _ |- _ => rewrite assert_unlock_spec in H
    end.
  destruct ν as [p|]; typed_inversion_all.
  assert (∃ vs, νs = vmap inr vs ∧ (Γ',Δ') ⊢* vs :* τs') as (vs&->&Hvs).
  { revert Hνs; clear; induction νs as [|ν ? νs IH].
    { inv_vec τs'; eexists [#]; simpl; auto. }
    inv_vec τs'; intros τ τs Hi; destruct (IH τs (λ i, Hi (FS i))) as (vs&->&?).
    specialize (Hi 0%fin); typed_inversion_all; eexists (_:::_); simpl; eauto. }
  clear Hνs.
  rewrite vec_to_list_zip_with, vec_to_list_map, zip_with_fmap_r.
  rewrite <-(zip_with_fmap_l (λ Ω v, #{Ω} v)%E mem_locks).
  apply ax_further_alt.
  intros Δ'' n'' ????? Hframe; inversion_clear Hframe as [mA mf ?????? HmA|];
    simplify_equality; simplify_mem_disjoint_hyps.
  destruct (HQ p vs Γ' Δ'' δ' ρ (S n'')
    (cmap_erase (mem_unlock_all (m ∪ ⋃ ms ∪ mA))))
    as (f&?&?&Hm&_&[-> ->]&?&?&->&_&Hf&m''&mf2&->&?&?&Hpost); clear HQ;
    eauto using indexes_valid_weaken, mem_unlock_all_valid, funenv_valid_weaken.
  { assert (## (mA :: cmap_erase m :: (cmap_erase <$> vec_to_list ms))).
    { rewrite <-cmap_erase_disjoint_le, <-cmap_erase_disjoint_list_le; auto. }
    rewrite (sep_commutative _ mA), mem_erase_unlock_all by auto.
    rewrite !cmap_erase_union,
      cmap_erase_union_list, (cmap_erased_spec mA) by auto.
    rewrite !mem_unlock_all_union,
      mem_unlock_all_union_list, (mem_unlock_all_empty_locks mA) by auto.
    assert (## (mA :: mem_unlock_all (cmap_erase m) ::
      (mem_unlock_all <$> (cmap_erase <$> vec_to_list ms)))) by
      by rewrite <-mem_unlock_all_disjoint_le,<-mem_unlock_all_disjoint_list_le.
    eexists mA, _; split_and ?; auto.
    eexists _, _; split_and ?; eauto using assert_weaken,
      indexes_valid_weaken, mem_unlock_all_valid, funenv_valid_weaken.
    apply assert_Forall_holds_2; auto.
    rewrite <-!vec_to_list_map, Forall2_vlookup; intros i; specialize (HQs i).
    rewrite !vlookup_map, vlookup_zip_with.
    rewrite !vlookup_map, assert_unlock_spec in HQs; simpl in *.
    eauto using assert_weaken, indexes_valid_weaken, mem_unlock_all_valid. }
  destruct (Hf n'') as (->&?&Hf'); clear Hf; auto.
  rewrite !sep_left_id in Hm by auto; typed_inversion_all.
  assert (## [mem_unlock_all (m ∪ ⋃ ms ∪ mA); mf])
    by (rewrite <-mem_unlock_all_disjoint_le; auto).
  destruct (cmap_erase_union_inv_r (mem_unlock_all (m ∪ ⋃ ms ∪ mA)) m'' mf2)
    as (m'&Hm'&?&->&?); auto.
  assert (mem_locks m' = ∅ ∧ mem_locks mf2 = ∅) as [??].
  { rewrite <-empty_union_L, <-mem_locks_union, <-Hm' by auto.
    by rewrite mem_locks_unlock_all. }
  assert (✓{Γ',Δ''} (mem_unlock_all (m ∪ ⋃ ms ∪ mA)))
    by eauto using mem_unlock_all_valid.
  assert (✓{Γ',Δ''} m' ∧ ✓{Γ',Δ''} mf2) as [??].
    by (rewrite <-cmap_union_valid, <-Hm' by auto; auto).
  assert (length (mem_locks <$> vec_to_list ms) = length vs).
  { rewrite fmap_length; apply vec_to_list_same_length. }
  split; [solve_rcred|intros ? p _].
  apply (rcstep_expr_call_inv _ _ _ _ _ _ _ _ _ _ _ _ p); auto; clear p.
  assert (mem_locks (m ∪ ⋃ ms ∪ mA) =
    mem_locks m ∪ ⋃ (mem_locks <$> vec_to_list ms)).
  { rewrite !mem_locks_union, mem_locks_union_list by auto.
    by rewrite HmA, (right_id_L _ _). }
  rewrite <-sep_associative, (sep_commutative mf), sep_associative by auto.
  rewrite mem_unlock_union, <-mem_unlock_all_spec_alt
    by eauto using (reflexive_eq (R:=(⊆) : relation lockset)), eq_sym.
  apply mk_ax_next with Δ'' (mem_unlock_all (m ∪ ⋃ ms ∪ mA)); auto.
  { apply ax_unframe_expr_to_fun with (mem_unlock_all (m ∪ ⋃ ms)); auto.
    * by rewrite mem_unlock_all_union, (mem_unlock_all_empty_locks mA) by auto.
    * rewrite mem_unlock_all_union, (mem_unlock_all_empty_locks mA) by auto.
      by rewrite <-!sep_associative, (sep_commutative mA)
        by (rewrite <-?mem_unlock_all_disjoint_le; auto).
    * rewrite <-mem_unlock_all_disjoint_le; auto. }
  rewrite Hm'; clear dependent m ms mA mf S'.
  eapply ax_compose_cons with ax_disjoint_cond
    (ax_fun_post f τ' (λ v, fpost Pf c vs v ★ assert_eq_mem mf2)%A);
    eauto using funenv_valid_weaken.
  { apply ax_frame with ax_disjoint_cond (ax_fun_post f τ' (fpost Pf c vs));
      eauto 3 using ax_disjoint_cond_frame_diagram, funenv_valid_weaken.
    apply Hf'; eauto using funenv_valid_weaken, Forall2_impl, val_typed_weaken.
    { eapply stack_indep_spec with ρ;
        eauto using assert_weaken, indexes_valid_weaken, funenv_valid_weaken. }
    intros Δ''' n''' ? m'' ?????; destruct 1; constructor; auto.
    * by rewrite mem_locks_union, empty_union_L by auto.
    * rewrite cmap_erase_union, (cmap_erased_spec mf2) by auto.
      exists (cmap_erase m), mf2; split_and ?; try done.
      by rewrite <-cmap_erase_disjoint_le. }
  clear dependent m' Hf'.
  intros Δ''' n''' m'; destruct 1 as [v m''' ?? (m''&?&?&?&?&Hmf)]; intros.
  repeat red in Hmf; subst. 
  destruct (cmap_erase_union_inv_r m''' m'' mf2) as (m&->&?&->&?); auto.
  apply ax_further_alt; intros Δ'''' n'''';
    destruct 4; simplify_equality'; simplify_mem_disjoint_hyps.
  split; [solve_rcred|intros S' p _; inv_rcstep p].
  destruct (Hpost v Γ' Δ'''' δ' (S n'''') (cmap_erase m))
    as (mA&m''&?&?&?&?); eauto using funenv_valid_weaken.
  { eapply stack_indep_spec with [];
      eauto using assert_weaken, indexes_valid_weaken, funenv_valid_weaken. }
  destruct (cmap_erase_union_inv_l (m ∪ mf2) mA m'')
    as (m'&Hm'&?&?&->); auto.
  { by rewrite cmap_erase_union, (cmap_erased_spec mf2) by auto. }
  assert (## [mA ∪ m'; mf]) by (rewrite <-Hm'; auto).
  assert (mem_locks mA = ∅ ∧ mem_locks m' = ∅) as [??].
  { by rewrite <-empty_union_L, <-mem_locks_union, <-Hm' by auto. }
  assert (✓{Γ',Δ''''} mA ∧ ✓{Γ',Δ''''} m') as [??].
  { rewrite <-cmap_union_valid, <-Hm' by auto; auto. }
  assert (mem_locks mA = ∅ ∧ mem_locks m' = ∅) as [??].
  { by rewrite <-empty_union_L, <-mem_locks_union, <-Hm' by auto. }
  rewrite Hm', <-sep_associative, (sep_commutative mA) by auto.
  apply mk_ax_next with Δ'''' m'; simpl; auto.
  { apply ax_unframe_fun_to_expr with mA; auto. }
  { apply subseteq_empty. }
  apply ax_done; constructor; eauto 7 using val_typed_weaken,
    assert_weaken, indexes_valid_weaken.
Qed.
End axiomatic_functions.
