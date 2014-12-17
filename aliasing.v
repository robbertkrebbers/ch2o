(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export operations memory pointer_casts.

Section aliasing.
Context `{EnvSpec Ti}.
Implicit Types Γ : env Ti.
Implicit Types Γm : memenv Ti.
Implicit Types τ σ : type Ti.
Implicit Types r : ref Ti.
Implicit Types a : addr Ti.
Implicit Types w : mtree Ti.
Implicit Types v : val Ti.
Implicit Types m : mem Ti.
Arguments lookupE _ _ _ _ _ _ _ !_ /.
Arguments cmap_lookup _ _ _ _ !_ /.

Lemma ref_disjoint_cases Γ τ r1 r2 σ1 σ2 :
  ✓ Γ → Γ ⊢ r1 : τ ↣ σ1 → freeze true <$> r1 = r1 →
  Γ ⊢ r2 : τ ↣ σ2 → freeze true <$> r2 = r2 →
  (**i 1.) *) (∀ j1 j2, ref_set_offset j1 r1 ⊥ ref_set_offset j2 r2) ∨
  (**i 2.) *) σ1 ⊆{Γ} σ2 ∨
  (**i 3.) *) σ2 ⊆{Γ} σ1 ∨
  (**i 4.) *) ∃ s r1' i1 r2' i2 r', r1 = r1' ++ RUnion i1 s true :: r' ∧
    r2 = r2' ++ RUnion i2 s true :: r' ∧ i1 ≠ i2.
Proof.
  intros HΓ Hr1 Hr1F Hr2 Hr2F. cut (
    (**i 1.) *) (∀ j1 j2, ref_set_offset j1 r1 ⊥ ref_set_offset j2 r2) ∨
    (**i 2.) *) (∃ j r', r1 = r' ++ ref_set_offset j r2) ∨
    (**i 3.) *) (∃ j r', r2 = r' ++ ref_set_offset j r1) ∨
    (**i 4.) *) ∃ s r1' i1 r2' i2 r', r1 = r1' ++ [RUnion i1 s true] ++ r' ∧
      r2 = r2' ++ [RUnion i2 s true] ++ r' ∧ i1 ≠ i2).
  { intros [?|[(j&r'&->)|[(j&r'&->)|(s&r1'&i1&r2'&i2&r'&Hr1'&Hr2'&?)]]].
    * by left.
    * rewrite ref_typed_app in Hr1; destruct Hr1 as (σ2'&?&?).
      assert (σ2'=σ2) as -> by eauto using ref_set_offset_typed_unique, eq_sym.
      by right; left; exists r'.
    * rewrite ref_typed_app in Hr2; destruct Hr2 as (σ1'&?&?).
      assert (σ1'=σ1) as -> by eauto using ref_set_offset_typed_unique, eq_sym.
      by do 2 right; left; exists r'.
    * do 3 right; naive_solver. }
  revert r1 τ σ1 Hr1 r2 σ2 Hr1F Hr2 Hr2F. assert (∀ τ rs1 r2 σ1 σ2,
    Γ ⊢ rs1 : τ ↣ σ1 → freeze true rs1 = rs1 →
    Γ ⊢ r2 : τ ↣ σ2 → freeze true <$> r2 = r2 →
    (* 1.) *) (∀ j1 j2, ref_set_offset j1 [rs1] ⊥ ref_set_offset j2 r2) ∨
    (* 2.) *) (∃ j r', r2 = r' ++ ref_set_offset j [rs1]) ∨
    (* 3.) *) r2 = [] ∨
    (* 4.) *) ∃ s i1 r2' i2, rs1 = RUnion i1 s true ∧
      r2 = r2' ++ [RUnion i2 s true] ∧ i1 ≠ i2) as aux.
  { intros τ rs1 r2 σ1 σ2 Hrs1 Hrs1F Hr2 Hr2F.
    destruct r2 as [|rs2 r2 _] using rev_ind; [by do 2 right; left|].
    rewrite ref_typed_snoc in Hr2; destruct Hr2 as (σ2'&Hrs2&Hr2).
    rewrite fmap_app in Hr2F. destruct Hrs1 as [? i1 n|s i1|s i1 ?];
      inversion Hrs2 as [? i2|? i2|? i2 []]; simplify_list_equality.
    * by right; left; exists i2 r2.
    * destruct (decide (i1 = i2)) as [->|]; [by right; left; exists 0 r2|].
      left. intros _ ?. destruct r2; simpl; [by repeat constructor|].
      rewrite app_comm_cons. apply ref_disjoint_app_r. by repeat constructor.
    * destruct (decide (i1 = i2)) as [->|]; [by right; left; exists 0 r2|].
      do 3 right. by exists s i1 r2 i2. }
  induction 1 as [τ|r1 rs1 τ τ1 σ1 Hrs1 Hr1 IH]
    using @ref_typed_ind; intros r2 σ2 Hr1F Hr2 Hr2F; simplify_equality'.
  { do 2 right; left; exists 0 r2. by rewrite (right_id_L [] (++)). }
  destruct Hr2 as [τ|r2 rs2 τ τ2 σ2 Hrs2 Hr2 _]
    using @ref_typed_ind; simplify_equality'.
  { right; left; exists 0 (rs1 :: r1). by rewrite (right_id_L [] (++)). }
  destruct (IH r2 τ2) as
    [Hr|[(j&r'&->)|[(j&r'&->)|(s&r1'&i1&r2'&i2&r'&->&->&?)]]];
    auto; clear IH; simplify_equality'.
  * left; intros j1 j2. apply ref_disjoint_cons_l, ref_disjoint_cons_r.
    by rewrite <-(ref_set_offset_offset r1), <-(ref_set_offset_offset r2).
  * rewrite ref_typed_app in Hr1; destruct Hr1 as (τ2'&Hr2'&Hr').
    assert (τ2' = τ2) as -> by eauto using ref_set_offset_typed_unique, eq_sym.
    destruct (ref_set_offset_disjoint r2 j) as [?| ->].
    { left; intros j1 j2. rewrite app_comm_cons.
      by apply ref_disjoint_app_l, ref_disjoint_cons_r. }
    destruct (aux τ2 rs2 (rs1 :: r') σ2 σ1)
      as [Hr|[(j'&r''&Hr'')|[?|(s&i1&r2'&i2&?&Hr2''&?)]]];
      simplify_equality'; auto.
    { econstructor; eauto. }
    { destruct (app_injective_1 (freeze true <$> r') r'
        (freeze true <$> ref_set_offset j r2) (ref_set_offset j r2));
        rewrite ?fmap_length, <-?fmap_app; congruence. }
    + left; intros j1 j2. rewrite app_comm_cons.
      apply (ref_disjoint_here_app _ [_]), symmetry, Hr.
    + right; left; exists j' r''.
      by rewrite app_comm_cons, Hr'', <-(associative_L (++)).
    + do 3 right. eexists s, r2', i2, [], i1, r2.
      by rewrite app_comm_cons, Hr2'', <-(associative_L (++)).
  * rewrite ref_typed_app in Hr2; destruct Hr2 as (τ1'&Hr1'&Hr').
    assert (τ1' = τ1) as -> by eauto using ref_set_offset_typed_unique, eq_sym.
    destruct (ref_set_offset_disjoint r1 j) as [?| ->]; simpl.
    { left; intros. rewrite app_comm_cons. by apply (ref_disjoint_app [_]). }
    destruct (aux τ1 rs1 (rs2 :: r') σ1 σ2)
      as [Hr|[(j'&r''&Hr'')|[?|(s&i1&r2'&i2&?&Hr1''&?)]]];
      simplify_equality'; auto.
    { econstructor; eauto. }
    { destruct (app_injective_1 (freeze true <$> r') r'
        (freeze true <$> ref_set_offset j r1) (ref_set_offset j r1));
        rewrite ?fmap_length, <-?fmap_app; congruence. }
    + left; intros j1 j2. rewrite app_comm_cons.
      apply (ref_disjoint_here_app [_]), Hr.
    + do 2 right; left; exists j' r''.
      by rewrite app_comm_cons, Hr'', <-(associative_L (++)).
    + do 3 right; eexists s, [], i1, r2', i2, r1.
      by rewrite app_comm_cons, Hr1'', <-(associative_L (++)).
  * by do 3 right; eexists s, (rs1 :: r1'), i1, (rs2 :: r2'), i2, r'.
Qed.
Lemma addr_disjoint_cases Γ Γm a1 a2 σ1 σ2 :
  ✓ Γ → (Γ,Γm) ⊢ a1 : Some σ1 → frozen a1 → addr_is_obj a1 →
  (Γ,Γm) ⊢ a2 : Some σ2 → frozen a2 → addr_is_obj a2 →
  (**i 1.) *) (∀ j1 j2, addr_plus Γ j1 a1 ⊥{Γ} addr_plus Γ j2 a2) ∨
  (**i 2.) *) σ1 ⊆{Γ} σ2 ∨
  (**i 3.) *) σ2 ⊆{Γ} σ1 ∨
  (**i 4.) *) addr_index a1 = addr_index a2 ∧ (∃ s r1' i1 r2' i2 r',
    addr_ref_base a1 = r1' ++ RUnion i1 s true :: r' ∧
    addr_ref_base a2 = r2' ++ RUnion i2 s true :: r' ∧ i1 ≠ i2).
Proof.
  unfold frozen. inversion 2 as [o1 r1 i1 τ1 σ1'];
    inversion 3 as [o2 r2 i2 τ2 σ2']; intros; simplify_equality'.
  destruct (decide (o1 = o2)); [simplify_type_equality|by do 2 left].
  destruct (ref_disjoint_cases Γ τ2 r1 r2 σ1' σ2')
    as [?|[?|[?|(s&r1'&i1'&r2'&i2'&r'&->&->&?)]]]; auto.
  * left; intros j1 j2; right; left; split; simpl; auto.
  * do 3 right; split; [done|]. by eexists s, r1', i1', r2', i2', r'.
Qed.
Lemma cmap_non_aliasing Γ Γm m a1 a2 σ1 σ2 :
  ✓ Γ → ✓{Γ,Γm} m → (Γ,Γm) ⊢ a1 : Some σ1 → frozen a1 → addr_is_obj a1 →
  (Γ,Γm) ⊢ a2 : Some σ2 → frozen a2 → addr_is_obj a2 →
  (**i 1.) *) (∀ j1 j2, addr_plus Γ j1 a1 ⊥{Γ} addr_plus Γ j2 a2) ∨
  (**i 2.) *) σ1 ⊆{Γ} σ2 ∨
  (**i 3.) *) σ2 ⊆{Γ} σ1 ∨
  (**i 4.) *) ∀ g j1 j2,
    cmap_alter Γ g (addr_plus Γ j1 a1) m !!{Γ} addr_plus Γ j2 a2 
    = @None (mtree _) ∧
    cmap_alter Γ g (addr_plus Γ j2 a2) m !!{Γ} addr_plus Γ j1 a1
    = @None (mtree _).
Proof.
  intros ? Hm ??????. destruct (addr_disjoint_cases Γ Γm a1 a2 σ1 σ2)
    as [Ha12|[?|[?|(Hidx&s&r1'&i1&r2'&i2&r'&Ha1&Ha2&?)]]]; auto.
  do 3 right. intros g j1 j2.
  assert (Γm ⊢ addr_index a1 : addr_type_object a1)
    by eauto using addr_typed_index.
  assert (Γm ⊢ addr_index a1 : addr_type_object a2)
    by (rewrite Hidx; eauto using addr_typed_index).
  destruct m as [m]; unfold insertE, cmap_alter, lookupE, cmap_lookup;
    simpl in *; rewrite !addr_index_plus, <-!Hidx; simplify_map_equality'.
  destruct (m !! addr_index a1) as [[|w malloc]|] eqn:?;
    [by simplify_option_equality| |by simplify_option_equality].
  destruct (proj2 Hm (addr_index a1) w malloc)
    as (τ&?&_&?&_); auto; simplify_type_equality'.
  assert (Γ ⊢ r1' ++ RUnion i1 s true :: r' :
    addr_type_object a2 ↣ addr_type_base a1).
  { erewrite <-Ha1, <-(typed_unique _ (addr_index a1)
      (addr_type_object a1) (addr_type_object a2)) by eauto.
    eauto using addr_typed_ref_base_typed. }
  assert (Γ ⊢ r2' ++ RUnion i2 s true :: r' :
    addr_type_object a2 ↣ addr_type_base a2).
  { rewrite <-Ha2. eauto using addr_typed_ref_base_typed. }
  unfold addr_ref; rewrite !addr_ref_base_plus, Ha1, Ha2.
  by split; case_option_guard; simplify_equality;
    erewrite ?ctree_lookup_non_aliasing by eauto.
Qed.
Lemma mem_non_aliasing Γ Γm m a1 a2 τ1 τ2 :
  ✓ Γ → ✓{Γ,Γm} m → (Γ,Γm) ⊢ a1 : Some τ1 → frozen a1 → addr_is_obj a1 →
  (Γ,Γm) ⊢ a2 : Some τ2 → frozen a2 → addr_is_obj a2 →
  (**i 1.) *) (∀ j1 j2, addr_plus Γ j1 a1 ⊥{Γ} addr_plus Γ j2 a2) ∨
  (**i 2.) *) τ1 ⊆{Γ} τ2 ∨
  (**i 3.) *) τ2 ⊆{Γ} τ1 ∨
  (**i 4.) *) ∀ j1 j2,
    (∀ v1, <[addr_plus Γ j1 a1:=v1]{Γ}>m !!{Γ} addr_plus Γ j2 a2 = None) ∧
    mem_force Γ (addr_plus Γ j1 a1) m !!{Γ} addr_plus Γ j2 a2 = None ∧
    (∀ v2, <[addr_plus Γ j2 a2:=v2]{Γ}>m !!{Γ} addr_plus Γ j1 a1 = None) ∧
    mem_force Γ (addr_plus Γ j2 a2) m !!{Γ} addr_plus Γ j1 a1 = None.
Proof.
  intros.
  destruct (cmap_non_aliasing Γ Γm m a1 a2 τ1 τ2) as [?|[?|[?|Ha]]]; auto.
  unfold lookupE, mem_lookup, insertE, mem_insert, mem_force.
  by do 3 right; repeat split; intros;
    rewrite ?(proj1 (Ha _ _ _)), ?(proj2 (Ha _ _ _)).
Qed.
End aliasing.
