(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Import type_environment.

Section natural_type_environment.
Context `{IntEnvSpec Ti}.
Context (ptr_size : type Ti → nat) (align_base : base_type Ti → nat).
Context (ptr_size_ne_0 : ∀ τ, ptr_size τ ≠ 0).
Context (align_void : align_base voidT = 1).
Context (align_int_divide : ∀ τi, (align_base (intT τi) | rank_size (rank τi))).
Context (align_ptr_divide : ∀ τ, (align_base (τ.*) | ptr_size τ)).

Definition natural_align_of (Γ : env Ti) : type Ti → nat := type_iter
  (**i TBase =>     *) align_base
  (**i TArray =>    *) (λ _ _ x, x)
  (**i TCompound => *) (λ c s τs rec, foldr lcm 1 (rec <$> τs)) Γ.
Definition natural_fields_align (Γ : env Ti) (τs : list (type Ti)) : nat :=
  foldr lcm 1 (natural_align_of Γ <$> τs).

Definition natural_padding (pos al : nat) : nat :=
  let z := pos `mod` al in if decide (z = 0) then 0 else al - z.

Definition natural_field_sizes (f : type Ti → nat) (Γ : env Ti)
    (whole_align : nat) : nat → list (type Ti) → list nat :=
  fix go pos τs :=
  match τs with
  | [] => []
  | τ :: τs =>
    let align := default whole_align (head τs) (natural_align_of Γ) in
    let sz := f τ + natural_padding (f τ + pos) align in
    sz :: go (sz + pos) τs
  end.
Definition natural_size_of (Γ : env Ti) : type Ti → nat :=
  type_iter
  (**i TBase =>     *) (λ τb,
    match τb with
    | voidT => 1 | intT τi => rank_size (rank τi) | τ.* => ptr_size τ
    end%BT)
  (**i TArray =>    *) (λ _, mult)
  (**i TCompound => *) (λ c s τs go,
    match c with
    | Struct_kind =>
       sum_list (natural_field_sizes go Γ (natural_fields_align Γ τs) 0 τs)
    | Union_kind =>
       let sz := foldr max 1 (go <$> τs) in
       sz + natural_padding sz (natural_fields_align Γ τs)
    end) Γ.

Instance natural_ptr_env : PtrEnv Ti := {
  size_of := natural_size_of;
  field_sizes Γ τs :=
    natural_field_sizes (natural_size_of Γ) Γ (natural_fields_align Γ τs) 0 τs
}.

Lemma natural_padding_divide pos al :
  al ≠ 0 → (al | pos + natural_padding pos al).
Proof.
  intros. unfold natural_padding; case_decide.
  { rewrite Nat.add_0_r. by apply Nat.mod_divide. }
  exists (1 + pos `div` al). rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
  assert (pos - al * pos `div` al < al).
  { rewrite <-Nat.mod_eq by done. by apply Nat.mod_bound_pos; lia. }
  assert (al * pos `div` al ≤ pos) by (by apply Nat.mul_div_le).
  rewrite Nat.mod_eq by done. lia.
Qed.
Lemma natural_align_of_compound_proper Γ :
  let fcompound c s τs rec := foldr lcm 1 (rec <$> τs) in
  ∀ rec1 rec2 (c : compound_kind) s (τs : list (type Ti)),
  Γ !! s = Some τs → Forall (λ τ, rec1 τ = rec2 τ) τs →
  fcompound c s τs rec1 = fcompound c s τs rec2.
Proof.
  intros fcompound rec1 rec2 c s τs _.
  unfold fcompound. induction 1; simpl; auto using f_equal.
Qed.
Lemma natural_align_of_base Γ τb :
  natural_align_of Γ (baseT τb) = align_base τb.
Proof. done. Qed.
Lemma natural_align_of_array Γ τ n :
  natural_align_of Γ (τ.[n]) = natural_align_of Γ τ.
Proof. unfold natural_align_of. by rewrite type_iter_array. Qed.
Lemma natural_align_of_compound Γ c s τs :
  ✓ Γ → Γ !! s = Some τs →
  natural_align_of Γ (compoundT{c} s) = natural_fields_align Γ τs.
Proof.
  intros. unfold natural_align_of. by rewrite type_iter_compound by eauto
    using natural_align_of_compound_proper with typeclass_instances.
Qed.
Lemma natural_align_weaken Γ1 Γ2 τ :
  ✓ Γ1 → ✓{Γ1} τ → Γ1 ⊆ Γ2 → natural_align_of Γ1 τ = natural_align_of Γ2 τ.
Proof.
  intros. unfold natural_align_of. apply type_iter_weaken; eauto
    using natural_align_of_compound_proper with typeclass_instances.
Qed.
Lemma natural_fields_align_weaken Γ1 Γ2 τs :
  ✓ Γ1 → ✓{Γ1}* τs → Γ1 ⊆ Γ2 →
  natural_fields_align Γ1 τs = natural_fields_align Γ2 τs.
Proof.
  intros ? Hτs ?. unfold natural_fields_align.
  induction Hτs; simpl; auto using natural_align_weaken.
Qed.
Lemma natural_field_sizes_weaken rec1 rec2 Γ1 Γ2 whole_align pos τs :
  ✓ Γ1 → Γ1 ⊆ Γ2 → ✓{Γ1}* τs → Forall (λ τ, rec1 τ = rec2 τ) τs →
  natural_field_sizes rec1 Γ1 whole_align pos τs =
    natural_field_sizes rec2 Γ2 whole_align pos τs.
Proof.
  intros ?? Hτs Hrec. revert pos Hτs.
  induction Hrec as [|τ τs Hτ ? IH]; intros; decompose_Forall; simpl; auto.
  rewrite Hτ, IH by done. destruct τs as [|τ2 τs]; simpl; [done|].
  decompose_Forall. by erewrite natural_align_weaken by eauto.
Qed.

Lemma natural_size_of_compound_proper Γ1 Γ2 rec1 rec2 c s τs :
  let fc Γ rec c (s : tag) τs :=
    match c with
    | Struct_kind =>
       sum_list (natural_field_sizes rec Γ (natural_fields_align Γ τs) 0 τs)
    | Union_kind =>
       let sz := foldr max 1 (rec <$> τs) in
       sz + natural_padding sz (natural_fields_align Γ τs)
    end in
  ✓ Γ1 → Γ1 ⊆ Γ2 → Γ1 !! s = Some τs → ✓{Γ1}* τs →
  Forall (λ τ, rec1 τ = rec2 τ) τs → fc Γ1 rec1 c s τs = fc Γ2 rec2 c s τs.
Proof.
  intros fc ??. destruct c; simpl.
  * intros _ Hτs Hrec. erewrite natural_fields_align_weaken by eauto.
    by erewrite natural_field_sizes_weaken by eauto.
  * intros. by erewrite Forall_fmap_ext_1, natural_fields_align_weaken by eauto.
Qed.
Lemma natural_size_of_base Γ τb :
  size_of Γ (baseT τb) =
    match τb with
    | voidT => 1 | intT τi => rank_size (rank τi) | τ.* => ptr_size τ
    end%BT.
Proof. done. Qed.
Lemma natural_size_of_compound Γ c s τs :
  ✓ Γ → Γ !! s = Some τs → size_of Γ (compoundT{c} s) =
    match c with
    | Struct_kind => sum_list (field_sizes Γ τs)
    | Union_kind =>
       let sz := foldr max 1 (size_of Γ <$> τs) in
       sz + natural_padding sz (natural_fields_align Γ τs)
    end.
Proof.
  intros. unfold size_of; simpl. unfold natural_size_of.
  by rewrite type_iter_compound by eauto
    using natural_size_of_compound_proper with typeclass_instances.
Qed.
Lemma natural_size_of_weaken Γ1 Γ2 τ :
  ✓ Γ1 → ✓{Γ1} τ → Γ1 ⊆ Γ2 → size_of Γ1 τ = size_of Γ2 τ.
Proof.
  intros. unfold size_of; simpl. unfold natural_size_of.
  apply type_iter_weaken;
    eauto using natural_size_of_compound_proper with typeclass_instances.
Qed.

Instance natural_env_spec: EnvSpec Ti.
Proof.
  split.
  * apply _.
  * intros ??. apply ptr_size_ne_0.
  * done.
  * done.
  * intros ???. unfold size_of; simpl. unfold natural_size_of.
    by rewrite type_iter_array.
  * intros Γ s τs ??. by erewrite natural_size_of_compound by eauto.
  * intros Γ τs ?. unfold field_sizes; simpl.
    change natural_size_of with size_of.
    generalize (natural_fields_align Γ τs), 0. intros align.
    induction τs; simpl; constructor; auto with lia.
  * intros Γ s τs ? Hτs. erewrite natural_size_of_compound by eauto.
    apply Forall_impl with (λ τ,
      size_of Γ τ ≤ foldr max 1 (size_of Γ <$> τs)); [|simpl; auto with lia].
    clear Hτs. induction τs; csimpl; constructor; [lia|].
    eapply Forall_impl; eauto with lia.
  * apply natural_size_of_weaken.
  * intros Γ1 Γ2 τs ? Hτs ?. unfold field_sizes; simpl.
    assert (Forall (λ τ, size_of Γ1 τ = size_of Γ2 τ) τs).
    { induction Hτs; constructor; auto using natural_size_of_weaken. }
    by erewrite natural_field_sizes_weaken,
      natural_fields_align_weaken by eauto.
Qed.

Lemma natural_align_of_divide Γ τ :
  ✓ Γ → ✓{Γ} τ → (natural_align_of Γ τ | size_of Γ τ).
Proof.
  intros HΓ. revert τ. refine (type_env_ind _ HΓ _ _ _ _).
  * intros τb. rewrite natural_align_of_base, natural_size_of_base.
    destruct 1; auto. by rewrite align_void.
  * intros τ n ? ? _. rewrite natural_align_of_array, size_of_array.
    by apply Nat.divide_mul_r.
  * intros c s τs Hs Hτs IH Hlen.
    erewrite natural_align_of_compound, natural_size_of_compound by eauto.
    assert (natural_fields_align Γ τs ≠ 0) as Hne_0.
    { clear Hs Hlen. unfold natural_fields_align.
      induction IH as [|τ τs IHτ ? IH]; decompose_Forall; simpl; [done|].
      rewrite Nat.lcm_eq_0; intros [|?]; [|by destruct IH].
      apply Nat_divide_ne_0 with (size_of Γ τ); auto using size_of_ne_0. }
    destruct c; [|by apply natural_padding_divide].
    clear Hs Hτs IH. unfold field_sizes; simpl. revert Hne_0.
    generalize (natural_fields_align Γ τs); intros whole_align ?.
    rewrite <-(Nat.add_0_l (sum_list _)). generalize 0.
    induction τs as [|τ1 τs IH]; intros pos; simpl; [done|].
    rewrite (Nat.add_assoc pos), (Nat.add_comm pos).
    destruct τs as [|τ2 τs]; [simpl|by apply IH].
    rewrite Nat.add_0_r, <-Nat.add_assoc, (Nat.add_comm _ pos),
      Nat.add_assoc; auto using natural_padding_divide.
Qed.
Lemma natural_align_ne_0 Γ τ : ✓ Γ → ✓{Γ} τ → natural_align_of Γ τ ≠ 0.
Proof.
  intros. apply Nat_divide_ne_0 with (size_of Γ τ); auto
    using natural_align_of_divide, size_of_ne_0.
Qed.
Lemma natural_field_offset Γ τs i τ :
  ✓ Γ → ✓{Γ}* τs → τs !! i = Some τ →
  (natural_align_of Γ τ | field_offset Γ τs i).
Proof.
  intros ? Hτs. revert i. cut (∀ whole_align i pos, τs !! i = Some τ →
    (default whole_align (head τs) (natural_align_of Γ) | pos) →
    (natural_align_of Γ τ | pos + sum_list (take i
       (natural_field_sizes (natural_size_of Γ) Γ whole_align pos τs)))).
  { intros help i ?. rewrite <-(Nat.add_0_l (field_offset _ _ _)).
    apply help; auto using Nat.divide_0_r. }
  intros whole_align. induction Hτs as [|τ' τs Hτ Hτs IH];
    intros [|i] pos al ?; simplify_equality'.
  { rewrite Nat.add_0_r. auto using Nat.divide_0_r. }
  rewrite Nat.add_assoc, (Nat.add_comm pos). apply IH; auto.
  clear IH. destruct τs as [|τ2 τs]; simplify_list_equality'.
  rewrite <-Nat.add_assoc, (Nat.add_comm _ pos), Nat.add_assoc.
  decompose_Forall. by apply natural_padding_divide, natural_align_ne_0.
Qed.
End natural_type_environment.
