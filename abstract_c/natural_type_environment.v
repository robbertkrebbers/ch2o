(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export type_environment.

Section natural_type_environment.
Context `{IntEnvSpec K}.
Context (ptr_size : ptr_type K → nat) (align_base : base_type K → nat).
Context (ptr_size_ne_0 : ∀ τ, ptr_size τ ≠ 0).
Context (align_void : align_base voidT = 1).
Context (align_int_divide : ∀ τi, (align_base (intT τi) | rank_size (rank τi))).
Context (align_ptr_divide : ∀ τp, (align_base (τp.*) | ptr_size τp)).
Context (alloc_can_fail : bool).

Definition natural_align_of (Γ : env K) : type K → nat := type_iter
  (**i TBase =>     *) align_base
  (**i TArray =>    *) (λ _ _ x, x)
  (**i TCompound => *) (λ c t τs rec, foldr lcm 1 (rec <$> τs)) Γ.
Definition natural_fields_align (Γ : env K) (τs : list (type K)) : nat :=
  foldr lcm 1 (natural_align_of Γ <$> τs).

Definition natural_padding (pos al : nat) : nat :=
  let z := pos `mod` al in if decide (z = 0) then 0 else al - z.

Definition natural_field_sizes (f : type K → nat) (Γ : env K)
    (whole_align : nat) : nat → list (type K) → list nat :=
  fix go pos τs :=
  match τs with
  | [] => []
  | τ :: τs =>
    let align := from_option (natural_align_of Γ) whole_align (head τs) in
    let sz := f τ + natural_padding (f τ + pos) align in
    sz :: go (sz + pos) τs
  end.
Definition natural_size_of (Γ : env K) : type K → nat :=
  type_iter
  (**i TBase =>     *) (λ τb,
    match τb with
    | voidT => 1 | intT τi => rank_size (rank τi) | τp.* => ptr_size τp
    end%BT)
  (**i TArray =>    *) (λ _, mult)
  (**i TCompound => *) (λ c t τs go,
    match c with
    | Struct_kind =>
       sum_list (natural_field_sizes go Γ (natural_fields_align Γ τs) 0 τs)
    | Union_kind =>
       let sz := foldr max 1 (go <$> τs) in
       sz + natural_padding sz (natural_fields_align Γ τs)
    end) Γ.

#[local] Instance natural_env : Env K := {
  size_of := natural_size_of;
  align_of := natural_align_of;
  field_sizes Γ τs :=
    natural_field_sizes (natural_size_of Γ) Γ (natural_fields_align Γ τs) 0 τs;
  alloc_can_fail := alloc_can_fail
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
Lemma natural_align_of_compound_proper (Γ: env K) :
  let fcompound c t τs rec := foldr lcm 1 (rec <$> τs) in
  ∀ rec1 rec2 (c : compound_kind) t (τs : list (type K)),
  Γ !! t = Some τs → Forall (λ τ, rec1 τ = rec2 τ) τs →
  fcompound c t τs rec1 = fcompound c t τs rec2.
Proof.
  intros fcompound rec1 rec2 c t τs _.
  unfold fcompound. induction 1; simpl; auto using f_equal.
Qed.
Lemma natural_align_of_base Γ τb : align_of Γ (baseT τb) = align_base τb.
Proof. done. Qed.
Lemma natural_align_of_array Γ τ n : align_of Γ (τ.[n]) = align_of Γ τ.
Proof.
  unfold align_of; simpl; unfold natural_align_of. by rewrite type_iter_array.
Qed.
Lemma natural_align_of_compound Γ c t τs :
  ✓ Γ → Γ !! t = Some τs →
  align_of Γ (compoundT{c} t) = natural_fields_align Γ τs.
Proof.
  intros. unfold align_of; simpl; unfold natural_align_of.
  by rewrite type_iter_compound by eauto
    using natural_align_of_compound_proper with typeclass_instances.
Qed.
Lemma natural_align_of_weaken Γ1 Γ2 τ :
  ✓ Γ1 → ✓{Γ1} τ → Γ1 ⊆ Γ2 → align_of Γ1 τ = align_of Γ2 τ.
Proof.
  intros. unfold align_of; simpl; unfold natural_align_of.
  apply type_iter_weaken; eauto
    using natural_align_of_compound_proper with typeclass_instances.
Qed.
Lemma natural_fields_align_weaken Γ1 Γ2 τs :
  ✓ Γ1 → ✓{Γ1}* τs → Γ1 ⊆ Γ2 →
  natural_fields_align Γ1 τs = natural_fields_align Γ2 τs.
Proof.
  intros ? Hτs ?. unfold natural_fields_align.
  induction Hτs; simpl; auto using natural_align_of_weaken.
Qed.
Lemma natural_field_sizes_weaken rec1 rec2 Γ1 Γ2 whole_align pos τs :
  ✓ Γ1 → Γ1 ⊆ Γ2 → ✓{Γ1}* τs → Forall (λ τ, rec1 τ = rec2 τ) τs →
  natural_field_sizes rec1 Γ1 whole_align pos τs =
    natural_field_sizes rec2 Γ2 whole_align pos τs.
Proof.
  intros ?? Hτs Hrec. revert pos Hτs.
  induction Hrec as [|τ τs Hτ ? IH]; intros; decompose_Forall; simpl; auto.
  rewrite Hτ, IH by done. destruct τs as [|τ2 τs]; simpl; [done|].
  decompose_Forall. by erewrite natural_align_of_weaken by eauto.
Qed.

Lemma natural_size_of_compound_proper Γ1 Γ2 rec1 rec2 c t τs :
  let fc Γ rec c (t : tag) τs :=
    match c with
    | Struct_kind =>
       sum_list (natural_field_sizes rec Γ (natural_fields_align Γ τs) 0 τs)
    | Union_kind =>
       let sz := foldr max 1 (rec <$> τs) in
       sz + natural_padding sz (natural_fields_align Γ τs)
    end in
  ✓ Γ1 → Γ1 ⊆ Γ2 → Γ1 !! t = Some τs → ✓{Γ1}* τs →
  Forall (λ τ, rec1 τ = rec2 τ) τs → fc Γ1 rec1 c t τs = fc Γ2 rec2 c t τs.
Proof.
  intros fc ??. destruct c; simpl.
  * intros _ Hτs Hrec. erewrite natural_fields_align_weaken by eauto.
    by erewrite natural_field_sizes_weaken by eauto.
  * intros. by erewrite Forall_fmap_ext_1, natural_fields_align_weaken by eauto.
Qed.
Lemma natural_size_of_base Γ τb :
  size_of Γ (baseT τb) =
    match τb with
    | voidT => 1 | intT τi => rank_size (rank τi) | τp.* => ptr_size τp
    end%BT.
Proof. done. Qed.
Lemma natural_size_of_array Γ τ n : size_of Γ (τ.[n]) = n * size_of Γ τ.
Proof. unfold size_of; simpl; unfold natural_size_of.
  by apply type_iter_array. Qed.
Lemma natural_size_of_compound Γ c t τs :
  ✓ Γ → Γ !! t = Some τs → size_of Γ (compoundT{c} t) =
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
Lemma natural_align_ne_0 Γ τ : ✓ Γ → ✓{Γ} τ → align_of Γ τ ≠ 0.
Proof.
  intros HΓ. revert τ. refine (type_env_ind _ HΓ _ _ _ _).
  * intros τb _; rewrite natural_align_of_base; destruct τb;
      rewrite ?align_void; eauto using Nat_divide_ne_0, rank_size_ne_0.
  * intros. by rewrite natural_align_of_array.
  * intros c t τs Ht _ IH _. erewrite natural_align_of_compound by eauto.
    clear Ht. unfold natural_fields_align.
    induction IH; csimpl; rewrite ?Nat.lcm_eq_0; naive_solver.
Qed.

#[local] Instance natural_env_spec: EnvSpec K.
Proof.
  split.
  * apply _.
  * intros ??. apply ptr_size_ne_0.
  * done.
  * done.
  * by apply natural_size_of_array.
  * intros Γ t τs ??. by erewrite natural_size_of_compound by eauto.
  * intros Γ τs ?. unfold field_sizes; simpl.
    change natural_size_of with size_of.
    generalize (natural_fields_align Γ τs), 0. intros align.
    induction τs; simpl; constructor; auto with lia.
  * intros Γ t τs ? Hτs. erewrite natural_size_of_compound by eauto.
    apply Forall_impl with (λ τ,
      size_of Γ τ ≤ foldr max 1 (size_of Γ <$> τs)); [|simpl; auto with lia].
    clear Hτs. induction τs; csimpl; constructor; [lia|].
    apply Forall_impl with (1:=IHτs); intros; lia.
  * intros Γ τ n. by rewrite natural_align_of_array.
  * intros Γ c t τs i τ ? Ht Hi. erewrite natural_align_of_compound by eauto.
    clear Ht. revert i τ Hi. unfold natural_fields_align.
    induction τs; intros [|?] ??; simplify_equality';
      eauto 3 using Nat.divide_trans, Nat.divide_lcm_r, Nat.divide_lcm_l.
  * intros Γ τ HΓ. revert τ. unfold size_of; simpl.
    refine (type_env_ind _ HΓ _ _ _ _).
    + intros τb. rewrite natural_align_of_base, natural_size_of_base.
      destruct 1; auto. by rewrite align_void.
    + intros τ n ? ? _. rewrite natural_align_of_array, natural_size_of_array.
      by apply Nat.divide_mul_r.
    + intros c t τs Ht Hτs IH Hlen.
      erewrite natural_align_of_compound, natural_size_of_compound by eauto.
      assert (natural_fields_align Γ τs ≠ 0) as Hne_0.
      { clear Ht Hlen. unfold natural_fields_align.
        induction IH as [|τ τs IHτ ? IH]; decompose_Forall; simpl; [done|].
        rewrite Nat.lcm_eq_0; intros [|?]; [|by destruct IH].
        by apply (natural_align_ne_0 Γ τ). }
      destruct c; [|by apply natural_padding_divide].
      clear Ht Hτs IH. unfold field_sizes; simpl. revert Hne_0.
      generalize (natural_fields_align Γ τs); intros whole_align ?.
      rewrite <-(Nat.add_0_l (sum_list _)). generalize 0.
      induction τs as [|τ1 τs IH]; intros pos; simpl; [done|].
      rewrite (Nat.add_assoc pos), (Nat.add_comm pos).
      destruct τs as [|τ2 τs]; [simpl|by apply IH].
      rewrite Nat.add_0_r, <-Nat.add_assoc, (Nat.add_comm _ pos),
        Nat.add_assoc; auto using natural_padding_divide.
  * intros Γ τs i τ ? Hτs. revert i.
    cut (∀ whole_align i pos, τs !! i = Some τ →
      (from_option (natural_align_of Γ) whole_align (head τs) | pos) →
      (natural_align_of Γ τ | pos + sum_list (take i
         (natural_field_sizes (natural_size_of Γ) Γ whole_align pos τs)))).
    { intros help i ?. rewrite <-(Nat.add_0_l (offset_of _ _ _)).
      apply help; auto using Nat.divide_0_r. }
    intros whole_align. induction Hτs as [|τ' τs Hτ Hτs IH];
      intros [|i] pos al ?; simplify_equality'.
    { rewrite Nat.add_0_r. auto using Nat.divide_0_r. }
    rewrite Nat.add_assoc, (Nat.add_comm pos). apply IH; auto.
    clear IH. destruct Hτs as [|τ2 τs]; simplify_list_eq.
    rewrite <-Nat.add_assoc, (Nat.add_comm _ pos), Nat.add_assoc.
    by apply natural_padding_divide, natural_align_ne_0.
  * apply natural_size_of_weaken.
  * apply natural_align_of_weaken.
  * intros Γ1 Γ2 τs ? Hτs ?. unfold field_sizes; simpl.
    assert (Forall (λ τ, size_of Γ1 τ = size_of Γ2 τ) τs).
    { induction Hτs; constructor; auto using natural_size_of_weaken. }
    by erewrite natural_field_sizes_weaken, natural_fields_align_weaken by eauto.
Qed.
End natural_type_environment.
