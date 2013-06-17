(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export memory_values base_values.
Local Open Scope ctype_scope.

Inductive val (Ti : Set) :=
  | VBase : base_val Ti → val Ti
  | VArray : list (val Ti) → val Ti
  | VStruct : tag → list (val Ti) → val Ti
  | VUnion : tag → nat → val Ti → val Ti
  | VUnionNone : tag → list (val Ti) → val Ti.
Arguments VBase {_} _.
Arguments VArray {_} _.
Arguments VStruct {_} _ _.
Arguments VUnion {_} _ _ _.
Arguments VUnionNone  {_} _ _.

Instance: Injective (=) (=) (@VBase Ti).
Proof. by injection 1. Qed.
Instance: Injective (=) (=) (@VArray Ti).
Proof. by injection 1. Qed.
Instance: Injective (=) (=) (@VStruct Ti s).
Proof. by injection 1. Qed.
Instance: Injective2 (=) (=) (=) (@VUnion Ti s).
Proof. by injection 1. Qed.
Instance: Injective (=) (=) (@VUnionNone Ti s).
Proof. by injection 1. Qed.

Instance val_eq_dec {Ti : Set} `{∀ τ1 τ2 : Ti, Decision (τ1 = τ2)} :
  ∀ v1 v2 : val Ti, Decision (v1 = v2).
Proof.
 refine (
  fix go v1 v2 : Decision (v1 = v2) :=
  match v1, v2 with
  | VBase v1, VBase v2 => cast_if (decide_rel (=) v1 v2)
  | VArray vs1, VArray vs2 => cast_if (decide_rel (=) vs1 vs2)
  | VStruct s1 vs1, VStruct s2 vs2 =>
     cast_if_and (decide_rel (=) s1 s2) (decide_rel (=) vs1 vs2)
  | VUnion s1 i1 v1, VUnion s2 i2 v2 =>
     cast_if_and3 (decide_rel (=) s1 s2) (decide_rel (=) i1 i2)
       (decide_rel (=) v1 v2)
  | VUnionNone s1 vs1, VUnionNone s2 vs2 =>
     cast_if_and (decide_rel (=) s1 s2) (decide_rel (=) vs1 vs2)
  | _, _ => right _
  end); clear go; abstract congruence.
Defined.

Section val_ind.
  Context {Ti} (P : val Ti → Prop).
  Context (Pbase : ∀ v, P (VBase v)).
  Context (Parray : ∀ vs, Forall P vs → P (VArray vs)).
  Context (Pstruct : ∀ s vs, Forall P vs → P (VStruct s vs)).
  Context (Punion : ∀ s i v, P v → P (VUnion s i v)).
  Context (Punion_none : ∀ s vs, Forall P vs → P (VUnionNone s vs)).
  Definition val_ind_alt: ∀ v, P v :=
    fix go v :=
    match v return P v with
    | VBase v => Pbase v
    | VArray vs => Parray _ $ list_ind (Forall _)
       (Forall_nil_2 _) (λ v _, Forall_cons_2 _ _ _ (go v)) vs
    | VStruct s vs => Pstruct _ _ $ list_ind (Forall _)
       (Forall_nil_2 _) (λ v _, Forall_cons_2 _ _ _ (go v)) vs
    | VUnion s i v => Punion _ _ _ (go v)
    | VUnionNone s vs => Punion_none _ _ $ list_ind (Forall _)
       (Forall_nil_2 _) (λ v _, Forall_cons_2 _ _ _ (go v)) vs
    end.
End val_ind.

Definition val_map {Ti} (f : base_val Ti → base_val Ti) :
    val Ti → val Ti :=
  fix go v :=
  match v with
  | VBase v => VBase (f v)
  | VArray vs => VArray (go <$> vs)
  | VStruct s vs => VStruct s (go <$> vs)
  | VUnion s i v => VUnion s i (go v)
  | VUnionNone s vs => VUnionNone s (go <$> vs)
  end.

Inductive val_forall {Ti} (P : base_val Ti → Prop) : val Ti → Prop :=
  | VBase_forall v : P v → val_forall P (VBase v)
  | VArray_forall vs : Forall (val_forall P) vs → val_forall P (VArray vs)
  | VStruct_forall s vs : Forall (val_forall P) vs → val_forall P (VStruct s vs)
  | VUnion_forall s i v : val_forall P v → val_forall P (VUnion s i v)
  | VUnionNone_forall s vs :
     Forall (val_forall P) vs → val_forall P (VUnionNone s vs).

Section val_forall_ind.
  Context {Ti} (P : base_val Ti → Prop).
  Context (Q : val Ti → Prop).
  Context (Qbase : ∀ v, P v → Q (VBase v)).
  Context (Qarray : ∀ vs,
    Forall (val_forall P) vs → Forall Q vs → Q (VArray vs)).
  Context (Qstruct : ∀ s vs,
    Forall (val_forall P) vs → Forall Q vs → Q (VStruct s vs)).
  Context (Qunion : ∀ s i v, val_forall P v → Q v → Q (VUnion s i v)).
  Context (Qunion_none : ∀ s vs,
    Forall (val_forall P) vs → Forall Q vs → Q (VUnionNone s vs)).
  Definition val_forall_ind_alt: ∀ v, val_forall P v → Q v :=
    fix go v Hv :=
    match Hv in val_forall _ v return Q v with
    | VBase_forall _ H => Qbase _ H
    | VArray_forall _ H => Qarray _ H (Forall_impl _ _ _ H go)
    | VStruct_forall _ _ H => Qstruct _ _ H (Forall_impl _ _ _ H go)
    | VUnion_forall _ _ _  H => Qunion _ _ _ H (go _ H)
    | VUnionNone_forall _ _ H => Qunion_none _ _ H (Forall_impl _ _ _ H go)
    end.
End val_forall_ind.

Section operations.
  Context `{IntEnv Ti} `{PtrEnv Ti} `{TypeOfIndex Ti M} `{IndexAlive M}.

  Global Instance type_of_val: TypeOf (type Ti) (val Ti) :=
    fix go v :=
    match v with
    | VBase v => base (type_of v)
    | VArray [] => TVoid
    | VArray (v :: vs) => go v.[length (v :: vs)]
    | VStruct s _ => struct s
    | VUnion s _ _ => union s
    | VUnionNone s _ => union s
    end.

  Definition val_new : type Ti → val Ti := type_iter
    (*i TBase     *) (λ τ, VBase (VIndet τ))
    (*i TVoid     *) (VBase (VIndet uchar)) (* dummy *)
    (*i TArray    *) (λ τ n x, VArray (replicate n x))
    (*i TCompound *) (λ c s τs rec,
      match c with
      | Struct => VStruct s (rec <$> τs)
      | Union =>
         match list_singleton_dec τs with
         | inleft (τ↾_) => VUnion s 0 (rec τ)
         | _ => VUnionNone s (rec <$> τs)
         end
      end) get_env.

  Definition val_of_bits : type Ti → list (bit Ti) → val Ti :=
    type_iter
    (*i TBase =>     *) (λ τ bs, VBase (base_val_of_bits τ bs))
    (*i TVoid =>     *) (λ bs, VBase (VIndet sint))
    (*i TArray =>    *) (λ τ n rec bs, VArray $ array_of_bits rec τ n bs)
    (*i TCompound => *) (λ c s τs rec bs,
      match c with
      | Struct => VStruct s (struct_of_bits rec τs bs)
      | Union =>
         match list_singleton_dec τs with
         | inleft (τ↾_) => VUnion s 0 (rec τ bs)
         | _ => VUnionNone s (flip rec bs <$> τs)
         end
      end) get_env.
  Fixpoint mval_to_val (w : mval Ti) : val Ti :=
    match w with
    | MBase τ bs => VBase (base_val_of_bits τ bs)
    | MArray ws => VArray (mval_to_val <$> ws)
    | MStruct s ws => VStruct s (mval_to_val <$> ws)
    | MUnion s i w => VUnion s i (mval_to_val w)
    | MUnionNone s bs => val_of_bits (union s) bs
    end.

  Definition union_of_val (f : val Ti → mval Ti) (sz : nat) :
      list (val Ti) → option (list (bit Ti)) :=
    fix go vs :=
    match vs with
    | [] => Some (replicate sz BIndet)
    | v :: vs =>
       let bs := mval_to_bits (f v) in
       go vs ≫= bits_join (resize sz BIndet bs)
    end.
  Fixpoint mval_of_val (v : val Ti) : mval Ti :=
    match v with
    | VBase v => MBase (type_of v) (base_val_to_bits v)
    | VArray vs => MArray (mval_of_val <$> vs)
    | VStruct s vs => MStruct s (mval_of_val <$> vs)
    | VUnion s i v => MUnion s i (mval_of_val v)
    | VUnionNone s vs =>
       let sz := bit_size_of (union s) in
       match union_of_val mval_of_val sz vs with
       | Some bs => MUnionNone s bs
       | None => MUnionNone s (replicate sz BIndet)
       end
    end.
  Notation val_to_bits v := (mval_to_bits (mval_of_val v)).

  Global Instance mval_lookup_byte: Lookup nat (val Ti) (mval Ti) := λ i w,
    bs ← sublist_lookup (i * char_bits) char_bits (mval_to_bits w);
    Some (val_of_bits uchar bs).
  Global Instance mval_insert_byte: Insert nat (val Ti) (mval Ti) := λ i v w,
    mval_of_bits (type_of w) $
      sublist_insert (i * char_bits) (val_to_bits v) (mval_to_bits w).

  Global Instance vtype_check: TypeCheck M (type Ti) (val Ti) := λ m,
    fix go v :=
    match v with
    | VBase v => TBase <$> type_check m v
    | VArray [] => None
    | VArray (v :: vs) =>
       τ ← go v;
       τs ← mapM go vs;
       guard (Forall (= τ) τs);
       Some (τ.[length (v :: vs)])
    | VStruct s vs =>
       τs ← get_env !! s;
       τs' ← mapM go vs;
       guard (τs = τs');
       Some (struct s)
    | VUnion s i v =>
       τ ← get_env !! s ≫= (!! i);
       τ' ← go v;
       guard (τ = τ');
       Some (union s)
    | VUnionNone s vs =>
       τs ← get_env !! s;
       guard (1 ≠ length τs);
       τs' ← mapM go vs;
       guard (τs = τs');
       let sz := bit_size_of (union s) in
       bs ← union_of_val mval_of_val sz vs;
       guard (vs = flip val_of_bits bs <$> τs);
       Some (union s)
    end.

  Global Instance val_lookup_item:
      Lookup ref_seg (val Ti) (val Ti) := λ rs v,
    match rs, v with
    | RArray i n, VArray vs => guard (n = length vs); vs !! i
    | RStruct i s, VStruct s' vs => guard (s = s'); vs !! i
    | RUnion i s _, VUnion s' j v => guard (s = s'); guard (i = j); Some v
    | RUnion i s _, VUnionNone s' vs => guard (s = s'); vs !! i
    | _, _ => None
    end.
  Global Instance val_lookup: Lookup ref (val Ti) (val Ti) :=
    fix go r v :=
    match r with
    | [] => Some v | rs :: r => @lookup _ _ _ go r v ≫= (!! rs)
    end.

  Inductive vunop_typed : unop → type Ti → type Ti → Prop :=
    | TBase_unop_typed op τ σ :
       base_unop_typed op τ σ → vunop_typed op (base τ) (base σ).
  Definition vunop_ok (op : unop) (v : val Ti) : Prop :=
    match v with
    | VBase v => base_unop_ok op v
    | _ => False
    end.
  Global Arguments vunop_ok !_ !_ /.
  Definition vunop (op : unop) (v : val Ti) : val Ti :=
    match v with
    | VBase v => VBase (base_unop op v)
    | _ => v
    end.
  Global Arguments vunop !_ !_ /.

  Inductive vbinop_typed : binop → type Ti → type Ti → type Ti → Prop :=
    | binop_TInt_TInt_typed op τ1 τ2 σ :
       base_binop_typed op τ1 τ2 σ →
       vbinop_typed op (base τ1) (base τ2) (base σ).
  Definition vbinop_ok (m : M) (op : binop) (v1 v2 : val Ti) : Prop :=
    match v1, v2 with
    | VBase v1, VBase v2 => base_binop_ok m op v1 v2
    | _, _ => False
    end.
  Global Arguments vbinop_ok _ !_ !_ !_ /.
  Definition vbinop (op : binop) (v1 v2 : val Ti) : val Ti :=
    match v1, v2 with
    | VBase v1, VBase v2 => VBase (base_binop op v1 v2)
    | _, _ => v1
    end.
  Global Arguments vbinop !_ !_ !_ /.

  Inductive vcast_typed : type Ti → type Ti → Prop :=
    | TBase_cast_typed τ1 τ2 :
       base_cast_typed τ1 τ2 → vcast_typed (base τ1) (base τ2).
  Definition vcast_ok (τ : type Ti) (v : val Ti) : Prop :=
    match v, τ with
    | VBase v, base τ => base_cast_ok τ v
    | _ , _ => False
    end.
  Global Arguments vcast_ok !_ !_ /.
  Definition vcast (τ : type Ti) (v : val Ti) : val Ti :=
    match v, τ with
    | VBase v, base τ => VBase (base_cast τ v)
    | _ , _ => v
    end.
  Global Arguments vcast !_ !_ /.
End operations.

Notation val_to_bits v := (mval_to_bits (mval_of_val v)).

Section vtyped.
  Context `{MemorySpec Ti M}.

  Inductive vtyped' (m : M) : val Ti → type Ti → Prop :=
    | VBase_typed' v τ :
       m ⊢ v : τ →
       vtyped' m (VBase v) (base τ)
    | VArray_typed' vs τ :
       Forall (λ v, vtyped' m v τ) vs →
       length vs ≠ 0 →
       vtyped' m (VArray vs) (τ.[length vs])
    | VStruct_typed' s vs τs :
       get_env !! s = Some τs →
       Forall2 (vtyped' m) vs τs →
       vtyped' m (VStruct s vs) (struct s)
    | VUnion_typed' s i τs v τ :
       get_env !! s = Some τs →
       τs !! i = Some τ →
       vtyped' m v τ →
       vtyped' m (VUnion s i v) (union s)
    | VUnionNone_typed' s vs τs bs :
       get_env !! s = Some τs → length τs ≠ 1 →
       (* we prove a smart constructor without this premise later *)
       Forall2 (vtyped' m) vs τs →
       vs = flip val_of_bits bs <$> τs →
       m ⊢* valid bs → length bs = bit_size_of (union s) →
       vtyped' m (VUnionNone s vs) (union s).
  Global Instance vtyped: Typed M (type Ti) (val Ti) := vtyped'.

  Lemma val_of_bits_base τ bs :
    val_of_bits (base τ) bs = VBase (base_val_of_bits τ bs).
  Proof. unfold val_of_bits. by rewrite type_iter_base. Qed. 
  Lemma val_of_bits_array τ n bs :
    val_of_bits (τ.[n]) bs = VArray (array_of_bits (val_of_bits τ) τ n bs).
  Proof. unfold val_of_bits. by rewrite type_iter_array. Qed.
  Lemma val_of_bits_compound c s τs bs :
    get_env !! s = Some τs →
    val_of_bits (compound@{c} s) bs =
      match c with
      | Struct => VStruct s (struct_of_bits val_of_bits τs bs)
      | Union =>
         match list_singleton_dec τs with
         | inleft (τ↾_) => VUnion s 0 (val_of_bits τ bs)
         | _ => VUnionNone s (flip val_of_bits bs <$> τs)
         end
      end.
  Proof.
    intros Hs. unfold val_of_bits. erewrite (type_iter_compound
      (pointwise_relation (list (bit Ti)) (@eq (val Ti))) _ _ _ _); eauto.
    { clear s τs Hs bs. intros τ n f g Hfg bs. f_equal.
      auto using array_of_bits_ext. }
    clear s τs Hs bs. intros f g [] s τs Hs Hτs bs.
    { f_equal. auto using struct_of_bits_ext. }
    destruct (list_singleton_dec _) as [[??]|?]; subst; f_equal.
    * by decompose_Forall.
    * apply Forall_fmap_ext. eauto using Forall_impl.
  Qed.

  Lemma VBase_typed m v τ : m ⊢ v : τ → m ⊢ VBase v : base τ.
  Proof. by constructor. Qed.
  Lemma VArray_typed m vs τ n :
    n = length vs → m ⊢* vs : τ → n ≠ 0 → m ⊢ VArray vs : τ.[n].
  Proof. intros; subst. by constructor. Qed.
  Lemma VStruct_typed m s vs τs :
    get_env !! s = Some τs → m ⊢* vs :* τs → m ⊢ VStruct s vs : struct s.
  Proof. econstructor; eauto. Qed.
  Lemma VUnion_typed m s i τs v τ :
    get_env !! s = Some τs → τs !! i = Some τ →
    m ⊢ v : τ → m ⊢ VUnion s i v : union s.
  Proof. econstructor; eauto. Qed.
  Lemma val_of_bits_resize τ bs sz :
    type_valid get_env τ → bit_size_of τ ≤ sz →
    val_of_bits τ (resize sz BIndet bs) = val_of_bits τ bs.
  Proof.
    intros Hτ. revert τ Hτ bs sz. refine (type_env_ind _ _ _ _).
    * intros τ Hτ bs sz ?. rewrite !val_of_bits_base.
      by rewrite base_val_of_bits_resize.
    * intros τ n Hτ IH _ bs sz. rewrite !val_of_bits_array, bit_size_of_array.
      intros. f_equal. auto using array_of_bits_resize.
    * intros [] s τs Hs Hτs IH _ bs sz Hsz.
      { erewrite !val_of_bits_compound by eauto.
        erewrite bit_size_of_struct in Hsz by eauto.
        f_equal. auto using struct_of_bits_resize. }
      erewrite !val_of_bits_compound by eauto.
      destruct (list_singleton_dec _) as [[τ ?]|_]; subst.
      + decompose_Forall. intros. f_equal.
        efeed pose proof bit_size_of_union_singleton; eauto with lia.
      + intros. f_equal. apply bit_size_of_union in Hs.
        induction Hs; decompose_Forall_hyps; simpl; f_equal; auto with lia.
  Qed.
  Lemma fmap_val_of_bits_resize τs bs sz :
    Forall (type_valid get_env) τs → Forall (λ τ, bit_size_of τ ≤ sz) τs →
    flip val_of_bits (resize sz BIndet bs) <$> τs = flip val_of_bits bs <$> τs.
  Proof.
    induction 1; intros; decompose_Forall_hyps; simpl; f_equal;
      auto using val_of_bits_resize.
  Qed.
  Lemma val_of_bits_typed m τ bs :
    type_valid get_env τ → m ⊢* valid bs → m ⊢ val_of_bits τ bs : τ.
  Proof.
    intros Hτ. revert τ Hτ bs. refine (type_env_ind _ _ _ _).
    * intros τ Hτ bs Hbs. rewrite val_of_bits_base. apply VBase_typed;
        auto using base_val_of_bits_typed, Forall_resize, BIndet_valid.
    * intros τ n Hτ IH Hn bs Hbs. rewrite val_of_bits_array.
      apply VArray_typed; eauto using array_of_bits_length.
      revert bs Hbs. clear Hn. induction n; simpl; auto using Forall_drop.
    * intros [] s τs Hs Hτs IH _ bs Hbs.
      { erewrite val_of_bits_compound by eauto.
        apply VStruct_typed with τs; auto. unfold struct_of_bits.
        revert bs Hbs. clear Hs Hτs. induction (bit_size_of_fields τs);
          intros; decompose_Forall; simpl; auto using Forall_drop. }
      erewrite val_of_bits_compound by eauto.
      destruct (list_singleton_dec _) as [[τ ?]|Hτs_len]; subst.
      { rewrite Forall_singleton in IH. eapply VUnion_typed, IH; eauto. }
      apply VUnionNone_typed'
        with τs (resize (bit_size_of (union s)) BIndet bs);
        auto using resize_length, Forall_resize, BIndet_valid.
      + change (vtyped' m) with (typed m).
        clear Hτs Hs Hτs_len; induction IH; simpl; constructor; auto.
      + by rewrite fmap_val_of_bits_resize by eauto using bit_size_of_union.
  Qed.
  Lemma VUnionNone_typed m s vs τs bs :
    get_env !! s = Some τs → length τs ≠ 1 →
    vs = flip val_of_bits bs <$> τs →
    m ⊢* valid bs → length bs = bit_size_of (union s) →
    m ⊢ VUnionNone s vs : union s.
  Proof.
    intros Hs Hτs_len Hvs Hbs. subst.
    eapply VUnionNone_typed'; eauto. change (vtyped' m) with (typed m).
    elim (env_valid_lookup s τs Hs); simpl;
      constructor; eauto using val_of_bits_typed.
  Qed.

  Lemma vtyped_inv_l m (P : type Ti → Prop) v τ :
    m ⊢ v : τ →
    match v with
    | VBase v => (∀ τ', m ⊢ v : τ' → P (base τ')) → P τ
    | VArray vs =>
       (∀ τ' n, n = length vs → m ⊢* vs : τ' → n ≠ 0 → P (τ'.[n])) → P τ
    | VStruct s vs =>
       (∀ τs, get_env !! s = Some τs → m ⊢* vs :* τs → P (struct s)) → P τ
    | VUnion s i v =>
       (∀ τs τ', get_env !! s = Some τs → τs !! i = Some τ' →
         m ⊢ v : τ' → P (union s)) → P τ
    | VUnionNone s vs =>
       (∀ τs bs,
         get_env !! s = Some τs → length τs ≠ 1 → m ⊢* vs :* τs →
         vs = flip val_of_bits bs <$> τs →
         m ⊢* valid bs → length bs = bit_size_of (union s) →
         P (union s)) → P τ
    end.
  Proof. destruct 1; eauto. Qed.

  Section vtyped_ind.
    Context (m : M) (P : val Ti → type Ti → Prop).
    Context (Pbase : ∀ v τ, m ⊢ v : τ → P (VBase v) (base τ)).
    Context (Parray : ∀ vs τ,
      m ⊢* vs : τ → Forall (λ v, P v τ) vs →
      length vs ≠ 0 → P (VArray vs) (τ.[length vs])).
    Context (Pstruct : ∀ s vs τs,
      get_env !! s = Some τs → m ⊢* vs :* τs → Forall2 P vs τs →
      P (VStruct s vs) (struct s)).
    Context (PUnion : ∀ s i τs v τ,
      get_env !! s = Some τs → τs !! i = Some τ → m ⊢ v : τ → P v τ →
      P (VUnion s i v) (union s)).
    Context (Punion_none : ∀ s vs τs bs,
      get_env !! s = Some τs → length τs ≠ 1 → m ⊢* vs :* τs →
      Forall2 P vs τs → vs = flip val_of_bits bs <$> τs →
      m ⊢* valid bs → length bs = bit_size_of (union s) →
      P (VUnionNone s vs) (union s)).
    Lemma vtyped_ind : ∀ v τ, vtyped' m v τ → P v τ.
    Proof.
     exact (fix go v τ H :=
      match H in vtyped' _ v τ return P v τ with
      | VBase_typed' _ _ H => Pbase _ _ H
      | VArray_typed' _ _ Hvs Hn =>
         Parray _ _ Hvs (Forall_impl _ _ _ Hvs (λ v, go _ _)) Hn
      | VStruct_typed' s _ _ Hs H =>
         Pstruct _ _ _ Hs H (Forall2_impl _ _ _ _ H go)
      | VUnion_typed' _ _ _ _ _ Hs Hτs H => PUnion _ _ _ _ _ Hs Hτs H (go _ _ H)
      | VUnionNone_typed' _ _ _ _ Hs Hτs H Hvs Hbs Hlen =>
         Punion_none _ _ _ _ Hs Hτs H (Forall2_impl _ _ _ _ H go) Hvs Hbs Hlen
      end).
    Qed.
  End vtyped_ind.

  Section vtyped_case.
    Context (m : M) (P : val Ti → type Ti → Prop).
    Context (Pbase : ∀ v τ, m ⊢ v : τ → P (VBase v) (base τ)).
    Context (Parray : ∀ vs τ,
      m ⊢* vs : τ → length vs ≠ 0 → P (VArray vs) (τ.[length vs])).
    Context (Pstruct : ∀ s vs τs,
      get_env !! s = Some τs → m ⊢* vs :* τs → P (VStruct s vs) (struct s)).
    Context (PUnion : ∀ s i τs v τ,
      get_env !! s = Some τs → τs !! i = Some τ →
      m ⊢ v : τ → P (VUnion s i v) (union s)).
    Context (Punion_none : ∀ s vs τs bs,
      get_env !! s = Some τs → length τs ≠ 1 → m ⊢* vs :* τs →
      vs = flip val_of_bits bs <$> τs →
      m ⊢* valid bs → length bs = bit_size_of (union s) →
      P (VUnionNone s vs) (union s)).
    Lemma vtyped_case : ∀ v τ, vtyped' m v τ → P v τ.
    Proof. destruct 1; eauto. Qed.
  End vtyped_case.
End vtyped.

Ltac vtyped_constructor := first
  [ eapply VBase_typed | eapply VArray_typed | eapply VStruct_typed
  | eapply VUnion_typed | eapply VUnionNone_typed ].

Section val_le.
  Inductive val_le' `{MemorySpec Ti M} (m : M) : relation (val Ti) :=
    | VBase_le' v1 v2 : v1 ⊑@{m} v2 → val_le' m (VBase v1) (VBase v2)
    | VArray_le' vs1 vs2 :
       Forall2 (val_le' m) vs1 vs2 → val_le' m (VArray vs1) (VArray vs2)
    | VStruct_le' s vs1 vs2 :
       Forall2 (val_le' m) vs1 vs2 → val_le' m (VStruct s vs1) (VStruct s vs2)
    | VUnion_le' s i v1 v2 :
       val_le' m v1 v2 → val_le' m (VUnion s i v1) (VUnion s i v2)
    | VUnionNone_le_refl' s vs : val_le' m (VUnionNone s vs) (VUnionNone s vs)
    | VUnionNone_le' s vs1 vs2 τs bs1 bs2 :
       get_env !! s = Some τs →
       vs1 = flip val_of_bits bs1 <$> τs →
       m ⊢* valid bs1 →
       vs2 = flip val_of_bits bs2 <$> τs →
       bs1 ⊑@{m}* bs2 → length bs2 = bit_size_of (union s) →
       val_le' m (VUnionNone s vs1) (VUnionNone s vs2)
    | VUnion_VUnionNone_le' s i τs v1 v2 vs2 bs2 :
       get_env !! s = Some τs → length τs ≠ 1 →
       vs2 !! i = Some v2 →
       val_le' m v1 v2 →
       vs2 = flip val_of_bits bs2 <$> τs →
       m ⊢* valid bs2 → length bs2 = bit_size_of (union s) →
       val_le' m (VUnion s i v1) (VUnionNone s vs2).

  Context `{MemorySpec Ti M}.

  Global Instance val_le: SubsetEqEnv M (val Ti) := val_le'.

  Lemma VBase_le m v1 v2 : v1 ⊑@{m} v2 → VBase v1 ⊑@{m} VBase v2.
  Proof. by constructor. Qed.
  Lemma VArray_le m vs1 vs2 : vs1 ⊑@{m}* vs2 → VArray vs1 ⊑@{m} VArray vs2.
  Proof. by constructor. Qed.
  Lemma VStruct_le m s vs1 vs2 :
    vs1 ⊑@{m}* vs2 → VStruct s vs1 ⊑@{m} VStruct s vs2.
  Proof. by constructor. Qed.
  Lemma VUnion_le m s i v1 v2 : v1 ⊑@{m} v2 → VUnion s i v1 ⊑@{m} VUnion s i v2.
  Proof. by constructor. Qed.
  Lemma VUnionNone_le_refl m s vs : VUnionNone s vs ⊑@{m} VUnionNone s vs.
  Proof. by constructor. Qed.
  Lemma VUnionNone_le m s vs1 vs2 τs bs1 bs2 :
    get_env !! s = Some τs →
    vs1 = flip val_of_bits bs1 <$> τs →
    m ⊢* valid bs1 →
    vs2 = flip val_of_bits bs2 <$> τs →
    bs1 ⊑@{m}* bs2 → length bs2 = bit_size_of (union s) →
    VUnionNone s vs1 ⊑@{m} VUnionNone s vs2.
  Proof. econstructor; eauto. Qed.
  Lemma VUnion_VUnionNone_le m s i τs v1 v2 vs2 bs2 :
    get_env !! s = Some τs → length τs ≠ 1 →
    vs2 !! i = Some v2 →
    v1 ⊑@{m} v2 →
    vs2 = flip val_of_bits bs2 <$> τs →
    m ⊢* valid bs2 → length bs2 = bit_size_of (union s) →
    VUnion s i v1 ⊑@{m} VUnionNone s vs2.
  Proof. econstructor; eauto. Qed.

  Lemma val_of_bits_le m τ bs1 bs2 :
    type_valid get_env τ →
    m ⊢* valid bs1 → bs1 ⊑@{m}* bs2 →
    val_of_bits τ bs1 ⊑@{m} val_of_bits τ bs2.
  Proof.
    intros Hτ. revert τ Hτ bs1 bs2. refine (type_env_ind _ _ _ _).
    * intros τ ? bs1 bs2 Hbs. rewrite !val_of_bits_base. constructor.
      apply base_val_of_bits_le;
        auto using Forall_resize, BIndet_valid, Forall2_resize.
    * intros τ n ? IH _ bs1 bs2 Hbs1 Hbs.
      rewrite !val_of_bits_array. apply VArray_le. revert bs1 bs2 Hbs1 Hbs.
      induction n; simpl; auto using Forall2_take, Forall2_drop, Forall_drop.
    * intros [] s τs Hs Hτs IH _ bs1 bs2 Hbs1 Hbs.
      { erewrite !val_of_bits_compound by eauto. apply VStruct_le.
        clear Hs Hτs. unfold struct_of_bits. revert bs1 bs2 Hbs1 Hbs.
        induction (field_bit_sizes_same_length τs);
          intros; decompose_Forall; simpl;
          auto using Forall2_take, Forall2_drop, Forall_drop. }
      erewrite !val_of_bits_compound by eauto.
      destruct (list_singleton_dec _) as [[??]|?]; subst; simpl.
      { rewrite Forall_singleton in IH. apply VUnion_le. auto. }
      apply VUnionNone_le with τs (resize (bit_size_of (union s)) BIndet bs1)
          (resize (bit_size_of (union s)) BIndet bs2);
        rewrite ?resize_length, ?fmap_val_of_bits_resize by
          auto using bit_size_of_union;
        auto using Forall_resize, BIndet_valid, Forall2_resize, BIndet_le.
  Qed.

  Lemma val_le_inv_l m (P : val Ti → Prop) v1 v2 :
    v1 ⊑@{m} v2 →
    match v1 with
    | VBase v1 => (∀ v2, v1 ⊑@{m} v2 → P (VBase v2)) → P v2
    | VArray vs1 => (∀ vs2, vs1 ⊑@{m}* vs2 → P (VArray vs2)) → P v2
    | VStruct s vs1 => (∀ vs2, vs1 ⊑@{m}* vs2 → P (VStruct s vs2)) → P v2 
    | VUnion s i v1 =>
       (∀ v2, v1 ⊑@{m} v2 → P (VUnion s i v2)) →
       (∀ τs v2 vs2 bs2,
         get_env !! s = Some τs → length τs ≠ 1 →
         vs2 !! i = Some v2 →
         v1 ⊑@{m} v2 →
         vs2 = flip val_of_bits bs2 <$> τs →
         m ⊢* valid bs2 → length bs2 = bit_size_of (union s) →
         P (VUnionNone s vs2)) → P v2
    | VUnionNone s vs1 =>
       P (VUnionNone s vs1) →
       (∀ vs2 τs bs1 bs2,
         get_env !! s = Some τs →
         vs1 = flip val_of_bits bs1 <$> τs →
         m ⊢* valid bs1 →
         vs2 = flip val_of_bits bs2 <$> τs →
         bs1 ⊑@{m}* bs2 → length bs2 = bit_size_of (union s) →
         P (VUnionNone s vs2)) → P v2
    end.
  Proof. destruct 1; eauto. Qed.

  Lemma val_le_inv m (P : Prop) v1 v2 :
    v1 ⊑@{m} v2 →
    match v1, v2 with
    | VBase v1, VBase v2 => (v1 ⊑@{m} v2 → P) → P
    | VArray vs1, VArray vs2 => (vs1 ⊑@{m}* vs2 → P) → P
    | VStruct s1 vs1, VStruct s2 vs2 => (s1 = s2 → vs1 ⊑@{m}* vs2 → P) → P 
    | VUnion s1 i1 v1, VUnion s2 i2 v2 =>
       (s1 = s2 → i1 = i2 → v1 ⊑@{m} v2 → P) → P
    | VUnionNone s1 vs1, VUnionNone s2 vs2 =>
       (s1 = s2 → vs1 = vs2 → P) →
       (∀ τs bs1 bs2,
         s1 = s2 →
         get_env !! s1 = Some τs →
         vs1 = flip val_of_bits bs1 <$> τs →
         m ⊢* valid bs1 →
         vs2 = flip val_of_bits bs2 <$> τs →
         bs1 ⊑@{m}* bs2 → length bs2 = bit_size_of (union s1) → P) → P
    | VUnion s1 i v1, VUnionNone s2 vs2 =>
       (∀ τs v2 bs2,
         s1 = s2 →
         get_env !! s1 = Some τs →
         length τs ≠ 1 →
         vs2 !! i = Some v2 →
         v1 ⊑@{m} v2 →
         vs2 = flip val_of_bits bs2 <$> τs →
         m ⊢* valid bs2 → length bs2 = bit_size_of (union s1) → P) → P
    | _, _ => P
    end.
  Proof. destruct 1; eauto. Qed.

  Section val_le_ind.
    Context (m : M) (P : val Ti → val Ti → Prop).
    Context (Pbase : ∀ v1 v2, v1 ⊑@{m} v2 → P (VBase v1) (VBase v2)).
    Context (Parray : ∀ vs1 vs2,
      vs1 ⊑@{m}* vs2 → Forall2 P vs1 vs2 → P (VArray vs1) (VArray vs2)).
    Context (Pstruct : ∀ s vs1 vs2,
      vs1 ⊑@{m}* vs2 → Forall2 P vs1 vs2 → P (VStruct s vs1) (VStruct s vs2)).
    Context (Punion : ∀ s i v1 v2,
      v1 ⊑@{m} v2 → P v1 v2 → P (VUnion s i v1) (VUnion s i v2)).
    Context (Punion_none_refl : ∀ s vs, P (VUnionNone s vs) (VUnionNone s vs)).
    Context (Punion_none : ∀ s vs1 vs2 τs bs1 bs2,
      get_env !! s = Some τs →
      vs1 = flip val_of_bits bs1 <$> τs →
      m ⊢* valid bs1 →
      vs2 = flip val_of_bits bs2 <$> τs →
      bs1 ⊑@{m}* bs2 → length bs2 = bit_size_of (union s) →
      vs1 ⊑@{m}* vs2 → Forall2 P vs1 vs2 →
      P (VUnionNone s vs1) (VUnionNone s vs2)).
    Context (Punion_union_none : ∀ s i τs v1 v2 vs2 bs2,
      get_env !! s = Some τs → length τs ≠ 1 →
      vs2 !! i = Some v2 →
      v1 ⊑@{m} v2 → P v1 v2 →
      vs2 = flip val_of_bits bs2 <$> τs →
      m ⊢* valid bs2 → length bs2 = bit_size_of (union s) →
      P (VUnion s i v1) (VUnionNone s vs2)).
    Lemma val_le_ind: ∀ v1 v2, val_le' m v1 v2 → P v1 v2.
    Proof.
      assert (∀ vs1 vs2,
        vs1 ⊑@{m}* vs2 → Forall (λ v1, ∀ v2, v1 ⊑@{m} v2 → P v1 v2) vs1 →
        Forall2 P vs1 vs2).
      { induction 1; intros; decompose_Forall; auto. }
      assert (∀ τs bs1 bs2,
        Forall (type_valid get_env) τs → m ⊢* valid bs1 →
        bs1 ⊑@{m}* bs2 →
        flip val_of_bits bs1 <$> τs ⊑@{m}* flip val_of_bits bs2 <$> τs).
      { induction 1; simpl; constructor; eauto using val_of_bits_le. }
      induction v1 using val_ind_alt;
        intros ? Hv1v2; apply (val_le_inv_l _ _ _ _ Hv1v2);
        intros; subst; eauto 7 using env_valid_lookup.
    Qed.
  End val_le_ind.
End val_le.

Ltac val_le_constructor := first
  [ eapply VBase_le | eapply VArray_le | eapply VStruct_le
  | eapply VUnion_le | eapply VUnionNone_le_refl
  | eapply VUnionNone_le | eapply VUnion_VUnionNone_le ].

Inductive union_free `{IntEnv Ti} `{PtrEnv Ti} : val Ti → Prop :=
  | VBase_union_free v : union_free (VBase v)
  | VArray_union_free vs : Forall union_free vs → union_free (VArray vs)
  | VStruct_union_free s vs : Forall union_free vs → union_free (VStruct s vs)
  | VUnion_union_free s v τ :
     get_env !! s = Some [τ] → union_free v → union_free (VUnion s 0 v)
  | VUnionNone_union_free s vs :
     Forall union_free vs → union_free (VUnionNone s vs).

Section union_free_ind.
  Context `{IntEnv Ti} `{PtrEnv Ti} (P : val Ti → Prop).
  Context (Pbase : ∀ v, P (VBase v)).
  Context (Parray : ∀ vs, Forall union_free vs → Forall P vs → P (VArray vs)).
  Context (Pstruct : ∀ s vs,
    Forall union_free vs → Forall P vs → P (VStruct s vs)).
  Context (Punion : ∀ s v τ,
    get_env !! s = Some [τ] → union_free v → P v → P (VUnion s 0 v)).
  Context (Punion_none : ∀ s vs,
    Forall union_free vs → Forall P vs → P (VUnionNone s vs)).
  Lemma union_free_ind_alt: ∀ v, union_free v → P v.
  Proof.
   exact (
    fix go v Hv :=
    match Hv in union_free v return P v with
    | VBase_union_free _ => Pbase _
    | VArray_union_free _ H => Parray _ H (Forall_impl _ _ _ H go)
    | VStruct_union_free _ _ H => Pstruct _ _ H (Forall_impl _ _ _ H go)
    | VUnion_union_free _ _ _ Hs H => Punion _ _ _ Hs H (go _ H)
    | VUnionNone_union_free _ _ H => Punion_none _ _ H (Forall_impl _ _ _ H go)
    end).
  Qed.
  Global Instance union_free_dec: ∀ v, Decision (union_free v).
   refine (
    fix go v :=
    match v return Decision (union_free v) with
    | VBase v => left _
    | VArray vs => cast_if (decide (Forall union_free vs))
    | VStruct _ vs => cast_if (decide (Forall union_free vs))
    | VUnion s i v =>
       if decide (i = 0) then
         match Some_dec (get_env !! s) with
         | inleft(τs↾_) =>
           match list_singleton_dec τs with
           | inleft (_↾_) => cast_if (decide (union_free v))
           | inright _ => right _
           end
         | _ => right _
         end
       else right _
    | VUnionNone _ vs => cast_if (decide (Forall union_free vs))
    end); first
      [ subst; econstructor; eauto
      | by inversion 1; simplify_option_equality].
  Defined.
End union_free_ind.

Section val.
Context `{MemorySpec Ti M}.
Implicit Types v : val Ti.
Implicit Types vs : list (val Ti).
Implicit Types w : mval Ti.
Implicit Types ws : list (mval Ti).
Implicit Types m : M.
Implicit Types τ : type Ti.
Implicit Types τs : list (type Ti).
Implicit Types bs : list (bit Ti).
Implicit Types r : ref.
Implicit Types rs : ref_seg.

Lemma vtyped_not_void m v τ : m ⊢ v : τ → τ ≠ void.
Proof. by destruct 1. Qed.
Lemma vtyped_type_valid m v τ : m ⊢ v : τ → type_valid get_env τ.
Proof.
  induction 1 using @vtyped_ind; econstructor; decompose_Forall_hyps;
    try match goal with
    | H : length ?vs ≠ 0, H2 : Forall _ ?vs |- _ => destruct H2; [done|]
    end; eauto using base_typed_type_valid.
Qed.
Global Instance: TypeOfSpec M (type Ti) (val Ti).
Proof.
  induction 1 using @vtyped_ind; decompose_Forall_hyps;
    try match goal with
    | H : length ?vs ≠ 0, H2 : Forall _ ?vs |- _ => destruct H2; [done|]
    end; simpl; eauto using type_of_correct with f_equal.
Qed.
Lemma vtyped_weaken_mem m1 m2 v τ :
  (∀ x σ, type_of_index m1 x = Some σ → type_of_index m2 x = Some σ) →
  m1 ⊢ v : τ → m2 ⊢ v : τ.
Proof.
  intro. induction 1 using @vtyped_ind;
    econstructor; eauto using base_typed_weaken_mem, bits_valid_weaken_mem.
Qed.
Lemma val_le_weaken_mem m1 m2 v1 v2 :
  (∀ x σ, type_of_index m1 x = Some σ → type_of_index m2 x = Some σ) →
  v1 ⊑@{m1} v2 → v1 ⊑@{m2} v2.
Proof.
  intro. induction 1 using @val_le_ind; econstructor; eauto using
    base_val_le_weaken_mem, bits_le_weaken_mem, bits_valid_weaken_mem.
Qed.

Lemma fmap_val_of_bits_typed m τs bs :
  Forall (type_valid get_env) τs → m ⊢* valid bs →
  m ⊢* (flip val_of_bits bs <$> τs) :* τs.
Proof. intros Hτs Hbs. induction Hτs; simpl; auto using val_of_bits_typed. Qed.
Lemma val_of_bits_type_of m τ bs :
  type_valid get_env τ → m ⊢* valid bs →
  type_of (val_of_bits τ bs) = τ.
Proof. intros. eapply type_of_correct, val_of_bits_typed; eauto. Qed.
Lemma val_of_bits_fmap_type_of m τs bs :
  Forall (type_valid get_env) τs → m ⊢* valid bs →
  type_of <$> flip val_of_bits bs <$> τs = τs.
Proof. induction 1; simpl; eauto using val_of_bits_type_of with f_equal. Qed.

Lemma val_of_bits_trans m τ bs1 bs2 bs3 :
  type_valid get_env τ → bs1 ⊑@{m}* bs2 → bs2 ⊑@{m}* bs3 →
  val_of_bits τ bs1 = val_of_bits τ bs3 →
  val_of_bits τ bs2 = val_of_bits τ bs3.
Proof.
  intros Hτ. revert τ Hτ bs1 bs2 bs3. refine (type_env_ind _ _ _ _).
  * intros τ ? bs1 bs2 bs3 ??. rewrite !val_of_bits_base.
    intros. f_equal. simplify_equality.
    eauto using bits_le_resize, base_val_of_bits_trans.
  * intros τ n ? IH _ bs1 bs2 bs3 Hbs1 Hbs2. rewrite !val_of_bits_array.
    intros Hbs3. f_equal. simplify_equality. revert bs1 bs2 bs3 Hbs1 Hbs2 Hbs3.
    induction n; simpl; intros; f_equal; simplify_list_equality;
      eauto using Forall2_drop, Forall2_take.
  * intros [] s τs Hs Hτs IH _ bs1 bs2 bs3 Hbs1 Hbs2.
    { erewrite !val_of_bits_compound by eauto.
      intros Hbs3. f_equal. simplify_equality.
      clear Hs Hτs. revert bs1 bs2 bs3 Hbs1 Hbs2 Hbs3. unfold struct_of_bits.
      induction (field_bit_sizes_same_length τs); simpl in *;
        decompose_Forall; intros; f_equal; simplify_list_equality;
        eauto using Forall2_drop, Forall2_take. }
    erewrite !val_of_bits_compound by eauto.
    destruct (list_singleton_dec _) as [[??]|_];
      intros Hbs3; f_equal; simplify_equality; decompose_Forall; eauto.
    clear Hs Hτs. revert bs1 bs2 bs3 Hbs1 Hbs2 Hbs3.
    induction IH; simpl; intros; f_equal; simplify_list_equality; eauto.
Qed.

Lemma val_freeze_frozen v : val_forall frozen (val_map freeze v).
Proof.
  induction v using val_ind_alt; simpl; constructor;
    auto using base_val_freeze_frozen; by apply Forall_fmap.
Qed.
Lemma val_frozen_freeze v : val_forall frozen v → val_map freeze v = v.
Proof.
  assert (∀ vs,
    Forall (λ v, val_map freeze v = v) vs → val_map freeze <$> vs = vs).
  { induction 1; simpl; f_equal; auto. }
  induction 1 using @val_forall_ind_alt; simpl; f_equal;
    auto using base_val_frozen_freeze.
Qed.
Lemma val_freeze_idempotent v :
  val_map freeze (val_map freeze v) = val_map freeze v.
Proof. apply val_frozen_freeze, val_freeze_frozen. Qed.
Lemma val_freeze_type_of v : type_of (val_map freeze v) = type_of v.
Proof.
  induction v using val_ind_alt; simpl; simpl; auto.
   * by rewrite base_val_freeze_type_of.
   * by match goal with
     | H: Forall (λ _, type_of _ = _) _ |- _ => destruct H
     end; simpl; f_equal; rewrite ?fmap_length.
Qed.

Lemma vals_freeze_frozen vs :
  Forall (val_forall frozen) (val_map freeze <$> vs).
Proof. induction vs; constructor; auto using val_freeze_frozen. Qed.
Lemma vals_frozen_freeze vs :
  Forall (val_forall frozen) vs → val_map freeze <$> vs = vs.
Proof. induction 1; simpl; f_equal; eauto using val_frozen_freeze. Qed.
Lemma vals_freeze_idempotent vs :
  val_map freeze <$> val_map freeze <$> vs = val_map freeze <$> vs.
Proof. apply vals_frozen_freeze, vals_freeze_frozen. Qed.
Lemma vals_freeze_type_of vs :
  type_of <$> val_map freeze <$> vs = type_of <$> vs.
Proof. induction vs; simpl; f_equal; auto using val_freeze_type_of. Qed.
Lemma vtyped_int_frozen m v τi : m ⊢ v : intt τi → val_forall frozen v.
Proof. inversion_clear 1; constructor. eauto using base_typed_int_frozen. Qed.

Lemma val_of_bits_frozen m τ bs :
  type_valid get_env τ → m ⊢* valid bs → val_forall frozen (val_of_bits τ bs).
Proof.
  intros Hτ. revert τ Hτ bs. refine (type_env_ind _ _ _ _).
  * intros. rewrite val_of_bits_base. constructor.
    eapply base_val_of_bits_frozen; eauto using Forall_resize, BIndet_valid.
  * intros τ n ? IH _ bs Hbs. rewrite val_of_bits_array. constructor.
    revert bs Hbs. induction n; simpl; auto using Forall_drop.
  * intros [] s τs Hs _ IH _ bs Hbs.
    { erewrite val_of_bits_compound by eauto. constructor.
      unfold struct_of_bits. revert bs Hbs. clear Hs.
      induction (bit_size_of_fields τs);
        intros; decompose_Forall; simpl; auto using Forall_drop. }
    erewrite val_of_bits_compound by eauto.
    destruct (list_singleton_dec _) as [[??]|?]; subst;
      decompose_Forall; constructor; auto.
    apply Forall_fmap. elim IH; constructor; eauto.
Qed.
Lemma vals_of_bits_frozen m τs bs :
  Forall (type_valid get_env) τs → m ⊢* valid bs →
  Forall (val_forall frozen) (flip val_of_bits bs <$> τs).
Proof.
  intros. eapply Forall_fmap, Forall_impl; eauto.
  intros. eapply val_of_bits_frozen; eauto.
Qed.

Lemma typed_freeze m v τ : m ⊢ v : τ → m ⊢ val_map freeze v : τ.
Proof.
  induction 1 using @vtyped_ind; simpl.
  * vtyped_constructor. by apply base_typed_freeze.
  * vtyped_constructor; auto. by rewrite fmap_length. by apply Forall_fmap.
  * vtyped_constructor; eauto. by apply Forall2_fmap_l.
  * vtyped_constructor; eauto.
  * subst. rewrite vals_frozen_freeze by
      eauto using vals_of_bits_frozen, env_valid_lookup.
    vtyped_constructor; eauto.
Qed.

Lemma vtyped_ge m v1 v2 τ : m ⊢ v1 : τ → v1 ⊑@{m} v2 → m ⊢ v2 : τ.
Proof.
  assert (∀ vs1 vs2 τ,
    Forall2 (λ v1 v2, ∀ τ, m ⊢ v1 : τ → m ⊢ v2 : τ) vs1 vs2 →
    m ⊢* vs1 : τ → m ⊢* vs2 : τ).
  { induction 1; intros; decompose_Forall; auto. }
  assert (∀ vs1 vs2 τs,
    Forall2 (λ v1 v2, ∀ τ, m ⊢ v1 : τ → m ⊢ v2 : τ) vs1 vs2 →
    m ⊢* vs1 :* τs → m ⊢* vs2 :* τs).
  { intros vs1 vs2 τs Hvs. revert τs.
    induction Hvs; intros; decompose_Forall; auto. }
  intros Hv1τ Hv1v2. revert τ Hv1τ. induction Hv1v2 using @val_le_ind;
    intros ? Hv1τ; apply (vtyped_inv_l _ _ _ _ Hv1τ); intros; clear Hv1τ;
    simplify_map_equality; vtyped_constructor; eauto using
      bits_valid_ge, Forall2_length, base_typed_ge.
Qed.
Lemma vtyped_le m v1 v2 τ : m ⊢ v1 : τ → v2 ⊑@{m} v1 → m ⊢ v2 : τ.
Proof.
  assert (∀ vs1 vs2 τ,
    Forall2 (λ v2 v1, ∀ τ, m ⊢ v1 : τ → m ⊢ v2 : τ) vs1 vs2 →
    m ⊢* vs2 : τ → m ⊢* vs1 : τ).
  { induction 1; intros; decompose_Forall; auto. }
  assert (∀ vs1 vs2 τs,
    Forall2 (λ v2 v1, ∀ τ, m ⊢ v1 : τ → m ⊢ v2 : τ) vs1 vs2 →
    m ⊢* vs2 :* τs → m ⊢* vs1 :* τs).
  { intros vs1 vs2 τs Hvs. revert τs.
    induction Hvs; intros; decompose_Forall; auto. }
  assert (∀ s i τs v1 v2 vs bs,
    get_env !! s = Some τs →
    v1 ⊑@{m} v2 → vs !! i = Some v2 →
    vs = flip val_of_bits bs <$> τs → m ⊢* valid bs →
    (∀ τ, m ⊢ v2 : τ → m ⊢ v1 : τ) →
    m ⊢ VUnion s i v1 : union s).
  { intros. subst. edestruct @list_lookup_fmap_inv as [? [??]]; eauto.
    subst. vtyped_constructor; eauto using val_of_bits_typed,
      env_valid_lookup_lookup. }
  intros Hv1τ Hv1v2. revert τ Hv1τ. induction Hv1v2 using @val_le_ind;
    intros ? Hv1τ; apply (vtyped_inv_l _ _ _ _ Hv1τ); intros;
    simplify_map_equality; first
     [ by eauto using vunion_none_typed_alt
     | by eauto
     | vtyped_constructor; eauto using base_typed_le ].
  * by erewrite <-Forall2_length by eauto.
  * by erewrite Forall2_length by eauto.
Qed.

Lemma val_of_bits_masked m τ bs1 bs2 bs3 :
  type_valid get_env τ →
  bs1 ⊑@{m}* bs2 → m ⊢* valid bs3 →
  bit_size_of τ ≤ length bs2 → length bs2 = length bs3 →
  val_of_bits τ bs2 = val_of_bits τ bs3 →
  val_of_bits τ (mask_bits bs1 bs3) = val_of_bits τ bs1.
Proof.
  intros Hτ. revert τ Hτ bs1 bs2 bs3. refine (type_env_ind _ _ _ _).
  * intros τ ? bs1 bs2 bs3 ????. rewrite !val_of_bits_base, !(injective_iff _).
    eauto using base_val_of_bits_masked.
  * intros τ n ? IH _ bs1 bs2 bs3.
    rewrite !bit_size_of_array, !val_of_bits_array, !(injective_iff _).
    revert bs1 bs2 bs3.
    induction n as [|n IHn]; intros; simplify_equality'; f_equal.
    + eapply IH; eauto using Forall2_drop with lia.
    + rewrite mask_bits_drop. eapply IHn; eauto using Forall2_drop,
        Forall_drop; rewrite ?drop_length; lia.
  * intros [] s τs Hs Hτs IH _ bs1 bs2 bs3.
    { erewrite !val_of_bits_compound, !(injective_iff _),
        bit_size_of_struct by eauto. revert bs1 bs2 bs3; clear Hs Hτs.
      unfold struct_of_bits.
      induction (bit_size_of_fields τs) as [|?????? IHτs];
        inversion IH as [|?? IH']; intros; simplify_equality'; f_equal.
      + eapply IH'; eauto using Forall2_drop with lia.
      + rewrite mask_bits_drop. eapply IHτs; eauto using Forall2_drop,
          Forall_drop; rewrite ?drop_length; lia. }
    erewrite !val_of_bits_compound by eauto.
    intros. destruct (list_singleton_dec _) as [[??]|_]; subst.
    + simplify_equality; f_equal. rewrite Forall_singleton in IH.
      eapply IH; eauto. transitivity (bit_size_of (union s));
        eauto using bit_size_of_union_singleton.
    + simplify_equality; f_equal. apply bit_size_of_union in Hs.
      clear Hτs. induction IH; decompose_Forall;
        simplify_equality'; f_equal; eauto with lia.
Qed.
Lemma fmap_val_of_bits_masked m τs bs1 bs2 bs3 :
  Forall (type_valid get_env) τs →
  bs1 ⊑@{m}* bs2 → m ⊢* valid bs3 →
  Forall (λ τ, bit_size_of τ ≤ length bs2) τs →
  length bs2 = length bs3 →
  flip val_of_bits bs2 <$> τs = flip val_of_bits bs3 <$> τs →
  flip val_of_bits (mask_bits bs1 bs3) <$> τs = flip val_of_bits bs1 <$> τs.
Proof.
  induction 1; intros; decompose_Forall; simplify_list_equality'; f_equal;
    eauto using val_of_bits_masked.
Qed.

Global Instance: PartialOrder (@subseteq_env M (val Ti) _ m).
Proof.
  intros m. repeat split.
  * assert (∀ vs, Forall (λ v, v ⊑@{m} v) vs → vs ⊑@{m}* vs).
    { induction 1; constructor; auto. }
    intros v. induction v using val_ind_alt; econstructor; auto.
  * assert (∀ vs1 vs2 vs3,
      Forall2 (λ v1 v2, ∀ v3, v2 ⊑@{m} v3 → v1 ⊑@{m} v3) vs1 vs2 →
      vs2 ⊑@{m}* vs3 → vs1 ⊑@{m}* vs3).
    { intros ???. apply Forall2_transitive. eauto. }
    assert (∀ s i τs vs2 vs3 v1 v2 bs2 bs3,
      get_env !! s = Some τs → length τs ≠ 1 →
      vs2 !! i = Some v2 → v1 ⊑@{m} v2 → (∀ v3, v2 ⊑@{m} v3 → v1 ⊑@{m} v3) →
      bs2 ⊑@{m}* bs3 →
      vs2 = flip val_of_bits bs2 <$> τs → m ⊢* valid bs2 →
      vs3 = flip val_of_bits bs3 <$> τs → length bs3 = bit_size_of (union s) →
      VUnion s i v1 ⊑@{m} VUnionNone s vs3).
    { intros s i τs ?? v1 v2 bs2 bs3 Hs Hτs Hv2 ???????; subst.
      destruct (list_lookup_fmap_inv _ _ _ _ Hv2) as [τ [Hτ ?]]. subst.
      simpl in *. apply VUnion_VUnionNone_le with τs (val_of_bits τ bs3) bs3;
        eauto using val_of_bits_le, env_valid_lookup_lookup, bits_valid_ge.
      rewrite list_lookup_fmap. by simplify_option_equality. }
    assert (∀ s τs vs1 vs2 vs3 bs1 bs2 bs2' bs3,
      get_env !! s = Some τs →
      bs1 ⊑@{m}* bs2 → length bs2 = bit_size_of (union s) →
      vs1 = flip val_of_bits bs1 <$> τs → m ⊢* valid bs1 →
      vs2 = flip val_of_bits bs2 <$> τs →
      bs2' ⊑@{m}* bs3 → length bs3 = bit_size_of (union s) →
      vs2 = flip val_of_bits bs2' <$> τs → m ⊢* valid bs2' →
      vs3 = flip val_of_bits bs3 <$> τs →
      VUnionNone s vs1 ⊑@{m} VUnionNone s vs3).
    { intros s τs ??? bs1 bs2 bs2' bs3 ?? Hbs2 ????????; subst.
      apply VUnionNone_le with τs (mask_bits bs1 bs2') bs3; eauto.
      * symmetry. eapply fmap_val_of_bits_masked; eauto using env_valid_lookup.
        + rewrite Hbs2. by apply bit_size_of_union.
        + by erewrite (Forall2_length _ bs2' bs3), Hbs2 by eauto.
      * by apply mask_bits_valid.
      * transitivity bs2'; auto. apply mask_bits_le_same_length; auto.
        erewrite (Forall2_length _ bs1), (Forall2_length _ bs2' bs3) by eauto.
        congruence. }
    intros v1 v2 v3 Hv1v2. revert v3. induction Hv1v2 using @val_le_ind;
      intros ? Hv2v3; apply (val_le_inv_l _ _ _ _ Hv2v3); intros;
      simplify_map_equality; first
       [ by eauto | val_le_constructor; eauto; etransitivity; eauto ].
  * assert (∀ vs1 vs2,
      Forall2 (λ v1 v2, v2 ⊑@{m} v1 → v1 = v2) vs1 vs2 →
      vs2 ⊑@{m}* vs1 → vs1 = vs2).
    { induction 1; inversion_clear 1; f_equal; auto. }
    assert (∀ vs1 vs2 τs bs1 bs2,
      Forall (type_valid get_env) τs →
      Forall2 (λ v1 v2, v2 ⊑@{m} v1 → v1 = v2) vs1 vs2 →
      bs1 ⊑@{m}* bs2 →
      vs2 = flip val_of_bits bs1 <$> τs → m ⊢* valid bs1 →
      vs1 = flip val_of_bits bs2 <$> τs → vs1 = vs2).
    { intros ?? τs ?? Hτs ?????. subst. induction Hτs; simpl in *;
        decompose_Forall; f_equal; eauto using val_of_bits_le. }
    induction 1 using @val_le_ind;
      intros Hv2v1; apply (val_le_inv _ _ _ _ Hv2v1); intros;
      f_equal; eauto using env_valid_lookup;
      by apply (anti_symmetric (⊑@{m})).
Qed.

Lemma union_free_freeze v : union_free (val_map freeze v) ↔ union_free v.
Proof.
  split.
  * assert (∀ vs,
      Forall (λ v, union_free (val_map freeze v) → union_free v) vs →
      Forall union_free (val_map freeze <$> vs) → Forall union_free vs).
    { induction 1; simpl; intros; decompose_Forall; eauto. } 
    induction v using val_ind_alt; inversion_clear 1; econstructor; eauto.
  * induction 1 using @union_free_ind_alt; simpl;
      econstructor; eauto; by apply Forall_fmap.
Qed.

Lemma val_new_base (τ : base_type Ti) : val_new (base τ) = VBase (VIndet τ).
Proof. unfold val_new. by rewrite type_iter_base. Qed.
Lemma val_new_array τ n :
  val_new (τ.[n]) = VArray (replicate n (val_new τ)).
Proof. unfold val_new. by rewrite type_iter_array. Qed.
Lemma val_new_compound c s τs :
  get_env !! s = Some τs →
  val_new (compound@{c} s) =
    match c with
    | Struct => VStruct s (val_new <$> τs)
    | Union =>
       match list_singleton_dec τs with
       | inleft (τ↾_) => VUnion s 0 (val_new τ)
       | _ => VUnionNone s (val_new <$> τs)
       end
    end.
Proof.
  intros. unfold val_new.
  rapply (@type_iter_compound Ti _ (@eq (val Ti))); eauto.
  { by intros; subst. }
  clear dependent s τs. intros ?? [] ? τs ??; simpl.
  { f_equal; by apply Forall_fmap_ext. }
  destruct (list_singleton_dec _) as [[??]|?]; subst; decompose_Forall.
  * by f_equal.
  * f_equal; by apply Forall_fmap_ext.
Qed.

Lemma val_of_bits_replicate τ sz :
  type_valid get_env τ → bit_size_of τ ≤ sz →
  val_of_bits τ (replicate sz BIndet) = val_new τ.
Proof.
  intros Hτ. revert τ Hτ sz. refine (type_env_ind _ _ _ _).
  * intros. rewrite val_new_base, val_of_bits_base. f_equal.
    rewrite <-(base_val_of_bits_resize _ _ (bit_size_of τ)) by done.
    by rewrite resize_replicate, base_val_of_bits_replicate.
  * intros τ n ? IH _ sz. rewrite val_new_array, val_of_bits_array,
      bit_size_of_array. intros Hsz. f_equal.
    revert sz Hsz. induction n; simpl; intros; f_equal.
    + by rewrite IH by lia.
    + rewrite drop_replicate. auto with lia.
  * intros [] s τs Hs Hτs IH _ sz.
    { erewrite val_new_compound, val_of_bits_compound by eauto.
      erewrite bit_size_of_struct by eauto. unfold struct_of_bits.
      intros Hsz. clear Hs Hτs. f_equal. revert sz Hsz.
      induction (bit_size_of_fields τs); decompose_Forall;
        simpl; intros; rewrite ?drop_replicate; f_equal; auto with lia. }
    erewrite val_new_compound, val_of_bits_compound by eauto. intros.
    destruct (list_singleton_dec τs) as [[τ ?]|_]; subst.
    { rewrite Forall_singleton in IH. f_equal.
      apply IH. transitivity (bit_size_of (union s));
        eauto using bit_size_of_union_singleton. }
    f_equal. apply bit_size_of_union in Hs. clear Hτs.
    induction IH; decompose_Forall; simpl; f_equal; auto with lia.
Qed.

Lemma val_new_typed m τ : type_valid get_env τ → m ⊢ val_new τ : τ.
Proof.
  revert τ. refine (type_env_ind _ _ _ _).
  * intros. rewrite val_new_base. by vtyped_constructor; constructor.
  * intros τ n ?? IH. rewrite val_new_array. vtyped_constructor.
    + by rewrite replicate_length.
    + elim n; simpl; constructor; auto.
    + done.
  * intros [|] s τs Hs Hτs IH _.
    { erewrite val_new_compound by eauto. vtyped_constructor; [by eauto|].
      clear Hs Hτs. induction IH; constructor; auto. }
    erewrite val_new_compound by eauto.
    destruct (list_singleton_dec τs) as [[τ ?]|Hlen]; subst.
    { decompose_Forall. by vtyped_constructor; eauto. }
    apply VUnionNone_typed with
      τs (replicate (bit_size_of (union s)) BIndet); auto.
    + clear IH Hlen. symmetry. apply bit_size_of_union in Hs.
      induction Hs; decompose_Forall; simpl; f_equal;
        auto using val_of_bits_replicate.
    + auto using Forall_replicate, BIndet_valid.
    + by rewrite replicate_length.
Qed.

Lemma val_of_bits_union_free τ bs :
  type_valid get_env τ → union_free (val_of_bits τ bs).
Proof.
  intros Hτ. revert τ Hτ bs. refine (type_env_ind _ _ _ _).
  * intros. rewrite val_of_bits_base. by constructor.
  * intros τ n Hτ IH _ bs. rewrite val_of_bits_array. constructor.
    revert bs. induction n; simpl; auto using Forall_drop.
  * intros [] s τs Hs Hτs IH _ bs.
    { erewrite !val_of_bits_compound by eauto. constructor.
      unfold struct_of_bits. revert bs. clear Hs Hτs.
      induction (bit_size_of_fields τs);
        intros; decompose_Forall; simpl; auto using Forall_drop. }
    erewrite !val_of_bits_compound by eauto.
    destruct (list_singleton_dec _) as [[τ ?]|?]; subst.
    + decompose_Forall. econstructor; eauto.
    + econstructor; eauto. apply Forall_fmap.
      unfold compose. elim IH; simpl; auto.
Qed.

Lemma mval_to_val_typed m w τ : m ⊢ w : τ → m ⊢ mval_to_val w : τ.
Proof.
  induction 1 using @mtyped_ind; simpl.
  * vtyped_constructor. eauto using base_val_of_bits_typed.
  * vtyped_constructor; trivial. by rewrite fmap_length. by apply Forall_fmap.
  * vtyped_constructor; eauto. by apply Forall2_fmap_l.
  * vtyped_constructor; eauto.
  * eapply val_of_bits_typed; eauto. constructor; eauto.
Qed.
Lemma mval_to_val_frozen m w τ : m ⊢ w : τ → val_forall frozen (mval_to_val w).
Proof.
  induction 1 using @mtyped_ind; simpl.
  * constructor. eauto using base_val_of_bits_frozen.
  * constructor. by apply Forall_fmap.
  * constructor. eapply Forall_fmap, Forall2_Forall_l; eauto.
    eapply Forall_true; eauto.
  * by constructor.
  * eauto using val_of_bits_frozen, TCompound_valid.
Qed.

Lemma mval_to_val_union_free_1 w : union_free (mval_to_val w) → munion_free w.
Proof.
  assert (∀ ws,
    Forall (λ w, union_free (mval_to_val w) → munion_free w) ws →
    Forall union_free (mval_to_val <$> ws) → Forall munion_free ws).
  { induction 1; simpl; intros; decompose_Forall; auto. }
  induction w using @mval_ind_alt; simpl.
  * constructor.
  * inversion_clear 1. constructor; auto.
  * inversion_clear 1. constructor; auto.
  * inversion_clear 1. econstructor; eauto.
  * constructor.
Qed.
Lemma mval_to_val_union_free_2 m w τ :
  m ⊢ w : τ → munion_free w → union_free (mval_to_val w).
Proof.
  assert (∀ ws,
    Forall (λ w, munion_free w → union_free (mval_to_val w)) ws →
    Forall munion_free ws → Forall union_free (mval_to_val <$> ws)).
  { induction 1; simpl; intros; decompose_Forall; auto. }
  assert (∀ ws τs,
    Forall2 (λ w _, munion_free w → union_free (mval_to_val w)) ws τs →
    Forall munion_free ws → Forall union_free (mval_to_val <$> ws)).
  { induction 1; simpl; intros; decompose_Forall; auto. }
  induction 1 using @mtyped_ind; simpl.
  * constructor.
  * inversion_clear 1. constructor; auto.
  * inversion_clear 1. econstructor; eauto.
  * inversion_clear 1. econstructor; eauto.
  * intros. apply val_of_bits_union_free. constructor; eauto.
Qed.
Lemma mval_to_val_union_free m w τ :
  m ⊢ w : τ → union_free (mval_to_val w) ↔ munion_free w.
Proof.
  split; eauto using mval_to_val_union_free_2, mval_to_val_union_free_1.
Qed.

Lemma mval_of_bits_to_val τ bs :
  type_valid get_env τ → mval_to_val (mval_of_bits τ bs) = val_of_bits τ bs.
Proof.
  intros Hτ. revert τ Hτ bs. refine (type_env_ind _ _ _ _).
  * intros τ ? bs. rewrite mval_of_bits_base, val_of_bits_base; simpl.
    by rewrite base_val_of_bits_resize by done.
  * intros. rewrite mval_of_bits_array, val_of_bits_array.
    simpl. erewrite array_of_bits_fmap; eauto.
  * intros [] s τs Hs Hτs IH _ bs.
    { erewrite mval_of_bits_compound, val_of_bits_compound by eauto.
      simpl. erewrite struct_of_bits_fmap; eauto. }
    erewrite mval_of_bits_compound, val_of_bits_compound by eauto.
    destruct (list_singleton_dec _) as [[??]|Hτ]; subst; simpl.
    { f_equal. by decompose_Forall. }
    erewrite val_of_bits_compound by eauto.
    destruct (list_singleton_dec _) as [[??]|_]; subst; [done|].
    pose proof (bit_size_of_union s τs Hs).
    pose proof (env_valid_lookup s τs Hs). f_equal. clear Hs Hs Hτs Hτ.
    induction IH as [|?? Hτ]; decompose_Forall; simpl; f_equal; auto.
    by rewrite <-Hτ, mval_of_bits_resize.
Qed.

Lemma val_of_bits_take τ bs sz :
  type_valid get_env τ → bit_size_of τ ≤ sz →
  val_of_bits τ (take sz bs) = val_of_bits τ bs.
Proof. intros. by rewrite <-!mval_of_bits_to_val, mval_of_bits_take. Qed.
Lemma val_of_bits_app τ bs1 bs2 :
  type_valid get_env τ → length bs1 = bit_size_of τ →
  val_of_bits τ (bs1 ++ bs2) = val_of_bits τ bs1.
Proof. intros. by rewrite <-!mval_of_bits_to_val, mval_of_bits_app. Qed.

Lemma mval_to_val_le m w1 w2 τ :
  m ⊢ w1 : τ → w1 ⊑@{m} w2 → mval_to_val w1 ⊑@{m} mval_to_val w2.
Proof.
  intros Hw1τ. revert w1 τ Hw1τ w2. assert (∀ ws1 ws2,
    Forall (λ w1, ∀ w2,
      w1 ⊑@{m} w2 → mval_to_val w1 ⊑@{m} mval_to_val w2) ws1 →
    ws1 ⊑@{m}* ws2 →
    Forall2 (λ w1 w2, mval_to_val w1 ⊑@{m} mval_to_val w2) ws1 ws2).
  { induction 2; decompose_Forall; auto. }
  assert (∀ ws1 ws2 τs,
    Forall2 (λ w1 _, ∀ w2,
      w1 ⊑@{m} w2 → mval_to_val w1 ⊑@{m} mval_to_val w2) ws1 τs →
    ws1 ⊑@{m}* ws2 →
    Forall2 (λ w1 w2, mval_to_val w1 ⊑@{m} mval_to_val w2) ws1 ws2).
  { intros ws1 ws2 τs Hws1. revert ws2.
    induction Hws1; intros; decompose_Forall; auto. }
  induction 1 using @mtyped_ind;
    intros w2 Hw1w2; pattern w2; apply (mval_le_inv_l _ _ _ _ Hw1w2);
    intros; simplify_option_equality.
  * val_le_constructor. eauto using base_val_of_bits_le.
  * val_le_constructor. auto using Forall2_fmap_2.
  * val_le_constructor. eauto using Forall2_fmap_2.
  * val_le_constructor. auto.
  * erewrite val_of_bits_compound by eauto.
    destruct (list_singleton_dec _) as [[??]|_]; subst; [done|].
    val_le_constructor; rewrite ?list_lookup_fmap;
      eauto with simplify_option_equality.
    rewrite <-mval_of_bits_to_val; eauto using env_valid_lookup_lookup.
  * eauto using val_of_bits_le, TCompound_valid.
Qed.

Lemma union_of_val_length f sz vs bs :
  union_of_val f sz vs = Some bs → length bs = sz.
Proof.
  revert bs. induction vs; intros; simplify_option_equality.
  * by rewrite replicate_length.
  * erewrite bits_join_length_r by eauto; eauto.
Qed.
Lemma union_of_val_valid f m sz vs τs bs :
  Forall2 (λ v τ, m ⊢ f v : τ) vs τs →
  union_of_val f sz vs = Some bs → m ⊢* valid bs.
Proof.
  intros Hvs. revert bs. induction Hvs; intros bs Hbs; simplify_equality'.
  { eauto using Forall_replicate, BIndet_valid. }
  destruct (union_of_val f sz l) as [bs'|] eqn:Hbs'; simplify_equality'.
  eapply bits_join_Some_r in Hbs; eauto using bits_valid_ge,
    Forall_resize, BIndet_valid, mval_to_bits_valid.
Qed.

Lemma mval_of_val_typed m v τ : m ⊢ v : τ → m ⊢ mval_of_val v : τ.
Proof.
  intros Hvτ. revert v τ Hvτ. refine (vtyped_ind _ _ _ _ _ _ _); simpl.
  * intros. erewrite type_of_correct by eauto.
    mtyped_constructor; eauto using base_typed_type_valid,
      base_val_to_bits_valid, base_val_to_bits_length.
  * intros. mtyped_constructor.
    + by rewrite fmap_length.
    + by apply Forall_fmap.
    + done.
  * intros. mtyped_constructor; eauto. by apply Forall2_fmap_l.
  * intros. mtyped_constructor; eauto.
  * intros s vs τs bs Hs Hτs Hvsτs IH ? Hbs Hlen; subst.
    destruct (union_of_val _ _ _) as [bs'|] eqn:Hbs'.
    + mtyped_constructor;
        eauto using union_of_val_length, union_of_val_valid.
    + mtyped_constructor; eauto using
        Forall_replicate, BIndet_valid, replicate_length.
Qed.

Lemma union_of_val_Some_inv_aux m τs sz bs bs' :
  let vs := flip val_of_bits bs <$> τs in
  Forall (type_valid get_env) τs →
  Forall (λ τ, bit_size_of τ ≤ sz) τs →
  m ⊢* valid bs →
  Forall (λ τ, ∀ bs', m ⊢* valid bs' →
    val_to_bits (val_of_bits τ bs') ⊑@{m}*
      resize (bit_size_of τ) BIndet bs') τs →
  union_of_val mval_of_val sz vs = Some bs' →
  bs' ⊑@{m}* resize sz BIndet bs.
Proof.
  intros vs Hτs Hszτs Hbs IH. unfold vs; clear vs.
  revert bs'. induction IH; intros bs' Hbs';
    decompose_Forall_hyps; simplify_option_equality.
  { eapply Forall2_replicate_l; eauto using
     resize_length, Forall_resize, Forall_BIndet_le. }
  eapply bits_join_min; eauto using Forall2_resize_ge_r,
    Forall2_resize_ge_r, Forall_BIndet_le.
Qed.
Lemma mval_to_bits_of_val_of_bits_le m τ bs :
  type_valid get_env τ → m ⊢* valid bs →
  val_to_bits (val_of_bits τ bs) ⊑@{m}* resize (bit_size_of τ) BIndet bs.
Proof.
  intros Hvτ. revert τ Hvτ bs. refine (type_env_ind _ _ _ _).
  * intros τ ? bs Hbs. rewrite val_of_bits_base; simpl.
    rewrite <-(base_val_of_bits_resize τ bs (bit_size_of τ)) by done.
    apply base_val_to_of_bits_le; auto using Forall_resize, BIndet_valid.
    by rewrite resize_length.
  * intros τ n Hτ IH _ bs Hbs. rewrite val_of_bits_array; simpl.
    rewrite bit_size_of_array.
    revert bs Hbs. induction n as [|n IHn]; intros bs Hbs; simpl.
    { by rewrite resize_0. }
    rewrite resize_plus; apply Forall2_app; auto using Forall_drop.
  * intros [] s τs Hs Hτs IH _ bs Hbs.
    { erewrite val_of_bits_compound by eauto; simpl.
      erewrite bit_size_of_struct, Hs by eauto; simpl.
      clear Hs Hτs. revert bs Hbs.
      unfold struct_of_bits. induction (bit_size_of_fields τs)
        as [|τ sz τs szs]; decompose_Forall_hyps; simpl; intros bs Hbs.
      { by rewrite resize_0. }
      rewrite resize_plus. apply Forall2_app; eauto using Forall_drop,
        Forall2_resize_ge_r, Forall_BIndet_le. }
    erewrite val_of_bits_compound by eauto; simpl.
    destruct (list_singleton_dec _) as [[??]|_]; subst; simpl.
    { rewrite Forall_singleton in IH.
      eauto using Forall2_resize_ge_r, Forall_BIndet_le,
         bit_size_of_union_singleton. }
    destruct (union_of_val _ _ _) as [bs'|] eqn:Hbs'; simpl.
    + apply bit_size_of_union in Hs. revert bs' Hbs'.
      induction IH; intros bs' Hbs';
        decompose_Forall_hyps; simplify_option_equality.
      { eapply Forall2_replicate_l; eauto using
          resize_length, Forall_resize, Forall_BIndet_le. }
      eapply bits_join_min; eauto using Forall2_resize_ge_r,
        Forall2_resize_ge_r, Forall_BIndet_le.
    + eapply Forall2_replicate_l; eauto using
        resize_length, Forall_resize, Forall_BIndet_le.
Qed.

Lemma union_of_val_Some_aux m τs sz bs :
  let vs := flip val_of_bits bs <$> τs in
  Forall (type_valid get_env) τs →
  Forall (λ τ, bit_size_of τ ≤ sz) τs →
  m ⊢* valid bs → length bs = sz →
  Forall (λ v, mval_to_val (mval_of_val v) = val_map freeze v) vs →
  ∃ bs',
    union_of_val mval_of_val sz vs = Some bs' ∧
    bs' ⊑@{m}* bs ∧
    vs = flip val_of_bits bs' <$> τs.
Proof.
  intros vs Hτs Hsz Hbs Hlen IH; unfold vs in *; clear vs.
  rewrite Forall_fmap in IH; unfold compose in IH.
  induction IH as [|τ τs IHτ _ IHτs]; simpl.
  { eexists (replicate sz BIndet). split_ands; auto.
    eapply Forall2_replicate_l; eauto using
      resize_length, Forall_resize, Forall_BIndet_le. }
  rewrite Forall_cons in Hτs; destruct Hτs as [Hτ Hτs]; simpl in *.
  rewrite Forall_cons in Hsz; destruct Hsz as [Hsz Hsz'].
  destruct IHτs as (bs2&Hbs2&?&?); auto. rewrite Hbs2; simpl.
  set (bs3:=resize sz BIndet (val_to_bits (val_of_bits τ bs))).
  assert (bs3 ⊑@{m}* bs).
  { rewrite <-(resize_all_alt bs sz BIndet) by done.
    eapply Forall2_resize_ge_r; eauto using Forall_BIndet_le,
      mval_to_bits_of_val_of_bits_le. } 
  destruct (bits_join_exists m bs3 bs2 bs) as (bs4&Hbs4&?); eauto.
  exists bs4. split_ands; auto. f_equal.
  * symmetry. apply (val_of_bits_trans m τ bs3 bs4 bs); eauto
      using bits_join_Some_l, bits_valid_le.
    rewrite val_frozen_freeze in IHτ by eauto using val_of_bits_frozen.
    unfold bs3. rewrite val_of_bits_resize by done.
    rewrite <-(mval_of_bits_to_val _ (mval_to_bits _)) by done.
    assert (munion_free (mval_of_val (val_of_bits τ bs))).
    { rewrite <-(mval_to_val_union_free m), IHτ by
        eauto using mval_of_val_typed, val_of_bits_typed.
      by apply val_of_bits_union_free. }
    by rewrite (mval_of_to_bits_union_free m) by
      eauto using mval_of_val_typed, val_of_bits_typed.
  * apply (bits_join_Some_r m) in Hbs4; eauto using bits_valid_le.
    clear dependent bs3; clear dependent τ; clear Hbs2.
    induction Hτs as [|τ τs]; simpl in *;
      decompose_Forall; simplify_list_equality; f_equal; auto.
    symmetry. apply (val_of_bits_trans m τ bs2 bs4 bs); eauto
      using bits_join_Some_l, bits_valid_le.
Qed.
Lemma mval_to_of_val m v τ :
  m ⊢ v : τ → mval_to_val (mval_of_val v) = val_map freeze v.
Proof.
  intros Hvτ. revert v τ Hvτ. refine (vtyped_ind _ _ _ _ _ _ _); simpl.
  * intros. erewrite type_of_correct by eauto.
    f_equal. eauto using base_val_of_to_bits.
  * intros vs τ Hvs IH _. f_equal.
    induction IH; simpl; decompose_Forall; f_equal; auto.
  * intros s vs τs _ _ IH. f_equal.
    induction IH; simpl; intros; decompose_Forall; f_equal; auto.
  * intros. f_equal. auto.
  * intros s vs τs bs Hs Hτs Hvs IH ? Hbs Hlen; subst.
    destruct (union_of_val_Some_aux m τs (bit_size_of (union s)) bs)
      as (bs'&Hbs'&?&Hbsbs'); eauto using bit_size_of_union, env_valid_lookup.
    { clear Hs Hτs Hvs. induction IH; constructor; auto. }
    rewrite Hbs'; simpl. erewrite val_of_bits_compound by eauto.
    destruct (list_singleton_dec _) as [[??]|_]; subst; [done|].
    by rewrite vals_frozen_freeze, Hbsbs' by
      eauto using vals_of_bits_frozen, env_valid_lookup.
Qed.
Lemma union_of_val_Some m τs sz bs :
  let vs := flip val_of_bits bs <$> τs in
  Forall (type_valid get_env) τs →
  Forall (λ τ, bit_size_of τ ≤ sz) τs →
  m ⊢* valid bs → length bs = sz →
  ∃ bs',
    union_of_val mval_of_val sz vs = Some bs' ∧
    bs' ⊑@{m}* bs ∧
    vs = flip val_of_bits bs' <$> τs.
Proof.
  intros vs Hτs Hsz Hbs ?. apply union_of_val_Some_aux; auto.
  apply Forall_fmap. clear vs Hsz. induction Hτs; constructor; simpl;
    eauto using mval_to_of_val, val_of_bits_typed.
Qed.

Lemma mval_of_val_union_free m v τ :
  m ⊢ v : τ → munion_free (mval_of_val v) ↔ union_free v.
Proof.
  intros. rewrite <-mval_to_val_union_free by eauto using mval_of_val_typed.
  by erewrite mval_to_of_val, union_free_freeze by eauto. 
Qed.
Lemma mval_of_val_union_free_2 m v τ :
  m ⊢ v : τ → union_free v → munion_free (mval_of_val v).
Proof. intros. eapply mval_of_val_union_free; eauto. Qed.

Lemma mval_of_to_val m w τ : m ⊢ w : τ → mval_of_val (mval_to_val w) ⊑@{m} w.
Proof.
  revert w τ. refine (mtyped_ind _ _ _ _ _ _ _); simpl.
  * intros τ bs ???. rewrite base_val_of_bits_type_of by done.
    mval_le_constructor. by apply base_val_to_of_bits_le.
  * intros ws τ Hws IH _. mval_le_constructor.
    elim IH; constructor; auto.
  * intros s ws τs Hs Hτs IH. mval_le_constructor.
    elim IH; constructor; auto.
  * intros s i τs w τ Hs Hτs Hw IH. by mval_le_constructor.
  * intros s τs bs Hs Hτs Hbs Hlen.
    erewrite val_of_bits_compound by eauto.
    destruct (list_singleton_dec _) as [[??]|_]; subst; [done |]; simpl.
    destruct (union_of_val_Some m τs (bit_size_of (union s)) bs)
      as (bs'&Hbs'&?&?); eauto using bit_size_of_union, env_valid_lookup.
    rewrite Hbs'. by mval_le_constructor.
Qed.
Lemma mval_of_to_bits_to_of_val m w τ :
  m ⊢ w : τ → mval_of_val (mval_to_val w) ⊑@{m} mval_of_bits τ (mval_to_bits w).
Proof.
  intros. erewrite mval_of_to_bits by eauto.
  transitivity w; eauto using mval_of_to_val, munion_reset_above.
Qed.
Lemma mval_of_val_le m v1 v2 τ :
  m ⊢ v1 : τ → v1 ⊑@{m} v2 → mval_of_val v1 ⊑@{m} mval_of_val v2.
Proof.
  intros Hv1τ Hv1v2. revert v1 v2 Hv1v2 τ Hv1τ.
  refine (val_le_ind _ _ _ _ _ _ _ _ _).
  * intros v1 v2 Hv1v2 τ' Hτ'. apply (vtyped_inv_l _ _ _ _ Hτ').
    clear τ' Hτ'; intros τ Hv1τ; simpl.
    erewrite !type_of_correct by eauto using base_typed_ge.
    mval_le_constructor. by apply base_val_to_bits_le.
  * intros vs1 vs2 Hvs IH τ' Hτ'. apply (vtyped_inv_l _ _ _ _ Hτ').
    clear τ' Hτ'; intros τ ? _ Hvs1 _; simpl.
    mval_le_constructor.
    induction IH; decompose_Forall_hyps; constructor; eauto.
  * intros s vs1 vs2 _ IH τ' Hτ'. apply (vtyped_inv_l _ _ _ _ Hτ').
    clear τ' Hτ'; intros τs _ Hvs1; simpl.
    mval_le_constructor. revert τs Hvs1.
    induction IH; intros; decompose_Forall_hyps; constructor; eauto.
  * intros s i v1 v2 Hv1v2 IH τ' Hτ'. apply (vtyped_inv_l _ _ _ _ Hτ').
    clear τ' Hτ'; intros τs τ Hs Hi Hv1τ; simpl.
    mval_le_constructor; eauto.
  * eauto.
  * intros s vs1 vs2 τs bs1 bs2 Hs Hvs1 Hbs1 Hlen Hvs2 Hbs2 Hvs _ τ' Hτ'.
    apply (vtyped_inv_l _ _ _ _ Hτ').
    clear τ' Hτ'; intros ????????; simplify_option_equality.
    assert (m ⊢* valid bs2) by eauto using bits_valid_ge.
    assert (Forall (λ τ, bit_size_of τ ≤ length bs2) τs).
    { rewrite Hbs2. by apply bit_size_of_union. }
    destruct (union_of_val_Some m τs (bit_size_of (union s)) bs2)
      as (bs2'&Hbs2'&?&?); eauto using bit_size_of_union, env_valid_lookup.
    rewrite <-(fmap_val_of_bits_masked m τs bs1 bs2 bs2') by
      eauto using env_valid_lookup, Forall2_length, eq_sym, bits_valid_le.
    destruct (union_of_val_Some m τs
      (bit_size_of (union s)) (mask_bits bs1 bs2'))
      as (bs1'&Hbs1'&?&?); eauto using bit_size_of_union, env_valid_lookup,
      mask_bits_valid, bits_valid_le.
    { by erewrite mask_bits_length, Forall2_length by eauto. }
    simplify_option_equality. mval_le_constructor.
    transitivity (mask_bits bs1 bs2'); auto.
    apply mask_bits_le_same_length; eauto using bits_valid_le.
    erewrite (Forall2_length _ bs2' bs2) by eauto. eauto using Forall2_length. 
  * intros s i τs v1 v2 vs2 bs2 Hs Hτs Hi Hv1 IH Hvs2 Hbs2 Hlen τ' Hτ'.
    apply (vtyped_inv_l _ _ _ _ Hτ').
    clear τ' Hτ'; intros ? τ ? Hiτ Hv1τ; simplify_option_equality.
    destruct (union_of_val_Some m τs (bit_size_of (union s)) bs2)
      as (bs2'&Hbs2'&?&Hbs); eauto using bit_size_of_union, env_valid_lookup.
    rewrite Hbs, list_lookup_fmap, Hiτ in Hi; simplify_option_equality.
    mval_le_constructor; eauto using bits_valid_le.
    + transitivity (mval_of_val (val_of_bits τ bs2')); eauto.
      rewrite <-(mval_of_bits_resize _ _ (bit_size_of τ)) by
        eauto using env_valid_lookup_lookup.
      apply mval_of_to_bits_le_flip; eauto 8 using mval_of_val_typed,
        val_of_bits_typed, bits_valid_le, env_valid_lookup_lookup.
      apply mval_to_bits_of_val_of_bits_le; eauto using
        env_valid_lookup_lookup, bits_valid_le.
    + by erewrite Forall2_length by eauto.
Qed.

Lemma val_to_bits_valid m τ v : m ⊢ v : τ → m ⊢* valid val_to_bits v.
Proof. eauto using mval_of_val_typed, mval_to_bits_valid. Qed.
Lemma val_to_bits_length m τ v :
  m ⊢ v : τ → length (val_to_bits v) = bit_size_of τ.
Proof. eauto using mval_to_bits_length, mval_of_val_typed. Qed.
Lemma val_of_to_bits m τ v :
  m ⊢ v : τ → union_free v →
  val_of_bits τ (val_to_bits v) = val_map freeze v.
Proof.
  intros. erewrite <-mval_of_bits_to_val, mval_of_to_bits
    by eauto using vtyped_type_valid, mval_of_val_typed.
  by erewrite munion_free_reset, mval_to_of_val
    by eauto using mval_of_val_union_free_2.
Qed.

Lemma mval_lookup_byte_typed m w τ i v :
  m ⊢ w : τ → w !! i = Some v → m ⊢ v : uchar.
Proof.
  unfold lookup, mval_lookup_byte; intros; simplify_option_equality.
  apply val_of_bits_typed; auto using TBase_valid, TInt_valid.
  eauto using Forall_sublist_lookup, mval_to_bits_valid.
Qed.
Lemma mval_lookup_byte_length m w τ i v :
  m ⊢ w : τ → w !! i = Some v → i < size_of τ.
Proof.
  unfold lookup, mval_lookup_byte, sublist_lookup.
  intros; simplify_option_equality.
  apply (Nat.mul_lt_mono_pos_r (char_bits)); auto using char_bits_pos.
  change (size_of τ * char_bits) with (bit_size_of τ).
  rewrite <-(mval_to_bits_length m w) by done. pose proof char_bits_pos; lia.
Qed.
Lemma mval_insert_byte_typed m w τ i v :
  m ⊢ w : τ → m ⊢ v : uchar → m ⊢ <[i:=v]>w : τ.
Proof.
  unfold insert, mval_insert_byte. intros. simplify_type_equality.
  apply mval_of_bits_typed; eauto using mtyped_type_valid.
  apply Forall_sublist_insert;
    eauto using val_to_bits_valid, mval_to_bits_valid.
Qed.

Lemma mval_lookup_byte_le m w1 w2 τ i v1 :
  m ⊢ w1 : τ →
  w1 ⊑@{m} w2 → w1 !! i = Some v1 → ∃ v2, w2 !! i = Some v2 ∧ v1 ⊑@{m} v2.
Proof.
  unfold lookup, mval_lookup_byte. intros.
  destruct (sublist_lookup _ _ (mval_to_bits w1)) as [bs1|]
    eqn:Hbs1; simplify_equality'.
  destruct (Forall2_sublist_lookup_l (⊑@{m}) (mval_to_bits w1)
    (mval_to_bits w2) (i * char_bits) char_bits bs1) as (bs2&?&?);
    eauto using mval_to_bits_le.
  exists (val_of_bits uchar bs2); simplify_option_equality.
  naive_solver eauto using val_of_bits_le, val_of_bits_le,
    TBase_valid, TInt_valid, Forall_sublist_lookup, mval_to_bits_valid.
Qed.
Lemma mval_lookup_byte_ge m w1 w2 τ i v2 :
  m ⊢ w1 : τ →
  w1 ⊑@{m} w2 → w2 !! i = Some v2 → ∃ v1, w1 !! i = Some v1 ∧ v1 ⊑@{m} v2.
Proof.
  unfold lookup, mval_lookup_byte. intros.
  destruct (sublist_lookup _ _ (mval_to_bits w2)) as [bs2|]
    eqn:Hbs1; simplify_equality'.
  destruct (Forall2_sublist_lookup_r (⊑@{m}) (mval_to_bits w1)
    (mval_to_bits w2) (i * char_bits) char_bits bs2) as (bs1&?&?);
    eauto using mval_to_bits_le.
  exists (val_of_bits uchar bs1); simplify_option_equality.
  naive_solver eauto using val_of_bits_le, val_of_bits_le,
    TBase_valid, TInt_valid, Forall_sublist_lookup, mval_to_bits_valid.
Qed.

Lemma mval_insert_byte_le m w1 w2 τ i v1 v2 :
  m ⊢ w1 : τ →
  m ⊢ v1 : uchar → w1 ⊑@{m} w2 → v1 ⊑@{m} v2 → <[i:=v1]>w1 ⊑@{m} <[i:=v2]>w2.
Proof.
  unfold insert, mval_insert_byte. intros.
  rewrite <-(mval_le_type_of m w1 w2) by done. simplify_type_equality.
  apply mval_of_bits_le; eauto using mtyped_type_valid.
  apply Forall2_sublist_insert;
    eauto using mval_to_bits_le, mval_to_bits_le, mval_of_val_le.
Qed.

Lemma mval_lookup_insert_byte m w τ i j v1 v2 :
  m ⊢ w : τ → i ≠ j → m ⊢ v2 : uchar →
  w !! i = Some v1 → <[j:=v2]>w !! i = Some v1.
Proof.
  unfold lookup, mval_lookup_byte, insert, mval_insert_byte. intros.
  destruct (sublist_lookup _ _ (mval_to_bits w)) as [bs|]
    eqn:Hbs; simplify_type_equality'.
  rewrite sublist_lookup_Some in Hbs; destruct Hbs as (Hi&?&Hbs).
  erewrite mval_to_bits_length in Hi by eauto.
  erewrite mval_to_of_bits by eauto using mtyped_type_valid,
    Forall_sublist_insert, val_to_bits_valid, mval_to_bits_valid.
  apply bind_Some; exists bs; split; auto.
  rewrite sublist_lookup_Some; split_ands; auto.
  { by erewrite mask_bits_length, mval_to_bits_length
      by eauto using (mval_0_typed m), mtyped_type_valid. }
  intros j' Hj'. rewrite <-(Hbs j') by done.
  transitivity (mask_bits (mval_to_bits (mval_0 τ)) (mval_to_bits w)
    !! (i * char_bits + j')); [| by erewrite mval_to_bits_mask by eauto].
  destruct (mval_to_bits (mval_0 τ) !! (i * char_bits + j')) as [bm|] eqn:Hbmj';
    [| by rewrite !lookup_mask_bits_None ].
  destruct (decide (bm = BIndet)) as [Hbm|Hbm]; subst;
    [by rewrite !lookup_mask_bits_indet |].
  rewrite (lookup_mask_bits _ bm), lookup_sublist_insert_ne,
    (lookup_mask_bits _ bm); auto.
  * erewrite mval_to_bits_length by eauto; lia.
  * erewrite val_to_bits_length, bit_size_of_int, int_bits_char by eauto.
    destruct (decide (i < j)).
    { left. replace j with (i + (j - i)) by lia.
      rewrite Nat.mul_add_distr_r. apply Nat.add_lt_mono_l.
      apply Nat.lt_le_trans with (1 * char_bits); auto with lia.
      apply Nat.mul_le_mono_r; lia. }
    right. rewrite <-Nat.mul_succ_l.
    transitivity (i * char_bits). apply Nat.mul_le_mono_r; lia. lia.
  * erewrite sublist_insert_length, mval_to_bits_length by eauto; lia.
Qed.

Lemma mval_insert_byte_commute_aux m w τ i j v1 v2 :
  m ⊢ w : τ → i < j → m ⊢ v1 : uchar → m ⊢ v2 : uchar →
  <[i:=v1]>(<[j:=v2]>w) = <[j:=v2]>(<[i:=v1]>w).
Proof.
  intros. unfold insert, mval_insert_byte; simplify_type_equality.
  set (f := sublist_insert (i * char_bits) (val_to_bits v1)).
  set (g := sublist_insert (j * char_bits) (val_to_bits v2)).
  assert (∀ bs, m ⊢* valid bs → m ⊢* valid (f bs)).
  { eauto using Forall_sublist_insert, val_to_bits_valid. }
  assert (∀ bs, m ⊢* valid bs → m ⊢* valid (g bs)).
  { eauto using Forall_sublist_insert, val_to_bits_valid. }
  assert (length (val_to_bits v1) = char_bits) as Hv1 by (by erewrite
    val_to_bits_length, bit_size_of_int, int_bits_char by eauto).
  assert (length (val_to_bits v2) = char_bits) as Hv2 by (by erewrite
    val_to_bits_length, bit_size_of_int, int_bits_char by eauto).
  erewrite !mval_to_of_bits by
    eauto using mtyped_type_valid, mval_to_bits_valid.
  erewrite !type_of_correct by
    eauto using mval_of_bits_typed, mtyped_type_valid, mval_to_bits_valid.
  erewrite <-(mval_of_bits_mask _ _ (f _)), <-(mval_of_bits_mask _ _ (g _))
    by eauto using mtyped_type_valid, mask_bits_valid,
      mval_0_typed, mval_to_bits_valid.
  f_equal. apply list_eq. intros j'.
  destruct (mval_to_bits (mval_0 τ) !! j') as [bm|] eqn:?;
    [|by rewrite !lookup_mask_bits_None ].
  destruct (decide (bm = BIndet)); subst; [by rewrite !lookup_mask_bits_indet|].
  assert (j' < bit_size_of τ).
  { rewrite <-(mval_to_bits_length m (mval_0 τ)) by eauto using mval_0_typed,
      mtyped_type_valid. eauto using lookup_lt_Some. }
  assert (j' < length (f (mask_bits (mval_to_bits (mval_0 τ))
    (g (mval_to_bits w))))) as Hfj'.
  { unfold f. by erewrite sublist_insert_length, mask_bits_length,
      mval_to_bits_length by eauto using (mval_0_typed m), mtyped_type_valid. }
  assert (j' < length (g (mask_bits (mval_to_bits (mval_0 τ))
    (f (mval_to_bits w))))) as Hgj'.
  { unfold g. by erewrite sublist_insert_length, mask_bits_length,
      mval_to_bits_length by eauto using (mval_0_typed m), mtyped_type_valid. }
  rewrite !(lookup_mask_bits _ bm) by done; clear Hfj' Hgj'.
  destruct (decide (size_of τ ≤ j)).
  { assert (bit_size_of τ ≤ j * char_bits) by (by apply Nat.mul_le_mono_r; lia).
    unfold g. rewrite !sublist_insert_ge by
      (by erewrite ?mask_bits_length, mval_to_bits_length
         by eauto using (mval_0_typed m), mtyped_type_valid).
    destruct (decide (size_of τ ≤ i)).
    { assert (bit_size_of τ ≤ i * char_bits) by (by apply Nat.mul_le_mono_r).
      unfold f. by rewrite !sublist_insert_ge by
        (by erewrite ?mask_bits_length, mval_to_bits_length
           by eauto using (mval_0_typed m), mtyped_type_valid). }
    assert (i * char_bits + char_bits ≤ bit_size_of τ).
    { rewrite <-Nat.mul_succ_l. apply Nat.mul_le_mono_r; omega. }
    destruct (decide (i * char_bits ≤ j' < i * char_bits + char_bits)).
    { unfold f. rewrite !(lookup_mask_bits _ bm) by
       (by erewrite ?sublist_insert_length, ?mval_to_bits_length by eauto).
     by rewrite !lookup_sublist_insert by 
       (by erewrite ?mask_bits_length, ?Hv1, ?mval_to_bits_length
          by eauto using (mval_0_typed m), mtyped_type_valid). }
    unfold f. rewrite !lookup_sublist_insert_ne by omega.
    rewrite !(lookup_mask_bits _ bm) by
      (by erewrite ?sublist_insert_length, ?mval_to_bits_length by eauto).
    by rewrite !lookup_sublist_insert_ne by omega. }
  assert (i * char_bits + char_bits ≤ bit_size_of τ).
  { rewrite <-Nat.mul_succ_l. apply Nat.mul_le_mono_r; omega. }
  assert (j * char_bits + char_bits ≤ bit_size_of τ).
  { rewrite <-Nat.mul_succ_l. apply Nat.mul_le_mono_r; omega. }
  destruct (decide (i * char_bits ≤ j' < i * char_bits + char_bits)).
  { unfold f at 1. rewrite lookup_sublist_insert by 
     (by erewrite ?mask_bits_length, ?Hv1, ?mval_to_bits_length
        by eauto using (mval_0_typed m), mtyped_type_valid).
    assert (j' < j * char_bits).
    { apply Nat.lt_le_trans with (i * char_bits + char_bits); [omega|].
      rewrite <-Nat.mul_succ_l. apply Nat.mul_le_mono_r; omega. }
    unfold g at 1. rewrite lookup_sublist_insert_ne by omega.
    unfold f. rewrite !(lookup_mask_bits _ bm) by
      (by erewrite ?sublist_insert_length, ?mval_to_bits_length by eauto).
    by rewrite lookup_sublist_insert by
      (by erewrite ?Hv1, ?mval_to_bits_length by eauto). }
  unfold f at 1. rewrite lookup_sublist_insert_ne by omega.
  destruct (decide (j * char_bits ≤ j' < j * char_bits + char_bits)).
  { unfold g at 2. rewrite lookup_sublist_insert by 
     (by erewrite ?mask_bits_length, ?Hv2, ?mval_to_bits_length
        by eauto using (mval_0_typed m), mtyped_type_valid).
    assert (j' < length (g (mval_to_bits w))).
    { unfold g.
      by erewrite sublist_insert_length, mval_to_bits_length by eauto. }
    rewrite !(lookup_mask_bits _ bm) by done.
    unfold g. by rewrite lookup_sublist_insert by
      (by erewrite ?Hv2, ?mval_to_bits_length by eauto). }
  unfold g at 2. rewrite lookup_sublist_insert_ne by omega.
  unfold f, g. rewrite !(lookup_mask_bits _ bm) by
    (by erewrite ?sublist_insert_length, ?mval_to_bits_length by eauto).
  by rewrite !lookup_sublist_insert_ne by omega.
Qed.
Lemma mval_insert_byte_commute m w τ i j v1 v2 :
  m ⊢ w : τ → i ≠ j → m ⊢ v1 : uchar → m ⊢ v2 : uchar →
  <[i:=v1]>(<[j:=v2]>w) = <[j:=v2]>(<[i:=v1]>w).
Proof.
  intros. destruct (decide (i < j)).
  * eapply mval_insert_byte_commute_aux; eauto.
  * symmetry. eapply mval_insert_byte_commute_aux; eauto with lia.
Qed.

Global Instance: TypeCheckSpec M (type Ti) (val Ti).
Proof.
  intros m. assert (∀ vs τs,
    Forall (λ v, ∀ τ, vtype_check m v = Some τ → m ⊢ v : τ) vs →
    mapM (vtype_check m) vs = Some τs → m ⊢* vs :* τs).
  { intros vs τs Hvs Hτs. eapply mapM_Some_1 in Hτs.
    induction Hτs; intros; decompose_Forall; subst; eauto. }
  assert (∀ vs τ,
    m ⊢* vs : τ → Forall (λ v, vtype_check m v = Some τ) vs →
    mapM (type_check m) vs = Some (replicate (length vs) τ)).
  { intros. apply mapM_Some, Forall2_replicate_r; decompose_Forall; eauto. }
  assert (∀ sz vs τs bs,
    m ⊢* vs :* τs → union_of_val mval_of_val sz vs = Some bs → m ⊢* valid bs).
  { intros sz vs τs bs Hvs.
    eapply (union_of_val_valid mval_of_val m _ _ τs); eauto.
    induction Hvs; constructor; eauto using mval_of_val_typed. }
  intros v τ. unfold type_check. split.
  * revert τ. induction v using @val_ind_alt; intros; simplify_option_equality.
    + vtyped_constructor; eauto. by apply type_check_sound.
    + case_match; simplify_option_equality; decompose_Forall_hyps.
      vtyped_constructor; eauto. constructor; eauto.
      eapply Forall2_Forall_typed; eauto.
    + vtyped_constructor; decompose_Forall_hyps; eauto.
    + vtyped_constructor; eauto.
    + vtyped_constructor; eauto using union_of_val_length.
  * induction 1 using @vtyped_ind; simplify_option_equality.
    + by erewrite type_check_complete by eauto.
    + match goal with
      | H : length ?vs ≠ 0, H2 : Forall _ ?vs |- _ => destruct H2; [done|]
      end; decompose_Forall_hyps; simplify_option_equality;
        naive_solver eauto using Forall_replicate_eq.
    + erewrite mapM_Some_2; eauto. by simplify_option_equality.
    + done.
    + erewrite mapM_Some_2; eauto; simplify_option_equality.
      match goal with
      | _ : get_env !! ?s = Some ?τs, _ : ?m ⊢* valid ?bs |- _ =>
        edestruct (union_of_val_Some m τs
          (bit_size_of (union s)) bs) as (?&?&?&?)
      end; eauto using env_valid_lookup, bit_size_of_union.
      by simplify_option_equality.
Qed.

Lemma val_lookup_nil v : v !! [] = Some v.
Proof. done. Qed.
Lemma val_lookup_cons v rs r : v !! (rs :: r) = v !! r ≫= (!! rs).
Proof. done. Qed.
Lemma val_lookup_app v r1 r2 : v !! (r1 ++ r2) = v !! r2 ≫= (!! r1).
Proof.
  induction r1 as [|rs1 r1 IH]; simpl.
  * by destruct (v !! r2).
  * by rewrite !val_lookup_cons, IH, option_bind_assoc.
Qed.
Lemma val_lookup_snoc v r rs : v !! (r ++ [rs]) = v !! rs ≫= (!! r).
Proof. apply val_lookup_app. Qed.

Lemma val_lookup_seg_Some m v τ rs v' :
  m ⊢ v : τ → v !! rs = Some v' → ∃ σ, rs @ τ ↣ σ ∧ m ⊢ v' : σ.
Proof.
  destruct 1 as [τ v|vs τ n ?? Hvs|s vs τs ? Hvs|s j τs v τ|s vs τs bs];
    destruct rs as [i|i|i]; intros Hlookup; simplify_option_equality.
  * exists τ. split.
    + constructor; eauto using lookup_lt_Some.
    + eapply (Forall_lookup (λ v, m ⊢ v : τ)); eauto.
  * destruct (Forall2_lookup_l _ _ _ i v' Hvs) as [σ [??]]; eauto.
    exists σ. split; [|done]. econstructor; eauto.
  * exists τ. split; try econstructor; eauto.
  * edestruct @list_lookup_fmap_inv as [? [??]]; eauto.
    subst. eexists; split; try econstructor;
      eauto using val_of_bits_typed, env_valid_lookup_lookup.
Qed.
Lemma val_lookup_Some m v τ r v' :
  m ⊢ v : τ → v !! r = Some v' → ∃ σ, r @ τ ↣ σ ∧ m ⊢ v' : σ.
Proof.
  revert v τ. induction r using rev_ind; intros v τ Hvτ Hr.
  { simplify_equality. eexists; split; [econstructor |]; eauto. }
  rewrite val_lookup_snoc in Hr. simplify_option_equality.
  edestruct val_lookup_seg_Some as [? [??]]; eauto.
  edestruct IHr as [? [??]]; eauto.
  eexists; split; [eapply ref_typed_snoc |]; eauto.
Qed.
Lemma val_lookup_seg_typed m v τ rs v' σ :
  m ⊢ v : τ → v !! rs = Some v' → rs @ τ ↣ σ → m ⊢ v' : σ.
Proof.
  intros Hvτ Hv' Hrσ. by destruct (val_lookup_seg_Some _ _ _ _ _ Hvτ Hv')
    as (σ'&Hrσ'&?); simplify_type_equality.
Qed.
Lemma val_lookup_typed m v τ r v' σ :
  m ⊢ v : τ → v !! r = Some v' → r @ τ ↣ σ → m ⊢ v' : σ.
Proof.
  intros Hvτ Hv' Hrσ. by destruct (val_lookup_Some _ _ _ _ _ Hvτ Hv')
    as (σ'&Hrσ'&?); simplify_type_equality.
Qed.

Lemma mval_to_val_lookup_seg w rs w' :
  w !! rs = Some w' → frozen rs →
  mval_to_val w !! rs = Some (mval_to_val w').
Proof.
  intros Hw Hrs. destruct w, Hrs; simplify_option_equality.
  * rewrite list_lookup_fmap. by simplify_option_equality.
  * exfalso. eauto using fmap_length.
  * rewrite list_lookup_fmap. by simplify_option_equality.
  * done.
  * erewrite val_of_bits_compound by eauto.
    rewrite mval_of_bits_to_val by eauto using env_valid_lookup_lookup.
    destruct (list_singleton_dec _) as [[??]|?];
      simplify_list_equality; simplify_option_equality; [done|].
    rewrite list_lookup_fmap. by simplify_option_equality.
Qed.
Lemma mval_to_val_lookup w r w' :
  w !! r = Some w' → Forall frozen r →
  mval_to_val w !! r = Some (mval_to_val w').
Proof.
  revert w. induction r using rev_ind; intros w Hr ?.
  { by rewrite mval_lookup_nil in Hr; simplify_equality. }
  rewrite mval_lookup_snoc in Hr; simplify_option_equality.
  decompose_Forall_hyps.
  erewrite val_lookup_snoc, mval_to_val_lookup_seg by eauto; eauto.
Qed.

Lemma mval_to_val_lookup_seg_inv m w1 τ rs v1 :
  m ⊢ w1 : τ → mval_to_val w1 !! rs = Some v1 →
  ∃ w2, w1 !! rs = Some w2 ∧ mval_to_val w2 = v1.
Proof.
  destruct 1 using @mtyped_case; destruct rs; intros;
    repeat match goal with
    | _ => progress simplify_option_equality
    | H: (_ <$> _) !! _ = Some _ |- _ => rewrite list_lookup_fmap in H
    | H: length (_ <$> _) ≠ _ |- _ => rewrite fmap_length in H
    | H: val_of_bits _ _ !! _ = Some _ |- _ =>
      erewrite val_of_bits_compound in H by eauto;
      destruct (list_singleton_dec _) as [[??]|?]
    end; eauto using  mval_of_bits_to_val, env_valid_lookup_lookup.
Qed.
Lemma mval_to_val_lookup_inv m w1 τ r v1 :
  m ⊢ w1 : τ → mval_to_val w1 !! r = Some v1 →
  ∃ w2, w1 !! r = Some w2 ∧ mval_to_val w2 = v1.
Proof.
  revert w1 τ. induction r as [|rs r IH] using rev_ind; intros w1 τ Hw1τ Hr.
  { rewrite val_lookup_nil in Hr; simplify_equality. by exists w1. }
  rewrite val_lookup_snoc in Hr.
  destruct (mval_to_val w1 !! rs) as [v|] eqn:Hv; simplify_equality'.
  destruct (mval_to_val_lookup_seg_inv m w1 τ rs v) as (w2&?&?); auto; subst.
  destruct (mval_lookup_seg_Some m w1 τ rs w2) as (τ2&?&?); auto.
  destruct (IH w2 τ2) as (w3&?&?); auto. exists w3.
  rewrite mval_lookup_snoc. by simplify_option_equality.
Qed.

Lemma val_lookup_seg_le m v1 v2 rs v3 :
  v1 ⊑@{m} v2 → v1 !! rs = Some v3 → ∃ v4, v2 !! rs = Some v4 ∧ v3 ⊑@{m} v4.
Proof.
  assert (∀ s τs i v3 bs1 bs2,
    get_env !! s = Some τs →
    bs1 ⊑@{m}* bs2 → m ⊢* valid bs1 →
    (flip val_of_bits bs1 <$> τs) !! i = Some v3 →
    ∃ v4, (flip val_of_bits bs2 <$> τs) !! i = Some v4 ∧ v3 ⊑@{m} v4).
  { intros s τs i ? bs1 bs2 ????.
    edestruct @list_lookup_fmap_inv as [τ [??]]; eauto.
    exists (val_of_bits τ bs2). rewrite list_lookup_fmap.
    simplify_option_equality.
    eauto using val_of_bits_le, env_valid_lookup_lookup. }
  destruct 1; destruct rs; intros;
    repeat (case_match || simplify_option_equality);
    eauto 7 using val_of_bits_le, env_valid_lookup_lookup,
      bits_le_resize, Forall2_take, Forall2_lookup_l;
    exfalso; eauto using Forall2_length.
Qed.
Lemma val_lookup_seg_ge m v1 v2 rs v4 :
  v1 ⊑@{m} v2 → v2 !! rs = Some v4 →
  v1 !! rs = None ∨ ∃ v3, v1 !! rs = Some v3 ∧ v3 ⊑@{m} v4.
Proof.
  assert (∀ s τs i v4 bs1 bs2,
    get_env !! s = Some τs →
    bs1 ⊑@{m}* bs2 → m ⊢* valid bs1 →
    (flip val_of_bits bs2 <$> τs) !! i = Some v4 →
    ∃ v3, (flip val_of_bits bs1 <$> τs) !! i = Some v3 ∧ v3 ⊑@{m} v4).
  { intros s τs i ? bs1 bs2 ????.
    edestruct @list_lookup_fmap_inv as [τ [??]]; eauto.
    exists (val_of_bits τ bs1). rewrite list_lookup_fmap.
    simplify_option_equality.
    eauto using val_of_bits_le, env_valid_lookup_lookup. }
  destruct 1; destruct rs; intros;
    repeat (case_match || simplify_option_equality);
    eauto 7 using mval_of_bits_le, mval_to_bits_le,
     env_valid_lookup_lookup, bits_le_resize, Forall2_take, Forall2_lookup_r.
Qed.

Lemma val_lookup_le m v1 v2 r v3 :
  v1 ⊑@{m} v2 → v1 !! r = Some v3 → ∃ v4, v2 !! r = Some v4 ∧ v3 ⊑@{m} v4.
Proof.
  revert v1 v2. induction r as [|rs r IH] using rev_ind; simpl.
  { intros. rewrite val_lookup_nil. simplify_equality. eauto. }
  intros v1 v2. rewrite !val_lookup_snoc. intros. simplify_option_equality.
  edestruct (val_lookup_seg_le m v1 v2 rs) as [? [??]];
    simplify_option_equality; eauto.
Qed.
Lemma val_lookup_ge m v1 v2 r v4 :
  v1 ⊑@{m} v2 → v2 !! r = Some v4 →
  v1 !! r = None ∨ ∃ v3, v1 !! r = Some v3 ∧ v3 ⊑@{m} v4.
Proof.
  revert v1 v2. induction r as [|rs r IH] using rev_ind; simpl.
  { intros. rewrite val_lookup_nil. simplify_equality. eauto. }
  intros v1 v2. rewrite !val_lookup_snoc. intros. simplify_option_equality.
  edestruct (val_lookup_seg_ge m v1 v2 rs) as [|(?&?&?)];
    simplify_option_equality; eauto.
Qed.

Lemma val_lookup_seg_freeze rs : lookup (A:=val Ti) (freeze rs) = lookup rs.
Proof. by destruct rs. Qed.
Lemma val_lookup_freeze v r : v !! (freeze <$> r) = v !! r.
Proof.
  induction r; simpl.
  * by rewrite val_lookup_nil.
  * rewrite !val_lookup_cons, val_lookup_seg_freeze. congruence.
Qed.

Lemma vunop_ok_typed m op v τ σ :
  m ⊢ v : τ → vunop_typed op τ σ →
  vunop_ok op v → m ⊢ vunop op v : σ.
Proof.
  unfold vunop_ok, vunop. intros Hvτ Hσ Hop.
  destruct Hσ; inversion Hvτ; simpl; simplify_equality; try done.
  constructor. eauto using base_unop_ok_typed.
Qed.
Lemma vbinop_ok_typed m op v1 v2 τ1 τ2 σ :
  ⊢ valid m → m ⊢ v1 : τ1 → m ⊢ v2 : τ2 → vbinop_typed op τ1 τ2 σ →
  vbinop_ok m op v1 v2 → m ⊢ vbinop op v1 v2 : σ.
Proof.
  unfold vbinop_ok, vbinop. intros Hm Hv1τ Hv2τ Hσ Hop.
  destruct Hσ; inversion Hv1τ; inversion Hv2τ;
    simpl; simplify_equality; try done.
  constructor. eauto using base_binop_ok_typed.
Qed.
Lemma vcast_ok_typed m v τ σ :
  m ⊢ v : τ → vcast_typed τ σ → vcast_ok σ v → m ⊢ vcast σ v : σ.
Proof.
  unfold vcast_ok, vcast. intros Hvτ Hσ Hok.
  destruct Hσ; inversion Hvτ; simpl; simplify_equality; try done.
  constructor. eauto using base_cast_ok_typed.
Qed.
End val.
