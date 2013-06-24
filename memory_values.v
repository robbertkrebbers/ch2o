(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export bits.
Local Open Scope ctype_scope.

Inductive mval (Ti : Set) :=
  | MBase : base_type Ti → list (bit Ti) → mval Ti
  | MArray : list (mval Ti) → mval Ti
  | MStruct : tag → list (mval Ti) → mval Ti
  | MUnion : tag → nat → mval Ti → mval Ti
  | MUnionNone : tag → list (bit Ti) → mval Ti.
Arguments MBase {_} _ _.
Arguments MArray {_} _.
Arguments MStruct {_} _ _.
Arguments MUnion {_} _ _ _.
Arguments MUnionNone {_} _ _.

Instance mval_eq_dec {Ti : Set} `{∀ τ1 τ2 : Ti, Decision (τ1 = τ2)} :
  ∀ w1 w2 : mval Ti, Decision (w1 = w2).
Proof.
 refine (
  fix go w1 w2 : Decision (w1 = w2) :=
  match w1, w2 with
  | MBase τ1 bs1, MBase τ2 bs2 =>
     cast_if_and (decide_rel (=) τ1 τ2) (decide_rel (=) bs1 bs2)
  | MArray ws1, MArray ws2 => cast_if (decide_rel (=) ws1 ws2)
  | MStruct s1 ws1, MStruct s2 ws2 =>
     cast_if_and (decide_rel (=) s1 s2) (decide_rel (=) ws1 ws2)
  | MUnion s1 i1 w1, MUnion s2 i2 w2 =>
     cast_if_and3 (decide_rel (=) s1 s2)
       (decide_rel (=) i1 i2) (decide_rel (=) w1 w2)
  | MUnionNone s1 bs1, MUnionNone s2 bs2 =>
     cast_if_and (decide_rel (=) s1 s2) (decide_rel (=) bs1 bs2)
  | _, _ => right _
  end); clear go; abstract congruence.
Defined.

Section mval_ind.
  Context {Ti} (P : mval Ti → Prop).
  Context (Pbase : ∀ τ bs, P (MBase τ bs)).
  Context (Parray : ∀ ws, Forall P ws → P (MArray ws)).
  Context (Pstruct : ∀ s ws, Forall P ws → P (MStruct s ws)).
  Context (Punion : ∀ s i w, P w → P (MUnion s i w)).
  Context (Punion_none : ∀ s bs, P (MUnionNone s bs)).

  Definition mval_ind_alt: ∀ w, P w.
  Proof.
   exact (
    fix go w :=
    match w return P w with
    | MBase τ bs => Pbase τ bs
    | MArray ws => Parray _ $ list_ind (Forall P)
       (Forall_nil_2 _) (λ w _, Forall_cons_2 _ _ _ (go w)) ws
    | MStruct s ws => Pstruct _ _ $ list_ind (Forall P)
       (Forall_nil_2 _) (λ w _, Forall_cons_2 _ _ _ (go w)) ws
    | MUnion s i w => Punion s i _ (go w)
    | MUnionNone s bs => Punion_none s bs
    end).
  Qed.
End mval_ind.

Section operations.
  Context `{IntEnv Ti} `{PtrEnv Ti} `{TypeOfIndex Ti M}.

  Definition mval_map
      (f : list (bit Ti) → list (bit Ti)) : mval Ti → mval Ti :=
    fix go w :=
    match w with
    | MBase τ bs => MBase τ (f bs)
    | MArray ws => MArray (go <$> ws)
    | MStruct s ws => MStruct s (go <$> ws)
    | MUnion s i w => MUnion s i (go w)
    | MUnionNone s bs => MUnionNone s (f bs)
    end.

  Global Instance type_of_mval: TypeOf (type Ti) (mval Ti) :=
    fix go w :=
    match w with
    | MBase τ _ => base τ
    | MArray [] => TVoid
    | MArray (w :: ws) => go w.[length (w :: ws)]
    | MStruct s ws => struct s
    | MUnion s _ _ => union s
    | MUnionNone s _ => union s
    end.
  Global Instance mtype_check: TypeCheck M (type Ti) (mval Ti) := λ m,
    fix go w :=
    match w with
    | MBase τ bs =>
       guard (base_type_valid get_env τ);
       guard (m ⊢* valid bs);
       guard (length bs = bit_size_of (base τ));
       Some (base τ)
    | MArray [] => None
    | MArray (w :: ws) =>
       τ ← go w;
       τs ← mapM go ws;
       guard (Forall (= τ) τs);
       Some (τ.[length (w :: ws)])
    | MStruct s ws =>
       τs ← get_env !! s;
       τs' ← mapM go ws;
       guard (τs = τs');
       Some (struct s)
    | MUnion s i w =>
       τ ← get_env !! s ≫= (!! i);
       τ' ← go w;
       guard (τ = τ');
       Some (union s)
    | MUnionNone s bs =>
       τs ← get_env !! s;
       guard (length τs ≠ 1);
       guard (m ⊢* valid bs);
       guard (length bs = bit_size_of (union s));
       Some (union s)
    end.

  Definition mval_to_bits : mval Ti → list (bit Ti) :=
    fix go w :=
    match w with
    | MBase _ bs => bs
    | MArray ws => ws ≫= go
    | MStruct s ws =>
       default [] (get_env !! s) $ λ τs,
         let flds := field_bit_sizes τs in
         mjoin $ zip_with (λ w sz, resize sz BIndet (go w)) ws flds
    | MUnion s i w => resize (bit_size_of (union s)) BIndet (go w)
    | MUnionNone _ bs => bs
    end.
  Definition mval_of_bits: type Ti → list (bit Ti) → mval Ti :=
    type_iter
    (*i TBase =>  *) (λ τ bs, MBase τ $ resize (bit_size_of (base τ)) BIndet bs)
    (*i TVoid =>     *) (λ bs, MBase uchar [BIndet]) (* dummy *)
    (*i TArray =>    *) (λ τ n rec bs, MArray $ array_of_bits rec τ n bs)
    (*i TCompound => *) (λ c s τs rec bs,
      match c with
      | Struct => MStruct s $ struct_of_bits rec τs bs
      | Union =>
         match list_singleton_dec τs with
         | inleft (τ↾_) => MUnion s 0 $ rec τ bs
         | _ => MUnionNone s $ resize (bit_size_of (union s)) BIndet bs
         end
      end) get_env.

  Definition mval_new_ (b : bit Ti) : type Ti → mval Ti := type_iter
    (*i TBase     *) (λ τ, MBase τ (replicate (bit_size_of τ) b))
    (*i TVoid     *) (MBase uchar [BIndet]) (* dummy *)
    (*i TArray    *) (λ τ n x, MArray (replicate n x))
    (*i TCompound *) (λ c s τs rec,
      match c with
      | Struct => MStruct s (rec <$> τs)
      | Union =>
         match list_singleton_dec τs with
         | inleft (τ↾_) => MUnion s 0 (rec τ)
         | _ => MUnionNone s $ replicate (bit_size_of (union s)) b
         end
      end) get_env.
  Notation mval_new := (mval_new_ BIndet).
  Notation mval_0 := (mval_new_ (BBit false)).

  Definition munion_reset : mval Ti → mval Ti :=
    fix go w :=
    match w with
    | MBase τ bs => MBase τ bs
    | MArray ws => MArray $ go <$> ws
    | MStruct s ws => MStruct s $ go <$> ws
    | MUnion s i w =>
       default (MUnion s i w) (get_env !! s) $ λ τs,
         match list_singleton_dec τs with
         | inleft (τ↾_) => MUnion s i (go w)
         | _ => MUnionNone s $
            resize (bit_size_of (union s)) BIndet $ mval_to_bits w
         end
    | MUnionNone s bs => MUnionNone s bs
    end.

  Global Instance mval_lookup_seg:
      Lookup ref_seg (mval Ti) (mval Ti) := λ rs w,
    match rs, w with
    | RArray i n, MArray ws => guard (n = length ws); ws !! i
    | RStruct i s, MStruct s' ws => guard (s = s'); ws !! i
    | RUnion i s q, MUnion s' j w =>
       guard (s = s');
       if decide (i = j) then Some w else
       guard (q = true);
       τ ← get_env !! s ≫= (!! i);
       Some (mval_of_bits τ (mval_to_bits w))
    | RUnion i s _, MUnionNone s' bs =>
       guard (s = s'); 
       τ ← get_env !! s ≫= (!! i);
       Some (mval_of_bits τ bs)
    | _, _ => None
    end.
  Global Instance mval_lookup: Lookup ref (mval Ti) (mval Ti) :=
    fix go r w :=
    match r with [] => Some w | rs :: r => @lookup _ _ _ go r w ≫= (!! rs) end.

  Global Instance mval_alter_seg:
      Alter ref_seg (mval Ti) (mval Ti) := λ f rs w,
    match rs, w with
    | RArray i n, MArray ws => MArray (alter f i ws)
    | RStruct i s, MStruct s' ws => MStruct s (alter f i ws)
    | RUnion i s _, MUnion s' j w' =>
       if decide (i = j) then MUnion s i (f w')
       else default w (get_env !! s ≫= (!! i)) $ λ τ,
         MUnion s i (f (mval_of_bits τ (mval_to_bits w)))
    | RUnion i s _, MUnionNone s' bs =>
       default w (get_env !! s ≫= (!! i)) $ λ τ,
         MUnion s i (f (mval_of_bits τ bs))
    | _, _ => w
    end.
  Global Instance mval_alter: Alter ref (mval Ti) (mval Ti) :=
    fix go f r :=
    match r with
    | [] => f
    | rs :: r => @alter _ _ _ (alter f rs) (go (alter f rs)) r
    end.
End operations.

Notation mval_new := (mval_new_ BIndet).
Notation mval_0 := (mval_new_ (BBit false)).

Section typed.
  Context `{MemorySpec Ti M}.

  Inductive mtyped' (m : M) : mval Ti → type Ti → Prop :=
    | MBase_typed' τ bs :
       base_type_valid get_env τ →
       m ⊢* valid bs →
       length bs = bit_size_of (base τ) →
       mtyped' m (MBase τ bs) (base τ)
    | MArray_typed' ws τ :
       Forall (λ w, mtyped' m w τ) ws →
       length ws ≠ 0 →
       mtyped' m (MArray ws) (τ.[length ws])
    | MStruct_typed' s ws τs :
       get_env !! s = Some τs →
       Forall2 (mtyped' m) ws τs →
       mtyped' m (MStruct s ws) (struct s)
    | MUnion_typed' s i τs w τ :
       get_env !! s = Some τs →
       τs !! i = Some τ →
       mtyped' m w τ →
       mtyped' m (MUnion s i w) (union s)
    | MUnionNone_typed' s τs bs :
       get_env !! s = Some τs →
       length τs ≠ 1 →
       m ⊢* valid bs → length bs = bit_size_of (union s) →
       mtyped' m (MUnionNone s bs) (union s).
  Global Instance mtyped: Typed M (type Ti) (mval Ti) := mtyped'.

  Lemma MBase_typed m τ bs :
    base_type_valid get_env τ →  m ⊢* valid bs →
    length bs = bit_size_of (base τ) → m ⊢ MBase τ bs : base τ.
  Proof. by constructor. Qed.
  Lemma MArray_typed m ws n τ :
    n = length ws → m ⊢* ws : τ → n ≠ 0 → m ⊢ MArray ws : τ.[n].
  Proof. intros; subst. by constructor. Qed.
  Lemma MStruct_typed m s ws τs :
    get_env !! s = Some τs → m ⊢* ws :* τs → m ⊢ MStruct s ws : struct s.
  Proof. econstructor; eauto. Qed.
  Lemma MUnion_typed m s i τs w τ :
    get_env !! s = Some τs → τs !! i = Some τ →
    m ⊢ w : τ → m ⊢ MUnion s i w : union s.
  Proof. econstructor; eauto. Qed.
  Lemma MUnionNone_typed m s τs bs :
    get_env !! s = Some τs → length τs ≠ 1 → m ⊢* valid bs →
    length bs = bit_size_of (union s) → m ⊢ MUnionNone s bs : union s.
  Proof. econstructor; eauto. Qed.

  Lemma mtyped_inv_l m (P : type Ti → Prop) w τ :
    m ⊢ w : τ →
    match w with
    | MBase τ' bs =>
       (base_type_valid get_env τ' → length bs = bit_size_of (base τ') →
         m ⊢* valid bs → P (base τ')) → P τ
    | MArray ws =>
       (∀ τ', m ⊢* ws : τ' → length ws ≠ 0 → P (τ'.[length ws])) → P τ
    | MStruct s ws =>
       (∀ τs, get_env !! s = Some τs → m ⊢* ws :* τs → P (struct s)) → P τ
    | MUnion s i w =>
       (∀ τs τ',
         get_env !! s = Some τs → τs !! i = Some τ' →
         m ⊢ w : τ' → P (union s)) → P τ
    | MUnionNone s bs =>
       (∀ τs,
         get_env !! s = Some τs → length τs ≠ 1 → m ⊢* valid bs →
         length bs = bit_size_of (union s) → P (union s)) → P τ
    end.
  Proof. destruct 1; eauto. Qed.

  Lemma mtyped_inv_r m (P : mval Ti → Prop) w τ :
    m ⊢ w : τ →
    match τ with
    | void => P w
    | base τ' =>
       (∀ bs, base_type_valid get_env τ' → length bs = bit_size_of (base τ') →
         m ⊢* valid bs → P (MBase τ' bs)) → P w
    | τ'.[n] =>
       (∀ ws, n = length ws → m ⊢* ws : τ' → n ≠ 0 → P (MArray ws)) → P w
    | struct s =>
       (∀ ws τs, get_env !! s = Some τs → m ⊢* ws :* τs →
         P (MStruct s ws)) → P w
    | union s =>
       (∀ i τs w' τ',
         get_env !! s = Some τs → τs !! i = Some τ' →
         m ⊢ w' : τ' → P (MUnion s i w')) →
       (∀ τs bs,
         get_env !! s = Some τs → length τs ≠ 1 → m ⊢* valid bs →
         length bs = bit_size_of (union s) → P (MUnionNone s bs)) →
       P w
    end.
  Proof. destruct 1; eauto. Qed.

  Section mtyped_ind.
    Context (m : M) (P : mval Ti → type Ti → Prop).
    Context (Pbase : ∀ τ bs,
      base_type_valid get_env τ →  m ⊢* valid bs →
      length bs = bit_size_of (base τ) → P (MBase τ bs) (base τ)).
    Context (Parray : ∀ ws τ,
      m ⊢* ws : τ → Forall (λ w, P w τ) ws →
      length ws ≠ 0 → P (MArray ws) (τ.[length ws])).
    Context (Pstruct : ∀ s ws τs,
      get_env !! s = Some τs → m ⊢* ws :* τs →
      Forall2 P ws τs → P (MStruct s ws) (struct s)).
    Context (Punion : ∀ s i τs w τ,
      get_env !! s = Some τs → τs !! i = Some τ →
      m ⊢ w : τ → P w τ → P (MUnion s i w) (union s)).
    Context (Punion_none : ∀ s τs bs,
      get_env !! s = Some τs →  length τs ≠ 1 → m ⊢* valid bs →
      length bs = bit_size_of (union s) → P (MUnionNone s bs) (union s)).
    Lemma mtyped_ind : ∀ w τ, mtyped' m w τ → P w τ.
    Proof.
     exact (
      fix go w τ H :=
      match H in mtyped' _ w τ return P w τ with
      | MBase_typed' _ _ Hτ Hbs Hlen => Pbase _ _ Hτ Hbs Hlen
      | MArray_typed' _ _ Hτs Hn =>
         Parray _ _ Hτs (Forall_impl _ _ _ Hτs (λ w, go _ _)) Hn
      | MStruct_typed' s _ _ Hs H =>
         Pstruct _ _ _ Hs H (Forall2_impl _ _ _ _ H go)
      | MUnion_typed' _ _ _ _ _ Hs Hi H => Punion _ _ _ _ _ Hs Hi H (go _ _ H)
      | MUnionNone_typed' _ _ _ Hs Hτs Hbs Hlen =>
         Punion_none _ _ _ Hs Hτs Hbs Hlen
      end).
    Qed.
  End mtyped_ind.

  Section mtyped_case.
    Context (m : M) (P : mval Ti → type Ti → Prop).
    Context (Pbase : ∀ τ bs,
      base_type_valid get_env τ → m ⊢* valid bs →
      length bs = bit_size_of (base τ) → P (MBase τ bs) (base τ)).
    Context (Parray : ∀ ws τ,
      m ⊢* ws : τ → length ws ≠ 0 → P (MArray ws) (τ.[length ws])).
    Context (Pstruct : ∀ s ws τs,
      get_env !! s = Some τs → m ⊢* ws :* τs → P (MStruct s ws) (struct s)).
    Context (Punion : ∀ s i τs w τ,
      get_env !! s = Some τs → τs !! i = Some τ →
      m ⊢ w : τ → P (MUnion s i w) (union s)).
    Context (Punion_none : ∀ s τs bs,
      get_env !! s = Some τs → length τs ≠ 1 → m ⊢* valid bs →
      length bs = bit_size_of (union s) → P (MUnionNone s bs) (union s)).
    Lemma mtyped_case : ∀ w τ, mtyped' m w τ → P w τ.
    Proof. destruct 1; eauto. Qed.
  End mtyped_case.
End typed.

Ltac mtyped_constructor := first
  [ eapply MBase_typed | eapply MArray_typed | eapply MStruct_typed
  | eapply MUnion_typed | eapply MUnionNone_typed ].

Section mval_le.
  Context `{MemorySpec Ti M}.

  Inductive mval_le' (m : M) : relation (mval Ti) :=
    | MBase_le' τ bs1 bs2 :
       bs1 ⊑@{m}* bs2 → mval_le' m (MBase τ bs1) (MBase τ bs2)
    | MArray_le' ws1 ws2 :
       Forall2 (mval_le' m) ws1 ws2 → mval_le' m (MArray ws1) (MArray ws2)
    | MStruct_le' s ws1 ws2 :
       Forall2 (mval_le' m) ws1 ws2 → mval_le' m (MStruct s ws1) (MStruct s ws2)
    | MUnion_le' s i w1 w2 :
       mval_le' m w1 w2 → mval_le' m (MUnion s i w1) (MUnion s i w2)
    | MUnionNone_le' s bs1 bs2 :
       bs1 ⊑@{m}* bs2 → mval_le' m (MUnionNone s bs1) (MUnionNone s bs2)
    | MUnion_MUnionNone_le' s i τs w τ bs :
       get_env !! s = Some τs → τs !! i = Some τ → length τs ≠ 1 →
       mval_le' m w (mval_of_bits τ bs) →
       m ⊢* valid bs → length bs = bit_size_of (union s) →
       mval_le' m (MUnion s i w) (MUnionNone s bs).
  Global Instance mval_le: SubsetEqEnv M (mval Ti) := mval_le'.

  Lemma MBase_le m τ bs1 bs2 : bs1 ⊑@{m}* bs2 → MBase τ bs1 ⊑@{m} MBase τ bs2.
  Proof. by constructor. Qed.
  Lemma MArray_le m ws1 ws2 : ws1 ⊑@{m}* ws2 → MArray ws1 ⊑@{m} MArray ws2.
  Proof. by constructor. Qed.
  Lemma MStruct_le m s ws1 ws2 :
    ws1 ⊑@{m}* ws2 → MStruct s ws1 ⊑@{m} MStruct s ws2.
  Proof. by constructor. Qed.
  Lemma MUnion_le m s i w1 w2 : w1 ⊑@{m} w2 → MUnion s i w1 ⊑@{m} MUnion s i w2.
  Proof. by constructor. Qed.
  Lemma MUnionNone_le m s bs1 bs2 :
    bs1 ⊑@{m}* bs2 → MUnionNone s bs1 ⊑@{m}MUnionNone s bs2.
  Proof. by constructor. Qed.
  Lemma MUnion_MUnionNone_le m s i τs w τ bs :
    get_env !! s = Some τs → τs !! i = Some τ → length τs ≠ 1 →
    w ⊑@{m} mval_of_bits τ bs →
    m ⊢* valid bs → length bs = bit_size_of (union s) →
    MUnion s i w ⊑@{m} MUnionNone s bs.
  Proof. econstructor; eauto. Qed.

  Lemma mval_le_inv_l (m : M) (P : mval Ti → Prop) w1 w2 :
    w1 ⊑@{m} w2 →
    match w1 with
    | MBase τ bs1 => (∀ bs2, bs1 ⊑@{m}* bs2 → P (MBase τ bs2)) → P w2
    | MArray ws1 => (∀ ws2, ws1 ⊑@{m}* ws2 → P (MArray ws2)) → P w2
    | MStruct s ws1 => (∀ ws2, ws1 ⊑@{m}* ws2 → P (MStruct s ws2)) → P w2
    | MUnion s i w1 =>
       (∀ w2, w1 ⊑@{m} w2 → P (MUnion s i w2)) →
       (∀ τs τ bs,
         get_env !! s = Some τs → τs !! i = Some τ → length τs ≠ 1 →
         w1 ⊑@{m} mval_of_bits τ bs →
         m ⊢* valid bs → length bs = bit_size_of (union s) →
         P (MUnionNone s bs)) → P w2
    | MUnionNone s bs1 => (∀ bs2, bs1 ⊑@{m}* bs2 → P (MUnionNone s bs2)) → P w2
    end.
  Proof. destruct 1; eauto. Qed.

  Lemma mval_le_inv (m : M) (P : Prop) w1 w2 :
    w1 ⊑@{m} w2 →
    match w1, w2 with
    | MBase τ1 bs1, MBase τ2 bs2 => (τ1 = τ2 → bs1 ⊑@{m}* bs2 → P) → P
    | MArray ws1, MArray ws2 => (ws1 ⊑@{m}* ws2 → P) → P
    | MStruct s1 ws1, MStruct s2 ws2 => (s1 = s2 → ws1 ⊑@{m}* ws2 → P) → P
    | MUnion s1 i1 w1, MUnion s2 i2 w2 =>
       (s1 = s2 → i1 = i2 → w1 ⊑@{m} w2 → P) → P
    | MUnionNone s1 bs1, MUnionNone s2 bs2 => (s1 = s2 → bs1 ⊑@{m}* bs2 → P) → P
    | MUnion s1 i w1, MUnionNone s2 bs =>
       (∀ τs τ,
         s1 = s2 →
         get_env !! s1 = Some τs → τs !! i = Some τ → length τs ≠ 1 →
         w1 ⊑@{m} mval_of_bits τ bs →
         m ⊢* valid bs → length bs = bit_size_of (union s1) → P) → P
    | _, _ => P
    end.
  Proof. destruct 1; eauto. Qed.

  Section mval_le_ind.
    Context (m : M) (P : mval Ti → mval Ti → Prop).
    Context (Pbase : ∀ τ bs1 bs2,
      bs1 ⊑@{m}* bs2 → P (MBase τ bs1) (MBase τ bs2)).
    Context (Parray : ∀ ws1 ws2,
      ws1 ⊑@{m}* ws2 → Forall2 P ws1 ws2 → P (MArray ws1) (MArray ws2)).
    Context (Pstruct : ∀ s ws1 ws2,
      ws1 ⊑@{m}* ws2 → Forall2 P ws1 ws2 → P (MStruct s ws1) (MStruct s ws2)).
    Context (Punion : ∀ s i w1 w2,
      w1 ⊑@{m} w2 → P w1 w2 → P (MUnion s i w1) (MUnion s i w2)).
    Context (Punion_none : ∀ s bs1 bs2,
      bs1 ⊑@{m}* bs2 → P (MUnionNone s bs1) (MUnionNone s bs2)).
    Context (Punion_union_none : ∀ s i τs w τ bs,
      get_env !! s = Some τs → τs !! i = Some τ → length τs ≠ 1 →
      w ⊑@{m} mval_of_bits τ bs → P w (mval_of_bits τ bs) →
      m ⊢* valid bs → length bs = bit_size_of (union s) →
      P (MUnion s i w) (MUnionNone s bs)).
    Lemma mval_le_ind: ∀ w1 w2, mval_le' m w1 w2 → P w1 w2.
     exact (
      fix go w1 w2 H :=
      match H in mval_le' _ w1 w2 return P w1 w2 with
      | MBase_le' _ _ _ Hbs => Pbase _ _ _ Hbs
      | MArray_le' _ _ Hvs => Parray _ _ Hvs (Forall2_impl _ _ _ _ Hvs go)
      | MStruct_le' _ _ _ Hvs => Pstruct _ _ _ Hvs (Forall2_impl _ _ _ _ Hvs go)
      | MUnion_le' _ _ _ _ Hv => Punion _ _ _ _ Hv (go _ _ Hv)
      | MUnionNone_le' _ _ _ Hbs => Punion_none _ _ _ Hbs
      | MUnion_MUnionNone_le' _ _ _ _ _ _ Hs Hi Hτs Hw Hbs Hbs' =>
         Punion_union_none _ _ _ _ _ _ Hs Hi Hτs Hw (go _ _ Hw) Hbs Hbs'
      end).
    Qed.
  End mval_le_ind.

  Section mval_le_case.
    Context (m : M) (P : mval Ti → mval Ti → Prop).
    Context (Pbase : ∀ τ bs1 bs2,
      bs1 ⊑@{m}* bs2 → P (MBase τ bs1) (MBase τ bs2)).
    Context (Parray : ∀ ws1 ws2,
      ws1 ⊑@{m}* ws2 → P (MArray ws1) (MArray ws2)).
    Context (Pstruct : ∀ s ws1 ws2,
      ws1 ⊑@{m}* ws2 → P (MStruct s ws1) (MStruct s ws2)).
    Context (Punion : ∀ s i w1 w2,
      w1 ⊑@{m} w2 → P (MUnion s i w1) (MUnion s i w2)).
    Context (Punion_none : ∀ s bs1 bs2,
      bs1 ⊑@{m}* bs2 →
      P (MUnionNone s bs1) (MUnionNone s bs2)).
    Context (Punion_union_none : ∀ s i τs w τ bs,
      get_env !! s = Some τs → τs !! i = Some τ → length τs ≠ 1 →
      w ⊑@{m} mval_of_bits τ bs →
      m ⊢* valid bs → length bs = bit_size_of (union s) →
      P (MUnion s i w) (MUnionNone s bs)).
    Definition mval_le_case: ∀ w1 w2, mval_le' m w1 w2 → P w1 w2.
    Proof. destruct 1; eauto. Qed.
  End mval_le_case.
End mval_le.

Ltac mval_le_constructor := first
  [ eapply MBase_le | eapply MArray_le | eapply MStruct_le
  | eapply MUnion_le | eapply MUnionNone_le | eapply MUnion_MUnionNone_le ].

Inductive munion_free `{IntEnv Ti} `{PtrEnv Ti} : mval Ti → Prop :=
  | MBase_union_free τ bs : munion_free (MBase τ bs)
  | MArray_union_free ws : Forall munion_free ws → munion_free (MArray ws)
  | MStruct_union_free s ws : Forall munion_free ws → munion_free (MStruct s ws)
  | MUnion_union_free s w τ :
     get_env !! s = Some [τ] → munion_free w → munion_free (MUnion s 0 w)
  | MUnionNone_union_free s bs : munion_free (MUnionNone s bs).

Section munion_free_ind.
  Context `{IntEnv Ti} `{PtrEnv Ti} (P : mval Ti → Prop).
  Context (Pbase : ∀ τ bs, P (MBase τ bs)).
  Context (Parray : ∀ ws, Forall munion_free ws → Forall P ws → P (MArray ws)).
  Context (Pstruct : ∀ s ws,
    Forall munion_free ws → Forall P ws → P (MStruct s ws)).
  Context (Punion : ∀ s w τ,
    get_env !! s = Some [τ] → munion_free w → P w → P (MUnion s 0 w)).
  Context (Punion_none : ∀ s bs, P (MUnionNone s bs)).
  Lemma munion_free_ind_alt: ∀ w, munion_free w → P w.
  Proof.
   exact (
    fix go w Hv :=
    match Hv in munion_free w return P w with
    | MBase_union_free _ _ => Pbase _ _
    | MArray_union_free _ H => Parray _ H (Forall_impl _ _ _ H go)
    | MStruct_union_free _ _ H => Pstruct _ _ H (Forall_impl _ _ _ H go)
    | MUnion_union_free _ _ _ Hs H => Punion _ _ _ Hs H (go _ H)
    | MUnionNone_union_free _ _ => Punion_none _ _
    end).
  Qed.
End munion_free_ind.

Section mval.
Context `{MemorySpec Ti M}.
Implicit Types w : mval Ti.
Implicit Types ws : list (mval Ti).
Implicit Types m : M.
Implicit Types τ : type Ti.
Implicit Types τs : list (type Ti).
Implicit Types bs : list (bit Ti).
Implicit Types r : ref.
Implicit Types rs : ref_seg.

Lemma mtyped_type_valid m w τ : m ⊢ w : τ → type_valid get_env τ.
Proof.
  induction 1 using @mtyped_ind; econstructor; decompose_Forall_hyps;
    try match goal with
    | H : length ?ws ≠ 0, H2 : Forall _ ?ws |- _ => destruct H2; [done|]
    end; eauto.
Qed.
Global Instance: TypeOfSpec M (type Ti) (mval Ti).
Proof.
  induction 1 using @mtyped_ind; decompose_Forall_hyps;
    try match goal with
    | H : length ?ws ≠ 0, H2 : Forall _ ?ws |- _ => destruct H2; [done|]
    end; simpl; eauto with f_equal.
Qed.
Global Instance: TypeCheckSpec M (type Ti) (mval Ti).
Proof.
  intros m. assert (∀ ws τs τ,
    Forall (λ w, ∀ τ, mtype_check m w = Some τ → m ⊢ w : τ) ws →
    Forall2 (λ w τ, mtype_check m w = Some τ) ws τs →
    m ⊢* ws :* τs).
  { induction 2; intros; decompose_Forall; subst; eauto. }
  assert (∀ ws τ,
    m ⊢* ws : τ → Forall (λ w, type_check m w = Some τ) ws →
    mapM (type_check m) ws = Some (replicate (length ws) τ)).
  { intros. apply mapM_Some, Forall2_replicate_r; decompose_Forall; eauto. }
  intros w τ. unfold type_check. split.
  * revert τ. induction w using @mval_ind_alt; intros;
      repeat (simplify_option_equality || case_match);
      repeat match goal with
      | H : mapM _ _ = Some _ |- _ => apply mapM_Some_1 in H
      end; mtyped_constructor; decompose_Forall; subst;
      eauto using Forall2_Forall_typed.
  * induction 1 using @mtyped_ind; simplify_option_equality; try done.
    + match goal with
      | H : length ?ws ≠ 0, H2 : Forall _ ?ws |- _ => destruct H2; [done|]
      end; decompose_Forall_hyps; simplify_option_equality;
        naive_solver eauto using Forall_replicate_eq.
    + erewrite mapM_Some_2; eauto. by simplify_option_equality.
Qed.
Lemma mtyped_weaken_mem m1 m2 w τ :
  (∀ x σ, type_of_index m1 x = Some σ → type_of_index m2 x = Some σ) →
  m1 ⊢ w : τ → m2 ⊢ w : τ.
Proof.
  intro. induction 1 using @mtyped_ind;
    econstructor; eauto using bits_valid_weaken_mem.
Qed.
Lemma mval_le_weaken_mem m1 m2 w1 w2 :
  (∀ x σ, type_of_index m1 x = Some σ → type_of_index m2 x = Some σ) →
  w1 ⊑@{m1} w2 → w1 ⊑@{m2} w2.
Proof.
  intro. induction 1 using @mval_le_ind;
    econstructor; eauto using bits_le_weaken_mem, bits_valid_weaken_mem.
Qed.

Lemma mval_of_bits_base (τ : base_type Ti) bs :
  mval_of_bits (base τ) bs = MBase τ $ resize (bit_size_of (base τ)) BIndet bs.
Proof. unfold mval_of_bits. by rewrite type_iter_base. Qed.
Lemma mval_of_bits_void bs :
  mval_of_bits void bs = MBase uchar [BIndet].
Proof. unfold mval_of_bits. by rewrite type_iter_void. Qed.
Lemma mval_of_bits_array τ n bs :
  mval_of_bits (τ.[n]) bs = MArray $ array_of_bits (mval_of_bits τ) τ n bs.
Proof. unfold mval_of_bits. by rewrite type_iter_array. Qed.
Lemma mval_of_bits_compound c s τs bs :
  get_env !! s = Some τs →
  mval_of_bits (compound@{c} s) bs =
    match c with
    | Struct => MStruct s $ struct_of_bits mval_of_bits τs bs
    | Union =>
       match list_singleton_dec τs with
       | inleft (τ↾_) => MUnion s 0 $ mval_of_bits τ bs
       | _ => MUnionNone s $ resize (bit_size_of (union s)) BIndet bs
       end
    end.
Proof.
  intros Hs. unfold mval_of_bits. erewrite (type_iter_compound
    (pointwise_relation (list (bit Ti)) (@eq (mval Ti))) _ _ _ _); eauto.
  { repeat intro. f_equal. auto using array_of_bits_ext. }
  clear s τs Hs bs. intros f g [] s τs Hs Hτs bs.
  * f_equal. auto using struct_of_bits_ext.
  * by destruct (list_singleton_dec _) as [[??]|?];
      subst; decompose_Forall; f_equal.
Qed.

Lemma mval_of_bits_typed m τ bs :
  type_valid get_env τ → m ⊢* valid bs → m ⊢ mval_of_bits τ bs : τ.
Proof.
  intros Hτ. revert τ Hτ bs. refine (type_env_ind _ _ _ _).
  * intros τ Hτ bs Hbs. rewrite mval_of_bits_base.
    mtyped_constructor; auto using Forall_resize, BIndet_valid.
    by rewrite resize_length.
  * intros τ n Hτ IH Hn bs Hbs. rewrite mval_of_bits_array.
    mtyped_constructor; eauto using array_of_bits_length.
    clear Hn. revert bs Hbs; induction n; simpl; auto using Forall_drop.
  * intros [] s τs Hs Hτs IH Hτs_len bs Hbs.
    { rewrite (mval_of_bits_compound _ _ τs) by done.
      apply MStruct_typed with τs; eauto.
      unfold struct_of_bits. clear Hs Hτs Hτs_len. revert bs Hbs.
      induction (bit_size_of_fields τs);
        intros; decompose_Forall; simpl; auto using Forall_drop. }
    rewrite (mval_of_bits_compound _ _ τs) by done.
    destruct (list_singleton_dec _) as [[τ ?]|?]; subst.
    + rewrite Forall_singleton in IH. eapply MUnion_typed, IH; eauto.
    + mtyped_constructor; eauto using Forall_resize, BIndet_valid.
      by rewrite resize_length.
Qed.
Lemma mval_of_bits_type_of m τ bs :
  type_valid get_env τ → m ⊢* valid bs → type_of (mval_of_bits τ bs) = τ.
Proof. eauto using type_of_correct, mval_of_bits_typed. Qed.
Lemma mval_of_bits_le m τ bs1 bs2 :
  type_valid get_env τ →
  bs1 ⊑@{m}* bs2 → mval_of_bits τ bs1 ⊑@{m} mval_of_bits τ bs2.
Proof.
  intros Hτ. revert τ Hτ bs1 bs2. refine (type_env_ind _ _ _ _).
  * intros τ ? bs1 bs2 Hbs. rewrite !mval_of_bits_base. mval_le_constructor.
    by apply bits_le_resize.
  * intros τ n ? IH Hn bs1 bs2 Hbs.
    rewrite !mval_of_bits_array. mval_le_constructor. revert bs1 bs2 Hbs.
    elim n; simpl; auto using Forall2_take, Forall2_drop.
  * intros [] s τs Hs Hτs IH _ bs1 bs2 Hbs.
    { erewrite !mval_of_bits_compound by eauto. mval_le_constructor.
      clear Hs Hτs. unfold struct_of_bits. revert bs1 bs2 Hbs.
      induction (field_bit_sizes_same_length τs); intros;
        decompose_Forall_hyps; simpl; auto using Forall2_take, Forall2_drop. }
    erewrite !mval_of_bits_compound by eauto.
    destruct (list_singleton_dec _) as [[??]|?]; subst.
    + decompose_Forall_hyps. mval_le_constructor. auto.
    + mval_le_constructor. by apply bits_le_resize.
Qed.
Lemma mval_of_bits_resize τ bs sz :
  type_valid get_env τ → bit_size_of τ ≤ sz →
  mval_of_bits τ (resize sz BIndet bs) = mval_of_bits τ bs.
Proof.
  intros Hτ. revert τ Hτ bs sz. refine (type_env_ind _ _ _ _).
  * intros τ Hτ bs sz ?. rewrite !mval_of_bits_base.
    f_equal. by rewrite resize_resize by lia.
  * intros τ n Hτ IH _ bs sz. rewrite !mval_of_bits_array, bit_size_of_array.
    intros. f_equal. auto using array_of_bits_resize.
  * intros [] s τs Hs Hτs IH _ bs ?.
    { erewrite !mval_of_bits_compound, bit_size_of_struct by eauto.
      intros. f_equal. auto using struct_of_bits_resize. }
    erewrite !mval_of_bits_compound by eauto.
    destruct (list_singleton_dec _) as [[τ ?]|?]; subst.
    + decompose_Forall. intros. f_equal.
      efeed pose proof bit_size_of_union_singleton; eauto with lia.
    + intros. f_equal. by rewrite resize_resize by lia.
Qed.
Lemma mval_of_bits_take τ bs sz :
  type_valid get_env τ → bit_size_of τ ≤ sz →
  mval_of_bits τ (take sz bs) = mval_of_bits τ bs.
Proof.
  destruct (le_lt_dec sz (length bs)).
  * rewrite <-(resize_le bs _ BIndet) by done. apply mval_of_bits_resize.
  * by rewrite take_ge by lia.
Qed.
Lemma mval_of_bits_app τ bs1 bs2 :
  type_valid get_env τ → length bs1 = bit_size_of τ →
  mval_of_bits τ (bs1 ++ bs2) = mval_of_bits τ bs1.
Proof.
  intros. by rewrite <-(mval_of_bits_resize _ (bs1 ++ bs2) (bit_size_of τ)),
    resize_app_le, mval_of_bits_resize by auto with lia.
Qed.
Lemma mval_of_bits_union_free τ bs : munion_free (mval_of_bits τ bs).
Proof.
  revert τ bs. refine (weak_type_env_ind _ _ _ _ _ _).
  * intros. rewrite mval_of_bits_base. by constructor.
  * intros. rewrite mval_of_bits_void. by constructor.
  * intros τ n IH bs. rewrite mval_of_bits_array. constructor.
    revert bs. elim n; simpl; constructor; auto.
  * intros [] s τs Hs IH bs.
    { erewrite !mval_of_bits_compound by eauto. constructor.
      unfold struct_of_bits. revert bs. clear Hs.
      induction (bit_size_of_fields τs);
        intros; decompose_Forall; simpl; auto using Forall_drop. }
    erewrite !mval_of_bits_compound by eauto.
    destruct (list_singleton_dec _) as [[τ ?]|?];
      subst; decompose_Forall; econstructor; eauto.
  * intros c s Hs bs. unfold mval_of_bits.
    rewrite type_iter_compound_None by done.
    destruct c; simpl; constructor.
    unfold struct_of_bits. revert bs. induction (zip _ _) as [|[??]];
      intros [|??]; simpl; repeat constructor; auto.
Qed.

Lemma mval_le_type_of m w1 w2 : w1 ⊑@{m} w2 → type_of w1 = type_of w2.
Proof.
  induction 1 using @mval_le_ind; simpl; auto.
  match goal with
  | H : Forall2 (λ w1 w2, type_of w1 = type_of w2) _ _ |- _ => destruct H
  end; simpl; auto. erewrite Forall2_length by eauto. by f_equal.
Qed.
Lemma mtyped_ge m w1 w2 τ : m ⊢ w1 : τ → w1 ⊑@{m} w2 → m ⊢ w2 : τ.
Proof.
  assert (∀ ws1 ws2 τ,
    Forall2 (λ w1 w2, ∀ τ, m ⊢ w1 : τ → m ⊢ w2 : τ) ws1 ws2 →
    m ⊢* ws1 : τ → m ⊢* ws2 : τ).
  { induction 1; intros; decompose_Forall; auto. }
  assert (∀ ws1 ws2 τs,
    Forall2 (λ w1 w2, ∀ τ, m ⊢ w1 : τ → m ⊢ w2 : τ) ws1 ws2 →
    m ⊢* ws1 :* τs → m ⊢* ws2 :* τs).
  { intros ws1 ws2 τs Hvs. revert τs.
    induction Hvs; intros; decompose_Forall_hyps; auto. }
  intros Hw1τ Hw1w2. revert τ Hw1τ. induction Hw1w2 using @mval_le_ind;
    intros ? Hw1τ; apply (mtyped_inv_l _ _ _ _ Hw1τ); intros;
    mtyped_constructor; eauto; simplify_map_equality;
    erewrite <-?Forall2_length by eassumption;
    eauto using resize_length, Forall2_length, bits_valid_ge.
Qed.
Lemma mtyped_le m w1 w2 τ : m ⊢ w1 : τ → w2 ⊑@{m} w1 → m ⊢ w2 : τ.
Proof.
  assert (∀ ws1 ws2  τ,
    Forall2 (λ w2 w1, ∀ τ, m ⊢ w1 : τ → m ⊢  w2 : τ) ws1 ws2 →
    m ⊢* ws2 : τ → m ⊢* ws1 : τ).
  { induction 1; intros; decompose_Forall; auto. }
  assert (∀ ws1 ws2 τs,
    Forall2 (λ w2 w1, ∀ τ, m ⊢ w1 : τ → m ⊢ w2 : τ) ws1 ws2 →
    m ⊢* ws2 :* τs → m ⊢* ws1 :* τs).
  { intros ws1 ws2 τs Hvs. revert τs.
    induction Hvs; intros; decompose_Forall_hyps; auto. }
  intros Hw1τ Hw1w2. revert τ Hw1τ. induction Hw1w2 using @mval_le_ind;
    intros ? Hw1τ; apply (mtyped_inv_l _ _ _ _ Hw1τ); intros;
    mtyped_constructor; eauto; simplify_map_equality;
    erewrite ?Forall2_length by eassumption;
    eauto using resize_length, Forall2_length, eq_sym,
      env_valid_lookup_lookup, mval_of_bits_typed, bits_valid_le.
Qed.

Global Instance: PartialOrder (@subseteq_env M (mval Ti) _ m).
Proof.
  intros m. repeat split.
  * assert (∀ ws, Forall (λ w, w ⊑@{m} w) ws → ws ⊑@{m}* ws).
    { induction 1; constructor; auto. }
    intros w. by induction w using mval_ind_alt; constructor; auto.
  * assert (∀ ws1 ws2 ws3,
      Forall2 (λ w1 w2, ∀ w3, w2 ⊑@{m} w3 → w1 ⊑@{m} w3) ws1 ws2 →
      ws2 ⊑@{m}* ws3 → ws1 ⊑@{m}* ws3).
    { intros ???. apply Forall2_transitive. auto. }
    intros w1 w2 w3 Hw1w2. revert w3. induction Hw1w2 using @mval_le_ind;
      intros w3 Hw2v3; apply (mval_le_inv_l _ _ _ _ Hw2v3); intros; subst;
      mval_le_constructor; eauto using bits_valid_ge, mval_of_bits_le,
        env_valid_lookup_lookup; try by (etransitivity; eauto).
    erewrite <-Forall2_length; eauto with lia.
  * assert (∀ ws1 ws2,
      Forall2 (λ w1 w2, w2 ⊑@{m} w1 → w1 = w2) ws1 ws2 →
      ws2 ⊑@{m}* ws1 → ws1 = ws2).
    { induction 1; intros; decompose_Forall; f_equal; auto. }
    induction 1 using @mval_le_ind;
      intros Hw2w1; apply (mval_le_inv _ _ _ _ Hw2w1);
      intros; subst; f_equal; auto; by apply (anti_symmetric (⊑@{m}*)).
Qed.

Lemma mval_new_base b (τ : base_type Ti) :
  mval_new_ b (base τ) = MBase τ (replicate (bit_size_of τ) b).
Proof. unfold mval_new_. by rewrite type_iter_base. Qed.
Lemma mval_new_array b τ n :
  mval_new_ b (τ.[n]) = MArray (replicate n (mval_new_ b τ)).
Proof. unfold mval_new_. by rewrite type_iter_array. Qed.
Lemma mval_new_compound b c s τs :
  get_env !! s = Some τs →
  mval_new_ b (compound@{c} s) =
    match c with
    | Struct => MStruct s (mval_new_ b <$> τs)
    | Union =>
       match list_singleton_dec τs with
       | inleft (τ↾_) => MUnion s 0 (mval_new_ b τ)
       | _ => MUnionNone s (replicate (bit_size_of (union s)) b)
       end
    end.
Proof.
  intros. unfold mval_new_.
  rapply (@type_iter_compound Ti _ (@eq (mval Ti))); eauto.
  { by intros; subst. }
  clear dependent s τs. intros ?? [] ? τs ??; simpl.
  * f_equal; by apply Forall_fmap_ext.
  * destruct (list_singleton_dec _) as [[??]|?];
      subst; decompose_Forall; by f_equal.
Qed.

Lemma mval_new_typed_ b m τ :
  m ⊢ valid b → type_valid get_env τ → m ⊢ mval_new_ b τ : τ.
Proof.
  intros Hb. revert τ. refine (type_env_ind _ _ _ _).
  * intros. rewrite mval_new_base. mtyped_constructor; auto.
    + auto using Forall_replicate.
    + by rewrite replicate_length.
  * intros τ n ?? IH. rewrite mval_new_array. mtyped_constructor.
    + by rewrite replicate_length.
    + elim n; simpl; constructor; auto.
    + done. 
  * intros [|] s τs Hs Hτs IH _.
    { erewrite mval_new_compound by eauto.
      mtyped_constructor; [by eauto|].
      clear Hs Hτs. induction IH; constructor; auto. }
    erewrite mval_new_compound by eauto.
    destruct (list_singleton_dec τs) as [[τ ?]|?]; subst.
    { decompose_Forall. by mtyped_constructor; eauto. }
    mtyped_constructor; eauto.
    + by apply Forall_replicate.
    + by rewrite replicate_length.
Qed.
Lemma mval_new_typed m τ : type_valid get_env τ → m ⊢ mval_new τ : τ.
Proof. auto using mval_new_typed_, BIndet_valid. Qed.
Lemma mval_0_typed m τ : type_valid get_env τ → m ⊢ mval_0 τ : τ.
Proof. auto using mval_new_typed_, BBit_valid. Qed.

Lemma mval_to_bits_length m w τ :
  m ⊢ w : τ → length (mval_to_bits w) = bit_size_of τ.
Proof.
  induction 1 as [|vs τ _ IH _|s ws τs Hs Hτs IH| |] using @mtyped_ind; simpl.
  * done.
  * rewrite bit_size_of_array. subst.
    induction IH; simpl; rewrite ?app_length; auto.
  * rewrite (bit_size_of_struct _ τs), Hs by done. simpl. clear Hs Hτs.
    revert ws IH. induction (bit_size_of_fields τs)
      as [|τ sz ?? Hn]; intros; simpl in *; decompose_Forall; simpl; [done |].
    rewrite app_length, resize_length; f_equal. eauto.
  * by rewrite resize_length.
  * done.
Qed.
Lemma mval_to_bits_valid m w τ : m ⊢ w : τ → m ⊢* valid (mval_to_bits w).
Proof.
  induction 1 as [|vs τ _ IH _|s ws τs Hs Hτs IH| |] using @mtyped_ind; simpl.
  * done.
  * induction IH; simpl; decompose_Forall; auto.
  * rewrite Hs; simpl; clear Hs. revert ws Hτs IH.
    induction (bit_size_of_fields τs) as [|τ sz ?? Hn];
      intros; decompose_Forall; simpl; [constructor |].
    apply Forall_app; split; auto using Forall_resize, BIndet_valid.
  * apply Forall_resize; auto. constructor.
  * done.
Qed.
Lemma mval_to_bits_union_reset w :
  mval_to_bits (munion_reset w) = mval_to_bits w.
Proof.
  induction w as [| |s ws Hws| |] using @mval_ind_alt; simpl.
  * done.
  * rewrite list_fmap_bind. by apply Forall_bind_ext.
  * destruct (get_env !! _); simpl; auto. f_equal.
    rewrite zip_with_fmap_l. apply Forall_zip_with_ext_l; auto.
    eapply Forall_impl; intuition (eauto with congruence).
  * destruct (get_env !! _); simpl; auto.
    destruct (list_singleton_dec _) as [[??]|?]; subst; simpl; congruence.
  * done.
Qed.
Lemma mval_of_to_bits_aux m w τ bs :
  m ⊢ w : τ → mval_of_bits τ (mval_to_bits w ++ bs) = munion_reset w.
Proof.
  intros Hvτ. revert bs. induction Hvτ as
    [τ bs'|vs τ Hvs IH _|s ws τs Hs Hτs IH|s j τs w τ Hs ?? IH|s τs bs' Hs]
    using @mtyped_ind; intros bs; simpl.
  * rewrite mval_of_bits_base. by rewrite resize_app_le, resize_all_alt by lia.
  * rewrite mval_of_bits_array. f_equal. subst.
    induction IH; simpl; [done |]; intros; decompose_Forall.
    rewrite <-(associative_L (++)). f_equal; auto.
    rewrite drop_app_alt by eauto using mval_to_bits_length, eq_sym. auto.
  * erewrite Hs, mval_of_bits_compound by eauto. simpl.
    f_equal. clear Hs. unfold struct_of_bits. revert ws Hτs IH.
    induction (bit_size_of_fields τs) as [|τ sz τs ??? IHflds]; intros ws;
      intros; decompose_Forall; simpl; f_equal.
    + rewrite resize_ge, <-!(associative_L (++)). auto.
      erewrite mval_to_bits_length; eauto.
    + rewrite <-(associative_L (++)), drop_app_alt; eauto using resize_length.
  * erewrite Hs, mval_of_bits_compound by eauto. simpl.
    destruct (list_singleton_dec _) as [[??]|?];
      simplify_list_equality; f_equal.
    + rewrite resize_ge, <-(associative_L (++)); auto.
      erewrite ?mval_to_bits_length by eauto;
       eauto using (bit_size_of_union_lookup _ _ 0).
    + by rewrite resize_app_le, resize_all_alt by (by rewrite ?resize_length).
  * erewrite mval_of_bits_compound by eauto.
    destruct (list_singleton_dec _) as [[??]|?]; subst; [done |].
    by rewrite resize_app_le, resize_all_alt by lia.
Qed.
Lemma mval_of_to_bits m w τ :
  m ⊢ w : τ → mval_of_bits τ (mval_to_bits w) = munion_reset w.
Proof.
  rewrite <-(right_id_L [] (++) (mval_to_bits w)). apply mval_of_to_bits_aux.
Qed.

Lemma mval_to_of_bits m τ bs :
  type_valid get_env τ → m ⊢* valid bs →
  mval_to_bits (mval_of_bits τ bs) = mask_bits (mval_to_bits (mval_0 τ)) bs.
Proof.
  intros Hτ. revert τ Hτ bs. refine (type_env_ind _ _ _ _).
  * intros τ Hτ bs Hbs. rewrite mval_new_base, mval_of_bits_base; simpl.
    by rewrite mask_bits_non_indet_mask.
  * intros τ n ? IH _ bs. rewrite mval_new_array, mval_of_bits_array; simpl.
    revert bs. induction n as [|n IHn]; simpl; intros bs ?; [done|].
    rewrite mask_bits_app; f_equal; auto. rewrite IHn by auto using Forall_drop.
    by erewrite mval_to_bits_length by eauto using (mval_0_typed m).
  * intros [] s τs Hs Hτs IH _ bs Hbs.
    { erewrite mval_new_compound, mval_of_bits_compound by eauto; simpl.
      erewrite Hs; simpl. clear Hs Hτs. revert bs Hbs. unfold struct_of_bits.
      induction (bit_size_of_fields τs) as [|τ sz τs szs ?? IH']; simpl;
        intros bs ?; decompose_Forall_hyps; [done|].
      rewrite mask_bits_app; f_equal; auto.
      + rewrite mask_bits_resize_mask; f_equal; auto.
      + by rewrite IH', resize_length by auto using Forall_drop. }
    erewrite mval_new_compound, mval_of_bits_compound by eauto; simpl.
    destruct (list_singleton_dec _) as [[??]|?]; simpl; subst.
    { decompose_Forall. rewrite mask_bits_resize_mask; f_equal; auto. }
    by rewrite mask_bits_non_indet_mask.
Qed.
Lemma mval_to_of_bits_below m τ bs :
  type_valid get_env τ → m ⊢* valid bs →
  mval_to_bits (mval_of_bits τ bs) ⊑@{m}* resize (bit_size_of τ) BIndet bs.
Proof.
  intros. erewrite mval_to_of_bits by eauto. apply mask_bits_le; auto.
  by erewrite mval_to_bits_length by eauto using (mval_0_typed m).
Qed.
Lemma mval_to_of_bits_below_drop m τ bs :
  type_valid get_env τ → m ⊢* valid bs → bit_size_of τ ≤ length bs →
  mval_to_bits (mval_of_bits τ bs) ++ drop (bit_size_of τ) bs ⊑@{m}* bs.
Proof.
  intros.
  transitivity (resize (bit_size_of τ) BIndet bs ++ drop (bit_size_of τ) bs).
  * by apply Forall2_app; auto using mval_to_of_bits_below.
  * by rewrite resize_le, take_drop.
Qed.

Lemma mval_to_of_bits_le_flip_aux m w τ sz bs :
  type_valid get_env τ → bit_size_of τ ≤ sz →
  m ⊢* valid bs → length bs = sz →
  mval_to_bits w ⊑@{m}* mval_to_bits (mval_of_bits τ bs) →
  w ⊑@{m} mval_of_bits τ bs → resize sz BIndet (mval_to_bits w) ⊑@{m}* bs.
Proof.
  intros; subst.
  assert (m ⊢ w : τ) by eauto using mtyped_le, mval_of_bits_typed.
  transitivity (mval_to_bits (mval_of_bits τ bs) ++ drop (bit_size_of τ) bs);
    auto using mval_to_of_bits_below_drop.
  rewrite resize_ge by (erewrite mval_to_bits_length; eauto).
  apply Forall2_app, Forall2_replicate_l;
    auto using Forall_drop, Forall_BIndet_le.
  erewrite drop_length, mval_to_bits_length; eauto.
Qed.
Lemma mval_to_bits_le m w1 w2 :
  w1 ⊑@{m} w2 → mval_to_bits w1 ⊑@{m}* mval_to_bits w2.
Proof.
  assert (∀ ws1 ws2 szs,
    Forall2 (λ w1 w2, mval_to_bits w1 ⊑@{m}* mval_to_bits w2) ws1 ws2 →
    mjoin (zip_with (λ w sz, resize sz BIndet (mval_to_bits w)) ws1 szs) ⊑@{m}*
    mjoin (zip_with (λ w sz, resize sz BIndet (mval_to_bits w)) ws2 szs)).
  { intros ws1 ws2 szs Hvs. revert szs. induction Hvs; intros [|??]; simpl;
      auto using Forall2_app, bits_le_resize. }
  induction 1 using @mval_le_ind; simpl; unfold default;
    repeat case_match; eauto using bits_le_resize, Forall2_bind,
    mval_to_of_bits_le_flip_aux, env_valid_lookup_lookup,
    bit_size_of_union_lookup.
Qed.
Lemma mval_to_of_bits_le_flip m w τ sz bs :
  type_valid get_env τ → bit_size_of τ ≤ sz →
  m ⊢* valid bs → length bs = sz →
  w ⊑@{m} mval_of_bits τ bs → resize sz BIndet (mval_to_bits w) ⊑@{m}* bs.
Proof. eauto using mval_to_of_bits_le_flip_aux, mval_to_bits_le. Qed.

Lemma munion_free_base m w (τ : base_type Ti) : m ⊢ w : base τ → munion_free w.
Proof. inversion 1; constructor. Qed.
Lemma munion_free_ge m w1 w2 : munion_free w1 → w1 ⊑@{m} w2 → munion_free w2.
Proof.
  assert (∀ ws1 ws2,
    Forall munion_free ws1 →
    Forall2 (λ w1 w2, munion_free w1 → munion_free w2) ws1 ws2 →
    Forall munion_free ws2).
  { induction 2; decompose_Forall; eauto. }
  intros Hw1. induction 1 using @mval_le_ind;
    inversion_clear Hw1; simplify_option_equality; econstructor; eauto.
Qed.
Lemma munion_free_reset w : munion_free w → munion_reset w = w.
Proof.
  assert (∀ ws, Forall (λ w, munion_reset w = w) ws → munion_reset <$> ws = ws).
  { induction 1; simpl; f_equal; auto. }
  induction 1 using @munion_free_ind_alt;
    simplify_option_equality; f_equal; auto.
Qed.
Lemma munion_reset_free m w τ : m ⊢ w : τ → munion_free (munion_reset w).
Proof.
  induction 1 using @mtyped_ind; simplify_option_equality.
  * constructor.
  * constructor. by apply Forall_fmap.
  * constructor. eapply Forall_fmap, Forall2_Forall_l; eauto.
    by apply Forall_true.
  * destruct (list_singleton_dec _) as [[??]|?];
      simplify_list_equality; econstructor; eauto.
  * econstructor; eauto.
Qed.
Lemma munion_reset_above m w τ : m ⊢ w : τ → w ⊑@{m} munion_reset w.
Proof.
  assert (∀ ws (τs : list (type Ti)),
    Forall2 (λ w _, w ⊑@{m} munion_reset w) ws τs →
    Forall2 (λ w1 w2, w1 ⊑@{m} munion_reset w2) ws ws).
  { induction 1; constructor; auto. }
  induction 1 using @mtyped_ind; simplify_option_equality.
  * done.
  * mval_le_constructor. by apply Forall2_fmap_r, Forall2_Forall.
  * mval_le_constructor. apply Forall2_fmap_r; eauto.
  * destruct (list_singleton_dec _) as [[??]|?]; subst;
      mval_le_constructor; eauto.
    + by erewrite mval_of_bits_resize, mval_of_to_bits
        by eauto using env_valid_lookup_lookup, bit_size_of_union_lookup.
    + eauto using Forall_resize, BIndet_valid, mval_to_bits_valid.
    + by rewrite resize_length.
  * done.
Qed.
Lemma munion_reset_least m w1 w2 :
  w1 ⊑@{m} w2 → munion_free w2 → munion_reset w1 ⊑@{m} w2.
Proof.
  assert (∀ ws1 ws2,
    Forall2 (λ w1 w2, munion_free w2 → munion_reset w1 ⊑@{m} w2) ws1 ws2 →
    Forall munion_free ws2 → munion_reset <$> ws1 ⊑@{m}* ws2).
  { induction 1; intros; decompose_Forall; simpl; auto. }
  induction 1 using @mval_le_ind; inversion_clear 1; simplify_option_equality;
    try destruct (list_singleton_dec _) as [[??]|?]; simplify_equality;
    mval_le_constructor; eauto using mval_to_of_bits_le_flip,
      env_valid_lookup_lookup, bit_size_of_union_lookup.
Qed.
Lemma munion_reset_typed m w τ : m ⊢ w : τ → m ⊢ munion_reset w : τ.
Proof. eauto using mtyped_ge, munion_reset_above. Qed.
Lemma munion_reset_le m w1 w2 :
  w1 ⊑@{m} w2 → munion_reset w1 ⊑@{m} munion_reset w2.
Proof.
  induction 1 using @mval_le_ind; simplify_option_equality; repeat case_match;
    repeat destruct (list_singleton_dec _) as [[??]|?]; simplify_equality;
    try mval_le_constructor; eauto using Forall2_fmap_2,
      bits_le_resize, mval_to_bits_le, mval_to_of_bits_le_flip,
      env_valid_lookup_lookup, bit_size_of_union_lookup.
Qed.

Lemma mval_new_union_free b τ :
  type_valid get_env τ → munion_free (mval_new_ b τ).
Proof.
  revert τ. refine (type_env_ind _ _ _ _).
  * intros τ ?. rewrite mval_new_base. constructor.
  * intros τ n ??. rewrite mval_new_array. simpl.
    constructor. by apply Forall_replicate.
  * intros [] s τs Hs Hτs IH.
    + rewrite (mval_new_compound _ _ _ τs) by done. simpl.
      constructor. elim IH; simpl; f_equal; auto.
    + rewrite (mval_new_compound _ _ _ τs) by done.
      destruct (list_singleton_dec _) as [[τ ?]|?]; subst;
        decompose_Forall; econstructor; eauto.
Qed.
Lemma mval_new_union_reset b τ :
  type_valid get_env τ → munion_reset (mval_new_ b τ) = mval_new_ b τ.
Proof. eauto using munion_free_reset, mval_new_union_free. Qed.

Lemma mval_to_bits_new τ :
  type_valid get_env τ →
  mval_to_bits (mval_new τ) = replicate (bit_size_of τ) BIndet.
Proof.
  revert τ. refine (type_env_ind _ _ _ _).
  * intros τ ?. by rewrite mval_new_base.
  * intros τ n ?? _. rewrite mval_new_array. simpl.
    rewrite bit_size_of_array. induction n as [|n IH]; simpl; [done|].
    rewrite replicate_plus. f_equal; auto.
  * intros [] s τs Hs Hτs IH _.
    + erewrite mval_new_compound by eauto. simpl.
      rewrite (bit_size_of_struct _ τs) by done.
      rewrite Hs. simpl. clear Hs. revert Hτs IH.
      induction (bit_size_of_fields τs) as [|τ sz τs ??? IHflds];
        intros; decompose_Forall; simpl in *; [done |].
      rewrite !replicate_plus. f_equal; [|by auto].
      rewrite (le_plus_minus (bit_size_of τ) sz) by done.
      rewrite replicate_plus, resize_plus_eq; [by f_equal; auto |].
      destruct (_ : Inhabited M) as [m].
      apply (mval_to_bits_length m). eauto using mval_new_typed.
    + erewrite mval_new_compound by eauto.
      destruct (list_singleton_dec _) as [[τ ?]|?]; subst; simpl; [|done].
      rewrite Forall_singleton in IH, Hτs. by rewrite IH, resize_replicate.
Qed.

Lemma mval_new_least_union_reset m w τ :
  m ⊢ w : τ → mval_new τ ⊑@{m} munion_reset w.
Proof.
  assert (∀ bs, m ⊢* valid bs → Forall (λ b, BIndet ⊑@{m} b) bs).
  { by induction 1; repeat constructor. }
  induction 1 using @mtyped_ind; simpl.
  * rewrite mval_new_base. unfold base_indet_bits.
    constructor. apply Forall2_replicate_l; auto.
  * rewrite mval_new_array. mval_le_constructor. apply Forall2_replicate_l.
    + by rewrite Forall_fmap.
    + by rewrite fmap_length.
  * rewrite (mval_new_compound _ _ _ τs) by done.
    mval_le_constructor. by rewrite Forall2_fmap, Forall2_flip.
  * simplify_option_equality.
    erewrite mval_new_compound by eauto.
    destruct (list_singleton_dec τs) as [[? Hτ]|?]; subst.
    + destruct i; simplify_map_equality. by mval_le_constructor.
    + mval_le_constructor.
      apply Forall2_replicate_l; auto using resize_length.
      apply Forall_resize; eauto using mval_to_bits_valid.
  * erewrite mval_new_compound by eauto.
    destruct (list_singleton_dec τs) as [[??]|?]; subst; [done|].
    mval_le_constructor. apply Forall2_replicate_l; auto.
Qed.
Lemma mval_new_least m w τ : m ⊢ w : τ → munion_free w → mval_new τ ⊑@{m} w.
Proof.
  intros. rewrite <-(munion_free_reset w) by done.
  auto using mval_new_least_union_reset.
Qed.

Lemma mval_of_to_bits_union_free m w τ :
  m ⊢ w : τ → munion_free w → mval_of_bits τ (mval_to_bits w) = w.
Proof. intros. erewrite mval_of_to_bits, munion_free_reset; eauto. Qed.
Lemma mval_of_to_bits_le_flip m w τ bs :
  m ⊢ w : τ → mval_to_bits w ⊑@{m}* bs → w ⊑@{m} mval_of_bits τ bs.
Proof.
  intros. transitivity (munion_reset w); eauto using munion_reset_above.
  erewrite <-mval_of_to_bits by eauto.
  eauto using mval_of_bits_le, mtyped_type_valid.
Qed.
Lemma mval_to_bits_inj m w1 w2 τ :
  m ⊢ w1 : τ → m ⊢ w2 : τ →
  mval_to_bits w1 = mval_to_bits w2 → munion_reset w1 = munion_reset w2.
Proof. intros. erewrite <-!(mval_of_to_bits) by eauto. by f_equal. Qed.
Lemma mval_to_bits_union_free_inj m w1 w2 τ :
  m ⊢ w1 : τ → m ⊢ w2 : τ → munion_free w1 → munion_free w2 →
  mval_to_bits w1 = mval_to_bits w2 → w1 = w2.
Proof.
  intros. rewrite <-(munion_free_reset w1), <-(munion_free_reset w2) by done.
  eauto using mval_to_bits_inj.
Qed.

Lemma mval_of_bits_replicate τ :
  type_valid get_env τ →
  mval_of_bits τ (replicate (bit_size_of τ) BIndet) = mval_new τ.
Proof.
  intros. rewrite <-mval_to_bits_new by done.
  destruct (_ : Inhabited M) as [m].
  rewrite (mval_of_to_bits m) by auto using mval_new_typed.
  by apply mval_new_union_reset.
Qed.

Lemma mval_to_bits_mask m w τ :
  m ⊢ w : τ →
  mask_bits (mval_to_bits (mval_0 τ)) (mval_to_bits w) = mval_to_bits w.
Proof.
  intros. erewrite <-mval_to_of_bits by
    eauto using mval_to_bits_valid, mtyped_type_valid.
  by erewrite mval_of_to_bits, mval_to_bits_union_reset by eauto.
Qed.
Lemma mval_of_bits_mask m τ bs :
  type_valid get_env τ → m ⊢* valid bs →
  mval_of_bits τ (mask_bits (mval_to_bits (mval_0 τ)) bs) = mval_of_bits τ bs.
Proof.
  intros. erewrite <-mval_to_of_bits by eauto.
  erewrite mval_of_to_bits by eauto using mval_of_bits_typed.
  by rewrite munion_free_reset by auto using mval_of_bits_union_free.
Qed.

Lemma mval_lookup_nil w : w !! [] = Some w.
Proof. done. Qed.
Lemma mval_lookup_cons w rs r : w !! (rs :: r) = w !! r ≫= (!! rs).
Proof. done. Qed.
Lemma mval_lookup_singleton rs : lookup (A:=mval Ti) [rs] = lookup rs.
Proof. done. Qed.
Lemma mval_lookup_app w r1 r2 : w !! (r1 ++ r2) = w !! r2 ≫= (!! r1).
Proof.
  induction r1 as [|rs1 r1 IH]; simpl.
  * by destruct (w !! r2).
  * by rewrite !mval_lookup_cons, IH, option_bind_assoc.
Qed.
Lemma mval_lookup_snoc w r rs : w !! (r ++ [rs]) = w !! rs ≫= (!! r).
Proof. apply mval_lookup_app. Qed.

Lemma mval_lookup_seg_freeze w rs w' :
  w !! freeze rs = Some w' → w !! rs = Some w'.
Proof.
  intros. destruct rs as [| |i s q]; auto.
  by destruct w, q; repeat (simplify_option_equality || case_decide).
Qed.
Lemma mval_lookup_freeze w r w' :
  w !! (freeze <$> r) = Some w' → w !! r = Some w'.
Proof.
  revert w'. induction r; intros w'; simpl.
  { by rewrite mval_lookup_nil. }
  rewrite !mval_lookup_cons. intros.
  simplify_option_equality; eauto using mval_lookup_seg_freeze.
Qed.
Lemma mval_lookup_seg_unfreeze w rs w' :
 w !! rs = Some w' → w !! unfreeze rs = Some w'.
Proof.
  intros. destruct rs as [| |i s q]; auto.
  by destruct w, q; repeat (simplify_option_equality || case_decide).
Qed.
Lemma mval_lookup_unfreeze w r w' :
  w !! r = Some w' → w !! (unfreeze <$> r) = Some w'.
Proof.
  revert w'. induction r; intros w'; simpl.
  { by rewrite mval_lookup_nil. }
  rewrite !mval_lookup_cons. intros.
  simplify_option_equality; eauto using mval_lookup_seg_unfreeze.
Qed.

Lemma mval_lookup_seg_freeze_proper w rs1 rs2 w1 w2 :
  w !! rs1 = Some w1 → w !! rs2 = Some w2 →
  freeze rs1 = freeze rs2 → w1 = w2.
Proof.
  intros.
  by destruct w, rs1, rs2; repeat (simplify_option_equality || case_decide).
Qed.
Lemma mval_lookup_freeze_proper w r1 r2 w1 w2 :
  w !! r1 = Some w1 → w !! r2 = Some w2 →
  freeze <$> r1 = freeze <$> r2 → w1 = w2.
Proof.
  revert r2 w1 w2.
  induction r1 as [|rs1 r1 IH]; intros [|rs2 r2] ??; try discriminate.
  { intros. by simplify_equality. }
  rewrite !mval_lookup_cons. intros. simplify_option_equality.
  efeed pose proof IH; eauto. subst.
  eauto using mval_lookup_seg_freeze_proper.
Qed.

Lemma munion_free_lookup_seg w rs w' :
  munion_free w → w !! rs = Some w' → munion_free w'.
Proof.
  destruct 1, rs; intros; repeat (case_decide || simplify_option_equality);
    decompose_Forall; eauto using mval_of_bits_union_free,
    env_valid_lookup_lookup, env_valid_lookup_singleton.
Qed.
Lemma munion_free_lookup w r w' :
  munion_free w → w !! r = Some w' → munion_free w'.
Proof.
  revert w. induction r using rev_ind; intros w Hw Hr;
    rewrite ?mval_lookup_snoc in Hr; simplify_option_equality;
    eauto using munion_free_lookup_seg.
Qed.

Lemma mval_lookup_seg_Some m w τ rs w' :
  m ⊢ w : τ → w !! rs = Some w' → ∃ σ, rs @ τ ↣ σ ∧ m ⊢ w' : σ.
Proof.
  destruct 1 as [τ bs|ws τ|s ws τs ? Hws|s j τs w τ|s τs bs]
    using @mtyped_ind; destruct rs as [i|i|i]; intros Hlookup;
    repeat (simplify_option_equality || case_decide).
  * exists τ. split.
    + constructor; eauto using lookup_lt_is_Some_1.
    + eapply (Forall_lookup (λ w, m ⊢ w : τ)); eauto.
  * destruct (Forall2_lookup_l _ _ _ i w' Hws) as [σ [??]]; eauto.
    exists σ. split; [|done]. econstructor; eauto.
  * exists τ. split; try econstructor; eauto.
  * eexists; split; [econstructor; eauto |].
    eauto using mval_of_bits_typed, mval_to_bits_valid, env_valid_lookup_lookup.
  * eexists; split; [econstructor; eauto |]; eauto.
  * eexists; split; [econstructor; eauto |].
    apply mval_of_bits_typed; eauto using env_valid_lookup_lookup, Forall_take.
Qed.
Lemma mval_lookup_Some m w τ r w' :
  m ⊢ w : τ → w !! r = Some w' → ∃ σ, r @ τ ↣ σ ∧ m ⊢ w' : σ.
Proof.
  revert w τ. induction r using rev_ind; intros w τ Hvτ Hr.
  { simpl in Hr. simplify_equality.
    eexists; split; [econstructor |]; eauto. }
  rewrite mval_lookup_snoc in Hr. simplify_option_equality.
  edestruct mval_lookup_seg_Some as [? [??]]; eauto.
  edestruct IHr as [? [??]]; eauto.
  eexists; split; [eapply ref_typed_snoc |]; eauto.
Qed.

Lemma mval_lookup_seg_typed m w τ rs w' σ :
  m ⊢ w : τ → w !! rs = Some w' → rs @ τ ↣ σ → m ⊢ w' : σ.
Proof.
  intros Hvτ Hw Hrσ. by destruct (mval_lookup_seg_Some _ _ _ _ _ Hvτ Hw)
    as (σ'&Hrσ'&?); simplify_type_equality.
Qed.
Lemma mval_lookup_typed m w τ r w' σ :
  m ⊢ w : τ → w !! r = Some w' → r @ τ ↣ σ → m ⊢ w' : σ.
Proof.
  intros Hvτ Hw' Hrσ. by destruct (mval_lookup_Some _ _ _ _ _ Hvτ Hw')
    as (σ'&Hrσ'&?); simplify_type_equality.
Qed.

Lemma mval_lookup_seg_le m w1 w2 rs w3 :
  w1 ⊑@{m} w2 → w1 !! rs = Some w3 → ∃ w4, w2 !! rs = Some w4 ∧ w3 ⊑@{m} w4.
Proof.
  assert (∀ s τs i j τi τj w bs,
    get_env !! s = Some τs → length τs ≠ 1 →
    τs !! i = Some τi → τs !! j = Some τj →
    m ⊢* valid bs → length bs = bit_size_of (union s) →
    w ⊑@{m} mval_of_bits τi bs →
    mval_of_bits τj (mval_to_bits w) ⊑@{m} mval_of_bits τj bs).
  { intros.
    rewrite <-(mval_of_bits_resize τj (mval_to_bits w) (bit_size_of (union s)))
      by eauto using env_valid_lookup_lookup, bit_size_of_union_lookup.
   eapply mval_of_bits_le; eauto using env_valid_lookup_lookup.
  eauto using mval_to_of_bits_le_flip,
    env_valid_lookup_lookup, bit_size_of_union_lookup. }
  destruct 1 using @mval_le_case; destruct rs; intros;
    repeat (case_decide || simplify_option_equality);
    eauto 7 using mval_of_bits_le, mval_to_bits_le,
      env_valid_lookup_lookup, bits_le_resize, Forall2_take, Forall2_lookup_l;
    by (exfalso; eauto using Forall2_length).
Qed.
Lemma mval_lookup_seg_ge m w1 w2 rs w4 :
  w1 ⊑@{m} w2 → w2 !! rs = Some w4 →
  w1 !! rs = None ∨ ∃ w3, w1 !! rs = Some w3 ∧ w3 ⊑@{m} w4.
Proof.
  assert (∀ s τs i j τi τj w bs,
    get_env !! s = Some τs → length τs ≠ 1 →
    τs !! i = Some τi → τs !! j = Some τj →
    m ⊢* valid bs → length bs = bit_size_of (union s) →
    w ⊑@{m} mval_of_bits τi bs →
    mval_of_bits τj (mval_to_bits w) ⊑@{m} mval_of_bits τj bs).
  { intros.
    rewrite <-(mval_of_bits_resize τj (mval_to_bits w) (bit_size_of (union s)))
      by eauto using env_valid_lookup_lookup, bit_size_of_union_lookup.
   eapply mval_of_bits_le; eauto using env_valid_lookup_lookup.
  eauto using mval_to_of_bits_le_flip,
    env_valid_lookup_lookup, bit_size_of_union_lookup. }
  destruct 1 using @mval_le_case; destruct rs; intros;
    repeat (case_match || simplify_option_equality);
    eauto 7 using mval_of_bits_le, mval_to_bits_le,
     env_valid_lookup_lookup, bits_le_resize, Forall2_take, Forall2_lookup_r.
Qed.

Lemma mval_lookup_le m w1 w2 r w3 :
  w1 ⊑@{m} w2 → w1 !! r = Some w3 → ∃ w4, w2 !! r = Some w4 ∧ w3 ⊑@{m} w4.
Proof.
  revert w1 w2. induction r as [|rs r IH] using rev_ind; simpl.
  { intros. rewrite mval_lookup_nil. simplify_equality. eauto. }
  intros w1 w2. rewrite !mval_lookup_snoc. intros. simplify_option_equality.
  edestruct (mval_lookup_seg_le m w1 w2 rs) as (?&?&?);
    simplify_option_equality; eauto.
Qed.
Lemma mval_lookup_ge m w1 w2 r w4 :
  w1 ⊑@{m} w2 → w2 !! r = Some w4 →
  w1 !! r = None ∨ ∃ w3, w1 !! r = Some w3 ∧ w3 ⊑@{m} w4.
Proof.
  revert w1 w2. induction r as [|rs r IH] using rev_ind; simpl.
  { intros. rewrite mval_lookup_nil. simplify_equality. eauto. }
  intros w1 w2. rewrite !mval_lookup_snoc. intros. simplify_option_equality.
  edestruct (mval_lookup_seg_ge m w1 w2 rs) as [?|(?&?&?)];
    simplify_option_equality; eauto.
Qed.

Lemma mval_new_lookup_seg τ rs σ :
  rs @ τ ↣ σ → mval_new τ !! rs = Some (mval_new σ).
Proof.
  destruct 1 as [τ n i|s i τs|s i q τs τ].
  * rewrite mval_new_array; simplify_option_equality.
    + by rewrite lookup_replicate.
    + exfalso; eauto using replicate_length.
  * erewrite mval_new_compound by eauto; simplify_option_equality.
    by rewrite list_lookup_fmap; simplify_option_equality.
  * erewrite mval_new_compound by eauto; simplify_option_equality.
    destruct (list_singleton_dec _) as [[??]|?];
      simplify_list_equality; simplify_option_equality; auto.
    by rewrite <-(mval_of_bits_resize _ _ (bit_size_of τ)), resize_replicate,
      mval_of_bits_replicate by eauto using env_valid_lookup_lookup.
Qed.
Lemma mval_new_lookup τ r σ : r @ τ ↣ σ → mval_new τ !! r = Some (mval_new σ).
Proof.
  induction 1 as [|r rs τ1 τ2 τ3 ?? IH]; [done|].
  rewrite mval_lookup_cons. rewrite IH; simpl. eauto using mval_new_lookup_seg.
Qed.

Lemma mval_lookup_seg_unfreeze_exists m w τ rs σ :
  m ⊢ w : τ → rs @ τ ↣ σ → ∃ w', w !! unfreeze rs = Some w' ∧ m ⊢ w' : σ.
Proof.
  destruct 1 as [τ bs|ws τ|s ws τs ? Hws|s j τs w τ|s τs bs] using @mtyped_case;
    inversion 1; repeat (simplify_option_equality || case_decide).
  * destruct (lookup_lt_is_Some_2 ws i) as (w&?); auto.
    exists w; split; auto. eapply (Forall_lookup_1 (flip (typed m) _)); eauto.
  * edestruct (Forall2_lookup_r (typed m)); eauto.
  * eauto.
  * naive_solver eauto using mval_of_bits_typed, mval_to_bits_valid,
      env_valid_lookup_lookup.
  * eauto using mval_of_bits_typed, env_valid_lookup_lookup.
Qed.
Lemma mval_lookup_unfreeze_exists m w τ r σ :
  m ⊢ w : τ → r @ τ ↣ σ → ∃ w', w !! (unfreeze <$> r) = Some w' ∧ m ⊢ w' : σ.
Proof.
  revert w τ. induction r as [|rs r IH] using rev_ind; intros w τ Hvτ Hr.
  { rewrite ref_typed_nil in Hr; subst. by exists w. }
  rewrite ref_typed_snoc in Hr; destruct Hr as (σ'&?&?).
  destruct (mval_lookup_seg_unfreeze_exists m w τ rs σ') as (w'&?&?); auto.
  destruct (IH w' σ') as (w''&?&?); eauto using munion_free_lookup_seg.
  exists w''. rewrite fmap_app; simpl.
  rewrite mval_lookup_snoc. by simplify_option_equality.
Qed.

Lemma mval_lookup_seg_union_free m w τ rs σ :
  m ⊢ w : τ → rs @ τ ↣ σ → munion_free w → ∃ w', w !! rs = Some w' ∧ m ⊢ w' : σ.
Proof.
  destruct 1 as [τ bs|ws τ|s ws τs ? Hws|s j τs w τ|s τs bs] using @mtyped_case;
    inversion 1; inversion 1;
    repeat (simplify_option_equality || simplify_list_equality || case_decide).
  * destruct (lookup_lt_is_Some_2 ws i) as (w&?); auto.
    exists w; split; auto. eapply (Forall_lookup_1 (flip (typed m) _)); eauto.
  * edestruct (Forall2_lookup_r (typed m)); eauto.
  * eauto.
  * eauto.
  * eauto using mval_of_bits_typed, env_valid_lookup_lookup.
Qed.
Lemma mval_lookup_Some_union_free m w τ r σ :
  m ⊢ w : τ → r @ τ ↣ σ → munion_free w → ∃ w', w !! r = Some w' ∧ m ⊢ w' : σ.
Proof.
  revert w τ. induction r as [|rs r IH] using rev_ind; intros w τ Hvτ Hr ?.
  { rewrite ref_typed_nil in Hr; subst. by exists w. }
  rewrite ref_typed_snoc in Hr. destruct Hr as (σ'&?&?).
  destruct (mval_lookup_seg_union_free m w τ rs σ') as (w'&?&?); auto.
  destruct (IH w' σ') as (w''&?&?); eauto using munion_free_lookup_seg.
  exists w''. rewrite mval_lookup_snoc. by simplify_option_equality.
Qed.

Lemma mval_alter_nil f : alter f (@nil ref_seg) = f.
Proof. done. Qed.
Lemma mval_alter_cons f rs r : alter f (rs :: r) = alter (alter f rs) r.
Proof. done. Qed.
Lemma mval_alter_singleton f rs : alter f [rs] = alter f rs.
Proof. done. Qed.
Lemma mval_alter_app f w r1 r2 : alter f (r1 ++ r2) w = alter (alter f r1) r2 w.
Proof.
  revert f. induction r1; simpl; intros; rewrite ?mval_alter_cons; auto.
Qed.
Lemma mval_alter_snoc f w r rs : alter f (r ++ [rs]) w = alter (alter f r) rs w.
Proof. apply mval_alter_app. Qed.

Lemma mval_alter_seg_freeze f rs : alter f (freeze rs) = alter f rs.
Proof. by destruct rs. Qed.
Lemma mval_alter_freeze f r : alter f (freeze <$> r) = alter f r.
Proof.
  revert f. induction r as [|rs r IH]; intros f; simpl; [done |].
  by rewrite !mval_alter_cons, IH, mval_alter_seg_freeze.
Qed.
Global Instance:
  Proper ((~{fmap freeze}) ==> (=)) (alter f : ref → mval Ti → mval Ti).
Proof. intros ??? E. by rewrite <-mval_alter_freeze, E, mval_alter_freeze. Qed.

Lemma mval_alter_seg_typed m f w j rs τ σ :
  m ⊢ w : τ → rs @ τ ↣ σ →
  (∀ w', m ⊢ w' : σ → m ⊢ f w' : σ) →
  m ⊢ alter f (ref_seg_set_offset j rs) w : τ.
Proof.
  intros Hwτ Hrs Hf. unfold alter. revert w Hwτ.
  destruct rs; inversion Hrs; intros w Hwτ; pattern w;
    apply (mtyped_inv_r _ _ _ _ Hwτ); intros;
    repeat (case_match || simplify_option_equality); mtyped_constructor;
    eauto 10 using alter_length, Forall_alter, Forall2_alter_l, Forall_resize,
      BIndet_valid,mval_new_typed, env_valid_lookup_lookup, mval_of_bits_typed,
      mval_to_bits_valid with simplify_option_equality.
Qed.
Lemma mval_alter_typed m f w j r τ σ :
  m ⊢ w : τ → r @ τ ↣ σ →
  (∀ w, m ⊢ w : σ → m ⊢ f w : σ) →
  m ⊢ alter f (ref_set_offset j r) w : τ.
Proof.
  revert f j σ w. induction r as [|rs r IH]; simpl; intros f j σ w Hwτ.
  { rewrite ref_typed_nil. intros <- Hf. by apply Hf. }
  rewrite ref_typed_cons, mval_alter_cons. intros (τ'&?&?) Hf.
  rewrite <-(ref_set_offset_offset r). eauto using mval_alter_seg_typed.
Qed.

Lemma mval_alter_seg_le m f g w1 w2 τ j rs σ :
  m ⊢ w1 : τ → rs @ τ ↣ σ → w1 ⊑@{m} w2 →
  (∀ w3 w4, m ⊢ w3 : σ → w3 ⊑@{m} w4 → f w3 ⊑@{m} g w4) →
  alter f (ref_seg_set_offset j rs) w1 ⊑@{m}
    alter g (ref_seg_set_offset j rs) w2.
Proof.
  intros Hw1 Hrs Hw12 Hfg. unfold alter. destruct Hw12 using @mval_le_case;
    inversion Hw1; destruct rs; inversion Hrs; simpl; intros;
    simplify_equality; try mval_le_constructor; eauto.
  * apply Forall2_alter; auto. intros; decompose_Forall_hyps; eauto.
  * simplify_option_equality.
    apply Forall2_alter; auto. intros; decompose_Forall_hyps; eauto.
  * repeat (case_match || simplify_option_equality);
      mval_le_constructor; eauto. eapply Hfg.
    + eapply mval_of_bits_typed; eauto using env_valid_lookup_lookup.
      eauto using Forall_resize, BIndet_valid, mval_to_bits_valid.
    + eapply mval_of_bits_le; eauto using env_valid_lookup_lookup.
      eapply Forall2_resize; eauto using mval_to_bits_le.
  * repeat (case_match || simplify_option_equality);
      mval_le_constructor; eauto. eapply Hfg.
    + eapply mval_of_bits_typed; eauto using env_valid_lookup_lookup.
    + eapply mval_of_bits_le; eauto using env_valid_lookup_lookup.
  * repeat (case_match || simplify_option_equality);
      mval_le_constructor; eauto. eapply Hfg.
    + eapply mval_of_bits_typed; eauto using env_valid_lookup_lookup.
      eauto using Forall_resize, BIndet_valid, mval_to_bits_valid.
    + eapply mval_of_bits_le; eauto using env_valid_lookup_lookup.
      eauto using mval_to_of_bits_le_flip,
        env_valid_lookup_lookup, bit_size_of_union_lookup.
Qed.
Lemma mval_alter_le m f g w1 w2 τ j r σ :
  m ⊢ w1 : τ → r @ τ ↣ σ → w1 ⊑@{m} w2 →
  (∀ w3 w4, m ⊢ w3 : σ → w3 ⊑@{m} w4 → f w3 ⊑@{m} g w4) →
  alter f (ref_set_offset j r) w1 ⊑@{m} alter g (ref_set_offset j r) w2.
Proof.
  revert f g j σ w1 w2. induction r as [|rs r IH]; simpl; intros f g j σ w1 w2.
  { rewrite ref_typed_nil. intros ? <- ? Hf. by apply Hf. }
  rewrite ref_typed_cons, !mval_alter_cons. intros ? (τ'&?&?) ? Hf.
  rewrite <-(ref_set_offset_offset r). eauto using mval_alter_seg_le.
Qed.

Lemma mval_lookup_alter_seg_freeze m f w rs τ w' :
  m ⊢ w : τ → w !! unfreeze rs = Some w' →
  alter f rs w !! freeze rs = Some (f w').
Proof.
  unfold alter. destruct 1 using @mtyped_case; destruct rs; intros;
    repeat (simplify_option_equality || case_decide); try done.
  * rewrite list_lookup_alter. by simplify_option_equality.
  * exfalso. eauto using alter_length.
  * rewrite list_lookup_alter. by simplify_option_equality.
  * rewrite !mval_of_bits_resize by
      eauto using env_valid_lookup_lookup, bit_size_of_union_lookup; eauto.
Qed.
Lemma mval_lookup_alter_freeze m f w r τ w' :
  m ⊢ w : τ → w !! (unfreeze <$> r) = Some w' →
  alter f r w !! (freeze <$> r) = Some (f w').
Proof.
  intros Hvτ. revert f τ w Hvτ.
  induction r as [|rs r IH] using rev_ind; intros f τ w Hvτ.
  { rewrite !mval_lookup_nil, mval_alter_nil. congruence. }
  rewrite !fmap_app; simpl. rewrite ?mval_alter_snoc, ?mval_lookup_snoc.
  intro. simplify_option_equality.
  erewrite mval_lookup_alter_seg_freeze by eauto. simpl.
  edestruct mval_lookup_seg_Some as [? [??]]; eauto.
Qed.
Lemma mval_lookup_alter m f w r τ w' :
  m ⊢ w : τ → w !! (unfreeze <$> r) = Some w' →
  alter f r w !! r = Some (f w').
Proof. eauto using mval_lookup_freeze, mval_lookup_alter_freeze. Qed.

Lemma mval_lookup_alter_seg_disjoint m f w τ σ rs1 rs2 :
  m ⊢ w : τ → rs2 @ τ ↣ σ → rs1 ⊥ rs2 → alter f rs1 w !! rs2 = w !! rs2.
Proof.
  unfold alter. intros Hw Hrs2. destruct 1; inversion Hw; inversion Hrs2;
    simplify_option_equality;
    auto using list_lookup_alter_ne; by (exfalso; auto using alter_length).
Qed.
Lemma mval_lookup_alter_disjoint m f w τ r1 r2 w' :
  m ⊢ w : τ → w !! r2 = Some w' →
  r1 ⊥ r2 → alter f r1 w !! r2 = Some w'.
Proof.
  rewrite ref_disjoint_alt.
  intros Hvτ Hw' (r1'&rs1&r1''&r2'&rs2&r2''&?&?&?&Hr); subst.
  revert Hw'. rewrite !mval_alter_app, !mval_lookup_app,
    !mval_alter_singleton, !mval_lookup_singleton.
  intros. destruct (w !! r2'') as [w1'|] eqn:Hw1'; simplify_equality'.
  destruct (w1' !! rs2) as [w2'|] eqn:Hw2'; simplify_equality'.
  destruct (mval_lookup_Some m w τ r2'' w1') as (σ1&?&?); auto.
  destruct (mval_lookup_seg_Some m w1' σ1 rs2 w2') as (σ2&?&?); auto.
  rewrite option_bind_assoc. apply bind_Some.
  exists (alter (alter f r1') rs1 w1'); split.
  { apply mval_lookup_freeze. rewrite <-Hr.
    eapply mval_lookup_alter_freeze; eauto using mval_lookup_unfreeze.
    rewrite <-ref_unfreeze_freeze, Hr, ref_unfreeze_freeze.
    by apply mval_lookup_unfreeze. }
  simpl. by erewrite mval_lookup_alter_seg_disjoint, Hw2' by eauto.
Qed.

Lemma mval_alter_seg_ext f g w rs :
  (∀ w', f w' = g w') → alter f rs w = alter g rs w.
Proof.
  unfold alter. destruct rs, w;
    repeat (simplify_option_equality || case_match);
    intros; auto using list_alter_ext with f_equal.
Qed.
Lemma mval_alter_ext f g w r :
  (∀ w, f w = g w) → alter f r w = alter g r w.
Proof.
  intros. revert w. induction r as [|rs r IH] using rev_ind; intros w; [done|].
  rewrite !mval_alter_snoc. by apply mval_alter_seg_ext.
Qed.

Lemma mval_alter_seg_ext_typed m f g w τ i rs σ :
  m ⊢ w : τ → rs @ τ ↣ σ →
  (∀ w', m ⊢ w' : σ → f w' = g w') →
  alter f (ref_seg_set_offset i rs) w = alter g (ref_seg_set_offset i rs) w.
Proof.
  unfold alter. destruct 1 using @mtyped_case;
    destruct rs; inversion 1;
    repeat (simplify_option_equality || case_match); intros Hfg; f_equal; auto.
  * apply list_alter_ext. intros w' Hw'.
    eapply Hfg, (Forall_lookup_1 (λ w', m ⊢ w' : _)); eauto.
  * apply list_alter_ext. intros w' Hw'.
    eapply Hfg, (Forall2_lookup_lr (typed m)); eauto.
  * intros; f_equal; eauto 10 using mval_of_bits_typed,
      env_valid_lookup_lookup, Forall_resize, BIndet_valid, mval_to_bits_valid.
  * intros; f_equal; eauto 10 using mval_of_bits_typed, env_valid_lookup_lookup.
Qed.
Lemma mval_alter_ext_typed m f g w τ i r σ :
  m ⊢ w : τ → r @ τ ↣ σ →
  (∀ w', m ⊢ w' : σ → f w' = g w') →
  alter f (ref_set_offset i r) w = alter g (ref_set_offset i r) w.
Proof.
  revert i f g σ. induction r as [|rs r IH]; simpl; intros i f g σ.
  { rewrite ref_typed_nil. intros ? <-; eauto. }
  rewrite ref_typed_cons, !mval_alter_cons. intros ? (?&?&?) ?.
  rewrite <-(ref_set_offset_offset r). eauto using mval_alter_seg_ext_typed.
Qed.

Lemma mval_alter_seg_compose f1 f2 w rs :
  alter (f1 ∘ f2) rs w = alter f1 rs (alter f2 rs w).
Proof.
  unfold alter. destruct rs, w;
    repeat (simplify_option_equality || case_match); auto;
    by rewrite list_alter_compose.
Qed.
Lemma mval_alter_compose f1 f2 w r :
  alter (f1 ∘ f2) r w = alter f1 r (alter f2 r w).
Proof.
  intros. revert w. induction r as [|rs r IH] using rev_ind; intros w; [done|].
  rewrite !mval_alter_snoc, <-mval_alter_seg_compose.
  by apply mval_alter_seg_ext.
Qed.

Lemma mval_alter_seg_commute f1 f2 w rs1 rs2 :
  rs1 ⊥ rs2 → alter f1 rs1 (alter f2 rs2 w) = alter f2 rs2 (alter f1 rs1 w).
Proof.
  unfold alter. destruct 1, w; simplify_option_equality; auto;
    by rewrite list_alter_commute.
Qed.
Lemma mval_alter_commute f1 f2 w r1 r2 :
  r1 ⊥ r2 → alter f1 r1 (alter f2 r2 w) = alter f2 r2 (alter f1 r1 w).
Proof.
  rewrite ref_disjoint_alt. unfold proj_eq.
  intros (r1'&rs1'&r1''&r2'&rs2'&r2''&?&?&?&Hr); subst.
  rewrite !mval_alter_app, !mval_alter_singleton.
  rewrite <-!(mval_alter_freeze _ r1''), !Hr, !mval_alter_freeze.
  rewrite <-!mval_alter_compose. apply mval_alter_ext. intros w'; simpl.
  by apply mval_alter_seg_commute.
Qed.

Lemma mval_lookup_non_aliasing_help m f w τ s τs r τ1 i1 τ2 i2 :
  let r1' := RUnion i1 s false :: r in
  let r2' := RUnion i2 s false :: r in
  m ⊢ w : τ → r @ τ ↣ union s → get_env !! s = Some τs →
  τs !! i1 = Some τ1 → τs !! i2 = Some τ2 →
  i1 ≠ i2 → alter f r1' w !! r2' = None.
Proof.
  intros r1' r2' Hw Hr ??? Hi. unfold r1', r2'; clear r1' r2'.
  rewrite !mval_alter_cons, !mval_lookup_cons.
  destruct (mval_lookup_unfreeze_exists m w τ r (union s))
    as (w'&Hr'&Hw'); auto.
  erewrite !mval_lookup_alter by eauto; unfold alter; simpl.
  revert Hr'. pattern w'. by apply (mtyped_inv_r m _ w' (union s) Hw');
    intros; repeat (case_decide || simplify_option_equality).
Qed.
Lemma mval_lookup_non_aliasing m f w τ s r r1 j1 σ1 i1 r2 j2 σ2 i2 :
  let r1' := r1 ++ RUnion i1 s false :: r in
  let r2' := r2 ++ RUnion i2 s false :: r in
  m ⊢ w : τ →
  r1' @ τ ↣ σ1 → r2' @ τ ↣ σ2 → i1 ≠ i2 →
  alter f (ref_set_offset j1 r1') w !! (ref_set_offset j2 r2') = None.
Proof.
  assert (∀ j r3 i3, ref_set_offset j (r3 ++ RUnion i3 s false :: r) =
    ref_set_offset j r3 ++ RUnion i3 s false :: r) as Hrhelp.
  { by intros ? [|??] ?. }
  intros r1' r2'; unfold r1', r2'; clear r1' r2'.
  rewrite !Hrhelp, !ref_typed_app; setoid_rewrite ref_typed_cons.
  intros Hw (τ1&(τ'&?&Hr1)&?) (τ2&(τ''&?&Hr2)&?) Hi; simplify_type_equality.
  inversion Hr1; inversion Hr2; simplify_option_equality.
  rewrite mval_lookup_app, mval_alter_app, bind_None; left.
  eauto using mval_lookup_non_aliasing_help.
Qed.
End mval.
