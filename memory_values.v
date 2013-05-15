(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export bytes.
Local Open Scope ctype_scope.

Inductive mval' (Ti C : Set) :=
  | MBase : base_type Ti → list (byte' Ti C) → mval' Ti C
  | MArray : list (mval' Ti C) → mval' Ti C
  | MStruct : tag → list (mval' Ti C) → mval' Ti C
  | MUnion : tag → nat → mval' Ti C → mval' Ti C
  | MUnionNone : tag → list (byte' Ti C) → mval' Ti C.
Notation mval Ti Vi := (mval' Ti (char Ti Vi)).
Arguments MBase {_ _} _ _.
Arguments MArray {_ _} _.
Arguments MStruct {_ _} _ _.
Arguments MUnion {_ _} _ _ _.
Arguments MUnionNone {_ _} _ _.

Instance mval_eq_dec {Ti C : Set}
  `{∀ τ1 τ2 : Ti, Decision (τ1 = τ2)} `{∀ c1 c2 : C, Decision (c1 = c2)} :
  ∀ w1 w2 : mval' Ti C, Decision (w1 = w2).
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
  Context {Ti C} (P : mval' Ti C → Prop).
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

Definition mval_map {Ti C} (f : list (byte' Ti C) → list (byte' Ti C)) :
    mval' Ti C → mval' Ti C :=
  fix go w :=
  match w with
  | MBase τ bs => MBase τ (f bs)
  | MArray ws => MArray (go <$> ws)
  | MStruct s ws => MStruct s (go <$> ws)
  | MUnion s i w => MUnion s i (go w)
  | MUnionNone s bs => MUnionNone s (f bs)
  end.

Section operations.
  Context `{EnvSpec Ti Vi} `{TypeOfIndex Ti M}.

  Global Instance type_of_mval: TypeOf (type Ti) (mval Ti Vi) :=
    fix go w :=
    match w with
    | MBase τ _ => base τ
    | MArray [] => TVoid
    | MArray (w :: ws) => go w.[length (w :: ws)]
    | MStruct s ws => struct s
    | MUnion s _ _ => union s
    | MUnionNone s _ => union s
    end.
  Global Instance mtype_check: TypeCheck M (type Ti) (mval Ti Vi) := λ m,
    fix go w :=
    match w with
    | MBase τ bs =>
       guard (base_type_valid get_env τ);
       guard (m ⊢* valid bs);
       guard (length bs = size_of (base τ));
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
       guard (length bs = size_of (union s));
       Some (union s)
    end.

  Definition mval_to_bytes : mval Ti Vi → list (byte Ti Vi) :=
    fix go w :=
    match w with
    | MBase _ bs => bs
    | MArray ws => ws ≫= go
    | MStruct s ws =>
       default [] (get_env !! s) $ λ τs,
         let flds := struct_fields τs in
         mjoin $ zip_with (λ w sz, resize sz BUndef (go w)) ws flds
    | MUnion s i w => resize (size_of (union s)) BUndef (go w)
    | MUnionNone _ bs => bs
    end.
  Definition mval_of_bytes: type Ti → list (byte Ti Vi) → mval Ti Vi :=
    type_iter
    (*i TBase =>     *) (λ τ bs, MBase τ $ resize (size_of (base τ)) BUndef bs)
    (*i TVoid =>     *) (λ bs, MBase uchar []) (* dummy *)
    (*i TArray =>    *) (λ τ n rec bs, MArray $ array_of_bytes rec τ n bs)
    (*i TCompound => *) (λ c s τs rec bs,
      match c with
      | Struct => MStruct s $ struct_of_bytes rec τs bs
      | Union =>
         match list_singleton_dec τs with
         | inleft (τ↾_) => MUnion s 0 $ rec τ bs
         | _ => MUnionNone s $ resize (size_of (union s)) BUndef bs
         end
      end).

  Definition mval_new (f : base_type Ti → list (byte Ti Vi)) :
      type Ti → mval Ti Vi := type_iter
    (*i TBase     *) (λ τ, MBase τ (f τ))
    (*i TVoid     *) (MBase (TInt TuChar) []) (* dummy *)
    (*i TArray    *) (λ τ n x, MArray (replicate n x))
    (*i TCompound *) (λ c s τs rec,
      match c with
      | Struct => MStruct s (rec <$> τs)
      | Union =>
         match list_singleton_dec τs with
         | inleft (τ↾_) => MUnion s 0 (rec τ)
         | _ => MUnionNone s $ replicate (size_of (union s)) BUndef
         end
      end).
  Notation mval_new_undef := (mval_new base_undef_bytes).

  Definition munion_reset : mval Ti Vi → mval Ti Vi :=
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
            resize (size_of (union s)) BUndef $ mval_to_bytes w
         end
    | MUnionNone s bs => MUnionNone s bs
    end.

  Global Instance mval_alter_seg:
      Alter ref_seg (mval Ti Vi) (mval Ti Vi) := λ f rs w,
    match rs, w with
    | RArray i n _, MArray ws =>
       if decide (n = length ws) then MArray (alter f i ws) else w
    | RStruct i, MStruct s ws => MStruct s (alter f i ws)
    | RUnion i b, MUnion s j w' =>
       if decide (i = j) then MUnion s i (f w')
       else if b then
         default w (get_env !! s ≫= (!! i)) $ λ τ,
           MUnion s i $ f $ mval_new_undef τ
       else w
    | RUnion i b, MUnionNone s bs =>
       default w (get_env !! s ≫= (!! i)) $ λ τ,
         MUnion s i $ f $ mval_of_bytes τ bs
    | _, _ => w
    end.
  Global Instance mval_alter: Alter ref (mval Ti Vi) (mval Ti Vi) :=
    fix go f r :=
    match r with
    | [] => f
    | rs :: r => @alter _ _ _ (alter f rs) (go (alter f rs)) r
    end.
  Global Instance mval_alter_byte:
      Alter (ref * nat) (byte Ti Vi) (mval Ti Vi) := λ f ri,
    alter (λ w, mval_of_bytes (type_of w) $
      alter f (snd ri) $ mval_to_bytes w) (fst ri).

  Global Instance mval_lookup_seg:
      Lookup ref_seg (mval Ti Vi) (mval Ti Vi) := λ rs w,
    match rs, w with
    | RArray i n _, MArray ws => guard (n = length ws); ws !! i
    | RStruct i, MStruct _ ws => ws !! i
    | RUnion i _, MUnion s j w => guard (i = j); Some w
    | RUnion i _, MUnionNone s bs =>
       τ ← get_env !! s ≫= (!! i);
       Some $ mval_of_bytes τ bs
    | _, _ => None
    end.
  Global Instance mval_lookup: Lookup ref (mval Ti Vi) (mval Ti Vi) :=
    fix go r w :=
    match r with
    | [] => Some w
    | rs :: r => @lookup _ _ _ go r w ≫= (!! rs)
    end.
  Global Instance mval_lookup_byte:
      Lookup (ref * nat) (byte Ti Vi) (mval Ti Vi) := λ ri w,
    w' ← w !! fst ri;
    mval_to_bytes w' !! snd ri.

  Definition mval_force : ref → mval Ti Vi → mval Ti Vi := alter id.
End operations.

Notation mval_new_undef := (mval_new base_undef_bytes).

Section typed.
  Context `{EnvSpec Ti Vi} `{TypeOfIndex Ti M}.

  Inductive mtyped' (m : M) : mval Ti Vi → type Ti → Prop :=
    | MBase_typed' τ bs :
       base_type_valid get_env τ →
       m ⊢* valid bs →
       length bs = size_of (base τ) →
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
       m ⊢* valid bs →
       length bs = size_of (union s) →
       mtyped' m (MUnionNone s bs) (union s).
  Global Instance mtyped: Typed M (type Ti) (mval Ti Vi) := mtyped'.

  Lemma MBase_typed m τ bs :
    base_type_valid get_env τ →  m ⊢* valid bs →
    length bs = size_of (base τ) → m ⊢ MBase τ bs : base τ.
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
    length bs = size_of (union s) → m ⊢ MUnionNone s bs : union s.
  Proof. econstructor; eauto. Qed.

  Lemma mtyped_inv_l m (P : type Ti → Prop) w τ :
    m ⊢ w : τ →
    match w with
    | MBase τ' bs =>
       (base_type_valid get_env τ' → length bs = size_of (base τ') →
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
         length bs = size_of (union s) → P (union s)) → P τ
    end .
  Proof. destruct 1; eauto. Qed.

  Lemma mtyped_inv_r m (P : mval Ti Vi → Prop) w τ :
    m ⊢ w : τ →
    match τ with
    | void => P w
    | base τ' =>
       (∀ bs, base_type_valid get_env τ' → length bs = size_of (base τ') →
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
         length bs = size_of (union s) → P (MUnionNone s bs)) →
       P w
    end.
  Proof. destruct 1; eauto. Qed.

  Section mtyped_ind.
    Context (m : M) (P : mval Ti Vi → type Ti → Prop).
    Context (Pbase : ∀ τ bs,
      base_type_valid get_env τ →  m ⊢* valid bs →
      length bs = size_of (base τ) → P (MBase τ bs) (base τ)).
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
      length bs = size_of (union s) → P (MUnionNone s bs) (union s)).
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
    Context (m : M) (P : mval Ti Vi → type Ti → Prop).
    Context (Pbase : ∀ τ bs,
      base_type_valid get_env τ → m ⊢* valid bs →
      length bs = size_of (base τ) → P (MBase τ bs) (base τ)).
    Context (Parray : ∀ ws τ,
      m ⊢* ws : τ → length ws ≠ 0 → P (MArray ws) (τ.[length ws])).
    Context (Pstruct : ∀ s ws τs,
      get_env !! s = Some τs → m ⊢* ws :* τs → P (MStruct s ws) (struct s)).
    Context (Punion : ∀ s i τs w τ,
      get_env !! s = Some τs → τs !! i = Some τ →
      m ⊢ w : τ → P (MUnion s i w) (union s)).
    Context (Punion_none : ∀ s τs bs,
      get_env !! s = Some τs → length τs ≠ 1 → m ⊢* valid bs →
      length bs = size_of (union s) → P (MUnionNone s bs) (union s)).
    Lemma mtyped_case : ∀ w τ, mtyped' m w τ → P w τ.
    Proof. destruct 1; eauto. Qed.
  End mtyped_case.
End typed.

Ltac mtyped_constructor := first
  [ eapply MBase_typed | eapply MArray_typed | eapply MStruct_typed
  | eapply MUnion_typed | eapply MUnionNone_typed ].

Section mval_le.
  Context `{EnvSpec Ti Vi} `{TypeOfIndex Ti M}.

  Inductive mval_le' (m : M) : relation (mval Ti Vi) :=
    | MBase_le' τ bs1 bs2 :
       bs1 ⊑@{m}* bs2 → mval_le' m (MBase τ bs1) (MBase τ bs2)
    | MArray_le' ws1 ws2 :
       Forall2 (mval_le' m) ws1 ws2 → mval_le' m (MArray ws1) (MArray ws2)
    | MStruct_le' s ws1 ws2 :
       Forall2 (mval_le' m) ws1 ws2 → mval_le' m (MStruct s ws1) (MStruct s ws2)
    | MUnion_le' s i w1 w2 :
       mval_le' m w1 w2 → mval_le' m (MUnion s i w1) (MUnion s i w2)
    | MUnionNone_le' s bs1 bs2 :
       bs1 ⊑@{m}* bs2 →
       mval_le' m (MUnionNone s bs1) (MUnionNone s bs2)
    | MUnion_MUnionNone_le' s i τs w τ bs :
       get_env !! s = Some τs → τs !! i = Some τ → length τs ≠ 1 →
       mval_le' m w (mval_of_bytes τ bs) →
       m ⊢* valid bs → length bs = size_of (union s) →
       mval_le' m (MUnion s i w) (MUnionNone s bs).
  Global Instance mval_le: SubsetEqEnv M (mval Ti Vi) := mval_le'.

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
    w ⊑@{m} mval_of_bytes τ bs →
    m ⊢* valid bs → length bs = size_of (union s) →
    MUnion s i w ⊑@{m} MUnionNone s bs.
  Proof. econstructor; eauto. Qed.

  Lemma mval_le_inv_l (m : M) (P : mval Ti Vi → Prop) w1 w2 :
    w1 ⊑@{m} w2 →
    match w1 with
    | MBase τ bs1 => (∀ bs2, bs1 ⊑@{m}* bs2 → P (MBase τ bs2)) → P w2
    | MArray ws1 => (∀ ws2, ws1 ⊑@{m}* ws2 → P (MArray ws2)) → P w2
    | MStruct s ws1 => (∀ ws2, ws1 ⊑@{m}* ws2 → P (MStruct s ws2)) → P w2
    | MUnion s i w1 =>
       (∀ w2, w1 ⊑@{m} w2 → P (MUnion s i w2)) →
       (∀ τs τ bs,
         get_env !! s = Some τs → τs !! i = Some τ → length τs ≠ 1 →
         w1 ⊑@{m} mval_of_bytes τ bs →
         m ⊢* valid bs → length bs = size_of (union s) →
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
         w1 ⊑@{m} mval_of_bytes τ bs →
         m ⊢* valid bs → length bs = size_of (union s1) → P) → P
    | _, _ => P
    end.
  Proof. destruct 1; eauto. Qed.

  Section mval_le_ind.
    Context (m : M) (P : mval Ti Vi → mval Ti Vi → Prop).
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
      w ⊑@{m} mval_of_bytes τ bs → P w (mval_of_bytes τ bs) →
      m ⊢* valid bs → length bs = size_of (union s) →
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
    Context (m : M) (P : mval Ti Vi → mval Ti Vi → Prop).
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
      w ⊑@{m} mval_of_bytes τ bs →
      m ⊢* valid bs → length bs = size_of (union s) →
      P (MUnion s i w) (MUnionNone s bs)).
    Definition mval_le_case: ∀ w1 w2, mval_le' m w1 w2 → P w1 w2.
    Proof. destruct 1; eauto. Qed.
  End mval_le_case.
End mval_le.

Ltac mval_le_constructor := first
  [ eapply MBase_le | eapply MArray_le | eapply MStruct_le
  | eapply MUnion_le | eapply MUnionNone_le | eapply MUnion_MUnionNone_le ].

Inductive munion_free `{EnvSpec Ti Vi} : mval Ti Vi → Prop :=
  | MBase_union_free τ bs : munion_free (MBase τ bs)
  | MArray_union_free ws : Forall munion_free ws → munion_free (MArray ws)
  | MStruct_union_free s ws : Forall munion_free ws → munion_free (MStruct s ws)
  | MUnion_union_free s w τ :
     get_env !! s = Some [τ] → munion_free w → munion_free (MUnion s 0 w)
  | MUnionNone_union_free s bs : munion_free (MUnionNone s bs).

Section munion_free_ind.
  Context `{EnvSpec Ti Vi} (P : mval Ti Vi → Prop).
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
Context `{EnvSpec Ti Vi} `{TypeOfIndex Ti M}.
Implicit Types w : mval Ti Vi.
Implicit Types ws : list (mval Ti Vi).
Implicit Types m : M.
Implicit Types τ : type Ti.
Implicit Types τs : list (type Ti).
Implicit Types bs : list (byte Ti Vi).
Implicit Types r : ref.
Implicit Types rs : ref_seg.

Lemma mtyped_type_valid m w τ : m ⊢ w : τ → type_valid get_env τ.
Proof.
  induction 1 using @mtyped_ind; econstructor; decompose_Forall_hyps; eauto.
Qed.
Global Instance: TypeOfSpec M (type Ti) (mval Ti Vi).
Proof.
  induction 1 using @mtyped_ind; decompose_Forall_hyps; simpl; f_equal; eauto.
Qed.

Global Instance: TypeCheckSpec M (type Ti) (mval Ti Vi).
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
      simplify_option_equality; try mtyped_constructor; eauto.
    + case_match; simplify_option_equality.
      mtyped_constructor; eauto using Forall2_Forall_typed.
    + decompose_Forall; eauto.
  * induction 1 using @mtyped_ind; simplify_option_equality; try done.
    + decompose_Forall_hyps; simplify_option_equality; try done;
        exfalso; eauto using Forall_replicate_eq.
    + erewrite mapM_Some_2; eauto. by simplify_option_equality.
Qed.

Lemma mval_of_bytes_base (τ : base_type Ti) bs :
  mval_of_bytes (base τ) bs = MBase τ $ resize (size_of (base τ)) BUndef bs.
Proof. unfold mval_of_bytes. by rewrite type_iter_base. Qed.
Lemma mval_of_bytes_array τ n bs :
  mval_of_bytes (τ.[n]) bs = MArray $ array_of_bytes (mval_of_bytes τ) τ n bs.
Proof. unfold mval_of_bytes. by rewrite type_iter_array. Qed.
Lemma mval_of_bytes_compound c s τs bs :
  get_env !! s = Some τs →
  mval_of_bytes (compound@{c} s) bs =
    match c with
    | Struct => MStruct s $ struct_of_bytes mval_of_bytes τs bs
    | Union =>
       match list_singleton_dec τs with
       | inleft (τ↾_) => MUnion s 0 $ mval_of_bytes τ bs
       | _ => MUnionNone s $ resize (size_of (union s)) BUndef bs
       end
    end.
Proof.
  intros Hs. unfold mval_of_bytes. erewrite (type_iter_compound
    (pointwise_relation (list (byte Ti Vi)) (@eq (mval Ti Vi)))); eauto.
  { repeat intro. f_equal. auto using array_of_bytes_ext. }
  clear s τs Hs bs. intros f g [] s τs Hs Hτs bs.
  * f_equal. auto using struct_of_bytes_ext.
  * by destruct (list_singleton_dec _) as [[??]|?];
      subst; decompose_Forall; f_equal.
Qed.

Lemma mval_of_bytes_typed m τ bs :
  type_valid get_env τ → m ⊢* valid bs → m ⊢ mval_of_bytes τ bs : τ.
Proof.
  intros Hτ. revert τ Hτ bs. refine (type_env_ind _ _ _ _).
  * intros τ Hτ bs Hbs. rewrite mval_of_bytes_base.
    mtyped_constructor; auto using Forall_resize, BUndef_valid.
    by rewrite resize_length.
  * intros τ n Hτ IH ? bs Hbs. rewrite mval_of_bytes_array.
    mtyped_constructor; eauto using array_of_bytes_length,
      Forall_array_of_bytes_alt.
  * intros [] s τs Hs Hτs IH ? bs Hbs.
    { rewrite (mval_of_bytes_compound _ _ τs) by done.
      apply MStruct_typed with τs; eauto using Forall2_struct_of_bytes_alt. }
    rewrite (mval_of_bytes_compound _ _ τs) by done.
    destruct (list_singleton_dec _) as [[τ ?]|?]; subst.
    + rewrite Forall_singleton in IH. eapply MUnion_typed, IH; eauto.
    + mtyped_constructor; eauto using Forall_resize, BUndef_valid.
      by rewrite resize_length.
Qed.
Lemma mval_of_bytes_type_of m τ bs :
  type_valid get_env τ → m ⊢* valid bs → type_of (mval_of_bytes τ bs) = τ.
Proof. eauto using type_of_correct, mval_of_bytes_typed. Qed.
Lemma mval_of_bytes_le m τ bs1 bs2 :
  type_valid get_env τ →
  bs1 ⊑@{m}* bs2 → mval_of_bytes τ bs1 ⊑@{m} mval_of_bytes τ bs2.
Proof.
  intros Hτ. revert τ Hτ bs1 bs2. refine (type_env_ind _ _ _ _).
  * intros τ ? bs1 bs2 Hbs. rewrite !mval_of_bytes_base. mval_le_constructor.
    by apply bytes_le_resize.
  * intros τ n ? IH Hn bs1 bs2 Hbs.
    rewrite !mval_of_bytes_array. mval_le_constructor. revert bs1 bs2 Hbs.
    elim n; simpl; auto using Forall2_take, Forall2_drop.
  * intros [] s τs Hs Hτs IH _ bs1 bs2 Hbs.
    { erewrite !mval_of_bytes_compound by eauto. mval_le_constructor.
      clear Hs Hτs. unfold struct_of_bytes. revert bs1 bs2 Hbs.
      induction (struct_fields_same_length τs); intros;
        decompose_Forall_hyps; simpl; auto using Forall2_take, Forall2_drop. }
    erewrite !mval_of_bytes_compound by eauto.
    destruct (list_singleton_dec _) as [[??]|?]; subst.
    + decompose_Forall_hyps. mval_le_constructor. auto.
    + mval_le_constructor. by apply bytes_le_resize.
Qed.

Lemma mval_of_bytes_resize τ bs sz :
  type_valid get_env τ → size_of τ ≤ sz →
  mval_of_bytes τ (resize sz BUndef bs) = mval_of_bytes τ bs.
Proof.
  intros Hτ. revert τ Hτ bs sz. refine (type_env_ind _ _ _ _).
  * intros τ Hτ bs sz ?. rewrite !mval_of_bytes_base.
    f_equal. by rewrite resize_resize by lia.
  * intros τ n Hτ IH _ bs sz. rewrite !mval_of_bytes_array, size_of_array.
    intros. f_equal. auto using array_of_bytes_resize.
  * intros [] s τs Hs Hτs IH _ bs ?.
    { erewrite !mval_of_bytes_compound, size_of_struct by eauto.
      intros. f_equal. auto using struct_of_bytes_resize. }
    erewrite !mval_of_bytes_compound by eauto.
    destruct (list_singleton_dec _) as [[τ ?]|?]; subst.
    + decompose_Forall. intros. f_equal.
      efeed pose proof size_of_union_singleton; eauto with lia.
    + intros. f_equal. by rewrite resize_resize by lia.
Qed.
Lemma mval_of_bytes_take τ bs sz :
  type_valid get_env τ → size_of τ ≤ sz →
  mval_of_bytes τ (take sz bs) = mval_of_bytes τ bs.
Proof.
  destruct (le_lt_dec sz (length bs)).
  * rewrite <-(resize_le bs _ BUndef) by done. apply mval_of_bytes_resize.
  * by rewrite take_ge by lia.
Qed.
Lemma mval_of_bytes_app τ bs1 bs2 :
  type_valid get_env τ → length bs1 = size_of τ →
  mval_of_bytes τ (bs1 ++ bs2) = mval_of_bytes τ bs1.
Proof.
  intros. by rewrite <-(mval_of_bytes_resize _ (bs1 ++ bs2) (size_of τ)),
    resize_app_le, mval_of_bytes_resize by auto with lia.
Qed.
Lemma mval_of_bytes_union_free τ bs :
  type_valid get_env τ → munion_free (mval_of_bytes τ bs).
Proof.
  intros Hτ. revert τ Hτ bs. refine (type_env_ind _ _ _ _).
  * intros. rewrite mval_of_bytes_base. by constructor.
  * intros. rewrite mval_of_bytes_array.
    constructor. by apply Forall_array_of_bytes.
  * intros []; intros.
    { erewrite !mval_of_bytes_compound by eauto.
      constructor. by apply Forall_struct_of_bytes. }
    erewrite !mval_of_bytes_compound by eauto.
    destruct (list_singleton_dec _) as [[τ ?]|?];
      subst; decompose_Forall; econstructor; eauto.
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
    eauto using resize_length, Forall2_length, bytes_valid_ge.
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
      env_valid_lookup_lookup, mval_of_bytes_typed, bytes_valid_le.
Qed.

Global Instance: PartialOrder (@subseteq_env M (mval Ti Vi) _ m).
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
      mval_le_constructor; eauto using bytes_valid_ge, mval_of_bytes_le,
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

Lemma mval_to_bytes_length m w τ :
  m ⊢ w : τ → length (mval_to_bytes w) = size_of τ.
Proof.
  induction 1 as [|vs τ _ IH _|s ws τs Hs Hτs IH| |] using @mtyped_ind; simpl.
  * done.
  * rewrite size_of_array. subst.
    induction IH; simpl; rewrite ?app_length; auto.
  * rewrite (size_of_struct _ τs), Hs by done. simpl. clear Hs Hτs.
    revert ws IH. induction (size_of_struct_fields τs)
      as [|τ sz ?? Hn]; intros; simpl in *; decompose_Forall; simpl; [done |].
    rewrite app_length, resize_length; f_equal. eauto.
  * by rewrite resize_length.
  * done.
Qed.
Lemma mval_to_bytes_valid m w τ : m ⊢ w : τ → m ⊢* valid (mval_to_bytes w).
Proof.
  induction 1 as [|vs τ _ IH _|s ws τs Hs Hτs IH| |] using @mtyped_ind; simpl.
  * done.
  * induction IH; simpl; decompose_Forall; auto.
  * rewrite Hs; simpl; clear Hs. revert ws Hτs IH.
    induction (size_of_struct_fields τs) as [|τ sz ?? Hn];
      intros; decompose_Forall; simpl; [constructor |].
    apply Forall_app; split; auto using Forall_resize, BUndef_valid.
  * apply Forall_resize; auto. constructor.
  * done.
Qed.
Lemma mval_of_to_bytes_aux m w τ bs :
  m ⊢ w : τ → mval_of_bytes τ (mval_to_bytes w ++ bs) = munion_reset w.
Proof.
  intros Hvτ. revert bs. induction Hvτ as
    [τ bs'|vs τ Hvs IH _|s ws τs Hs Hτs IH|s j τs w τ Hs ?? IH|s τs bs' Hs]
    using @mtyped_ind; intros bs; simpl.
  * rewrite mval_of_bytes_base. by rewrite resize_app_le, resize_all_alt by lia.
  * rewrite mval_of_bytes_array. f_equal. subst.
    induction IH; simpl; [done |]; intros; decompose_Forall.
    rewrite <-(associative_L (++)). f_equal; auto.
    rewrite drop_app_alt by eauto using mval_to_bytes_length, eq_sym. auto.
  * erewrite Hs, mval_of_bytes_compound by eauto. simpl.
    f_equal. clear Hs. unfold struct_of_bytes. revert ws Hτs IH.
    induction (size_of_struct_fields τs) as [|τ sz τs ??? IHflds]; intros ws;
      intros; decompose_Forall; simpl; f_equal.
    + rewrite resize_ge, <-!(associative_L (++)). auto.
      erewrite mval_to_bytes_length; eauto.
    + rewrite <-(associative_L (++)), drop_app_alt; eauto using resize_length.
  * erewrite Hs, mval_of_bytes_compound by eauto. simpl.
    destruct (list_singleton_dec _) as [[??]|?];
      simplify_list_equality; f_equal.
    + rewrite resize_ge, <-(associative_L (++)); auto.
      erewrite ?mval_to_bytes_length by eauto;
       eauto using (size_of_union_lookup _ _ 0).
    + by rewrite resize_app_le, resize_all_alt by (by rewrite ?resize_length).
  * erewrite mval_of_bytes_compound by eauto.
    destruct (list_singleton_dec _) as [[??]|?]; subst; [done |].
    by rewrite resize_app_le, resize_all_alt by lia.
Qed.
Lemma mval_of_to_bytes m w τ :
  m ⊢ w : τ → mval_of_bytes τ (mval_to_bytes w) = munion_reset w.
Proof.
  rewrite <-(right_id_L [] (++) (mval_to_bytes w)). apply mval_of_to_bytes_aux.
Qed.

Lemma mval_to_of_bytes_below m τ bs :
  type_valid get_env τ →
  m ⊢* valid bs →
  mval_to_bytes (mval_of_bytes τ bs) ⊑@{m}* resize (size_of τ) BUndef bs.
Proof.
  intros Hτ. revert τ Hτ bs. refine (type_env_ind _ _ _ _).
  * done.
  * intros τ n ? IH _ bs. rewrite mval_of_bytes_array; simpl.
    rewrite size_of_array. revert bs. induction n; simpl; intros bs ?.
    { by rewrite resize_0. }
    rewrite resize_plus. auto using Forall2_app, Forall_drop.
  * intros [] s τs Hs Hτs IH _ bs Hbs.
    { erewrite mval_of_bytes_compound by eauto; simpl.
      erewrite Hs, size_of_struct by eauto; simpl.
      clear Hs Hτs. revert bs Hbs. unfold struct_of_bytes.
      induction (size_of_struct_fields τs); simpl;
        intros bs ?; decompose_Forall_hyps.
      { by rewrite resize_0. }
      rewrite resize_plus. apply Forall2_app; auto using Forall_drop.
      eapply Forall2_resize_ge_r; eauto using Forall_BUndef_le. }
    erewrite mval_of_bytes_compound by eauto. destruct (list_singleton_dec _)
      as [[τ ?]|?]; subst; simpl; decompose_Forall_hyps; [|done].
    apply Forall2_resize_ge_r with (size_of τ);
      eauto using size_of_union_singleton, Forall_BUndef_le.
Qed.
Lemma mval_to_of_bytes_below_drop m τ bs :
  type_valid get_env τ → m ⊢* valid bs → size_of τ ≤ length bs →
  mval_to_bytes (mval_of_bytes τ bs) ++ drop (size_of τ) bs ⊑@{m}* bs.
Proof.
  intros. transitivity (resize (size_of τ) BUndef bs ++ drop (size_of τ) bs).
  * by apply Forall2_app; auto using mval_to_of_bytes_below.
  * by rewrite resize_le, take_drop.
Qed.

Lemma mval_to_of_bytes_le_flip_aux m w τ sz bs :
  type_valid get_env τ → size_of τ ≤ sz →
  m ⊢* valid bs → length bs = sz →
  mval_to_bytes w ⊑@{m}* mval_to_bytes (mval_of_bytes τ bs) →
  w ⊑@{m} mval_of_bytes τ bs → resize sz BUndef (mval_to_bytes w) ⊑@{m}* bs.
Proof.
  intros; subst. assert (m ⊢ w : τ) by eauto using mtyped_le, mval_of_bytes_typed.
  transitivity (mval_to_bytes (mval_of_bytes τ bs) ++ drop (size_of τ) bs);
    auto using mval_to_of_bytes_below_drop.
  rewrite resize_ge by (erewrite mval_to_bytes_length; eauto).
  apply Forall2_app, Forall2_replicate_l; auto using Forall_drop, Forall_BUndef_le.
  erewrite drop_length, mval_to_bytes_length; eauto.
Qed.
Lemma mval_to_bytes_le m w1 w2 :
  w1 ⊑@{m} w2 → mval_to_bytes w1 ⊑@{m}* mval_to_bytes w2.
Proof.
  assert (∀ ws1 ws2 szs,
    Forall2 (λ w1 w2, mval_to_bytes w1 ⊑@{m}* mval_to_bytes w2) ws1 ws2 →
    mjoin (zip_with (λ w sz, resize sz BUndef (mval_to_bytes w)) ws1 szs) ⊑@{m}*
    mjoin (zip_with (λ w sz, resize sz BUndef (mval_to_bytes w)) ws2 szs)).
  { intros ws1 ws2 szs Hvs. revert szs. induction Hvs; intros [|??]; simpl;
      auto using Forall2_app, bytes_le_resize. }
  induction 1 using @mval_le_ind; simpl; unfold default;
    repeat case_match; eauto using bytes_le_resize, Forall2_bind,
    mval_to_of_bytes_le_flip_aux, env_valid_lookup_lookup, size_of_union_lookup.
Qed.
Lemma mval_to_of_bytes_le_flip m w τ sz bs :
  type_valid get_env τ → size_of τ ≤ sz →
  m ⊢* valid bs → length bs = sz →
  w ⊑@{m} mval_of_bytes τ bs → resize sz BUndef (mval_to_bytes w) ⊑@{m}* bs.
Proof. eauto using mval_to_of_bytes_le_flip_aux, mval_to_bytes_le. Qed.

Section mval_new.
  Context (f : base_type Ti → list (byte Ti Vi)).

  Lemma mval_new_base (τ : base_type Ti) : mval_new f (base τ) = MBase τ (f τ).
  Proof. unfold mval_new. by rewrite type_iter_base. Qed.
  Lemma mval_new_array τ n :
    mval_new f (τ.[n]) = MArray (replicate n (mval_new f τ)).
  Proof. unfold mval_new. by rewrite type_iter_array. Qed.
  Lemma mval_new_compound c s τs :
    get_env !! s = Some τs →
    mval_new f (compound@{c} s) =
      match c with
      | Struct => MStruct s (mval_new f <$> τs)
      | Union =>
         match list_singleton_dec τs with
         | inleft (τ↾_) => MUnion s 0 $ mval_new f τ
         | _ => MUnionNone s $ replicate (size_of (union s)) BUndef
         end
      end.
  Proof.
    intros. unfold mval_new.
    rapply (@type_iter_compound Ti _ (@eq (mval Ti Vi))); eauto.
    { by intros; subst. }
    clear dependent s τs. intros ?? [] ? τs ??; simpl.
    * f_equal; by apply Forall_fmap_ext.
    * destruct (list_singleton_dec _) as [[??]|?]; subst;
        decompose_Forall; by f_equal.
  Qed.

  Lemma mval_new_typed m τ :
    (∀ σ, base_type_valid get_env σ → m ⊢* valid (f σ)) →
    (∀ σ, length (f σ) = size_of (base σ)) →
    type_valid get_env τ → m ⊢ mval_new f τ : τ.
  Proof.
    intros Hf1 Hf2. revert τ. refine (type_env_ind _ _ _ _).
    * intros. rewrite mval_new_base. mtyped_constructor; auto.
    * intros τ n ?? IH. rewrite mval_new_array. mtyped_constructor.
      + by rewrite replicate_length.
      + elim n; simpl; constructor; auto.
      + done. 
    * intros [|] s τs Hs Hτs IH _.
      { rewrite (mval_new_compound _ _ τs) by done.
        mtyped_constructor; [by eauto|].
        clear Hs Hτs. induction IH; constructor; auto. }
      rewrite (mval_new_compound _ _ τs) by done.
      destruct (list_singleton_dec τs) as [[τ ?]|?]; subst.
      { decompose_Forall. by mtyped_constructor; eauto. }
      mtyped_constructor; eauto.
      + apply Forall_replicate. by constructor.
      + by rewrite ?replicate_length.
  Qed.
End mval_new.

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
    + by erewrite mval_of_bytes_resize, mval_of_to_bytes
        by eauto using env_valid_lookup_lookup, size_of_union_lookup.
    + eauto using Forall_resize, BUndef_valid, mval_to_bytes_valid.
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
    mval_le_constructor; eauto using mval_to_of_bytes_le_flip,
      env_valid_lookup_lookup, size_of_union_lookup.
Qed.
Lemma munion_reset_typed m w τ : m ⊢ w : τ → m ⊢ munion_reset w : τ.
Proof. eauto using mtyped_ge, munion_reset_above. Qed.
Lemma munion_reset_le m w1 w2 :
  w1 ⊑@{m} w2 → munion_reset w1 ⊑@{m} munion_reset w2.
Proof.
  induction 1 using @mval_le_ind; simplify_option_equality; repeat case_match;
    repeat destruct (list_singleton_dec _) as [[??]|?]; simplify_equality;
    try mval_le_constructor; eauto using Forall2_fmap_2,
      bytes_le_resize, mval_to_bytes_le, mval_to_of_bytes_le_flip,
      env_valid_lookup_lookup, size_of_union_lookup.
Qed.
Lemma mval_new_undef_typed m τ :
  type_valid get_env τ → m ⊢ mval_new_undef τ : τ.
Proof.
  apply mval_new_typed; eauto using base_undef_bytes_valid, replicate_length.
Qed.
Lemma mval_new_undef_union_free τ :
  type_valid get_env τ → munion_free (mval_new_undef τ).
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
Lemma mval_new_undef_union_reset τ :
  type_valid get_env τ → munion_reset (mval_new_undef τ) = mval_new_undef τ.
Proof. eauto using munion_free_reset, mval_new_undef_union_free. Qed.

Lemma mval_to_bytes_new `{Inhabited M} τ :
  type_valid get_env τ →
  mval_to_bytes (mval_new_undef τ) = replicate (size_of τ) BUndef.
Proof.
  revert τ. refine (type_env_ind _ _ _ _).
  * intros τ ?. by rewrite mval_new_base.
  * intros τ n ?? _. rewrite mval_new_array. simpl.
    rewrite size_of_array. induction n as [|n IH]; simpl; [done|].
    rewrite replicate_plus. f_equal; auto.
  * intros [] s τs Hs Hτs IH _.
    + erewrite mval_new_compound by eauto. simpl.
      rewrite (size_of_struct _ τs) by done.
      rewrite Hs. simpl. clear Hs. revert Hτs IH.
      induction (size_of_struct_fields τs) as [|τ sz τs ??? IHflds];
        intros; decompose_Forall; simpl in *; [done |].
      rewrite !replicate_plus. f_equal; [|by auto].
      rewrite (le_plus_minus (size_of τ) sz) by done.
      rewrite replicate_plus, resize_plus_eq; [by f_equal; auto |].
      destruct (_ : Inhabited M) as [m].
      apply (mval_to_bytes_length m). eauto using mval_new_undef_typed.
    + erewrite mval_new_compound by eauto.
      destruct (list_singleton_dec _) as [[τ ?]|?]; subst; simpl; [|done].
      rewrite Forall_singleton in IH, Hτs. by rewrite IH, resize_replicate.
Qed.

Lemma mval_new_least_union_reset `{Inhabited M} m w τ :
  m ⊢ w : τ → mval_new_undef τ ⊑@{m} munion_reset w.
Proof.
  assert (∀ bs, m ⊢* valid bs → Forall (λ b, BUndef ⊑@{m} b) bs).
  { by induction 1; repeat constructor. }
  induction 1 using @mtyped_ind; simpl.
  * rewrite mval_new_base. unfold base_undef_bytes.
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
      apply Forall_resize; eauto using mval_to_bytes_valid.
  * erewrite mval_new_compound by eauto.
    destruct (list_singleton_dec τs) as [[??]|?]; subst; [done|].
    mval_le_constructor. apply Forall2_replicate_l; auto.
Qed.
Lemma mval_new_least `{Inhabited M} m w τ :
  m ⊢ w : τ → munion_free w → mval_new_undef τ ⊑@{m} w.
Proof.
  intros. rewrite <-(munion_free_reset w) by done.
  auto using mval_new_least_union_reset.
Qed.

Lemma mval_of_to_bytes_union_free m w τ :
  m ⊢ w : τ → munion_free w → mval_of_bytes τ (mval_to_bytes w) = w.
Proof. intros. erewrite mval_of_to_bytes, munion_free_reset; eauto. Qed.
Lemma mval_of_to_bytes_le_flip m w τ bs :
  m ⊢ w : τ → mval_to_bytes w ⊑@{m}* bs → w ⊑@{m} mval_of_bytes τ bs.
Proof.
  intros. transitivity (munion_reset w); eauto using munion_reset_above.
  erewrite <-mval_of_to_bytes by eauto.
  eauto using mval_of_bytes_le, mtyped_type_valid.
Qed.
Lemma mval_to_bytes_inj m w1 w2 τ :
  m ⊢ w1 : τ → m ⊢ w2 : τ →
  mval_to_bytes w1 = mval_to_bytes w2 → munion_reset w1 = munion_reset w2.
Proof. intros. erewrite <-!(mval_of_to_bytes) by eauto. by f_equal. Qed.

Lemma mval_of_bytes_replicate `{Inhabited M} τ :
  type_valid get_env τ →
  mval_of_bytes τ (replicate (size_of τ) BUndef) = mval_new_undef τ.
Proof.
  intros. rewrite <-mval_to_bytes_new by done.
  destruct (_ : Inhabited M) as [m].
  rewrite (mval_of_to_bytes m) by auto using mval_new_undef_typed.
  by apply mval_new_undef_union_reset.
Qed.

Lemma mval_lookup_nil w : w !! [] = Some w.
Proof. done. Qed.
Lemma mval_lookup_cons w rs r : w !! (rs :: r) = w !! r ≫= (!! rs).
Proof. done. Qed.
Lemma mval_lookup_singleton rs : lookup (A:=mval Ti Vi) [rs] = lookup rs.
Proof. done. Qed.
Lemma mval_lookup_app w r1 r2 : w !! (r1 ++ r2) = w !! r2 ≫= (!! r1).
Proof.
  induction r1 as [|rs1 r1 IH]; simpl.
  * by destruct (w !! r2).
  * by rewrite !mval_lookup_cons, IH, option_bind_assoc.
Qed.
Lemma mval_lookup_snoc w r rs : w !! (r ++ [rs]) = w !! rs ≫= (!! r).
Proof. apply mval_lookup_app. Qed.
Lemma mval_lookup_byte_nil w i : w !! ([],i) = mval_to_bytes w !! i.
Proof. done. Qed.
Lemma mval_lookup_byte_app w i r1 r2 : w !! (r1++r2,i) = w !! r2 ≫= (!! (r1,i)).
Proof.
  unfold lookup, mval_lookup_byte at 1 2. simpl.
  by rewrite mval_lookup_app, option_bind_assoc.
Qed.
Lemma mval_lookup_byte_snoc w i r rs : w !! (r++[rs],i) = w !! rs ≫= (!! (r,i)).
Proof. apply mval_lookup_byte_app. Qed.

Lemma mval_lookup_seg_Some m w τ rs w' :
  m ⊢ w : τ → w !! rs = Some w' → ∃ σ, τ ∙ rs ↝ σ ∧ m ⊢ w' : σ.
Proof.
  destruct 1 as [τ bs|ws τ n ?? Hws|s ws τs ? Hws|s j τs w τ|s τs bs];
    destruct rs as [i|i|i]; intros Hlookup; simplify_option_equality.
  * exists τ. split.
    + constructor; eauto using lookup_lt_length_1.
    + eapply (Forall_lookup (λ w, m ⊢ w : τ)); eauto.
  * destruct (Forall2_lookup_l _ _ _ i w' Hws) as [σ [??]]; eauto.
    exists σ. split; [|done]. econstructor; eauto.
  * exists τ. split; try econstructor; eauto.
  * eexists; split; try econstructor; eauto.
    apply mval_of_bytes_typed; eauto using env_valid_lookup_lookup, Forall_take.
Qed.
Lemma mval_lookup_Some m w τ r w' :
  m ⊢ w : τ → w !! r = Some w' → ∃ σ, τ ∙ r ↝ σ ∧ m ⊢ w' : σ.
Proof.
  revert w τ. induction r using rev_ind; intros w τ Hvτ Hr.
  * simpl in Hr. simplify_equality.
    eexists; split; [econstructor |]; eauto.
  * rewrite mval_lookup_snoc in Hr. simplify_option_equality.
    edestruct mval_lookup_seg_Some as [? [??]]; eauto.
    edestruct IHr as [? [??]]; eauto.
    eexists; split; [eapply ref_typed_snoc |]; eauto.
Qed.
Lemma mval_lookup_seg_typed m w τ rs w' σ :
  m ⊢ w : τ → w !! rs = Some w' → τ ∙ rs ↝ σ → m ⊢ w' : σ.
Proof.
  intros Hvτ Hw Hrσ.
  destruct (mval_lookup_seg_Some _ _ _ _ _ Hvτ Hw) as (σ'&Hrσ'&?).
  rewrite ref_seg_lookup_correct in Hrσ, Hrσ'. by simplify_option_equality.
Qed.
Lemma mval_lookup_typed m w τ r w' σ :
  m ⊢ w : τ → w !! r = Some w' → τ ∙ r ↝ σ → m ⊢ w' : σ.
Proof.
  intros Hvτ Hw' Hrσ.
  destruct (mval_lookup_Some _ _ _ _ _ Hvτ Hw') as (σ'&Hrσ'&?).
  rewrite ref_lookup_correct in Hrσ, Hrσ'. by simplify_option_equality.
Qed.

Lemma mval_eq m w1 w2 τ :
  m ⊢ w1 : τ → m ⊢ w2 : τ → (∀ i r, w1 !! (r,i) = w2 !! (r,i)) → w1 = w2.
Proof.
  intros Hw1τ. revert w1 τ Hw1τ w2. refine (mtyped_ind _ _ _ _ _ _ _).
  * intros τ bs ??? w2 Hw2. pattern w2.
    apply (mtyped_inv_r _ _ _ _ Hw2). intros bs' ?? Hbs' Hlookup.
    f_equal. apply list_eq. intros i. apply (Hlookup i []).
  * intros ws τ ? IH _ w2 Hw2. pattern w2.
    apply (mtyped_inv_r _ _ _ _ Hw2). intros ws' ? Hws' ? Hlookup.
    f_equal. apply list_eq_length; [by subst|]. intros j x y Hx Hy.
    rewrite Forall_lookup in IH, Hws'.
    apply (IH j x); eauto. intros i r.
    assert (j < length ws) as Hjn by eauto using lookup_lt_Some.
    specialize (Hlookup i (r ++ [RArray j (length ws) Hjn])).
    rewrite !mval_lookup_byte_snoc in Hlookup. by simplify_option_equality.
  * intros s ws τs ?? IH w2 Hw2. pattern w2.
    apply (mtyped_inv_r _ _ _ _ Hw2). intros ws' τs' ? Hvs' Hlookup.
    simplify_option_equality. f_equal. apply list_eq_length.
    { transitivity (length τs); eauto using Forall2_length, eq_sym. }
    intros j x y Hx Hy.
    destruct (Forall2_lookup_l (typed m) ws' τs j y) as [τ [??]]; auto.
    apply (Forall2_lookup_lr _ _ _ j x τ IH); auto. intros i r.
    specialize (Hlookup i (r ++ [RStruct j])).
    setoid_rewrite mval_lookup_byte_snoc in Hlookup.
    by simplify_option_equality.
  * intros s j τs w τ ?? ? IH w2 Hw2. pattern w2.
    apply (mtyped_inv_r _ _ _ _ Hw2).
    + intros j' τs' w' τ' ?? Hw' Hlookup. simplify_option_equality.
      destruct (decide (j' = j)); simplify_option_equality.
      - f_equal. eapply IH; auto. intros i r.
        specialize (Hlookup i (r ++ [RUnion j true])).
        setoid_rewrite mval_lookup_byte_snoc in Hlookup.
        by simplify_option_equality.
      - specialize (Hlookup 0 [RUnion j true]).
        setoid_rewrite (mval_lookup_byte_snoc _ _ [] (RUnion j true))
          in Hlookup; simplify_option_equality.
        revert Hlookup. rewrite mval_lookup_byte_nil, lookup_ge_None,
          (mval_to_bytes_length m _ τ), NPeano.Nat.le_ngt by done.
        intros []. eauto using size_of_pos, env_valid_lookup_lookup.
    + intros τs' bs ???? Hlookup. simplify_option_equality.
      destruct (list_lookup_other τs j τ) as (j' & τ' & ? & ?); auto.
      specialize (Hlookup 0 [RUnion j' true]).
      setoid_rewrite (mval_lookup_byte_snoc _ _ [] (RUnion j' true)) in Hlookup.
      simpl in Hlookup. repeat case_decide; simplify_option_equality.
      symmetry in Hlookup. apply eq_None_not_Some in Hlookup.
      destruct Hlookup. rewrite mval_lookup_byte_nil.
      apply lookup_lt_is_Some_2.
      rewrite (mval_to_bytes_length m _ τ'); eauto using Forall_take,
        size_of_pos, mval_of_bytes_typed, env_valid_lookup_lookup.
  * intros s τs bs ???? w2 Hw2. pattern w2.
    apply (mtyped_inv_r _ _ _ _ Hw2).
    + intros j' τs' w' τ' ??? Hlookup. simplify_option_equality.
      destruct (list_lookup_other τs j' τ') as (j & τ & ? & ?); auto.
      specialize (Hlookup 0 [RUnion j true]).
      setoid_rewrite (mval_lookup_byte_snoc _ _ [] (RUnion j true)) in Hlookup.
      simpl in Hlookup. repeat case_decide; simplify_option_equality.
      apply eq_None_not_Some in Hlookup.
      destruct Hlookup. rewrite mval_lookup_byte_nil.
      apply lookup_lt_is_Some_2.
      rewrite (mval_to_bytes_length m _ τ); eauto using Forall_take,
        size_of_pos, mval_of_bytes_typed, env_valid_lookup_lookup.
    + intros ?????? Hlookup. f_equal. apply list_eq, (λ i, Hlookup i []).
Qed.
Lemma mval_lookup_seg_le m w1 w2 rs w3 :
  w1 ⊑@{m} w2 → w1 !! rs = Some w3 → ∃ w4, w2 !! rs = Some w4 ∧ w3 ⊑@{m} w4.
Proof.
  assert (∀ s i τs w τ bs,
    get_env !! s = Some τs → τs !! i = Some τ → m ⊢ w : τ →
    resize (size_of (union s)) BUndef (mval_to_bytes w) ⊑@{m}* bs →
    w ⊑@{m} mval_of_bytes τ (take (size_of τ) bs)).
  { intros. apply mval_of_to_bytes_le_flip; trivial.
    rewrite <-(take_length_resize_alt (mval_to_bytes w)
      (size_of (union s)) (size_of τ) BUndef);
     eauto using size_of_union_lookup, mval_to_bytes_length,
       Forall2_take, eq_sym. }
  assert (∀ s i τs w τ (bs : list (byte Ti Vi)),
    resize (size_of (union s)) BUndef (mval_to_bytes w) ⊑@{m}* bs →
    get_env !! s = Some τs → τs !! i = Some τ →
    resize (size_of τ) BUndef (mval_to_bytes w) ⊑@{m}* take (size_of τ) bs).
  { intros. rewrite <-(take_resize_le _ _ (size_of (union s)));
      eauto using size_of_union_lookup, Forall2_take. }
  destruct 1 using @mval_le_case; destruct rs; intros;
    repeat (case_match || simplify_option_equality);
    eauto 7 using mval_of_bytes_le, mval_to_bytes_le,
      env_valid_lookup_lookup, bytes_le_resize, Forall2_take, Forall2_lookup_l;
    exfalso; eauto using Forall2_length.
Qed.
Lemma mval_lookup_seg_ge m w1 w2 rs w4 :
  w1 ⊑@{m} w2 → w2 !! rs = Some w4 →
  w1 !! rs = None ∨ ∃ w3, w1 !! rs = Some w3 ∧ w3 ⊑@{m} w4.
Proof.
  assert (∀ s i τs w τ bs,
    get_env !! s = Some τs → τs !! i = Some τ → m ⊢ w : τ →
    resize (size_of (union s)) BUndef (mval_to_bytes w) ⊑@{m}* bs →
    w ⊑@{m} mval_of_bytes τ (take (size_of τ) bs)).
  { intros. apply mval_of_to_bytes_le_flip; trivial.
    rewrite <-(take_length_resize_alt (mval_to_bytes w)
      (size_of (union s)) (size_of τ) BUndef); eauto using
      size_of_union_lookup, mval_to_bytes_length, Forall2_take, eq_sym. }
  destruct 1 using @mval_le_case; destruct rs; intros;
    repeat (case_match || simplify_option_equality);
    eauto 7 using mval_of_bytes_le, mval_to_bytes_le,
     env_valid_lookup_lookup, bytes_le_resize, Forall2_take, Forall2_lookup_r.
Qed.

Lemma mval_lookup_le m w1 w2 r w3 :
  w1 ⊑@{m} w2 → w1 !! r = Some w3 → ∃ w4, w2 !! r = Some w4 ∧ w3 ⊑@{m} w4.
Proof.
  revert w1 w2. induction r as [|rs r IH] using rev_ind; simpl.
  * intros. rewrite mval_lookup_nil. simplify_equality. eauto.
  * intros w1 w2. rewrite !mval_lookup_snoc. intros. simplify_option_equality.
    edestruct (mval_lookup_seg_le m w1 w2 rs) as (?&?&?);
      simplify_option_equality; eauto.
Qed.
Lemma mval_lookup_ge m w1 w2 r w4 :
  w1 ⊑@{m} w2 → w2 !! r = Some w4 →
  w1 !! r = None ∨ ∃ w3, w1 !! r = Some w3 ∧ w3 ⊑@{m} w4.
Proof.
  revert w1 w2. induction r as [|rs r IH] using rev_ind; simpl.
  * intros. rewrite mval_lookup_nil. simplify_equality. eauto.
  * intros w1 w2. rewrite !mval_lookup_snoc. intros. simplify_option_equality.
    edestruct (mval_lookup_seg_ge m w1 w2 rs) as [?|(?&?&?)];
      simplify_option_equality; eauto.
Qed.
Lemma mval_lookup_seg_freeze rs: lookup (A:=mval Ti Vi) (freeze rs) = lookup rs.
Proof. by destruct rs. Qed.
Lemma mval_lookup_freeze w r : w !! (freeze <$> r) = w !! r.
Proof.
  induction r; simpl.
  * by rewrite mval_lookup_nil.
  * rewrite !mval_lookup_cons, mval_lookup_seg_freeze. congruence.
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

Lemma mval_alter_seg_typed m f w rs τ :
  m ⊢ w : τ →
  (∀ w' σ, τ ∙ rs ↝ σ → m ⊢ w' : σ → m ⊢ f w' : σ) →
  m ⊢ alter f rs w : τ.
Proof.
  intros Hwτ Hf. unfold alter.
  destruct Hwτ using @mtyped_case; destruct rs as [| |i' b];
    try solve [mtyped_constructor; eauto]; simpl; subst.
  * subst. case_decide; subst; mtyped_constructor; eauto.
    + by rewrite alter_length.
    + apply Forall_alter; eauto using RArray_typed.
  * mtyped_constructor; eauto using Forall2_alter_l, RStruct_typed.
  * repeat (case_match || simplify_option_equality); mtyped_constructor;
      eauto using RUnion_typed, mval_new_undef_typed, env_valid_lookup_lookup.
  * repeat (case_match || simplify_option_equality); mtyped_constructor;
      eauto 10 using RUnion_typed, mval_of_bytes_typed,
      env_valid_lookup_lookup, Forall_take.
Qed.
Lemma mval_alter_typed m f w r τ :
  m ⊢ w : τ →
  (∀ w σ, τ ∙ r ↝ σ → m ⊢ w : σ → m ⊢ f w : σ) →
  m ⊢ alter f r w : τ.
Proof.
  revert f w τ. induction r; simpl; intros f w τ Hvτ Hr.
  * apply Hr; by try constructor.
  * rewrite mval_alter_cons. eauto using mval_alter_seg_typed, ref_typed_cons_2.
Qed.

Lemma mval_alter_seg_le m f g w1 w2 rs w3 :
  w1 ⊑@{m} w2 → w1 !! rs = Some w3 →
  (∀ w4, w2 !! rs = Some w4 → f w3 ⊑@{m} g w4) →
  alter f rs w1 ⊑@{m} alter g rs w2.
Proof.
  unfold alter. destruct 1 using @mval_le_case; destruct rs; simpl; intros;
    simplify_equality; try by (mtyped_constructor; eauto).
  * repeat (case_match || simplify_option_equality); mval_le_constructor;
      eauto using Forall2_alter with simplify_option_equality.
    exfalso; eauto using Forall2_length.
  * mval_le_constructor;
      eauto using Forall2_alter with simplify_option_equality.
  * repeat (case_match || simplify_option_equality); mval_le_constructor;
      eauto using Forall2_alter with simplify_option_equality.
  * repeat (case_match || simplify_option_equality); mval_le_constructor;
      eauto using Forall2_alter with simplify_option_equality.
  * repeat (case_match || simplify_option_equality); mval_le_constructor;
      eauto using Forall2_alter with simplify_option_equality.
Qed.
Lemma mval_alter_le m f g w1 w2 r w3 :
  w1 ⊑@{m} w2 → w1 !! r = Some w3 →
  (∀ w4, w2 !! r = Some w4 → f w3 ⊑@{m} g w4) →
  alter f r w1 ⊑@{m} alter g r w2.
Proof.
  revert f g w3 w1 w2. induction r; simpl; intros f g w3 w1 w2 ? Hr Hf.
  * rewrite !mval_alter_nil. rewrite mval_lookup_nil in Hr.
    simplify_equality. eauto.
  * rewrite !mval_alter_cons. rewrite mval_lookup_cons in Hr, Hf.
    simplify_option_equality. edestruct mval_lookup_le as (?&?&?); eauto.
    eauto using mval_alter_seg_le with simplify_option_equality.
Qed.
Lemma mval_lookup_alter_seg m f w rs τ w' :
  m ⊢ w : τ → w !! rs = Some w' → alter f rs w !! rs = Some (f w').
Proof.
  unfold alter. destruct 1 using @mtyped_case; destruct rs;
    simplify_option_equality; try done.
  * intros. rewrite list_lookup_alter. by simplify_option_equality.
  * exfalso. eauto using alter_length.
  * intros. rewrite list_lookup_alter. by simplify_option_equality.
  * congruence.
  * intros. by case_match; simplify_option_equality.
Qed.
Lemma mval_lookup_alter m f w r τ w' :
  m ⊢ w : τ → w !! r = Some w' → alter f r w !! r = Some (f w').
Proof.
  intros Hvτ. revert f τ w Hvτ.
  induction r as [|rs r IH] using rev_ind; intros f τ w Hvτ.
  { rewrite !mval_lookup_nil, mval_alter_nil. congruence. }
  rewrite ?mval_alter_snoc, ?mval_lookup_snoc.
  intro. simplify_option_equality.
  erewrite mval_lookup_alter_seg by eauto. simpl.
  edestruct mval_lookup_seg_Some as [? [??]]; eauto.
Qed.

Lemma mval_lookup_alter_seg_disjoint f w rs1 rs2 :
  rs1 ⊥ rs2 → alter f rs1 w !! rs2 = w !! rs2.
Proof.
  unfold alter. destruct 1; destruct w; simpl; simplify_option_equality;
    auto using list_lookup_alter_ne; exfalso; auto using alter_length.
Qed.
Lemma mval_lookup_alter_disjoint m f w τ r1 r2 w' :
  m ⊢ w : τ → w !! r2 = Some w' → r1 ⊥ r2 → alter f r1 w !! r2 = Some w'.
Proof.
  rewrite ref_disjoint_alt.
  intros Hvτ Hw' (r1'&rs1'&r1''&r2'&rs2'&r2''&?&?&?&Hr). subst.
  revert Hw'. rewrite !mval_alter_app, !mval_lookup_app,
    !mval_alter_singleton, !mval_lookup_singleton.
  rewrite <-!(mval_lookup_freeze _ r2''), <-!Hr, !mval_lookup_freeze.
  intros. simplify_option_equality. erewrite mval_lookup_alter by eauto. simpl.
  rewrite mval_lookup_alter_seg_disjoint by done. by simplify_option_equality.
Qed.
Lemma mval_force_le m w1 w2 r w3 :
  w1 !! r = Some w3 → w1 ⊑@{m} w2 → mval_force r w1 ⊑@{m} mval_force r w2.
Proof.
  intros. destruct (mval_lookup_le m w1 w2 r w3) as (w4&?&?); auto.
  eapply mval_alter_le; eauto. intros. by simplify_option_equality.
Qed.
End mval.
