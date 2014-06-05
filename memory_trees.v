(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export cmap permission_bits.
Local Open Scope ctype_scope.

Notation mtree Ti := (ctree Ti (pbit Ti)).
Notation mem Ti := (cmap Ti (pbit Ti)).

Section operations.
  Context `{IntEnv Ti, PtrEnv Ti}.

  Global Instance type_of_ctree : TypeOf (type Ti) (mtree Ti) := λ w,
    match w with
    | MBase τb _ => baseT τb
    | MArray τ ws => τ.[length ws]
    | MStruct s _ => structT s
    | MUnion s _ _ _ | MUnionAll s _ => unionT s
    end.
  Global Instance cmap_index_alive : IndexAlive (mem Ti) := λ m o,
    ∃ w, cmap_car m !! o = Some w ∧ ¬ctree_Forall (λ xb, pbit_kind xb = None) w.
  Global Instance cmap_type_of_index : TypeOfIndex Ti (mem Ti) := λ m o,
    type_of <$> cmap_car m !! o.

  Inductive ctree_typed' (Γ: env Ti) (m : mem Ti) : mtree Ti → type Ti → Prop :=
    | MBase_typed' τb xbs :
       ✓{Γ} τb → ✓{Γ,m}* xbs → length xbs = bit_size_of Γ (baseT τb) →
       ctree_typed' Γ m (MBase τb xbs) (baseT τb)
    | MArray_typed' τ ws :
       Forall (λ w, ctree_typed' Γ m w τ) ws → length ws ≠ 0 →
       ctree_typed' Γ m (MArray τ ws) (τ.[length ws])
    | MStruct_typed' s wxbss τs :
       Γ !! s = Some τs → Forall2 (ctree_typed' Γ m ∘ fst) wxbss τs →
       ✓{Γ,m}2** wxbss →
       Forall (λ wxbs, pbit_indetify <$> wxbs.2 = wxbs.2) wxbss →
       length ∘ snd <$> wxbss = field_bit_padding Γ τs →
       ctree_typed' Γ m (MStruct s wxbss) (structT s)
    | MUnion_typed' s i τs w xbs τ :
       Γ !! s = Some τs → τs !! i = Some τ → ctree_typed' Γ m w τ →
       ✓{Γ,m}* xbs → pbit_indetify <$> xbs = xbs →
       bit_size_of Γ (unionT s) = bit_size_of Γ τ + length xbs →
       ¬(ctree_unmapped w ∧ Forall sep_unmapped xbs) →
       ctree_typed' Γ m (MUnion s i w xbs) (unionT s)
    | MUnionAll_typed' s τs xbs :
       Γ !! s = Some τs → ✓{Γ,m}* xbs → length xbs = bit_size_of Γ (unionT s) →
       ctree_typed' Γ m (MUnionAll s xbs) (unionT s).
  Global Instance ctree_typed:
    Typed (env Ti * mem Ti) (type Ti) (mtree Ti) := curry ctree_typed'.

  Lemma MBase_typed Γ m τb xbs :
    ✓{Γ} τb → ✓{Γ,m}* xbs →
    length xbs = bit_size_of Γ (baseT τb) → (Γ,m) ⊢ MBase τb xbs : baseT τb.
  Proof. by constructor. Qed.
  Lemma MArray_typed Γ m τ ws n :
    n = length ws → (Γ,m) ⊢* ws : τ → n ≠ 0 → (Γ,m) ⊢ MArray τ ws : τ.[n].
  Proof. intros -> ??. by constructor. Qed.
  Lemma MStruct_typed Γ m s wxbss τs :
    Γ !! s = Some τs → (Γ,m) ⊢1* wxbss :* τs → ✓{Γ,m}2** wxbss →
    Forall (λ wxbs, pbit_indetify <$> wxbs.2 = wxbs.2) wxbss →
    length ∘ snd <$> wxbss = field_bit_padding Γ τs →
    (Γ,m) ⊢ MStruct s wxbss : structT s.
  Proof. econstructor; eauto. Qed.
  Lemma MUnion_typed Γ m s i τs w xbs τ :
    Γ !! s = Some τs → τs !! i = Some τ → (Γ,m) ⊢ w : τ →
    ✓{Γ,m}* xbs → pbit_indetify <$> xbs = xbs →
    bit_size_of Γ (unionT s) = bit_size_of Γ τ + length xbs →
    ¬(ctree_unmapped w ∧ Forall sep_unmapped xbs) →
    (Γ,m) ⊢ MUnion s i w xbs : unionT s.
  Proof. econstructor; eauto. Qed.
  Lemma MUnionAll_typed Γ m s τs xbs :
    Γ !! s = Some τs → ✓{Γ,m}* xbs → length xbs = bit_size_of Γ (unionT s) →
    (Γ,m) ⊢ MUnionAll s xbs : unionT s.
  Proof. econstructor; eauto. Qed.

  Lemma ctree_typed_inv_l Γ m (P : type Ti → Prop) w τ :
    (Γ,m) ⊢ w : τ →
    match w with
    | MBase τb xbs =>
       (✓{Γ} τb → length xbs = bit_size_of Γ (baseT τb) →
         ✓{Γ,m}* xbs → P (baseT τb)) → P τ
    | MArray τ' ws =>
       ((Γ,m) ⊢* ws : τ' → length ws ≠ 0 → P (τ'.[length ws])) → P τ
    | MStruct s wxbss =>
       (∀ τs, Γ !! s = Some τs → (Γ,m) ⊢1* wxbss :* τs → ✓{Γ,m}2** wxbss →
         Forall (λ wxbs, pbit_indetify <$> wxbs.2 = wxbs.2) wxbss →
         length ∘ snd <$> wxbss = field_bit_padding Γ τs → P (structT s)) → P τ
    | MUnion s i w xbs =>
       (∀ τs τ, Γ !! s = Some τs → τs !! i = Some τ → (Γ,m) ⊢ w : τ →
         ✓{Γ,m}* xbs → pbit_indetify <$> xbs = xbs →
         bit_size_of Γ (unionT s) = bit_size_of Γ τ + length xbs →
         ¬(ctree_unmapped w ∧ Forall sep_unmapped xbs) → P (unionT s)) → P τ
    | MUnionAll s xbs =>
       (∀ τs, Γ !! s = Some τs → ✓{Γ,m}* xbs →
         length xbs = bit_size_of Γ (unionT s) → P (unionT s)) → P τ
    end.
  Proof. destruct 1; eauto. Qed.
  Lemma ctree_typed_inv_r Γ m (P : mtree Ti → Prop) w τ :
    (Γ,m) ⊢ w : τ →
    match τ with
    | voidT => P w
    | baseT τb =>
       (∀ xbs, ✓{Γ} τb → length xbs = bit_size_of Γ (baseT τb) →
         ✓{Γ,m}* xbs → P (MBase τb xbs)) → P w
    | τ.[n] =>
       (∀ ws, n = length ws → (Γ,m) ⊢* ws : τ → n ≠ 0 → P (MArray τ ws)) → P w
    | structT s =>
       (∀ wxbss τs, Γ !! s = Some τs → (Γ,m) ⊢1* wxbss :* τs →
         ✓{Γ,m}2** wxbss →
         Forall (λ wxbs, pbit_indetify <$> wxbs.2 = wxbs.2) wxbss →
         length ∘ snd <$> wxbss = field_bit_padding Γ τs →
         P (MStruct s wxbss)) → P w
    | unionT s =>
       (∀ i τs w xbs τ, Γ !! s = Some τs → τs !! i = Some τ → (Γ,m) ⊢ w : τ →
         ✓{Γ,m}* xbs → pbit_indetify <$> xbs = xbs →
         bit_size_of Γ (unionT s) = bit_size_of Γ τ + length xbs →
         ¬(ctree_unmapped w ∧ Forall sep_unmapped xbs) →
         P (MUnion s i w xbs)) →
       (∀ τs xbs, Γ !! s = Some τs → ✓{Γ,m}* xbs →
         length xbs = bit_size_of Γ (unionT s) → P (MUnionAll s xbs)) →
       P w
    end.
  Proof. destruct 1; eauto. Qed.
  Lemma ctree_typed_inv Γ m (P : Prop) w τ :
    (Γ,m) ⊢ w : τ →
    match w, τ with
    | MBase τb xbs, baseT τb' =>
       (τb' = τb → ✓{Γ} τb → length xbs = bit_size_of Γ (baseT τb) →
         ✓{Γ,m}* xbs → P) → P
    | MArray τ' ws, τ''.[n] =>
       (τ'' = τ' → n = length ws → (Γ,m) ⊢* ws : τ' → length ws ≠ 0 → P) → P
    | MStruct s wxbss, structT s' =>
       (∀ τs, s' = s → Γ !! s = Some τs → (Γ,m) ⊢1* wxbss :* τs →
         ✓{Γ,m}2** wxbss →
         Forall (λ wxbs, pbit_indetify <$> wxbs.2 = wxbs.2) wxbss →
         length ∘ snd <$> wxbss = field_bit_padding Γ τs → P) → P
    | MUnion s i w xbs, unionT s' =>
       (∀ τs τ, s' = s → Γ !! s = Some τs → τs !! i = Some τ → (Γ,m) ⊢ w : τ →
         ✓{Γ,m}* xbs → pbit_indetify <$> xbs = xbs →
         bit_size_of Γ (unionT s) = bit_size_of Γ τ + length xbs →
         ¬(ctree_unmapped w ∧ Forall sep_unmapped xbs) → P) → P
    | MUnionAll s xbs, unionT s' =>
       (∀ τs, s' = s → Γ !! s = Some τs → ✓{Γ,m}* xbs →
         length xbs = bit_size_of Γ (unionT s) → P) → P
    | _, _ => P
    end.
  Proof. destruct 1; eauto. Qed.
  Section ctree_typed_ind.
    Context (Γ : env Ti) (m : mem Ti) (P : mtree Ti → type Ti → Prop).
    Context (Pbase : ∀ τb xbs,
      ✓{Γ} τb → ✓{Γ,m}* xbs →
      length xbs = bit_size_of Γ (baseT τb) → P (MBase τb xbs) (baseT τb)).
    Context (Parray : ∀ ws τ,
      (Γ,m) ⊢* ws : τ → Forall (λ w, P w τ) ws →
      length ws ≠ 0 → P (MArray τ ws) (τ.[length ws])).
    Context (Pstruct : ∀ s wxbss τs,
      Γ !! s = Some τs → (Γ,m) ⊢1* wxbss :* τs → Forall2 (P ∘ fst) wxbss τs →
      ✓{Γ,m}2** wxbss →
      Forall (λ wxbs, pbit_indetify <$> wxbs.2 = wxbs.2) wxbss →
      length ∘ snd <$> wxbss = field_bit_padding Γ τs →
      P (MStruct s wxbss) (structT s)).
    Context (Punion : ∀ s i τs w xbs τ,
      Γ !! s = Some τs → τs !! i = Some τ → (Γ,m) ⊢ w : τ → P w τ →
      ✓{Γ,m}* xbs → pbit_indetify <$> xbs = xbs →
      bit_size_of Γ (unionT s) = bit_size_of Γ τ + length xbs →
      ¬(ctree_unmapped w ∧ Forall sep_unmapped xbs) →
      P (MUnion s i w xbs) (unionT s)).
    Context (Punion_all : ∀ s τs xbs,
      Γ !! s = Some τs → ✓{Γ,m}* xbs → length xbs = bit_size_of Γ (unionT s) →
      P (MUnionAll s xbs) (unionT s)).
    Definition ctree_typed_ind : ∀ w τ, ctree_typed' Γ m w τ → P w τ.
    Proof. fix 3; destruct 1; eauto using Forall2_impl, Forall_impl. Qed.
  End ctree_typed_ind.
  Section ctree_typed_case.
    Context (Γ : env Ti) (m : mem Ti) (P : mtree Ti → type Ti → Prop).
    Context (Pbase : ∀ τb xbs,
      ✓{Γ} τb → ✓{Γ,m}* xbs →
      length xbs = bit_size_of Γ (baseT τb) → P (MBase τb xbs) (baseT τb)).
    Context (Parray : ∀ ws τ,
      (Γ,m) ⊢* ws : τ → length ws ≠ 0 → P (MArray τ ws) (τ.[length ws])).
    Context (Pstruct : ∀ s wxbss τs,
      Γ !! s = Some τs → (Γ,m) ⊢1* wxbss :* τs → ✓{Γ,m}2** wxbss →
      Forall (λ wxbs, pbit_indetify <$> wxbs.2 = wxbs.2) wxbss →
      length ∘ snd <$> wxbss = field_bit_padding Γ τs →
      P (MStruct s wxbss) (structT s)).
    Context (Punion : ∀ s i τs w xbs τ,
      Γ !! s = Some τs → τs !! i = Some τ → (Γ,m) ⊢ w : τ →
      ✓{Γ,m}* xbs → pbit_indetify <$> xbs = xbs →
      bit_size_of Γ (unionT s) = bit_size_of Γ τ + length xbs →
      ¬(ctree_unmapped w ∧ Forall sep_unmapped xbs) →
      P (MUnion s i w xbs) (unionT s)).
    Context (Punion_all : ∀ s τs xbs,
      Γ !! s = Some τs → ✓{Γ,m}* xbs → length xbs = bit_size_of Γ (unionT s) →
      P (MUnionAll s xbs) (unionT s)).
    Lemma ctree_typed_case : ∀ w τ, ctree_typed' Γ m w τ → P w τ.
    Proof. destruct 1; eauto. Qed.
  End ctree_typed_case.

  Global Instance mval_check:TypeCheck (env Ti * mem Ti) (type Ti) (mtree Ti) :=
    fix go Γm w {struct w} := let _ : TypeCheck _ _ _ := @go in
    match w with
    | MBase τb xbs =>
       guard (✓{Γm.1} τb);
       guard (✓{Γm}* xbs);
       guard (length xbs = bit_size_of (Γm.1) (baseT τb));
       Some (baseT τb)
    | MArray τ ws =>
       τs ← mapM (type_check Γm) ws;
       guard (length ws ≠ 0);
       guard (Forall (τ =) τs);
       Some (τ.[length ws])
    | MStruct s wxbss =>
       τs ← Γm.1 !! s;
       τs' ← mapM (type_check Γm ∘ fst) wxbss;
       guard (τs' = τs);
       guard (✓{Γm}2** wxbss);
       guard (Forall (λ wxbs, pbit_indetify <$> wxbs.2 = wxbs.2) wxbss);
       guard (length ∘ snd <$> wxbss = field_bit_padding (Γm.1) τs);
       Some (structT s)
    | MUnion s i w xbs =>
       τ ← Γm.1 !! s ≫= (!! i);
       τ' ← type_check Γm w;
       guard (τ' = τ);
       guard (✓{Γm}* xbs);
       guard (pbit_indetify <$> xbs = xbs);
       guard (bit_size_of (Γm.1) (unionT s)
         = bit_size_of (Γm.1) τ + length xbs);
       guard (¬(ctree_unmapped w ∧ Forall sep_unmapped xbs));
       Some (unionT s)
    | MUnionAll s xbs =>
       τs ← Γm.1 !! s;
       guard (✓{Γm}* xbs);
       guard (length xbs = bit_size_of (Γm.1) (unionT s));
       Some (unionT s)
    end.

  Inductive union_free : mtree Ti → Prop :=
    | MBase_union_free τb xbs : union_free (MBase τb xbs)
    | MArray_union_free τ ws : Forall union_free ws → union_free (MArray τ ws)
    | MStruct_union_free s wxbss :
       Forall (union_free ∘ fst) wxbss → union_free (MStruct s wxbss)
    | MUnionAll_union_free s xbs : union_free (MUnionAll s xbs).
  Definition union_reset : mtree Ti → mtree Ti :=
    fix go w :=
    match w with
    | MBase τb xbs => MBase τb xbs
    | MArray τ ws => MArray τ (go <$> ws)
    | MStruct s wxbss => MStruct s (prod_map go id <$> wxbss)
    | MUnion s i w xbs => MUnionAll s (ctree_flatten w ++ xbs)
    | MUnionAll s xbs => MUnionAll s xbs
    end.
  Section union_free_ind.
    Context (P : mtree Ti → Prop).
    Context (Pbase : ∀ τ xbs, P (MBase τ xbs)).
    Context (Parray : ∀ τ ws,
      Forall union_free ws → Forall P ws → P (MArray τ ws)).
    Context (Pstruct : ∀ s wxbss,
      Forall (union_free ∘ fst) wxbss → Forall (P ∘ fst) wxbss →
      P (MStruct s wxbss)).
    Context (Punion_bits : ∀ s xbs, P (MUnionAll s xbs)).
    Definition union_free_ind_alt: ∀ w, union_free w → P w.
    Proof. fix 2; destruct 1; eauto using Forall_impl. Qed.
  End union_free_ind.
  Global Instance union_free_dec: ∀ w : mtree Ti, Decision (union_free w).
  Proof.
   refine (
    fix go w :=
    match w return Decision (union_free w) with
    | MBase _ _ => left _
    | MArray _ ws => cast_if (decide (Forall union_free ws))
    | MStruct _ wxbss => cast_if (decide (Forall (union_free ∘ fst) wxbss))
    | MUnion _ _ _ _ => right _
    | MUnionAll _ _ => left _
    end); clear go; abstract first [by constructor | by inversion 1].
  Defined.

  Definition array_unflatten {A B} (Γ : env Ti) (f : list A → B)
      (τ : type Ti) : nat → list A → list B :=
    let sz := bit_size_of Γ τ in fix go n bs :=
    match n with 0 => [] | S n => f (take sz bs) :: go n (drop sz bs) end.
  Definition struct_unflatten_aux {A B}
      (f : type Ti → list A → B) : list (nat * type Ti) → list A → list B :=
    fix go τs bs :=
    match τs with
    | [] => [] | (sz,τ) :: τs => f τ (take sz bs) :: go τs (drop sz bs)
    end.
  Definition struct_unflatten {A B} (Γ : env Ti)
      (f : type Ti → list A → B) (τs : list (type Ti)) : list A → list B :=
    struct_unflatten_aux f (zip (field_bit_sizes Γ τs) τs).
  Definition ctree_unflatten (Γ : env Ti) :
      type Ti → list (pbit Ti) → mtree Ti := type_iter
    (**i TBase =>     *) (λ τb xbs, MBase τb xbs)
    (**i TVoid =>     *) (λ xbs, MBase ucharT []) (* dummy *)
    (**i TArray =>    *) (λ τ n go xbs, MArray τ (array_unflatten Γ go τ n xbs))
    (**i TCompound => *) (λ c s τs go xbs,
      match c with
      | Struct_kind =>
         MStruct s (struct_unflatten Γ (λ τ xbs,
           let τsz := bit_size_of Γ τ
           in (go τ (take τsz xbs), pbit_indetify <$> drop τsz xbs)
         ) τs xbs)
      | Union_kind => MUnionAll s xbs
      end) Γ.

  Definition ctree_new (Γ : env Ti) (xb : pbit Ti) : type Ti → mtree Ti :=
    type_iter
    (**i TBase     *) (λ τb, MBase τb (replicate (bit_size_of Γ τb) xb))
    (**i TVoid     *) (MBase ucharT []) (* dummy *)
    (**i TArray    *) (λ τ n x, MArray τ (replicate n x))
    (**i TCompound *) (λ c s τs go,
      match c with
      | Struct_kind => MStruct s (zip (go <$> τs)
         (flip replicate (pbit_indetify xb) <$> field_bit_padding Γ τs))
      | Union_kind => MUnionAll s (replicate (bit_size_of Γ (unionT s)) xb)
      end) Γ.

  Global Instance ctree_lookup_seg:
      LookupE (env Ti) (ref_seg Ti) (mtree Ti) (mtree Ti) := λ Γ rs w,
    match rs, w with
    | RArray i τ n, MArray τ' ws =>
       guard (n = length ws); guard (τ = τ'); ws !! i
    | RStruct i s, MStruct s' wxbss => guard (s = s'); fst <$> wxbss !! i
    | RUnion i s β, MUnion s' j w xbs =>
       guard (s = s');
       if decide (i = j) then Some w else
       guard (β = false);
       τ ← Γ !! s ≫= (!! i);
       guard (ctree_unshared w);
       guard (Forall sep_unshared xbs);
       let xbs' := ctree_flatten w ++ xbs in
       Some (ctree_unflatten Γ τ (take (bit_size_of Γ τ) xbs'))
    | RUnion i s _, MUnionAll s' xbs =>
       guard (s = s'); 
       τ ← Γ !! s ≫= (!! i);
       guard (Forall sep_unshared xbs);
       Some (ctree_unflatten Γ τ (take (bit_size_of Γ τ) xbs))
    | _, _ => None
    end.

  Definition ctree_alter_seg (Γ : env Ti) (g : mtree Ti → mtree Ti)
      (rs : ref_seg Ti) (w : mtree Ti) : mtree Ti :=
    match rs, w with
    | RArray i _ _, MArray τ ws => MArray τ (alter g i ws)
    | RStruct i _, MStruct s wxbss => MStruct s (alter (prod_map g id) i wxbss)
    | RUnion i _ _, MUnion s j w' xbs' =>
       if decide (i = j) then MUnion s i (g w') xbs'
       else default w (Γ !! s ≫= (!! i)) $ λ τ,
         let xbs := ctree_flatten w' ++ xbs' in
         MUnion s i (g (ctree_unflatten Γ τ (take (bit_size_of Γ τ) xbs)))
                    (pbit_indetify <$> drop (bit_size_of Γ τ) xbs)
    | RUnion i _ _, MUnionAll s xbs => default w (Γ !! s ≫= (!! i)) $ λ τ,
       MUnion s i (g (ctree_unflatten Γ τ (take (bit_size_of Γ τ) xbs)))
                  (pbit_indetify <$> drop (bit_size_of Γ τ) xbs)
    | _, _ => w
    end.
  Fixpoint ctree_alter (Γ : env Ti) (g : mtree Ti → mtree Ti)
      (r : ref Ti) : mtree Ti → mtree Ti :=
    match r with
    | [] => g | rs :: r => ctree_alter Γ (ctree_alter_seg Γ g rs) r
    end.

  Global Instance ctree_lookup_byte:
      LookupE (env Ti) nat (mtree Ti) (mtree Ti) :=
    λ Γ i w, ctree_unflatten Γ ucharT <$>
      sublist_lookup (i * char_bits) char_bits (ctree_flatten w).
  Definition ctree_alter_byte (Γ : env Ti) (f : mtree Ti → mtree Ti)
      (i : nat) (w : mtree Ti) : mtree Ti :=
    ctree_unflatten Γ (type_of w) $
      sublist_alter (ctree_flatten ∘ f ∘ ctree_unflatten Γ ucharT)
                    (i * char_bits) char_bits (ctree_flatten w).

  Inductive ctree_refine' (Γ : env Ti) (f : mem_inj Ti) (m1 m2 : mem Ti) :
       mtree Ti → mtree Ti → type Ti → Prop :=
    | MBase_refine' τb xbs1 xbs2 :
       ✓{Γ} τb → xbs1 ⊑{Γ,f@m1↦m2}* xbs2 →
       length xbs1 = bit_size_of Γ (baseT τb) →
       ctree_refine' Γ f m1 m2 (MBase τb xbs1) (MBase τb xbs2) (baseT τb)
    | MArray_refine' τ n ws1 ws2 :
       n = length ws1 →
       Forall2 (λ w1 w2, ctree_refine' Γ f m1 m2 w1 w2 τ) ws1 ws2 →
       n ≠ 0 → ctree_refine' Γ f m1 m2 (MArray τ ws1) (MArray τ ws2) (τ.[n])
    | MStruct_refine' s wxbss1 wxbss2 τs :
       Γ !! s = Some τs → Forall3 (λ wxbs1 wxbs2 τ,
         ctree_refine' Γ f m1 m2 (wxbs1.1) (wxbs2.1) τ) wxbss1 wxbss2 τs →
       wxbss1 ⊑{Γ,f@m1↦m2}2** wxbss2 →
       Forall (λ wxbs, pbit_indetify <$> wxbs.2 = wxbs.2) wxbss2 →
       length ∘ snd <$> wxbss1 = field_bit_padding Γ τs →
       ctree_refine' Γ f m1 m2 (MStruct s wxbss1) (MStruct s wxbss2) (structT s)
    | MUnion_refine' s τs i w1 w2 xbs1 xbs2 τ :
       Γ !! s = Some τs → τs !! i = Some τ → ctree_refine' Γ f m1 m2 w1 w2 τ →
       xbs1 ⊑{Γ,f@m1↦m2}* xbs2 → pbit_indetify <$> xbs2 = xbs2 →
       bit_size_of Γ (unionT s) = bit_size_of Γ τ + length xbs1 →
       ¬(ctree_unmapped w1 ∧ Forall sep_unmapped xbs1) →
       ctree_refine' Γ f m1 m2
         (MUnion s i w1 xbs1) (MUnion s i w2 xbs2) (unionT s)
    | MUnionAll_refine' s τs xbs1 xbs2 :
       Γ !! s = Some τs → xbs1 ⊑{Γ,f@m1↦m2}* xbs2 →
       length xbs1 = bit_size_of Γ (unionT s) →
       ctree_refine' Γ f m1 m2 (MUnionAll s xbs1) (MUnionAll s xbs2) (unionT s)
    | MUnion_MUnionAll_refine' s τs i w1 xbs1 xbs2 τ :
       Γ !! s = Some τs → τs !! i = Some τ →
       ctree_flatten w1 ++ xbs1 ⊑{Γ,f@m1↦m2}* xbs2 →
       pbit_indetify <$> xbs1 = xbs1 →
       (Γ,m1) ⊢ w1 : τ → Forall sep_unshared xbs2 →
       bit_size_of Γ (unionT s) = bit_size_of Γ τ + length xbs1 →
       ¬(ctree_unmapped w1 ∧ Forall sep_unmapped xbs1) →
       ctree_refine' Γ f m1 m2
         (MUnion s i w1 xbs1) (MUnionAll s xbs2) (unionT s).
  Global Instance ctree_refine:
    RefineT Ti (mem Ti) (mtree Ti) (type Ti) := ctree_refine'.

  Lemma MBase_refine Γ f m1 m2 τb xbs1 xbs2 :
    ✓{Γ} τb → xbs1 ⊑{Γ,f@m1↦m2}* xbs2 →
    length xbs1 = bit_size_of Γ (baseT τb) →
    MBase τb xbs1 ⊑{Γ,f@m1↦m2} MBase τb xbs2 : baseT τb.
  Proof. by constructor. Qed.
  Lemma MArray_refine Γ f m1 m2 τ n ws1 ws2 :
    n = length ws1 → ws1 ⊑{Γ,f@m1↦m2}* ws2 : τ → n ≠ 0 →
    MArray τ ws1 ⊑{Γ,f@m1↦m2} MArray τ ws2 : τ.[n].
  Proof. by constructor. Qed.
  Lemma MStruct_refine Γ f m1 m2 s τs (wxbss1 wxbss2 : list (_ * list _)) :
    Γ !! s = Some τs →
    wxbss1 ⊑{Γ,f@m1↦m2}1* wxbss2 :* τs → wxbss1 ⊑{Γ,f@m1↦m2}2** wxbss2 →
    Forall (λ wxbs, pbit_indetify <$> wxbs.2 = wxbs.2) wxbss2 →
    length ∘ snd <$> wxbss1 = field_bit_padding Γ τs →
    MStruct s wxbss1 ⊑{Γ,f@m1↦m2} MStruct s wxbss2 : structT s.
  Proof. econstructor; eauto. Qed.
  Lemma MUnion_refine Γ f m1 m2 s τs i w1 w2 xbs1 xbs2 τ :
    Γ !! s = Some τs → τs !! i = Some τ → w1 ⊑{Γ,f@m1↦m2} w2 : τ →
    xbs1 ⊑{Γ,f@m1↦m2}* xbs2 → pbit_indetify <$> xbs2 = xbs2 →
    bit_size_of Γ (unionT s) = bit_size_of Γ τ + length xbs1 →
    ¬(ctree_unmapped w1 ∧ Forall sep_unmapped xbs1) →
    MUnion s i w1 xbs1 ⊑{Γ,f@m1↦m2} MUnion s i w2 xbs2 : unionT s.
  Proof. econstructor; eauto. Qed.
  Lemma MUnionAll_refine Γ f m1 m2 s τs xbs1 xbs2 :
    Γ !! s = Some τs → xbs1 ⊑{Γ,f@m1↦m2}* xbs2 →
    length xbs1 = bit_size_of Γ (unionT s) →
    MUnionAll s xbs1 ⊑{Γ,f@m1↦m2} MUnionAll s xbs2 : unionT s.
  Proof. econstructor; eauto. Qed.
  Lemma MUnion_MUnionAll_refine Γ f m1 m2 s i τs w1 xbs1 xbs2 τ :
    Γ !! s = Some τs → τs !! i = Some τ →
    ctree_flatten w1 ++ xbs1 ⊑{Γ,f@m1↦m2}* xbs2 →
    pbit_indetify <$> xbs1 = xbs1 →
    (Γ,m1) ⊢ w1 : τ → Forall sep_unshared xbs2 →
    bit_size_of Γ (unionT s) = bit_size_of Γ τ + length xbs1 →
    ¬(ctree_unmapped w1 ∧ Forall sep_unmapped xbs1) →
    MUnion s i w1 xbs1 ⊑{Γ,f@m1↦m2} MUnionAll s xbs2 : unionT s.
  Proof. econstructor; eauto. Qed.

  Lemma ctree_refine_inv_l (Γ : env Ti)
      (f : mem_inj Ti) (m1 m2 : mem Ti) (P : mtree Ti → Prop) w1 w2 τ :
    w1 ⊑{Γ,f@m1↦m2} w2 : τ →
    match w1 with
    | MBase τb xbs1 =>
       (∀ xbs2, xbs1 ⊑{Γ,f@m1↦m2}* xbs2 → P (MBase τb xbs2)) → P w2
    | MArray τ ws1 =>
       (∀ ws2, ws1 ⊑{Γ,f@m1↦m2}* ws2 : τ → P (MArray τ ws2)) → P w2
    | MStruct s wxbss1 => (∀ τs wxbss2,
       Γ !! s = Some τs → wxbss1 ⊑{Γ,f@m1↦m2}1* wxbss2 :* τs →
       Forall (λ wxbs, pbit_indetify <$> wxbs.2 = wxbs.2) wxbss2 →
       wxbss1 ⊑{Γ,f@m1↦m2}2** wxbss2 → P (MStruct s wxbss2)) → P w2
    | MUnion s i w1 xbs1 =>
       (∀ τs w2 xbs2 τ,
         Γ !! s = Some τs → τs !! i = Some τ → w1 ⊑{Γ,f@m1↦m2} w2 : τ →
         xbs1 ⊑{Γ,f@m1↦m2}* xbs2 → pbit_indetify <$> xbs2 = xbs2 →
         P (MUnion s i w2 xbs2)) →
       (∀ τs τ xbs2,
         Γ !! s = Some τs → τs !! i = Some τ →
         ctree_flatten w1 ++ xbs1 ⊑{Γ,f@m1↦m2}* xbs2 →
         Forall sep_unshared xbs2 → P (MUnionAll s xbs2)) → P w2
    | MUnionAll s xbs1 =>
       (∀ xbs2, xbs1 ⊑{Γ,f@m1↦m2}* xbs2 → P (MUnionAll s xbs2)) → P w2
    end.
  Proof. destruct 1; eauto. Qed.

  Section ctree_refine_ind.
    Context (Γ : env Ti) (f : mem_inj Ti) (m1 m2 : mem Ti).
    Context (P : mtree Ti → mtree Ti → type Ti → Prop).
    Context (Pbase : ∀ τb xbs1 xbs2,
      ✓{Γ} τb → xbs1 ⊑{Γ,f@m1↦m2}* xbs2 →
      length xbs1 = bit_size_of Γ (baseT τb) →
      P (MBase τb xbs1) (MBase τb xbs2) (baseT τb)).
    Context (Parray : ∀ τ n ws1 ws2,
      n = length ws1 → ws1 ⊑{Γ,f@m1↦m2}* ws2 : τ →
      Forall2 (λ w1 w2, P w1 w2 τ) ws1 ws2 →
      n ≠ 0 → P (MArray τ ws1) (MArray τ ws2) (τ.[n])).
    Context (Pstruct : ∀ s τs wxbss1 wxbss2,
      Γ !! s = Some τs → wxbss1 ⊑{Γ,f@m1↦m2}1* wxbss2 :* τs →
      Forall3 (λ wxbs1 wxbs2 τ, P (wxbs1.1) (wxbs2.1) τ) wxbss1 wxbss2 τs →
      wxbss1 ⊑{Γ,f@m1↦m2}2** wxbss2 →
      Forall (λ wxbs, pbit_indetify <$> wxbs.2 = wxbs.2) wxbss2 →
      length ∘ snd <$> wxbss1 = field_bit_padding Γ τs →
      P (MStruct s wxbss1) (MStruct s wxbss2) (structT s)).
    Context (Punion : ∀ s τs i w1 w2 xbs1 xbs2 τ,
      Γ !! s = Some τs → τs !! i = Some τ → w1 ⊑{Γ,f@m1↦m2} w2 : τ → P w1 w2 τ →
      xbs1 ⊑{Γ,f@m1↦m2}* xbs2 → pbit_indetify <$> xbs2 = xbs2 →
      bit_size_of Γ (unionT s) = bit_size_of Γ τ + length xbs1 →
      ¬(ctree_unmapped w1 ∧ Forall sep_unmapped xbs1) →
      P (MUnion s i w1 xbs1) (MUnion s i w2 xbs2) (unionT s)).
    Context (Punion_all : ∀ s τs xbs1 xbs2,
      Γ !! s = Some τs → xbs1 ⊑{Γ,f@m1↦m2}* xbs2 →
      length xbs1 = bit_size_of Γ (unionT s) →
      P (MUnionAll s xbs1) (MUnionAll s xbs2) (unionT s)).
    Context (Punion_union_all : ∀ s i τs w1 xbs1 xbs2 τ,
      Γ !! s = Some τs → τs !! i = Some τ →
      ctree_flatten w1 ++ xbs1 ⊑{Γ,f@m1↦m2}* xbs2 →
      pbit_indetify <$> xbs1 = xbs1 →
      (Γ,m1) ⊢ w1 : τ → Forall sep_unshared xbs2 →
      bit_size_of Γ (unionT s) = bit_size_of Γ τ + length xbs1 →
      ¬(ctree_unmapped w1 ∧ Forall sep_unmapped xbs1) →
      P (MUnion s i w1 xbs1) (MUnionAll s xbs2) (unionT s)).
    Definition ctree_refine_ind: ∀ w1 w2 τ,
      ctree_refine' Γ f m1 m2 w1 w2 τ → P w1 w2 τ.
    Proof. fix 4; destruct 1; eauto using Forall2_impl, Forall3_impl. Qed.
  End ctree_refine_ind.
End operations.

Ltac ctree_typed_constructor := first
  [ eapply MBase_typed | eapply MArray_typed | eapply MStruct_typed
  | eapply MUnion_typed | eapply MUnionAll_typed ].
Ltac ctree_refine_constructor := first [ eapply MBase_refine
  | eapply MArray_refine | eapply MStruct_refine | eapply MUnion_refine
  | eapply MUnionAll_refine | eapply MUnion_MUnionAll_refine ].

Section ctree.
Context `{EnvSpec Ti}.

Implicit Types Γ : env Ti.
Implicit Types m : mem Ti.
Implicit Types τb : base_type Ti.
Implicit Types τ σ : type Ti.
Implicit Types τs σs : list (type Ti).
Implicit Types o : index.
Implicit Types xb : pbit Ti.
Implicit Types xbs : list (pbit Ti).
Implicit Types w : mtree Ti.
Implicit Types ws : list (mtree Ti).
Implicit Types wxbs : mtree Ti * list (pbit Ti).
Implicit Types wxbss : list (mtree Ti * list (pbit Ti)).
Implicit Types rs : ref_seg Ti.
Implicit Types r : ref Ti.
Implicit Types f : mem_inj Ti.
Implicit Types g : mtree Ti → mtree Ti.

Local Arguments union _ _ !_ !_ /.
Hint Resolve Forall_take Forall_drop Forall_app_2 Forall_replicate.
Hint Resolve Forall2_take Forall2_drop Forall2_app.
Hint Immediate env_valid_lookup env_valid_lookup_lookup.
Hint Extern 0 (Separation _) => apply (_ : Separation (pbit Ti)).

(** ** General properties of the typing judgment *)
Lemma ctree_typed_type_valid Γ m w τ : (Γ,m) ⊢ w : τ → ✓{Γ} τ.
Proof.
  induction 1 using @ctree_typed_ind; econstructor; decompose_Forall_hyps;
    try match goal with
    | H : length ?ws ≠ 0, H2 : Forall _ ?ws |- _ => destruct H2; [done|]
    end; eauto.
Qed.
Hint Immediate ctree_typed_type_valid.
Global Instance: TypeOfSpec (env Ti * mem Ti) (type Ti) (mtree Ti).
Proof.
  intros [Γ mm]. induction 1 using @ctree_typed_ind; decompose_Forall_hyps;
    try match goal with
    | H : length ?ws ≠ 0, H2 : Forall _ ?ws |- _ => destruct H2; [done|]
    end; simpl; eauto with f_equal.
Qed.
Local Arguments type_check _ _ _ _ _ !_ /.
Global Instance:
  TypeCheckSpec (env Ti * mem Ti) (type Ti) (mtree Ti) (λ _, True).
Proof.
  intros [Γ m]. assert (∀ ws τs,
    Forall (λ w, ∀ τ, type_check (Γ,m) w = Some τ → (Γ,m) ⊢ w : τ) ws →
    Forall2 (λ w τ, type_check (Γ,m) w = Some τ) ws τs →
    (Γ,m) ⊢* ws :* τs) by (intros; decompose_Forall; eauto).
  assert (∀ ws τ,
    (Γ,m) ⊢* ws : τ → Forall (λ w, type_check (Γ,m) w = Some τ) ws →
    mapM (type_check (Γ,m)) ws = Some (replicate (length ws) τ)).
  { intros. apply mapM_Some,Forall2_replicate_r; decompose_Forall_hyps; eauto. }
  intros w τ _. split.
  * revert τ. induction w using @ctree_ind_alt; intros;
      repeat (progress simplify_option_equality || case_match);
      repeat match goal with
      | H : mapM _ _ = Some _ |- _ => apply mapM_Some_1 in H
      end; ctree_typed_constructor;
      eauto using Forall2_Forall_typed; decompose_Forall; eauto.
  * by induction 1 using @ctree_typed_ind;
      repeat (simplify_option_equality || case_match
        || decompose_Forall_hyps || erewrite ?mapM_Some_2 by eauto);
      repeat match goal with
      | H : ¬Forall _ (replicate _ _) |- _ =>
        by destruct H; apply Forall_replicate_eq
      end.
Qed.
Lemma ctree_typed_weaken Γ1 Γ2 m1 m2 w τ :
  ✓ Γ1 → (Γ1,m1) ⊢ w : τ → Γ1 ⊆ Γ2 →
  (∀ o σ, type_of_index m1 o = Some σ → type_of_index m2 o = Some σ) →
  (Γ2,m2) ⊢ w : τ.
Proof.
  intros ? Hw ??. induction Hw using @ctree_typed_ind; ctree_typed_constructor;
    eauto using base_type_valid_weaken,
      lookup_weaken, Forall_impl, pbit_valid_weaken;
    by erewrite <-?(bit_size_of_weaken Γ1 Γ2), <-?(field_bit_padding_weaken Γ1 Γ2)
      by eauto using TBase_valid, TCompound_valid.
Qed.
Lemma ctree_typed_sep_valid Γ m w τ : (Γ,m) ⊢ w : τ → ctree_valid w.
Proof.
  induction 1 using @ctree_typed_ind; constructor; eauto using Forall_impl,
    Forall2_Forall_l, Forall_true, pbit_valid_sep_valid.
Qed.

(** ** Properties of the [ctree_flatten] function *)
Lemma ctree_flatten_length Γ m w τ :
  ✓ Γ → (Γ,m) ⊢ w : τ → length (ctree_flatten w) = bit_size_of Γ τ.
Proof.
  intros HΓ. revert w τ. refine (ctree_typed_ind _ _ _ _ _ _ _ _); simpl.
  * done.
  * intros ws τ _ IH _; simpl. rewrite bit_size_of_array.
    induction IH; simpl; rewrite ?app_length; f_equal; auto.
  * intros s wxbss τs Hs _ IH _ _ Hxbss; erewrite bit_size_of_struct by eauto.
    clear Hs. revert wxbss Hxbss IH. unfold field_bit_padding.
    induction (bit_size_of_fields _ τs HΓ); intros [|??] ??;
      decompose_Forall_hyps'; rewrite ?app_length; f_equal; auto with lia.
  * intros s i τs w xbs τ ?? _ <- _ _ ? _. by rewrite app_length.
  * done.
Qed.
Lemma ctree_flatten_valid Γ m w τ :
  ✓ Γ → (Γ,m) ⊢ w : τ → ✓{Γ,m}* (ctree_flatten w).
Proof.
  intros HΓ. revert w τ.
  refine (ctree_typed_ind _ _ _ _ _ _ _ _); simpl; auto 2.
  * intros ws τ _ IH _. induction IH; simpl; decompose_Forall_hyps; auto.
  * intros s wxbss τs _ _ IH ? _ _. induction IH; decompose_Forall_hyps'; auto.
Qed.
Lemma ctree_flatten_union_reset w :
  ctree_flatten (union_reset w) = ctree_flatten w.
Proof.
  induction w as [| |s wxbss IH| |] using @ctree_ind_alt; simpl;
    rewrite ?list_fmap_bind; auto using Forall_bind_ext.
  induction IH; f_equal'; auto with f_equal.
Qed.
Lemma ctree_Forall_not P Γ m w τ :
  ✓ Γ → (Γ,m) ⊢ w : τ → ctree_Forall (not ∘ P) w → ¬ctree_Forall P w.
Proof.
  intros ??. apply Forall_not.
  erewrite ctree_flatten_length by eauto. eauto using bit_size_of_ne_0.
Qed.
Lemma ctree_typed_subseteq Γ m w1 w2 τ :
  ✓ Γ → (∀ x1 x2, ✓{Γ,m} x2 → x1 ⊆ x2 → ✓{Γ,m} x1) →
  (Γ,m) ⊢ w2 : τ → w1 ⊆ w2 → (Γ,m) ⊢ w1 : τ.
Proof.
  intros ?? Hw2 Hw. revert w1 w2 Hw τ Hw2. assert (∀ xbs1 xbs2,
    ✓{Γ,m}* xbs2 → xbs1 ⊆* xbs2 → ✓{Γ,m}* xbs1).
  { induction 2; decompose_Forall_hyps; eauto. }
  refine (ctree_subseteq_ind_alt _ _ _ _ _ _ _).
  * intros τb xbs1 xbs2 ?? Hw2; apply (ctree_typed_inv_l _ _ _ _ _ Hw2).
    intros. ctree_typed_constructor; eauto using Forall2_length_r.
  * intros τ ws1 ws2 _ IH τ' Hw2;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw2); clear τ' Hw2.
    intros ? Hle; ctree_typed_constructor; eauto using Forall2_length, eq_sym.
    clear Hle. induction IH; decompose_Forall_hyps; auto.
  * intros s wxbss1 wxbss2 _ IH Hxbss τ Hw2;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw2); clear τ Hw2.
    intros τs Hs Hws2 Hxbss2 Hindet Hlen. ctree_typed_constructor; eauto.
    + clear Hxbss Hs Hxbss2 Hlen. revert τs Hws2.
      induction IH; intros; decompose_Forall_hyps'; auto.
    + clear IH Hws2 Hlen. induction Hxbss; decompose_Forall_hyps; eauto.
    + clear Hlen Hws2 IH Hxbss2. induction Hxbss; decompose_Forall_hyps';
        constructor; eauto using pbits_indetified_subseteq.
    + rewrite <-Hlen. clear IH Hws2 Hxbss2 Hlen Hindet.
      induction Hxbss; f_equal'; eauto using Forall2_length.
  * intros s i w1 w2 xbs1 xbs2 ? IH ? Hmap τ Hw2;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw2); clear τ Hw2.
    intros. ctree_typed_constructor; eauto.
    + eauto using pbits_indetified_subseteq.
    + by erewrite Forall2_length by eauto.
  * intros s xbs1 xbs2 ?? Hw2; apply (ctree_typed_inv_l _ _ _ _ _ Hw2).
    intros. ctree_typed_constructor; eauto using Forall2_length_r.
  * intros s i xbs1 w2 xbs2 ??? Hmap τ Hw2;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw2); clear τ Hw2.
    intros τs τ ???????. ctree_typed_constructor; eauto 1.
    + eauto using ctree_flatten_valid.
    + by erewrite Forall2_length, app_length, ctree_flatten_length by eauto.
Qed.

(** ** Properties of the [union_reset] function *)
Lemma union_free_base Γ m w τb : (Γ,m) ⊢ w : baseT τb → union_free w.
Proof. inversion 1; constructor. Qed.
Lemma union_reset_typed Γ m w τ :
  ✓ Γ → (Γ,m) ⊢ w : τ → (Γ,m) ⊢ union_reset w : τ.
Proof.
  intros HΓ. revert w τ. refine (ctree_typed_ind _ _ _ _ _ _ _ _); simpl.
  * by ctree_typed_constructor.
  * intros ws τ Hws IH; ctree_typed_constructor; auto.
    + by rewrite fmap_length.
    + induction IH; decompose_Forall_hyps'; auto.
  * intros s wxbss τs Hs Hws IH ? Hindet Hlen; ctree_typed_constructor; eauto.
    + clear Hs Hlen Hindet. induction IH; decompose_Forall_hyps'; auto.
    + clear Hindet. eapply Forall_fmap, Forall_impl; eauto.
    + elim Hindet; intros; constructor; simpl; auto.
    + rewrite <-Hlen, <-list_fmap_compose. by apply list_fmap_ext.
  * intros s i τs w xbs τ ??????? Hemp; simpl. ctree_typed_constructor; eauto.
    + eauto using ctree_flatten_valid.
    + by erewrite app_length, ctree_flatten_length by eauto.
  * ctree_typed_constructor.
Qed.
Lemma union_free_reset w : union_free w → union_reset w = w.
Proof.
  induction 1 as [|? ws _ IH|s wxbss _ IH|]
    using @union_free_ind_alt; f_equal'; auto.
  * by induction IH; f_equal'.
  * induction IH as [|[]]; f_equal'; auto with f_equal.
Qed.
Lemma union_reset_free w : union_free (union_reset w).
Proof.
  by induction w as [|ws IH|s wxbss IH| |]
    using ctree_ind_alt; simpl; constructor; apply Forall_fmap.
Qed.
Lemma union_free_unmapped w :
  ctree_valid w → ctree_Forall sep_unmapped w → union_free w.
Proof.
  induction 1 as [|? ws ? IH|? wxss ? IH| |] using @ctree_valid_ind_alt;
    intros; decompose_Forall_hyps'; try constructor.
  * induction IH; decompose_Forall_hyps'; auto.
  * induction IH; decompose_Forall_hyps'; auto.
  * tauto.
Qed.

(** ** The [type_mask] function *)
Definition type_mask (Γ : env Ti) : type Ti → list bool := type_iter
  (**i TBase =>  *) (λ τb, replicate (bit_size_of Γ τb) false)
  (**i TVoid =>     *) [] (* dummy *)
  (**i TArray =>    *) (λ _ n go, mjoin (replicate n go))
  (**i TCompound => *) (λ c s τs go,
    match c with
    | Struct_kind =>
       let τszs := field_bit_sizes Γ τs in
       mjoin (zip_with (λ τ sz, resize sz true (go τ)) τs τszs)
    | Union_kind => replicate (bit_size_of Γ (unionT s)) false
   end) Γ.
Lemma type_mask_base Γ τb : type_mask Γ τb = replicate (bit_size_of Γ τb) false.
Proof. done. Qed.
Lemma type_mask_void Γ : type_mask Γ voidT = [].
Proof. done. Qed.
Lemma type_mask_array Γ τ n :
  type_mask Γ (τ.[n]) = mjoin (replicate n (type_mask Γ τ)).
Proof. unfold type_mask. by rewrite type_iter_array. Qed.
Lemma type_mask_compound Γ c s τs :
  ✓ Γ → Γ !! s = Some τs → type_mask Γ (compoundT{c} s)
  = match c with
    | Struct_kind =>
       let flds := field_bit_sizes Γ τs in
       mjoin (zip_with (λ τ sz, resize sz true (type_mask Γ τ)) τs flds)
    | Union_kind => replicate (bit_size_of Γ (unionT s)) false
    end.
Proof.
  intros HΓ Hs. unfold type_mask. erewrite (type_iter_compound (=)); try done.
  { by intros ????? ->. }
  clear s τs Hs. intros f g [] s τs _ _ Hfg; f_equal.
  induction (bit_size_of_fields Γ τs HΓ);
    decompose_Forall_hyps'; f_equal; auto with congruence.
Qed.
Lemma type_mask_length Γ τ :
  ✓ Γ → ✓{Γ} τ → length (type_mask Γ τ) = bit_size_of Γ τ.
Proof.
  intros HΓ. revert τ. refine (type_env_ind _ HΓ _ _ _ _).
  * intros τb _. by rewrite type_mask_base, replicate_length.
  * intros τ n _ IH _. rewrite type_mask_array, bit_size_of_array, <-IH.
    induction n; simpl; rewrite ?app_length; auto.
  * intros [] s τs Hs _ _ _; erewrite !type_mask_compound by eauto; simpl.
    { erewrite bit_size_of_struct by eauto. clear Hs.
      induction (bit_size_of_fields _ τs HΓ); simpl; [done|].
      rewrite app_length, resize_length; auto. }
    by rewrite replicate_length.
Qed.

(** ** Properties of the [ctree_unflatten] function *)
Section array_unflatten.
  Context {A B} (f : list A → B).
  Lemma array_unflatten_weaken (g : list A → B) Γ1 Γ2 τ n xs :
    ✓ Γ1 → ✓{Γ1} τ → Γ1 ⊆ Γ2 → (∀ xs, f xs = g xs) →
    array_unflatten Γ1 f τ n xs = array_unflatten Γ2 g τ n xs.
  Proof.
    intros. unfold array_unflatten. erewrite bit_size_of_weaken by eauto.
    revert xs; induction n; intros; f_equal'; auto.
  Qed.
  Lemma array_unflatten_length Γ τ n xs :
    length (array_unflatten Γ f τ n xs) = n.
  Proof. revert xs. induction n; simpl; auto. Qed.
End array_unflatten.
Section struct_unflatten.
  Context {A B} (f : type Ti → list A → B).
  Lemma struct_unflatten_weaken (g : type Ti → list A → B) Γ1 Γ2 τs xs :
    ✓ Γ1 → ✓{Γ1}* τs → Γ1 ⊆ Γ2 →
    Forall (λ τ, ✓{Γ1} τ → ∀ xs, f τ xs = g τ xs) τs →
    struct_unflatten Γ1 f τs xs = struct_unflatten Γ2 g τs xs.
  Proof.
    unfold struct_unflatten. intros HΓ1 Hτs HΓ Hfg.
    erewrite <-(field_bit_sizes_weaken Γ1 Γ2) by eauto. revert xs.
    induction (bit_size_of_fields _ τs HΓ1); intros;
      decompose_Forall_hyps; f_equal'; eauto.
  Qed.
  Lemma struct_unflatten_type_of `{TypeOf (type Ti) B} Γ τs xs :
    ✓ Γ → (∀ τ xs, ✓{Γ} τ → type_of (f τ xs) = τ) → ✓{Γ}* τs →
    type_of <$> struct_unflatten Γ f τs xs = τs.
  Proof.
    intros HΓ ??. unfold struct_unflatten. revert xs.
    induction (bit_size_of_fields _ τs HΓ); intros;
      decompose_Forall_hyps'; f_equal'; auto.
  Qed.
End struct_unflatten.

Lemma ctree_unflatten_base Γ τb xbs : ctree_unflatten Γ τb xbs = MBase τb xbs.
Proof. unfold ctree_unflatten. by rewrite type_iter_base. Qed.
Lemma ctree_unflatten_void Γ xbs :
  ctree_unflatten Γ voidT xbs = MBase ucharT [].
Proof. unfold ctree_unflatten. by rewrite type_iter_void. Qed.
Lemma ctree_unflatten_array Γ τ n xbs :
  ctree_unflatten Γ (τ.[n]) xbs =
    MArray τ (array_unflatten Γ (ctree_unflatten Γ τ) τ n xbs).
Proof. unfold ctree_unflatten. by rewrite type_iter_array. Qed.
Lemma ctree_unflatten_compound Γ c s τs xbs :
  ✓ Γ → Γ !! s = Some τs → ctree_unflatten Γ (compoundT{c} s) xbs
  = match c with
    | Struct_kind =>
       MStruct s (struct_unflatten Γ (λ τ xbs,
        let τsz := bit_size_of Γ τ in
        (ctree_unflatten Γ τ (take τsz xbs), pbit_indetify <$> drop τsz xbs)
       ) τs xbs)
    | Union_kind => MUnionAll s xbs
    end.
Proof.
  intros ? Hs. unfold ctree_unflatten.
  erewrite (type_iter_compound (pointwise_relation _ (=))); try done.
  { intros ???????; f_equal. by apply array_unflatten_weaken. }
  clear s τs Hs xbs. intros f g [] s τs Hs Hτs Hfg xbs; f_equal; auto.
  eapply struct_unflatten_weaken, Forall_impl; eauto with f_equal.
Qed.
Lemma ctree_unflatten_weaken Γ1 Γ2 τ xbs :
  ✓ Γ1 → ✓{Γ1} τ → Γ1 ⊆ Γ2 →
  ctree_unflatten Γ1 τ xbs = ctree_unflatten Γ2 τ xbs.
Proof.
  intros. apply (type_iter_weaken (pointwise_relation _ (=))); try done.
  { intros ???????; f_equal. by apply array_unflatten_weaken. }
  clear xbs. intros f g [] s τs Hs Hτs Hfg xbs; f_equal; auto.
  eapply struct_unflatten_weaken, Forall_impl; eauto 1.
  auto using bit_size_of_weaken with f_equal.
Qed.

Ltac solve_length := repeat first 
  [ rewrite take_length | rewrite drop_length | rewrite app_length
  | rewrite fmap_length | erewrite ctree_flatten_length by eauto
  | rewrite type_mask_length by eauto | rewrite replicate_length
  | rewrite bit_size_of_int | rewrite int_bits_char | rewrite resize_length
  | erewrite sublist_lookup_length by eauto
  | erewrite sublist_alter_length by eauto
  | match goal with
    | |- context [ bit_size_of ?Γ ?τ ] =>
      match goal with
        | H : Γ !! ?s = Some ?τs, H2 : ?τs !! _ = Some τ |- _ =>
          unless (bit_size_of Γ τ ≤ bit_size_of Γ (unionT s)) by done;
          assert (bit_size_of Γ τ ≤ bit_size_of Γ (unionT s))
            by eauto using bit_size_of_union_lookup
        end
    | H : Forall2 _ _ _ |- _ => apply Forall2_length in H
    end ]; lia.
Hint Extern 0 (length _ = _) => solve_length.
Hint Extern 0 (_ = length _) => solve_length.
Hint Extern 0 (_ ≤ length _) => solve_length.
Hint Extern 0 (length _ ≤ _) => solve_length.

Lemma ctree_unflatten_typed Γ m τ xbs :
  ✓ Γ → ✓{Γ} τ → ✓{Γ,m}* xbs → length xbs = bit_size_of Γ τ →
  (Γ,m) ⊢ ctree_unflatten Γ τ xbs : τ.
Proof.
  intros HΓ Hτ. revert τ Hτ xbs. refine (type_env_ind _ HΓ _ _ _ _).
  * intros τ ? xbs ??. rewrite ctree_unflatten_base. by ctree_typed_constructor.
  * intros τ n Hτ IH Hn xbs Hxbs.
    rewrite ctree_unflatten_array, bit_size_of_array.
    intros Hxbs'. ctree_typed_constructor; auto using array_unflatten_length.
    clear Hn. revert xbs Hxbs Hxbs'. induction n; simpl; auto.
  * intros [] s τs Hs Hτs IH Hτs_len xbs Hxbs;
      erewrite ctree_unflatten_compound, ?bit_size_of_struct by eauto;
      intros Hxbs'; simpl; ctree_typed_constructor; eauto.
    + unfold struct_unflatten. clear Hs Hτs Hτs_len. revert xbs Hxbs Hxbs'.
      induction (bit_size_of_fields Γ τs HΓ);
        intros; decompose_Forall_hyps'; constructor; eauto.
    + clear Hs IH Hτs Hτs_len Hxbs'. unfold struct_unflatten. revert xbs Hxbs.
      induction (bit_size_of_fields _ τs HΓ); constructor;
        simpl; auto using pbits_indetify_valid.
    + clear Hs IH Hτs Hτs_len Hxbs Hxbs'. unfold struct_unflatten. revert xbs.
      induction (bit_size_of_fields _ τs HΓ); constructor;
        simpl; auto using pbits_indetify_idempotent.
    + clear Hs IH Hτs Hτs_len Hxbs.
      unfold struct_unflatten, field_bit_padding. revert xbs Hxbs'.
      induction (bit_size_of_fields _ τs HΓ); intros; f_equal'; auto.
Qed.
Lemma ctree_unflatten_type_of Γ τ xbs :
  ✓ Γ → ✓{Γ} τ → type_of (ctree_unflatten Γ τ xbs) = τ.
Proof.
  intros HΓ Hτ. revert τ Hτ xbs. refine (type_env_ind _ HΓ _ _ _ _).
  * done.
  * intros τ n _ IH ? xbs. rewrite ctree_unflatten_array; simpl.
    destruct n; simplify_equality'. by rewrite array_unflatten_length.
  * by intros [] s τs ? _ _ _ xbs; erewrite ctree_unflatten_compound by eauto.
Qed.
Lemma ctree_unflatten_union_free Γ τ xbs :
  ✓ Γ → union_free (ctree_unflatten Γ τ xbs).
Proof.
  intros HΓ. revert τ xbs. refine (weak_type_env_ind _ HΓ _ _ _ _ _ _).
  * intros τb xbs. rewrite ctree_unflatten_base. constructor.
  * intros xbs. rewrite ctree_unflatten_void. constructor.
  * intros τ n IH xbs. rewrite ctree_unflatten_array. constructor.
    revert xbs. elim n; simpl; constructor; auto.
  * intros [] s τs Hs IH xbs;
      erewrite !ctree_unflatten_compound by eauto; constructor.
    clear Hs. unfold struct_unflatten. revert xbs.
    induction (bit_size_of_fields _ τs HΓ); intros;
      decompose_Forall_hyps'; constructor; eauto.
  * intros c s Hs xbs. unfold ctree_unflatten.
    rewrite type_iter_compound_None by done.
    destruct c; simpl; unfold struct_unflatten; constructor.
    revert xbs. induction (zip _ _) as [|[??]]; intros [|??];
      simpl; repeat constructor; auto using (MBase_union_free _ []).
Qed.
Lemma ctree_unflatten_flatten Γ m w τ :
  ✓ Γ → (Γ,m) ⊢ w : τ → ctree_unflatten Γ τ (ctree_flatten w) = union_reset w.
Proof.
  intros HΓ. revert w τ. refine (ctree_typed_ind _ _ _ _ _ _ _ _); simpl.
  * intros. by rewrite ctree_unflatten_base.
  * intros ws τ ? IH _. rewrite ctree_unflatten_array. f_equal.
    induction IH; [done |]; intros; decompose_Forall_hyps'; auto.
    rewrite take_app_alt, drop_app_alt by auto. f_equal; auto.
  * intros s wxbss τs Hs Hws IH _ Hindet Hlen.
    erewrite ctree_unflatten_compound by eauto; f_equal'. clear Hs.
    revert wxbss Hindet Hlen Hws IH. unfold struct_unflatten, field_bit_padding.
    induction (bit_size_of_fields _ τs HΓ);
      intros [|[] ?] ????; decompose_Forall_hyps'; [done|].
    rewrite ?take_app_alt, ?drop_app_alt by auto. repeat f_equal; auto.
  * intros. by erewrite ctree_unflatten_compound by eauto.
  * intros. by erewrite ctree_unflatten_compound by eauto.
Qed.
Lemma ctree_flatten_unflatten_le Γ τ xbs :
  ✓ Γ → ✓{Γ} τ → length xbs ≤ bit_size_of Γ τ →
  ctree_flatten (ctree_unflatten Γ τ xbs)
  = mask pbit_indetify (type_mask Γ τ) xbs.
Proof.
  intros HΓ Hτ. revert τ Hτ xbs. refine (type_env_ind _ HΓ _ _ _ _).
  * intros. by rewrite ctree_unflatten_base, type_mask_base, mask_false.
  * intros τ n ? IH _ xbs.
    rewrite ctree_unflatten_array, bit_size_of_array, type_mask_array; simpl.
    revert xbs. induction n as [|n IHn]; intros xbs ?; simplify_equality'.
    { symmetry; apply nil_length_inv; lia. }
    by rewrite IH, IHn, mask_app, type_mask_length by auto.
  * intros [] s τs Hs Hτs IH _ xbs; erewrite ctree_unflatten_compound,
      ?type_mask_compound, ?bit_size_of_struct, ?mask_false by eauto; eauto.
    clear Hs; simpl. revert xbs IH. unfold struct_unflatten.
    induction (bit_size_of_fields _ τs HΓ) as [|τ sz τs szs ?? IHτ]; simpl.
    { intros [|??] _ ?; simpl in *; auto with lia. }
    intros xbs. rewrite Forall_cons. intros [IH ?] ?; decompose_Forall_hyps'.
    by rewrite IH, IHτ, mask_app, resize_length, resize_ge, mask_app,
      type_mask_length, mask_true by eauto.
Qed.
Lemma ctree_flatten_unflatten Γ τ xbs :
  ✓ Γ → ✓{Γ} τ → length xbs = bit_size_of Γ τ →
  ctree_flatten (ctree_unflatten Γ τ xbs)
  = mask pbit_indetify (type_mask Γ τ) xbs.
Proof. intros. apply ctree_flatten_unflatten_le; auto with lia. Qed.
Lemma ctree_mask_flatten Γ m w τ :
  ✓ Γ → (Γ,m) ⊢ w : τ →
  mask pbit_indetify (type_mask Γ τ) (ctree_flatten w) = ctree_flatten w.
Proof.
  intros. by erewrite <-ctree_flatten_unflatten,
    ctree_unflatten_flatten, ctree_flatten_union_reset by eauto.
Qed.
Lemma ctree_unflatten_Forall_le (P : pbit Ti → Prop) Γ τ xbs :
  ✓ Γ → ✓{Γ} τ → (∀ xb, P xb → P (pbit_indetify xb)) → Forall P xbs →
  length xbs ≤ bit_size_of Γ τ → ctree_Forall P (ctree_unflatten Γ τ xbs).
Proof.
  intros ??? Hxbs Hlen. rewrite ctree_flatten_unflatten_le by done.
  generalize (type_mask Γ τ). clear Hlen.
  induction Hxbs; intros [|[] ?]; simpl; auto.
Qed.
Lemma ctree_unflatten_Forall (P : pbit Ti → Prop) Γ τ xbs :
  ✓ Γ → ✓{Γ} τ → (∀ xb, P xb → P (pbit_indetify xb)) → Forall P xbs →
  length xbs = bit_size_of Γ τ → ctree_Forall P (ctree_unflatten Γ τ xbs).
Proof. intros. apply ctree_unflatten_Forall_le; auto with lia. Qed.

(** ** Properties of the [ctree_new] function *)
Lemma ctree_new_base Γ xb τb :
  ctree_new Γ xb τb = MBase τb (replicate (bit_size_of Γ τb) xb).
Proof. unfold ctree_new. by rewrite type_iter_base. Qed.
Lemma ctree_new_array Γ xb τ n :
  ctree_new Γ xb (τ.[n]) = MArray τ (replicate n (ctree_new Γ xb τ)).
Proof. unfold ctree_new. by rewrite type_iter_array. Qed.
Lemma ctree_new_compound Γ xb c s τs :
  ✓ Γ → Γ !! s = Some τs → ctree_new Γ xb (compoundT{c} s)
  = match c with
    | Struct_kind => MStruct s (zip (ctree_new Γ xb <$> τs)
       (flip replicate (pbit_indetify xb) <$> field_bit_padding Γ τs))
    | Union_kind => MUnionAll s (replicate (bit_size_of Γ (unionT s)) xb)
    end.
Proof.
  intros HΓ Hs. unfold ctree_new; erewrite (type_iter_compound (=)); try done.
  { by intros ????? ->. }
  intros ?? [] ?????; do 2 f_equal'. by apply Forall_fmap_ext.
Qed.
Lemma ctree_unflatten_replicate Γ xb τ :
  ✓ Γ → ✓{Γ} τ →
  ctree_unflatten Γ τ (replicate (bit_size_of Γ τ) xb) = ctree_new Γ xb τ.
Proof.
  intros HΓ Hτ. revert τ Hτ. refine (type_env_ind _ HΓ _ _ _ _).
  * intros. by rewrite ctree_unflatten_base.
  * intros τ n _ IH _. rewrite ctree_unflatten_array,
      ctree_new_array, bit_size_of_array; f_equal; induction n; simpl;
      rewrite ?take_replicate_plus, ?drop_replicate_plus; f_equal; auto.
  * intros [] s τs Hs _ IH _; erewrite ctree_unflatten_compound,
      ctree_new_compound, ?bit_size_of_struct by eauto; clear Hs; f_equal'.
    unfold field_bit_padding, struct_unflatten.
    induction (bit_size_of_fields _ τs HΓ); decompose_Forall_hyps';
      rewrite ?take_replicate_plus, ?drop_replicate_plus, ?take_replicate,
      ?drop_replicate, ?Min.min_l, ?fmap_replicate by done; repeat f_equal; auto.
Qed.
Lemma ctree_new_weaken Γ1 Γ2 xb τ :
  ✓ Γ1 → ✓{Γ1} τ → Γ1 ⊆ Γ2 → ctree_new Γ1 xb τ = ctree_new Γ2 xb τ.
Proof.
  intros. apply (type_iter_weaken (=)); try done.
  { intros. by erewrite bit_size_of_weaken by eauto using TBase_valid. }
  { by intros ????? ->. }
  intros f g [] s τs Hs Hτs ?; do 2 f_equal; [by apply Forall_fmap_ext| |].
  * by erewrite field_bit_padding_weaken by eauto.
  * by erewrite bit_size_of_weaken by eauto using TCompound_valid.
Qed.
Lemma ctrees_new_weaken Γ1 Γ2 xb τs :
  ✓ Γ1 → ✓{Γ1}* τs → Γ1 ⊆ Γ2 → ctree_new Γ1 xb <$> τs = ctree_new Γ2 xb <$> τs.
Proof. induction 2; intros; f_equal'; auto using ctree_new_weaken. Qed.
Lemma ctree_new_Forall (P : pbit Ti → Prop) Γ xb τ :
  ✓ Γ → ✓{Γ} τ → P xb → P (pbit_indetify xb) → ctree_Forall P (ctree_new Γ xb τ).
Proof.
  intros. rewrite <-ctree_unflatten_replicate, ctree_flatten_unflatten_le by done.
  generalize (type_mask Γ τ).
  induction (bit_size_of Γ τ); intros [|[]?]; simpl; constructor; auto.
Qed.
Lemma ctree_new_type_of Γ xb τ :
  ✓ Γ → ✓{Γ} τ → type_of (ctree_new Γ xb τ) = τ.
Proof.
  intros. by rewrite <-ctree_unflatten_replicate,
    ctree_unflatten_type_of by done.
Qed.
Lemma ctree_new_typed Γ m xb τ :
  ✓ Γ → ✓{Γ} τ → ✓{Γ,m} xb → (Γ,m) ⊢ ctree_new Γ xb τ : τ.
Proof.
  intros. rewrite <-ctree_unflatten_replicate by done.
  apply ctree_unflatten_typed; auto using replicate_length.
Qed.
Lemma ctree_new_union_free Γ xb τ: ✓ Γ → ✓{Γ} τ → union_free (ctree_new Γ xb τ).
Proof.
  intros. rewrite <-ctree_unflatten_replicate by done.
  auto using ctree_unflatten_union_free.
Qed.

(** ** Properties about disjointness *)
Lemma ctree_disjoint_type_of w1 w2 : w1 ⊥ w2 → type_of w1 = type_of w2.
Proof. destruct 1; f_equal'; eauto using Forall2_length. Qed.
Lemma ctree_union_type_of w1 w2 : w1 ⊥ w2 → type_of (w1 ∪ w2) = type_of w1.
Proof. destruct 1; f_equal'; rewrite zip_with_length; auto. Qed.
Lemma ctree_disjoint_typed_unique Γ m1 m2 w1 w2 τ1 τ2 :
  w1 ⊥ w2 → (Γ,m1) ⊢ w1 : τ1 → (Γ,m2) ⊢ w2 : τ2 → τ1 = τ2.
Proof.
  intros. erewrite <-(type_of_correct _ _ τ1), <-(type_of_correct _ _ τ2)
    by eauto; eauto using ctree_disjoint_type_of.
Qed.
Lemma ctree_disjoint_typed Γ m w1 w2 τ :
  ✓ Γ → w1 ⊥ w2 → (Γ,m) ⊢ w1 : τ → ctree_unmapped w2 → (Γ,m) ⊢ w2 : τ.
Proof.
  intros ? Hw. revert w1 w2 Hw τ.
  refine (ctree_disjoint_ind_alt _ _ _ _ _ _ _ _); simpl.
  * intros τb ??? τ Hw; pattern τ; apply (ctree_typed_inv_l _ _ _ _ _ Hw).
    intros; constructor; eauto using pbits_disjoint_typed.
  * intros τ ws1 ws2 _ IH τ' Hw; pattern τ';
      apply (ctree_typed_inv_l _ _ _ _ _ Hw); clear τ' Hw; intros Hws2 Hlen ?.
    ctree_typed_constructor; auto. clear Hlen.
    revert τ Hws2. induction IH; intros; decompose_Forall_hyps'; auto.
  * intros s wxbss1 wxbss2 _ IH Hxbs τ' Hw; pattern τ';
      apply (ctree_typed_inv_l _ _ _ _ _ Hw); clear τ' Hw;
      intros τs Hs Hws2 Hxbs2 ? Hlen ?.
    ctree_typed_constructor; eauto.
    + clear Hlen Hxbs2 Hs. revert τs Hws2.
      induction IH; intros; decompose_Forall_hyps'; auto.
    + clear Hlen Hs Hws2 IH.
      induction Hxbs; decompose_Forall_hyps'; eauto using pbits_disjoint_typed.
    + clear Hlen Hs Hws2 Hxbs2 IH. induction Hxbs;
        decompose_Forall_hyps'; eauto using pbits_disjoint_indetified.
    + rewrite <-Hlen. elim Hxbs; intros; f_equal'; auto.
  * intros; decompose_Forall_hyps'; naive_solver.
  * intros s ??? τ Hw; pattern τ; apply (ctree_typed_inv_l _ _ _ _ _ Hw).
    intros. ctree_typed_constructor; eauto using pbits_disjoint_typed.
  * intros; decompose_Forall_hyps'; naive_solver.
  * intros s i w1 xbs1 xbs2 ???? τ Hw; pattern τ;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw); clear τ Hw; intros τs τ; intros.
    assert (length xbs2 = bit_size_of Γ (unionT s)).
    { erewrite <-Forall2_length by eauto; auto. }
    econstructor; eauto using pbits_disjoint_typed, ctree_flatten_valid.
Qed.
Lemma ctree_unflatten_disjoint Γ τ xbs1 xbs2 :
  ✓ Γ → ✓{Γ} τ →
  xbs1 ⊥* xbs2 → ctree_unflatten Γ τ xbs1 ⊥ ctree_unflatten Γ τ xbs2.
Proof.
  intros HΓ Hτ. revert τ Hτ xbs1 xbs2. refine (type_env_ind _ HΓ _ _ _ _).
  * intros. rewrite !ctree_unflatten_base. by constructor.
  * intros τ n _ IH _ xbs1 xbs2 Hxbs. rewrite !ctree_unflatten_array.
    constructor. revert xbs1 xbs2 Hxbs.
    induction n; simpl; intros; constructor; auto.
  * intros [] s τs Hs _ IH _ xbs1 xbs2 Hxbs;
      erewrite !ctree_unflatten_compound by eauto; constructor; auto.
    + revert xbs1 xbs2 Hxbs. clear Hs. unfold struct_unflatten.
      induction (bit_size_of_fields _ τs HΓ); intros;
        decompose_Forall_hyps'; constructor; simpl; auto.
    + revert xbs1 xbs2 Hxbs. clear Hs IH. unfold struct_unflatten.
      induction (bit_size_of_fields _ τs HΓ); intros;
        constructor; simpl; auto using pbits_indetify_disjoint.
Qed.
Lemma ctree_unflatten_union Γ τ xbs1 xbs2 :
  ✓ Γ → ✓{Γ} τ → xbs1 ⊥* xbs2 → ctree_unflatten Γ τ (xbs1 ∪* xbs2)
  = ctree_unflatten Γ τ xbs1 ∪ ctree_unflatten Γ τ xbs2.
Proof.
  intros HΓ Hτ. revert τ Hτ xbs1 xbs2. refine (type_env_ind _ HΓ _ _ _ _).
  * intros. by rewrite !ctree_unflatten_base.
  * intros τ n _ IH _ xbs1 xbs2 Hxbs. rewrite !ctree_unflatten_array; f_equal'.
    revert xbs1 xbs2 Hxbs. induction n; simpl; intros; f_equal';
      rewrite ?zip_with_take, ?zip_with_drop; auto.
  * intros [] s τs Hs _ IH _ xbs1 xbs2 Hxbs;
      erewrite !ctree_unflatten_compound by eauto; f_equal'; auto.
    revert xbs1 xbs2 Hxbs. clear Hs. unfold struct_unflatten.
    induction (bit_size_of_fields _ τs HΓ); intros;
      decompose_Forall_hyps'; repeat f_equal; simpl;
      rewrite ?fmap_drop, ?zip_with_take, ?pbits_indetify_union,
      ?zip_with_drop; eauto.
Qed.
Lemma ctree_unflatten_subseteq Γ τ xbs1 xbs2 :
  ✓ Γ → ✓{Γ} τ →
  xbs1 ⊆* xbs2 → ctree_unflatten Γ τ xbs1 ⊆ ctree_unflatten Γ τ xbs2.
Proof.
  intros. rewrite <-(seps_union_difference xbs1 xbs2) by done.
  rewrite ctree_unflatten_union; eauto using @seps_disjoint_difference.
  apply ctree_union_subseteq_l, ctree_unflatten_disjoint;
    eauto using @seps_disjoint_difference.
Qed.
Lemma ctree_flatten_unflatten_disjoint Γ m w τ ys :
  ✓ Γ → (Γ,m) ⊢ w : τ →
  ys ⊥* ctree_flatten w → Forall sep_unmapped ys → ctree_unflatten Γ τ ys ⊥ w.
Proof.
  intros HΓ Hw. revert w τ Hw ys. refine (ctree_typed_ind _ _ _ _ _ _ _ _).
  * by constructor.
  * intros ws τ Hws IH _ ys Hys Hys'.
    rewrite ctree_unflatten_array; simplify_equality'. constructor.
    revert ys Hys Hys'. induction IH; intros; decompose_Forall_hyps';
      rewrite ?take_app_alt, ?drop_app_alt
        by (erewrite Forall2_length by eauto; auto); constructor; auto.
  * intros s wxbss τs Hs Hws IH _ ? Hlen ys Hys Hys';
      erewrite ctree_unflatten_compound by eauto; simplify_equality'.
    clear Hs. constructor; revert dependent wxbss; revert dependent ys;
      unfold field_bit_padding, struct_unflatten;
      induction (bit_size_of_fields _ τs HΓ); intros; decompose_Forall_hyps';
      rewrite ?take_app_alt, ?drop_app_alt
        by (erewrite ?app_length, !Forall2_length by eauto; solve_length);
      rewrite ?pbits_indetify_unmapped by auto; constructor; eauto.
  * intros s i τs w xbs τ ????????  ys Hys Hys';
      erewrite ctree_unflatten_compound by eauto; decompose_Forall_hyps'.
    constructor; eauto using ctree_typed_sep_valid.
  * intros. erewrite ctree_unflatten_compound by eauto. by constructor.
Qed.
Lemma ctree_new_disjoint Γ m w τ : ✓ Γ → (Γ,m) ⊢ w : τ → ctree_new Γ ∅ τ ⊥ w.
Proof.
  intros.
  rewrite <-ctree_unflatten_replicate by eauto using ctree_typed_type_valid.
  eapply ctree_flatten_unflatten_disjoint; eauto using @sep_unmapped_empty.
  eapply Forall2_replicate_l, Forall_impl; eauto using ctree_flatten_valid.
  eauto using @sep_disjoint_empty_l, pbit_valid_sep_valid.
Qed.

(** ** The map operation *)
Lemma ctree_map_typed Γ m h w τ :
  ✓ Γ → (Γ,m) ⊢ w : τ → ✓{Γ,m}* (h <$> ctree_flatten w) →
  (∀ xb, pbit_indetify xb = xb → pbit_indetify (h xb) = h xb) →
  (Γ,m) ⊢ ctree_map h w : τ.
Proof.
  intros ? Hw Hw' ?. revert w τ Hw Hw'. assert (∀ xbs,
    pbit_indetify <$> xbs = xbs → pbit_indetify <$> h <$> xbs = h <$> xbs).
  { induction xbs; intros; simplify_equality'; f_equal; auto. }
  refine (ctree_typed_ind _ _ _ _ _ _ _ _); simpl.
  * intros. ctree_typed_constructor; auto.
  * intros ws τ _ IH Hlen Hw'. ctree_typed_constructor; auto. clear Hlen.
    revert Hw'. induction IH; simpl; rewrite ?fmap_app; intros;
      decompose_Forall_hyps'; constructor; auto.
  * intros s wxbss τs Hs _ IH Hxss Hindet Hlen Hw'.
    ctree_typed_constructor; eauto.
    + revert Hw'. elim IH; [|intros [??] ???]; simpl; rewrite ?fmap_app;
        intros; decompose_Forall_hyps'; auto.
    + revert Hw'. elim Hxss; [|intros [??] ???]; simpl; rewrite ?fmap_app;
        intros; decompose_Forall_hyps'; auto.
    + elim Hindet; intros; constructor; simpl; auto.
    + rewrite <-Hlen. elim wxbss; intros; f_equal'; auto.
  * intros s i τs w xbs τ; rewrite fmap_app; intros; decompose_Forall_hyps'.
    unfold MUnion'; case_decide; ctree_typed_constructor;
      eauto using ctree_flatten_valid; try solve_length.
  * intros. ctree_typed_constructor; eauto.
Qed.
Lemma ctree_map_type_of h w : type_of (ctree_map h w) = type_of w.
Proof. destruct w; simpl; unfold MUnion'; repeat case_decide; auto. Qed.

(** ** Lookup operation *)
Lemma ctree_lookup_seg_freeze Γ w rs w' :
  w !!{Γ} freeze true rs = Some w' → w !!{Γ} rs = Some w'.
Proof.
  intros. destruct rs as [| |i s q]; auto.
  by destruct w, q; simplify_option_equality.
Qed.
Lemma ctree_lookup_freeze Γ w r w' :
  w !!{Γ} (freeze true <$> r) = Some w' → w !!{Γ} r = Some w'.
Proof.
  revert w'. induction r; intros w'; simpl; [by rewrite list_path_lookup_nil|].
  rewrite !list_path_lookup_cons. intros.
  simplify_option_equality; eauto using ctree_lookup_seg_freeze.
Qed.
Lemma ctree_lookup_seg_unfreeze Γ w rs w' :
  w !!{Γ} rs = Some w' → w !!{Γ} freeze false rs = Some w'.
Proof.
  intros. destruct rs as [| |i s q]; auto.
  by destruct w, q; simplify_option_equality.
Qed.
Lemma ctree_lookup_unfreeze Γ w r w' :
  w !!{Γ} r = Some w' → w !!{Γ} (freeze false <$> r) = Some w'.
Proof.
  revert w'. induction r; intros w'; simpl; [by rewrite list_path_lookup_nil|].
  rewrite !list_path_lookup_cons. intros.
  simplify_option_equality; eauto using ctree_lookup_seg_unfreeze.
Qed.
Lemma ctree_lookup_seg_freeze_proper Γ q1 q2 w rs1 rs2 w1 w2 :
  w !!{Γ} rs1 = Some w1 → w !!{Γ} rs2 = Some w2 →
  freeze q1 rs1 = freeze q2 rs2 → w1 = w2.
Proof. intros. by destruct w, rs1, rs2; simplify_option_equality. Qed.
Lemma ctree_lookup_freeze_proper Γ q1 q2 w r1 r2 w1 w2 :
  w !!{Γ} r1 = Some w1 → w !!{Γ} r2 = Some w2 →
  freeze q1 <$> r1 = freeze q2 <$> r2 → w1 = w2.
Proof.
  revert r2 w1 w2. induction r1 as [|rs1 r1 IH]; intros [|rs2 r2] ??; try done.
  { intros. by simplify_equality. }
  rewrite !list_path_lookup_cons; intros; simplify_option_equality.
  efeed pose proof IH; eauto. subst. eauto using ctree_lookup_seg_freeze_proper.
Qed.
Lemma ctree_lookup_seg_inv P Γ rs w w' :
  w !!{Γ} rs = Some w' →
  match rs, w with
  | RArray i τ n, MArray τ' ws =>
     (∀ w'', τ' = τ → n = length ws → ws !! i = Some w'' → P w'') → P w'
  | RStruct i s, MStruct s' wxbss =>
     (∀ w'' xs, s = s' → wxbss !! i = Some (w'', xs) → P w'') → P w'
  | RUnion i s q, MUnion s' j w'' xs =>
     (s = s' → i = j → P w'') →
     (∀ τs τ, s = s' → i ≠ j → q = false →
       Γ !! s = Some τs → τs !! i = Some τ →
       ctree_unshared w'' → Forall sep_unshared xs →
       P (ctree_unflatten Γ τ (take (bit_size_of Γ τ)
          (ctree_flatten w'' ++ xs)))) →
     P w'
  | RUnion i s _, MUnionAll s' xs =>
     (∀ τs τ, s = s' → Γ !! s = Some τs → τs !! i = Some τ →
       Forall sep_unshared xs →
       P (ctree_unflatten Γ τ (take (bit_size_of Γ τ) xs))) →
     P w'
  | _, _ => P w'
  end.
Proof.
  destruct rs, w; intros; simplify_option_equality;
    repeat match goal with p : prod _ _ |- _ => destruct p end; eauto.
Qed.

Lemma ctree_lookup_seg_union_free Γ w rs w' :
  ✓ Γ → union_free w → w !!{Γ} rs = Some w' → union_free w'.
Proof.
  intros ? Hw Hrs; destruct Hw, rs; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs).
  * by intros; decompose_Forall_hyps.
  * by intros; decompose_Forall_hyps.
  * eauto using ctree_unflatten_union_free, env_valid_lookup_singleton.
Qed.
Lemma ctree_lookup_union_free Γ w r w' :
  ✓ Γ → union_free w → w !!{Γ} r = Some w' → union_free w'.
Proof.
  intros HΓ. revert w. induction r using rev_ind; intros w Hw Hr;
    rewrite ?list_path_lookup_snoc in Hr; simplify_option_equality;
    eauto using ctree_lookup_seg_union_free.
Qed.
Lemma ctree_lookup_seg_Some Γ m w τ rs w' :
  ✓ Γ → (Γ,m) ⊢ w : τ → w !!{Γ} rs = Some w' →
  ∃ σ, Γ ⊢ rs : τ ↣ σ ∧ (Γ,m) ⊢ w' : σ.
Proof.
  intros ? Hw Hrs; destruct rs as [i τ' n|i|i]; destruct Hw as
    [τ xbs|ws|s wxbss τs ? Hws|s j τs w xbs τ|s τs xbs] using @ctree_typed_case;
    pattern w'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
  * intros w'' -> -> ?. exists τ'. decompose_Forall_hyps'.
    repeat constructor; eauto using lookup_lt_is_Some_1.
  * intros w'' xbs -> ?.
    destruct (Forall2_lookup_l _ _ _ i (w'',xbs) Hws) as [σ [??]]; eauto.
    exists σ; repeat econstructor; eauto.
  * intros -> ->. exists τ; repeat econstructor; eauto.
  * intros ? τ' ???????; simplify_equality'. exists τ'; repeat econstructor;
      eauto 6 using ctree_unflatten_typed, ctree_flatten_valid.
  * intros ?? -> ???; simplify_equality'.
    exists τ; repeat econstructor; eauto using ctree_unflatten_typed.
Qed.
Lemma ctree_lookup_Some Γ m w τ r w' :
  ✓ Γ → (Γ,m) ⊢ w : τ → w !!{Γ} r = Some w' →
  ∃ σ, Γ ⊢ r : τ ↣ σ ∧ (Γ,m) ⊢ w' : σ.
Proof.
  intros HΓ. revert w τ.
  induction r as [|rs r IH] using rev_ind; intros w τ Hvτ Hr.
  { simplify_equality'. eexists; split; [econstructor |]; eauto. }
  rewrite list_path_lookup_snoc in Hr. simplify_option_equality.
  edestruct ctree_lookup_seg_Some as (?&?&?); eauto.
  edestruct IH as (?&?&?); eauto.
  eexists; split; [eapply list_typed_snoc |]; eauto.
Qed.
Lemma ctree_lookup_seg_typed Γ m w τ rs w' σ :
  ✓ Γ → (Γ,m) ⊢ w : τ → w !!{Γ} rs = Some w' → Γ ⊢ rs : τ ↣ σ → (Γ,m) ⊢ w' :σ.
Proof.
  intros HΓ Hvτ Hw ?. by destruct (ctree_lookup_seg_Some _ _ _ _ _ _ HΓ Hvτ Hw)
    as (σ'&Hrσ'&?); simplify_type_equality.
Qed.
Lemma ctree_lookup_typed Γ m w τ r w' σ :
  ✓ Γ → (Γ,m) ⊢ w : τ → w !!{Γ} r = Some w' → Γ ⊢ r : τ ↣ σ → (Γ,m) ⊢ w' : σ.
Proof.
  intros HΓ Hvτ Hw' ?. by destruct (ctree_lookup_Some _ _ _ _ _ _ HΓ Hvτ Hw')
    as (σ'&Hrσ'&?); simplify_type_equality.
Qed.
Lemma ctree_lookup_seg_Forall (P : pbit Ti → Prop) Γ w rs w' :
  ✓ Γ → (∀ xb, P xb → P (pbit_indetify xb)) →
  ctree_Forall P w → w !!{Γ} rs = Some w' → ctree_Forall P w'.
Proof.
  intros ??.
  assert (∀ βs xbs, Forall P xbs → Forall P (mask pbit_indetify βs xbs)).
  { intros βs xbs Hxbs. revert βs. induction Hxbs; intros [|[]]; simpl; auto. }
  intros Hw Hrs; destruct w, rs; simpl in Hw; rewrite ?Forall_bind in Hw;
    pattern w'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs;
    intros; decompose_Forall_hyps'; eauto 7 using ctree_unflatten_Forall_le.
Qed.
Lemma ctree_lookup_Forall (P : pbit Ti → Prop) Γ w r w' :
  ✓ Γ → (∀ xb, P xb → P (pbit_indetify xb)) →
  ctree_Forall P w → w !!{Γ} r = Some w' → ctree_Forall P w'.
Proof.
  intros HΓ ?. revert w. induction r as [|rs r] using rev_ind;
    intros w; rewrite ?list_path_lookup_snoc; intros; simplify_option_equality;
    eauto using ctree_lookup_seg_Forall.
Qed.
Lemma ctree_new_lookup_seg Γ τ x rs σ :
  ✓ Γ → sep_unshared x → ✓{Γ} τ →
  Γ ⊢ rs : τ ↣ σ → ctree_new Γ x τ !!{Γ} rs = Some (ctree_new Γ x σ).
Proof.
  destruct 4 as [τ n i|s i τs τ Hs Hτs|s i q τs τ].
  * rewrite ctree_new_array; simplify_option_equality.
    by rewrite lookup_replicate by done.
  * erewrite ctree_new_compound by eauto; simplify_option_equality.
    by rewrite <-list_lookup_fmap, fst_zip, list_lookup_fmap, Hτs
      by (by rewrite !fmap_length, field_bit_padding_length).
  * erewrite ctree_new_compound by eauto; simplify_option_equality by eauto.
    by rewrite take_replicate, Min.min_l, ctree_unflatten_replicate
      by eauto using bit_size_of_union_lookup.
Qed.
Lemma ctree_new_lookup Γ x τ r σ :
  ✓ Γ → sep_unshared x → ✓{Γ} τ →
  Γ ⊢ r : τ ↣ σ → ctree_new Γ x τ !!{Γ} r = Some (ctree_new Γ x σ).
Proof.
  induction 4 as [|r rs τ1 τ2 τ3 ?? IH] using @list_typed_ind; [done|].
  rewrite list_path_lookup_cons, IH; simpl;
    eauto using ctree_new_lookup_seg, ref_typed_type_valid.
Qed.
Lemma ctree_lookup_seg_unfreeze_exists Γ m w τ rs σ :
  ✓ Γ → (Γ,m) ⊢ w : τ → ctree_unshared w →
  Γ ⊢ rs : τ ↣ σ → ∃ w', w !!{Γ} freeze false rs = Some w'.
Proof.
  destruct 2 as [|ws τ|s wxbss τs| | ] using @ctree_typed_case;
    inversion 2; decompose_Forall_hyps'; simplify_option_equality; eauto.
  by apply lookup_lt_is_Some_2.
Qed.
Lemma ctree_lookup_unfreeze_exists Γ m w τ r σ :
  ✓ Γ → (Γ,m) ⊢ w : τ → ctree_unshared w →
  Γ ⊢ r : τ ↣ σ → ∃ w', w !!{Γ} (freeze false <$> r) = Some w'.
Proof.
  intros HΓ. revert w τ.
  induction r as [|rs r IH] using rev_ind; intros w τ Hwτ Hw Hr.
  { rewrite list_typed_nil in Hr; subst. by exists w. }
  rewrite list_typed_snoc in Hr; destruct Hr as (σ'&?&?).
  destruct (ctree_lookup_seg_unfreeze_exists Γ m w τ rs σ') as (w'&?); auto.
  destruct (IH w' σ') as (w''&?); eauto using ctree_lookup_seg_union_free,
    ctree_lookup_seg_Forall, ctree_lookup_seg_typed,
    ref_seg_typed_freeze_2, pbit_indetify_unshared.
  exists w''. rewrite fmap_app; simpl.
  rewrite list_path_lookup_snoc. by simplify_option_equality.
Qed.
Lemma type_mask_ref_seg Γ τ rs σ :
  ✓ Γ → Γ ⊢ rs : τ ↣ σ → ✓{Γ} τ →
  take (bit_size_of Γ σ) (drop (ref_seg_object_offset Γ rs) (type_mask Γ τ))
  =.>* type_mask Γ σ.
Proof.
  intros HΓ Hrs Hτ.
  destruct Hrs as [τ i n Hin|s i τs τ Hs Hi|]; simplify_option_equality.
  * rewrite type_mask_array; apply reflexive_eq. revert i Hin.
    apply TArray_valid_inv_type in Hτ.
    induction n as [|n]; intros [|i] ?; simplify_equality'; rewrite ?drop_0,
      ?take_app_alt, <-?drop_drop, ?drop_app_alt by done; auto with lia.
  * erewrite type_mask_compound by eauto; simpl; apply reflexive_eq.
    assert (✓{Γ}* τs) as Hτs by eauto; revert i Hi Hτs. clear Hs Hτ.
    unfold field_bit_offset.
    induction (bit_size_of_fields _ τs HΓ); intros [|i] ??;
      decompose_Forall_hyps'; rewrite <-?drop_drop, ?drop_app_alt, ?drop_0,
        ?resize_ge, <-?(associative_L (++)), ?take_app_alt by done; auto.
  * erewrite type_mask_compound by eauto; simpl.
    rewrite drop_0, take_replicate, Min.min_l by solve_length.
    by apply replicate_false.
Qed.
Lemma ctree_lookup_seg_flatten Γ m w τ rs w' τ' :
  ✓ Γ → (Γ,m) ⊢ w : τ → w !!{Γ} rs = Some w' → (Γ,m) ⊢ w' : τ' →
  mask pbit_indetify (type_mask Γ τ') $ take (bit_size_of Γ τ') $
    drop (ref_seg_object_offset Γ rs) $ ctree_flatten w = ctree_flatten w'.
Proof.
  intros HΓ. revert w τ. refine (ctree_typed_ind _ _ _ _ _ _ _ _).
  * by destruct rs.
  * intros ws τ Hws _ _ Hrs; destruct rs as [i| |]; pattern w';
      apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear w' Hrs.
    assert (∀ ws', (Γ,m) ⊢* ws' : τ →
      length (ws' ≫= ctree_flatten) = length ws' * bit_size_of Γ τ) as help.
    { induction 1; f_equal'; auto. }
    intros w <- -> ??; decompose_Forall_hyps'; simplify_type_equality.
    rewrite <-(take_drop_middle ws i w), bind_app, bind_cons by done.
    rewrite drop_app_alt by (by rewrite help, take_length_le
      by eauto using Nat.lt_le_incl, lookup_lt_Some).
    by erewrite take_app_alt, ctree_mask_flatten by eauto.
  * intros s wxbss τs Hs Hws _ _ Hindet Hlen Hrs; destruct rs as [|i|];
      pattern w'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    intros w xs -> Hi ?; destruct (Forall2_lookup_l (typed (Γ,m) ∘ fst)
      wxbss τs i (w,xs)) as (τ&Hi'&Hw); auto;
      simplify_option_equality; simplify_type_equality'.
    assert (field_bit_offset Γ τs i =
      length (take i wxbss ≫= λ wxs, ctree_flatten (wxs.1) ++ wxs.2)) as help2.
    { clear Hs Hi' Hw Hindet. apply lookup_lt_Some in Hi.
      unfold field_bit_padding, field_bit_offset in *.
      revert i wxbss Hi Hlen Hws. induction (bit_size_of_fields _ τs HΓ);
        intros [|?] ????; decompose_Forall_hyps';
        rewrite ?app_length; f_equal; auto; solve_length. }
    rewrite <-(take_drop_middle wxbss i (w,xs)), bind_app by done; simpl.
    by erewrite drop_app_alt, <-(associative_L (++)), take_app_alt,
      ctree_mask_flatten by eauto.
  * intros s i τs w xs τ Hs Hτ ? _ _ Hindet ? _ Hrs; destruct rs as [| |i'];
      pattern w'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    { intros -> -> ?; simplify_option_equality; simplify_type_equality.
      by erewrite drop_0, take_app_alt, ctree_mask_flatten by eauto. }
    intros ? τ'' -> ? -> ?? _ _ Hw; simplify_option_equality.
    apply type_of_correct in Hw;
      rewrite ctree_unflatten_type_of in Hw by eauto; simplify_equality'.
    by rewrite ctree_flatten_unflatten by eauto.
  * intros s τs xs ? _ ? Hrs; destruct rs as [| |i'];
      pattern w'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    intros ?? -> ?? _ Hw; simplify_option_equality.
    apply type_of_correct in Hw;
      rewrite ctree_unflatten_type_of in Hw by eauto; simplify_equality'.
    by rewrite ctree_flatten_unflatten by eauto.
Qed.
Lemma ctree_lookup_flatten Γ m w τ r w' τ' :
  ✓ Γ → (Γ,m) ⊢ w : τ → w !!{Γ} r = Some w' → (Γ,m) ⊢ w' : τ' →
  mask pbit_indetify (type_mask Γ τ') $
    take (bit_size_of Γ τ') $
    drop (ref_object_offset Γ r) $ ctree_flatten w = ctree_flatten w'.
Proof.
  intros HΓ ?. unfold ref_object_offset.
  revert w' τ'. induction r as [|rs r IH]; intros w'' τ''.
  { intros; simplify_type_equality'.
    by erewrite drop_0, take_ge, ctree_mask_flatten by eauto. }
  rewrite list_path_lookup_cons; intros.
  destruct (w !!{Γ} r) as [w'|] eqn:?; simplify_equality'.
  destruct (ctree_lookup_Some Γ m w τ r w') as (τ'&?&?); auto.
  destruct (ctree_lookup_seg_Some Γ m w' τ' rs w'') as (?&?&?); auto.
  simplify_type_equality'.
  assert (ref_seg_object_offset Γ rs + bit_size_of Γ τ'' ≤ bit_size_of Γ τ')
    by eauto using ref_seg_object_offset_size.
  rewrite Nat.add_comm, <-drop_drop, <-(Min.min_l (bit_size_of Γ τ'')
    (bit_size_of Γ τ' - ref_seg_object_offset Γ rs)), <-take_take,
    take_drop_commute, le_plus_minus_r by lia.
  by erewrite <-(mask_mask _ pbit_indetify), <-take_mask, <-drop_mask,
    IH, ctree_lookup_seg_flatten by eauto using type_mask_ref_seg.
Qed.
Lemma ctree_lookup_seg_disjoint Γ m1 m2 w1 w2 τ rs w1' w2' :
  ✓ Γ → (Γ,m1) ⊢ w1 : τ → (Γ,m2) ⊢ w2 : τ → w1 ⊥ w2 →
  w1 !!{Γ} rs = Some w1' → w2 !!{Γ} rs = Some w2' → w1' ⊥ w2'.
Proof.
  intros ? Hw1 Hw2 Hw' Hrs1 Hrs2. destruct Hw', rs;
    pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs1); clear Hrs1;
    pattern w2'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs2); clear Hrs2;
    intros; decompose_Forall_hyps';
    eauto using ctree_unflatten_disjoint, @ctree_flatten_disjoint.
  * apply (ctree_typed_inv_l _ _ _ _ _ Hw2); intros; simplify_equality.
    rewrite take_app_alt by (erewrite Forall2_length by eauto; auto).
    eauto using ctree_flatten_unflatten_disjoint.
  * apply (ctree_typed_inv_l _ _ _ _ _ Hw1); intros; simplify_equality.
    rewrite take_app_alt by (erewrite <-Forall2_length by eauto; auto).
    symmetry; eauto using ctree_flatten_unflatten_disjoint.
Qed.
Lemma ctree_lookup_disjoint Γ m1 m2 w1 w2 τ r w1' w2' :
  ✓ Γ → (Γ,m1) ⊢ w1 : τ → (Γ,m2) ⊢ w2 : τ → w1 ⊥ w2 →
  w1 !!{Γ} r = Some w1' → w2 !!{Γ} r = Some w2' → w1' ⊥ w2'.
Proof.
  intros ??. revert w1' w2'. induction r as [|rs r]; intros w1'' w2''.
  { by intros; simplify_equality'. }
  rewrite !list_path_lookup_cons; intros. destruct (w1 !!{Γ} r) as [w1'|] eqn:?,
    (w2 !!{Γ} r) as [w2'|] eqn:?; simplify_equality'.
  destruct (ctree_lookup_Some Γ m1 w1 τ r w1') as (σ1&?&?); auto.
  destruct (ctree_lookup_Some Γ m2 w2 τ r w2') as (σ1'&?&?); auto.
  simplify_type_equality; eauto using ctree_lookup_seg_disjoint.
Qed.
Lemma ctree_lookup_seg_subseteq Γ w1 w2 rs w1' :
  ✓ Γ → w1 ⊆ w2 → w1 !!{Γ} rs = Some w1' → ¬ctree_Forall sep_unmapped w1' →
  ∃ w2', w2 !!{Γ} rs = Some w2' ∧ w1' ⊆ w2'.
Proof.
  intros ? Hw' Hrs1. destruct Hw', rs;
    pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs1); clear Hrs1;
    intros; decompose_Forall_hyps; eauto 1.
  * simplify_option_equality; eauto.
  * simplify_option_equality; eauto.
  * simplify_option_equality; eauto.
  * simplify_option_equality by eauto using @seps_unshared_weaken,
      @ctree_unshared_weaken; eexists; split;
      eauto using ctree_unflatten_subseteq, @ctree_flatten_subseteq.
  * simplify_option_equality by eauto using @seps_unshared_weaken;
      eexists; split; eauto; eauto using ctree_unflatten_subseteq.
  * exfalso; naive_solver
      eauto using ctree_unflatten_Forall_le, pbit_unmapped_indetify.
Qed.
Lemma ctree_lookup_subseteq Γ w1 w2 r w1' :
  ✓ Γ → w1 ⊆ w2 → w1 !!{Γ} r = Some w1' → ¬ctree_Forall sep_unmapped w1' →
  ∃ w2', w2 !!{Γ} r = Some w2' ∧ w1' ⊆ w2'.
Proof.
  intros ?. revert w1'. induction r as [|rs r IH]; intros w1'' w2''.
  { intros; simplify_equality'. by exists w2. }
  rewrite !list_path_lookup_cons; intros.
  destruct (w1 !!{Γ} r) as [w1'|] eqn:?; simplify_equality'.
  destruct (IH w1') as (?&->&?);
    eauto using ctree_lookup_seg_Forall, pbit_unmapped_indetify; simpl.
  eauto using ctree_lookup_seg_subseteq.
Qed.

(** ** Alter operation *)
Lemma ctree_alter_nil Γ g : ctree_alter Γ g [] = g.
Proof. done. Qed.
Lemma ctree_alter_cons Γ g rs r :
  ctree_alter Γ g (rs :: r) = ctree_alter Γ (ctree_alter_seg Γ g rs) r.
Proof. done. Qed.
Lemma ctree_alter_singleton Γ g rs :
  ctree_alter Γ g [rs] = ctree_alter_seg Γ g rs.
Proof. done. Qed.
Lemma ctree_alter_app Γ g w r1 r2 :
  ctree_alter Γ g (r1 ++ r2) w = ctree_alter Γ (ctree_alter Γ g r1) r2 w.
Proof.
  revert g. induction r1; simpl; intros; rewrite ?ctree_alter_cons; auto.
Qed.
Lemma ctree_alter_snoc Γ g w r rs :
  ctree_alter Γ g (r ++ [rs]) w = ctree_alter_seg Γ (ctree_alter Γ g r) rs w.
Proof. apply ctree_alter_app. Qed.
Lemma ctree_alter_seg_freeze Γ q g rs :
  ctree_alter_seg Γ g (freeze q rs) = ctree_alter_seg Γ g rs.
Proof. by destruct rs. Qed.
Lemma ctree_alter_freeze Γ q g r :
  ctree_alter Γ g (freeze q <$> r) = ctree_alter Γ g r.
Proof.
  revert g. induction r as [|rs r IH]; intros g; simpl; [done |].
  by rewrite IH, ctree_alter_seg_freeze.
Qed.
Lemma ctree_alter_seg_ext Γ g1 g2 w rs :
  (∀ w', g1 w' = g2 w') → ctree_alter_seg Γ g1 rs w = ctree_alter_seg Γ g2 rs w.
Proof.
  intros. destruct rs, w; simpl; unfold default; simplify_option_equality;
    repeat case_match; f_equal; auto using list_fmap_ext, list_alter_ext.
  by apply list_alter_ext; [intros [??] ?; f_equal'; auto|].
Qed.
Lemma ctree_alter_ext Γ g1 g2 w r :
  (∀ w, g1 w = g2 w) → ctree_alter Γ g1 r w = ctree_alter Γ g2 r w.
Proof.
  intros. revert w. induction r as [|rs r IH] using rev_ind; intros w; [done|].
  rewrite !ctree_alter_snoc. by apply ctree_alter_seg_ext.
Qed.
Lemma ctree_alter_seg_compose Γ g1 g2 w rs :
  ctree_alter_seg Γ (g1 ∘ g2) rs w
  = ctree_alter_seg Γ g1 rs (ctree_alter_seg Γ g2 rs w).
Proof.
  destruct w as [| |s wxbss| |], rs as [i|i|i]; simpl; unfold default;
    repeat (simplify_option_equality || case_match);
    f_equal; auto using list_alter_compose, list_fmap_compose.
  rewrite <-list_alter_compose. by apply list_alter_ext.
Qed.
Lemma ctree_alter_compose Γ g1 g2 w r :
  ctree_alter Γ (g1 ∘ g2) r w = ctree_alter Γ g1 r (ctree_alter Γ g2 r w).
Proof.
  intros. revert w. induction r as [|rs r IH] using rev_ind; intros w; [done|].
  rewrite !ctree_alter_snoc, <-ctree_alter_seg_compose.
  by apply ctree_alter_seg_ext.
Qed.
Lemma ctree_alter_seg_commute Γ g1 g2 w rs1 rs2 :
  rs1 ⊥ rs2 → ctree_alter_seg Γ g1 rs1 (ctree_alter_seg Γ g2 rs2 w)
  = ctree_alter_seg Γ g2 rs2 (ctree_alter_seg Γ g1 rs1 w).
Proof.
  destruct 1 as [|i1 i2 ? Hi], w as [| |? wxbss| |]; intros;
    simplify_option_equality; f_equal; auto using list_alter_commute.
Qed.
Lemma ctree_alter_commute Γ g1 g2 w r1 r2 :
  r1 ⊥ r2 → ctree_alter Γ g1 r1 (ctree_alter Γ g2 r2 w)
  = ctree_alter Γ g2 r2 (ctree_alter Γ g1 r1 w).
Proof.
  rewrite ref_disjoint_alt. intros (r1'&rs1'&r1''&r2'&rs2'&r2''&->&->&?&Hr).
  rewrite !ctree_alter_app, !ctree_alter_singleton.
  rewrite <-!(ctree_alter_freeze _ true _ r1''), !Hr, !ctree_alter_freeze.
  rewrite <-!ctree_alter_compose. apply ctree_alter_ext; intros w'; simpl; auto.
  by apply ctree_alter_seg_commute.
Qed.
Lemma ctree_alter_lookup_seg_Forall (P : pbit Ti → Prop) Γ g w rs w' :
  ctree_Forall P (ctree_alter_seg Γ g rs w) →
  w !!{Γ} rs = Some w' → ctree_Forall P (g w').
Proof.
  intros Hgw Hrs. destruct w as [|τ ws|s wxbss|s i w xbs|], rs as [i'|i'|i'];
    pattern w'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear w' Hrs.
  * intros w -> -> Hw; simplify_equality'; rewrite Forall_bind in Hgw.
    apply (Forall_lookup_1 (λ w, ctree_Forall P w) (alter g i' ws) i'); auto.
    by rewrite list_lookup_alter, Hw.
  * intros w xbs -> Hwxbs; simplify_equality'; rewrite Forall_bind in Hgw.
    assert (alter (prod_map g id) i' wxbss !! i' = Some (g w, xbs)).
    { by rewrite list_lookup_alter, Hwxbs. }
    by decompose_Forall_hyps'.
  * by intros; simplify_option_equality; decompose_Forall_hyps'.
  * by intros; simplify_option_equality; decompose_Forall_hyps'.
  * by intros; simplify_option_equality; decompose_Forall_hyps'.
Qed.
Lemma ctree_alter_lookup_Forall (P : pbit Ti → Prop) Γ g w r w' :
  ctree_Forall P (ctree_alter Γ g r w) →
  w !!{Γ} r = Some w' → ctree_Forall P (g w').
Proof.
  revert g w. induction r as [|rs r IH] using @rev_ind.
  { intros g w. rewrite list_path_lookup_nil. naive_solver. }
  intros g w. rewrite ctree_alter_snoc, list_path_lookup_snoc.
  intros. destruct (w !!{Γ} rs) as [w''|] eqn:Hw''; simplify_equality'.
  eauto using ctree_alter_lookup_seg_Forall.
Qed.
Lemma ctree_alter_seg_unmapped Γ m g w rs τ w' :
  ✓ Γ → (Γ,m) ⊢ w : τ → ctree_unmapped (ctree_alter_seg Γ g rs w) →
  w !!{Γ} rs = Some w' → ctree_unmapped (g w').
Proof.
  intros HΓ Hw Hgw Hrs; destruct rs as [i|i|i]; destruct Hw
    as [|ws τ|s wxbss τs| |] using @ctree_typed_case;
    pattern w'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
  * intros w _ ??; simplify_option_equality; rewrite Forall_bind in Hgw.
    cut (alter g i ws !! i = Some (g w)); [by intros; decompose_Forall_hyps|].
    rewrite list_lookup_alter. by simplify_option_equality.
  * intros w xbs -> ?; simplify_option_equality; rewrite Forall_bind in Hgw.
    assert (alter (prod_map g id) i wxbss !! i = Some (g w, xbs)).
    { rewrite list_lookup_alter. by simplify_option_equality. }
    by decompose_Forall_hyps'.
  * by intros; simplify_option_equality; decompose_Forall_hyps'.
  * by intros; simplify_option_equality; decompose_Forall_hyps'.
  * by intros; simplify_option_equality; decompose_Forall_hyps'.
Qed.
Lemma ctree_alter_unmapped Γ m g w r τ w' :
  ✓ Γ → (Γ,m) ⊢ w : τ → ctree_unmapped (ctree_alter Γ g r w) →
  w !!{Γ} r = Some w' → ctree_unmapped (g w').
Proof.
  intros HΓ. revert g τ w. induction r as [|rs r IH] using @rev_ind.
  { intros g τ w. rewrite list_path_lookup_nil. naive_solver. }
  intros g τ w. rewrite ctree_alter_snoc, list_path_lookup_snoc; intros.
  destruct (w !!{Γ} rs) as [w''|] eqn:?; simplify_equality'.
  destruct (ctree_lookup_seg_Some Γ m w τ rs w'') as (?&_&?);
    eauto using ctree_alter_seg_unmapped.
Qed.
Lemma ctree_alter_seg_typed Γ m g w rs τ w' :
  ✓ Γ → (Γ,m) ⊢ w : τ → w !!{Γ} rs = Some w' →
  (Γ,m) ⊢ g w' : type_of w' → ¬ctree_unmapped (g w') →
  (Γ,m) ⊢ ctree_alter_seg Γ g rs w : τ.
Proof.
  intros HΓ Hw Hrs. destruct rs as [i|i|i]; destruct Hw
    as [|ws τ|s wxbss τs ??? Hindet Hlen| |] using @ctree_typed_case;
    pattern w'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
  * intros; simplify_option_equality.
    ctree_typed_constructor; auto using alter_length.
    apply (Forall_alter _ g _ i); auto. by intros; simplify_type_equality'.
  * intros; simplify_option_equality. ctree_typed_constructor; eauto.
    + apply Forall2_alter_l; auto 1. by intros [] ????; simplify_type_equality'.
    + apply Forall_alter; auto.
    + apply Forall_alter; auto.
    + rewrite <-Hlen. generalize i. elim wxbss; [done|].
      intros [??] wxbss' ? [|?]; f_equal'; auto.
  * intros; simplify_option_equality. ctree_typed_constructor; eauto.
    + by simplify_type_equality.
    + intuition.
  * intros ? τ'; intros; simplify_option_equality.
    ctree_typed_constructor; eauto using pbits_indetify_idempotent.
    + erewrite <-ctree_unflatten_type_of by eauto; eauto.
    + eauto using pbits_indetify_valid, ctree_flatten_valid.
    + erewrite fmap_length, drop_length,
        app_length, ctree_flatten_length by eauto; solve_length.
    + by intros [? _].
  * intros ? τ'; intros; simplify_option_equality.
    ctree_typed_constructor; eauto using
      pbits_indetify_valid, pbits_indetify_idempotent.
    + erewrite <-ctree_unflatten_type_of by eauto; eauto.
    + solve_length.
    + by intros [? _].
Qed.
Lemma ctree_alter_typed Γ m g w r τ w' :
  ✓ Γ → (Γ,m) ⊢ w : τ → w !!{Γ} r = Some w' →
  (Γ,m) ⊢ g w' : type_of w' → ¬ctree_unmapped (g w') →
  (Γ,m) ⊢ ctree_alter Γ g r w : τ.
Proof.
  intros HΓ. revert g τ w. induction r as [|rs r IH] using @rev_ind.
  { by intros; simplify_type_equality'. }
  intros g τ w; rewrite ctree_alter_snoc, list_path_lookup_snoc; intros.
  destruct (w !!{Γ} rs) as [w''|] eqn:?; simplify_equality'.
  destruct (ctree_lookup_seg_Some Γ m w τ rs w'') as (?&_&?); eauto.
  eapply ctree_alter_seg_typed;
    eauto using ctree_lookup_seg_typed, ctree_alter_unmapped, type_of_typed.
Qed.
Lemma ctree_alter_seg_type_of Γ g w rs :
  (∀ w', type_of (g w') = type_of w') →
  type_of (ctree_alter_seg Γ g rs w) = type_of w.
Proof.
  intros; destruct w as [|[]| | |], rs as [[]| |];
    simpl; unfold default; repeat (simplify_option_equality || case_match);
    f_equal'; rewrite ?alter_length; auto.
Qed.
Lemma ctree_alter_type_of Γ g w r :
  (∀ w', type_of (g w') = type_of w') →
  type_of (ctree_alter Γ g r w) = type_of w.
Proof. revert g w. induction r; simpl; auto using ctree_alter_seg_type_of. Qed.
Lemma ctree_alter_seg_type_of_weak Γ m g w rs τ w' :
  (Γ,m) ⊢ w : τ → w !!{Γ} rs = Some w' →
  type_of (g w') = type_of w' → type_of (ctree_alter_seg Γ g rs w) = τ.
Proof.
  intros Hw Hrs. destruct rs as [[]| |];
    destruct Hw as [|?? []| | |] using @ctree_typed_case;
    pattern w'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs; intros;
    simplify_option_equality; simplify_type_equality; by rewrite ?alter_length.
Qed.
Lemma ctree_alter_type_of_weak Γ m g w r τ w' :
  ✓ Γ → (Γ,m) ⊢ w : τ → w !!{Γ} r = Some w' →
  type_of (g w') = type_of w' → type_of (ctree_alter Γ g r w) = τ.
Proof.
  revert g τ w. induction r as [|rs r IH] using @rev_ind.
  { by intros; simplify_type_equality'. }
  intros g τ w; rewrite ctree_alter_snoc, list_path_lookup_snoc; intros.
  destruct (w !!{Γ} rs) as [w''|] eqn:?; simplify_equality'.
  destruct (ctree_lookup_seg_Some Γ m w τ rs w'') as (?&_&?); eauto.
  eapply ctree_alter_seg_type_of_weak; eauto using type_of_typed.
Qed.
Lemma ctree_lookup_alter_seg_freeze Γ g w rs w' :
  ✓ Γ → w !!{Γ} freeze false rs = Some w' →
  ctree_alter_seg Γ g rs w !!{Γ} freeze true rs = Some (g w').
Proof.
  destruct w, rs; intros; simplify_option_equality; try done.
  * rewrite list_lookup_alter. simplify_option_equality. done.
  * exfalso. eauto using alter_length.
  * rewrite list_lookup_alter. by simplify_option_equality.
Qed.
Lemma ctree_lookup_alter_freeze Γ g w r w' :
  ✓ Γ → w !!{Γ} (freeze false <$> r) = Some w' →
  ctree_alter Γ g r w !!{Γ} (freeze true <$> r) = Some (g w').
Proof.
  intros HΓ. revert g w. induction r as [|rs r IH] using rev_ind; simpl.
  { intros g w. rewrite !list_path_lookup_nil. congruence. }
  intros g w. rewrite !fmap_app, !fmap_cons, !fmap_nil, !ctree_alter_snoc,
    !list_path_lookup_snoc; intros; simplify_option_equality.
  erewrite ctree_lookup_alter_seg_freeze by eauto; eauto.
Qed.
Lemma ctree_lookup_alter Γ g w r1 r2 w' :
  ✓ Γ → w !!{Γ} (freeze false <$> r1) = Some w' →
  freeze true <$> r1 = freeze true <$> r2 →
  ctree_alter Γ g r2 w !!{Γ} r1 = Some (g w').
Proof.
  intros ?? Hr. apply ctree_lookup_freeze; rewrite Hr.
  eapply ctree_lookup_alter_freeze; eauto using ctree_lookup_unfreeze.
  by rewrite <-(ref_freeze_freeze _ true), <-Hr, ref_freeze_freeze.
Qed.
Lemma ctree_lookup_alter_seg_inv Γ m g w rs τ σ w' :
  ✓ Γ → (Γ,m) ⊢ w : τ → Γ ⊢ rs : τ ↣ σ →
  ctree_alter_seg Γ g rs w !!{Γ} rs = Some w' →
  ∃ w'', w' = g w'' ∧ (Γ,m) ⊢ w'' : σ.
Proof.
  intros ? Hw. destruct 1 as [τ i|s i τs|s i q τs τ];
    pattern w; apply (ctree_typed_inv_r _ _ _ _ _ Hw); clear w Hw.
  * intros ws -> ?? Hw'.
    simplify_option_equality; rewrite list_lookup_alter in Hw'.
    destruct (ws !! i) as [w''|] eqn:?; simplify_equality'.
    exists w''; split; auto. eapply (Forall_lookup_1 (λ w', _ ⊢ w' : _)); eauto.
  * intros wxbss ?????? Hw'; simplify_equality'; case_option_guard; try done.
    rewrite list_lookup_alter in Hw'.
    destruct (wxbss !! i) as [[w'' xbs]|] eqn:?; simplify_equality'.
    exists w''; split; auto. by decompose_Forall_hyps.
  * intros; simplify_option_equality;
      eauto 8 using ctree_unflatten_typed, ctree_flatten_valid.
  * intros; simplify_option_equality; eauto 7 using ctree_unflatten_typed.
Qed.
Lemma ctree_lookup_alter_inv Γ m g w r τ σ w' :
  ✓ Γ → (Γ,m) ⊢ w : τ → Γ ⊢ r : τ ↣ σ →
  ctree_alter Γ g r w !!{Γ} r = Some w' →
  ∃ w'', w' = g w'' ∧ (Γ,m) ⊢ w'' : σ.
Proof.
  intros ? Hw Hr. revert g w w' Hw.
  induction Hr as [|r rs ????? IH] using @list_typed_ind.
  { intros ? w ???; simplify_equality. by exists w. }
  intros g w w' Hw'. rewrite ctree_alter_cons, list_path_lookup_cons; intros.
  destruct (ctree_alter Γ (ctree_alter_seg Γ g rs) r w !!{Γ} r)
    as [w''|] eqn:Hw''; simplify_equality'.
  apply IH in Hw''; auto; destruct Hw'' as (w'''&->&?).
  eauto using ctree_lookup_alter_seg_inv.
Qed.
Lemma ctree_lookup_alter_seg_disjoint Γ g w rs1 rs2 :
  rs1 ⊥ rs2 → ctree_alter_seg Γ g rs2 w !!{Γ} rs1 = w !!{Γ} rs1.
Proof.
  destruct w; destruct 1; simplify_option_equality; auto.
  * by rewrite list_lookup_alter_ne.
  * exfalso; auto using alter_length.
  * exfalso; auto using alter_length.
  * by rewrite list_lookup_alter_ne by done.
Qed.
Lemma ctree_lookup_alter_disjoint Γ g w r1 r2 w' :
  ✓ Γ → r1 ⊥ r2 → w !!{Γ} r1 = Some w' →
  ctree_alter Γ g r2 w !!{Γ} r1 = Some w'.
Proof.
  intros HΓ. rewrite ref_disjoint_alt. intros (r1'&rs1&r&r2'&rs2&r'&->&->&?&Hr).
  rewrite !ctree_alter_app, !list_path_lookup_app,
    !ctree_alter_singleton, !list_path_lookup_singleton; intros.
  destruct (w !!{_} r) as [w1'|] eqn:Hw1'; simplify_equality'.
  destruct (w1' !!{_} rs1) as [w2'|] eqn:Hw2'; simplify_equality'.
  erewrite ctree_lookup_alter by eauto using ctree_lookup_unfreeze; simpl.
  by rewrite ctree_lookup_alter_seg_disjoint, Hw2' by done.
Qed.
Lemma ctree_alter_seg_ext_lookup Γ g1 g2 w rs w' :
  w !!{Γ} rs = Some w' → g1 w' = g2 w' →
  ctree_alter_seg Γ g1 rs w = ctree_alter_seg Γ g2 rs w.
Proof.
  destruct w, rs; intros Hrs;
    pattern w'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs;
    intros; simplify_option_equality; f_equal; auto.
  * apply list_alter_ext; naive_solver.
  * apply list_alter_ext; auto 1. by intros [] ?; simplify_equality'; f_equal.
Qed.
Lemma ctree_alter_ext_lookup Γ g1 g2 w r w' :
  w !!{Γ} r = Some w' → g1 w' = g2 w' →
  ctree_alter Γ g1 r w = ctree_alter Γ g2 r w.
Proof.
  revert g1 g2 w'. induction r as [|rs r]; simpl; intros g1 g2 w'.
  { by intros; simplify_equality'. }
  rewrite list_path_lookup_cons; intros; simplify_option_equality;
    eauto using ctree_alter_seg_ext_lookup.
Qed.
Lemma ctree_alter_seg_disjoint Γ m g w1 w2 τ rs w1' :
  ✓ Γ → (Γ,m) ⊢ w1 : τ →
  w1 ⊥ w2 → w1 !!{Γ} rs = Some w1' → ¬ctree_unmapped (g w1') →
  (∀ w2', w1' ⊥ w2' → g w1' ⊥ w2') → ctree_alter_seg Γ g rs w1 ⊥ w2.
Proof.
  intros ? Hw1 Hw Hw1' Hrs. revert w1 w2 Hw Hw1 Hw1' Hrs.
  refine (ctree_disjoint_ind _ _ _ _ _ _ _ _).
  * by destruct rs.
  * intros τ' ws1 ws2 ? _ ? Hrs Hg. destruct rs; simplify_option_equality.
    constructor. apply Forall2_alter_l; auto 1.
    intros; decompose_Forall_hyps'; eauto.
  * intros s wxbss1 wxbss2 Hws Hxbss _ Hrs; destruct rs as [|i|];
      pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    intros w1 xbs -> ? _ ?; simpl; constructor.
    + apply Forall2_alter_l; [elim Hws; constructor; simpl; eauto|].
      intros [??] [??] ??; decompose_Forall_hyps'; eauto.
    + apply Forall2_alter_l; [elim Hxbss; constructor; simpl; eauto|].
      intros [??] [??] ??; decompose_Forall_hyps'; eauto.
  * intros s i w1 w2 xbs1 xbs2 ? _ ??  Hum ? Hrs; destruct rs as [| |i'];
      pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    { intros; simplify_option_equality. constructor; naive_solver. }
    intros τs τ' ???????; destruct Hum; simplify_equality'.
    eauto using @seps_unshared_unmapped, @ctree_flatten_disjoint.
  * intros s xbs1 xbs2 ? _ Hrs; destruct rs as [| |i'];
      pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    intros τs τ' ??????; simplify_option_equality. constructor.
    + rewrite <-(take_drop (bit_size_of Γ τ') xbs2); apply Forall2_app.
      { erewrite <-pbits_indetify_mask_unmapped, <-(ctree_flatten_unflatten_le
          Γ τ') by eauto using @seps_unshared_unmapped.
        eauto using @ctree_flatten_disjoint, ctree_unflatten_disjoint. }
      erewrite <-pbits_indetify_unmapped by eauto using @seps_unshared_unmapped.
      eauto using pbits_indetify_disjoint.
    + eauto using @seps_unshared_unmapped.
    + eapply ctree_disjoint_valid_l;
        eauto using ctree_flatten_disjoint, ctree_unflatten_disjoint.
    + naive_solver.
  * intros s i xbs1 w2 xbs2 ??? Hum _ Hrs; destruct rs as [| |i'];
      pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    intros τs τ' ????; destruct Hum; simplify_equality.
    rewrite <-Forall_app; eauto using @seps_unshared_unmapped.
  * intros s i w1 xbs1 xbs2 Hxbs2 ??? Hw1 Hrs;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw1); clear Hw1 τ;
      intros τs τ ??? _ ? _; destruct rs as [| |i'];
      pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    { rewrite Forall2_app_inv_l in Hxbs2;
        destruct Hxbs2 as (xbs2'&xbs2''&?&?&->).
      intros ???? Hw; simplify_option_equality; decompose_Forall_hyps.
      constructor; auto.
      + apply Forall2_app; auto.
        erewrite <-(pbits_indetify_mask_unmapped (type_mask Γ τ) xbs2'),
          <-(ctree_flatten_unflatten Γ τ xbs2') by
          (erewrite <-?(Forall2_length _ (ctree_flatten _)) by eauto; eauto).
        apply ctree_flatten_disjoint, Hw.
        symmetry; eauto using ctree_flatten_unflatten_disjoint.
      + eapply ctree_disjoint_valid_l, Hw.
        symmetry; eauto using ctree_flatten_unflatten_disjoint.
      + naive_solver. }
    intros ? τ' ?????????; simplify_option_equality. constructor; auto.
    + rewrite <-(take_drop (bit_size_of Γ τ') xbs2); apply Forall2_app; auto.
      { erewrite <-pbits_indetify_mask_unmapped, <-(ctree_flatten_unflatten_le
          Γ τ') by eauto using @seps_unshared_unmapped.
        eauto using @ctree_flatten_disjoint, ctree_unflatten_disjoint. }
      erewrite <-pbits_indetify_unmapped by eauto using @seps_unshared_unmapped.
      eauto using pbits_indetify_disjoint.
    + eapply ctree_disjoint_valid_l;
        eauto using ctree_flatten_disjoint, ctree_unflatten_disjoint.
    + naive_solver.
Qed.
Lemma ctree_alter_disjoint Γ m g w1 w2 τ r w1' :
  ✓ Γ → (Γ,m) ⊢ w1 : τ →
  w1 ⊥ w2 → w1 !!{Γ} r = Some w1' → ¬ctree_unmapped (g w1') →
  (∀ w2', w1' ⊥ w2' → g w1' ⊥ w2') → ctree_alter Γ g r w1 ⊥ w2.
Proof.
  intros ??. revert g w1'. induction r as [|rs r]; intros g w1''.
  { intros; simplify_equality'; eauto. }
  rewrite !list_path_lookup_cons; intros.
  destruct (w1 !!{Γ} r) as [w1'|] eqn:?; simplify_equality'.
  destruct (ctree_lookup_Some Γ m w1 τ r w1') as (σ1&?&?);
    eauto 8 using ctree_alter_seg_unmapped, ctree_alter_seg_disjoint.
Qed.
Lemma ctree_alter_seg_union Γ m g w1 w2 τ rs w1' :
  ✓ Γ → (Γ,m) ⊢ w1 : τ →
  w1 ⊥ w2 → w1 !!{Γ} rs = Some w1' → ¬ctree_unmapped (g w1') →
  (∀ w2', w1' ⊥ w2' → g w1' ⊥ w2') →
  (∀ w2', w1' ⊥ w2' → g (w1' ∪ w2') = g w1' ∪ w2') →
  ctree_alter_seg Γ g rs (w1 ∪ w2) = ctree_alter_seg Γ g rs w1 ∪ w2.
Proof.
  intros ? Hw1 Hw Hw1' Hrs. revert w1 w2 Hw Hw1 Hw1' Hrs.
  refine (ctree_disjoint_ind _ _ _ _ _ _ _ _).
  * by destruct rs.
  * intros τ' ws1 ws2 Hws _ Hrs  _ Hg Hg'.
    destruct rs as [i| |]; simplify_option_equality. f_equal. revert i Hrs.
    induction Hws; intros [|?] ?; simplify_equality'; f_equal'; eauto.
  * intros s wxbss1 wxbss2 Hws _ _ Hrs; destruct rs as [|i|];
      pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    intros w1 xbs -> Hrs _ Hg Hg'; f_equal'. revert i Hrs.
    induction Hws as [|[] []]; intros [|?] ?;
      simplify_equality'; repeat f_equal'; eauto.
  * intros s i w1 w2 xbs1 xbs2 ? _ ??  Hum ? Hrs; destruct rs as [| |i'];
      pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    { intros; simplify_option_equality; f_equal; auto. }
    intros τs τ' ???????; destruct Hum; simplify_equality'.
    eauto using @seps_unshared_unmapped, @ctree_flatten_disjoint.
  * intros s xbs1 xbs2 ? Hw1 Hrs;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw1); clear Hw1 τ;
      intros τs ??? _; destruct rs as [| |i'];
      pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    intros ?????? Hg Hg'; simplify_option_equality.
    erewrite Forall2_length by (eapply ctree_flatten_disjoint,
      Hg, ctree_unflatten_disjoint; eauto).
    rewrite ctree_flatten_unflatten_le, mask_length, take_length_le by eauto.
    f_equal.
    + by rewrite zip_with_take, ctree_unflatten_union, Hg', <-ctree_merge_flatten,
        ctree_flatten_unflatten_le, pbits_indetify_mask_unmapped
        by eauto using ctree_unflatten_Forall_le, ctree_unflatten_disjoint,
          @seps_unshared_unmapped, pbit_unmapped_indetify.
    + by rewrite zip_with_drop, pbits_indetify_union, (pbits_indetify_unmapped
        (drop _ xbs2)) by eauto using @seps_unshared_unmapped.
  * intros s i xbs1 w2 xbs2 ??? Hum _ Hrs; destruct rs as [| |i'];
      pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    intros τs τ' ????; destruct Hum; simplify_equality.
    rewrite <-Forall_app; eauto using @seps_unshared_unmapped.
  * intros s i w1 xbs1 xbs2 Hxbs2 ??? Hw1 Hrs;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw1); clear Hw1 τ;
      intros τs τ ?? Hw1 _ ??; destruct rs as [| |i'];
      pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    { rewrite Forall2_app_inv_l in Hxbs2;
        destruct Hxbs2 as (xbs2'&xbs2''&?&?&->).
      intros ???? Hg Hg'; simplify_option_equality; decompose_Forall_hyps.
      assert (length xbs2' = bit_size_of Γ τ).
      { erewrite <-Forall2_length by eauto. solve_length. }
      assert (w1 ⊥ ctree_unflatten Γ τ xbs2').
      { symmetry; eauto using ctree_flatten_unflatten_disjoint. }
      assert (ctree_flatten (g w1) ⊥* xbs2').
      { rewrite <-(pbits_indetify_mask_unmapped (type_mask Γ τ) xbs2'),
          <-ctree_flatten_unflatten by eauto.
        by apply ctree_flatten_disjoint, Hg. }
      clear Hw1. rewrite !take_app_alt, !drop_app_alt by auto.
      rewrite <-(pbits_indetify_mask_unmapped (type_mask Γ τ) xbs2'),
        <-ctree_flatten_unflatten, !ctree_merge_flatten
        by eauto using ctree_unflatten_Forall_le, pbit_unmapped_indetify.
      f_equal; auto. }
    intros ? τ' ????????? Hg Hg'; simplify_option_equality.
    assert (length xbs2 = bit_size_of Γ (unionT s)).
    { by erewrite <-Forall2_length by eauto. }
    rewrite ctree_flatten_merge, <-zip_with_app,
      zip_with_take, zip_with_drop, take_drop by done.
    erewrite Forall2_length
      by (eapply ctree_flatten_disjoint, Hg, ctree_unflatten_disjoint; eauto).
    rewrite ctree_flatten_unflatten_le, mask_length, take_length_le by eauto.
    f_equal.
    + by rewrite ctree_unflatten_union, Hg', <-ctree_merge_flatten,
        ctree_flatten_unflatten, pbits_indetify_mask_unmapped
        by eauto using ctree_unflatten_Forall_le, ctree_unflatten_disjoint,
        @seps_unshared_unmapped, pbit_unmapped_indetify.
    + by rewrite pbits_indetify_union,
       (pbits_indetify_unmapped (drop _ xbs2)) by auto.
Qed.
Lemma ctree_alter_union Γ m g w1 w2 τ r w1' :
  ✓ Γ → (Γ,m) ⊢ w1 : τ →
  w1 ⊥ w2 → w1 !!{Γ} r = Some w1' → ¬ctree_unmapped (g w1') →
  (∀ w2', w1' ⊥ w2' → g w1' ⊥ w2') →
  (∀ w2', w1' ⊥ w2' → g (w1' ∪ w2') = g w1' ∪ w2') →
  ctree_alter Γ g r (w1 ∪ w2) = ctree_alter Γ g r w1 ∪ w2.
Proof.
  intros ??. revert g w1'. induction r as [|rs r IH]; intros g w1''.
  { intros; simplify_equality'; eauto. }
  rewrite !list_path_lookup_cons; intros.
  destruct (w1 !!{Γ} r) as [w1'|] eqn:?; simplify_equality'.
  destruct (ctree_lookup_Some Γ m w1 τ r w1') as (σ1&?&?); auto.
  eapply IH; eauto using ctree_alter_seg_unmapped,
    ctree_alter_seg_disjoint, ctree_alter_seg_union.
Qed.

(** ** Non-aliasing resuls *)
Lemma ctree_lookup_non_aliasing_help Γ m g w τ s τs r τ1 i1 τ2 i2 :
  let r1' := RUnion i1 s true :: r in
  let r2' := RUnion i2 s true :: r in
  ✓ Γ → (Γ,m) ⊢ w : τ → Γ ⊢ r : τ ↣ unionT s → Γ !! s = Some τs →
  τs !! i1 = Some τ1 → τs !! i2 = Some τ2 →
  i1 ≠ i2 → ctree_alter Γ g r1' w !!{Γ} r2' = None.
Proof.
  intros r1' r2' ? Hwτ Hw Hr ?? Hi. unfold r1', r2'; clear r1' r2'.
  rewrite !ctree_alter_cons, !list_path_lookup_cons.
  destruct (ctree_alter Γ (ctree_alter_seg Γ g
    (RUnion i1 s true)) r w !!{Γ} r) as [w'|] eqn:Hw'; simpl; [|done].
  eapply ctree_lookup_alter_inv in Hw'; eauto. destruct Hw' as (w''&->&?).
  by pattern w''; apply (ctree_typed_inv_r Γ m _ w'' (unionT s));
    intros; simplify_option_equality.
Qed.
Lemma ctree_lookup_non_aliasing Γ m g w τ s r r1 j1 σ1 i1 r2 j2 σ2 i2 :
  let r1' := r1 ++ RUnion i1 s true :: r in
  let r2' := r2 ++ RUnion i2 s true :: r in
  ✓ Γ → (Γ,m) ⊢ w : τ → Γ ⊢ r1' : τ ↣ σ1 → Γ ⊢ r2' : τ ↣ σ2 → i1 ≠ i2 →
  ctree_alter Γ g (ref_set_offset j1 r1') w
    !!{Γ} (ref_set_offset j2 r2') = None.
Proof.
  assert (∀ j r3 i3, ref_set_offset j (r3 ++ RUnion i3 s true :: r) =
    ref_set_offset j r3 ++ RUnion i3 s true :: r) as Hrhelp.
  { by intros ? [|??] ?. }
  intros r1' r2' HΓ; unfold r1', r2'; clear r1' r2'.
  rewrite !Hrhelp, !list_typed_app; setoid_rewrite list_typed_cons.
  intros Hwτ (τ1&(τ'&?&Hr1)&?) (τ2&(τ''&?&Hr2)&?) Hi; simplify_type_equality.
  inversion Hr1; inversion Hr2; simplify_option_equality.
  rewrite list_path_lookup_app, ctree_alter_app, bind_None; left.
  eauto using ctree_lookup_non_aliasing_help.
Qed.

(** ** Looking up individual bytes *)
Lemma ctree_lookup_byte_typed Γ m w τ i c :
  ✓ Γ → (Γ,m) ⊢ w : τ → w !!{Γ} i = Some c → (Γ,m) ⊢ c : ucharT.
Proof.
  unfold lookupE, ctree_lookup_byte; intros; simplify_option_equality.
  apply ctree_unflatten_typed; eauto using TBase_valid, TInt_valid,
    Forall_sublist_lookup, ctree_flatten_valid.
Qed.
Lemma ctree_lookup_byte_length Γ m w τ i c :
  ✓ Γ → (Γ,m) ⊢ w : τ → w !!{Γ} i = Some c → i < size_of Γ τ.
Proof.
  unfold lookupE, ctree_lookup_byte, sublist_lookup.
  intros; simplify_option_equality.
  apply (Nat.mul_lt_mono_pos_r (char_bits)); auto using char_bits_pos.
  change (size_of Γ τ * char_bits) with (bit_size_of Γ τ).
  erewrite <-ctree_flatten_length by eauto. pose proof char_bits_pos; lia.
Qed.
Lemma ctree_lookup_byte_Forall (P : pbit Ti → Prop) Γ w i c :
  ✓ Γ → (∀ xb, P xb → P (pbit_indetify xb)) →
  ctree_Forall P w → w !!{Γ} i = Some c → ctree_Forall P c.
Proof.
  unfold lookupE, ctree_lookup_byte; intros; simplify_option_equality.
  eauto using TBase_valid, TInt_valid, Forall_sublist_lookup.
Qed.
Lemma ctree_flatten_mask Γ m w τ :
  ✓ Γ → (Γ,m) ⊢ w : τ → 
  mask pbit_indetify (type_mask Γ τ) (ctree_flatten w) = ctree_flatten w.
Proof.
  intros. rewrite <-ctree_flatten_union_reset at 2.
  by erewrite <-ctree_unflatten_flatten, ctree_flatten_unflatten by eauto.
Qed.
Definition ctree_lookup_byte_after (Γ : env Ti)
    (τ : type Ti) (i : nat) : mtree Ti → mtree Ti :=
  ctree_unflatten Γ ucharT ∘
    mask pbit_indetify (take char_bits (drop (i * char_bits) (type_mask Γ τ))) ∘
    ctree_flatten.
Lemma ctree_lookup_byte_after_spec Γ m w τ i :
  ✓Γ → (Γ,m) ⊢ w : τ → w !!{Γ} i = ctree_lookup_byte_after Γ τ i <$> w !!{Γ} i.
Proof.
  intros. unfold lookupE, ctree_lookup_byte, ctree_lookup_byte_after.
  destruct (sublist_lookup (i * char_bits) _ _) as [xbs|] eqn:?; f_equal'.
  unfold sublist_lookup in *; simplify_option_equality.
  by erewrite <-take_mask, <-drop_mask, ctree_flatten_mask by eauto.
Qed.
Lemma ctree_lookup_byte_ext Γ m w1 w2 τ :
  ✓ Γ → (Γ,m) ⊢ w1 : τ → union_free w1 → (Γ,m) ⊢ w2 : τ → union_free w2 →
  (∀ i, i < size_of Γ τ → w1 !!{Γ} i = w2 !!{Γ} i) → w1 = w2.
Proof.
  intros ????? Hlookup. erewrite <-(union_free_reset w1),
    <-(union_free_reset w2), <-!ctree_unflatten_flatten by eauto.
  f_equal; apply sublist_eq_same_length with (size_of Γ τ) char_bits.
  { by erewrite ctree_flatten_length by eauto. }
  { by erewrite ctree_flatten_length by eauto. }
  intros i Hi. specialize (Hlookup i Hi).
  unfold lookupE, ctree_lookup_byte in Hlookup.
  destruct (sublist_lookup _ _(ctree_flatten w1)) as [bs1|] eqn:?,
    (sublist_lookup _ _(ctree_flatten w2)) as [bs2|] eqn:?; try done.
  apply (injective Some) in Hlookup; rewrite !ctree_unflatten_base in Hlookup.
  congruence.
Qed.
Lemma ctree_lookup_byte_char Γ m w :
  ✓ Γ → (Γ,m) ⊢ w : ucharT → w !!{Γ} 0 = Some w.
Proof.
  intros ? Hw. unfold lookupE, ctree_lookup_byte; simpl.
  rewrite sublist_lookup_all by auto. f_equal'.
  erewrite ctree_unflatten_flatten by eauto. by inversion Hw.
Qed.
Lemma ctree_lookup_reshape Γ m w τ i :
  let szs := replicate (size_of Γ τ) char_bits in
  ✓ Γ → (Γ,m) ⊢ w : τ →
  w !!{Γ} i = ctree_unflatten Γ ucharT <$> reshape szs (ctree_flatten w) !! i.
Proof.
  intros szs ? Hwτ. unfold lookupE at 1, ctree_lookup_byte. unfold szs.
  by rewrite sublist_lookup_reshape
    by (erewrite ?ctree_flatten_length by eauto; eauto using char_bits_pos).
Qed.
Lemma ctree_lookup_byte_disjoint Γ w1 w2 i c1 c2 :
  ✓ Γ → w1 ⊥ w2 → w1 !!{Γ} i = Some c1 → w2 !!{Γ} i = Some c2 → c1 ⊥ c2.
Proof.
  unfold lookupE, ctree_lookup_byte, sublist_lookup; intros;
    simplify_option_equality; auto using ctree_unflatten_disjoint,
    TBase_valid, TInt_valid, @ctree_flatten_disjoint.
Qed.
Lemma ctree_lookup_byte_subseteq Γ w1 w2 i c1 :
  ✓ Γ → w1 ⊆ w2 → w1 !!{Γ} i = Some c1 →
  ∃ c2, w2 !!{Γ} i = Some c2 ∧ c1 ⊆ c2.
Proof.
  unfold lookupE, ctree_lookup_byte. intros.
  destruct (sublist_lookup _ _ (ctree_flatten w1))
    as [xbs1|] eqn:Hbs1; simplify_equality'.
  destruct (Forall2_sublist_lookup_l (⊆) (ctree_flatten w1)
    (ctree_flatten w2) (i * char_bits) char_bits xbs1) as (xbs2&?&?);
    eauto using @ctree_flatten_subseteq.
  exists (ctree_unflatten Γ ucharT xbs2); simplify_option_equality;
    eauto using ctree_unflatten_subseteq, TBase_valid, TInt_valid.
Qed.

(** ** Altering individual bytes *)
Lemma ctree_alter_byte_typed Γ m g w i c τ :
  ✓ Γ → w !!{Γ} i = Some c → (Γ,m) ⊢ w : τ →
  (Γ,m) ⊢ g c : ucharT → (Γ,m) ⊢ ctree_alter_byte Γ g i w : τ.
Proof.
  unfold lookupE, ctree_lookup_byte, ctree_alter_byte. intros ? Hw ??.
  destruct (sublist_lookup _ _ _) as [xbs|] eqn:?; simplify_type_equality'.
  set (G := ctree_flatten ∘ g ∘ ctree_unflatten Γ ucharT).
  assert (length (G xbs) = char_bits).
  { unfold G; simplify_option_equality; auto. }
  apply ctree_unflatten_typed; eauto 2.
  eapply Forall_sublist_alter; unfold G; simpl; eauto using ctree_flatten_valid.
Qed.
Lemma ctree_alter_byte_Forall (P : pbit Ti → Prop) Γ m g w i c τ :
  ✓ Γ → (∀ xb, P xb → P (pbit_indetify xb)) →
  w !!{Γ} i = Some c → (Γ,m) ⊢ w : τ → (Γ,m) ⊢ g c : ucharT →
  ctree_Forall P w → ctree_Forall P (g c) →
  ctree_Forall P (ctree_alter_byte Γ g i w).
Proof.
  unfold lookupE, ctree_lookup_byte, ctree_alter_byte. intros.
  destruct (sublist_lookup _ _ _) as [xbs|] eqn:?; simplify_type_equality'.
  set (G := ctree_flatten ∘ g ∘ ctree_unflatten Γ ucharT).
  assert (length (G xbs) = char_bits).
  { unfold G; simplify_option_equality; auto. }
  eapply ctree_unflatten_Forall; eauto 1 using ctree_typed_type_valid.
  eapply Forall_sublist_alter; unfold G; simpl; eauto.
Qed.
Lemma ctree_alter_byte_type_of Γ g i w :
  ✓ Γ → ✓{Γ} (type_of w) → type_of (ctree_alter_byte Γ g i w) = type_of w.
Proof. apply ctree_unflatten_type_of. Qed.
Lemma ctree_alter_byte_union_free Γ g w i :
  ✓ Γ → union_free (ctree_alter_byte Γ g i w).
Proof. apply ctree_unflatten_union_free. Qed.
Lemma ctree_alter_byte_char Γ m g w :
  ✓ Γ → (Γ,m) ⊢ w : ucharT → (Γ,m) ⊢ g w : ucharT →
  ctree_alter_byte Γ g 0 w = g w.
Proof.
  intros ?? Hc. unfold ctree_alter_byte; simplify_type_equality'.
  erewrite sublist_alter_all by auto; simpl.
  by erewrite (ctree_unflatten_flatten _ _ w), union_free_reset,
    ctree_unflatten_flatten, union_free_reset by eauto using union_free_base.
Qed.
Lemma ctree_lookup_alter_byte Γ m g w τ i c :
  ✓ Γ → w !!{Γ} i = Some c → (Γ,m) ⊢ g c : ucharT → (Γ,m) ⊢ w : τ → 
  ctree_alter_byte Γ g i w !!{Γ} i
  = ctree_lookup_byte_after Γ τ i <$> g <$> w !!{Γ} i.
Proof.
  unfold lookupE, ctree_lookup_byte, ctree_alter_byte. intros.
  destruct (sublist_lookup _ _ (ctree_flatten w))
    as [xbs|] eqn:?; simplify_type_equality'.
  set (G:=ctree_flatten ∘ g ∘ ctree_unflatten Γ ucharT).
  assert (length (G xbs) = char_bits).
  { unfold G; simplify_option_equality; auto. }
  erewrite ctree_flatten_unflatten
    by (rewrite ?sublist_alter_length by auto; eauto).
  erewrite sublist_lookup_mask, sublist_lookup_alter by eauto.
  unfold G, ctree_lookup_byte_after. by simplify_option_equality.
Qed.
Lemma ctree_lookup_alter_byte_ne Γ m g w τ i j c :
  ✓ Γ → w !!{Γ} j = Some c → (Γ,m) ⊢ g c : ucharT →
  (Γ,m) ⊢ w : τ → i ≠ j → ctree_alter_byte Γ g j w !!{Γ} i = w !!{Γ} i.
Proof.
  unfold lookupE, ctree_lookup_byte, ctree_alter_byte. intros.
  destruct (sublist_lookup (j * _) _ (ctree_flatten w))
    as [xbs|] eqn:?; simplify_type_equality'.
  set (G:=ctree_flatten ∘ g ∘ ctree_unflatten Γ ucharT).
  assert (length (G xbs) = char_bits).
  { unfold G; simplify_option_equality; auto. }
  assert (i * char_bits + char_bits ≤ j * char_bits
    ∨ j * char_bits + char_bits ≤ i * char_bits).
  { destruct (decide (i < j)); [left|right];
      rewrite <-Nat.mul_succ_l; apply Nat.mul_le_mono_r; lia. }
  erewrite ctree_flatten_unflatten, sublist_lookup_mask,
    sublist_lookup_alter_ne by eauto.
  destruct (sublist_lookup (i * char_bits) _ _) as [xbs'|] eqn:?; f_equal'.
  unfold sublist_lookup in *; simplify_option_equality.
  by erewrite <-take_mask, <-drop_mask, ctree_flatten_mask by eauto.
Qed.
Lemma ctree_alter_byte_commute Γ m g1 g2 w τ i j c1 c2 :
  ✓ Γ → w !!{Γ} i = Some c1 → (Γ,m) ⊢ g1 c1 : ucharT →
  w !!{Γ} j = Some c2 → (Γ,m) ⊢ g2 c2 : ucharT → (Γ,m) ⊢ w : τ → i ≠ j →
  ctree_alter_byte Γ g1 i (ctree_alter_byte Γ g2 j w)
  = ctree_alter_byte Γ g2 j (ctree_alter_byte Γ g1 i w).
Proof.
  intros. assert (ctree_alter_byte Γ g2 j w !!{Γ} i = Some c1).
  { by erewrite ctree_lookup_alter_byte_ne by eauto. }
  assert (ctree_alter_byte Γ g1 i w !!{Γ} j = Some c2).
  { by erewrite ctree_lookup_alter_byte_ne by eauto. }
  eapply ctree_lookup_byte_ext;
    eauto using ctree_alter_byte_union_free, ctree_alter_byte_typed.
  intros ii _. destruct (decide (ii = i)) as [->|].
  { by erewrite ctree_lookup_alter_byte, ctree_lookup_alter_byte_ne,
      ctree_lookup_alter_byte_ne, ctree_lookup_alter_byte
      by eauto using ctree_alter_byte_typed. }
  destruct (decide (ii = j)) as [->|].
  { by erewrite ctree_lookup_alter_byte, ctree_lookup_alter_byte_ne,
      ctree_lookup_alter_byte, ctree_lookup_alter_byte_ne
      by eauto using ctree_alter_byte_typed. }
  by erewrite !ctree_lookup_alter_byte_ne by eauto using ctree_alter_byte_typed.
Qed.
Lemma ctree_alter_byte_unmapped Γ m g w i τ c :
  ✓ Γ → (Γ,m) ⊢ w : τ → ctree_unmapped (ctree_alter_byte Γ g i w) →
  w !!{Γ} i = Some c → (Γ,m) ⊢ g c : ucharT → ctree_unmapped (g c).
Proof.
  unfold lookupE,ctree_lookup_byte,ctree_alter_byte. intros ?? Hw ??; revert Hw.
  destruct (sublist_lookup _ _ _) as [xbs|] eqn:?; simplify_type_equality'.
  rewrite ctree_flatten_unflatten
    by (unfold compose; eauto 1 using ctree_typed_type_valid); intros Hw.
  eapply (Forall_sublist_alter_inv _ (ctree_flatten ∘ g ∘ _)),
    pbits_unmapped_indetify_inv; eauto.
  eapply Forall_impl with ✓{Γ,m}; eauto using pbit_valid_sep_valid.
  eapply Forall_sublist_alter; simpl; eauto 2 using ctree_flatten_valid.
Qed.  
Lemma ctree_alter_byte_disjoint Γ m g w1 w2 τ i c1 :
  ✓ Γ → (Γ,m) ⊢ w1 : τ → ctree_unshared w1 → w1 ⊥ w2 → w1 !!{Γ} i = Some c1 →
  (∀ c2, c1 ⊥ c2 → g c1 ⊥ c2) → ctree_alter_byte Γ g i w1 ⊥ w2.
Proof.
  unfold lookupE, ctree_alter_byte, ctree_lookup_byte; intros ???? Hw1 ?.
  destruct (sublist_lookup _ _ _) as [xbs1|] eqn:?; simplify_type_equality.
  assert (ctree_unmapped w2) by eauto using @ctree_unshared_unmapped.
  assert ((Γ,m) ⊢ w2 : τ) by eauto using ctree_disjoint_typed.
  assert (union_free w2)
    by eauto using union_free_unmapped, ctree_typed_sep_valid.
  erewrite <-(union_free_reset w2), <-ctree_unflatten_flatten by eauto.
  destruct (Forall2_sublist_lookup_l (⊥) (ctree_flatten w1)
    (ctree_flatten w2) (i * char_bits) char_bits xbs1) as (xbs2&?&?);
    eauto using @ctree_flatten_disjoint.
  eapply ctree_unflatten_disjoint, Forall2_sublist_alter_l;
    eauto using @ctree_flatten_disjoint; simpl.
  rewrite <-(mask_false pbit_indetify xbs2 (bit_size_of Γ ucharT)),
    <-type_mask_base, <-ctree_flatten_unflatten
    by eauto using TBase_valid, TInt_valid.
  eauto using @ctree_flatten_disjoint,
    ctree_unflatten_disjoint, TBase_valid, TInt_valid.
Qed.
Lemma ctree_alter_byte_union Γ m g w1 w2 τ i c1 :
  ✓ Γ → (Γ,m) ⊢ w1 : τ → ctree_unshared w1 → w1 ⊥ w2 → w1 !!{Γ} i = Some c1 →
  (∀ c2, c1 ⊥ c2 → g c1 ⊥ c2) → (∀ c2, c1 ⊥ c2 → g (c1 ∪ c2) = g c1 ∪ c2) →
  ctree_alter_byte Γ g i (w1 ∪ w2) = ctree_alter_byte Γ g i w1 ∪ w2.
Proof.
  unfold lookupE, ctree_alter_byte, ctree_lookup_byte; intros ????? Hg Hg'.
  rewrite ctree_union_type_of by done.
  destruct (sublist_lookup _ _ _) as [xbs1|] eqn:?; simplify_type_equality.
  assert (ctree_unmapped w2) by eauto using @ctree_unshared_unmapped.
  assert ((Γ,m) ⊢ w2 : τ) by eauto using ctree_disjoint_typed.
  assert (union_free w2)
    by eauto using union_free_unmapped, ctree_typed_sep_valid.
  erewrite <-(union_free_reset w2) at 2 by eauto.
  erewrite <-ctree_unflatten_flatten by eauto.
  destruct (Forall2_sublist_lookup_l (⊥) (ctree_flatten w1)
    (ctree_flatten w2) (i * char_bits) char_bits xbs1) as (xbs2&?&?);
    auto using @ctree_flatten_disjoint.
  assert (ctree_flatten (g (ctree_unflatten Γ ucharT xbs1)) ⊥* xbs2).
  { rewrite <-(mask_false pbit_indetify xbs2 (bit_size_of Γ ucharT)),
      <-type_mask_base, <-ctree_flatten_unflatten
      by eauto using TBase_valid, TInt_valid.
    eauto using @ctree_flatten_disjoint,
      ctree_unflatten_disjoint, TBase_valid, TInt_valid. }
  assert (sublist_alter (ctree_flatten ∘ g ∘ ctree_unflatten Γ ucharT)
    (i * char_bits) char_bits (ctree_flatten w1) ⊥* ctree_flatten w2).
  { eapply Forall2_sublist_alter_l; eauto using @ctree_flatten_disjoint. }
  rewrite <-ctree_unflatten_union, ctree_flatten_union by eauto; f_equal.
  symmetry; apply zip_with_sublist_alter with xbs1 xbs2; simpl; auto 1.
  by rewrite ctree_unflatten_union, Hg', ctree_flatten_union,
    ctree_flatten_unflatten, type_mask_base, mask_false by eauto using
    ctree_unflatten_disjoint, TBase_valid, TInt_valid.
Qed.

(** ** Refinements *)
Lemma ctree_unflatten_refine Γ f m1 m2 τ xbs1 xbs2 :
  ✓ Γ → ✓{Γ} τ → xbs1 ⊑{Γ,f@m1↦m2}* xbs2 → length xbs1 = bit_size_of Γ τ →
  ctree_unflatten Γ τ xbs1 ⊑{Γ,f@m1↦m2} ctree_unflatten Γ τ xbs2 : τ.
Proof.
  intros HΓ Hτ. revert τ Hτ xbs1 xbs2. refine (type_env_ind _ HΓ _ _ _ _).
  * intros. rewrite !ctree_unflatten_base. by ctree_refine_constructor.
  * intros τ n _ IH Hn xbs1 xbs2 Hxbs.
    rewrite !ctree_unflatten_array, bit_size_of_array; intros Hxbs1.
    ctree_refine_constructor; auto using array_unflatten_length.
    revert xbs1 xbs2 Hxbs Hxbs1. clear Hn. induction n; simpl; auto.
  * intros [] s τs Hs _ IH _ xbs1 xbs2 Hxbs; erewrite !ctree_unflatten_compound,
      ?bit_size_of_struct by eauto; simpl; intros Hxbs1.
    { unfold struct_unflatten; ctree_refine_constructor; eauto; clear Hs.
      + revert xbs1 xbs2 Hxbs Hxbs1. induction (bit_size_of_fields _ τs HΓ);
          intros; decompose_Forall_hyps'; constructor; simpl; auto.
      + revert xbs1 xbs2 Hxbs Hxbs1. induction (bit_size_of_fields _ τs HΓ);
          intros; decompose_Forall_hyps'; constructor; simpl;
          auto using pbits_indetify_refine.
      + clear Hxbs1 Hxbs IH. revert xbs2.
        induction (bit_size_of_fields _ τs HΓ); intros;
          constructor; simpl; auto using pbits_indetify_idempotent.
      + unfold field_bit_padding. clear IH Hxbs. revert xbs1 Hxbs1.
        induction (bit_size_of_fields _ τs HΓ); intros; f_equal'; auto. }
    ctree_refine_constructor; eauto.
Qed.
Lemma ctree_flatten_refine Γ f m1 m2 w1 w2 τ :
  ✓ Γ → w1 ⊑{Γ,f@m1↦m2} w2 : τ →
  ctree_flatten w1 ⊑{Γ,f@m1↦m2}* ctree_flatten w2.
Proof.
  intros ?. revert w1 w2 τ.
  refine (ctree_refine_ind _ _ _ _ _ _ _ _ _ _ _); simpl; auto 2.
  * eauto using Forall2_bind.
  * intros s τs wxbss1 wxbss2 _ _ IH Hxbss _ _.
    induction IH; decompose_Forall_hyps'; auto.
Qed.
Lemma ctree_refine_Forall (P : pbit Ti → Prop) Γ f m1 m2 w1 w2 τ :
  ✓ Γ → (∀ x1 x2, P x1 → x1 ⊑{Γ,f@m1↦m2} x2 → P x2) →
  ctree_Forall P w1 → w1 ⊑{Γ,f@m1↦m2} w2 : τ → ctree_Forall P w2.
Proof.
  intros HΓ ? Hw2 Hw12. induction (ctree_flatten_refine Γ f m1 m2 w1 w2 τ HΓ Hw12);
    decompose_Forall_hyps; eauto.
Qed.
Lemma ctree_refine_Forall_inv (P : pbit Ti → Prop) Γ f m1 m2 w1 w2 τ :
  ✓ Γ → (∀ x1 x2, P x2 → x1 ⊑{Γ,f@m1↦m2} x2 → P x1) →
  ctree_Forall P w2 → w1 ⊑{Γ,f@m1↦m2} w2 : τ → ctree_Forall P w1.
Proof.
  intros HΓ ? Hw2 Hw12. induction (ctree_flatten_refine Γ f m1 m2 w1 w2 τ HΓ Hw12);
    decompose_Forall_hyps; eauto.
Qed.
Lemma ctree_refine_typed_l Γ f m1 m2 w1 w2 τ :
  ✓ Γ → w1 ⊑{Γ,f@m1↦m2} w2 : τ → (Γ,m1) ⊢ w1 : τ.
Proof.
  intros ?. revert w1 w2 τ. refine (ctree_refine_ind _ _ _ _ _ _ _ _ _ _ _).
  * intros; ctree_typed_constructor; eauto using pbits_refine_valid_l.
  * intros τ n ws1 ws2 Hn _ IH ?; ctree_typed_constructor; auto.
    clear Hn. induction IH; auto.
  * intros s τs wxbss1 wxbss2 Hs _ IH Hxbs Hindet Hlen.
    ctree_typed_constructor; eauto; clear Hs Hlen; induction IH;
      decompose_Forall_hyps';
      eauto using pbits_refine_valid_l, pbits_indetified_refine.
  * intros; ctree_typed_constructor;
      eauto using pbits_refine_valid_l, pbits_indetified_refine.
  * intros; ctree_typed_constructor; eauto using pbits_refine_valid_l.
  * intros; decompose_Forall_hyps'; ctree_typed_constructor;
      eauto using pbits_refine_valid_l.
Qed.
Lemma ctree_refine_typed_r Γ f m1 m2 w1 w2 τ :
  ✓ Γ → w1 ⊑{Γ,f@m1↦m2} w2 : τ → (Γ,m2) ⊢ w2 : τ.
Proof.
  intros ?. revert w1 w2 τ. refine (ctree_refine_ind _ _ _ _ _ _ _ _ _ _ _).
  * intros; ctree_typed_constructor;
      eauto using Forall2_length_l, pbits_refine_valid_r.
  * intros τ n ws1 ws2 -> _ IH Hn;
      ctree_typed_constructor; eauto using Forall2_length.
    clear Hn. induction IH; auto.
  * intros s τs wxbss1 wxbss2 Hs _ IH Hxbs Hindet Hlen.
    ctree_typed_constructor; eauto.
    + elim IH; eauto.
    + elim Hxbs; eauto using pbits_refine_valid_r.
    + rewrite <-Hlen; symmetry.
      elim Hxbs; intros; f_equal'; eauto using Forall2_length.
  * intros; ctree_typed_constructor; eauto using pbits_refine_valid_r.
    + by erewrite <-Forall2_length by eauto.
    + intuition eauto using ctree_refine_Forall_inv,
        pbit_refine_unmapped_inv, pbits_refine_unmapped_inv.
  * intros; ctree_typed_constructor;
      eauto using Forall2_length_l, pbits_refine_valid_r.
  * intros; ctree_typed_constructor;
      eauto using Forall2_length_l, pbits_refine_valid_r.
Qed.
Hint Immediate ctree_refine_typed_l ctree_refine_typed_r.
Lemma ctree_refine_type_of_l Γ f m1 m2 w1 w2 τ :
  w1 ⊑{Γ,f@m1↦m2} w2 : τ → type_of w1 = τ.
Proof. destruct 1 using @ctree_refine_ind; simpl; auto. Qed.
Lemma ctree_refine_type_of_r Γ f m1 m2 w1 w2 τ :
  w1 ⊑{Γ,f@m1↦m2} w2 : τ → type_of w2 = τ.
Proof. destruct 1; f_equal'; eauto using Forall2_length_l. Qed.
Lemma ctree_refine_id Γ m w τ : (Γ,m) ⊢ w : τ → w ⊑{Γ@m} w : τ.
Proof.
  revert w τ. refine (ctree_typed_ind _ _ _ _ _ _ _ _);
     try by (intros; ctree_refine_constructor; eauto using pbits_refine_id).
  * intros ws τ _ IH Hlen; ctree_refine_constructor; auto. elim IH; auto.
  * intros s wxbss τs ? _ IH Hwxbss; ctree_refine_constructor; auto.
    + elim IH; constructor; eauto.
    + elim Hwxbss; constructor; eauto using pbits_refine_id.
Qed.
Lemma ctree_refine_compose Γ f1 f2 m1 m2 m3 w1 w2 w3 τ :
  ✓ Γ → w1 ⊑{Γ,f1@m1↦m2} w2 : τ → w2 ⊑{Γ,f2@m2↦m3} w3 : τ →
  w1 ⊑{Γ,f1 ◎ f2@m1↦m3} w3 : τ.
Proof.
  intros ? Hw. revert w1 w2 τ Hw w3.
  refine (ctree_refine_ind _ _ _ _ _ _ _ _ _ _ _); simpl.
  * intros τb xbs1 xbs2 ??? w3 Hw3; pattern w3;
      apply (ctree_refine_inv_l _ _ _ _ _ _ _ _ Hw3);
      intros; ctree_refine_constructor; eauto using pbits_refine_compose.
  * intros τ n ws1 ws2 -> _ IH Hlen w3 Hw3;
      pattern w3; apply (ctree_refine_inv_l _ _ _ _ _ _ _ _ Hw3); clear w3 Hw3;
      intros ws3 Hws3; ctree_refine_constructor; auto.
    clear Hlen. revert ws3 Hws3.
    induction IH; intros; decompose_Forall_hyps'; constructor; auto.
  * intros s τs wxbss1 wxbss2 Hs _ IH Hxbs _ Hlen w3 Hw3; pattern w3;
      apply (ctree_refine_inv_l _ _ _ _ _ _ _ _ Hw3); clear w3 Hw3.
    intros ? wxbss3 ? Hws3 Hindet Hxbs3;
      simplify_equality; ctree_refine_constructor; eauto.
    + clear Hs Hlen Hxbs3 Hxbs Hindet. revert wxbss3 Hws3.
      induction IH; inversion_clear 1; constructor; eauto.
    + clear Hs Hlen IH Hws3 Hindet. revert wxbss3 Hxbs3.
      induction Hxbs; intros; decompose_Forall_hyps';
        constructor; eauto using pbits_refine_compose.
  * intros s τs i w1 w2 xbs1 xbs2 τ Hs Hτs ? IH ???? w3 Hw3; pattern w3;
      apply (ctree_refine_inv_l _ _ _ _ _ _ _ _ Hw3); clear w3 Hw3;
      intros; decompose_Forall_hyps'; ctree_refine_constructor;
        eauto using ctree_flatten_refine, pbits_refine_compose,
        pbits_indetified_refine.
  * intros s τs xbs1 xbs2 Hs ?? w3 Hw3; pattern w3;
      apply (ctree_refine_inv_l _ _ _ _ _ _ _ _ Hw3);
      intros; ctree_refine_constructor; eauto using pbits_refine_compose.
  * intros s i τs w1 xbs1 xbs2 τ ???????? w3 Hw3; pattern w3;
      apply (ctree_refine_inv_l _ _ _ _ _ _ _ _ Hw3); clear w3 Hw3.
    intros; ctree_refine_constructor; eauto using ctree_unflatten_refine,
      Forall2_length_l, pbits_refine_compose, pbits_refine_unshared.
Qed.
Lemma ctree_refine_weaken Γ Γ' f f' m1 m2 m1' m2' w1 w2 τ :
  ✓ Γ → w1 ⊑{Γ,f@m1↦m2} w2 : τ → Γ ⊆ Γ' → f ⊆ f' →
  (∀ o τ, type_of_index m1 o = Some τ → type_of_index m1' o = Some τ) →
  (∀ o τ, type_of_index m2 o = Some τ → type_of_index m2' o = Some τ) →
  w1 ⊑{Γ',f'@m1'↦m2'} w2 : τ.
Proof.
  intros ? Hw ????. induction Hw using @ctree_refine_ind;
    ctree_refine_constructor; eauto using base_type_valid_weaken,
      lookup_weaken, Forall2_impl, pbit_refine_weaken, ctree_typed_weaken;
    erewrite <-?(bit_size_of_weaken Γ Γ'), <-?(field_bit_padding_weaken Γ Γ')
      by eauto using TBase_valid, TCompound_valid; auto.
  eapply Forall2_impl; eauto.
  simpl; eauto using Forall2_impl, pbit_refine_weaken.
Qed.
Lemma union_free_refine Γ f m1 m2 w1 w2 τ :
  union_free w1 → w1 ⊑{Γ,f@m1↦m2} w2 : τ → union_free w2.
Proof.
  intros Hw1 Hw. revert w1 w2 τ Hw Hw1.
  refine (ctree_refine_ind _ _ _ _ _ _ _ _ _ _ _); simpl; try by constructor.
  * intros τ n ws1 ws2 _ _ IH _; inversion_clear 1; constructor.
    induction IH; decompose_Forall_hyps'; auto.
  * intros s τs wxbss1 wxnss2 _ _ IH _ _ _; inversion_clear 1; constructor.
    induction IH; decompose_Forall_hyps'; auto.
  * inversion_clear 9.
Qed.
Lemma union_reset_above Γ f m1 m2 w1 w2 τ :
  ✓ Γ → w1 ⊑{Γ,f@m1↦m2} w2 : τ →
  ctree_unshared w2 → w1 ⊑{Γ,f@m1↦m2} union_reset w2 : τ.
Proof.
  intros HΓ. revert w1 w2 τ.
  refine (ctree_refine_ind _ _ _ _ _ _ _ _ _ _ _); simpl.
  * by intros; ctree_refine_constructor.
  * intros τ n ws1 ws2 Hn _ IH ??. ctree_refine_constructor; auto.
    clear Hn. induction IH; decompose_Forall_hyps'; auto.
  * intros s τs wxbss1 wxbss2 Hs _ IH ? Hindet Hlen ?;
      ctree_refine_constructor; eauto; clear Hs Hlen;
      induction IH; decompose_Forall_hyps'; constructor; auto.
  * intros s τs i w1 w2 xbs1 xbs2 τ; intros.
    ctree_refine_constructor; eauto using ctree_flatten_refine,
      pbits_indetified_refine.
  * intros; ctree_refine_constructor; eauto.
  * intros; ctree_refine_constructor; eauto.
Qed.
Lemma union_reset_refine Γ f m1 m2 w1 w2 τ :
  ✓ Γ → w1 ⊑{Γ,f@m1↦m2} w2 : τ → union_reset w1 ⊑{Γ,f@m1↦m2} union_reset w2 : τ.
Proof.
  intros ?. revert w1 w2 τ. refine (ctree_refine_ind _ _ _ _ _ _ _ _ _ _ _);
    simpl; try by (intros; ctree_refine_constructor; eauto 1).
  * intros τ n ws1 ws2 -> _ IH Hlen; ctree_refine_constructor; auto.
    elim IH; constructor; eauto.
  * intros s τs wxbss1 wxbss2 ? _ IH Hxbs Hindet Hlen.
    ctree_refine_constructor; eauto.
    + elim IH; constructor; eauto.
    + elim Hxbs; constructor; eauto.
    + elim Hindet; constructor; auto.
    + rewrite <-Hlen. elim wxbss1; intros; f_equal'; auto.
  * intros; ctree_refine_constructor; eauto using ctree_flatten_refine.
Qed.
Lemma ctree_flatten_unflatten_refine Γ m1 m2 f w xbs τ :
  ✓ Γ → (Γ,m1) ⊢ w : τ → Forall sep_unshared xbs →
  ctree_flatten w ⊑{Γ,f@m1↦m2}* xbs →
  w ⊑{Γ,f@m1↦m2} ctree_unflatten Γ τ xbs : τ.
Proof.
  intros. rewrite <-(left_id_L _ (◎) f); apply ctree_refine_compose
    with m1 (ctree_unflatten Γ τ (ctree_flatten w)); auto.
  { erewrite ctree_unflatten_flatten by eauto.
    apply union_reset_above; eauto using ctree_refine_id.
    eauto using pbits_refine_unshared_inv. }
  apply ctree_unflatten_refine; eauto.
Qed.
Lemma ctree_lookup_seg_refine Γ f m1 m2 w1 w2 τ rs w3 :
  ✓ Γ → w1 ⊑{Γ,f@m1↦m2} w2 : τ → w1 !!{Γ} rs = Some w3 →
  ∃ w4, w2 !!{Γ} rs = Some w4 ∧ w3 ⊑{Γ,f@m1↦m2} w4 : type_of w3.
Proof.
  intros ? Hw Hrs. destruct Hw using @ctree_refine_ind; destruct rs;
    pattern w3; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); simpl; clear Hrs.
  * intros; simplify_option_equality by eauto using Forall2_length.
    decompose_Forall_hyps. erewrite ctree_refine_type_of_l by eauto; eauto.
  * intros; simplify_option_equality.
    decompose_Forall_hyps'; simplify_option_equality.
    erewrite ctree_refine_type_of_l by eauto; eauto.
  * intros; simplify_option_equality; eauto.
    erewrite ctree_refine_type_of_l by eauto; eauto.
  * intros; simplify_option_equality by eauto using ctree_refine_Forall,
      pbit_refine_unshared, pbits_refine_unshared.
    rewrite ctree_unflatten_type_of by eauto.
    eauto 8 using ctree_unflatten_refine, ctree_flatten_refine.
  * intros; simplify_option_equality by eauto using pbits_refine_unshared.
    rewrite ctree_unflatten_type_of by eauto.
    eauto 8 using ctree_unflatten_refine.
  * intros; simplify_option_equality; decompose_Forall_hyps'.
    rewrite take_app_alt by (by erewrite <-Forall2_length by eauto).
    erewrite type_of_correct by eauto.
    eauto using ctree_flatten_unflatten_refine.
  * intros; simplify_option_equality.
    rewrite ctree_unflatten_type_of by eauto.
    eauto 8 using ctree_unflatten_refine, ctree_flatten_refine.
Qed.
Lemma ctree_lookup_refine Γ f m1 m2 w1 w2 τ r w3 :
  ✓ Γ → w1 ⊑{Γ,f@m1↦m2} w2 : τ → w1 !!{Γ} r = Some w3 →
  ∃ w4, w2 !!{Γ} r = Some w4 ∧ w3 ⊑{Γ,f@m1↦m2} w4 : type_of w3.
Proof.
  intros HΓ. revert w1 w2 τ. induction r as [|rs r IH] using rev_ind; simpl.
  { intros. rewrite list_path_lookup_nil. simplify_equality.
    erewrite ctree_refine_type_of_l by eauto; eauto. }
  intros w1 w2. rewrite !list_path_lookup_snoc. intros. simplify_option_equality.
  edestruct (ctree_lookup_seg_refine Γ f m1 m2 w1 w2 τ rs) as (?&?&?);
    simplify_option_equality; eauto.
Qed.
Lemma ctree_lookup_refine_both Γ f m1 m2 w1 w2 τ r w3 w4 :
  ✓ Γ → w1 ⊑{Γ,f@m1↦m2} w2 : τ → w1 !!{Γ} r = Some w3 →
  w2 !!{Γ} r = Some w4 → w3 ⊑{Γ,f@m1↦m2} w4 : type_of w3.
Proof.
  intros. destruct (ctree_lookup_refine Γ f m1 m2 w1 w2 τ r w3)
    as (?&?&?); simplify_equality'; auto.
Qed.
Lemma ctree_alter_seg_refine Γ f m1 m2 g1 g2 w1 w2 τ rs w3 w4 :
  ✓ Γ → w1 ⊑{Γ,f@m1↦m2} w2 : τ → w1 !!{Γ} rs = Some w3 → w2 !!{Γ} rs = Some w4 →
  g1 w3 ⊑{Γ,f@m1↦m2} g2 w4 : type_of w3 → ¬ctree_unmapped (g1 w3) →
  ctree_alter_seg Γ g1 rs w1 ⊑{Γ,f@m1↦m2} ctree_alter_seg Γ g2 rs w2 : τ.
Proof.
  intros ? Hw Hw3 Hw4. destruct Hw as [|τ n ws1 ws2 ?? _
    |s τw wxbss1 wxbss2 ? Hws _ Hxbss ? Hlen|s τs i w1 w2 xbs1 xbs2 τ ??? _| |]
    using @ctree_refine_ind; destruct rs as [i'|i'|i']; simpl;
    pattern w3; apply (ctree_lookup_seg_inv _ _ _ _ _ Hw3); simpl; clear Hw3;
    pattern w4; apply (ctree_lookup_seg_inv _ _ _ _ _ Hw4); simpl; clear Hw4;
    intros; simplify_option_equality; decompose_Forall_hyps;
    repeat match goal with
    | H : g1 _ ⊑{Γ,f@_↦_} g2 _ : _ |- _ => first
       [ erewrite ctree_refine_type_of_l in H by eauto
       | erewrite ctree_unflatten_type_of in H by eauto
       | erewrite type_of_correct in H by eauto ]
    end.
  * ctree_refine_constructor; auto using alter_length.
    apply Forall2_alter; auto. intros; simplify_equality'; auto.
  * ctree_refine_constructor; eauto.
    + apply Forall3_alter_lm; [elim Hws; constructor; simpl; eauto|].
      intros [??] [??] ????; simplify_equality; auto.
    + by apply Forall2_alter; [elim Hxbss; constructor; simpl; eauto|].
    + apply Forall_alter; auto.
    + rewrite <-Hlen. generalize i'.
      elim wxbss1; [|intros ? wxbss ?]; intros [|?]; f_equal'; auto.
  * ctree_refine_constructor; eauto; solve_length || tauto.
  * ctree_refine_constructor; eauto using ctree_flatten_refine,
      pbits_indetify_refine, pbits_indetify_idempotent; solve_length || tauto.
  * ctree_refine_constructor; eauto using pbits_indetify_refine,
      pbits_indetify_idempotent; solve_length || tauto.
  * ctree_refine_constructor; eauto using pbits_indetify_idempotent; [|tauto].
    rewrite drop_app_alt by (by erewrite <-Forall2_length by eauto); eauto.
    match goal with H : pbit_indetify <$> _ = _ |- _ => rewrite <-H end.
    eauto using pbits_indetify_refine.
  * ctree_refine_constructor; eauto using pbits_indetify_refine,
      pbits_indetify_idempotent; solve_length || intuition.
Qed.
Lemma ctree_alter_refine Γ f m1 m2 g1 g2 w1 w2 τ r w3 w4 :
  ✓ Γ → w1 ⊑{Γ,f@m1↦m2} w2 : τ → w1 !!{Γ} r = Some w3 → w2 !!{Γ} r = Some w4 →
  g1 w3 ⊑{Γ,f@m1↦m2} g2 w4 : type_of w3 → ¬ctree_unmapped (g1 w3) →
  ctree_alter Γ g1 r w1 ⊑{Γ,f@m1↦m2} ctree_alter Γ g2 r w2 : τ.
Proof.
  intros ?. revert g1 g2 w1 w2 τ.
  induction r as [|rs r IH] using rev_ind; simpl; intros g1 g2 w1 w2 τ.
  { rewrite !list_path_lookup_nil; intros ???; simplify_equality.
    erewrite ctree_refine_type_of_l by eauto; eauto. }
  rewrite !list_path_lookup_snoc, !ctree_alter_snoc; intros.
  destruct (w1 !!{Γ} rs) as [w1'|] eqn:?; simplify_equality'.
  destruct (w2 !!{Γ} rs) as [w2'|] eqn:?; simplify_equality'.
  destruct (ctree_lookup_seg_refine Γ f m1 m2 w1 w2 τ rs w1')
    as (?&?&?); auto; simplify_equality'.
  eapply ctree_alter_seg_refine; eauto using ctree_alter_unmapped.
Qed.
Lemma ctree_lookup_byte_refine Γ f m1 m2 w1 w2 τ i c1 :
  ✓ Γ → w1 ⊑{Γ,f@m1↦m2} w2 : τ → w1 !!{Γ} i = Some c1 →
  ∃ c2, w2 !!{Γ} i = Some c2 ∧ c1 ⊑{Γ,f@m1↦m2} c2 : ucharT.
Proof.
  unfold lookupE, ctree_lookup_byte. intros.
  destruct (sublist_lookup _ _ (ctree_flatten w1))
    as [xbs1|] eqn:Hbs1; simplify_equality'.
  destruct (Forall2_sublist_lookup_l (refine Γ f m1 m2) (ctree_flatten w1)
    (ctree_flatten w2) (i * char_bits) char_bits xbs1) as (xbs2&?&?);
    eauto using ctree_flatten_refine.
  exists (ctree_unflatten Γ ucharT xbs2); simplify_option_equality; split; auto.
  apply ctree_unflatten_refine; auto using TBase_valid, TInt_valid.
Qed.
Lemma ctree_lookup_byte_refine_inv Γ f m1 m2 w1 w2 τ i c2 :
  ✓ Γ → w1 ⊑{Γ,f@m1↦m2} w2 : τ → w2 !!{Γ} i = Some c2 →
  ∃ c1, w1 !!{Γ} i = Some c1 ∧ c1 ⊑{Γ,f@m1↦m2} c2 : ucharT.
Proof.
  unfold lookupE, ctree_lookup_byte. intros.
  destruct (sublist_lookup _ _ (ctree_flatten w2))
    as [xbs2|] eqn:Hbs1; simplify_equality'.
  destruct (Forall2_sublist_lookup_r (refine Γ f m1 m2) (ctree_flatten w1)
    (ctree_flatten w2) (i * char_bits) char_bits xbs2) as (xbs1&?&?);
    eauto using ctree_flatten_refine.
  exists (ctree_unflatten Γ ucharT xbs1); simplify_option_equality; split; auto.
  apply ctree_unflatten_refine; auto using TBase_valid, TInt_valid.
Qed.
Lemma ctree_alter_byte_refine Γ f m1 m2 g1 g2 w1 w2 τ i c1 c2 :
  ✓ Γ → w1 ⊑{Γ,f@m1↦m2} w2 : τ → w1 !!{Γ} i = Some c1 → w2 !!{Γ} i = Some c2 →
  g1 c1 ⊑{Γ,f@m1↦m2} g2 c2 : ucharT →
  ctree_alter_byte Γ g1 i w1 ⊑{Γ,f@m1↦m2} ctree_alter_byte Γ g2 i w2 : τ.
Proof.
  unfold lookupE, ctree_lookup_byte, ctree_alter_byte. intros.
  set (G1 := ctree_flatten ∘ g1 ∘ ctree_unflatten Γ ucharT).
  set (G2 := ctree_flatten ∘ g2 ∘ ctree_unflatten Γ ucharT).
  assert ((Γ,m1) ⊢ w1 : τ) by eauto; assert ((Γ,m2) ⊢ w2 : τ) by eauto.
  destruct (sublist_lookup _ _ (ctree_flatten w1)) as [xbs1|] eqn:?,
    (sublist_lookup _ _ (ctree_flatten w2)) as [xbs2|] eqn:?;
    simplify_type_equality'.
  destruct (Forall2_sublist_lookup_l (refine Γ f m1 m2) (ctree_flatten w1)
    (ctree_flatten w2) (i * char_bits) char_bits xbs1) as (?&?&?);
    eauto 2 using ctree_flatten_refine; simplify_option_equality.
  assert (length (G1 xbs1) = char_bits).
  { unfold G1; simpl. eauto using ctree_refine_typed_l. }
  apply ctree_unflatten_refine; eauto 1.
  eapply Forall2_sublist_alter; eauto 2 using ctree_flatten_refine.
  apply ctree_flatten_refine with ucharT; simplify_option_equality; auto.
Qed.
End ctree.
