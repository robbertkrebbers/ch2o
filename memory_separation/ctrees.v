(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)

From stdpp Require Import list.
Require Export separation types.

Local Open Scope ctype_scope.

Inductive ctree (K : iType) (A : sType) : iType :=
  | MBase : base_type K → list A → ctree K A
  | MArray : type K → list (ctree K A) → ctree K A
  | MStruct : tag → list (ctree K A * list A) → ctree K A
  | MUnion : tag → nat → ctree K A → list A → ctree K A
  | MUnionAll : tag → list A → ctree K A.
Arguments MBase {_ _} _ _.
Arguments MArray {_ _} _ _.
Arguments MStruct {_ _} _ _.
Arguments MUnion {_ _} _ _ _ _.
Arguments MUnionAll {_ _} _ _.

#[global] Instance: `{Inj (=) (=) (@MBase K A τb)}.
Proof. by injection 1. Qed.
#[global] Instance: `{Inj2 (=) (=) (=) (@MArray K A)}.
Proof. by injection 1. Qed.
#[global] Instance: `{Inj (=) (=) (@MStruct K A t)}.
Proof. by injection 1. Qed.
#[global] Instance: `{Inj2 (=) (=) (=) (@MUnion K A t i)}.
Proof. by injection 1. Qed.
#[global] Instance: `{Inj (=) (=) (@MUnionAll K A t)}.
Proof. by injection 1. Qed.

#[global] Instance ctree_eq_dec {K : iType} {A : sType}
  `{EqDecision K, EqDecision A} : EqDecision (ctree K A).
Proof.
 refine (
  fix go w1 w2 : Decision (w1 = w2) :=
  match w1, w2 with
  | MBase τb1 xs1, MBase τb2 xs2 =>
     cast_if_and (decide_rel (=) τb1 τb2) (decide_rel (=) xs1 xs2)
  | MArray τ1 ws1, MArray τ2 ws2 =>
     cast_if_and (decide_rel (=) τ1 τ2) (decide_rel (=) ws1 ws2)
  | MStruct t1 wxss1, MStruct t2 wxss2 =>
     cast_if_and (decide_rel (=) t1 t2) (decide_rel (=) wxss1 wxss2)
  | MUnion t1 i1 w1 xs1, MUnion t2 i2 w2 xs2 =>
     cast_if_and4 (decide_rel (=) t1 t2) (decide_rel (=) i1 i2)
       (decide_rel (=) w1 w2) (decide_rel (=) xs1 xs2)
  | MUnionAll t1 bs1, MUnionAll t2 bs2 =>
     cast_if_and (decide_rel (=) t1 t2) (decide_rel (=) bs1 bs2)
  | _, _ => right _
  end); try congruence; (eauto with typeclass_instances).
Defined.

Section ctree_ind.
  Context {K : iType} {A : sType} (P : ctree K A → Prop).
  Context (Pbase : ∀ τb xs, P (MBase τb xs)).
  Context (Parray : ∀ τ ws, Forall P ws → P (MArray τ ws)).
  Context (Pstruct : ∀ t wxss, Forall (P ∘ fst) wxss → P (MStruct t wxss)).
  Context (Punion : ∀ t i w xs, P w → P (MUnion t i w xs)).
  Context (Punion_all : ∀ t xs, P (MUnionAll t xs)).
  Definition ctree_ind_alt: ∀ w, P w :=
    fix go w :=
    match w return P w with
    | MBase _ _ => Pbase _ _
    | MArray _ ws => Parray _ _ $ list_ind (Forall P)
       (Forall_nil_2 _) (λ w _, Forall_cons_2 _ _ _ (go w)) ws
    | MStruct _ wxss  => Pstruct _ _ $ list_ind (Forall (P ∘ fst))
       (Forall_nil_2 _) (λ w _, Forall_cons_2 (P ∘ fst) _ _ (go (fst w))) wxss
    | MUnion _ _ w _ => Punion _ _ _ _ (go w)
    | MUnionAll _ _ => Punion_all _ _
    end.
End ctree_ind.

Definition ctree_flatten {K A} : ctree K A → list A :=
  fix go w :=
  match w with
  | MBase _ xs => xs
  | MArray _ ws => ws ≫= go
  | MStruct t wxss => wxss ≫= λ wxs, go (wxs.1) ++ wxs.2
  | MUnion t i w xs => go w ++ xs
  | MUnionAll _ xs => xs
  end.
Notation ctree_Forall P w := (Forall P (ctree_flatten w)).
Notation ctree_empty w := (ctree_Forall (∅ =.) w).
Notation ctree_unmapped w := (ctree_Forall sep_unmapped w).
Notation ctree_splittable w := (ctree_Forall sep_splittable w).
Notation ctree_unshared w := (ctree_Forall sep_unshared w).

Definition MUnion' {K} `{SeparationOps A}
    (t : tag) (i : nat) (w : ctree K A) (xs : list A) : ctree K A :=
  if decide (ctree_unmapped w ∧ Forall sep_unmapped xs)
  then MUnionAll t (ctree_flatten w ++ xs) else MUnion t i w xs.
Definition ctree_map {K A B} (f : A → B) : ctree K A → ctree K B :=
  fix go w :=
  match w with
  | MBase τb xs => MBase τb (f <$> xs)
  | MArray τ ws => MArray τ (go <$> ws)
  | MStruct t wxss => MStruct t (prod_map go (fmap (M:=list) f) <$> wxss)
  | MUnion t i w xs => MUnion t i (go w) (f <$> xs)
  | MUnionAll t xs => MUnionAll t (f <$> xs)
  end.
Definition ctree_merge_array {K A B C} (f : ctree K A → list B → ctree K C) :
    list (ctree K A) → list B → list (ctree K C) :=
  fix go ws ys :=
  match ws with
  | [] => []
  | w :: ws =>
     let sz := length (ctree_flatten w) in
     f w (take sz ys) :: go ws (drop sz ys)
  end.
Definition ctree_merge_struct {K A B C}
  (f : A → B → C) (g : ctree K A → list B → ctree K C) :
    list (ctree K A * list A) → list B → list (ctree K C * list C) :=
  fix go wxss ys :=
  match wxss with
  | [] => []
  | (w,xs) :: wxss =>
     let sz_w := length (ctree_flatten w) in
     let ys' := drop sz_w ys in
     let sz_xs := length xs in
     (g w (take sz_w ys), zip_with f xs (take sz_xs ys'))
     :: go wxss (drop sz_xs ys')
  end.
Definition ctree_merge {K A B C}
    (f : A → B → C) : ctree K A → list B → ctree K C :=
  fix go w ys :=
  match w with
  | MBase τb xs => MBase τb (zip_with f xs ys)
  | MArray τ ws => MArray τ (ctree_merge_array go ws ys)
  | MStruct t wxss => MStruct t (ctree_merge_struct f go wxss ys)
  | MUnion t i w xs =>
     let sz := length (ctree_flatten w) in
     let w' := go w (take sz ys) in let xs' := zip_with f xs (drop sz ys) in
     MUnion t i w' xs'
  | MUnionAll t xs => MUnionAll t (zip_with f xs ys)
  end.

Section operations.
  Context {K : iType} `{SeparationOps A}.

  Inductive ctree_valid : ctree K A → Prop :=
    | MBase_valid τb xs : Forall sep_valid xs → ctree_valid (MBase τb xs)
    | MArray_valid τ ws : Forall ctree_valid ws → ctree_valid (MArray τ ws)
    | MStruct_valid t wxss :
       Forall (ctree_valid ∘ fst) wxss → Forall (Forall sep_valid ∘ snd) wxss →
       ctree_valid (MStruct t wxss)
    | MUnion_valid t i w xs :
       ctree_valid w → Forall sep_valid xs →
       ¬(ctree_unmapped w ∧ Forall sep_unmapped xs) →
       ctree_valid (MUnion t i w xs)
    | MUnionAll_valid t xs : Forall sep_valid xs → ctree_valid (MUnionAll t xs).
  Section ctree_valid_ind.
    Context (P : ctree K A → Prop).
    Context (Pbase : ∀ τb xs, Forall sep_valid xs → P (MBase τb xs)).
    Context (Parray : ∀ τ ws,
      Forall ctree_valid ws → Forall P ws → P (MArray τ ws)).
    Context (Pstruct : ∀ t wxss,
      Forall (ctree_valid ∘ fst) wxss → Forall (P ∘ fst) wxss →
      Forall (Forall sep_valid ∘ snd) wxss → P (MStruct t wxss)).
    Context (Punion : ∀ t i w xs,
      ctree_valid w → P w → Forall sep_valid xs →
      ¬(ctree_unmapped w ∧ Forall sep_unmapped xs) → P (MUnion t i w xs)).
    Context (Punion_all : ∀ t xs, Forall sep_valid xs → P (MUnionAll t xs)).
    Definition ctree_valid_ind_alt : ∀ w, ctree_valid w → P w.
    Proof. fix H'2 2. destruct 1; eauto using Forall_impl. Qed.
  End ctree_valid_ind.
  Global Instance ctree_valid_dec : ∀ w, Decision (ctree_valid w).
  Proof.
   refine
    (fix go w :=
    match w return Decision (ctree_valid w) with
    | MBase _ xs => cast_if (decide (Forall sep_valid xs))
    | MArray _ ws => cast_if (decide (Forall ctree_valid ws))
    | MStruct _ wxss =>
       cast_if_and (decide (Forall (ctree_valid ∘ fst) wxss))
         (decide (Forall (Forall sep_valid ∘ snd) wxss))
    | MUnion _ _ w xs =>
       cast_if_and3 (decide (ctree_valid w)) (decide (Forall sep_valid xs))
         (decide (¬(ctree_unmapped w ∧ Forall sep_unmapped xs)))
    | MUnionAll _ xs => cast_if (decide (Forall sep_valid xs))
    end); clear go; abstract first [by constructor|by inversion 1].
  Defined.

  Inductive ctree_disjoint : Disjoint (ctree K A) :=
    | MBase_disjoint τb xs1 xs2 : xs1 ##* xs2 → MBase τb xs1 ## MBase τb xs2
    | MArray_disjoint τ ws1 ws2 : ws1 ##* ws2 → MArray τ ws1 ## MArray τ ws2
    | MStruct_disjoint t wxss1 wxss2 :
       wxss1 ##1* wxss2 → wxss1 ##2** wxss2 → MStruct t wxss1 ## MStruct t wxss2
    | MUnion_disjoint t i w1 w2 xs1 xs2 :
       w1 ## w2 → xs1 ##* xs2 →
       ¬(ctree_unmapped w1 ∧ Forall sep_unmapped xs1) →
       ¬(ctree_unmapped w2 ∧ Forall sep_unmapped xs2) →
       MUnion t i w1 xs1 ## MUnion t i w2 xs2
    | MUnionAll_disjoint t xs1 xs2 :
       xs1 ##* xs2 → MUnionAll t xs1 ## MUnionAll t xs2
    | MUnionAll_MUnion_disjoint t i xs1 w2 xs2 :
       xs1 ##* ctree_flatten w2 ++ xs2 → Forall sep_unmapped xs1 →
       ctree_valid w2 → ¬(ctree_unmapped w2 ∧ Forall sep_unmapped xs2) →
       MUnionAll t xs1 ## MUnion t i w2 xs2
    | MUnion_MUnionAll_disjoint t i w1 xs1 xs2 :
       ctree_flatten w1 ++ xs1 ##* xs2 → Forall sep_unmapped xs2 →
       ctree_valid w1 → ¬(ctree_unmapped w1 ∧ Forall sep_unmapped xs1) →
       MUnion t i w1 xs1 ##  MUnionAll t xs2.
  #[global] Existing Instance ctree_disjoint.
  Section ctree_disjoint_ind.
    Context (P : ctree K A → ctree K A → Prop).
    Context (Pbase: ∀ τb xs1 xs2, xs1 ##* xs2 → P (MBase τb xs1) (MBase τb xs2)).
    Context (Parray : ∀ τ ws1 ws2,
      ws1 ##* ws2 → Forall2 P ws1 ws2 → P (MArray τ ws1) (MArray τ ws2)).
    Context (Pstruct : ∀ t wxss1 wxss2,
      wxss1 ##1* wxss2 → Forall2 (λ wxs1 wxs2, P (wxs1.1) (wxs2.1)) wxss1 wxss2 →
      wxss1 ##2** wxss2 → P (MStruct t wxss1) (MStruct t wxss2)).
    Context (Punion : ∀ t i w1 w2 xs1 xs2,
      w1 ## w2 → P w1 w2 → xs1 ##* xs2 →
       ¬(ctree_unmapped w1 ∧ Forall sep_unmapped xs1) →
       ¬(ctree_unmapped w2 ∧ Forall sep_unmapped xs2) →
      P (MUnion t i w1 xs1) (MUnion t i w2 xs2)).
    Context (Punion_bits : ∀ t xs1 xs2,
      xs1 ##* xs2 → P (MUnionAll t xs1) (MUnionAll t xs2)).
    Context (Punion_all_union : ∀ t i xs1 w2 xs2,
      xs1 ##* ctree_flatten w2 ++ xs2 → Forall sep_unmapped xs1 →
      ctree_valid w2 → ¬(ctree_unmapped w2 ∧ Forall sep_unmapped xs2) →
      P (MUnionAll t xs1) (MUnion t i w2 xs2)).
    Context (Punion_union_empty : ∀ t i w1 xs1 xs2,
      ctree_flatten w1 ++ xs1 ##* xs2 → Forall sep_unmapped xs2 →
      ctree_valid w1 → ¬(ctree_unmapped w1 ∧ Forall sep_unmapped xs1) →
      P (MUnion t i w1 xs1) (MUnionAll t xs2)).
    Definition ctree_disjoint_ind_alt : ∀ w1 w2, ctree_disjoint w1 w2 → P w1 w2.
    Proof. fix H'3 3. destruct 1; eauto using Forall2_impl. Qed.
  End ctree_disjoint_ind.
  Lemma ctree_disjoint_inv_l (P : ctree K A → Prop) w1 w2 :
    w1 ## w2 →
    match w1 with
    | MBase τb xs1 => (∀ xs2, xs1 ##* xs2 → P (MBase τb xs2)) → P w2
    | MArray τ ws1 => (∀ ws2, ws1 ##* ws2 → P (MArray τ ws2)) → P w2
    | MStruct t wxss1 =>
      (∀ wxss2, wxss1 ##1* wxss2 → wxss1 ##2** wxss2 → P (MStruct t wxss2)) → P w2
    | MUnion t i w1 xs1 =>
       (∀ w2 xs2,
         w1 ## w2 → xs1 ##* xs2 →
         ¬(ctree_unmapped w1 ∧ Forall sep_unmapped xs1) →
         ¬(ctree_unmapped w2 ∧ Forall sep_unmapped xs2) →
         P (MUnion t i w2 xs2)) →
       (∀ xs2,
         ctree_flatten w1 ++ xs1 ##* xs2 → Forall sep_unmapped xs2 →
         ctree_valid w1 → ¬(ctree_unmapped w1 ∧ Forall sep_unmapped xs1) →
         P (MUnionAll t xs2)) → P w2
    | MUnionAll t xs1 =>
       (∀ xs2, xs1 ##* xs2 → P (MUnionAll t xs2)) →
       (∀ i w2 xs2,
         xs1 ##* ctree_flatten w2 ++ xs2 → Forall sep_unmapped xs1 →
         ctree_valid w2 → ¬(ctree_unmapped w2 ∧ Forall sep_unmapped xs2) →
         P (MUnion t i w2 xs2)) → P w2
    end.
  Proof. destruct 1; auto. Qed.
  Global Instance ctree_disjoint_dec `{EqDecision K} :
    ∀ (w1 w2: ctree K A), Decision (w1 ## w2).
  Proof.
   refine
    (fix go w1 w2 :=
    match w1, w2 return Decision (w1 ## w2) with
    | MBase τb1 xs1, MBase τb2 xs2 =>
       cast_if_and (decide (τb1 = τb2)) (decide (xs1 ##* xs2))
    | MArray τ1 ws1, MArray τ2 ws2 =>
       cast_if_and (decide (τ1 = τ2)) (decide (ws1 ##* ws2))
    | MStruct t1 wxss1, MStruct t2 wxss2 =>
       cast_if_and3 (decide (t1 = t2)) (decide (wxss1 ##1* wxss2))
         (decide (wxss1 ##2** wxss2))
    | MUnion t1 i1 w1 xs1, MUnion t2 i2 w2 xs2 =>
       cast_if_and6 (decide (t1 = t2)) (decide (i1 = i2))
         (decide (w1 ## w2)) (decide (xs1 ##* xs2))
         (decide (¬(ctree_unmapped w1 ∧ Forall sep_unmapped xs1)))
         (decide (¬(ctree_unmapped w2 ∧ Forall sep_unmapped xs2)))
    | MUnionAll t1 xs1, MUnionAll t2 xs2 =>
       cast_if_and (decide (t1 = t2)) (decide (xs1 ##* xs2))
    | MUnionAll t1 xs1, MUnion t2 _ w2 xs2 =>
       cast_if_and5 (decide (t1 = t2)) (decide (xs1 ##* ctree_flatten w2 ++ xs2))
         (decide (Forall sep_unmapped xs1)) (decide (ctree_valid w2))
         (decide (¬(ctree_unmapped w2 ∧ Forall sep_unmapped xs2)))
    | MUnion t1 _ w1 xs1, MUnionAll t2 xs2 =>
       cast_if_and5 (decide (t1 = t2)) (decide (ctree_flatten w1 ++ xs1 ##* xs2))
         (decide (Forall sep_unmapped xs2)) (decide (ctree_valid w1))
         (decide (¬(ctree_unmapped w1 ∧ Forall sep_unmapped xs1)))
    | _, _ => right _
    end); clear go; abstract first [by subst; constructor|by inversion 1;subst].
  Defined.

  Inductive ctree_subseteq : SubsetEq (ctree K A) :=
    | MBase_subseteq τb xs1 xs2 : xs1 ⊆* xs2 → MBase τb xs1 ⊆ MBase τb xs2
    | MArray_subseteq τ ws1 ws2 : ws1 ⊆* ws2 → MArray τ ws1 ⊆ MArray τ ws2
    | MStruct_subseteq t wxss1 wxss2 :
       wxss1 ⊆1* wxss2 → wxss1 ⊆2** wxss2 → MStruct t wxss1 ⊆ MStruct t wxss2
    | MUnion_subseteq t i w1 w2 xs1 xs2 :
       w1 ⊆ w2 → xs1 ⊆* xs2 →
       ¬(ctree_unmapped w1 ∧ Forall sep_unmapped xs1) →
       MUnion t i w1 xs1 ⊆ MUnion t i w2 xs2
    | MUnionAll_subseteq t xs1 xs2 :
       xs1 ⊆* xs2 → MUnionAll t xs1 ⊆ MUnionAll t xs2
    | MUnionAll_MUnion_subseteq t i xs1 w2 xs2 :
       xs1 ⊆* ctree_flatten w2 ++ xs2 → Forall sep_unmapped xs1 →
       ctree_valid w2 → ¬(ctree_unmapped w2 ∧ Forall sep_unmapped xs2) →
       MUnionAll t xs1 ⊆ MUnion t i w2 xs2.
  #[global] Existing Instance ctree_subseteq.
  Section ctree_subseteq_ind.
    Context (P : ctree K A → ctree K A → Prop).
    Context (Pbase : ∀ τb xs1 xs2,
      xs1 ⊆* xs2 → P (MBase τb xs1) (MBase τb xs2)).
    Context (Parray : ∀ τ ws1 ws2,
      ws1 ⊆* ws2 → Forall2 P ws1 ws2 → P (MArray τ ws1) (MArray τ ws2)).
    Context (Pstruct : ∀ t wxss1 wxss2,
      wxss1 ⊆1* wxss2 → Forall2 (λ wxs1 wxs2, P (wxs1.1) (wxs2.1)) wxss1 wxss2 →
      wxss1 ⊆2** wxss2 → P (MStruct t wxss1) (MStruct t wxss2)).
    Context (Punion : ∀ t i w1 w2 xs1 xs2,
      w1 ⊆ w2 → P w1 w2 → xs1 ⊆* xs2 →
      ¬(ctree_unmapped w1 ∧ Forall sep_unmapped xs1) →
      P (MUnion t i w1 xs1) (MUnion t i w2 xs2)).
    Context (Punion_all : ∀ t xs1 xs2,
      xs1 ⊆* xs2 → P (MUnionAll t xs1) (MUnionAll t xs2)).
    Context (Punion_empty_union : ∀ t i xs1 w2 xs2,
      xs1 ⊆* ctree_flatten w2 ++ xs2 → Forall sep_unmapped xs1 →
      ctree_valid w2 → ¬(ctree_unmapped w2 ∧ Forall sep_unmapped xs2) →
      P (MUnionAll t xs1) (MUnion t i w2 xs2)).
    Definition ctree_subseteq_ind_alt : ∀ w1 w2, ctree_subseteq w1 w2 → P w1 w2.
    Proof. fix H'3 3; destruct 1; eauto using Forall2_impl. Qed.
  End ctree_subseteq_ind.
  Global Instance ctree_subseteq_dec `{EqDecision K} :
    ∀ (w1 w2: ctree K A), Decision (w1 ⊆ w2).
  Proof.
   refine
    (fix go w1 w2 :=
    match w1, w2 return Decision (w1 ⊆ w2) with
    | MBase τb1 xs1, MBase τb2 xs2 =>
       cast_if_and (decide (τb1 = τb2)) (decide (xs1 ⊆* xs2))
    | MArray τ1 ws1, MArray τ2 ws2 =>
       cast_if_and (decide (τ1 = τ2)) (decide (ws1 ⊆* ws2))
    | MStruct t1 wxss1, MStruct t2 wxss2 =>
       cast_if_and3 (decide (t1 = t2))
         (decide (wxss1 ⊆1* wxss2)) (decide (wxss1 ⊆2** wxss2))
    | MUnion t1 i1 w1 xs1, MUnion t2 i2 w2 xs2 =>
       cast_if_and5 (decide (t1 = t2)) (decide (i1 = i2))
         (decide (w1 ⊆ w2)) (decide (xs1 ⊆* xs2))
         (decide (¬(ctree_unmapped w1 ∧ Forall sep_unmapped xs1)))
    | MUnionAll t1 xs1, MUnionAll t2 xs2 =>
       cast_if_and (decide (t1 = t2)) (decide (xs1 ⊆* xs2))
    | MUnionAll t1 xs1, MUnion t2 _ w2 xs2 =>
       cast_if_and5 (decide (t1 = t2)) (decide (xs1 ⊆* ctree_flatten w2 ++ xs2))
         (decide (Forall sep_unmapped xs1)) (decide (ctree_valid w2))
         (decide (¬(ctree_unmapped w2 ∧ Forall sep_unmapped xs2)))
    | _, _ => right _
    end); clear go; abstract first [by subst; constructor|by inversion 1].
  Defined.

  Global Instance ctree_union : Union (ctree K A) :=
    fix go w1 w2 := let _ : Union _ := @go in
    match w1, w2 with
    | MBase τb xs1, MBase _ xs2 => MBase τb (xs1 ∪* xs2)
    | MArray τ ws1, MArray _ ws2 => MArray τ (ws1 ∪* ws2)
    | MStruct t wxss1, MStruct _ wxss2 => MStruct t (wxss1 ∪*∪** wxss2)
    | MUnion t i w1 xs1, MUnion _ _ w2 xs2 => MUnion t i (w1 ∪ w2) (xs1 ∪* xs2)
    | MUnionAll t xs1, MUnionAll _ xs2 => MUnionAll t (xs1 ∪* xs2)
    | w, MUnionAll _ xs | MUnionAll _ xs, w => ctree_merge (∪) w xs
    | _, _ => w1 (* dummy *)
    end.
  Definition ctree_difference_merge : ctree K A → list A → ctree K A :=
    fix go w ys :=
    match w with
    | MBase τb xs => MBase τb (zip_with (∖) xs ys)
    | MArray τ ws => MArray τ (ctree_merge_array go ws ys)
    | MStruct t wxss => MStruct t (ctree_merge_struct (∖) go wxss ys)
    | MUnion t i w xs =>
       let sz := length (ctree_flatten w) in
       let w' := go w (take sz ys) in let xs' := zip_with (∖) xs (drop sz ys) in
       MUnion' t i w' xs'
    | MUnionAll t xs => MUnionAll t (zip_with (∖) xs ys)
    end.
  Global Instance ctree_difference : Difference (ctree K A) :=
    fix go w1 w2 := let _ : Difference _ := @go in
    match w1, w2 with
    | MBase τb xs1, MBase _ xs2 => MBase τb (xs1 ∖* xs2)
    | MArray τ ws1, MArray _ ws2 => MArray τ (ws1 ∖* ws2)
    | MStruct t wxss1, MStruct _ wxss2 => MStruct t (wxss1 ∖*∖** wxss2)
    | MUnion t i w1 xs1, MUnion _ _ w2 xs2 => MUnion' t i (w1 ∖ w2) (xs1 ∖* xs2)
    | MUnionAll t xs1, MUnionAll _ xs2 => MUnionAll t (xs1 ∖* xs2)
    | w, MUnionAll _ xs2 => ctree_difference_merge w xs2
    | _, _ => w1
    end.
End operations.

Section memory_trees.
Context {K : iType} `{Separation A}.
Implicit Types x : A.
Implicit Types xs : list A.
Implicit Types xss : list (list A).
Implicit Types w : ctree K A.
Implicit Types ws : list (ctree K A).
Implicit Types wxs : ctree K A * list A.
Implicit Types wxss : list (ctree K A * list A).
Implicit Types τb : base_type K.
Implicit Types τ : type K.
Implicit Types τs : list (type K).
Local Arguments union _ _ !_ !_ /.
Local Arguments difference _ _ !_ !_ /.
Local Arguments half _ _ !_ /.

Local Hint Resolve Forall_app_2 Forall2_app: core.
Local Hint Immediate seps_disjoint_lr seps_disjoint_ll: core.
Local Hint Immediate seps_disjoint_rl seps_disjoint_rr: core.

Ltac simplifier :=
  repeat match goal with
  | |- _ => progress list_simplifier
  | |- _ => progress autorewrite with simplifier
  | |- _ => progress autorewrite with simplifier in *
  | H : ?zs ∪* ?xs = ?zs ∪* _ |- _ =>
     apply seps_cancel_l in H; [subst xs|by eauto|by eauto]
  | H : ?xs ∪* ?zs = _ ∪* ?zs |- _ =>
     apply seps_cancel_r in H; [subst xs|by eauto|by eauto]
  end.

Lemma ctree_valid_Forall w : ctree_valid w → ctree_Forall sep_valid w.
Proof.
  induction 1 as [|? ws ? IH|? ws ? IH| |]
    using @ctree_valid_ind_alt; simpl; auto; induction IH; simplifier; auto.
Qed.
Local Hint Immediate ctree_valid_Forall: core.

Section merge.
Context {B : Type} `{SeparationOps C}.
Lemma ctree_flatten_merge (f : A → B → C) w ys :
  ctree_flatten (ctree_merge f w ys) = zip_with f (ctree_flatten w) ys.
Proof.
  revert w ys. refine (ctree_ind_alt _ _ _ _ _ _); simpl.
  * done.
  * induction 2; csimpl; intros; rewrite ?zip_with_app_l; f_equal'; auto.
  * induction 2 as [|[]]; intros; simplifier;
      rewrite <-?(assoc_L (++)), ?zip_with_app_l; repeat f_equal; auto.
  * intros. rewrite zip_with_app_l; f_equal'; auto.
  * done.
Qed.
Lemma ctree_merge_valid (f : A → B → C) w ys :
  ctree_valid w → length (ctree_flatten w) = length ys →
  Forall2 (λ x y, sep_unmapped (f x y) → sep_unmapped x) (ctree_flatten w) ys →
  Forall sep_valid (zip_with f (ctree_flatten w) ys) →
  ctree_valid (ctree_merge f w ys).
Proof.
  intros Hw. rewrite <-Forall2_same_length. revert w Hw ys.
  assert (∀ xs ys,
    Forall2 (λ x y, sep_unmapped (f x y) → sep_unmapped x) xs ys →
    Forall sep_unmapped (zip_with f xs ys) → Forall sep_unmapped xs).
  { induction 1; intros; simplifier; constructor; auto. }
  refine (ctree_valid_ind_alt _ _ _ _ _ _); simpl.
  * by constructor.
  * intros τ ws _ IH ys Hys Hys' Hys''; constructor; revert ys Hys Hys' Hys''.
    induction IH; intros; simplifier; auto.
  * intros t ? _ IH ? ys Hys Hys' Hys''; constructor; revert ys Hys Hys' Hys'';
      induction IH as [|[]]; intros; simplifier; constructor; simpl; eauto.
  * intros t i w xs ? IH ? Hun ys Hys Hys' Hys''; simplifier.
    constructor; rewrite ?ctree_flatten_merge; intuition eauto 10.
  * by constructor.
Qed.
End merge.
Hint Rewrite @ctree_flatten_merge : simplifier.

Lemma ctree_flatten_disjoint w1 w2 :
  w1 ## w2 → ctree_flatten w1 ##* ctree_flatten w2.
Proof.
  revert w1 w2. refine (ctree_disjoint_ind_alt _ _ _ _ _ _ _ _);
    simpl; auto 2 using Forall2_bind.
  intros _ wxss1 wxss2 _ IH ?. induction IH; simplifier; auto.
Qed.
Ltac list.solve_length ::=
  repeat rewrite app_length;
  repeat match goal with
  | H : _ ## _ |- _ => apply ctree_flatten_disjoint in H
  | H : Forall2 _ _ _ |- _ => apply Forall2_length in H
  end; assumption || congruence.
Lemma ctree_flatten_union w1 w2 :
  w1 ## w2 → ctree_flatten (w1 ∪ w2) = ctree_flatten w1 ∪* ctree_flatten w2.
Proof.
  revert w1 w2. refine (ctree_disjoint_ind_alt _ _ _ _ _ _ _ _); simpl; auto 1.
  * intros τ ws1 ws2 ? IH. induction IH; simplifier; f_equal; auto.
  * intros t wxss1 wxss2 ? IH ?.
    induction IH as [|[]]; simplifier; repeat f_equal; auto.
  * intros; simplifier; by f_equal.
  * intros; simplifier; f_equal; eauto using seps_commutative.
  * by intros; simplifier.
Qed.
Lemma ctree_flatten_disjoint_l w1 w2 ys :
  w1 ## w2 → ctree_flatten (w1 ∪ w2) ##* ys → ctree_flatten w2 ##* ys.
Proof.
  intros ?. rewrite ctree_flatten_union by done.
  eauto using seps_disjoint_lr, ctree_flatten_disjoint.
Qed.
#[global] Instance ctree_symmetric : Symmetric (@disjoint (ctree K A) _).
Proof.
  induction 1 using @ctree_disjoint_ind_alt; constructor;
    done || apply Forall2_flip; eauto using Forall2_impl.
Qed.
Lemma ctree_disjoint_valid_l w1 w2 : w1 ## w2 → ctree_valid w1.
Proof.
  induction 1 as [|τ ws1 ws2 _ IH|t wxss1 wxss2 _ IH Hwxss| | | |]
    using @ctree_disjoint_ind_alt; simplifier;
    constructor; eauto using seps_disjoint_valid_l.
  * induction IH; auto.
  * clear Hwxss. induction IH; auto.
  * clear IH. induction Hwxss; eauto using seps_disjoint_valid_l.
Qed.
Lemma ctree_disjoint_valid_r w1 w2 : w1 ## w2 → ctree_valid w2.
Proof. intros. by apply ctree_disjoint_valid_l with w1. Qed.
Lemma ctree_flatten_difference_merge w ys :
  ctree_flatten (ctree_difference_merge w ys) = ctree_flatten w ∖* ys.
Proof.
  revert w ys. refine (ctree_ind_alt _ _ _ _ _ _); simpl.
  * done.
  * induction 2; csimpl; intros; rewrite ?zip_with_app_l; f_equal'; auto.
  * induction 2 as [|[]]; intros; simplifier;
      rewrite <-?(assoc_L (++)), ?zip_with_app_l; repeat f_equal; auto.
  * intros; unfold MUnion'; case_decide; rewrite zip_with_app_l; f_equal'; auto.
  * done.
Qed.
Hint Rewrite @ctree_flatten_difference_merge : simplifier.
Lemma ctree_difference_merge_valid w ys :
  ctree_valid w → ys ⊆* ctree_flatten w →
  ctree_valid (ctree_difference_merge w ys).
Proof.
  intros Hw; revert w Hw ys. refine (ctree_valid_ind_alt _ _ _ _ _ _); simpl.
  * constructor; eauto using @seps_difference_valid.
  * intros τ ws _ IH ys Hys; constructor; revert ys Hys.
    induction IH; intros; simplifier; auto.
  * intros t ? _ IH ? ys Hys; constructor; revert ys Hys;
      induction IH as [|[]]; intros; simplifier;
      constructor; simpl; eauto using @seps_difference_valid.
  * intros t i w xs ? IH ? Hun ys Hys; simplifier.
    unfold MUnion'; rewrite ctree_flatten_difference_merge;
      case_decide; constructor; rewrite ?ctree_flatten_difference_merge;
      eauto using @seps_difference_valid.
  * constructor; eauto using @seps_difference_valid.
Qed.
Lemma ctree_disjoint_difference w1 w2 : w1 ⊆ w2 → w1 ## w2 ∖ w1.
Proof.
  revert w1 w2. refine (ctree_subseteq_ind_alt _ _ _ _ _ _ _); simpl.
  * constructor; auto using seps_disjoint_difference.
  * intros τ ws1 ws2 _ IH; constructor. induction IH; simpl; auto.
  * intros t wxss1 wxss2 _ IH Hwxss; constructor.
    + clear Hwxss. induction IH; simpl; auto.
    + clear IH. induction Hwxss as [|[] []]; constructor;
        simpl; auto using seps_disjoint_difference.
  * intros; unfold MUnion'; case_decide; constructor;
      intuition eauto using seps_disjoint_difference,
      ctree_disjoint_valid_l, ctree_flatten_disjoint.
  * constructor; auto using seps_disjoint_difference.
  * intros t i xs1 w2 xs2 ????; unfold MUnion';
      case_decide; constructor; simplifier;
      auto using seps_disjoint_difference, ctree_difference_merge_valid.
Qed.
Ltac list.solve_length ::=
  rewrite ?ctree_flatten_union by done;
  repeat match goal with
  | H : ?w1 ⊆ ?w2 |- _ =>
    unless (w1 ## w2 ∖ w1) by assumption;
    assert (w1 ## w2 ∖ w1) by (by apply ctree_disjoint_difference)
  | H : ?xs1 ⊆* ?xs2 |- _ =>
    unless (xs1 ##* xs2 ∖* xs1) by assumption;
    assert (xs1 ##* xs2 ∖* xs1) by (by apply seps_disjoint_difference)
  end;
  repeat match goal with
  | H : _ ##* _ |- _ => apply ctree_flatten_disjoint_l in H; [|done]
  | H : _ ##* _ |- _ => apply seps_disjoint_lr in H; [|done]
  | H : _ ##* _ |- _ => apply seps_disjoint_rr in H; [|done]
  | H : _ ## _ |- _ => apply ctree_flatten_disjoint in H
  end;
  repeat match goal with
  | H : Forall2 _ _ _ |- _ => apply Forall2_length in H
  | |- _ => rewrite zip_with_length_l_eq
  | |- _ => rewrite replicate_length
  | |- _ => rewrite app_length
  | |- _ => rewrite fmap_length
  | |- _ => rewrite app_length
  end;
  assumption || congruence.

Section merge_merge.
Context {B C D} (f:A → B → A) (g : A → C → A) (h1 : A → D → A) (h2 : C → B → D).
Lemma ctree_merge_merge w ys1 ys2 :
  length (ctree_flatten w) = length ys1 →
  length (ctree_flatten w) = length ys2 →
  zip_with f (zip_with g (ctree_flatten w) ys1) ys2
  = zip_with h1 (ctree_flatten w) (zip_with h2 ys1 ys2) →
  ctree_merge f (ctree_merge g w ys1) ys2
  = ctree_merge h1 w (zip_with h2 ys1 ys2).
Proof.
  rewrite <-!Forall2_same_length. revert ys1 ys2.
  induction w as [|τ ws IH|s wxs IH| |] using @ctree_ind_alt; simpl.
  * intros; simplifier; f_equal; auto.
  * intros ys1 ys2 Hys1 Hys2 Hys3; f_equal. revert ys1 ys2 Hys1 Hys2 Hys3.
    induction IH; intros; simplifier; f_equal; auto.
  * intros ys1 ys2 Hys1 Hys2 Hys3; f_equal. revert ys1 ys2 Hys1 Hys2 Hys3.
    induction IH as [|[]]; intros; simplifier; repeat f_equal; auto.
  * intros; simplifier; f_equal; auto.
  * intros; simplifier; f_equal; auto.
Qed.
End merge_merge.

Section merge_union.
Context {B} (f : A → B → A).
Lemma ctree_merge_disjoint w1 w2 ys :
  w1 ## w2 → length (ctree_flatten w1) = length ys →
  Forall2 (λ x y, sep_unmapped (f x y) → sep_unmapped x) (ctree_flatten w1) ys →
  Forall2 (λ x y, sep_unmapped x → sep_unmapped (f x y)) (ctree_flatten w1) ys →
  zip_with f (ctree_flatten w1) ys ##* ctree_flatten w2 →
  ctree_merge f w1 ys ## w2.
Proof.
  intros Hw. rewrite <-Forall2_same_length. revert w1 w2 Hw ys.
  assert (∀ xs ys,
    Forall2 (λ x y, sep_unmapped (f x y) → sep_unmapped x) xs ys →
    Forall sep_unmapped (zip_with f xs ys) → Forall sep_unmapped xs).
  { induction 1; intros; simplifier; constructor; auto. }
  assert (∀ xs ys,
    Forall2 (λ x y, sep_unmapped x → sep_unmapped (f x y)) xs ys →
    Forall sep_unmapped xs → Forall sep_unmapped (zip_with f xs ys)).
  { induction 1; intros; simplifier; constructor; auto. }
  refine (ctree_disjoint_ind_alt _ _ _ _ _ _ _ _); simpl.
  * by constructor.
  * intros τ ws1 ws2 ? IH ys Hys1 Hys2 Hys3 Hys4. constructor.
    revert ys Hys1 Hys2 Hys3 Hys4.
    induction IH; intros; simplifier; constructor; auto.
  * intros t wxss1 wxss2 ? IH ? ys Hys1 Hys2 Hys3 Hys4; constructor;
      revert ys Hys1 Hys2 Hys3 Hys4; induction IH as [|[][]];
      intros; simplifier; constructor; simpl; eauto.
  * intros; simplifier. constructor; auto.
    rewrite ctree_flatten_merge; intuition eauto 10.
  * by constructor.
  * intros; simplifier; constructor; eauto.
  * intros; simplifier.
    constructor; rewrite ?ctree_flatten_merge; intuition eauto using
      ctree_merge_valid, Forall2_impl, seps_disjoint_valid_l, @Forall2_length.
Qed.
Lemma ctree_merge_union_commute w xs ys :
  length (ctree_flatten w) = length xs → length (ctree_flatten w) = length ys →
  zip_with f (ctree_flatten w ∪* xs) ys
  = zip_with f (ctree_flatten w) ys ∪* xs →
  ctree_merge f (ctree_merge (∪) w xs) ys
  = ctree_merge (∪) (ctree_merge f w ys) xs.
Proof.
  rewrite <-!Forall2_same_length. revert xs ys.
  induction w as [|τ ws IH|s wxs IH| |] using @ctree_ind_alt; simpl.
  * intros; simplifier; f_equal; auto.
  * intros ys1 ys2 Hys1 Hys2 Hys3; f_equal. revert ys1 ys2 Hys1 Hys2 Hys3.
    induction IH; intros; simplifier; f_equal; auto.
  * intros ys1 ys2 Hys1 Hys2 Hys3; f_equal. revert ys1 ys2 Hys1 Hys2 Hys3.
    induction IH as [|[]]; intros; simplifier; repeat f_equal; auto.
  * intros; simplifier; f_equal; auto.
  * intros; simplifier; f_equal; auto.
Qed.
Lemma ctree_merge_union w1 w2 ys :
  w1 ## w2 → length (ctree_flatten w1) = length ys →
  zip_with f (ctree_flatten w1) ys ##* ctree_flatten w2 →
  zip_with f (ctree_flatten w1 ∪* ctree_flatten w2) ys
  = zip_with f (ctree_flatten w1) ys ∪* ctree_flatten w2 →
  ctree_merge f (w1 ∪ w2) ys = ctree_merge f w1 ys ∪ w2.
Proof.
  intros Hw. rewrite <-Forall2_same_length. revert w1 w2 Hw ys.
  refine (ctree_disjoint_ind_alt _ _ _ _ _ _ _ _); simpl.
  * intros; by f_equal.
  * intros τ ws1 ws2 ? IH ys Hys1 Hys2 Hys3; f_equal.
    revert ys Hys1 Hys2 Hys3. induction IH; intros; simplifier; f_equal; auto.
  * intros t wxss1 wxss2 ? IH ? ys Hys1 Hys2 Hys3; f_equal;
      revert ys Hys1 Hys2 Hys3; induction IH as [|[][]];
      intros; simplifier; repeat f_equal; simpl; eauto.
  * intros; simplifier; f_equal; auto.
  * intros; by f_equal.
  * intros; simplifier; f_equal; auto.
    { rewrite (ctree_merge_merge f (∪) (∪) f); auto; try list.solve_length.
      rewrite seps_commutative by done; etransitivity; [eassumption|].
      by rewrite seps_commutative by done. }
    rewrite seps_commutative by done; etransitivity; [eassumption|].
    by rewrite seps_commutative by done.
  * intros; simplifier; f_equal; auto.
    apply ctree_merge_union_commute; list.solve_length.
Qed.
Lemma ctree_merge_map (g : A → A) w ys :
  length (ctree_flatten w) = length ys →
  zip_with f (ctree_flatten w) ys = g <$> ctree_flatten w →
  ctree_merge f w ys = ctree_map g w.
Proof.
  rewrite <-Forall2_same_length. revert ys.
  induction w as [|τ ws IH|t wxss IH| |]
    using @ctree_ind_alt; intros ys Hys Hys'; simplifier; f_equal'; auto.
  * revert ys Hys Hys'. induction IH; intros; simplifier; f_equal'; auto.
  * revert ys Hys Hys'.
    induction IH as [|[]]; intros; simplifier; repeat f_equal'; auto.
Qed.
End merge_union.

Section map_union.
Context (f : A → A).
Hint Rewrite (@app_length A) (@replicate_plus ()) : simplifier.
Lemma ctree_merge_replicate w :
  ctree_merge (λ x _, f x) w (replicate (length (ctree_flatten w)) ())
  = ctree_map f w.
Proof.
  apply ctree_merge_map; auto using replicate_length.
  by rewrite zip_with_replicate_r.
Qed.
Lemma ctree_map_disjoint w1 w2 :
  w1 ## w2 →
  Forall (λ x, sep_unmapped (f x) → sep_unmapped x) (ctree_flatten w1) →
  Forall (λ x, sep_unmapped x → sep_unmapped (f x)) (ctree_flatten w1) →
  f <$> ctree_flatten w1 ##* ctree_flatten w2 → ctree_map f w1 ## w2.
Proof.
  intros ? Hf1 Hf2 Hf3. rewrite <-ctree_merge_replicate.
  apply ctree_merge_disjoint; auto using replicate_length.
  * elim Hf1; simpl; auto.
  * elim Hf2; simpl; auto.
  * rewrite Forall2_fmap_l in Hf3; elim Hf3; simplifier; auto.
Qed.
Lemma ctree_map_union w1 w2 :
  w1 ## w2 → f <$> ctree_flatten w1 ##* ctree_flatten w2 →
  f <$> ctree_flatten w1 ∪* ctree_flatten w2
  = (f <$> ctree_flatten w1) ∪* ctree_flatten w2 →
  ctree_map f (w1 ∪ w2) = ctree_map f w1 ∪ w2.
Proof.
  intros ? Hf1 Hf2. rewrite <-!ctree_merge_replicate, ctree_flatten_union by done.
  rewrite zip_with_length_l_eq by list.solve_length.
  apply ctree_merge_union; auto using replicate_length.
  * rewrite Forall2_fmap_l in Hf1; elim Hf1; simplifier; auto.
  * by rewrite !zip_with_replicate_r_eq by list.solve_length.
Qed.
End map_union.

Lemma ctree_merge_unmapped w ys :
  ctree_flatten w ##* ys → ctree_unmapped w → Forall sep_unmapped ys →
  ctree_unmapped (ctree_merge (∪) w ys).
Proof.
  rewrite ctree_flatten_merge by done. eauto using seps_unmapped_union.
Qed.
Lemma ctree_merge_mapped w ys :
  ctree_flatten w ##* ys →
  ctree_unmapped (ctree_merge (∪) w ys) → ctree_unmapped w.
Proof.
  rewrite ctree_flatten_merge by done. eauto using seps_unmapped_union_l.
Qed.
Lemma ctree_merge_union_valid w ys :
  ctree_valid w → ctree_flatten w ##* ys → Forall sep_unmapped ys →
  ctree_valid (ctree_merge (∪) w ys).
Proof.
  eauto 10 using ctree_merge_valid, seps_union_valid,
    Forall2_length, Forall2_impl, sep_unmapped_union_l'.
Qed.
Lemma ctree_merge_flatten w1 w2 :
  w1 ## w2 → ctree_unmapped w2 → ctree_merge (∪) w1 (ctree_flatten w2) = w1 ∪ w2.
Proof.
  revert w1 w2. refine (ctree_disjoint_ind_alt _ _ _ _ _ _ _ _); simpl.
  * done.
  * intros τ ws1 ws2 ? IH ?; f_equal. induction IH; simplifier; f_equal; auto.
  * intros t wxss1 wxss2 ? IH ??; f_equal.
    induction IH as [|[][]]; simplifier; repeat f_equal; auto.
  * intros t i w1 w2 xs1 xs2; intros; simplifier; f_equal; auto.
  * done.
  * intros; simplifier; naive_solver.
  * intros; simplifier; naive_solver.
Qed.
Lemma ctree_unmapped_union w1 w2 :
  w1 ## w2 → ctree_unmapped w1 → ctree_unmapped w2 → ctree_unmapped (w1 ∪ w2).
Proof.
  intros ?. rewrite ctree_flatten_union by done.
  eauto using seps_unmapped_union, ctree_flatten_disjoint.
Qed.
Lemma ctree_unmapped_union_l w1 w2 :
  w1 ## w2 → ctree_unmapped (w1 ∪ w2) → ctree_unmapped w1.
Proof.
  intros ?. rewrite ctree_flatten_union by done.
  eauto using seps_unmapped_union_l, ctree_flatten_disjoint.
Qed.
Lemma ctree_unmapped_union_r w1 w2 :
  w1 ## w2 → ctree_unmapped (w1 ∪ w2) → ctree_unmapped w2.
Proof.
  intros ?. rewrite ctree_flatten_union by done.
  eauto using seps_unmapped_union_r, ctree_flatten_disjoint.
Qed.
Lemma ctree_positive_l w1 w2 : w1 ## w2 → ctree_empty (w1 ∪ w2) → ctree_empty w1.
Proof.
  intros ?. rewrite ctree_flatten_union by done.
  eauto using seps_positive_l, ctree_flatten_disjoint.
Qed.
Lemma ctree_union_valid w1 w2 : w1 ## w2 → ctree_valid (w1 ∪ w2).
Proof.
  revert w1 w2. refine (ctree_disjoint_ind_alt _ _ _ _ _ _ _ _); simpl.
  * constructor; eauto using seps_union_valid.
  * intros τ ws1 ws2 _ IH. constructor. induction IH; simpl; auto.
  * intros t wxss1 wxss2 _ IH Hwxss. constructor.
    + clear Hwxss. induction IH; simpl; auto.
    + clear IH. induction Hwxss; constructor;
        simpl; eauto using seps_union_valid.
  * constructor; intuition eauto using seps_union_valid,
      ctree_unmapped_union_l, seps_unmapped_union_l.
  * constructor; eauto using seps_union_valid.
  * intros; simplifier.
    constructor; eauto using seps_union_valid, ctree_merge_union_valid.
    intuition eauto using ctree_merge_mapped, seps_unmapped_union_l.
  * intros; simplifier.
    constructor; eauto using seps_union_valid, ctree_merge_union_valid.
    intuition eauto using ctree_merge_mapped, seps_unmapped_union_l.
Qed.
Lemma ctree_commutative w1 w2 : w1 ## w2 → w1 ∪ w2 = w2 ∪ w1.
Proof.
  induction 1 as [|τ ws1 ws2 _ IH|t wxss1 wxss2 _ IH Hwxss| | | |]
    using @ctree_disjoint_ind_alt; f_equal'; auto using seps_commutative.
  * induction IH; f_equal'; auto.
  * induction IH as [|[] []]; simplifier;
      auto using seps_commutative with f_equal.
Qed.
Lemma ctree_merge_id {B} (h : A → B → A) w ys :
  length (ctree_flatten w) = length ys →
  zip_with h (ctree_flatten w) ys = ctree_flatten w → ctree_merge h w ys = w.
Proof.
  rewrite <-Forall2_same_length.
  revert w ys. refine (ctree_ind_alt _ _ _ _ _ _); simpl.
  * by intros; f_equal.
  * intros τ ws IH ys Hys Hys'; f_equal; revert ys Hys Hys'.
    induction IH; intros; simplifier; f_equal; eauto.
  * intros t wxss IH ys Hys Hys'; f_equal; revert ys Hys Hys'.
    induction IH as [|[]]; intros; simplifier; repeat f_equal; auto.
  * intros; simplifier; f_equal; auto.
  * by intros; f_equal.
Qed.
Lemma ctree_flatten_map {B} (h : A → B) w :
  ctree_flatten (ctree_map h w) = h <$> ctree_flatten w.
Proof.
  induction w as [|? ws IH|? wxss IH| |] using @ctree_ind_alt; simpl; auto.
  * induction IH; csimpl; rewrite ?fmap_app; f_equal; auto.
  * induction IH; csimpl; rewrite ?fmap_app; repeat f_equal; auto.
  * rewrite fmap_app; f_equal; auto.
Qed.
Lemma ctree_merge_empty w ys :
  ctree_flatten w ##* ys → Forall (∅ =.) ys → ctree_merge (∪) w ys = w.
Proof. eauto using ctree_merge_id, seps_right_id, Forall2_length. Qed.
Lemma ctree_left_id w1 w2 : w1 ## w2 → ctree_empty w1 → w1 ∪ w2 = w2.
Proof.
  revert w1 w2. refine (ctree_disjoint_ind_alt _ _ _ _ _ _ _ _); simpl.
  * intros; f_equal; auto using seps_left_id.
  * intros τ ws1 ws2 _ IH ?; f_equal. induction IH; simplifier; f_equal; auto.
  * intros t wxss1 wxss2 _ IH Hwxss ?; f_equal.
    induction IH as [|[][]]; simplifier; repeat f_equal;auto using seps_left_id.
  * intros; simplifier; f_equal; auto using seps_left_id.
  * intros; simplifier; f_equal; auto using seps_left_id.
  * intros; simplifier; f_equal; auto using seps_right_id, ctree_merge_empty.
  * intros; simplifier.
    exfalso; naive_solver eauto using Forall_impl, sep_unmapped_empty_alt.
Qed.
Lemma ctree_right_id w1 w2 : w1 ## w2 → ctree_empty w2 → w1 ∪ w2 = w1.
Proof. intros. by rewrite ctree_commutative, ctree_left_id. Qed.
Lemma ctree_merge_disjoint_l w1 w2 ys :
  ctree_valid w1 → ctree_flatten w1 ##* ys →
  ctree_merge (∪) w1 ys ## w2 → w1 ## w2.
Proof.
  intros Hw1. revert w1 Hw1 w2 ys.
  refine (ctree_valid_ind_alt _ _ _ _ _ _); simpl.
  * intros τb xs1 _ w2 ys Hys Hw2. apply (ctree_disjoint_inv_l _ _ _ Hw2).
    constructor; eauto.
  * intros τ ws1 _ IH w2 ys Hys Hw2. apply (ctree_disjoint_inv_l _ _ _ Hw2).
    clear w2 Hw2. intros ws2 Hws2. constructor. revert ws2 ys Hys Hws2.
    induction IH; intros; simplifier; eauto.
  * intros t wxss _ IH _ w2 ys Hys Hw2.
    apply (ctree_disjoint_inv_l _ _ _ Hw2).
    clear w2 Hw2. intros wxss2 Hwxss Hwxss'. constructor.
     + clear Hwxss'. revert wxss2 ys Hys Hwxss.
      induction IH as [|[]]; intros; simplifier; eauto.
     + clear IH Hwxss. revert wxss2 ys Hys Hwxss'.
       induction wxss as [|[]]; intros; simplifier; eauto.
  * intros t i w1 xs1 Hw1 IH _ ? w2 ys Hys Hw2; simplifier.
    apply (ctree_disjoint_inv_l _ _ _ Hw2); clear w2 Hw2.
    + intros w2 xs2 ????. constructor; eauto.
    + intros xs2 ???; simplifier; constructor; eauto.
  * intros t xs1 _ w2 ys Hys Hw2; apply (ctree_disjoint_inv_l _ _ _ Hw2);
      constructor; eauto using seps_unmapped_union_l.
Qed.
Lemma ctree_disjoint_ll w1 w2 w3 : w1 ## w2 → w1 ∪ w2 ## w3 → w1 ## w3.
Proof.
  intros Hw12. revert w1 w2 Hw12 w3.
  refine (ctree_disjoint_ind_alt _ _ _ _ _ _ _ _); simpl.
  * intros τb xs1 xs2 ? w3 Hw3; apply (ctree_disjoint_inv_l _ _ _ Hw3).
    constructor; eauto.
  * intros τ ws1 ws2 _ IH w3 Hw3; apply (ctree_disjoint_inv_l _ _ _ Hw3).
    clear w3 Hw3. intros ws3 Hws3. constructor. revert ws3 Hws3.
    induction IH; intros; simplifier; auto.
  * intros t wxss1 wxss2 _ IH Hwxss w3 Hw3.
    apply (ctree_disjoint_inv_l _ _ _ Hw3). clear w3 Hw3.
    intros wxss3 Hwxss3 Hwxss3'. constructor.
    + clear Hwxss Hwxss3'. revert wxss3 Hwxss3.
      induction IH; intros; simplifier; auto.
    + clear IH Hwxss3. revert wxss3 Hwxss3'.
      induction Hwxss; intros; simplifier; eauto.
  * intros t i w1 w2 xs1 xs2 ? IH Hxs ?? w3 Hw3;
      apply (ctree_disjoint_inv_l _ _ _ Hw3); clear w3 Hw3.
    { constructor; eauto. }
    intros xs3. rewrite ctree_flatten_union by done.
    intros Hxs3 ? _ ?; simplifier.
    constructor; eauto using ctree_disjoint_valid_l,
      seps_disjoint_ll, ctree_flatten_disjoint.
  * intros t xs1 xs2 Hxs w3 Hw3; apply (ctree_disjoint_inv_l _ _ _ Hw3);
      constructor; eauto using seps_unmapped_union_l.
  * intros t i xs1 w2 xs2 ???? w3 Hw3.
    simplifier. apply (ctree_disjoint_inv_l _ _ _ Hw3); clear w3 Hw3.
    { intros w3 xs3 Hw3 ???. constructor; eauto using ctree_disjoint_valid_r.
      apply ctree_flatten_disjoint in Hw3; simplifier; eauto. }
    constructor; simplifier; eauto.
  * intros t i w1 xs1 xs2 ???? w3 Hw3; simplifier.
    apply (ctree_disjoint_inv_l _ _ _ Hw3);
      constructor; simplifier; eauto using ctree_merge_disjoint_l.
Qed.
Lemma ctree_disjoint_lr w1 w2 w3 : w1 ## w2 → w1 ∪ w2 ## w3 → w2 ## w3.
Proof.
  intros ?. rewrite ctree_commutative by done. by apply ctree_disjoint_ll.
Qed.
Lemma ctree_merge_move w1 w2 ys :
  w1 ## w2 → ctree_flatten (w1 ∪ w2) ##* ys →
  Forall sep_unmapped ys → w1 ## ctree_merge (∪) w2 ys.
Proof.
  intros Hw. revert w1 w2 Hw ys.
  refine (ctree_disjoint_ind_alt _ _ _ _ _ _ _ _); simpl.
  * constructor; eauto using seps_disjoint_move_l.
  * intros τ ws1 ws2 Hws IH ys Hys Hys'. constructor. revert ys Hys Hys'.
    induction IH; intros; simplifier; constructor; auto.
  * intros t wxss1 wxss2 Hws IH Hxss ys Hys Hys'. constructor.
    + revert ys Hys Hys'. induction IH as [|[] []]; intros;
        constructor; simplifier; auto.
    + revert ys Hys Hys'. clear IH. induction Hxss as [|[] []]; intros;
        constructor; simplifier; auto using seps_disjoint_move_l.
  * intros t i w1 w2 xs1 xs2 ? IH ?? Hc2 ys; rewrite Forall2_app_inv_l.
    intros (ys1&ys2&Hys1&Hys2&->); rewrite Forall_app; intros [??].
    simplifier. constructor; eauto using seps_disjoint_move_l.
    rewrite ctree_flatten_union in Hys1 by done.
    intros [??]; destruct Hc2; split; eauto using ctree_merge_mapped,
      seps_unmapped_union_l, seps_disjoint_lr, ctree_flatten_disjoint.
  * constructor; eauto using seps_disjoint_move_l.
  * intros t i xs1_ w2 xs2; rewrite Forall2_app_inv_r.
    intros (xs1&xs1'&Hxs1&Hxs1'&->); rewrite Forall_app; intros [??] ? Hc ys.
    simplifier. rewrite (seps_commutative _ xs1), Forall2_app_inv_l by done.
    intros (ys1&ys2&Hys1&Hys2&->); rewrite Forall_app; intros [??].
    simplifier. rewrite seps_commutative in Hys2 by done. constructor.
    + simplifier. eauto using seps_disjoint_move_l.
    + eauto.
    + eauto using ctree_merge_union_valid.
    + intuition eauto using ctree_merge_mapped, seps_unmapped_union_l.
  * intros t i w1 xs1 xs2 ???? ys ??; simplifier.
    constructor; eauto using seps_disjoint_move_l, seps_unmapped_union.
Qed.
Lemma ctree_disjoint_move_l w1 w2 w3 : w1 ## w2 → w1 ∪ w2 ## w3 → w1 ## w2 ∪ w3.
Proof.
  intros Hw12. revert w1 w2 Hw12 w3.
  refine (ctree_disjoint_ind_alt _ _ _ _ _ _ _ _); simpl.
  * intros τb xs1 xs2 ? w3 Hw3.
    pattern w3; apply (ctree_disjoint_inv_l _ _ _ Hw3).
    constructor; eauto using seps_disjoint_move_l.
  * intros τ ws1 ws2 _ IH w3 Hw3; pattern w3;
      apply (ctree_disjoint_inv_l _ _ _ Hw3); clear w3 Hw3.
    intros ws3 Hws3. constructor. revert ws3 Hws3.
    induction IH; intros; simplifier; auto.
  * intros t wxss1 wxss2 _ IH Hwxss w3 Hw3; pattern w3;
      apply (ctree_disjoint_inv_l _ _ _ Hw3); clear w3 Hw3.
    intros wxss3 Hwxss3 Hwxss3'. constructor.
    + clear Hwxss Hwxss3'. revert wxss3 Hwxss3.
      induction IH; intros; simplifier; constructor; simpl; auto.
    + clear IH Hwxss3. revert wxss3 Hwxss3'.
      induction Hwxss; intros; simplifier;
        constructor; simpl; eauto using seps_disjoint_move_l.
  * intros t i w1 w2 xs1 xs2 ? IH Hxs ? Hc2 w3 Hw3; pattern w3;
      apply (ctree_disjoint_inv_l _ _ _ Hw3); clear w3 Hw3; simpl.
    { intros w3 xs3 ????. constructor; eauto using seps_disjoint_move_l.
      assert (w2 ## w3) by eauto using ctree_disjoint_lr.
      intuition eauto using seps_unmapped_union_l, ctree_unmapped_union_l. }
    intros xs3_; rewrite Forall2_app_inv_l; intros (xs3&xs3'&?&?&->).
    rewrite Forall_app; intros [??] ? _. assert (ctree_flatten w2 ##* xs3).
    { apply seps_disjoint_lr with (ctree_flatten w1);
        rewrite <-?ctree_flatten_union; eauto using ctree_flatten_disjoint. }
    simplifier. constructor; eauto using ctree_merge_move, seps_disjoint_move_l.
    intuition eauto using ctree_merge_mapped, seps_unmapped_union_l.
  * intros t xs1 xs2 Hxs w3 Hw3; pattern w3;
      apply (ctree_disjoint_inv_l _ _ _ Hw3); clear w3 Hw3; simpl.
    { constructor; eauto using seps_disjoint_move_l. }
    intros i w2 zs; rewrite Forall2_app_inv_r; intros (?&?&?&?&Hxs3);
      apply zip_with_app_inv in Hxs3;
      destruct Hxs3 as (xs3&xs3'&xs4&xs4'&->&->&->&->&?); intros; simplifier.
    assert (xs3' ##* ctree_flatten w2) by eauto using seps_disjoint_lr.
    assert (xs4' ##* zs) by eauto using seps_disjoint_lr.
    simplifier. constructor.
    + simplifier. apply Forall2_app; rewrite
        seps_commutative by done; eauto using seps_disjoint_move_l.
    + eauto using seps_unmapped_union_l.
    + eauto using ctree_merge_union_valid, seps_unmapped_union_r.
    + intuition eauto using seps_unmapped_union_l, ctree_merge_mapped.
  * intros t i xs1_ w2 xs2; rewrite Forall2_app_inv_r.
    intros (xs1&xs1'&Hxs1&Hxs2&->) ??? w3 Hw3; simplifier. symmetry in Hxs2.
    pattern w3; apply (ctree_disjoint_inv_l _ _ _ Hw3); clear w3 Hw3; simpl.
    { intros w3 xs3; rewrite seps_commutative by done; intros.
      assert (w2 ## w3) by eauto using ctree_merge_disjoint_l.
      constructor; eauto using ctree_union_valid.
      + apply Forall2_app; eauto using seps_disjoint_move_l.
        rewrite ctree_flatten_union by done. apply seps_disjoint_move_l; auto.
        rewrite seps_commutative, <-ctree_flatten_merge by done.
        eauto using ctree_flatten_disjoint.
      + intuition eauto using seps_unmapped_union_l, ctree_unmapped_union_l. }
    intros xs3_. rewrite ctree_flatten_merge, (seps_commutative _ xs1),
      (seps_commutative _ xs1'), Forall2_app_inv_l by done.
    intros (xs3&xs3'&?&?&->); rewrite Forall_app; intros [??] ??; simplifier.
    constructor.
    + simplifier. eauto using seps_disjoint_move_l.
    + eauto.
    + eauto using ctree_merge_union_valid.
    + intuition eauto using seps_unmapped_union_l, ctree_merge_mapped.
  * intros t i w1 xs1 xs2_; rewrite Forall2_app_inv_l.
    intros (xs2&xs2'&Hxs2&Hxs2'&->) ??? w3 Hw3; simplifier.
    pattern w3; apply (ctree_disjoint_inv_l _ _ _ Hw3); clear w3 Hw3; simpl.
    { intros w3 xs3 ????. assert (xs2 ##* ctree_flatten w3).
      { apply seps_disjoint_ll with (ctree_flatten w1); auto.
        rewrite seps_commutative, <-ctree_flatten_merge by auto.
        eauto using ctree_flatten_disjoint. }
      assert (xs3 ##* xs2') by eauto.
      simplifier. rewrite seps_commutative. constructor; eauto.
      + eapply ctree_merge_move; eauto using ctree_merge_disjoint_l.
        rewrite ctree_flatten_union by eauto using ctree_merge_disjoint_l.
        symmetry; apply seps_disjoint_move_l; auto.
        rewrite seps_commutative, <-ctree_flatten_merge by done.
        eauto using ctree_flatten_disjoint.
      + eauto using seps_disjoint_move_l.
      + intuition eauto using ctree_merge_mapped, seps_unmapped_union_r.
      + eauto. }
    intros xs3 ????; simplifier.
    constructor; eauto using seps_disjoint_move_l, seps_unmapped_union.
Qed.
Lemma ctree_merge_associative_1 w ys1 ys2 :
  ctree_valid w → ys1 ##* ys2 → ctree_flatten w ##* ys1 ∪* ys2 →
  ctree_merge (∪) w (ys1 ∪* ys2) = ctree_merge (∪) (ctree_merge (∪) w ys1) ys2.
Proof.
  intros Hw. revert w Hw ys1 ys2.
  refine (ctree_valid_ind_alt _ _ _ _ _ _); simpl.
  * intros; f_equal; auto using seps_associative.
  * intros τ ws _ IH ys1 ys2 Hys Hys'. f_equal. revert ys1 ys2 Hys Hys'.
    induction IH; intros; simplifier; f_equal; auto.
  * intros t wxss _ IH Hwxss ys1 ys2 Hys Hys'. f_equal. revert ys1 ys2 Hys Hys'.
    induction IH as [|[]]; intros; simplifier; f_equal;
      auto using seps_associative with f_equal.
  * intros; simplifier; f_equal; auto using seps_associative.
  * intros; f_equal; auto using seps_associative.
Qed.
Lemma ctree_merge_associative_2 w1 w2 ys :
  w1 ## w2 → ctree_flatten (w1 ∪ w2) ##* ys →
  ctree_merge (∪) (w1 ∪ w2) ys = w1 ∪ ctree_merge (∪) w2 ys.
Proof.
  intros Hw. revert w1 w2 Hw ys.
  refine (ctree_disjoint_ind_alt _ _ _ _ _ _ _ _); simpl.
  * intros. f_equal; auto using seps_associative_rev.
  * intros τ ws1 ws2 Hws IH ys Hys. f_equal. revert ys Hys.
    induction IH; intros; simplifier; f_equal; auto.
  * intros t wxss1 wxss2 Hws IH Hxss ys Hys. f_equal. revert ys Hys.
    induction IH as [|[] []]; intros; simplifier;
      f_equal; auto using seps_associative_rev with f_equal.
  * intros; simplifier; f_equal; auto using seps_associative_rev.
  * intros; f_equal; auto using seps_associative_rev.
  * intros t i xs1_ w2 xs2; rewrite Forall2_app_inv_r.
    intros (xs1&xs1'&Hxs1&Hxs1'&->); rewrite Forall_app; intros [??] ? _ ys.
    simplifier; rewrite Forall2_app_inv_l; intros (ys1&ys2&Hys1&Hys2&->).
    assert (xs1 ##* ys1) by eauto.
    assert (ctree_flatten w2 ∪* ys1 ##* xs1).
    { apply seps_disjoint_move_r; auto. rewrite seps_commutative by done.
      by apply seps_disjoint_move_l. }
    simplifier. by rewrite seps_permute, <-!ctree_merge_associative_1,
      (seps_commutative xs1) by eauto using seps_disjoint_move_l.
  * intros; simplifier. by rewrite ctree_merge_associative_1,
      seps_associative_rev by eauto using seps_disjoint_move_l.
Qed.
Lemma ctree_associative_2 w1 w2 w3 :
  w1 ## w2 → w1 ∪ w2 ## w3 → (w1 ∪ w2) ∪ w3 = w1 ∪ (w2 ∪ w3).
Proof.
  intros Hw12. revert w1 w2 Hw12 w3.
  refine (ctree_disjoint_ind_alt _ _ _ _ _ _ _ _); simpl.
  * intros τb xs1 xs2 ? w3 Hw3; pattern w3;
      apply (ctree_disjoint_inv_l _ _ _ Hw3); intros xs3 ?; simpl.
    f_equal; auto using seps_associative_rev.
  * intros τ ws1 ws2 _ IH w3 Hw3; pattern w3;
      apply (ctree_disjoint_inv_l _ _ _ Hw3); clear w3 Hw3; simpl.
    intros ws3 Hws3; f_equal. revert ws3 Hws3.
    induction IH; intros; simplifier; f_equal; auto.
  * intros t wxss1 wxss2 _ IH Hwxss w3 Hw3; pattern w3;
      apply (ctree_disjoint_inv_l _ _ _ Hw3); clear w3 Hw3; simpl.
    intros wxss3 Hwxss3 Hwxss3'. f_equal.
    revert wxss3 Hwxss3 Hwxss3'. induction IH as [|[][]];
      intros [|[]]; intros; simplifier; f_equal;
      auto using seps_associative_rev with f_equal.
  * intros t i w1 w2 xs1 xs2 ? IH Hxs ?? w3 Hw3; pattern w3;
      apply (ctree_disjoint_inv_l _ _ _ Hw3); clear w3 Hw3; simpl.
    { intros; f_equal; auto using seps_associative_rev. }
    intros xs3 ? _ _ _. simplifier.
    f_equal; auto using ctree_merge_associative_2, seps_associative_rev.
  * intros t xs1_ xs2_ ? w3 Hw3; pattern w3;
      apply (ctree_disjoint_inv_l _ _ _ Hw3); clear w3 Hw3; simpl.
    { intros; f_equal; auto using seps_associative_rev. }
    intros i w3 xs3; rewrite Forall2_app_inv_r.
    intros (xs12&xs12'&?&?&Hxs12) _ ? _. apply zip_with_app_inv in Hxs12.
    destruct Hxs12 as (xs1&xs2&xs1'&xs2'&->&->&->&->&?); simplifier.
    assert (xs2 ##* ctree_flatten w3) by eauto.
    assert (ctree_flatten w3 ∪* xs2 ##* xs1).
    { apply seps_disjoint_move_r; auto. by rewrite seps_commutative. }
    assert (xs3 ##* xs2' ∪* xs1') by (by rewrite seps_commutative).
    simplifier. rewrite <-ctree_merge_associative_1, seps_associative_rev,
      (seps_commutative xs1), (seps_commutative xs1');
      eauto using seps_disjoint_move_l, seps_disjoint_move_r.
  * intros t i xs1_ w2 xs2; rewrite Forall2_app_inv_r;
      intros (xs1&xs1'&?&?&->) _ ? _ w3 Hw3; pattern w3;
      apply (ctree_disjoint_inv_l _ _ _ Hw3); clear w3 Hw3; simpl.
    { intros w3 xs3; simplifier; intros ?? _ _.
      assert (w2 ## w3) by eauto using ctree_merge_disjoint_l.
      rewrite (ctree_commutative w2) by done.
      assert (ctree_flatten (w3 ∪ w2) ##* xs1).
      { rewrite ctree_flatten_union by done. apply seps_disjoint_move_r; auto.
        rewrite <-ctree_flatten_merge by done.
        eauto using ctree_flatten_disjoint. }
      simplifier. by rewrite seps_permute,
        ctree_merge_associative_2, ctree_commutative by eauto. }
    intros xs3_; simplifier;
      rewrite Forall2_app_inv_l; intros (xs3&xs3'&?&?&->) _ _ _.
    assert (ctree_flatten w2 ##* xs3) by eauto.
    assert (ctree_flatten w2 ∪* xs3 ##* xs1).
    { rewrite seps_commutative by eauto; eauto using seps_disjoint_move_r. }
    simplifier. by rewrite <-!ctree_merge_associative_1,
      (seps_commutative xs1), seps_permute by eauto using seps_disjoint_move_l.
  * intros t i w1 xs1 xs2_; rewrite Forall2_app_inv_l;
      intros (xs2&xs2'&?&?&->) _ ? _ w3 Hw3; pattern w3;
      apply (ctree_disjoint_inv_l _ _ _ Hw3); clear w3 Hw3; simpl.
    { intros w3 xs3; simplifier; intros ?? _ _.
      assert (w1 ## w3) by eauto using ctree_merge_disjoint_l.
      assert (ctree_flatten w3 ##* xs2).
      { apply seps_disjoint_rr with (ctree_flatten w1); auto.
        rewrite <-ctree_flatten_merge by done.
        eauto using ctree_flatten_disjoint. }
      assert (ctree_flatten (w3 ∪ w1) ##* xs2).
      { rewrite ctree_flatten_union by done. apply seps_disjoint_move_r; auto.
        rewrite <-ctree_flatten_merge by done.
        eauto using ctree_flatten_disjoint. }
      assert (ctree_flatten (w1 ∪ w3) ##* xs2) by (by rewrite ctree_commutative).
      simplifier. by rewrite seps_associative_rev, (seps_commutative xs2'),
        (ctree_commutative _ w3), <-!ctree_merge_associative_2,
        (ctree_commutative w3) by eauto. }
    intros; simplifier; by rewrite ctree_merge_associative_1,
      seps_associative_rev by eauto using seps_disjoint_move_l.
Qed.
Lemma ctree_associative w1 w2 w3 :
  w2 ## w3 → w1 ## w2 ∪ w3 → w1 ∪ (w2 ∪ w3) = (w1 ∪ w2) ∪ w3.
Proof.
  intros. assert (w1 ## w2).
  { symmetry. by apply ctree_disjoint_ll with w3. }
  assert (w1 ∪ w2 ## w3).
  { symmetry. rewrite ctree_commutative by done.
    by apply ctree_disjoint_move_l; rewrite 1?ctree_commutative by done. }
  by rewrite ctree_associative_2 by done.
Qed.
Lemma ctree_cancel_empty_l w1 w2 : w1 ## w2 → w1 ∪ w2 = w2 → ctree_empty w1.
Proof.
  revert w1 w2. refine (ctree_disjoint_ind_alt _ _ _ _ _ _ _ _); simpl.
  * intros; simplifier; eauto using seps_cancel_empty_l.
  * intros τ ws1 ws2 _ IH ?; simplify_equality'.
    induction IH; simplifier; auto.
  * intros t wxss1 wxss2 _ IH ??; simplifier.
    induction IH as [|[] []]; simplifier; eauto 6 using seps_cancel_empty_l.
  * intros; simplifier; eauto using seps_cancel_empty_l.
  * intros; simplifier; eauto using seps_cancel_empty_l.
  * intros t i xs1 w2 xs2 ?????; simplifier.
    apply Forall_app_2; eauto using seps_cancel_empty_r.
    apply seps_cancel_empty_r with (ctree_flatten w2); auto.
    rewrite <-ctree_flatten_merge by done; congruence.
  * done.
Qed.
Lemma ctree_cancel_empty_r w1 w2 : w1 ## w2 → w1 ∪ w2 = w1 → ctree_empty w2.
Proof.
  intros ?. rewrite ctree_commutative by done. by apply ctree_cancel_empty_l.
Qed.
Lemma ctree_merge_cancel_1 w ys1 ys2 :
  ctree_flatten w ##* ys1 → ctree_flatten w ##* ys2 →
  ctree_merge (∪) w ys1 = ctree_merge (∪) w ys2 → ys1 = ys2.
Proof.
  revert w ys1 ys2. refine (ctree_ind_alt _ _ _ _ _ _); simpl.
  * by intros; simplifier.
  * intros τ ws IH ys1 ys2; rewrite (inj_iff (MArray τ)).
    revert ys1 ys2. induction IH; intros; simplifier; f_equal; auto.
  * intros t wxss IH ys1 ys2; rewrite (inj_iff (MStruct t)).
    revert ys1 ys2.
    induction IH as [|[]]; intros; simplifier; repeat f_equal; eauto.
  * intros; simplifier; f_equal; eauto.
  * by intros; simplifier.
Qed.
Lemma ctree_merge_cancel_2 w1 w2 ys :
  ctree_flatten w1 ##* ys → ctree_flatten w2 ##* ys →
  ctree_merge (∪) w1 ys = ctree_merge (∪) w2 ys → w1 = w2.
Proof.
  revert w1 w2 ys. refine (ctree_ind_alt _ _ _ _ _ _); simpl.
  * by intros τb xs1 [] ys ???; simplifier.
  * intros τ ws1 IH [|? ws2| | |]; simpl; try discriminate. cut (∀ ys1 ys2,
      ws1 ≫= ctree_flatten ##* ys1 → ws2 ≫= ctree_flatten ##* ys2 →
      ys1 = ys2 → ctree_merge_array (ctree_merge (∪)) ws1 ys1 =
        ctree_merge_array (ctree_merge (∪)) ws2 ys2 → ws1 = ws2).
    { naive_solver. }
    revert ws2. induction IH as [|w1 ws1];
      intros [|w2 ws2] ys1_ ys2_; csimpl; try discriminate; auto.
    rewrite !Forall2_app_inv_l; intros (ys1&ys1'&?&?&->) (ys2&ys2'&?&?&->) ??.
    simplifier. assert (length ys1 = length ys2).
    { erewrite <-(zip_with_length_same_r _ _ _ ys1),  <-(zip_with_length_same_r
        _ _ _ ys2), <-!(ctree_flatten_merge (∪)) by eauto; congruence. }
    simplifier; f_equal; eauto.
  * intros t wxss1 IH [| |s' wxss2| |]; simpl; try discriminate. cut (∀ ys1 ys2,
      wxss1 ≫= (λ wxs, ctree_flatten (wxs.1) ++ wxs.2) ##* ys1 →
      wxss2 ≫= (λ wxs, ctree_flatten (wxs.1) ++ wxs.2) ##* ys2 → ys1 = ys2 →
      ctree_merge_struct (∪) (ctree_merge (∪)) wxss1 ys1
      = ctree_merge_struct (∪) (ctree_merge (∪)) wxss2 ys2 →
      wxss1 = wxss2); [naive_solver|].
    revert wxss2. induction IH as [|[w1 xs1] wxss1];
      intros [|[w2 xs2] wxss2] ys1_ ys2_; simpl; try discriminate; auto.
    repeat setoid_rewrite Forall2_app_inv_l.
    intros (?&ys1''&(ys1&ys1'&?&?&->)&?&->) (?&ys2''&(ys2&ys2'&?&?&->)&?&->) ??.
    simplifier. assert (length ys1 = length ys2).
    { erewrite <-(zip_with_length_same_r _ _ _ ys1),  <-(zip_with_length_same_r
        _ _ _ ys2), <-!(ctree_flatten_merge (∪)) by eauto; congruence. }
    assert (length ys1' = length ys2').
    { erewrite <-(zip_with_length_same_r _ _ _ ys1'),  <-(zip_with_length_same_r
        _ _ _ ys2') by eauto; f_equal; eauto. }
    simplifier; repeat f_equal; eauto.
  * intros t i w xs1 IH [| | |s' i' w2 xs2|] ys1_; simpl; try discriminate.
    generalize (eq_refl ys1_); generalize ys1_ at 2 4 7 8; intros ys2_.
    rewrite !Forall2_app_inv_l;
      intros ? (ys1&ys1'&?&?&->) (ys2&ys2'&?&?&->) ?; simplifier.
    assert (length ys1 = length ys2).
    { erewrite <-(zip_with_length_same_r _ _ _ ys1),  <-(zip_with_length_same_r
        _ _ _ ys2), <-!(ctree_flatten_merge (∪)) by eauto; congruence. }
    simplifier; f_equal; eauto.
  * by intros t xs1 [] ys ???; simplifier.
Qed.
Lemma ctree_cancel_l w1 w2 w3 :
  w3 ## w1 → w3 ## w2 → w3 ∪ w1 = w3 ∪ w2 → w1 = w2.
Proof.
  intros Hw31. revert w3 w1 Hw31 w2.
  refine (ctree_disjoint_ind_alt _ _ _ _ _ _ _ _); simpl.
  * by intros τb xs3 xs1 ? w2 Hw2; pattern w2;
      apply (ctree_disjoint_inv_l _ _ _ Hw2); intros xs2 ??; simplifier.
  * intros τ ws3 ws1 _ IH w2 Hw2; pattern w2;
      apply (ctree_disjoint_inv_l _ _ _ Hw2); clear w2 Hw2; simpl.
    intros ws2; rewrite !(inj_iff (MArray τ)); revert ws2.
    induction IH; intros; simplifier; f_equal; auto.
  * intros t wxss3 wxss1 _ IH Hwxss w2 Hw2; pattern w2;
      apply (ctree_disjoint_inv_l _ _ _ Hw2); clear w2 Hw2; simpl.
    intros wxss2; rewrite !(inj_iff (MStruct t)); revert wxss2.
    induction IH as [|[][]]; intros [|[]]; intros;
      simplifier; repeat f_equal; eauto.
  * intros t i w3 w1 xs3 xs1 ? IH ?? Hc w2 Hw2; pattern w2;
      apply (ctree_disjoint_inv_l _ _ _ Hw2); clear w2 Hw2; simpl.
    { intros w2 xs2 ?????; simplifier; f_equal; auto. }
    intros xs2_; rewrite Forall2_app_inv_l; intros (xs2&xs2'&?&?&->) ? _ _ ?.
    simplifier. cut (ctree_flatten w1 = xs2); [intros <-; intuition|].
    apply seps_cancel_l with (ctree_flatten w3);
      auto using ctree_flatten_disjoint.
    rewrite <-ctree_flatten_union, <-ctree_flatten_merge
        by auto using ctree_flatten_disjoint; f_equal; auto.
  * intros t xs3 xs1 ? w2 Hw2; pattern w2;
      apply (ctree_disjoint_inv_l _ _ _ Hw2); clear w2 Hw2; [|done].
    by intros xs2 ??; simplifier.
  * intros t i xs3_ w1 xs1. generalize (eq_refl xs3_);
      generalize xs3_ at 2 4 5 8; intros xs4_; rewrite Forall2_app_inv_r;
      intros ? (xs3&xs3'&?&?&->) _ _ _ w2 Hw2; pattern w2;
      apply (ctree_disjoint_inv_l _ _ _ Hw2); clear w2 Hw2; simpl; [done|].
    intros i' w2 xs2; rewrite Forall2_app_inv_r;
      intros (xs4&xs4'&?&?&->) _ ???; simplifier.
    assert (length xs3 = length xs4).
    { erewrite <-(zip_with_length_same_r _ (##) _ xs3),
        <-(zip_with_length_same_r _ (##) _ xs4),
        <-!(ctree_flatten_merge (∪)) by eauto; congruence. }
    simplifier; f_equal; eauto using ctree_merge_cancel_2.
  * intros t i w3 xs3 xs1_; rewrite Forall2_app_inv_l;
      intros (xs1&xs1'&?&?&->) ??? w2 Hw2; pattern w2;
      apply (ctree_disjoint_inv_l _ _ _ Hw2); clear w2 Hw2; simpl.
    { intros w2 xs2 ??? Hc ?; simplifier.
      cut (xs1 = ctree_flatten w2); [intros ->; intuition|].
      apply seps_cancel_l with (ctree_flatten w3);
        auto using ctree_flatten_disjoint.
      rewrite <-ctree_flatten_union, <-ctree_flatten_merge
        by auto using ctree_flatten_disjoint; f_equal; auto. }
    intros; simplifier; repeat f_equal; eauto using ctree_merge_cancel_1.
Qed.
Lemma ctree_merge_subseteq w ys :
  ctree_valid w → ctree_flatten w ##* ys → w ⊆ ctree_merge (∪) w ys.
Proof.
  intros Hw. revert w Hw ys. refine (ctree_valid_ind_alt _ _ _ _ _ _); simpl.
  * constructor; auto using seps_union_subseteq_l.
  * intros τ ws _ IH ys Hys; constructor; revert ys Hys.
    induction IH; intros; simplifier; constructor; auto.
  * intros t wxss _ IH _ ys Hys; constructor; revert ys Hys.
    + induction IH as [|[]]; intros; constructor; simplifier; auto.
    + induction IH as [|[]]; intros; constructor; simplifier;
        auto using seps_union_subseteq_l.
  * intros; simplifier; constructor; auto using seps_union_subseteq_l.
  * constructor; auto using seps_union_subseteq_l.
Qed.
Local Hint Immediate seps_disjoint_difference: core.
Local Hint Extern 5 => symmetry; apply seps_disjoint_difference: core.
Lemma seps_reflexive xs : Forall sep_valid xs → xs ⊆* xs.
Proof. induction 1; auto using sep_reflexive. Qed.
Lemma ctree_subseteq_reflexive w : ctree_valid w → w ⊆ w.
Proof.
  revert w. refine (ctree_valid_ind_alt _ _ _ _ _ _).
  * constructor; auto using seps_reflexive.
  * intros τ ws _ IH; constructor. induction IH; auto.
  * intros t wxss _ IH Hwxss; constructor.
    + clear Hwxss. induction IH; auto.
    + clear IH. induction Hwxss; auto using seps_reflexive.
  * constructor; auto using seps_reflexive.
  * constructor; auto using seps_reflexive.
Qed.
Lemma ctree_union_subseteq_l w1 w2 : w1 ## w2 → w1 ⊆ w1 ∪ w2.
Proof.
  revert w1 w2. refine (ctree_disjoint_ind_alt _ _ _ _ _ _ _ _); simpl.
  * constructor; auto using seps_union_subseteq_l.
  * intros τ ws1 ws2 _ IH; constructor. induction IH; simpl; auto.
  * intros t wxss1 wxss2 _ IH Hwxss; constructor.
    + clear Hwxss. induction IH; simpl; auto.
    + clear IH. induction Hwxss as [|[][]];
        constructor; simpl; auto using seps_union_subseteq_l.
  * constructor; auto using seps_union_subseteq_l.
  * constructor; auto using seps_union_subseteq_l.
  * intros t i xs1 w2 xs2 ????; simplifier; constructor.
    + simplifier. auto using seps_union_subseteq_r.
    + auto.
    + eauto using ctree_merge_union_valid.
    + intuition eauto using ctree_merge_mapped, seps_unmapped_union_l.
  * intros; simplifier; constructor;
      auto using seps_union_subseteq_l, ctree_merge_subseteq.
Qed.
Lemma MUnion'_flatten t i w xs :
  ctree_flatten (MUnion' t i w xs) = ctree_flatten w ++ xs.
Proof. by unfold MUnion'; case_decide. Qed.
Lemma ctree_difference_merge_unmapped_1 w ys :
  ys ⊆* ctree_flatten w → Forall sep_unmapped ys →
  ctree_unmapped (ctree_difference_merge w ys) → ctree_unmapped w.
Proof.
  intros ?. rewrite ctree_flatten_difference_merge by done.
  eauto using seps_unmapped_difference_1.
Qed.
Local Hint Immediate ctree_disjoint_difference: core.
Local Hint Extern 5 => symmetry; apply ctree_disjoint_difference: core.
Lemma ctree_merge_difference_merge w ys :
  ctree_valid w → ys ⊆* ctree_flatten w → Forall sep_unmapped ys →
  ctree_merge (∪) (ctree_difference_merge w ys) ys = w.
Proof.
  assert (∀ xs ys, ys ⊆* xs → xs ∖* ys ∪* ys = xs).
  { intros. rewrite seps_commutative by eauto.
    auto using seps_union_difference. }
  intros Hw. revert w Hw ys. refine (ctree_valid_ind_alt _ _ _ _ _ _); simpl.
  * intros; f_equal; auto.
  * intros τ ws _ IH ys Hys Hys'; f_equal; revert ys Hys Hys'.
    induction IH; intros; simplifier; f_equal; auto.
  * intros t wxss ? IH ? ys Hys Hys'; f_equal; revert ys Hys Hys'.
    induction IH as [|[]]; intros; simplifier; f_equal; auto with f_equal.
  * intros; simplifier;
      unfold MUnion'; case_decide; simplifier; [|f_equal; auto].
    naive_solver eauto using seps_unmapped_difference_1,
      ctree_difference_merge_unmapped_1.
  * intros; f_equal; auto.
Qed.
Lemma ctree_union_difference w1 w2 : w1 ⊆ w2 → w1 ∪ w2 ∖ w1 = w2.
Proof.
  revert w1 w2. refine (ctree_subseteq_ind_alt _ _ _ _ _ _ _); simpl.
  * intros; f_equal; auto using seps_union_difference.
  * intros τ ws1 ws2 _ IH; f_equal. induction IH; f_equal'; auto.
  * intros t wxss1 wxss2 _ IH Hwxss; f_equal. induction IH as [|[][]];
      simplifier; repeat f_equal; auto using seps_union_difference.
  * intros; unfold MUnion'; case_decide; simplifier;
      f_equal'; auto using seps_union_difference.
    by rewrite ctree_merge_flatten by intuition eauto.
  * intros; f_equal; auto using seps_union_difference.
  * intros; simplifier. unfold MUnion'; rewrite decide_False by intuition eauto
      using seps_unmapped_difference_1, ctree_difference_merge_unmapped_1.
    simplifier. by rewrite ctree_merge_difference_merge, seps_commutative,
      seps_union_difference by eauto.
Qed.
Lemma ctree_difference_empty_rev w1 w2 :
  w1 ⊆ w2 → ctree_empty (w2 ∖ w1) → w1 = w2.
Proof.
  revert w1 w2. refine (ctree_subseteq_ind_alt _ _ _ _ _ _ _); simpl.
  * intros; f_equal; auto using seps_difference_empty_rev.
  * intros τ ws1 ws2 _ IH ?; f_equal. induction IH; simplifier; f_equal; auto.
  * intros t wxss1 wxss2 _ IH Hwxss ?; f_equal.
    induction IH as [|[][]]; simplifier;
      repeat f_equal; auto using seps_difference_empty_rev.
  * intros t i w1 w2 xs1 xs2; rewrite MUnion'_flatten.
    intros; simplifier. f_equal; auto using seps_difference_empty_rev.
  * intros; f_equal; auto using seps_difference_empty_rev.
  * intros t i xs1_ w2 xs2; rewrite MUnion'_flatten.
    rewrite Forall2_app_inv_r; intros (xs1&xs1'&?&?&->) ????; simplifier.
    assert (xs1' = xs2) by auto using seps_difference_empty_rev; subst.
    cut (xs1 = ctree_flatten w2); [intros ->; intuition|].
    apply seps_difference_empty_rev; auto.
Qed.
Lemma ctree_flatten_subseteq w1 w2 :
  w1 ⊆ w2 → ctree_flatten w1 ⊆* ctree_flatten w2.
Proof.
  intros. rewrite <-(ctree_union_difference w1 w2) by done.
  rewrite ctree_flatten_union by auto using ctree_disjoint_difference.
  apply seps_union_subseteq_l, ctree_flatten_disjoint;
    auto using ctree_disjoint_difference.
Qed.
Lemma ctree_unshared_weaken w1 w2 :
  ctree_unshared w1 → w1 ⊆ w2 → ctree_unshared w2.
Proof. eauto using seps_unshared_weaken, ctree_flatten_subseteq. Qed.
Lemma ctree_unshared_unmapped w1 w2 :
  ctree_unshared w1 → w1 ## w2 → ctree_unmapped w2.
Proof. eauto using seps_disjoint_unshared_unmapped, ctree_flatten_disjoint. Qed.
Lemma ctree_empty_unmapped w : ctree_empty w → ctree_unmapped w.
Proof. eauto using Forall_impl, sep_unmapped_empty_alt. Qed.

Lemma ctree_splittable_union w : w ## w → ctree_splittable (w ∪ w).
Proof.
  cut (∀ w1 w2, w1 ## w2 → w1 = w2 → ctree_splittable (w1 ∪ w2)); [eauto|].
  refine (ctree_disjoint_ind_alt _ _ _ _ _ _ _ _); simpl.
  * intros; simplify_equality'; auto using seps_splittable_union.
  * intros τ ? ws _ IH ?; simplify_equality'.
    induction ws; simplifier; auto.
  * intros t ? wxss _ IH ??; simplify_equality'.
    induction wxss; simplifier; auto using seps_splittable_union.
  * intros; simplify_equality'; auto using seps_splittable_union.
  * intros; simplify_equality'; auto using seps_splittable_union.
  * done.
  * done.
Qed.
Lemma ctree_disjoint_map (P : A → Prop) f g w :
  (∀ x, sep_valid x → P x → f x ## g x) →
  (∀ x, sep_valid x → P x → sep_unmapped (f x) → sep_unmapped x) →
  (∀ x, sep_valid x → P x → sep_unmapped (g x) → sep_unmapped x) →
  ctree_valid w → ctree_Forall P w → ctree_map f w ## ctree_map g w.
Proof.
  intros ???; revert w.
  assert (∀ xs, Forall sep_valid xs → Forall P xs → f <$> xs ##* g <$> xs).
  { induction 1; intros; decompose_Forall_hyps; constructor; eauto. }
  assert (∀ xs, Forall sep_valid xs → Forall P xs →
    Forall sep_unmapped (f <$> xs) → Forall sep_unmapped xs).
  { induction 1; intros; decompose_Forall_hyps; constructor; eauto. }
  assert (∀ xs, Forall sep_valid xs → Forall P xs →
    Forall sep_unmapped (g <$> xs) → Forall sep_unmapped xs).
  { induction 1; intros; decompose_Forall_hyps; constructor; eauto. }
  refine (ctree_valid_ind_alt _ _ _ _ _ _); simpl.
  * constructor; auto.
  * intros τ ws _ IH ?; constructor.
    induction IH; decompose_Forall_hyps; auto.
  * intros t wxss _ IH Hxs; constructor;
      induction IH as [|[]]; decompose_Forall_hyps; constructor; simpl; auto.
  * constructor; decompose_Forall_hyps;
      rewrite ?ctree_flatten_map; naive_solver.
  * constructor; auto.
Qed.
Lemma ctree_union_map (f g : A → A) w :
  ctree_map f w ∪ ctree_map g w = ctree_map (λ x, f x ∪ g x) w.
Proof.
  assert (∀ xs, (f <$> xs) ∪* (g <$> xs) = (λ x, f x ∪ g x) <$> xs).
  { induction xs; f_equal'; auto. }
  induction w as [|τ ws IH|t wxss IH| |] using @ctree_ind_alt; f_equal'; auto.
  * induction IH; f_equal'; auto.
  * induction IH as [|[]]; repeat f_equal'; auto.
Qed.
Lemma ctree_map_id (P : A → Prop) f w :
  (∀ x, P x → f x = x) → ctree_Forall P w → ctree_map f w = w.
Proof.
  intros ?.
  assert (∀ xs, Forall P xs → f <$> xs = xs) by (induction 1; f_equal'; auto).
  induction w as [|τ ws IH|t wxss IH| |] using @ctree_ind_alt;
    intros; decompose_Forall_hyps; f_equal; auto.
  * induction IH; decompose_Forall_hyps; f_equal; auto.
  * induction IH as [|[]]; decompose_Forall_hyps; repeat f_equal'; auto.
Qed.
Lemma ctree_map_compose {B C} (f : A → B) (g : B → C) w :
  ctree_map (g ∘ f) w = ctree_map g (ctree_map f w).
Proof.
  induction w as [|τ ws IH|t wxss IH| |] using @ctree_ind_alt;
    f_equal'; rewrite <-?list_fmap_compose; auto.
  * by apply Forall_fmap_ext.
  * eapply Forall_fmap_ext, Forall_impl; eauto.
    intros [??] ?; f_equal'; rewrite <-?list_fmap_compose; auto.
Qed.
Notation h := (ctree_map sep_half).
Hint Rewrite @ctree_flatten_map : simplifier.
Lemma ctree_merge_half w ys :
  ctree_flatten w ##* ys → Forall sep_splittable (ctree_flatten w ∪* ys) →
  h (ctree_merge (∪) w ys) = ctree_merge (∪) (h w) (½* ys).
Proof.
  revert w ys. refine (ctree_ind_alt _ _ _ _ _ _); simpl.
  * intros; f_equal; auto using seps_union_half_distr.
  * intros τ ws IH ys Hys Hys'; f_equal; revert ys Hys Hys'.
    induction IH; intros; simplifier; f_equal; auto.
  * intros t wxss IH ys Hys Hys'; f_equal; revert ys Hys Hys'.
    induction IH as [|[]]; intros; simplifier;
      repeat f_equal; auto using seps_union_half_distr.
  * intros; simplifier; f_equal; auto using seps_union_half_distr.
  * intros; f_equal; auto using seps_union_half_distr.
Qed.
Lemma ctree_union_half_distr w1 w2 :
  w1 ## w2 → ctree_splittable (w1 ∪ w2) → h (w1 ∪ w2) = h w1 ∪ h w2.
Proof.
  revert w1 w2. refine (ctree_disjoint_ind_alt _ _ _ _ _ _ _ _); simpl.
  * intros; f_equal; auto using seps_union_half_distr.
  * intros τ ws1 ws2 _ IH ?; f_equal. induction IH; simplifier; f_equal; auto.
  * intros t wxss1 wxss2 _ IH ??; f_equal. induction IH; simplifier;
      repeat f_equal; auto using seps_union_half_distr.
  * intros; simplifier; f_equal; auto using seps_union_half_distr.
  * intros; f_equal; auto using seps_union_half_distr.
  * intros t i xs1_ w2 xs2; rewrite Forall2_app_inv_r;
      intros (xs1&xs1'&?&?&->) ????; simplifier.
    f_equal; auto using seps_union_half_distr, ctree_merge_half.
  * intros t i w1 xs1 xs2_; rewrite Forall2_app_inv_l;
      intros (xs2&xs2'&?&?&->) ????; simplifier.
    f_equal; auto using seps_union_half_distr, ctree_merge_half.
Qed.
End memory_trees.
