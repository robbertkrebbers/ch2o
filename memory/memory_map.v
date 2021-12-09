(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
From stdpp Require Import fin_map_dom.
Require Export memory_trees cmap.

Local Open Scope ctype_scope.

Definition mem K := (cmap K (pbit K)).
#[global] Instance mem_sep_ops `{Env K} : SeparationOps (mem K) := _.
#[global] Instance mem_sep `{Env K} : Separation (mem K) := _.
Typeclasses Opaque mem.
Global Hint Extern 0 (Separation _) => apply (_ : Separation (mem _)): core.

Section operations.
  Context `{Env K}.

  Global Instance cmap_dom: Dom (mem K) indexset := λ m,
    let (m) := m in dom _ m.
  Global Instance cmap_valid: Valid (env K * memenv K) (mem K) := λ ΓΔ m,
    let (Γ,Δ) := ΓΔ in
    (**i 1). *) ✓{Γ} Δ ∧
    (**i 2). *) (∀ o τ,
      cmap_car m !! o = Some (Freed τ) → Δ ⊢ o : τ ∧ ¬index_alive Δ o) ∧
    (**i 3). *) (∀ o w μ,
      cmap_car m !! o = Some (Obj w μ) →
      ∃ τ, Δ ⊢ o : τ ∧ index_alive Δ o ∧ (Γ,Δ) ⊢ w : τ ∧ ¬ctree_empty w).
  Definition memenv_of (m : mem K) : memenv K :=
    let (m) := m in
    let f x : type K * bool :=
      match x with Freed τ => (τ,true) | Obj w _ => (type_of w,false) end in
    f <$> m.
  Global Instance cmap_valid': Valid (env K) (mem K) := λ Γ m,
    ✓{Γ,memenv_of m} m.
  Definition index_alive' (m : mem K) (o : index) : Prop :=
    match cmap_car m !! o with Some (Obj _ _) => True | _ => False end.
  Definition cmap_erase (m : mem K) : mem K :=
    let (m) := m in CMap (omap (λ x, '(w,μ) ← maybe_Obj x; Some (Obj w μ)) m).
  Definition cmap_erased (m : mem K) := cmap_erase m = m.

  Global Instance cmap_lookup_ref:
      LookupE (env K) (index * ref K) (mtree K) (mem K) := λ Γ or m,
    (cmap_car m !! or.1 ≫= maybe2 Obj) ≫= lookupE Γ (or.2) ∘ fst.
  Global Instance cmap_lookup:
      LookupE (env K) (addr K) (mtree K) (mem K) := λ Γ a m,
    guard (addr_strict Γ a);
    w ← m !!{Γ} (addr_index a, addr_ref Γ a);
    if decide (addr_is_obj a) then Some w
    else guard (ctree_unshared w); w !!{Γ} (addr_ref_byte Γ a).
  Definition cmap_alter_ref (Γ : env K) (g : mtree K → mtree K)
      (o : index) (r : ref K) (m : mem K) : mem K :=
    let (m) := m in CMap (alter (cmap_elem_map (ctree_alter Γ g r)) o m).
  Definition cmap_alter (Γ : env K) (g : mtree K → mtree K)
      (a : addr K) (m : mem K) : mem K :=
    let G := if decide (addr_is_obj a) then g
             else ctree_alter_byte Γ g (addr_ref_byte Γ a) in
    cmap_alter_ref Γ G (addr_index a) (addr_ref Γ a) m.
  Definition cmap_singleton (Γ : env K) (a : addr K)
      (μ : bool) (w : mtree K) : mem K :=
    CMap {[ addr_index a := Obj (ctree_singleton Γ (addr_ref Γ a) w) μ ]}.
End operations.

Arguments cmap_lookup_ref _ _ _ !_ !_ /.
Notation "'{ m }" := (memenv_of m) (at level 8, format "''{' m }") : C_scope.

Section memory_map.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types m : mem K.
Implicit Types Δ : memenv K.
Implicit Types τ σ : type K.
Implicit Types o : index.
Implicit Types w : mtree K.
Implicit Types rs : ref_seg K.
Implicit Types r : ref K.
Implicit Types a : addr K.
Implicit Types g : mtree K → mtree K.
Implicit Types α β μ : bool.

Lemma cmap_dom_alt m o : o ∉ dom indexset m ↔ cmap_car m !! o = None.
Proof. destruct m as [m]; simpl. by rewrite not_elem_of_dom. Qed.
Lemma cmap_dom_memenv_of m : dom indexset '{m} = dom indexset m.
Proof. destruct m; f_equal'; by apply dom_fmap_L. Qed.
Lemma cmap_dom_None Γ Δ m o : ✓{Γ,Δ} m → Δ !! o = None → o ∉ dom indexset m.
Proof.
  intros (_&Hm1&Hm2) ?.
  rewrite cmap_dom_alt, eq_None_not_Some; intros [[τ|μ w] ?].
  * destruct (Hm1 o τ) as ([??]&_); naive_solver.
  * destruct (Hm2 o μ w) as (?&[??]&_); naive_solver.
Qed.
Lemma index_alive_spec' m o : index_alive' m o ↔ index_alive '{m} o.
Proof.
  unfold index_alive'; destruct m as [m]; simpl; split.
  * intros. destruct (m !! o) as [[|w]|] eqn:?; try done.
    by exists (type_of w); simplify_map_eq.
  * intros [τ ?]; simplify_map_eq.
    by destruct (m !! o) as [[|w []]|] eqn:?.
Qed.
Lemma index_alive_1' m o : index_alive' m o → index_alive '{m} o.
Proof. by rewrite index_alive_spec'. Qed.
Lemma index_alive_2' m o : index_alive '{m} o → index_alive' m o.
Proof. by rewrite index_alive_spec'. Qed.
#[global] Instance index_alive_dec' m o : Decision (index_alive' m o).
Proof.
  refine
    match cmap_car m !! o as mw' return Decision (match mw' with
       Some (Obj _ _) => True | _ => False end) with
    | Some (Obj _ _) => left _ | _ => right _
    end; tauto.
Defined.
Lemma index_alive_erase' m o :
  index_alive' (cmap_erase m) o = index_alive' m o.
Proof.
  unfold index_alive'; destruct m as [m]; simpl.
  rewrite lookup_omap. by destruct (m !! o) as [[]|].
Qed.

Lemma index_typed_lookup_cmap m o τ :
  '{m} ⊢ o : τ → ∃ x, cmap_car m !! o = Some x ∧
  match x with Freed τ' => τ' = τ | Obj w _ => type_of w = τ end.
Proof.
  intros [β Hβ]. destruct m as [m]; simplify_map_eq.
  by destruct (m !! o) as [[]|]; simplify_equality'; do 2 eexists; eauto.
Qed.
Lemma cmap_valid_Freed Γ Δ m o τ :
  ✓{Γ,Δ} m → cmap_car m !! o = Some (Freed τ) →
  Δ ⊢ o : τ ∧ ¬index_alive Δ o ∧ ✓{Γ} τ.
Proof. intros (HΔ&Hm&_) ?; destruct (Hm o τ); eauto. Qed.
Lemma cmap_valid_Obj Γ Δ m o w μ :
  ✓{Γ,Δ} m → cmap_car m !! o = Some (Obj w μ) →
  ∃ τ, Δ ⊢ o : τ ∧ index_alive Δ o ∧ (Γ,Δ) ⊢ w : τ ∧ ¬ctree_empty w.
Proof. intros (HΔ&_&Hm) ?; destruct (Hm o w μ) as (τ&?&?&?&?); eauto. Qed.
Lemma cmap_valid_memenv_valid Γ Δ m : ✓{Γ,Δ} m → ✓{Γ} Δ.
Proof. by intros []. Qed.
Lemma cmap_index_typed_valid Γ Δ m o τ : ✓{Γ,Δ} m → Δ ⊢ o : τ → ✓{Γ} τ.
Proof. eauto using cmap_valid_memenv_valid, index_typed_valid. Qed.
Lemma cmap_empty_valid Γ Δ : ✓{Γ} Δ → ✓{Γ,Δ} (∅ : mem K).
Proof. by intros; split_and !; intros *; simplify_map_eq. Qed.
Lemma cmap_empty_valid' Γ : ✓{Γ} (∅ : mem K).
Proof. eauto using cmap_empty_valid, memenv_empty_valid. Qed.
Lemma cmap_valid_weaken Γ1 Γ2 Δ1 Δ2 m :
  ✓ Γ1 → ✓{Γ1,Δ1} m → Γ1 ⊆ Γ2 → Δ1 ⊆ Δ2 → ✓{Γ2} Δ2 → ✓{Γ2,Δ2} m.
Proof.
  intros ? (HΔ&Hm1&Hm2) ???; split_and !; eauto using memenv_valid_weaken.
  * intros o τ ?; destruct (Hm1 o τ); eauto 10 using index_typed_weaken,
      memenv_forward_alive, memenv_subseteq_forward.
  * intros o w μ ?; destruct (Hm2 o w μ) as (τ&?&?&?&?);
      eauto 10 using ctree_typed_weaken, index_typed_weaken,
      memenv_subseteq_forward, memenv_subseteq_alive.
Qed.
Lemma cmap_valid_weaken' Γ1 Γ2 m : ✓ Γ1 → ✓{Γ1} m → Γ1 ⊆ Γ2 → ✓{Γ2} m.
Proof.
  intros. eapply cmap_valid_weaken;
    eauto using memenv_valid_weaken, cmap_valid_memenv_valid.
Qed.
Lemma cmap_valid_weaken_squeeze Γ1 Γ2 Δ1 Δ2 m1 m2 :
  ✓ Γ1 → ✓{Γ1,Δ1} m2 → Γ1 ⊆ Γ2 → Δ1 ⇒ₘ Δ2 →
  ✓{Γ2,Δ2} m1 → '{m1} = '{m2} → ✓{Γ2,Δ2} m2.
Proof.
  intros ? (_&_&Hm2') ?? (?&Hm1&Hm1') Hm; split_and !; eauto.
  * intros o τ Ho. apply (f_equal (.!! o)) in Hm.
    destruct m1 as [m1], m2 as [m2]; simplify_equality'.
    rewrite !lookup_fmap, Ho in Hm; simplify_equality'.
    destruct (m1 !! o) as [[]|] eqn:?; simplify_equality'; eauto.
  * intros o w μ Ho. apply (f_equal (.!! o)) in Hm.
    destruct m1 as [m1], m2 as [m2]; simplify_equality'.
    rewrite !lookup_fmap, Ho in Hm; simplify_equality'.
    destruct (m1 !! o) as [[|w' μ']|] eqn:?; simplify_equality'.
    destruct (Hm1' o w' μ') as (τ1&?&?&?&?); auto.
    destruct (Hm2' o w μ) as (τ2&?&?&?&?); auto.
    assert (Δ2 ⊢ o : τ2) by eauto using index_typed_weaken;
      simplify_type_equality'; eauto 10 using ctree_typed_weaken.
Qed.
Lemma cmap_valid_sep_valid Γ Δ m : ✓{Γ,Δ} m → sep_valid m.
Proof.
  destruct m as [m]; intros Hm o [τ|w μ] ?; [done|].
  destruct (cmap_valid_Obj Γ Δ (CMap m) o w μ)
    as (?&?&?&?&?); simpl; eauto using ctree_typed_sep_valid.
Qed.
Lemma cmap_memenv_of_subseteq Γ Δ m : ✓{Γ,Δ} m → '{m} ⊆ Δ.
Proof.
  rewrite map_subseteq_spec. intros (_&Hm1&Hm2) o [τ β].
  destruct m as [m]; simplify_map_eq.
  destruct (m !! o) as [[τ'|w μ]|] eqn:?; intros; simplify_equality'.
  * destruct (Hm1 o τ) as [[[] ?] Halive]; auto. by destruct Halive; exists τ.
  * destruct (Hm2 o w μ) as (?&[??]&[??]&?&?); simplify_type_equality; auto.
Qed.

Lemma cmap_erase_empty : cmap_erase (∅ : mem K) = ∅.
Proof. simpl. by rewrite omap_empty. Qed.
Lemma cmap_erased_empty : cmap_erased (∅ : mem K).
Proof. by apply cmap_erase_empty. Qed.
Lemma cmap_erase_erase m : cmap_erase (cmap_erase m) = cmap_erase m.
Proof.
  destruct m as [m]; f_equal'; apply map_eq; intros o.
  rewrite !lookup_omap. by destruct (m !! o) as [[]|].
Qed.
Lemma cmap_erased_spec m : cmap_erased m → cmap_erase m = m.
Proof. done. Qed.
Lemma cmap_erased_erase m : cmap_erased (cmap_erase m).
Proof. apply cmap_erase_erase. Qed.
Lemma cmap_erase_erased m1 m2 : cmap_erase m1 = m2 → cmap_erased m2.
Proof. intros <-. apply cmap_erased_erase. Qed.
Lemma cmap_erase_valid Γ Δ m : ✓{Γ,Δ} m →  ✓{Γ,Δ} (cmap_erase m).
Proof.
  destruct m as [m]; unfold lookupE; intros (?&?&?); split_and !; simpl in *.
  * done.
  * intros o τ. rewrite lookup_omap. by destruct (m !! o) as [[]|].
  * intros o w maloc. rewrite lookup_omap.
    destruct (m !! o) as [[]|] eqn:?; intros; simplify_equality'; eauto.
Qed.
Lemma cmap_dom_erase m o : o ∈ dom indexset (cmap_erase m) → o ∈ dom indexset m.
Proof.
  destruct m as [m]; simpl.
  rewrite !elem_of_dom, lookup_omap, <-!not_eq_None_Some.
  destruct (m !! o) as [[]|]; naive_solver.
Qed.

Lemma cmap_lookup_ref_empty Γ o r : ∅ !!{Γ} (o,r) = None.
Proof. by unfold lookupE, cmap_lookup_ref; simplify_map_eq. Qed.
Lemma cmap_lookup_empty Γ a : ∅ !!{Γ} a = None.
Proof.
  unfold lookupE, cmap_lookup. rewrite cmap_lookup_ref_empty.
  by case_option_guard.
Qed.
Lemma cmap_lookup_ref_erase Γ m o r : cmap_erase m !!{Γ} (o,r) = m !!{Γ} (o,r).
Proof.
  unfold lookupE, cmap_lookup_ref; destruct m as [m]; simpl.
  rewrite lookup_omap. by destruct (m !! _) as [[]|].
Qed.
Lemma cmap_lookup_erase Γ m a : cmap_erase m !!{Γ} a = m !!{Γ} a.
Proof. unfold lookupE, cmap_lookup. by rewrite cmap_lookup_ref_erase. Qed.
Lemma cmap_lookup_ref_weaken Γ1 Γ2 Δ m o r w :
  ✓ Γ1 → m !!{Γ1} (o,r) = Some w → Γ1 ⊆ Γ2 → m !!{Γ2} (o,r) = Some w.
Proof.
  destruct m; intros; simplify_option_eq; eauto using ctree_lookup_weaken.
Qed.
Lemma cmap_lookup_weaken Γ1 Γ2 Δ m a w σ :
  ✓ Γ1 → (Γ1,Δ) ⊢ a : TType σ → m !!{Γ1} a = Some w → Γ1 ⊆ Γ2 →
  m !!{Γ2} a = Some w.
Proof.
  unfold lookupE, cmap_lookup; intros; case_option_guard; simplify_equality'.
  erewrite option_guard_True, <-addr_ref_weaken,
    <-addr_ref_byte_weaken by eauto using addr_strict_weaken.
  destruct (m !!{Γ1} _) as [w'|] eqn:?; simplify_equality'.
  by erewrite cmap_lookup_ref_weaken by eauto; simpl.
Qed.
Lemma cmap_lookup_ref_le Γ m o r1 r2 w' :
  m !!{Γ} (o,r1) = Some w' → r1 ⊆* r2 → m !!{Γ} (o,r2) = Some w'.
Proof.
  destruct m as [m]; intros; simplify_option_eq.
  by erewrite ctree_lookup_le by eauto.
Qed.
Lemma cmap_lookup_ref_freeze_proper Γ q1 q2 m o1 r1 o2 r2 w1 w2 :
  m !!{Γ} (o1,r1) = Some w1 → m !!{Γ} (o2,r2) = Some w2 →
  o1 = o2 → freeze q1 <$> r1 = freeze q2 <$> r2 → w1 = w2.
Proof.
  destruct m as [m]; intros; simplify_option_eq;
    eauto using ctree_lookup_freeze_proper.
Qed.
Lemma cmap_lookup_unfreeze Γ m a w :
  m !!{Γ} a = Some w → m !!{Γ} (freeze false a) = Some w.
Proof.
  unfold lookupE, cmap_lookup; intros; case_option_guard; simplify_equality'.
  rewrite addr_index_freeze, addr_ref_freeze, addr_ref_byte_freeze.
  rewrite option_guard_True by auto using addr_strict_freeze_2.
  destruct (m !!{Γ} (_, addr_ref _ _)) as [w'|] eqn:?; simplify_equality'.
  erewrite cmap_lookup_ref_le
    by eauto using cmap_lookup_ref_le, ref_freeze_le_r; simpl.
  by rewrite (decide_iff _ _ _ _ (addr_is_obj_freeze _ _)).
Qed.
Lemma cmap_lookup_ref_Some Γ Δ m o r w :
  ✓ Γ → ✓{Γ,Δ} m → m !!{Γ} (o,r) = Some w →
  ∃ τ σ, Δ ⊢ o : τ ∧ Γ ⊢ r : τ ↣ σ ∧ (Γ,Δ) ⊢ w : σ.
Proof.
  destruct m as [m]; simpl; intros ? Hm ?.
  destruct (m !! o) as [[|w' μ]|] eqn:Hw; simplify_equality'.
  destruct (cmap_valid_Obj Γ Δ (CMap m) o w' μ) as (τ&?&_&?&_); auto.
  destruct (ctree_lookup_Some Γ Δ w' τ r w) as (σ&?&?); eauto.
Qed.
Lemma cmap_lookup_typed Γ Δ m a w σ :
  ✓ Γ → ✓{Γ,Δ} m → (Γ,Δ) ⊢ a : TType σ → m !!{Γ} a = Some w → (Γ,Δ) ⊢ w : σ.
Proof.
  unfold lookupE, cmap_lookup; intros; case_option_guard; simplify_equality'.
  destruct (m !!{Γ} _) as [w'|] eqn:?; simplify_equality'.
  destruct (cmap_lookup_ref_Some Γ Δ m (addr_index a) (addr_ref Γ a) w')
    as (τ&σ'&?&?&?); auto; simplify_option_eq; simplify_type_equality.
  * cut (σ = σ'); [by intros ->|].
    erewrite (addr_is_obj_type _ _ _ σ) by eauto.
    assert (Δ ⊢ addr_index a : addr_type_object a)
      by eauto using addr_typed_index; simplify_type_equality.
    eauto using ref_set_offset_typed_unique, addr_typed_ref_base_typed.
  * erewrite addr_not_is_obj_type by eauto; eauto using ctree_lookup_byte_typed.
Qed.
Lemma cmap_lookup_strict Γ m a w : m !!{Γ} a = Some w → addr_strict Γ a.
Proof. by unfold lookupE, cmap_lookup; intros; simplify_option_eq. Qed.
Lemma cmap_lookup_Some Γ Δ m w a :
  ✓ Γ → ✓{Γ,Δ} m → m !!{Γ} a = Some w → (Γ,Δ) ⊢ w : type_of w.
Proof.
  unfold lookupE, cmap_lookup; intros; case_option_guard; simplify_equality'.
  destruct (m !!{Γ} _) as [w'|] eqn:?; simplify_equality'.
  destruct (cmap_lookup_ref_Some Γ Δ m (addr_index a) (addr_ref Γ a) w')
    as (τ&σ'&?&?&?); auto; simplify_option_eq;
    eauto using ctree_lookup_byte_typed, type_of_typed.
Qed.
Lemma cmap_lookup_ref_cons Γ m o rs r :
  m !!{Γ} (o,rs :: r) = m !!{Γ} (o,r) ≫= lookupE Γ rs.
Proof. destruct m as [m]; simpl. by destruct (m !! o) as [[|w' μ]|]. Qed.
Lemma cmap_lookup_ref_app Γ m o r1 r2 :
  m !!{Γ} (o,r1 ++ r2) = m !!{Γ} (o,r2) ≫= lookupE Γ r1.
Proof.
  destruct m as [m]; simpl.
  destruct (m !! o) as [[|w' μ]|] eqn:Hw; simplify_equality'; auto.
  by rewrite ctree_lookup_app.
Qed.
Lemma cmap_lookup_elt Γ Δ m a rs σ σ' :
  ✓ Γ → (Γ,Δ) ⊢ a : TType σ → addr_strict Γ a → Γ ⊢ rs : σ ↣ σ' → 
  m !!{Γ} (addr_elt Γ rs a) = m !!{Γ} a ≫= lookupE Γ rs.
Proof.
  unfold lookupE at 1 3, cmap_lookup; intros; simpl.
  rewrite !option_guard_True by eauto using addr_elt_strict.
  erewrite addr_ref_elt, addr_ref_byte_elt, addr_index_elt by eauto.
  rewrite cmap_lookup_ref_cons; destruct (m !!{Γ} _) as [w|]; simpl; auto.
  rewrite decide_True by eauto using addr_ref_byte_is_obj_parent; simpl.
  destruct (w !!{Γ} rs); simpl; auto.
  by rewrite decide_True by eauto using addr_ref_byte_is_obj.
Qed.
Lemma cmap_alter_ref_le Γ g o r1 r2 m :
  r1 ⊆* r2 → cmap_alter_ref Γ g o r1 m = cmap_alter_ref Γ g o r2 m.
Proof.
  destruct m as [m]; intros; f_equal'. by erewrite ctree_alter_le by eauto.
Qed.
Lemma cmap_erase_alter_ref Γ g m o r :
  cmap_erase (cmap_alter_ref Γ g o r m) = cmap_alter_ref Γ g o r (cmap_erase m).
Proof.
  destruct m as [m]; f_equal'; apply map_eq; intros o'.
  destruct (decide (o = o')); simplify_map_eq; auto.
  by destruct (m !! _) as [[]|].
Qed.
Lemma cmap_erase_alter Γ g m a :
  cmap_erase (cmap_alter Γ g a m) = cmap_alter Γ g a (cmap_erase m).
Proof. apply cmap_erase_alter_ref. Qed.
Lemma cmap_alter_ref_memenv_of Γ Δ m g o r w :
  ✓ Γ → ✓{Γ,Δ} m → m !!{Γ} (o,r) = Some w → type_of (g w) = type_of w →
  '{cmap_alter_ref Γ g o r m} = '{m}.
Proof.
  destruct m as [m]; intros; apply map_eq; intros o'; simpl.
  destruct (decide (o' = o)); simplify_map_eq; auto.
  destruct (m !! o) as [[|w' μ]|] eqn:?; simplify_equality'; do 2 f_equal.
  destruct (cmap_valid_Obj Γ Δ (CMap m) o w' μ) as (τ&?&_&?&_); auto.
  destruct (ctree_lookup_Some Γ Δ w' τ r w) as (σ'&?&?);
    eauto using ctree_alter_type_of_weak, type_of_typed.
Qed.
Lemma cmap_alter_memenv_of Γ Δ m g a w :
  ✓ Γ → ✓{Γ,Δ} m → m !!{Γ} a = Some w → type_of (g w) = type_of w →
  '{cmap_alter Γ g a m} = '{m}.
Proof.
  unfold lookupE, cmap_lookup; intros; case_option_guard; simplify_equality'.
  destruct (m !!{Γ} _) as [w'|] eqn:?; simplify_equality'.
  eapply cmap_alter_ref_memenv_of; eauto; simplify_option_eq; eauto.
  cut (✓{Γ} (type_of w')); [eauto using ctree_alter_byte_type_of|].
  destruct (cmap_lookup_ref_Some Γ Δ m (addr_index a) (addr_ref Γ a) w')
    as (?&?&?&?&?); simplify_type_equality; eauto using ctree_typed_type_valid.
Qed.
Lemma cmap_alter_ref_valid Γ Δ m g o r w :
  ✓ Γ → ✓{Γ,Δ} m → m !!{Γ} (o,r) = Some w → (Γ,Δ) ⊢ g w : type_of w →
  ¬ctree_unmapped (g w) → ✓{Γ,Δ} (cmap_alter_ref Γ g o r m).
Proof.
  destruct m as [m]; intros ? (?&Hm&Hm') ???; split_and !; simpl in *; auto.
  { intros o' τ; rewrite lookup_alter_Some;
      intros [(?&[]&?&?)|[??]]; simplify_option_eq; eauto. }
  intros o' ? μ; rewrite lookup_alter_Some;
    intros [(?&[|w' μ']&?&?)|[??]]; simplify_map_eq; eauto.
    destruct (Hm' o' w' μ') as (τ&?&?&?&?); naive_solver eauto using
    ctree_alter_lookup_Forall, ctree_alter_typed, @ctree_empty_unmapped.
Qed.
Lemma cmap_alter_ref_weaken Γ1 Γ2 Δ m g o r :
  ✓ Γ1 → Γ1 ⊆ Γ2 → ✓{Γ1,Δ} m →
  cmap_alter_ref Γ1 g o r m = cmap_alter_ref Γ2 g o r m.
Proof.
  destruct m as [m]; intros ?? (_&_&Hm); f_equal'; apply alter_ext.
  intros [|w' μ] ?; f_equal'. naive_solver eauto using ctree_alter_weaken.
Qed.
Lemma cmap_alter_valid Γ Δ m g a w :
  ✓ Γ → ✓{Γ,Δ} m → m !!{Γ} a = Some w → (Γ,Δ) ⊢ g w : type_of w →
  ¬ctree_unmapped (g w) → ✓{Γ,Δ} (cmap_alter Γ g a m).
Proof.
  unfold cmap_alter, lookupE, cmap_lookup;
    intros; case_option_guard; simplify_equality'.
  destruct (m !!{Γ} _) as [w'|] eqn:?; simplify_equality'.
  simplify_option_eq; eauto using cmap_alter_ref_valid.
  destruct (cmap_lookup_ref_Some Γ Δ m (addr_index a) (addr_ref Γ a) w')
    as (τ&σ&?&?&?); auto.
  assert ((Γ,Δ) ⊢ w : ucharT)
    by eauto using ctree_lookup_byte_typed; simplify_type_equality'.
  eapply cmap_alter_ref_valid; intuition eauto 3 using
    ctree_alter_byte_typed, type_of_typed, ctree_alter_byte_unmapped.
Qed.
Lemma cmap_alter_ref_commute Γ g1 g2 m o1 r1 o2 r2 :
  (o1 ≠ o2 ∨ o1 = o2 ∧ r1 ## r2) →
  cmap_alter_ref Γ g1 o1 r1 (cmap_alter_ref Γ g2 o2 r2 m)
  = cmap_alter_ref Γ g2 o2 r2 (cmap_alter_ref Γ g1 o1 r1 m).
Proof.
  destruct m as [m]; intros [?|[??]]; simplify_equality'; f_equal.
  * by rewrite alter_commute.
  * rewrite <-!alter_compose.
    apply alter_ext; intros [|??] ?; f_equal'; auto using ctree_alter_commute.
Qed.
Lemma cmap_alter_ref_compose Γ g1 g2 m o r :
  cmap_alter_ref Γ (g1 ∘ g2) o r m
  = cmap_alter_ref Γ g1 o r (cmap_alter_ref Γ g2 o r m).
Proof.
  destruct m as [m]; simplify_equality'; f_equal; rewrite <-alter_compose.
  apply alter_ext; intros [|??] ?; f_equal'; auto using ctree_alter_compose.
Qed.
Lemma cmap_alter_ref_ext_lookup Γ g1 g2 m o r w :
  m !!{Γ} (o,r) = Some w → g1 w = g2 w →
  cmap_alter_ref Γ g1 o r m = cmap_alter_ref Γ g2 o r m.
Proof.
  destruct m as [m]; intros; f_equal'; apply alter_ext.
  intros [?|w' ?] ?; simplify_option_eq; f_equal'.
  eauto using ctree_alter_ext_lookup.
Qed.
Lemma cmap_alter_commute Γ Δ g1 g2 m a1 a2 w1 w2 τ1 τ2 :
  ✓ Γ → ✓{Γ,Δ} m → a1 ##{Γ} a2 → 
  (Γ,Δ) ⊢ a1 : TType τ1 → m !!{Γ} a1 = Some w1 → (Γ,Δ) ⊢ g1 w1 : τ1 →
  (Γ,Δ) ⊢ a2 : TType τ2 → m !!{Γ} a2 = Some w2 → (Γ,Δ) ⊢ g2 w2 : τ2 →
  cmap_alter Γ g1 a1 (cmap_alter Γ g2 a2 m)
  = cmap_alter Γ g2 a2 (cmap_alter Γ g1 a1 m).
Proof.
  unfold cmap_alter, lookupE, cmap_lookup; simplify_equality'.
  intros ?? [?|[[??]|(Ho&Hr&?&?&?)]] ??????; auto using cmap_alter_ref_commute.
  repeat case_option_guard; simplify_equality'.
  destruct (m !!{Γ} (addr_index a1, _)) as [w1'|] eqn:?,
    (m !!{Γ} (addr_index a2, _)) as [w2'|] eqn:?; simplify_equality'.
  rewrite <-!(cmap_alter_ref_le _ _ _ _ (addr_ref Γ a1)), Ho, !Hr,
    !(cmap_alter_ref_le _ _ _ (freeze true <$> addr_ref Γ a2) (addr_ref Γ a2)),
    <-!cmap_alter_ref_compose by eauto using ref_freeze_le_l.
  assert (w1' = w2') by eauto using cmap_lookup_ref_freeze_proper.
  assert (τ1 = ucharT) by eauto using addr_not_is_obj_type.
  assert (τ2 = ucharT) by eauto using addr_not_is_obj_type.
  eapply cmap_alter_ref_ext_lookup; eauto; simplify_option_eq.
  destruct (cmap_lookup_ref_Some Γ Δ m
    (addr_index a2) (addr_ref Γ a2) w2') as (τ'&σ&?&?&?);
    eauto using ctree_alter_byte_commute.
Qed.
Lemma cmap_lookup_ref_alter Γ Δ g m o r1 r2 w :
  ✓ Γ → ✓{Γ,Δ} m → m !!{Γ} (o,freeze false <$> r1) = Some w →
  freeze true <$> r1 = freeze true <$> r2 →
  cmap_alter_ref Γ g o r2 m !!{Γ} (o,r1) = Some (g w).
Proof.
  destruct m as [m]; simpl; intros.
  destruct (m !! o) as [[|w' μ]|] eqn:?; simplify_map_eq.
  eauto using ctree_lookup_alter.
Qed.
(** We need [addr_is_obj a] because padding bytes are ignored *)
Lemma cmap_lookup_alter Γ Δ g m a w :
  ✓ Γ → ✓{Γ,Δ} m → addr_is_obj a → m !!{Γ} a = Some w →
  cmap_alter Γ g a m !!{Γ} a = Some (g w).
Proof.
  unfold lookupE, cmap_lookup, cmap_alter;
    intros; case_option_guard; simplify_map_eq.
  destruct (m !!{Γ} _) as [w'|] eqn:?; simplify_equality'.
  by erewrite cmap_lookup_ref_alter by eauto using
    cmap_lookup_ref_le, ref_freeze_le_r; simplify_option_eq.
Qed.
Lemma cmap_lookup_alter_not_obj Γ Δ g m a w τ :
  ✓ Γ → ✓{Γ,Δ} m → ¬addr_is_obj a →
  (Γ,Δ) ⊢ a : TType τ → m !!{Γ} a = Some w → (Γ,Δ) ⊢ g w : τ →
  ctree_unshared (g w) → cmap_alter Γ g a m !!{Γ} a =
  Some (ctree_lookup_byte_after Γ (addr_type_base a) (addr_ref_byte Γ a) (g w)).
Proof.
  unfold lookupE, cmap_lookup, cmap_alter;
    intros; case_option_guard; simplify_map_eq.
  destruct (m !!{Γ} _) as [w'|] eqn:?; simplify_equality'.
  erewrite cmap_lookup_ref_alter by eauto using
    cmap_lookup_ref_le, ref_freeze_le_r; simpl; case_decide; [done|].
  assert (Δ ⊢ addr_index a : addr_type_object a)
    by eauto using addr_typed_index.
  assert (Γ ⊢ addr_ref Γ a : addr_type_object a ↣ addr_type_base a).
  { eapply addr_typed_ref_typed; eauto. }
  destruct (cmap_lookup_ref_Some Γ Δ m (addr_index a)
    (addr_ref Γ a) w') as (?&?&?&?&?); auto; simplify_type_equality.
  assert (τ = ucharT) by eauto using addr_not_is_obj_type; subst.
  simplify_option_eq by
    eauto using ctree_alter_byte_Forall, pbit_indetify_unshared.
  by erewrite ctree_lookup_alter_byte by eauto; simplify_option_eq.
Qed.
Lemma cmap_lookup_ref_alter_disjoint Γ g m o1 r1 o2 r2 w1:
  ✓ Γ → (o1 ≠ o2 ∨ o1 = o2 ∧ r1 ## r2) → m !!{Γ} (o1,r1) = Some w1 →
  cmap_alter_ref Γ g o2 r2 m !!{Γ} (o1,r1) = Some w1.
Proof.
  destruct m as [m]; intros ? [?|[??]] ?; simplify_equality';
    destruct (m !! _) as [[|w' μ]|] eqn:?; simplify_map_eq;
    eauto using ctree_lookup_alter_disjoint.
Qed.
Lemma cmap_lookup_alter_disjoint Γ Δ g m a1 a2 w1 w2 τ2 :
  ✓ Γ → ✓{Γ,Δ} m → a1 ##{Γ} a2 → m !!{Γ} a1 = Some w1 →
  (Γ,Δ) ⊢ a2 : TType τ2 → m !!{Γ} a2 = Some w2 → (Γ,Δ) ⊢ g w2 : τ2 →
  (ctree_unshared w2 → ctree_unshared (g w2)) →
  cmap_alter Γ g a2 m !!{Γ} a1 = Some w1.
Proof.
  unfold lookupE, cmap_lookup, cmap_alter;
    intros ? Hm [?|[[-> ?]|(->&Ha&?&?&?)]] ?? Hw2 ??;
    repeat case_option_guard; simplify_equality'; try contradiction.
  { destruct (m !!{_} (addr_index a1, _)) as [w'|] eqn:?; simplify_equality'.
    by erewrite cmap_lookup_ref_alter_disjoint by eauto. }
  { destruct (m !!{_} (_, addr_ref Γ a1)) as [w'|] eqn:?; simplify_equality'.
    by erewrite cmap_lookup_ref_alter_disjoint by eauto. }
  destruct (m !!{_} (_, addr_ref Γ a1)) as [w1'|] eqn:?,
    (m !!{_} (_, addr_ref Γ a2)) as [w2'|] eqn:?; simplify_equality'.
  assert (w1' = w2') by eauto using cmap_lookup_ref_freeze_proper.
  assert (τ2 = ucharT%T)
    by eauto using addr_not_is_obj_type; simplify_option_eq.
  destruct (cmap_lookup_ref_Some Γ Δ m (addr_index a2)
    (addr_ref Γ a2) w2') as (?&?&?&?&?); auto; simplify_type_equality.
  erewrite cmap_lookup_ref_alter
    by eauto using cmap_lookup_ref_le, ref_freeze_le_r; simpl.
  assert (ctree_unshared (g w2))
    by eauto using ctree_lookup_byte_Forall, pbit_indetify_unshared.
  by erewrite option_guard_True, ctree_lookup_alter_byte_ne
    by eauto using ctree_alter_byte_Forall, pbit_indetify_unshared.
Qed.
Lemma cmap_singleton_freeze Γ β a μ w :
  cmap_singleton Γ (freeze β a) μ w = cmap_singleton Γ a μ w.
Proof.
  unfold cmap_singleton. rewrite addr_index_freeze, addr_ref_freeze.
  destruct β.
  * by erewrite ctree_singleton_le by eauto using ref_freeze_le_l.
  * by erewrite <-ctree_singleton_le by eauto using ref_freeze_le_r.
Qed.
Lemma cmap_erase_singleton Γ a μ w :
  cmap_erase (cmap_singleton Γ a μ w) = cmap_singleton Γ a μ w.
Proof. by simpl; erewrite omap_singleton by done. Qed.
Lemma cmap_singleton_sep_valid Γ Δ a μ w τ :
  ✓ Γ → (Γ,Δ) ⊢ a : TType τ → addr_is_obj a → addr_strict Γ a →
  (Γ,Δ) ⊢ w : τ → ¬ctree_empty w → sep_valid (cmap_singleton Γ a μ w).
Proof.
  intros ????? Hperm o [|] ?; simplify_map_eq.
  assert (τ = addr_type_base a) by eauto using addr_is_obj_type; subst.
  split; eauto using ctree_typed_sep_valid,
    ctree_singleton_typed, addr_typed_ref_typed, ctree_singleton_Forall_inv.
Qed.
Lemma cmap_singleton_valid Γ Δ a μ w τ :
  ✓ Γ → ✓{Γ} Δ → (Γ,Δ) ⊢ a : TType τ →
  index_alive Δ (addr_index a) → addr_is_obj a → addr_strict Γ a →
  (Γ,Δ) ⊢ w : τ → ¬ctree_empty w → ✓{Γ,Δ} (cmap_singleton Γ a μ w).
Proof.
  intros ??????? Hperm; split_and !; intros; simplify_map_eq; auto.
  assert (τ = addr_type_base a) by eauto using addr_is_obj_type; subst.
  exists (addr_type_object a); split_and ?; eauto using addr_typed_index,
    ctree_singleton_typed, ctree_singleton_Forall_inv, addr_typed_ref_typed.
Qed.
Lemma cmap_singleton_weaken Γ1 Γ2 Δ a μ w τ :
  ✓ Γ1 → Γ1 ⊆ Γ2 → (Γ1,Δ) ⊢ a : TType τ → addr_strict Γ1 a →
  cmap_singleton Γ1 a μ w = cmap_singleton Γ2 a μ w.
Proof.
  unfold cmap_singleton; intros; f_equal'.
  by erewrite ctree_singleton_weaken, addr_ref_weaken
    by eauto using addr_typed_ref_typed, addr_typed_type_object_valid.
Qed.
Lemma cmap_lookup_singleton Γ Δ a μ w τ :
  ✓ Γ → (Γ,Δ) ⊢ a : TType τ → addr_is_obj a → addr_strict Γ a →
  (Γ,Δ) ⊢ w : τ → ¬ctree_unmapped w →
  cmap_singleton Γ a μ w !!{Γ} a = Some w.
Proof.
  intros. unfold lookupE, cmap_lookup.
  assert (τ = addr_type_base a) by eauto using addr_is_obj_type.
  rewrite option_guard_True by done; simplify_map_eq.
  erewrite ctree_lookup_singleton by eauto using addr_typed_ref_typed; simpl.
  by rewrite decide_True by done.
Qed.
Lemma cmap_alter_ref_singleton Γ Δ g a μ w τ :
  ✓ Γ → (Γ,Δ) ⊢ a : TType τ → addr_is_obj a → addr_strict Γ a →
  (Γ,Δ) ⊢ w : τ → ¬ctree_unmapped w → ¬ctree_unmapped (g w) →
  cmap_alter_ref Γ g (addr_index a) (addr_ref Γ a) (cmap_singleton Γ a μ w)
  = cmap_singleton Γ a μ (g w).
Proof.
  intros; unfold cmap_singleton; f_equal'; rewrite alter_singleton; simpl.
  assert (τ = addr_type_base a) by eauto using addr_is_obj_type; subst.
  by erewrite ctree_alter_singleton by eauto using addr_typed_ref_typed.
Qed.
Lemma cmap_alter_singleton Γ Δ g a μ w τ :
  ✓ Γ → (Γ,Δ) ⊢ a : TType τ → addr_is_obj a → addr_strict Γ a →
  (Γ,Δ) ⊢ w : τ → ¬ctree_unmapped w → ¬ctree_unmapped (g w) →
  cmap_alter Γ g a (cmap_singleton Γ a μ w) = cmap_singleton Γ a μ (g w).
Proof.
  intros; unfold cmap_alter.
  by erewrite decide_True, cmap_alter_ref_singleton by eauto.
Qed.
End memory_map.
