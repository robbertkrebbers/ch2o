(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export fin_map_dom types.
Require Import nmap natmap mapset.

(** * Indexes into the memory *)
(** We define indexes into the memory as binary naturals and use the [Nmap]
implementation to obtain efficient finite maps and finite sets with these
indexes as keys. *)
Definition index := N.
Definition indexmap := Nmap.
Notation indexset := (mapset (indexmap unit)).

Instance index_dec: ∀ o1 o2 : index, Decision (o1 = o2) := decide_rel (=).
Instance index_fresh_`{FinCollection index C} : Fresh index C := _.
Instance index_fresh_spec `{FinCollection index C} : FreshSpec index C := _.
Instance index_inhabited: Inhabited index := populate 0%N.
Instance indexmap_dec {A} `{∀ a1 a2 : A, Decision (a1 = a2)} :
  ∀ m1 m2 : indexmap A, Decision (m1 = m2) := decide_rel (=).
Instance indexmap_empty {A} : Empty (indexmap A) := @empty (Nmap A) _.
Instance indexmap_lookup {A} : Lookup index A (indexmap A) :=
  @lookup _ _ (Nmap A) _.
Instance indexmap_partial_alter {A} : PartialAlter index A (indexmap A) :=
  @partial_alter _ _ (Nmap A) _.
Instance indexmap_to_list {A} : FinMapToList index A (indexmap A) :=
  @map_to_list _ _ (Nmap A) _.
Instance indexmap_omap: OMap indexmap := @omap Nmap _.
Instance indexmap_merge: Merge indexmap := @merge Nmap _.
Instance indexmap_fmap: FMap indexmap := @fmap Nmap _.
Instance: FinMap index indexmap := _.
Instance indexmap_dom {A} : Dom (indexmap A) indexset := mapset_dom.
Instance: FinMapDom index indexmap indexset := mapset_dom_spec.
Instance index_lexico : Lexico index := @lexico N _.
Instance index_lexico_order : StrictOrder (@lexico index _) := _.
Instance index_trichotomy: TrichotomyT (@lexico index _) := _.
Typeclasses Opaque index indexmap.

(** * Memory environments *)
Notation memenv Ti :=
  (indexmap (type Ti * bool (* false = alive, true = freed *))).
Instance index_typed {Ti} : Typed (memenv Ti) (type Ti) index := λ Γm o τ,
  ∃ β, Γm !! o = Some (τ,β).
Instance index_typecheck {Ti} : TypeCheck (memenv Ti) (type Ti) index := λ Γm o,
  fst <$> Γm !! o.
Definition index_alive {Ti} (Γm : memenv Ti) (o : index) : Prop :=
  ∃ τ, Γm !! o = Some (τ,false).
Instance: TypeCheckSpec (memenv Ti) (type Ti) index (λ _, True).
Proof.
  intros ? Γm o τ. split; unfold type_check, typed,index_typecheck, index_typed.
  * destruct (Γm !! o) as [[??]|]; naive_solver.
  * by intros [? ->].
Qed.
Instance index_alive_dec {Ti} (Γm : memenv Ti) o : Decision (index_alive Γm o).
 refine
  match Γm !! o as mβτ return Decision (∃ τ, mβτ = Some (τ,false)) with
  | Some (_,β) => match β with true => right _ | false => left _ end
  | None => right _
  end; abstract naive_solver.
Defined.

(** During the execution of the semantics, the memory environments should only
grow, i.e. new objects may be allocated and current objects may be freed. We
prove that the step relation of the semantics is monotone with respect to the
forward relation below. *)
Record memenv_forward {Ti} (Γm1 Γm2  : memenv Ti) := {
  memenv_forward_typed o τ : Γm1 ⊢ o : τ → Γm2 ⊢ o : τ;
  memenv_forward_alive o τ : Γm1 ⊢ o : τ → index_alive Γm2 o → index_alive Γm1 o
}.
Notation "Γm1 ⇒ₘ Γm2" := (memenv_forward Γm1 Γm2)
  (at level 70, format "Γm1  ⇒ₘ  Γm2") : C_scope.
Instance: PreOrder (@memenv_forward Ti).
Proof. split; [|intros ??? [??] [??]]; split; naive_solver. Qed.
Hint Extern 0 (?Γm1 ⇒ₘ ?Γm2) => reflexivity.

(** * Locked locations *)
Definition lockset : Set :=
  dsigS (map_Forall (λ _, (≠ ∅)) : indexmap natset → Prop).
Instance lockset_eq_dec (Ω1 Ω2 : lockset) : Decision (Ω1 = Ω2) | 1 := _.
Typeclasses Opaque lockset.

Instance lockset_elem_of : ElemOf (index * nat) lockset := λ oi Ω,
  ∃ ω, `Ω !! oi.1 = Some ω ∧ oi.2 ∈ ω.
Program Instance lockset_empty: Empty lockset := dexist ∅ _.
Next Obligation. by intros ??; simpl_map. Qed.
Program Instance lockset_singleton: Singleton (index * nat) lockset := λ oi,
  dexist {[oi.1, {[oi.2]} ]} _.
Next Obligation.
  intros o ω; rewrite lookup_singleton_Some; intros [<- <-].
  apply non_empty_singleton_L.
Qed.
Program Instance lockset_union: Union lockset := λ Ω1 Ω2,
  let (Ω1,HΩ1) := Ω1 in let (Ω2,HΩ2) := Ω2 in
  dexist (union_with (λ ω1 ω2, Some (ω1 ∪ ω2)) Ω1 Ω2) _.
Next Obligation.
  apply bool_decide_unpack in HΩ1; apply bool_decide_unpack in HΩ2.
  intros n ω. rewrite lookup_union_with_Some.
  intros [[??]|[[??]|(ω1&ω2&?&?&?)]]; simplify_equality'; eauto.
  apply collection_positive_l_alt_L; eauto.
Qed.
Program Instance lockset_intersection: Intersection lockset := λ Ω1 Ω2,
  let (Ω1,HΩ1) := Ω1 in let (Ω2,HΩ2) := Ω2 in
  dexist (intersection_with (λ ω1 ω2,
    let ω := ω1 ∩ ω2 in guard (ω ≠ ∅); Some ω) Ω1 Ω2) _.
Next Obligation.
  apply bool_decide_unpack in HΩ1; apply bool_decide_unpack in HΩ2.
  intros n ω. rewrite lookup_intersection_with_Some.
  intros (ω1&ω2&?&?&?); simplify_option_equality; eauto.
Qed.
Program Instance lockset_difference: Difference lockset := λ Ω1 Ω2,
  let (Ω1,HΩ1) := Ω1 in let (Ω2,HΩ2) := Ω2 in
  dexist (difference_with (λ ω1 ω2,
    let ω := ω1 ∖ ω2 in guard (ω ≠ ∅); Some ω) Ω1 Ω2) _.
Next Obligation.
  apply bool_decide_unpack in HΩ1; apply bool_decide_unpack in HΩ2.
  intros n ω. rewrite lookup_difference_with_Some.
  intros [[??]|(ω1&ω2&?&?&?)]; simplify_option_equality; eauto.
Qed.
Instance lockset_elems: Elements (index * nat) lockset := λ Ω,
  let (Ω,_) := Ω in
  map_to_list Ω ≫= λ oω, pair (oω.1) <$> elements (oω.2 : natset).

Lemma lockset_eq (Ω1 Ω2 : lockset) : Ω1 = Ω2 ↔ ∀ o i, (o,i) ∈ Ω1 ↔ (o,i) ∈ Ω2.
Proof.
  revert Ω1 Ω2. cut (∀ (Ω1 Ω2 : indexmap natset) ω o,
    (∀ o i, (∃ ω, Ω1 !! o = Some ω ∧ i ∈ ω) ↔ (∃ ω, Ω2 !! o = Some ω ∧ i ∈ ω)) →
    map_Forall (λ _, (≠ ∅)) Ω1 → Ω1 !! o = Some ω → Ω2 !! o = Some ω).
  { intros help Ω1 Ω2; split; [by intros ->|]; destruct Ω1 as [Ω1 HΩ1],
       Ω2 as [Ω2 HΩ2]; unfold elem_of, lockset_elem_of; simpl; intros.
     apply dsig_eq; simpl; apply map_eq; intros o.
     apply bool_decide_unpack in HΩ1; apply bool_decide_unpack in HΩ2.
     by apply option_eq; split; apply help. }
  intros Ω1 Ω2 ω o Hoi ??. destruct (collection_choose_L ω) as (i&?); eauto.
  destruct (proj1 (Hoi o i)) as (ω'&Ho'&_); eauto; rewrite Ho'.
  f_equal; apply elem_of_equiv_L; intros j; split; intros.
  * by destruct (proj2 (Hoi o j)) as (?&?&?); eauto; simplify_equality'.
  * by destruct (proj1 (Hoi o j)) as (?&?&?); eauto; simplify_equality'.
Qed.
Instance lockset_elem_of_dec oi (Ω : lockset) : Decision (oi ∈ Ω) | 1.
Proof.
 refine
  match `Ω !! oi.1 as mω return Decision (∃ ω, mω = Some ω ∧ oi.2 ∈ ω) with
  | Some ω => cast_if (decide (oi.2 ∈ ω)) | None => right _
  end; abstract naive_solver.
Defined.
Instance: FinCollection (index * nat) lockset.
Proof.
  split; [split; [split| |]| | ].
  * intros [??] (?&?&?); simplify_map_equality'.
  * unfold elem_of, lockset_elem_of, singleton, lockset_singleton.
    intros [o1 i1] [o2 i2]; simpl. setoid_rewrite lookup_singleton_Some. split.
    { by intros (?&[??]&Hi); simplify_equality'; decompose_elem_of. }
    intros; simplify_equality'. eexists {[i2]}; esolve_elem_of.
  * unfold elem_of, lockset_elem_of, union, lockset_union.
    intros [Ω1 ?] [Ω2 ?] [o i]; simpl.
    setoid_rewrite lookup_union_with_Some. split.
    { intros (?&[[]|[[]|(?&?&?&?&?)]]&?);
        simplify_equality'; decompose_elem_of; eauto. }
    intros [(ω1&?&?)|(ω2&?&?)].
    + destruct (Ω2 !! o) as [ω2|]; eauto.
      exists (ω1 ∪ ω2). rewrite elem_of_union. naive_solver.
    + destruct (Ω1 !! o) as [ω1|]; eauto 6.
      exists (ω1 ∪ ω2). rewrite elem_of_union. naive_solver.
  * unfold elem_of, lockset_elem_of, intersection, lockset_intersection.
    intros [m1 ?] [m2 ?] [o i]; simpl.
    setoid_rewrite lookup_intersection_with_Some. split.
    { intros (?&(l&k&?&?&?)&?);
        simplify_option_equality; decompose_elem_of; eauto 6. }
    intros [(ω1&?&?) (ω2&?&?)].
    assert (i ∈ ω1 ∩ ω2) by (by rewrite elem_of_intersection).
    exists (ω1 ∩ ω2); split; [exists ω1 ω2|]; split_ands; auto.
    by rewrite option_guard_True by esolve_elem_of.
  * unfold elem_of, lockset_elem_of, intersection, lockset_intersection.
    intros [Ω1 ?] [Ω2 ?] [o i]; simpl.
    setoid_rewrite lookup_difference_with_Some. split.
    { intros (?&[[??]|(l&k&?&?&?)]&?);
        simplify_option_equality; decompose_elem_of; naive_solver. }
    intros [(ω1&?&?) HΩ2]; destruct (Ω2 !! o) as [ω2|] eqn:?; eauto.
    destruct (decide (i ∈ ω2)); [destruct HΩ2; eauto|].
    assert (i ∈ ω1 ∖ ω2) by (by rewrite elem_of_difference).
    exists (ω1 ∖ ω2); split; [right; exists ω1 ω2|]; split_ands; auto.
    by rewrite option_guard_True by esolve_elem_of.
  * unfold elem_of at 2, lockset_elem_of, elements, lockset_elems.
    intros [Ω ?] [o i]; simpl. setoid_rewrite elem_of_list_bind. split.
    { intros ([o' ω]&Hoi&Ho'); simpl in *; rewrite elem_of_map_to_list in Ho'.
      setoid_rewrite elem_of_list_fmap in Hoi;
        setoid_rewrite elem_of_elements in Hoi;
        destruct Hoi as (?&?&?); simplify_equality'; eauto. }
    intros (ω&?&?). exists (o, ω); simpl.
    rewrite elem_of_map_to_list, elem_of_list_fmap;
      setoid_rewrite elem_of_elements; eauto.
  * unfold elements, lockset_elems. intros [Ω HΩ]; simpl.
    apply bool_decide_unpack in HΩ. rewrite map_Forall_to_list in HΩ.
    generalize (NoDup_fst_map_to_list Ω).
    induction HΩ as [|[o ω] Ω'];
      csimpl; inversion_clear 1 as [|?? Ho]; [constructor|].
    apply NoDup_app; split_ands; eauto.
    { eapply (NoDup_fmap_2 _), NoDup_elements. }
    setoid_rewrite elem_of_list_bind; setoid_rewrite elem_of_list_fmap.
    intros [o' i] (?&?&?) ([o'' ω'']&(?&?&?)&?); simplify_equality'.
    destruct Ho; rewrite elem_of_list_fmap. exists (o, ω''); eauto.
Qed.
Instance: PartialOrder (@subseteq lockset _).
Proof. split; try apply _. intros ????. apply lockset_eq. intuition. Qed.

Instance lockset_valid {Ti} : Valid (memenv Ti) lockset := λ Γm Ω,
  ∀ o r, (o,r) ∈ Ω → ∃ τ, Γm ⊢ o : τ.
Lemma lockset_valid_alt {Ti} (Γm : memenv Ti) (Ω : lockset) :
  ✓{Γm} Ω ↔ dom indexset (`Ω) ⊆ dom indexset Γm.
Proof.
  rewrite elem_of_subseteq; setoid_rewrite elem_of_dom; split.
  * intros HΩ o [ω ?].
    destruct (collection_choose_L ω) as [i ?]; [by apply (proj2_dsig Ω o ω)|].
    destruct (HΩ o i) as (τ&β&?); [by exists ω|by exists (τ,β)].
  * intros HΩ o r (ω&?&_). destruct (HΩ o) as [[τ β] ?]; eauto. by exists τ β.
Qed.
Instance lockset_valid_dec {Ti} (Γm : memenv Ti) Ω : Decision (✓{Γm} Ω).
Proof.
 refine (cast_if (decide (dom indexset (`Ω) ⊆ dom _ Γm)));
  by rewrite lockset_valid_alt.
Defined.
Lemma lockset_valid_weaken {Ti} (Γm1 Γm2 : memenv Ti) Ω :
  ✓{Γm1} Ω → Γm1 ⇒ₘ Γm2 → ✓{Γm2} Ω.
Proof. intros HΩ [??] o r ?; destruct (HΩ o r); eauto. Qed.
Lemma lockset_empty_valid {Ti} (Γm : memenv Ti) : ✓{Γm} ∅.
Proof. intros o r; solve_elem_of. Qed.
Lemma lockset_union_valid {Ti} (Γm : memenv Ti) Ω1 Ω2 :
  ✓{Γm} Ω1 → ✓{Γm} Ω2 → ✓{Γm} (Ω1 ∪ Ω2).
Proof. intros HΩ1 HΩ2 o r; rewrite elem_of_union; naive_solver. Qed.
