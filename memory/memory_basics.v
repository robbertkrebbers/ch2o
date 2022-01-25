(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
From stdpp Require Import nmap pmap natmap mapset fin_maps.
Require Export type_environment.

Set Warnings "-fragile-hint-constr".

(** * Indexes into the memory *)
(** We define indexes into the memory as binary naturals and use the [Nmap]
implementation to obtain efficient finite maps and finite sets with these
indexes as keys. *)
Definition index := N.
Definition indexmap := Nmap.
Notation indexset := (mapset indexmap).

#[global] Instance index_dec: EqDecision index := _.
#[global] Instance index_inhabited: Inhabited index := populate 0%N.
#[global] Instance indexmap_dec {A} `{EqDecision A} : EqDecision (indexmap A) := _.
#[global] Instance indexmap_empty {A} : Empty (indexmap A) := @empty (Nmap A) _.
#[global] Instance indexmap_lookup {A} : Lookup index A (indexmap A) :=
  @lookup _ _ (Nmap A) _.
#[global] Instance indexmap_partial_alter {A} : PartialAlter index A (indexmap A) :=
  @partial_alter _ _ (Nmap A) _.
#[global] Instance indexmap_to_list {A} : FinMapToList index A (indexmap A) :=
  @map_to_list _ _ (Nmap A) _.
#[global] Instance indexmap_omap: OMap indexmap := @omap Nmap _.
#[global] Instance indexmap_merge: Merge indexmap := @merge Nmap _.
#[global] Instance indexmap_fmap: FMap indexmap := @fmap Nmap _.
#[global] Instance: FinMap index indexmap := _.
#[global] Instance indexmap_dom {A} : Dom (indexmap A) indexset := mapset_dom.
#[global] Instance: FinMapDom index indexmap indexset := mapset_dom_spec.
#[global] Instance index_fresh : Fresh index indexset := _.
#[global] Instance index_infinity: Infinite index := _.
#[global] Instance index_lexico : Lexico index := @lexico N _.
#[global] Instance index_lexico_order : StrictOrder (@lexico index _) := _.
#[global] Instance index_trichotomy: TrichotomyT (@lexico index _) := _.
Typeclasses Opaque index indexmap.

Global Hint Immediate (is_fresh (A:=index) (C:=indexset)): core.
Global Hint Immediate (Forall_fresh_list (A:=index) (C:=indexset)): core.
Global Hint Immediate (fresh_list_length (A:=index) (C:=indexset)): core.

(** * Memory environments *)
Notation memenv K :=
  (indexmap (type K * bool (* false = alive, true = freed *))).
#[global] Instance index_typed {K} : Typed (memenv K) (type K) index := λ Δ o τ,
  ∃ β, Δ !! o = Some (τ,β).
Definition index_alive {K} (Δ : memenv K) (o : index) : Prop :=
  ∃ τ, Δ !! o = Some (τ,false).
#[global] Instance memenv_valid `{Env K} : Valid (env K) (memenv K) := λ Γ Δ,
  ∀ o τ, Δ ⊢ o : τ → ✓{Γ} τ.

#[global] Instance index_typecheck {K} : TypeCheck (memenv K) (type K) index := λ Δ o,
  fst <$> Δ !! o.
#[global] Instance: `{TypeCheckSpec (memenv K) (type K) index (λ _, True)}.
Proof.
  intros ? Δ o τ. split; unfold type_check, typed,index_typecheck, index_typed.
  * destruct (Δ !! o) as [[??]|]; naive_solver.
  * by intros [? ->].
Qed.
#[global] Instance index_alive_dec {K} (Δ : memenv K) o : Decision (index_alive Δ o).
 refine
  match Δ !! o as mβτ return Decision (∃ τ, mβτ = Some (τ,false)) with
  | Some (_,β) => match β with true => right _ | false => left _ end
  | None => right _
  end; abstract naive_solver.
Defined.
Lemma memenv_empty_valid `{Env K} Γ : ✓{Γ} (∅ : memenv K).
Proof. intros ?? [??]; simplify_map_eq. Qed.
Lemma memenv_valid_weaken `{EnvSpec K} Γ1 Γ2 (Δ : memenv K) :
  ✓ Γ1 → ✓{Γ1} Δ → Γ1 ⊆ Γ2 → ✓{Γ2} Δ.
Proof. intros ? HΔ ? o τ ?; eauto using type_valid_weaken. Qed.
Lemma index_typed_valid `{EnvSpec K} Γ (Δ : memenv K) o τ :
  ✓{Γ} Δ → Δ ⊢ o : τ → ✓{Γ} τ.
Proof. eauto. Qed.

(** During the execution of the semantics, the memory environments should only
grow, i.e. new objects may be allocated and current objects may be freed. We
prove that the step relation of the semantics is monotone with respect to the
forward relation below. *)
Record memenv_forward {K} (Δ1 Δ2  : memenv K) := {
  memenv_forward_typed o τ : Δ1 ⊢ o : τ → Δ2 ⊢ o : τ;
  memenv_forward_alive o τ : Δ1 ⊢ o : τ → index_alive Δ2 o → index_alive Δ1 o
}.
Notation "Δ1 ⇒ₘ Δ2" := (memenv_forward Δ1 Δ2)
  (at level 70, format "Δ1  ⇒ₘ  Δ2") : C_scope.
#[global] Instance: `{PartialOrder (@memenv_forward K)}.
Proof.
  split; [split; [|intros ??? [??] [??]]; split; naive_solver|].
  cut (∀ (Δ1 Δ2 : memenv K) o τ β,
    Δ1 ⇒ₘ Δ2 → Δ2 ⇒ₘ Δ1 → Δ1 !! o = Some (τ,β) → Δ2 !! o = Some (τ,β)).
  { intros ? Δ1 Δ2 ??; apply map_eq; intros o.
    apply option_eq; intros [τ β]; naive_solver. }
  intros Δ1 Δ2 o τ β [Htyped Halive1] [_ Halive2] ?.
  destruct (Htyped o τ) as [β' ?]; [by exists β|]; destruct β, β'; auto.
  * destruct (Halive1 o τ). by exists true. by exists τ. naive_solver.
  * destruct (Halive2 o τ). by exists true. by exists τ. naive_solver.
Qed.
Global Hint Extern 0 (?Δ1 ⇒ₘ ?Δ2) => reflexivity: core.
Global Hint Extern 1 (_ ⇒ₘ _) => etransitivity; [eassumption|]: core.
Global Hint Extern 1 (_ ⇒ₘ _) => etransitivity; [|eassumption]: core.
Lemma index_typed_weaken {K} (Δ1 Δ2 : memenv K) o τ :
  Δ1 ⊢ o : τ → Δ1 ⇒ₘ Δ2 → Δ2 ⊢ o : τ.
Proof. eauto using memenv_forward_typed. Qed.
Lemma indexes_typed_weaken {K} (Δ1 Δ2 : memenv K) os τs :
  Δ1 ⊢* os :* τs → Δ1 ⇒ₘ Δ2 → Δ2 ⊢* os :* τs.
Proof. eauto using Forall2_impl, memenv_forward_typed. Qed.
Lemma memenv_subseteq_forward {K} (Δ1 Δ2  : memenv K) :
  Δ1 ⊆ Δ2 → Δ1 ⇒ₘ Δ2.
Proof.
  split.
  * intros o τ [β ?]; exists β; eauto using lookup_weaken.
  * intros o τ [β ?] [τ' ?]; exists τ.
    assert (Δ2 !! o = Some (τ, β)) by eauto using lookup_weaken.
    naive_solver.
Qed.
Lemma memenv_subseteq_alive {K} (Δ1 Δ2  : memenv K) o :
  Δ1 ⊆ Δ2 → index_alive Δ1 o → index_alive Δ2 o.
Proof. intros ? [β ?]; exists β; eauto using lookup_weaken. Qed.

(** * Locked locations *)
Definition lockset : iType :=
  dsig (A:=indexmap natset) (map_Forall (λ _, (.≠ ∅))).
#[global] Instance lockset_eq_dec: EqDecision lockset | 1 := _.
Typeclasses Opaque lockset.

#[global] Instance lockset_elem_of : ElemOf (index * nat) lockset := λ oi Ω,
  ∃ ω, `Ω !! oi.1 = Some ω ∧ oi.2 ∈ ω.
#[global, program] Instance lockset_empty: Empty lockset := dexist ∅ _.
Next Obligation. by intros ??; simpl_map. Qed.
Global Program Instance lockset_singleton: Singleton (index * nat) lockset := λ oi,
  dexist {[ oi.1 := {[ oi.2 ]} ]} _.
Next Obligation.
  intros ???. rewrite lookup_singleton_Some; intros [<- <-];
  apply non_empty_singleton_L.
Qed.
Global Program Instance lockset_union: Union lockset := λ Ω1 Ω2,
  let (Ω1,HΩ1) := Ω1 in let (Ω2,HΩ2) := Ω2 in
  dexist (union_with (λ ω1 ω2, Some (ω1 ∪ ω2)) Ω1 Ω2) _.
Next Obligation.
  intros; apply bool_decide_unpack in HΩ1; apply bool_decide_unpack in HΩ2.
  intros n ω. rewrite lookup_union_with_Some.
  intros [[??]|[[??]|(ω1&ω2&?&?&?)]]; simplify_equality'; eauto.
  apply union_positive_l_alt_L; eauto.
Qed.
Global Program Instance lockset_intersection: Intersection lockset := λ Ω1 Ω2,
  let (Ω1,HΩ1) := Ω1 in let (Ω2,HΩ2) := Ω2 in
  dexist (intersection_with (λ ω1 ω2,
    let ω := ω1 ∩ ω2 in guard (ω ≠ ∅); Some ω) Ω1 Ω2) _.
Next Obligation.
  intros; apply bool_decide_unpack in HΩ1; apply bool_decide_unpack in HΩ2.
  intros n ω. rewrite lookup_intersection_with_Some.
  intros (ω1&ω2&?&?&?); simplify_option_eq; eauto.
Qed.
Global Program Instance lockset_difference: Difference lockset := λ Ω1 Ω2,
  let (Ω1,HΩ1) := Ω1 in let (Ω2,HΩ2) := Ω2 in
  dexist (difference_with (λ ω1 ω2,
    let ω := ω1 ∖ ω2 in guard (ω ≠ ∅); Some ω) Ω1 Ω2) _.
Next Obligation.
  intros; apply bool_decide_unpack in HΩ1; apply bool_decide_unpack in HΩ2.
  intros n ω. rewrite lookup_difference_with_Some.
  intros [[??]|(ω1&ω2&?&?&?)]; simplify_option_eq; eauto.
Qed.
#[global] Instance lockset_elems: Elements (index * nat) lockset := λ Ω,
  let (Ω,_) := Ω in
  map_to_list Ω ≫= λ oω, pair (oω.1) <$> elements (oω.2 : natset).

Lemma lockset_eq (Ω1 Ω2 : lockset) : Ω1 = Ω2 ↔ ∀ o i, (o,i) ∈ Ω1 ↔ (o,i) ∈ Ω2.
Proof.
  revert Ω1 Ω2. cut (∀ (Ω1 Ω2 : indexmap natset) ω o,
    (∀ o i, (∃ ω, Ω1 !! o = Some ω ∧ i ∈ ω) ↔ (∃ ω, Ω2 !! o = Some ω ∧ i ∈ ω)) →
    map_Forall (λ _, (.≠ ∅)) Ω1 → Ω1 !! o = Some ω → Ω2 !! o = Some ω).
  { intros help Ω1 Ω2; split; [by intros ->|]; destruct Ω1 as [Ω1 HΩ1],
       Ω2 as [Ω2 HΩ2]; unfold elem_of, lockset_elem_of; simpl; intros.
     apply dsig_eq; simpl; apply map_eq; intros o.
     apply bool_decide_unpack in HΩ1; apply bool_decide_unpack in HΩ2.
     by apply option_eq; split; apply help. }
  intros Ω1 Ω2 ω o Hoi ??. destruct (set_choose_L ω) as (i&?); eauto.
  destruct (proj1 (Hoi o i)) as (ω'&Ho'&_); eauto; rewrite Ho'.
  f_equal; apply set_eq; intros j; split; intros.
  * by destruct (proj2 (Hoi o j)) as (?&?&?); eauto; simplify_equality'.
  * by destruct (proj1 (Hoi o j)) as (?&?&?); eauto; simplify_equality'.
Qed.
#[global] Instance lockset_elem_of_dec oi (Ω : lockset) : Decision (oi ∈ Ω) | 1.
Proof.
 refine
  match `Ω !! oi.1 as mω return Decision (∃ ω, mω = Some ω ∧ oi.2 ∈ ω) with
  | Some ω => cast_if (decide (oi.2 ∈ ω)) | None => right _
  end; abstract naive_solver.
Defined.
#[global] Instance: FinSet (index * nat) lockset.
Proof.
  split; [split; [split| |]| | ].
  * intros [??] (?&?&?); simplify_map_eq.
  * unfold elem_of, lockset_elem_of, singleton, lockset_singleton.
    intros [o1 i1] [o2 i2]; simpl. setoid_rewrite lookup_singleton_Some. split.
    { by intros (?&[??]&Hi); simplify_equality'; set_solver. }
    intros; simplify_equality'. eexists {[i2]}; set_solver.
  * unfold elem_of, lockset_elem_of, union, lockset_union.
    intros [Ω1 HΩ1] [Ω2 HΩ2] [o i]; simpl.
    setoid_rewrite lookup_union_with_Some. split.
    { intros (?&[[]|[[]|(?&?&?&?&?)]]&?);
        simplify_equality'; set_solver; eauto. }
    intros [(ω1&?&?)|(ω2&?&?)].
    + destruct (Ω2 !! o) as [ω2|]; eauto.
      exists (ω1 ∪ ω2). rewrite elem_of_union. naive_solver.
    + destruct (Ω1 !! o) as [ω1|]; eauto 6.
      exists (ω1 ∪ ω2). rewrite elem_of_union. naive_solver.
  * unfold elem_of, lockset_elem_of, intersection, lockset_intersection.
    intros [m1 Hm1] [m2 Hm2] [o i]; simpl.
    setoid_rewrite lookup_intersection_with_Some. split.
    { intros (?&(l&k&?&?&?)&?);
        simplify_option_eq; set_solver; eauto 6. }
    intros [(ω1&?&?) (ω2&?&?)].
    assert (i ∈ ω1 ∩ ω2) by (by rewrite elem_of_intersection).
    exists (ω1 ∩ ω2); split; [exists ω1, ω2|]; split_and ?; auto.
    by rewrite option_guard_True by set_solver.
  * unfold elem_of, lockset_elem_of, intersection, lockset_intersection.
    intros [Ω1 HΩ1_wf] [Ω2 HΩ2_wf] [o i]; simpl.
    setoid_rewrite lookup_difference_with_Some. split.
    { intros (?&[[??]|(l&k&?&?&?)]&?);
        simplify_option_eq; set_solver; naive_solver. }
    intros [(ω1&?&?) HΩ2]; destruct (Ω2 !! o) as [ω2|] eqn:?; eauto.
    destruct (decide (i ∈ ω2)); [destruct HΩ2; eauto|].
    assert (i ∈ ω1 ∖ ω2) by (by rewrite elem_of_difference).
    exists (ω1 ∖ ω2); split; [right; exists ω1, ω2|]; split_and ?; auto.
    by rewrite option_guard_True by set_solver.
  * unfold elem_of at 2, lockset_elem_of, elements, lockset_elems.
    intros [Ω HΩ_wf] [o i]; simpl. setoid_rewrite elem_of_list_bind. split.
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
    apply NoDup_app; split_and ?; eauto.
    { eapply (NoDup_fmap_2 _), NoDup_elements. }
    setoid_rewrite elem_of_list_bind; setoid_rewrite elem_of_list_fmap.
    intros [o' i] (?&?&?) ([o'' ω'']&(?&?&?)&?); simplify_equality'.
    destruct Ho; rewrite elem_of_list_fmap. exists (o, ω''); eauto.
Qed.
#[global] Instance: PartialOrder (@subseteq lockset _).
Proof. split; try apply _. intros ????. apply lockset_eq. intuition. Qed.
#[global] Instance: SemiSet (index * nat) lockset := _.
#[global] Instance: Set_ (index * nat) lockset := _.
#[global] Instance: @RelDecision (prod index nat) lockset 
  (@elem_of (prod index nat) lockset lockset_elem_of) := lockset_elem_of_dec.
#[global] Instance: @LeibnizEquiv lockset (@set_equiv_instance _ _ lockset_elem_of).
Proof. intros ???; by rewrite lockset_eq. Qed.

#[global] Instance lockset_valid `{Env K} : Valid (env K * memenv K) lockset := λ ΓΔ Ω,
  ∀ o i, (o,i) ∈ Ω → ∃ τ, ΓΔ.2 ⊢ o : τ ∧ ✓{ΓΔ.1} τ ∧ i < bit_size_of (ΓΔ.1) τ.
Local Obligation Tactic := idtac.
Global Program Instance lockset_valid_dec
    `{Env K} Γ Δ (Ω : lockset) : Decision (✓{Γ,Δ} Ω) :=
  cast_if (decide (map_relation (λ τβ ω,
    ✓{Γ} (τβ.1) ∧ length (natmap_car (mapset_car ω)) ≤ bit_size_of Γ (τβ.1)
  ) (λ _, True) (λ _, False) Δ (`Ω))).
Next Obligation.
  intros K ? Γ Δ Ω HΩ o i (ω&?&Hi); specialize (HΩ o); unfold option_relation in HΩ; simplify_option_eq.
  destruct (Δ !! o) as [[τ β]|] eqn:?; intuition; simplify_equality'.
  exists τ; split_and ?; [by exists β|auto|eapply Nat.lt_le_trans; [|eauto]].
  unfold elem_of, mapset_elem_of, lookup, natmap_lookup in Hi.
  destruct ω as [[ω ?]]; simplify_equality'.
  destruct (ω !! i) eqn:?; simplify_equality'; eauto using lookup_lt_Some.
Qed.
Next Obligation.
  intros K ? Γ Δ Ω HΩ; contradict HΩ.
  intros o. unfold option_relation. destruct (`Ω !! o) as [ω|] eqn:Ho; [|by destruct (Δ !! _)].
  set (i:=length (natmap_car (mapset_car ω)) - 1); assert (i ∈ ω).
  { unfold i; clear i; destruct ω as [[ω Hω]]; simplify_equality'.
    unfold elem_of, mapset_elem_of, lookup, natmap_lookup; simpl.
    destruct ω as [|u ω _] using rev_ind.
    { destruct ((bool_decide_unpack _ (proj2_sig Ω) o _) Ho).
      by apply (bool_decide_unpack _). }
    clear Ho; unfold natmap_wf in Hω.
    rewrite last_snoc in Hω; destruct Hω as [[] ->]; simpl.
    by rewrite app_length; simpl; rewrite <-Nat.add_sub_assoc, Nat.sub_diag,
      Nat.add_0_r, lookup_app_r, Nat.sub_diag by done. }
  destruct (HΩ o i) as (τ&[β]&?&?); [by exists ω|]; simplify_option_eq.
  unfold i in *; split_and ?; auto with lia.
Qed.
Lemma lockset_valid_weaken `{EnvSpec K} Γ1 Γ2 Δ1 Δ2 (Ω : lockset) :
  ✓ Γ1 → ✓{Γ1,Δ1} Ω → Γ1 ⊆ Γ2 → Δ1 ⇒ₘ Δ2 → ✓{Γ2,Δ2} Ω.
Proof.
  intros ? HΩ ? [??] o i ?; destruct (HΩ o i) as (τ&?&?&?); eauto.
  exists τ. erewrite <-(bit_size_of_weaken Γ1 Γ2) by eauto.
  eauto using type_valid_weaken.
Qed.
Lemma lockset_empty_valid `{Env K} Γ Δ : ✓{Γ,Δ} (∅ : lockset).
Proof. intros o i; set_solver. Qed.
Lemma lockset_union_valid `{Env K} Γ Δ (Ω1 Ω2 : lockset) :
  ✓{Γ,Δ} Ω1 → ✓{Γ,Δ} Ω2 → ✓{Γ,Δ} (Ω1 ∪ Ω2).
Proof. intros HΩ1 HΩ2 o r; rewrite elem_of_union; naive_solver. Qed.
