(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects definitions and theorems on collections. Most
importantly, it implements some tactics to automatically solve goals involving
collections. *)
Require Export base tactics orders.

Instance collection_subseteq `{ElemOf A C} : SubsetEq C := λ X Y,
  ∀ x, x ∈ X → x ∈ Y.

(** * Basic theorems *)
Section simple_collection.
  Context `{SimpleCollection A C}.

  Lemma elem_of_empty x : x ∈ ∅ ↔ False.
  Proof. split. apply not_elem_of_empty. done. Qed.
  Lemma elem_of_union_l x X Y : x ∈ X → x ∈ X ∪ Y.
  Proof. intros. apply elem_of_union. auto. Qed.
  Lemma elem_of_union_r x X Y : x ∈ Y → x ∈ X ∪ Y.
  Proof. intros. apply elem_of_union. auto. Qed.
  Global Instance: BoundedJoinSemiLattice C.
  Proof. firstorder auto. Qed.
  Lemma elem_of_subseteq X Y : X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y.
  Proof. done. Qed.
  Lemma elem_of_equiv X Y : X ≡ Y ↔ ∀ x, x ∈ X ↔ x ∈ Y.
  Proof. firstorder. Qed.
  Lemma elem_of_equiv_alt X Y :
    X ≡ Y ↔ (∀ x, x ∈ X → x ∈ Y) ∧ (∀ x, x ∈ Y → x ∈ X).
  Proof. firstorder. Qed.
  Lemma elem_of_equiv_empty X : X ≡ ∅ ↔ ∀ x, x ∉ X.
  Proof. firstorder. Qed.
  Lemma collection_positive_l X Y : X ∪ Y ≡ ∅ → X ≡ ∅.
  Proof.
    rewrite !elem_of_equiv_empty. setoid_rewrite elem_of_union. naive_solver.
  Qed.
  Lemma collection_positive_l_alt X Y : X ≢ ∅ → X ∪ Y ≢ ∅.
  Proof. eauto using collection_positive_l. Qed.
  Lemma elem_of_subseteq_singleton x X : x ∈ X ↔ {[ x ]} ⊆ X.
  Proof.
    split.
    * intros ??. rewrite elem_of_singleton. by intros ->.
    * intros Ex. by apply (Ex x), elem_of_singleton.
  Qed.
  Global Instance singleton_proper : Proper ((=) ==> (≡)) singleton.
  Proof. by repeat intro; subst. Qed.
  Global Instance elem_of_proper: Proper ((=) ==> (≡) ==> iff) (∈) | 5.
  Proof. intros ???; subst. firstorder. Qed.
  Lemma elem_of_union_list Xs x : x ∈ ⋃ Xs ↔ ∃ X, X ∈ Xs ∧ x ∈ X.
  Proof.
    split.
    * induction Xs; simpl; intros HXs; [by apply elem_of_empty in HXs|].
      setoid_rewrite elem_of_cons. apply elem_of_union in HXs. naive_solver.
    * intros [X []]. induction 1; simpl; [by apply elem_of_union_l |].
      intros. apply elem_of_union_r; auto.
  Qed.
  Lemma non_empty_singleton x : {[ x ]} ≢ ∅.
  Proof. intros [E _]. by apply (elem_of_empty x), E, elem_of_singleton. Qed.
  Lemma not_elem_of_singleton x y : x ∉ {[ y ]} ↔ x ≠ y.
  Proof. by rewrite elem_of_singleton. Qed.
  Lemma not_elem_of_union x X Y : x ∉ X ∪ Y ↔ x ∉ X ∧ x ∉ Y.
  Proof. rewrite elem_of_union. tauto. Qed.

  Section leibniz.
    Context `{!LeibnizEquiv C}.
    Lemma elem_of_equiv_L X Y : X = Y ↔ ∀ x, x ∈ X ↔ x ∈ Y.
    Proof. unfold_leibniz. apply elem_of_equiv. Qed.
    Lemma elem_of_equiv_alt_L X Y :
      X = Y ↔ (∀ x, x ∈ X → x ∈ Y) ∧ (∀ x, x ∈ Y → x ∈ X).
    Proof. unfold_leibniz. apply elem_of_equiv_alt. Qed.
    Lemma elem_of_equiv_empty_L X : X = ∅ ↔ ∀ x, x ∉ X.
    Proof. unfold_leibniz. apply elem_of_equiv_empty. Qed.
    Lemma collection_positive_l_L X Y : X ∪ Y = ∅ → X = ∅.
    Proof. unfold_leibniz. apply collection_positive_l. Qed.
    Lemma collection_positive_l_alt_L X Y : X ≠ ∅ → X ∪ Y ≠ ∅.
    Proof. unfold_leibniz. apply collection_positive_l_alt. Qed.
    Lemma non_empty_singleton_L x : {[ x ]} ≠ ∅.
    Proof. unfold_leibniz. apply non_empty_singleton. Qed.
  End leibniz.

  Section dec.
    Context `{∀ X Y : C, Decision (X ⊆ Y)}.
    Global Instance elem_of_dec_slow (x : A) (X : C) : Decision (x ∈ X) | 100.
    Proof.
      refine (cast_if (decide_rel (⊆) {[ x ]} X));
        by rewrite elem_of_subseteq_singleton.
    Defined.
  End dec.
End simple_collection.

Definition of_option `{Singleton A C} `{Empty C} (x : option A) : C :=
  match x with None => ∅ | Some a => {[ a ]} end.
Lemma elem_of_of_option `{SimpleCollection A C} (x : A) o :
  x ∈ of_option o ↔ o = Some x.
Proof.
  destruct o; simpl; rewrite ?elem_of_empty, ?elem_of_singleton; naive_solver.
Qed.

Global Instance collection_guard `{CollectionMonad M} : MGuard M :=
  λ P dec A x, match dec with left H => x H | _ => ∅ end.
Lemma elem_of_guard `{CollectionMonad M} `{Decision P} {A} (x : A) (X : M A) :
  x ∈ guard P; X ↔ P ∧ x ∈ X.
Proof.
  unfold mguard, collection_guard; simpl; case_match;
    rewrite ?elem_of_empty; naive_solver.
Qed.

(** * Tactics *)
(** Given a hypothesis [H : _ ∈ _], the tactic [destruct_elem_of H] will
recursively split [H] for [(∪)], [(∩)], [(∖)], [map], [∅], [{[_]}]. *)
Tactic Notation "decompose_elem_of" hyp(H) :=
  let rec go H :=
  lazymatch type of H with
  | _ ∈ ∅ => apply elem_of_empty in H; destruct H
  | ?x ∈ {[ ?y ]} =>
    apply elem_of_singleton in H; try first [subst y | subst x]
  | _ ∈ _ ∪ _ =>
    let H1 := fresh in let H2 := fresh in apply elem_of_union in H;
    destruct H as [H1|H2]; [go H1 | go H2]
  | _ ∈ _ ∩ _ =>
    let H1 := fresh in let H2 := fresh in apply elem_of_intersection in H;
    destruct H as [H1 H2]; go H1; go H2
  | _ ∈ _ ∖ _ =>
    let H1 := fresh in let H2 := fresh in apply elem_of_difference in H;
    destruct H as [H1 H2]; go H1; go H2
  | ?x ∈ _ <$> _ =>
    let H1 := fresh in apply elem_of_fmap in H;
    destruct H as [? [? H1]]; try (subst x); go H1
  | _ ∈ _ ≫= _ =>
    let H1 := fresh in let H2 := fresh in apply elem_of_bind in H;
    destruct H as [? [H1 H2]]; go H1; go H2
  | ?x ∈ mret ?y =>
    apply elem_of_ret in H; try first [subst y | subst x]
  | _ ∈ mjoin _ ≫= _ =>
    let H1 := fresh in let H2 := fresh in apply elem_of_join in H;
    destruct H as [? [H1 H2]]; go H1; go H2
  | _ ∈ guard _; _ =>
    let H1 := fresh in let H2 := fresh in apply elem_of_guard in H;
    destruct H as [H1 H2]; go H2
  | _ ∈ of_option _ => apply elem_of_of_option in H
  | _ => idtac
  end in go H.
Tactic Notation "decompose_elem_of" :=
  repeat_on_hyps (fun H => decompose_elem_of H).

Ltac decompose_empty := repeat
  match goal with
  | H : ∅ ≡ ∅ |- _ => clear H
  | H : ∅ = ∅ |- _ => clear H
  | H : ∅ ≡ _ |- _ => symmetry in H
  | H : ∅ = _ |- _ => symmetry in H
  | H : _ ∪ _ ≡ ∅ |- _ => apply empty_union in H; destruct H
  | H : _ ∪ _ ≢ ∅ |- _ => apply non_empty_union in H; destruct H
  | H : {[ _ ]} ≡ ∅ |- _ => destruct (non_empty_singleton _ H)
  | H : _ ∪ _ = ∅ |- _ => apply empty_union_L in H; destruct H
  | H : _ ∪ _ ≠ ∅ |- _ => apply non_empty_union_L in H; destruct H
  | H : {[ _ ]} = ∅ |- _ => destruct (non_empty_singleton_L _ H)
  end.

(** The first pass of our collection tactic consists of eliminating all
occurrences of [(∪)], [(∩)], [(∖)], [(<$>)], [∅], [{[_]}], [(≡)], and [(⊆)],
by rewriting these into logically equivalent propositions. For example we
rewrite [A → x ∈ X ∪ ∅] into [A → x ∈ X ∨ False]. *)
Ltac unfold_elem_of :=
  repeat_on_hyps (fun H =>
    repeat match type of H with
    | context [ _ ⊆ _ ] => setoid_rewrite elem_of_subseteq in H
    | context [ _ ⊂ _ ] => setoid_rewrite subset_spec in H
    | context [ _ ≡ ∅ ] => setoid_rewrite elem_of_equiv_empty in H
    | context [ _ ≡ _ ] => setoid_rewrite elem_of_equiv_alt in H
    | context [ _ = ∅ ] => setoid_rewrite elem_of_equiv_empty_L in H
    | context [ _ = _ ] => setoid_rewrite elem_of_equiv_alt_L in H
    | context [ _ ∈ ∅ ] => setoid_rewrite elem_of_empty in H
    | context [ _ ∈ {[ _ ]} ] => setoid_rewrite elem_of_singleton in H
    | context [ _ ∈ _ ∪ _ ] => setoid_rewrite elem_of_union in H
    | context [ _ ∈ _ ∩ _ ] => setoid_rewrite elem_of_intersection in H
    | context [ _ ∈ _ ∖ _ ] => setoid_rewrite elem_of_difference in H
    | context [ _ ∈ _ <$> _ ] => setoid_rewrite elem_of_fmap in H
    | context [ _ ∈ mret _ ] => setoid_rewrite elem_of_ret in H
    | context [ _ ∈ _ ≫= _ ] => setoid_rewrite elem_of_bind in H
    | context [ _ ∈ mjoin _ ] => setoid_rewrite elem_of_join in H
    end);
  repeat match goal with
  | |- context [ _ ⊆ _ ] => setoid_rewrite elem_of_subseteq
  | |- context [ _ ⊂ _ ] => setoid_rewrite subset_spec
  | |- context [ _ ≡ ∅ ] => setoid_rewrite elem_of_equiv_empty
  | |- context [ _ ≡ _ ] => setoid_rewrite elem_of_equiv_alt
  | |- context [ _ = ∅ ] => setoid_rewrite elem_of_equiv_empty_L
  | |- context [ _ = _ ] => setoid_rewrite elem_of_equiv_alt_L
  | |- context [ _ ∈ ∅ ] => setoid_rewrite elem_of_empty
  | |- context [ _ ∈ {[ _ ]} ] => setoid_rewrite elem_of_singleton
  | |- context [ _ ∈ _ ∪ _ ] => setoid_rewrite elem_of_union
  | |- context [ _ ∈ _ ∩ _ ] => setoid_rewrite elem_of_intersection
  | |- context [ _ ∈ _ ∖ _ ] => setoid_rewrite elem_of_difference
  | |- context [ _ ∈ _ <$> _ ] => setoid_rewrite elem_of_fmap
  | |- context [ _ ∈ mret _ ] => setoid_rewrite elem_of_ret
  | |- context [ _ ∈ _ ≫= _ ] => setoid_rewrite elem_of_bind
  | |- context [ _ ∈ mjoin _ ] => setoid_rewrite elem_of_join
  end.

(** The tactic [solve_elem_of tac] composes the above tactic with [intuition].
For goals that do not involve [≡], [⊆], [map], or quantifiers this tactic is
generally powerful enough. This tactic either fails or proves the goal. *)
Tactic Notation "solve_elem_of" tactic3(tac) :=
  simpl in *;
  decompose_empty;
  unfold_elem_of;
  solve [intuition (simplify_equality; tac)].
Tactic Notation "solve_elem_of" := solve_elem_of auto.

(** For goals with quantifiers we could use the above tactic but with
[firstorder] instead of [intuition] as finishing tactic. However, [firstorder]
fails or loops on very small goals generated by [solve_elem_of] already. We
use the [naive_solver] tactic as a substitute. This tactic either fails or
proves the goal. *)
Tactic Notation "esolve_elem_of" tactic3(tac) :=
  simpl in *;
  decompose_empty;
  unfold_elem_of;
  naive_solver tac.
Tactic Notation "esolve_elem_of" := esolve_elem_of eauto.
 
(** * More theorems *)
Section collection.
  Context `{Collection A C}.

  Global Instance: LowerBoundedLattice C.
  Proof. split. apply _. firstorder auto. solve_elem_of. Qed.

  Lemma intersection_singletons x : {[x]} ∩ {[x]} ≡ {[x]}.
  Proof. esolve_elem_of. Qed.
  Lemma difference_twice X Y : (X ∖ Y) ∖ Y ≡ X ∖ Y.
  Proof. esolve_elem_of. Qed.
  Lemma empty_difference X Y : X ⊆ Y → X ∖ Y ≡ ∅.
  Proof. esolve_elem_of. Qed.
  Lemma difference_diag X : X ∖ X ≡ ∅.
  Proof. esolve_elem_of. Qed.
  Lemma difference_union_distr_l X Y Z : (X ∪ Y) ∖ Z ≡ X ∖ Z ∪ Y ∖ Z.
  Proof. esolve_elem_of. Qed.
  Lemma difference_intersection_distr_l X Y Z : (X ∩ Y) ∖ Z ≡ X ∖ Z ∩ Y ∖ Z.
  Proof. esolve_elem_of. Qed.

  Section leibniz.
    Context `{!LeibnizEquiv C}.
    Lemma intersection_singletons_L x : {[x]} ∩ {[x]} = {[x]}.
    Proof. unfold_leibniz. apply intersection_singletons. Qed.
    Lemma difference_twice_L X Y : (X ∖ Y) ∖ Y = X ∖ Y.
    Proof. unfold_leibniz. apply difference_twice. Qed.
    Lemma empty_difference_L X Y : X ⊆ Y → X ∖ Y = ∅.
    Proof. unfold_leibniz. apply empty_difference. Qed.
    Lemma difference_diag_L X : X ∖ X = ∅.
    Proof. unfold_leibniz. apply difference_diag. Qed.
    Lemma difference_union_distr_l_L X Y Z : (X ∪ Y) ∖ Z = X ∖ Z ∪ Y ∖ Z.
    Proof. unfold_leibniz. apply difference_union_distr_l. Qed.
    Lemma difference_intersection_distr_l_L X Y Z :
      (X ∩ Y) ∖ Z = X ∖ Z ∩ Y ∖ Z.
    Proof. unfold_leibniz. apply difference_intersection_distr_l. Qed.
  End leibniz.

  Section dec.
    Context `{∀ X Y : C, Decision (X ⊆ Y)}.
    Lemma not_elem_of_intersection x X Y : x ∉ X ∩ Y ↔ x ∉ X ∨ x ∉ Y.
    Proof. rewrite elem_of_intersection. destruct (decide (x ∈ X)); tauto. Qed.
    Lemma not_elem_of_difference x X Y : x ∉ X ∖ Y ↔ x ∉ X ∨ x ∈ Y.
    Proof. rewrite elem_of_difference. destruct (decide (x ∈ Y)); tauto. Qed.
    Lemma union_difference X Y : X ⊆ Y → Y ≡ X ∪ Y ∖ X.
    Proof.
      split; intros x; rewrite !elem_of_union, elem_of_difference; [|intuition].
      destruct (decide (x ∈ X)); intuition.
    Qed.
    Lemma non_empty_difference X Y : X ⊂ Y → Y ∖ X ≢ ∅.
    Proof.
      intros [HXY1 HXY2] Hdiff. destruct HXY2. intros x.
      destruct (decide (x ∈ X)); esolve_elem_of.
    Qed.

    Context `{!LeibnizEquiv C}.
    Lemma union_difference_L X Y : X ⊆ Y → Y = X ∪ Y ∖ X.
    Proof. unfold_leibniz. apply union_difference. Qed.
    Lemma non_empty_difference_L X Y : X ⊂ Y → Y ∖ X ≠ ∅.
    Proof. unfold_leibniz. apply non_empty_difference. Qed.
  End dec.
End collection.

Section collection_ops.
  Context `{CollectionOps A C}.

  Lemma elem_of_intersection_with_list (f : A → A → option A) Xs Y x :
    x ∈ intersection_with_list f Y Xs ↔ ∃ xs y,
      Forall2 (∈) xs Xs ∧ y ∈ Y ∧ foldr (λ x, (≫= f x)) (Some y) xs = Some x.
  Proof.
    split.
    * revert x. induction Xs; simpl; intros x HXs; [eexists [], x; intuition|].
      rewrite elem_of_intersection_with in HXs; destruct HXs as (x1&x2&?&?&?).
      destruct (IHXs x2) as (xs & y & hy & ? & ?); trivial.
      eexists (x1 :: xs), y. intuition (simplify_option_equality; auto).
    * intros (xs & y & Hxs & ? & Hx). revert x Hx.
      induction Hxs; intros; simplify_option_equality; [done |].
      rewrite elem_of_intersection_with. naive_solver.
  Qed.

  Lemma intersection_with_list_ind (P Q : A → Prop) f Xs Y :
    (∀ y, y ∈ Y → P y) →
    Forall (λ X, ∀ x, x ∈ X → Q x) Xs →
    (∀ x y z, Q x → P y → f x y = Some z → P z) →
    ∀ x, x ∈ intersection_with_list f Y Xs → P x.
  Proof.
    intros HY HXs Hf. induction Xs; simplify_option_equality; [done |].
    intros x Hx. rewrite elem_of_intersection_with in Hx.
    decompose_Forall. destruct Hx as (? & ? & ? & ? & ?). eauto.
  Qed.
End collection_ops.

(** * Sets without duplicates up to an equivalence *)
Section NoDup.
  Context `{SimpleCollection A B} (R : relation A) `{!Equivalence R}.

  Definition elem_of_upto (x : A) (X : B) := ∃ y, y ∈ X ∧ R x y.
  Definition set_NoDup (X : B) := ∀ x y, x ∈ X → y ∈ X → R x y → x = y.

  Global Instance: Proper ((≡) ==> iff) (elem_of_upto x).
  Proof. intros ??? E. unfold elem_of_upto. by setoid_rewrite E. Qed.
  Global Instance: Proper (R ==> (≡) ==> iff) elem_of_upto.
  Proof.
    intros ?? E1 ?? E2. split; intros [z [??]]; exists z.
    * rewrite <-E1, <-E2; intuition.
    * rewrite E1, E2; intuition.
  Qed.
  Global Instance: Proper ((≡) ==> iff) set_NoDup.
  Proof. firstorder. Qed.

  Lemma elem_of_upto_elem_of x X : x ∈ X → elem_of_upto x X.
  Proof. unfold elem_of_upto. esolve_elem_of. Qed.
  Lemma elem_of_upto_empty x : ¬elem_of_upto x ∅.
  Proof. unfold elem_of_upto. esolve_elem_of. Qed.
  Lemma elem_of_upto_singleton x y : elem_of_upto x {[ y ]} ↔ R x y.
  Proof. unfold elem_of_upto. esolve_elem_of. Qed.

  Lemma elem_of_upto_union X Y x :
    elem_of_upto x (X ∪ Y) ↔ elem_of_upto x X ∨ elem_of_upto x Y.
  Proof. unfold elem_of_upto. esolve_elem_of. Qed.
  Lemma not_elem_of_upto x X : ¬elem_of_upto x X → ∀ y, y ∈ X → ¬R x y.
  Proof. unfold elem_of_upto. esolve_elem_of. Qed.

  Lemma set_NoDup_empty: set_NoDup ∅.
  Proof. unfold set_NoDup. solve_elem_of. Qed.
  Lemma set_NoDup_add x X :
    ¬elem_of_upto x X → set_NoDup X → set_NoDup ({[ x ]} ∪ X).
  Proof. unfold set_NoDup, elem_of_upto. esolve_elem_of. Qed.
  Lemma set_NoDup_inv_add x X :
    x ∉ X → set_NoDup ({[ x ]} ∪ X) → ¬elem_of_upto x X.
  Proof.
    intros Hin Hnodup [y [??]].
    rewrite (Hnodup x y) in Hin; solve_elem_of.
  Qed.
  Lemma set_NoDup_inv_union_l X Y : set_NoDup (X ∪ Y) → set_NoDup X.
  Proof. unfold set_NoDup. solve_elem_of. Qed.
  Lemma set_NoDup_inv_union_r X Y : set_NoDup (X ∪ Y) → set_NoDup Y.
  Proof. unfold set_NoDup. solve_elem_of. Qed.
End NoDup.

(** * Quantifiers *)
Section quantifiers.
  Context `{SimpleCollection A B} (P : A → Prop).

  Definition set_Forall X := ∀ x, x ∈ X → P x.
  Definition set_Exists X := ∃ x, x ∈ X ∧ P x.

  Lemma set_Forall_empty : set_Forall ∅.
  Proof. unfold set_Forall. solve_elem_of. Qed.
  Lemma set_Forall_singleton x : set_Forall {[ x ]} ↔ P x.
  Proof. unfold set_Forall. solve_elem_of. Qed.
  Lemma set_Forall_union X Y : set_Forall X → set_Forall Y → set_Forall (X ∪ Y).
  Proof. unfold set_Forall. solve_elem_of. Qed.
  Lemma set_Forall_union_inv_1 X Y : set_Forall (X ∪ Y) → set_Forall X.
  Proof. unfold set_Forall. solve_elem_of. Qed.
  Lemma set_Forall_union_inv_2 X Y : set_Forall (X ∪ Y) → set_Forall Y.
  Proof. unfold set_Forall. solve_elem_of. Qed.

  Lemma set_Exists_empty : ¬set_Exists ∅.
  Proof. unfold set_Exists. esolve_elem_of. Qed.
  Lemma set_Exists_singleton x : set_Exists {[ x ]} ↔ P x.
  Proof. unfold set_Exists. esolve_elem_of. Qed.
  Lemma set_Exists_union_1 X Y : set_Exists X → set_Exists (X ∪ Y).
  Proof. unfold set_Exists. esolve_elem_of. Qed.
  Lemma set_Exists_union_2 X Y : set_Exists Y → set_Exists (X ∪ Y).
  Proof. unfold set_Exists. esolve_elem_of. Qed.
  Lemma set_Exists_union_inv X Y :
    set_Exists (X ∪ Y) → set_Exists X ∨ set_Exists Y.
  Proof. unfold set_Exists. esolve_elem_of. Qed.
End quantifiers.

Section more_quantifiers.
  Context `{SimpleCollection A B}.

  Lemma set_Forall_weaken (P Q : A → Prop) (Hweaken : ∀ x, P x → Q x) X :
    set_Forall P X → set_Forall Q X.
  Proof. unfold set_Forall. naive_solver. Qed.
  Lemma set_Exists_weaken (P Q : A → Prop) (Hweaken : ∀ x, P x → Q x) X :
    set_Exists P X → set_Exists Q X.
  Proof. unfold set_Exists. naive_solver. Qed.
End more_quantifiers.

(** * Fresh elements *)
(** We collect some properties on the [fresh] operation. In particular we
generalize [fresh] to generate lists of fresh elements. *)
Section fresh.
  Context `{FreshSpec A C} .

  Definition fresh_sig (X : C) : { x : A | x ∉ X } :=
    exist (∉ X) (fresh X) (is_fresh X).

  Global Instance fresh_proper: Proper ((≡) ==> (=)) fresh.
  Proof. intros ???. by apply fresh_proper_alt, elem_of_equiv. Qed.

  Fixpoint fresh_list (n : nat) (X : C) : list A :=
    match n with
    | 0 => []
    | S n => let x := fresh X in x :: fresh_list n ({[ x ]} ∪ X)
    end.

  Global Instance fresh_list_proper: Proper ((=) ==> (≡) ==> (=)) fresh_list.
  Proof.
    intros ? n ->. induction n as [|n IH]; intros ?? E; f_equal'; [by rewrite E|].
    apply IH. by rewrite E.
  Qed.
  Lemma fresh_list_length n X : length (fresh_list n X) = n.
  Proof. revert X. induction n; simpl; auto. Qed.
  Lemma fresh_list_is_fresh n X x : x ∈ fresh_list n X → x ∉ X.
  Proof.
    revert X. induction n as [|n IH]; intros X; simpl; [by rewrite elem_of_nil|].
    rewrite elem_of_cons; intros [->| Hin]; [apply is_fresh|].
    apply IH in Hin; solve_elem_of.
  Qed.
  Lemma fresh_list_nodup n X : NoDup (fresh_list n X).
  Proof.
    revert X. induction n; simpl; constructor; auto.
    intros Hin. apply fresh_list_is_fresh in Hin. solve_elem_of.
  Qed.
End fresh.

(** * Properties of implementations of collections that form a monad *)
Section collection_monad.
  Context `{CollectionMonad M}.

  Global Instance collection_fmap_proper {A B} (f : A → B) :
    Proper ((≡) ==> (≡)) (fmap f).
  Proof. intros X Y E. esolve_elem_of. Qed.
  Global Instance collection_ret_proper {A} :
    Proper ((=) ==> (≡)) (@mret M _ A).
  Proof. intros X Y E. esolve_elem_of. Qed.
  Global Instance collection_bind_proper {A B} (f : A → M B) :
    Proper ((≡) ==> (≡)) (mbind f).
  Proof. intros X Y E. esolve_elem_of. Qed.
  Global Instance collection_join_proper {A} :
    Proper ((≡) ==> (≡)) (@mjoin M _ A).
  Proof. intros X Y E. esolve_elem_of. Qed.

  Lemma collection_fmap_compose {A B C} (f : A → B) (g : B → C) X :
    g ∘ f <$> X ≡ g <$> (f <$> X).
  Proof. esolve_elem_of. Qed.
  Lemma elem_of_fmap_1 {A B} (f : A → B) (X : M A) (y : B) :
    y ∈ f <$> X → ∃ x, y = f x ∧ x ∈ X.
  Proof. esolve_elem_of. Qed.
  Lemma elem_of_fmap_2 {A B} (f : A → B) (X : M A) (x : A) :
    x ∈ X → f x ∈ f <$> X.
  Proof. esolve_elem_of. Qed.
  Lemma elem_of_fmap_2_alt {A B} (f : A → B) (X : M A) (x : A) (y : B) :
    x ∈ X → y = f x → y ∈ f <$> X.
  Proof. esolve_elem_of. Qed.

  Lemma elem_of_mapM {A B} (f : A → M B) l k :
    l ∈ mapM f k ↔ Forall2 (λ x y, x ∈ f y) l k.
  Proof.
    split.
    * revert l. induction k; esolve_elem_of.
    * induction 1; esolve_elem_of.
  Qed.
  Lemma collection_mapM_length {A B} (f : A → M B) l k :
    l ∈ mapM f k → length l = length k.
  Proof. revert l; induction k; esolve_elem_of. Qed.

  Lemma elem_of_mapM_fmap {A B} (f : A → B) (g : B → M A) l k :
    Forall (λ x, ∀ y, y ∈ g x → f y = x) l → k ∈ mapM g l → fmap f k = l.
  Proof.
    intros Hl. revert k. induction Hl; simpl; intros;
      decompose_elem_of; f_equal'; auto.
  Qed.

  Lemma elem_of_mapM_Forall {A B} (f : A → M B) (P : B → Prop) l k :
    l ∈ mapM f k → Forall (λ x, ∀ y, y ∈ f x → P y) k → Forall P l.
  Proof. rewrite elem_of_mapM. apply Forall2_Forall_l. Qed.
  Lemma elem_of_mapM_Forall2_l {A B C} (f : A → M B) (P: B → C → Prop) l1 l2 k :
    l1 ∈ mapM f k → Forall2 (λ x y, ∀ z, z ∈ f x → P z y) k l2 →
    Forall2 P l1 l2.
  Proof.
    rewrite elem_of_mapM. intros Hl1. revert l2.
    induction Hl1; inversion_clear 1; constructor; auto.
  Qed.
End collection_monad.
