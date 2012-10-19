(* Copyright (c) 2012, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects definitions and theorems on collections. Most
importantly, it implements some tactics to automatically solve goals involving
collections. *)
Require Export base tactics orders.

(** * Theorems *)
Section collection.
  Context `{Collection A C}.

  Lemma elem_of_empty x : x ∈ ∅ ↔ False.
  Proof. split. apply not_elem_of_empty. done. Qed.
  Lemma elem_of_union_l x X Y : x ∈ X → x ∈ X ∪ Y.
  Proof. intros. apply elem_of_union. auto. Qed.
  Lemma elem_of_union_r x X Y : x ∈ Y → x ∈ X ∪ Y.
  Proof. intros. apply elem_of_union. auto. Qed.

  Global Instance collection_subseteq: SubsetEq C := λ X Y,
    ∀ x, x ∈ X → x ∈ Y.
  Global Instance: LowerBoundedLattice C.
  Proof. firstorder auto. Qed.

  Lemma elem_of_subseteq X Y : X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y.
  Proof. done. Qed.
  Lemma elem_of_equiv X Y : X ≡ Y ↔ ∀ x, x ∈ X ↔ x ∈ Y.
  Proof. firstorder. Qed.
  Lemma elem_of_equiv_alt X Y :
    X ≡ Y ↔ (∀ x, x ∈ X → x ∈ Y) ∧ (∀ x, x ∈ Y → x ∈ X).
  Proof. firstorder. Qed.
  Lemma elem_of_subseteq_singleton x X : x ∈ X ↔ {[ x ]} ⊆ X.
  Proof.
    split.
    * intros ??. rewrite elem_of_singleton. intro. by subst.
    * intros Ex. by apply (Ex x), elem_of_singleton.
  Qed.
  Global Instance singleton_proper : Proper ((=) ==> (≡)) singleton.
  Proof. repeat intro. by subst. Qed.
  Global Instance elem_of_proper: Proper ((=) ==> (≡) ==> iff) (∈).
  Proof. intros ???. subst. firstorder. Qed.

  Lemma elem_of_union_list (x : A) (Xs : list C) :
    x ∈ ⋃ Xs ↔ ∃ X, In X Xs ∧ x ∈ X.
  Proof.
    split.
    * induction Xs; simpl; intros HXs.
      + by apply elem_of_empty in HXs.
      + apply elem_of_union in HXs. naive_solver.
    * intros [X []]. induction Xs; [done | intros [?|?] ?; subst; simpl].
      + by apply elem_of_union_l.
      + apply elem_of_union_r; auto.
  Qed.

  Lemma non_empty_singleton x : {[ x ]} ≢ ∅.
  Proof. intros [E _]. by apply (elem_of_empty x), E, elem_of_singleton. Qed.

  Lemma intersection_twice x : {[x]} ∩ {[x]} ≡ {[x]}.
  Proof.
    split; intros y; rewrite elem_of_intersection, !elem_of_singleton; tauto.
  Qed.
  Lemma not_elem_of_singleton x y : x ∉ {[ y ]} ↔ x ≠ y.
  Proof. by rewrite elem_of_singleton. Qed.
  Lemma not_elem_of_union x X Y : x ∉ X ∪ Y ↔ x ∉ X ∧ x ∉ Y.
  Proof. rewrite elem_of_union. tauto. Qed.

  Context `{∀ (X Y : C), Decision (X ⊆ Y)}.

  Global Instance elem_of_dec_slow (x : A) (X : C) : Decision (x ∈ X) | 100.
  Proof.
    refine (cast_if (decide_rel (⊆) {[ x ]} X));
      by rewrite elem_of_subseteq_singleton.
  Defined.

  Lemma not_elem_of_intersection x X Y : x ∉ X ∩ Y ↔ x ∉ X ∨ x ∉ Y.
  Proof.
    rewrite elem_of_intersection.
    destruct (decide (x ∈ X)); tauto.
  Qed.
  Lemma not_elem_of_difference x X Y : x ∉ X ∖ Y ↔ x ∉ X ∨ x ∈ Y.
  Proof.
    rewrite elem_of_difference.
    destruct (decide (x ∈ Y)); tauto.
  Qed.
  Lemma union_difference X Y : X ∪ Y ∖ X ≡ X ∪ Y.
  Proof.
    split; intros x; rewrite !elem_of_union, elem_of_difference.
    * tauto.
    * destruct (decide (x ∈ X)); tauto.
  Qed.
End collection.

Ltac decompose_empty := repeat
  match goal with
  | H : _ ∪ _ ≡ ∅ |- _ => apply empty_union in H; destruct H
  | H : _ ∪ _ ≢ ∅ |- _ => apply non_empty_union in H; destruct H
  | H : {[ _ ]} ≡ ∅ |- _ => destruct (non_empty_singleton _ H)
  end.

(** * Theorems about map *)
Section map.
  Context `{Collection A C}.

  Lemma elem_of_map_1 (f : A → A) (X : C) (x : A) :
    x ∈ map f X → ∃ y, x = f y ∧ y ∈ X.
  Proof. intros. by apply (elem_of_map _). Qed.
  Lemma elem_of_map_2 (f : A → A) (X : C) (x : A) :
    x ∈ X → f x ∈ map f X.
  Proof. intros. apply (elem_of_map _). eauto. Qed.
  Lemma elem_of_map_2_alt (f : A → A) (X : C) (x : A) y :
    x ∈ X → y = f x → y ∈ map f X.
  Proof. intros. apply (elem_of_map _). eauto. Qed.
End map.

(** * Tactics *)
(** The first pass consists of eliminating all occurrences of [(∪)], [(∩)],
[(∖)], [map], [∅], [{[_]}], [(≡)], and [(⊆)], by rewriting these into
logically equivalent propositions. For example we rewrite [A → x ∈ X ∪ ∅] into
[A → x ∈ X ∨ False]. *)
Ltac unfold_elem_of :=
  repeat_on_hyps (fun H =>
    repeat match type of H with
    | context [ _ ⊆ _ ] => setoid_rewrite elem_of_subseteq in H
    | context [ _ ≡ _ ] => setoid_rewrite elem_of_equiv_alt in H
    | context [ _ ∈ ∅ ] => setoid_rewrite elem_of_empty in H
    | context [ _ ∈ {[ _ ]} ] => setoid_rewrite elem_of_singleton in H
    | context [ _ ∈ _ ∪ _ ] => setoid_rewrite elem_of_union in H
    | context [ _ ∈ _ ∩ _ ] => setoid_rewrite elem_of_intersection in H
    | context [ _ ∈ _ ∖ _ ] => setoid_rewrite elem_of_difference in H
    | context [ _ ∈ map _ _ ] => setoid_rewrite elem_of_map in H
    end);
  repeat match goal with
  | |- context [ _ ⊆ _ ] => setoid_rewrite elem_of_subseteq
  | |- context [ _ ≡ _ ] => setoid_rewrite elem_of_equiv_alt
  | |- context [ _ ∈ ∅ ] => setoid_rewrite elem_of_empty
  | |- context [ _ ∈ {[ _ ]} ] => setoid_rewrite elem_of_singleton
  | |- context [ _ ∈ _ ∪ _ ] => setoid_rewrite elem_of_union
  | |- context [ _ ∈ _ ∩ _ ] => setoid_rewrite elem_of_intersection
  | |- context [ _ ∈ _ ∖ _ ] => setoid_rewrite elem_of_difference
  | |- context [ _ ∈ map _ _ ] => setoid_rewrite elem_of_map
  end.

(** The tactic [solve_elem_of tac] composes the above tactic with [intuition].
For goals that do not involve [≡], [⊆], [map], or quantifiers this tactic is
generally powerful enough. This tactic either fails or proves the goal. *)
Tactic Notation "solve_elem_of" tactic3(tac) :=
  simpl in *;
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
  unfold_elem_of;
  naive_solver tac.
Tactic Notation "esolve_elem_of" := esolve_elem_of eauto.

(** Given a hypothesis [H : _ ∈ _], the tactic [destruct_elem_of H] will
recursively split [H] for [(∪)], [(∩)], [(∖)], [map], [∅], [{[_]}]. *)
Tactic Notation "decompose_elem_of" hyp(H) :=
  let rec go H :=
  lazymatch type of H with
  | _ ∈ ∅ => apply elem_of_empty in H; destruct H
  | ?l ∈ {[ ?l' ]} =>
    apply elem_of_singleton in H; first [ subst l' | subst l | idtac ]
  | _ ∈ _ ∪ _ =>
    let H1 := fresh in let H2 := fresh in apply elem_of_union in H;
    destruct H as [H1|H2]; [go H1 | go H2]
  | _ ∈ _ ∩ _ =>
    let H1 := fresh in let H2 := fresh in apply elem_of_intersection in H;
    destruct H as [H1 H2]; go H1; go H2
  | _ ∈ _ ∖ _ =>
    let H1 := fresh in let H2 := fresh in apply elem_of_difference in H;
    destruct H as [H1 H2]; go H1; go H2
  | _ ∈ map _ _ =>
    let H1 := fresh in apply elem_of_map in H;
    destruct H as [?[? H1]]; go H1
  | _ => idtac
  end in go H.
Tactic Notation "decompose_elem_of" :=
  repeat_on_hyps (fun H => decompose_elem_of H).

(** * Sets without duplicates up to an equivalence *)
Section no_dup.
  Context `{Collection A B} (R : relation A) `{!Equivalence R}.

  Definition elem_of_upto (x : A) (X : B) := ∃ y, y ∈ X ∧ R x y.
  Definition no_dup (X : B) := ∀ x y, x ∈ X → y ∈ X → R x y → x = y.

  Global Instance: Proper ((≡) ==> iff) (elem_of_upto x).
  Proof. firstorder. Qed.
  Global Instance: Proper (R ==> (≡) ==> iff) elem_of_upto.
  Proof.
    intros ?? E1 ?? E2. split; intros [z [??]]; exists z.
    * rewrite <-E1, <-E2; intuition.
    * rewrite E1, E2; intuition.
  Qed.
  Global Instance: Proper ((≡) ==> iff) no_dup.
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

  Lemma no_dup_empty: no_dup ∅.
  Proof. unfold no_dup. solve_elem_of. Qed.
  Lemma no_dup_add x X : ¬elem_of_upto x X → no_dup X → no_dup ({[ x ]} ∪ X).
  Proof. unfold no_dup, elem_of_upto. esolve_elem_of. Qed.
  Lemma no_dup_inv_add x X : x ∉ X → no_dup ({[ x ]} ∪ X) → ¬elem_of_upto x X.
  Proof.
    intros Hin Hnodup [y [??]].
    rewrite (Hnodup x y) in Hin; solve_elem_of.
  Qed.
  Lemma no_dup_inv_union_l X Y : no_dup (X ∪ Y) → no_dup X.
  Proof. unfold no_dup. solve_elem_of. Qed.
  Lemma no_dup_inv_union_r X Y : no_dup (X ∪ Y) → no_dup Y.
  Proof. unfold no_dup. solve_elem_of. Qed.
End no_dup.

(** * Quantifiers *)
Section quantifiers.
  Context `{Collection A B} (P : A → Prop).

  Definition cforall X := ∀ x, x ∈ X → P x.
  Definition cexists X := ∃ x, x ∈ X ∧ P x.

  Lemma cforall_empty : cforall ∅.
  Proof. unfold cforall. solve_elem_of. Qed.
  Lemma cforall_singleton x : cforall {[ x ]} ↔ P x.
  Proof. unfold cforall. solve_elem_of. Qed.
  Lemma cforall_union X Y : cforall X → cforall Y → cforall (X ∪ Y).
  Proof. unfold cforall. solve_elem_of. Qed.
  Lemma cforall_union_inv_1 X Y : cforall (X ∪ Y) → cforall X.
  Proof. unfold cforall. solve_elem_of. Qed.
  Lemma cforall_union_inv_2 X Y : cforall (X ∪ Y) → cforall Y.
  Proof. unfold cforall. solve_elem_of. Qed.

  Lemma cexists_empty : ¬cexists ∅.
  Proof. unfold cexists. esolve_elem_of. Qed.
  Lemma cexists_singleton x : cexists {[ x ]} ↔ P x.
  Proof. unfold cexists. esolve_elem_of. Qed.
  Lemma cexists_union_1 X Y : cexists X → cexists (X ∪ Y).
  Proof. unfold cexists. esolve_elem_of. Qed.
  Lemma cexists_union_2 X Y : cexists Y → cexists (X ∪ Y).
  Proof. unfold cexists. esolve_elem_of. Qed.
  Lemma cexists_union_inv X Y : cexists (X ∪ Y) → cexists X ∨ cexists Y.
  Proof. unfold cexists. esolve_elem_of. Qed.
End quantifiers.

Section more_quantifiers.
  Context `{Collection A B}.

  Lemma cforall_weaken (P Q : A → Prop) (Hweaken : ∀ x, P x → Q x) X :
    cforall P X → cforall Q X.
  Proof. unfold cforall. naive_solver. Qed.
  Lemma cexists_weaken (P Q : A → Prop) (Hweaken : ∀ x, P x → Q x) X :
    cexists P X → cexists Q X.
  Proof. unfold cexists. naive_solver. Qed.
End more_quantifiers.

(** * Fresh elements *)
(** We collect some properties on the [fresh] operation. In particular we
generalize [fresh] to generate lists of fresh elements. *)
Section fresh.
  Context `{Collection A C} `{Fresh A C} `{!FreshSpec A C} .

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
    intros ? n ?. subst.
    induction n; simpl; intros ?? E; f_equal.
    * by rewrite E.
    * apply IHn. by rewrite E.
  Qed.

  Lemma fresh_list_length n X : length (fresh_list n X) = n.
  Proof. revert X. induction n; simpl; auto. Qed.

  Lemma fresh_list_is_fresh n X x : In x (fresh_list n X) → x ∉ X.
  Proof.
    revert X. induction n; simpl.
    * done.
    * intros X [?| Hin]. subst.
      + apply is_fresh.
      + apply IHn in Hin. solve_elem_of.
  Qed.

  Lemma fresh_list_nodup n X : NoDup (fresh_list n X).
  Proof.
    revert X.
    induction n; simpl; constructor; auto.
    intros Hin. apply fresh_list_is_fresh in Hin.
    solve_elem_of.
  Qed.
End fresh.
