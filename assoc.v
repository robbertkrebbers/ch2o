(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** An implementation of finite maps and finite sets using association lists
ordered by keys. Although the lookup and insert operation are linear-time, the
main advantage of these association lists compared to search trees, is that it
has canonical representatives and thus extensional Leibniz equality. Compared
to a naive unordered association list, the merge operation (used for unions,
intersections, and difference) is also linear-time. *)
Require Import mapset.
Require Export fin_maps.

(** Because the association list is sorted using [strict lexico] instead of
[lexico], it automatically guarantees that no duplicates exist. *)
Definition assoc (K : Type) `{Lexico K} `{!TrichotomyT lexico}
    `{!StrictOrder lexico} (A : Type) : Type :=
  dsig (λ l : list (K * A), StronglySorted lexico (fst <$> l)).

Section assoc.
Context `{Lexico K} `{!StrictOrder lexico}.
Context `{∀ x y : K, Decision (x = y)} `{!TrichotomyT lexico}.

Infix "⊂" := lexico.
Notation assoc_before j l :=
  (Forall (lexico j) (fst <$> l)) (only parsing).
Notation assoc_wf l :=
  (StronglySorted (lexico) (fst <$> l)) (only parsing).

Lemma assoc_before_transitive {A} (l : list (K * A)) i j :
  i ⊂ j → assoc_before j l → assoc_before i l.
Proof. intros. eapply Forall_impl; eauto. intros. by transitivity j. Qed.
Hint Resolve assoc_before_transitive.

Hint Extern 1 (StronglySorted _ []) => constructor.
Hint Extern 1 (StronglySorted _ (_ :: _)) => constructor.
Hint Extern 1 (Forall _ []) => constructor.
Hint Extern 1 (Forall _ (_ :: _)) => constructor.
Hint Extern 100 => progress simpl.

Ltac simplify_assoc := intros;
  repeat match goal with
  | H : Forall _ [] |- _ => clear H
  | H : Forall _ (_ :: _) |- _ => inversion_clear H
  | H : StronglySorted _ [] |- _ => clear H
  | H : StronglySorted _ (_ :: _) |- _ => inversion_clear H
  | _ => progress decompose_elem_of_list
  | _ => progress simplify_equality'
  end;
  repeat first
  [ progress simplify_order
  | progress autorewrite with assoc in *; simplify_equality'
  | destruct (trichotomyT lexico) as [[?|?]|?]; simplify_equality' ];
  eauto 9.

Fixpoint assoc_lookup_raw {A} (i : K) (l : list (K * A)) : option A :=
  match l with
  | [] => None
  | (j,x) :: l =>
    match trichotomyT lexico i j with
    | (**i i ⊂ j *) inleft (left _) => None
    | (**i i = j *) inleft (right _) => Some x
    | (**i j ⊂ i *) inright _ => assoc_lookup_raw i l
    end
  end.
Global Instance assoc_lookup {A} : Lookup K A (assoc K A) := λ k m,
  assoc_lookup_raw k (`m).

Lemma assoc_lookup_before {A} (l : list (K * A)) i :
  assoc_before i l → assoc_lookup_raw i l = None.
Proof. induction l as [|[??]]; simplify_assoc. Qed.
Hint Rewrite @assoc_lookup_before using (by eauto) : assoc.

Lemma assoc_eq {A} (l1 l2 : list (K * A)) :
  assoc_wf l1 → assoc_wf l2 →
  (∀ i, assoc_lookup_raw i l1 = assoc_lookup_raw i l2) → l1 = l2.
Proof.
  revert l2. induction l1 as [|[i x] l1 IH]; intros [|[j y] l2]; intros ?? E.
  { done. }
  { specialize (E j); simplify_assoc; by repeat constructor. }
  { specialize (E i); simplify_assoc; by repeat constructor. }
  pose proof (E i); pose proof (E j); simplify_assoc.
  f_equal. apply IH; auto. intros i'. specialize (E i'); simplify_assoc.
Qed.
Definition assoc_empty_wf {A} : assoc_wf (@nil (K * A)).
Proof. constructor. Qed.
Global Instance assoc_empty {A} : Empty (assoc K A) := dexist _ assoc_empty_wf.

Definition assoc_cons {A} (i : K) (o : option A) (l : list (K * A)) :
  list (K * A) := match o with None => l | Some z => (i,z) :: l end.
Lemma assoc_cons_before {A} (l : list (K * A)) i j o :
  assoc_before i l → i ⊂ j → assoc_before i (assoc_cons j o l).
Proof. destruct o; simplify_assoc. Qed.
Lemma assoc_cons_wf {A} (l : list (K * A)) i o :
  assoc_wf l → assoc_before i l → assoc_wf (assoc_cons i o l).
Proof. destruct o; simplify_assoc. Qed.
Hint Resolve assoc_cons_before assoc_cons_wf.
Lemma assoc_lookup_cons {A} (l : list (K * A)) i o :
  assoc_before i l → assoc_lookup_raw i (assoc_cons i o l) = o.
Proof. destruct o; simplify_assoc. Qed.
Lemma assoc_lookup_cons_lt {A} (l : list (K * A)) i j o :
  i ⊂ j → assoc_before i l → assoc_lookup_raw i (assoc_cons j o l) = None.
Proof. destruct o; simplify_assoc. Qed.
Lemma assoc_lookup_cons_gt {A} (l : list (K * A)) i j o :
  j ⊂ i → assoc_lookup_raw i (assoc_cons j o l) = assoc_lookup_raw i l.
Proof. destruct o; simplify_assoc. Qed.
Hint Rewrite @assoc_lookup_cons @assoc_lookup_cons_lt
  @assoc_lookup_cons_gt using (by eauto 8) : assoc.

Fixpoint assoc_alter_raw {A} (f : option A → option A)
    (i : K) (l : list (K * A)) : list (K * A) :=
  match l with
  | [] => assoc_cons i (f None) []
  | (j,x) :: l =>
    match trichotomyT lexico i j with
    | (**i i ⊂ j *) inleft (left _) => assoc_cons i (f None) ((j,x) :: l)
    | (**i i = j *) inleft (right _) => assoc_cons j (f (Some x)) l
    | (**i j ⊂ i *) inright _ => (j,x) :: assoc_alter_raw f i l
    end
  end.
Lemma assoc_alter_wf {A} (f : option A → option A) i l :
  assoc_wf l → assoc_wf (assoc_alter_raw f i l).
Proof.
  revert l. assert (∀ j l,
    j ⊂ i → assoc_before j l → assoc_before j (assoc_alter_raw f i l)).
  { intros j l. induction l as [|[??]]; simplify_assoc. }
  intros l. induction l as [|[??]]; simplify_assoc.
Qed.
Global Instance assoc_alter {A} : PartialAlter K A (assoc K A) := λ f i m,
  dexist _ (assoc_alter_wf f i _ (proj2_dsig m)).

Lemma assoc_lookup_raw_alter {A} f (l : list (K * A)) i :
  assoc_wf l →
  assoc_lookup_raw i (assoc_alter_raw f i l) = f (assoc_lookup_raw i l).
Proof. induction l as [|[??]]; simplify_assoc. Qed.
Lemma assoc_lookup_raw_alter_ne {A} f (l : list (K * A)) i j :
  assoc_wf l → i ≠ j →
  assoc_lookup_raw j (assoc_alter_raw f i l) = assoc_lookup_raw j l.
Proof.
  induction l as [|[??]]; simplify_assoc; unfold assoc_cons;
    destruct (f _); simplify_assoc.
Qed.
Lemma assoc_fmap_wf {A B} (f : A → B) (l : list (K * A)) :
  assoc_wf l → assoc_wf (snd_map f <$> l).
Proof.
  intros. by rewrite <-list_fmap_compose,
    (list_fmap_ext _ fst l l) by (done; by intros []).
Qed.
Global Program Instance assoc_fmap: FMap (assoc K) := λ A B f m,
  dexist _ (assoc_fmap_wf f _ (proj2_dsig m)).

Lemma assoc_lookup_fmap {A B} (f : A → B) (l : list (K * A)) i :
  assoc_lookup_raw i (snd_map f <$> l) = fmap f (assoc_lookup_raw i l).
Proof. induction l as [|[??]]; simplify_assoc. Qed.

Fixpoint assoc_merge_aux {A B} (f : option A → option B)
    (l : list (K * A)) : list (K * B) :=
  match l with
  | [] => []
  | (i,x) :: l => assoc_cons i (f (Some x)) (assoc_merge_aux f l)
  end.
Fixpoint assoc_merge_raw {A B C} (f : option A → option B → option C)
    (l : list (K * A)) : list (K * B) → list (K * C) :=
  fix go (k : list (K * B)) :=
  match l, k with
  | [], _ => assoc_merge_aux (f None) k
  | _, [] => assoc_merge_aux (flip f None) l
  | (i,x) :: l, (j,y) :: k =>
    match trichotomyT lexico i j with
    | (**i i ⊂ j *) inleft (left _) =>
      assoc_cons i (f (Some x) None) (assoc_merge_raw f l ((j,y) :: k))
    | (**i i = j *) inleft (right _) =>
      assoc_cons i (f (Some x) (Some y)) (assoc_merge_raw f l k)
    | (**i j ⊂ i *) inright _ =>
      assoc_cons j (f None (Some y)) (go k)
    end
  end.

Section assoc_merge_raw.
  Context  {A B C} (f : option A → option B → option C).

  Lemma assoc_merge_nil_l k :
    assoc_merge_raw f [] k = assoc_merge_aux (f None) k.
  Proof. by destruct k. Qed.
  Lemma assoc_merge_nil_r l :
    assoc_merge_raw f l [] = assoc_merge_aux (flip f None) l.
  Proof. by destruct l as [|[??]]. Qed.
  Lemma assoc_merge_cons i x j y l k :
    assoc_merge_raw f ((i,x) :: l) ((j,y) :: k) =
      match trichotomyT lexico i j with
      | (**i i ⊂ j *) inleft (left _) =>
        assoc_cons i (f (Some x) None) (assoc_merge_raw f l ((j,y) :: k))
      | (**i i = j *) inleft (right _) =>
        assoc_cons i (f (Some x) (Some y)) (assoc_merge_raw f l k)
      | (**i j ⊂ i *) inright _ =>
        assoc_cons j (f None (Some y)) (assoc_merge_raw f ((i,x) :: l) k)
      end.
  Proof. done. Qed.
End assoc_merge_raw.

Arguments assoc_merge_raw _ _ _ _ _ _ : simpl never.
Hint Rewrite @assoc_merge_nil_l @assoc_merge_nil_r @assoc_merge_cons : assoc.

Lemma assoc_merge_aux_before {A B} (f : option A → option B) l j :
  assoc_before j l → assoc_before j (assoc_merge_aux f l).
Proof. induction l as [|[??]]; simplify_assoc. Qed.
Hint Resolve assoc_merge_aux_before.
Lemma assoc_merge_before {A B C} (f : option A → option B → option C) l1 l2 j :
  assoc_before j l1 → assoc_before j l2 →
  assoc_before j (assoc_merge_raw f l1 l2).
Proof.
  revert l2. induction l1 as [|[??] l1 IH];
    intros l2; induction l2 as [|[??] l2 IH2]; simplify_assoc.
Qed.
Hint Resolve assoc_merge_before.

Lemma assoc_merge_wf {A B C} (f : option A → option B → option C) l1 l2 :
  assoc_wf l1 → assoc_wf l2 → assoc_wf (assoc_merge_raw f l1 l2).
Proof.
  revert A B C f l1 l2. assert (∀ A B (f : option A → option B) l,
    assoc_wf l → assoc_wf (assoc_merge_aux f l)).
  { intros ?? j l. induction l as [|[??]]; simplify_assoc. }
  intros A B C f l1. induction l1 as [|[i x] l1 IH];
    intros l2; induction l2 as [|[j y] l2 IH2]; simplify_assoc.
Qed.
Global Instance assoc_merge: Merge (assoc K) := λ A B C f m1 m2,
  dexist (merge f (`m1) (`m2))
    (assoc_merge_wf _ _ _ (proj2_dsig m1) (proj2_dsig m2)).

Lemma assoc_merge_aux_spec {A B} (f : option A → option B) l i :
  f None = None → assoc_wf l →
  assoc_lookup_raw i (assoc_merge_aux f l) = f (assoc_lookup_raw i l).
Proof. intros. induction l as [|[??]]; simplify_assoc. Qed.
Hint Rewrite @assoc_merge_aux_spec using (by eauto) : assoc.

Lemma assoc_merge_spec {A B C} (f : option A → option B → option C) l1 l2 i :
  f None None = None → assoc_wf l1 → assoc_wf l2 →
  assoc_lookup_raw i (assoc_merge_raw f l1 l2) =
    f (assoc_lookup_raw i l1) (assoc_lookup_raw i l2).
Proof.
  intros ?. revert l2. induction l1 as [|[??] l1 IH]; intros l2;
    induction l2 as [|[??] l2 IH2]; simplify_assoc; rewrite ?IH; simplify_assoc.
Qed.

Global Instance assoc_to_list {A} : FinMapToList K A (assoc K A) := proj1_sig.
Lemma assoc_to_list_nodup {A} (l : list (K * A)) : assoc_wf l → NoDup l.
Proof.
  revert l. assert (∀ i x (l : list (K * A)), assoc_before i l → (i,x) ∉ l).
  { intros i x l. rewrite Forall_fmap, Forall_forall. intros Hl Hi.
    destruct (irreflexivity (lexico) i). by apply (Hl (i,x) Hi). }
  induction l as [|[??]]; simplify_assoc; constructor; auto.
Qed.
Lemma assoc_to_list_elem_of {A} (l : list (K * A)) i x :
  assoc_wf l → (i,x) ∈ l ↔ assoc_lookup_raw i l = Some x.
Proof.
  split.
  * induction l as [|[??]]; simplify_assoc; naive_solver.
  * induction l as [|[??]]; simplify_assoc; [left| right]; eauto.
Qed.

(** * Instantiation of the finite map interface *)
Hint Extern 1 (assoc_wf _) => by apply (bool_decide_unpack _).
Global Instance: FinMap K (assoc K).
Proof.
  split.
  * intros ? [l1 ?] [l2 ?] ?. apply (sig_eq_pi _), assoc_eq; auto.
  * done.
  * intros ?? [??] ?. apply assoc_lookup_raw_alter; auto. 
  * intros ?? [??] ???. apply assoc_lookup_raw_alter_ne; auto.
  * intros ??? [??] ?. apply assoc_lookup_fmap.
  * intros ? [??]. apply assoc_to_list_nodup; auto.
  * intros ? [??] ??. apply assoc_to_list_elem_of; auto.
  * intros ????? [??] [??] ?. apply assoc_merge_spec; auto.
Qed.
End assoc.

(** * Finite sets *)
(** We construct finite sets using the above implementation of maps. *)
Notation assoc_set K := (mapset (assoc K)).
Instance assoc_map_dom `{Lexico K} `{!TrichotomyT (@lexico K _)}
  `{!StrictOrder lexico} {A} : Dom (assoc K A) (assoc_set K) := mapset_dom.
Instance assoc_map_dom_spec `{Lexico K} `{!TrichotomyT (@lexico K _)}
    `{!StrictOrder lexico} `{∀ x y : K, Decision (x = y)} :
  FinMapDom K (assoc K) (assoc_set K) := mapset_dom_spec.
