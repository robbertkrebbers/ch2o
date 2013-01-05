(* Copyright (c) 2012, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This files implements an efficient implementation of finite maps whose keys
range over Coq's data type of positive binary naturals [positive]. The
implementation is based on Xavier Leroy's implementation of radix-2 search
trees (uncompressed Patricia trees) and guarantees logarithmic-time operations.
However, we extend Leroy's implementation by packing the trees into a Sigma
type such that canonicity of representation is ensured. This is necesarry for
Leibniz equality to become extensional. *)
Require Import PArith.
Require Export prelude fin_maps.

Local Open Scope positive_scope.
Local Hint Extern 0 (@eq positive _ _) => congruence.
Local Hint Extern 0 (¬@eq positive _ _) => congruence.

(** * The tree data structure *)
(** The data type [Pmap_raw] specifies radix-2 search trees. These trees do
not ensure canonical representations of maps. For example the empty map can
be represented as a binary tree of an arbitrary size that contains [None] at
all nodes. *)
Inductive Pmap_raw A :=
  | Pleaf: Pmap_raw A
  | Pnode: Pmap_raw A → option A → Pmap_raw A → Pmap_raw A.
Arguments Pleaf {_}.
Arguments Pnode {_} _ _ _.

Instance Pmap_raw_eq_dec `{∀ x y : A, Decision (x = y)} (x y : Pmap_raw A) :
  Decision (x = y).
Proof. solve_decision. Defined.

(** The following predicate describes non empty trees. *)
Inductive Pmap_ne {A} : Pmap_raw A → Prop :=
  | Pmap_ne_val l x r : Pmap_ne (Pnode l (Some x) r)
  | Pmap_ne_l l r : Pmap_ne l → Pmap_ne (Pnode l None r)
  | Pmap_ne_r l r : Pmap_ne r → Pmap_ne (Pnode l None r).
Local Hint Constructors Pmap_ne.

Instance Pmap_ne_dec `(t : Pmap_raw A) : Decision (Pmap_ne t).
Proof.
  red. induction t as [|? IHl [?|] ? IHr].
  * right. by inversion 1.
  * intuition.
  * destruct IHl, IHr; try (by left; auto); right; by inversion_clear 1.
Qed.

(** The following predicate describes well well formed trees. A tree is well
formed if it is empty or if all nodes at the bottom contain a value. *)
Inductive Pmap_wf {A} : Pmap_raw A → Prop :=
  | Pmap_wf_leaf : Pmap_wf Pleaf
  | Pmap_wf_node l x r : Pmap_wf l → Pmap_wf r → Pmap_wf (Pnode l (Some x) r)
  | Pmap_wf_empty l r :
     Pmap_wf l → Pmap_wf r → (Pmap_ne l ∨ Pmap_ne r) → Pmap_wf (Pnode l None r).
Local Hint Constructors Pmap_wf.

Instance Pmap_wf_dec `(t : Pmap_raw A) : Decision (Pmap_wf t).
Proof.
  red. induction t as [|l IHl [?|] r IHr]; simpl.
  * intuition.
  * destruct IHl, IHr; try solve [left; intuition];
      right; by inversion_clear 1.
  * destruct IHl, IHr, (decide (Pmap_ne l)), (decide (Pmap_ne r));
      try solve [left; intuition];
      right; inversion_clear 1; intuition.
Qed.

(** Now we restrict the data type of trees to those that are well formed. *)
Definition Pmap A := @dsig (Pmap_raw A) Pmap_wf _.

(** * Operations on the data structure *)
Global Instance Pmap_dec `{∀ x y : A, Decision (x = y)} (t1 t2 : Pmap A) :
    Decision (t1 = t2) :=
  match Pmap_raw_eq_dec (`t1) (`t2) with
  | left H => left (proj2 (dsig_eq _ t1 t2) H)
  | right H => right (H ∘ proj1 (dsig_eq _ t1 t2))
  end.

Instance Pempty_raw {A} : Empty (Pmap_raw A) := Pleaf.
Global Instance Pempty {A} : Empty (Pmap A) :=
  (∅ : Pmap_raw A) ↾ bool_decide_pack _ Pmap_wf_leaf.

Instance Plookup_raw {A} : Lookup positive A (Pmap_raw A) :=
  fix Plookup_raw (i : positive) (t : Pmap_raw A) {struct t} : option A :=
  match t with
  | Pleaf => None
  | Pnode l o r =>
     match i with
     | 1 => o
     | i~0 => @lookup _ _ _ Plookup_raw i l
     | i~1 => @lookup _ _ _ Plookup_raw i r
     end
  end.
Instance Plookup {A} : Lookup positive A (Pmap A) := λ i t, `t !! i.

Lemma Plookup_raw_empty {A} i : (∅ : Pmap_raw A) !! i = None.
Proof. by destruct i. Qed.

Lemma Pmap_ne_lookup `(t : Pmap_raw A) : Pmap_ne t → ∃ i x, t !! i = Some x.
Proof.
  induction 1 as [? x ?| l r ? IHl | l r ? IHr].
  * intros. by exists 1 x.
  * destruct IHl as [i [x ?]]. by exists (i~0) x.
  * destruct IHr as [i [x ?]]. by exists (i~1) x.
Qed.

Lemma Pmap_wf_eq_get {A} (t1 t2 : Pmap_raw A) :
  Pmap_wf t1 → Pmap_wf t2 → (∀ i, t1 !! i = t2 !! i) → t1 = t2.
Proof.
  intros t1wf. revert t2.
  induction t1wf as [| ? x ? ? IHl ? IHr | l r ? IHl ? IHr Hne1 ].
  * destruct 1 as [| | ???? [?|?]]; intros Hget.
    + done.
    + discriminate (Hget 1).
    + destruct (Pmap_ne_lookup l) as [i [??]]; trivial.
      specialize (Hget (i~0)). simpl in *. congruence.
    + destruct (Pmap_ne_lookup r) as [i [??]]; trivial.
      specialize (Hget (i~1)). simpl in *. congruence.
  * destruct 1; intros Hget.
    + discriminate (Hget xH).
    + f_equal.
      - apply IHl; trivial. intros i. apply (Hget (i~0)).
      - apply (Hget 1).
      - apply IHr; trivial. intros i. apply (Hget (i~1)).
    + specialize (Hget 1). simpl in *. congruence.
  * destruct 1; intros Hget.
    + destruct Hne1.
      destruct (Pmap_ne_lookup l) as [i [??]]; trivial.
      - specialize (Hget (i~0)). simpl in *. congruence.
      - destruct (Pmap_ne_lookup r) as [i [??]]; trivial.
        specialize (Hget (i~1)). simpl in *. congruence.
    + specialize (Hget 1). simpl in *. congruence.
    + f_equal.
      - apply IHl; trivial. intros i. apply (Hget (i~0)).
      - apply IHr; trivial. intros i. apply (Hget (i~1)).
Qed.

Fixpoint Psingleton_raw {A} (i : positive) (x : A) : Pmap_raw A :=
  match i with
  | 1 => Pnode Pleaf (Some x) Pleaf
  | i~0 => Pnode (Psingleton_raw i x) None Pleaf
  | i~1 => Pnode Pleaf None (Psingleton_raw i x)
  end.

Lemma Psingleton_raw_ne {A} i (x : A) : Pmap_ne (Psingleton_raw i x).
Proof. induction i; simpl; intuition. Qed.
Local Hint Resolve Psingleton_raw_ne.
Lemma Psingleton_raw_wf {A} i (x : A) : Pmap_wf (Psingleton_raw i x).
Proof. induction i; simpl; intuition. Qed.
Local Hint Resolve Psingleton_raw_wf.

Lemma Plookup_raw_singleton {A} i (x : A) : Psingleton_raw i x !! i = Some x.
Proof. by induction i. Qed.
Lemma Plookup_raw_singleton_ne {A} i j (x : A) :
  i ≠ j → Psingleton_raw i x !! j = None.
Proof. revert j. induction i; intros [?|?|]; simpl; auto. congruence. Qed.

Definition Pnode_canon `(l : Pmap_raw A) (o : option A) (r : Pmap_raw A) :=
  match l, o, r with
  | Pleaf, None, Pleaf => Pleaf
  | _, _, _ => Pnode l o r
  end.

Lemma Pnode_canon_wf `(l : Pmap_raw A) (o : option A) (r : Pmap_raw A) :
  Pmap_wf l → Pmap_wf r → Pmap_wf (Pnode_canon l o r).
Proof. intros H1 H2. destruct H1, o, H2; simpl; intuition. Qed.
Local Hint Resolve Pnode_canon_wf.

Lemma Pnode_canon_lookup_xH `(l : Pmap_raw A) o (r : Pmap_raw A) :
  Pnode_canon l o r !! 1 = o.
Proof. by destruct l,o,r. Qed.
Lemma Pnode_canon_lookup_xO `(l : Pmap_raw A) o (r : Pmap_raw A) i :
  Pnode_canon l o r !! i~0 = l !! i.
Proof. by destruct l,o,r. Qed.
Lemma Pnode_canon_lookup_xI `(l : Pmap_raw A) o (r : Pmap_raw A) i :
  Pnode_canon l o r !! i~1 = r !! i.
Proof. by destruct l,o,r. Qed.
Ltac Pnode_canon_rewrite := repeat (
  rewrite Pnode_canon_lookup_xH ||
  rewrite Pnode_canon_lookup_xO ||
  rewrite Pnode_canon_lookup_xI).

Instance Ppartial_alter_raw {A} : PartialAlter positive A (Pmap_raw A) :=
  fix go f i t {struct t} : Pmap_raw A :=
  match t with
  | Pleaf =>
     match f None with
     | None => Pleaf
     | Some x => Psingleton_raw i x
     end
  | Pnode l o r =>
     match i with
     | 1 => Pnode_canon l (f o) r
     | i~0 => Pnode_canon (@partial_alter _ _ _ go f i l) o r
     | i~1 => Pnode_canon l o (@partial_alter _ _ _ go f i r)
     end
  end.

Lemma Ppartial_alter_raw_wf {A} f i (t : Pmap_raw A) :
  Pmap_wf t → Pmap_wf (partial_alter f i t).
Proof.
  intros twf. revert i. induction twf.
  * unfold partial_alter. simpl. case (f None); intuition.
  * intros [?|?|]; simpl; intuition.
  * intros [?|?|]; simpl; intuition.
Qed.

Instance Ppartial_alter {A} : PartialAlter positive A (Pmap A) := λ f i t,
  dexist (partial_alter f i (`t)) (Ppartial_alter_raw_wf f i _ (proj2_dsig t)).

Lemma Plookup_raw_alter {A} f i (t : Pmap_raw A) :
  partial_alter f i t !! i = f (t !! i).
Proof.
  revert i. induction t.
  * intros i. change (
     match f None with
     | Some x => Psingleton_raw i x
     | None => Pleaf
     end !! i = f None). destruct (f None).
    + intros. apply Plookup_raw_singleton.
    + by destruct i.
  * intros [?|?|]; simpl; by Pnode_canon_rewrite.
Qed.
Lemma Plookup_raw_alter_ne {A} f i j (t : Pmap_raw A) :
  i ≠ j → partial_alter f i t !! j = t !! j.
Proof.
  revert i j. induction t as [|l IHl ? r IHr].
  * intros. change (
     match f None with
     | Some x => Psingleton_raw i x
     | None => Pleaf
     end !! j = None). destruct (f None).
    + intros. by apply Plookup_raw_singleton_ne.
    + done.
  * intros [?|?|] [?|?|]; simpl; Pnode_canon_rewrite; auto; congruence.
Qed.

Instance Pfmap_raw {A B} (f : A → B) : FMapD Pmap_raw f :=
  fix go (t : Pmap_raw A) : Pmap_raw B :=
  let _ : FMapD Pmap_raw f := @go in
  match t with
  | Pleaf => Pleaf
  | Pnode l x r => Pnode (f <$> l) (f <$> x) (f <$> r)
  end.

Lemma Pfmap_raw_ne `(f : A → B) (t : Pmap_raw A) :
  Pmap_ne t → Pmap_ne (fmap f t).
Proof. induction 1; simpl; auto. Qed.
Local Hint Resolve Pfmap_raw_ne.
Lemma Pfmap_raw_wf `(f : A → B) (t : Pmap_raw A) :
  Pmap_wf t → Pmap_wf (fmap f t).
Proof. induction 1; simpl; intuition. Qed.

Global Instance Pfmap {A B} (f : A → B) : FMapD Pmap f := λ t,
  dexist _ (Pfmap_raw_wf f _ (proj2_dsig t)).

Lemma Plookup_raw_fmap `(f : A → B) (t : Pmap_raw A) i :
  fmap f t !! i = fmap f (t !! i).
Proof. revert i. induction t. done. by intros [?|?|]; simpl. Qed.

(** The [finmap_to_list] function is rather inefficient, but since we do not
use it for computation at this moment, we do not care. *)
Fixpoint Pto_list_raw {A} (t : Pmap_raw A) : list (positive * A) :=
  match t with
  | Pleaf => []
  | Pnode l o r =>
     option_case (λ x, [(1,x)]) [] o ++ 
       (fst_map (~0) <$> Pto_list_raw l) ++ 
       (fst_map (~1) <$> Pto_list_raw r)
  end.

Lemma Pto_list_raw_nodup {A} (t : Pmap_raw A) : NoDup (Pto_list_raw t).
Proof.
  induction t as [|? IHl [?|] ? IHr]; simpl.
  * constructor.
  * rewrite NoDup_cons, NoDup_app, !(NoDup_fmap _).
    repeat split; trivial.
    + rewrite elem_of_app, !elem_of_list_fmap.
      intros [[[??] [??]] | [[??] [??]]]; simpl in *; simplify_equality.
    + intro. rewrite !elem_of_list_fmap.
      intros [[??] [??]] [[??] [??]]; simpl in *; simplify_equality.
  * rewrite NoDup_app, !(NoDup_fmap _).
    repeat split; trivial.
    intro. rewrite !elem_of_list_fmap.
    intros [[??] [??]] [[??] [??]]; simpl in *; simplify_equality.
Qed.

Lemma Pelem_of_to_list_raw {A} (t : Pmap_raw A) i x :
  (i,x) ∈ Pto_list_raw t ↔ t !! i = Some x.
Proof.
  split.
  * revert i. induction t as [|? IHl [?|] ? IHr]; intros i; simpl.
    + by rewrite ?elem_of_nil.
    + rewrite elem_of_cons, !elem_of_app, !elem_of_list_fmap.
      intros [? | [[[??] [??]] | [[??] [??]]]]; naive_solver.
    + rewrite !elem_of_app, !elem_of_list_fmap.
      intros [[[??] [??]] | [[??] [??]]]; naive_solver.
  * revert i. induction t as [|? IHl [?|] ? IHr]; simpl.
    + done.
    + intros i. rewrite elem_of_cons, elem_of_app.
      destruct i as [i|i|]; simpl.
      - right. right. rewrite elem_of_list_fmap.
        exists (i,x); simpl; auto.
      - right. left. rewrite elem_of_list_fmap.
        exists (i,x); simpl; auto.
      - left. congruence.
    + intros i. rewrite elem_of_app.
      destruct i as [i|i|]; simpl.
      - right. rewrite elem_of_list_fmap.
        exists (i,x); simpl; auto.
      - left. rewrite elem_of_list_fmap.
        exists (i,x); simpl; auto.
      - done.
Qed.

Global Instance Pto_list {A} : FinMapToList positive A (Pmap A) :=
  λ t, Pto_list_raw (`t).

Fixpoint Pmerge_aux `(f : option A → option B) (t : Pmap_raw A) : Pmap_raw B :=
  match t with
  | Pleaf => Pleaf
  | Pnode l o r => Pnode_canon (Pmerge_aux f l) (f o) (Pmerge_aux f r)
  end.

Lemma Pmerge_aux_wf `(f : option A → option B) (t : Pmap_raw A) :
  Pmap_wf t → Pmap_wf (Pmerge_aux f t).
Proof. induction 1; simpl; auto. Qed.
Local Hint Resolve Pmerge_aux_wf.

Lemma Pmerge_aux_spec `(f : option A → option B) (Hf : f None = None)
    (t : Pmap_raw A) i :
  Pmerge_aux f t !! i = f (t !! i).
Proof.
  revert i. induction t as [| l IHl o r IHr ]; [done |].
  intros [?|?|]; simpl; Pnode_canon_rewrite; auto.
Qed.

Global Instance Pmerge_raw {A} : Merge A (Pmap_raw A) :=
  fix Pmerge_raw f (t1 t2 : Pmap_raw A) : Pmap_raw A :=
  match t1, t2 with
  | Pleaf, t2 => Pmerge_aux (f None) t2
  | t1, Pleaf => Pmerge_aux (flip f None) t1
  | Pnode l1 o1 r1, Pnode l2 o2 r2 =>
     Pnode_canon (@merge _ _ Pmerge_raw f l1 l2)
      (f o1 o2) (@merge _ _ Pmerge_raw f r1 r2)
  end.
Local Arguments Pmerge_aux _ _ _ _ : simpl never.

Lemma Pmerge_wf {A} f (t1 t2 : Pmap_raw A) :
  Pmap_wf t1 → Pmap_wf t2 → Pmap_wf (merge f t1 t2).
Proof. intros t1wf. revert t2. induction t1wf; destruct 1; simpl; auto. Qed.
Global Instance Pmerge {A} : Merge A (Pmap A) := λ f t1 t2,
  dexist (merge f (`t1) (`t2))
    (Pmerge_wf _ _ _ (proj2_dsig t1) (proj2_dsig t2)).

Lemma Pmerge_raw_spec {A} f (Hf : f None None = None) (t1 t2 : Pmap_raw A) i :
  merge f t1 t2 !! i = f (t1 !! i) (t2 !! i).
Proof.
  revert t2 i. induction t1 as [| l1 IHl1 o1 r1 IHr1 ].
  * intros. unfold merge. simpl. by rewrite Pmerge_aux_spec.
  * destruct t2 as [| l2 o2 r2 ].
    + unfold merge, Pmerge_raw. intros. by rewrite Pmerge_aux_spec.
    + intros [?|?|]; simpl; by Pnode_canon_rewrite.
Qed.

Global Instance: FinMap positive Pmap.
Proof.
  split.
  * intros ? [t1?] [t2?]. intros. apply dsig_eq. simpl.
    apply Pmap_wf_eq_get; trivial; by apply (bool_decide_unpack _).
  * by destruct i.
  * intros ?? [??] ?. by apply Plookup_raw_alter.
  * intros ?? [??] ??. by apply Plookup_raw_alter_ne.
  * intros ??? [??]. by apply Plookup_raw_fmap.
  * intros ? [??]. apply Pto_list_raw_nodup.
  * intros ? [??]. apply Pelem_of_to_list_raw.
  * intros ??? [??] [??] ?. by apply Pmerge_raw_spec.
Qed.
