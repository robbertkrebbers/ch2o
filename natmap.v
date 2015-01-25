(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This files implements a type [natmap A] of finite maps whose keys range
over Coq's data type of unary natural numbers [nat]. The implementation equips
a list with a proof of canonicity. *)
Require Import fin_maps mapset.

Notation natmap_raw A := (list (option A)).
Definition natmap_wf {A} (l : natmap_raw A) :=
  match last l with None => True | Some x => is_Some x end.
Instance natmap_wf_pi {A} (l : natmap_raw A) : ProofIrrel (natmap_wf l).
Proof. unfold natmap_wf. case_match; apply _. Qed.

Lemma natmap_wf_inv {A} (o : option A) (l : natmap_raw A) :
  natmap_wf (o :: l) → natmap_wf l.
Proof. by destruct l. Qed.
Lemma natmap_wf_lookup {A} (l : natmap_raw A) :
  natmap_wf l → l ≠ [] → ∃ i x, mjoin (l !! i) = Some x.
Proof.
  intros Hwf Hl. induction l as [|[x|] l IH]; simpl; [done| |].
  { exists 0. simpl. eauto. }
  destruct IH as (i&x&?); eauto using natmap_wf_inv; [|by exists (S i) x].
  intros ->. by destruct Hwf.
Qed.

Record natmap (A : Type) : Type := NatMap {
  natmap_car : natmap_raw A;
  natmap_prf : natmap_wf natmap_car
}.
Arguments NatMap {_} _ _.
Arguments natmap_car {_} _.
Arguments natmap_prf {_} _.
Lemma natmap_eq {A} (m1 m2 : natmap A) :
  m1 = m2 ↔ natmap_car m1 = natmap_car m2.
Proof.
  split; [by intros ->|intros]; destruct m1 as [t1 ?], m2 as [t2 ?].
  simplify_equality'; f_equal; apply proof_irrel.
Qed.
Global Instance natmap_eq_dec `{∀ x y : A, Decision (x = y)}
    (m1 m2 : natmap A) : Decision (m1 = m2) :=
  match decide (natmap_car m1 = natmap_car m2) with
  | left H => left (proj2 (natmap_eq m1 m2) H)
  | right H => right (H ∘ proj1 (natmap_eq m1 m2))
  end.

Instance natmap_empty {A} : Empty (natmap A) := NatMap [] I.
Instance natmap_lookup {A} : Lookup nat A (natmap A) := λ i m,
  let (l,_) := m in mjoin (l !! i).

Fixpoint natmap_singleton_raw {A} (i : nat) (x : A) : natmap_raw A :=
  match i with 0 => [Some x]| S i => None :: natmap_singleton_raw i x end.
Lemma natmap_singleton_wf {A} (i : nat) (x : A) :
  natmap_wf (natmap_singleton_raw i x).
Proof. unfold natmap_wf. induction i as [|[]]; simplify_equality'; eauto. Qed.
Lemma natmap_lookup_singleton_raw {A} (i : nat) (x : A) :
  mjoin (natmap_singleton_raw i x !! i) = Some x.
Proof. induction i; simpl; auto. Qed.
Lemma natmap_lookup_singleton_raw_ne {A} (i j : nat) (x : A) :
  i ≠ j → mjoin (natmap_singleton_raw i x !! j) = None.
Proof. revert j; induction i; intros [|?]; simpl; auto with congruence. Qed.
Hint Rewrite @natmap_lookup_singleton_raw : natmap.

Definition natmap_cons_canon {A} (o : option A) (l : natmap_raw A) :=
  match o, l with None, [] => [] | _, _ => o :: l end.
Lemma natmap_cons_canon_wf {A} (o : option A) (l : natmap_raw A) :
  natmap_wf l → natmap_wf (natmap_cons_canon o l).
Proof. unfold natmap_wf, last. destruct o, l; simpl; eauto. Qed.
Lemma natmap_cons_canon_O {A} (o : option A) (l : natmap_raw A) :
  mjoin (natmap_cons_canon o l !! 0) = o.
Proof. by destruct o, l. Qed.
Lemma natmap_cons_canon_S {A} (o : option A) (l : natmap_raw A) i :
  natmap_cons_canon o l !! S i = l !! i.
Proof. by destruct o, l. Qed.
Hint Rewrite @natmap_cons_canon_O @natmap_cons_canon_S : natmap.

Definition natmap_alter_raw {A} (f : option A → option A) :
    nat → natmap_raw A → natmap_raw A :=
  fix go i l {struct l} :=
  match l with
  | [] =>
     match f None with
     | Some x => natmap_singleton_raw i x | None => []
     end
  | o :: l =>
     match i with
     | 0 => natmap_cons_canon (f o) l | S i => natmap_cons_canon o (go i l)
     end
  end.
Lemma natmap_alter_wf {A} (f : option A → option A) i l :
  natmap_wf l → natmap_wf (natmap_alter_raw f i l).
Proof.
  revert i. induction l; [intro | intros [|?]]; simpl; repeat case_match;
    eauto using natmap_singleton_wf, natmap_cons_canon_wf, natmap_wf_inv.
Qed.
Instance natmap_alter {A} : PartialAlter nat A (natmap A) := λ f i m,
  let (l,Hl) := m in NatMap _ (natmap_alter_wf f i l Hl).
Lemma natmap_lookup_alter_raw {A} (f : option A → option A) i l :
  mjoin (natmap_alter_raw f i l !! i) = f (mjoin (l !! i)).
Proof.
  revert i. induction l; intros [|?]; simpl; repeat case_match; simpl;
    autorewrite with natmap; auto.
Qed.
Lemma natmap_lookup_alter_raw_ne {A} (f : option A → option A) i j l :
  i ≠ j → mjoin (natmap_alter_raw f i l !! j) = mjoin (l !! j).
Proof.
  revert i j. induction l; intros [|?] [|?] ?; simpl;
    repeat case_match; simpl; autorewrite with natmap; auto with congruence.
  rewrite natmap_lookup_singleton_raw_ne; congruence.
Qed.

Definition natmap_omap_raw {A B} (f : A → option B) :
    natmap_raw A → natmap_raw B :=
  fix go l :=
  match l with [] => [] | o :: l => natmap_cons_canon (o ≫= f) (go l) end.
Lemma natmap_omap_raw_wf {A B} (f : A → option B) l :
  natmap_wf l → natmap_wf (natmap_omap_raw f l).
Proof. induction l; simpl; eauto using natmap_cons_canon_wf, natmap_wf_inv. Qed.
Lemma natmap_lookup_omap_raw {A B} (f : A → option B) l i :
  mjoin (natmap_omap_raw f l !! i) = mjoin (l !! i) ≫= f.
Proof.
  revert i. induction l; intros [|?]; simpl; autorewrite with natmap; auto.
Qed.
Hint Rewrite @natmap_lookup_omap_raw : natmap.
Global Instance natmap_omap: OMap natmap := λ A B f m,
  let (l,Hl) := m in NatMap _ (natmap_omap_raw_wf f _ Hl).

Definition natmap_merge_raw {A B C} (f : option A → option B → option C) :
    natmap_raw A → natmap_raw B → natmap_raw C :=
  fix go l1 l2 :=
  match l1, l2 with
  | [], l2 => natmap_omap_raw (f None ∘ Some) l2
  | l1, [] => natmap_omap_raw (flip f None ∘ Some) l1
  | o1 :: l1, o2 :: l2 => natmap_cons_canon (f o1 o2) (go l1 l2)
  end.
Lemma natmap_merge_wf {A B C} (f : option A → option B → option C) l1 l2 :
  natmap_wf l1 → natmap_wf l2 → natmap_wf (natmap_merge_raw f l1 l2).
Proof.
  revert l2. induction l1; intros [|??]; simpl;
    eauto using natmap_omap_raw_wf, natmap_cons_canon_wf, natmap_wf_inv.
Qed.
Lemma natmap_lookup_merge_raw {A B C} (f : option A → option B → option C)
    l1 l2 i : f None None = None →
  mjoin (natmap_merge_raw f l1 l2 !! i) = f (mjoin (l1 !! i)) (mjoin (l2 !! i)).
Proof.
  intros. revert i l2. induction l1; intros [|?] [|??]; simpl;
    autorewrite with natmap; auto;
    match goal with |- context [?o ≫= _] => by destruct o end.
Qed.
Instance natmap_merge: Merge natmap := λ A B C f m1 m2,
  let (l1, Hl1) := m1 in let (l2, Hl2) := m2 in
  NatMap (natmap_merge_raw f l1 l2) (natmap_merge_wf _ _ _ Hl1 Hl2).

Fixpoint natmap_to_list_raw {A} (i : nat) (l : natmap_raw A) : list (nat * A) :=
  match l with
  | [] => []
  | None :: l => natmap_to_list_raw (S i) l
  | Some x :: l => (i,x) :: natmap_to_list_raw (S i) l
  end.
Lemma natmap_elem_of_to_list_raw_aux {A} j (l : natmap_raw A) i x :
  (i,x) ∈ natmap_to_list_raw j l ↔ ∃ i', i = i' + j ∧ mjoin (l !! i') = Some x.
Proof.
  split.
  * revert j. induction l as [|[y|] l IH]; intros j; simpl.
    + by rewrite elem_of_nil.
    + rewrite elem_of_cons. intros [?|?]; simplify_equality.
      - by exists 0.
      - destruct (IH (S j)) as (i'&?&?); auto.
        exists (S i'); simpl; auto with lia.
    + intros. destruct (IH (S j)) as (i'&?&?); auto.
      exists (S i'); simpl; auto with lia.
  * intros (i'&?&Hi'). subst. revert i' j Hi'.
    induction l as [|[y|] l IH]; intros i j ?; simpl.
    + done.
    + destruct i as [|i]; simplify_equality'; [left|].
      right. rewrite <-Nat.add_succ_r. by apply (IH i (S j)).
    + destruct i as [|i]; simplify_equality'.
      rewrite <-Nat.add_succ_r. by apply (IH i (S j)).
Qed.
Lemma natmap_elem_of_to_list_raw {A} (l : natmap_raw A) i x :
  (i,x) ∈ natmap_to_list_raw 0 l ↔ mjoin (l !! i) = Some x.
Proof.
  rewrite natmap_elem_of_to_list_raw_aux. setoid_rewrite Nat.add_0_r.
  naive_solver.
Qed.
Lemma natmap_to_list_raw_nodup {A} i (l : natmap_raw A) :
  NoDup (natmap_to_list_raw i l).
Proof.
  revert i. induction l as [|[?|] ? IH]; simpl; try constructor; auto.
  rewrite natmap_elem_of_to_list_raw_aux. intros (?&?&?). lia.
Qed.
Instance natmap_to_list {A} : FinMapToList nat A (natmap A) := λ m,
  let (l,_) := m in natmap_to_list_raw 0 l.

Definition natmap_map_raw {A B} (f : A → B) : natmap_raw A → natmap_raw B :=
  fmap (fmap f).
Lemma natmap_map_wf {A B} (f : A → B) l :
  natmap_wf l → natmap_wf (natmap_map_raw f l).
Proof.
  unfold natmap_map_raw, natmap_wf. rewrite fmap_last.
  destruct (last l). by apply fmap_is_Some. done.
Qed.
Lemma natmap_lookup_map_raw {A B} (f : A → B) i l :
  mjoin (natmap_map_raw f l !! i) = f <$> mjoin (l !! i).
Proof.
  unfold natmap_map_raw. rewrite list_lookup_fmap. by destruct (l !! i).
Qed.
Instance natmap_map: FMap natmap := λ A B f m,
  let (l,Hl) := m in NatMap (natmap_map_raw f l) (natmap_map_wf _ _ Hl).

Instance: FinMap nat natmap.
Proof.
  split.
  * unfold lookup, natmap_lookup. intros A [l1 Hl1] [l2 Hl2] E.
    apply natmap_eq. revert l2 Hl1 Hl2 E. simpl.
    induction l1 as [|[x|] l1 IH]; intros [|[y|] l2] Hl1 Hl2 E; simpl in *.
    + done.
    + by specialize (E 0).
    + destruct (natmap_wf_lookup (None :: l2)) as (i&?&?); auto with congruence.
    + by specialize (E 0).
    + f_equal. apply (E 0). apply IH; eauto using natmap_wf_inv.
      intros i. apply (E (S i)).
    + by specialize (E 0).
    + destruct (natmap_wf_lookup (None :: l1)) as (i&?&?); auto with congruence.
    + by specialize (E 0).
    + f_equal. apply IH; eauto using natmap_wf_inv. intros i. apply (E (S i)).
  * done.
  * intros ?? [??] ?. apply natmap_lookup_alter_raw.
  * intros ?? [??] ??. apply natmap_lookup_alter_raw_ne.
  * intros ??? [??] ?. apply natmap_lookup_map_raw.
  * intros ? [??]. by apply natmap_to_list_raw_nodup.
  * intros ? [??] ??. by apply natmap_elem_of_to_list_raw.
  * intros ??? [??] ?. by apply natmap_lookup_omap_raw.
  * intros ????? [??] [??] ?. by apply natmap_lookup_merge_raw.
Qed.

Fixpoint strip_Nones {A} (l : list (option A)) : list (option A) :=
  match l with None :: l => strip_Nones l | _ => l end.

Lemma list_to_natmap_wf {A} (l : list (option A)) :
  natmap_wf (reverse (strip_Nones (reverse l))).
Proof.
  unfold natmap_wf. rewrite last_reverse.
  induction (reverse l) as [|[]]; simpl; eauto.
Qed.
Definition list_to_natmap {A} (l : list (option A)) : natmap A :=
  NatMap (reverse (strip_Nones (reverse l))) (list_to_natmap_wf l).
Lemma list_to_natmap_spec {A} (l : list (option A)) i :
  list_to_natmap l !! i = mjoin (l !! i).
Proof.
  unfold lookup at 1, natmap_lookup, list_to_natmap; simpl.
  rewrite <-(reverse_involutive l) at 2. revert i.
  induction (reverse l) as [|[x|] l' IH]; intros i; simpl; auto.
  rewrite reverse_cons, IH. clear IH. revert i.
  induction (reverse l'); intros [|?]; simpl; auto.
Qed.

(** Finally, we can construct sets of [nat]s satisfying extensional equality. *)
Notation natset := (mapset (natmap unit)).
Instance natmap_dom {A} : Dom (natmap A) natset := mapset_dom.
Instance: FinMapDom nat natmap natset := mapset_dom_spec.

(* Fixpoint avoids this definition from being unfolded *)
Fixpoint of_bools (βs : list bool) : natset :=
  let f (β : bool) := if β then Some () else None in
  Mapset $ list_to_natmap $ f <$> βs.
Definition to_bools (sz : nat) (X : natset) : list bool :=
  let f (mu : option ()) := match mu with Some _ => true | None => false end in
  resize sz false $ f <$> natmap_car (mapset_car X).

Lemma of_bools_unfold βs :
  let f (β : bool) := if β then Some () else None in
  of_bools βs = Mapset $ list_to_natmap $ f <$> βs.
Proof. by destruct βs. Qed.
Lemma elem_of_of_bools βs i : i ∈ of_bools βs ↔ βs !! i = Some true.
Proof.
  rewrite of_bools_unfold; unfold elem_of, mapset_elem_of; simpl.
  rewrite list_to_natmap_spec, list_lookup_fmap.
  destruct (βs !! i) as [[]|]; compute; intuition congruence.
Qed.
Lemma of_bools_union βs1 βs2 :
  length βs1 = length βs2 →
  of_bools (βs1 ||* βs2) = of_bools βs1 ∪ of_bools βs2.
Proof.
  rewrite <-Forall2_same_length; intros Hβs.
  apply elem_of_equiv_L. intros i. rewrite elem_of_union, !elem_of_of_bools.
  revert i. induction Hβs as [|[] []]; intros [|?]; naive_solver.
Qed.
Lemma to_bools_length (X : natset) sz : length (to_bools sz X) = sz.
Proof. apply resize_length. Qed.
Lemma lookup_to_bools_ge sz X i : sz ≤ i → to_bools sz X !! i = None.
Proof. by apply lookup_resize_old. Qed.
Lemma lookup_to_bools sz X i β :
  i < sz → to_bools sz X !! i = Some β ↔ (i ∈ X ↔ β = true).
Proof.
  unfold to_bools, elem_of, mapset_elem_of, lookup at 2, natmap_lookup; simpl.
  intros. destruct (mapset_car X) as [l ?]; simpl.
  destruct (l !! i) as [mu|] eqn:Hmu; simpl.
  { rewrite lookup_resize, list_lookup_fmap, Hmu
      by (rewrite ?fmap_length; eauto using lookup_lt_Some).
    destruct mu as [[]|], β; simpl; intuition congruence. }
  rewrite lookup_resize_new by (rewrite ?fmap_length;
    eauto using lookup_ge_None_1); destruct β; intuition congruence.
Qed.
Lemma lookup_to_bools_true sz X i :
  i < sz → to_bools sz X !! i = Some true ↔ i ∈ X.
Proof. intros. rewrite lookup_to_bools by done. intuition. Qed.
Lemma lookup_to_bools_false sz X i :
  i < sz → to_bools sz X !! i = Some false ↔ i ∉ X.
Proof. intros. rewrite lookup_to_bools by done. naive_solver. Qed.
Lemma to_bools_union sz X1 X2 :
  to_bools sz (X1 ∪ X2) = to_bools sz X1 ||* to_bools sz X2.
Proof.
  apply list_eq; intros i; rewrite lookup_zip_with.
  destruct (decide (i < sz)); [|by rewrite !lookup_to_bools_ge by lia].
  apply option_eq; intros β.
  rewrite lookup_to_bools, elem_of_union by done; intros.
  destruct (decide (i ∈ X1)), (decide (i ∈ X2)); repeat first
    [ rewrite (λ X H, proj2 (lookup_to_bools_true sz X i H)) by done
    | rewrite (λ X H, proj2 (lookup_to_bools_false sz X i H)) by done];
    destruct β; naive_solver.
Qed.
Lemma to_of_bools βs sz : to_bools sz (of_bools βs) = resize sz false βs.
Proof.
  apply list_eq; intros i. destruct (decide (i < sz));
    [|by rewrite lookup_to_bools_ge, lookup_resize_old by lia].
  apply option_eq; intros β.
  rewrite lookup_to_bools, elem_of_of_bools by done.
  destruct (decide (i < length βs)).
  { rewrite lookup_resize by done.
    destruct (lookup_lt_is_Some_2 βs i) as [[]]; destruct β; naive_solver. }
  rewrite lookup_resize_new, lookup_ge_None_2 by lia. destruct β; naive_solver.
Qed.

(** A [natmap A] forms a stack with elements of type [A] and possible holes *)
Definition natmap_push {A} (o : option A) (m : natmap A) : natmap A :=
  let (l,Hl) := m in NatMap _ (natmap_cons_canon_wf o l Hl).

Definition natmap_pop_raw {A} (l : natmap_raw A) : natmap_raw A := tail l.
Lemma natmap_pop_wf {A} (l : natmap_raw A) :
  natmap_wf l → natmap_wf (natmap_pop_raw l).
Proof. destruct l; simpl; eauto using natmap_wf_inv. Qed.
Definition natmap_pop {A} (m : natmap A) : natmap A :=
  let (l,Hl) := m in NatMap _ (natmap_pop_wf _ Hl).

Lemma lookup_natmap_push_O {A} o (m : natmap A) : natmap_push o m !! 0 = o.
Proof. by destruct o, m as [[|??]]. Qed.
Lemma lookup_natmap_push_S {A} o (m : natmap A) i :
  natmap_push o m !! S i = m !! i.
Proof. by destruct o, m as [[|??]]. Qed.
Lemma lookup_natmap_pop {A} (m : natmap A) i : natmap_pop m !! i = m !! S i.
Proof. by destruct m as [[|??]]. Qed.
Lemma natmap_push_pop {A} (m : natmap A) :
  natmap_push (m !! 0) (natmap_pop m) = m.
Proof.
  apply map_eq. intros i. destruct i.
  * by rewrite lookup_natmap_push_O.
  * by rewrite lookup_natmap_push_S, lookup_natmap_pop.
Qed.
Lemma natmap_pop_push {A} o (m : natmap A) : natmap_pop (natmap_push o m) = m.
Proof. apply natmap_eq. by destruct o, m as [[|??]]. Qed.
