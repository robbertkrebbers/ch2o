(* Copyright (c) 2012, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This files extends the implementation of finite over [positive] to finite
maps whose keys range over Coq's data type of binary naturals [N]. *)
Require Import pmap.
Require Export prelude fin_maps.

Local Open Scope N_scope.

Record Nmap A := NMap { Nmap_0 : option A; Nmap_pos : Pmap A }.
Arguments Nmap_0 {_} _.
Arguments Nmap_pos {_} _.
Arguments NMap {_} _ _.

Instance Pmap_dec `{∀ x y : A, Decision (x = y)} :
  ∀ x y : Nmap A, Decision (x = y).
Proof. solve_decision. Defined.

Instance Nempty {A} : Empty (Nmap A) := NMap None ∅.
Instance Nlookup {A} : Lookup N A (Nmap A) := λ i t,
  match i with
  | N0 => Nmap_0 t
  | Npos p => Nmap_pos t !! p
  end.
Instance Npartial_alter {A} : PartialAlter N A (Nmap A) := λ f i t,
  match i, t with
  | N0, NMap o t => NMap (f o) t
  | Npos p, NMap o t => NMap o (partial_alter f p t)
  end.
Instance Nto_list {A} : FinMapToList N A (Nmap A) := λ t,
  match t with
  | NMap o t => option_case (λ x, [(0,x)]) [] o ++
     (fst_map Npos <$> finmap_to_list t)
  end.
Instance Nmerge {A} : Merge A (Nmap A) := λ f t1 t2,
  match t1, t2 with
  | NMap o1 t1, NMap o2 t2 => NMap (f o1 o2) (merge f t1 t2)
  end.
Instance Nfmap: FMap Nmap := λ A B f t,
  match t with
  | NMap o t => NMap (fmap f o) (fmap f t)
  end.

Instance: FinMap N Nmap.
Proof.
  split.
  * intros ? [??] [??] H. f_equal.
    + apply (H 0).
    + apply finmap_eq. intros i. apply (H (Npos i)).
  * by intros ? [|?].
  * intros ? f [? t] [|i]; simpl.
    + done.
    + apply lookup_partial_alter.
  * intros ? f [? t] [|i] [|j]; simpl; try intuition congruence.
    intros. apply lookup_partial_alter_ne. congruence.
  * intros ??? [??] []; simpl. done. apply lookup_fmap.
  * intros ? [[x|] t]; unfold finmap_to_list; simpl.
    + constructor.
      - rewrite elem_of_list_fmap. by intros [[??] [??]].
      - rewrite (NoDup_fmap _). apply finmap_to_list_nodup.
    + rewrite (NoDup_fmap _). apply finmap_to_list_nodup.
  * intros ? t i x. unfold finmap_to_list. split.
    + destruct t as [[y|] t]; simpl.
      - rewrite elem_of_cons, elem_of_list_fmap.
        intros [? | [[??] [??]]]; simplify_equality; simpl; [done |].
        by apply elem_of_finmap_to_list.
      - rewrite elem_of_list_fmap.
        intros [[??] [??]]; simplify_equality; simpl.
        by apply elem_of_finmap_to_list.
    + destruct t as [[y|] t]; simpl.
      - rewrite elem_of_cons, elem_of_list_fmap.
        destruct i as [|i]; simpl; [intuition congruence |].
        intros. right. exists (i, x). by rewrite elem_of_finmap_to_list.
      - rewrite elem_of_list_fmap.
        destruct i as [|i]; simpl; [done |].
        intros. exists (i, x). by rewrite elem_of_finmap_to_list.
  * intros ? f ? [o1 t1] [o2 t2] [|?]; simpl.
    + done.
    + apply (merge_spec f t1 t2).
Qed.
