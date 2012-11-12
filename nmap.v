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
Instance Nlookup {A} : Lookup N (Nmap A) A := λ i t,
  match i with
  | N0 => Nmap_0 t
  | Npos p => Nmap_pos t !! p
  end.
Instance Npartial_alter {A} : PartialAlter N (Nmap A) A := λ f i t,
  match i, t with
  | N0, NMap o t => NMap (f o) t
  | Npos p, NMap o t => NMap o (partial_alter f p t)
  end.
Instance Ndom {A} : Dom N (Nmap A) := λ C _ _ _ t,
  match t with
  | NMap o t => option_case (λ _, {[ 0 ]}) ∅ o ∪ (Pdom_raw Npos (`t))
  end.
Instance Nmerge: Merge Nmap := λ A f t1 t2,
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
  * intros ?? ??????? [o t] n; simpl.
    rewrite elem_of_union, Plookup_raw_dom.
    destruct o, n; esolve_elem_of (inv_is_Some; eauto).
  * intros ? f ? [o1 t1] [o2 t2] [|?]; simpl.
    + done.
    + apply (merge_spec f t1 t2).
Qed.
