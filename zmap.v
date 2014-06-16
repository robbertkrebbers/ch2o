(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This files extends the implementation of finite over [positive] to finite
maps whose keys range over Coq's data type of binary naturals [Z]. *)
Require Import pmap mapset.
Require Export prelude fin_maps.
Local Open Scope Z_scope.

Record Zmap A :=
  ZMap { Zmap_0 : option A; Zmap_pos : Pmap A; Zmap_neg : Pmap A }.
Arguments Zmap_0 {_} _.
Arguments Zmap_pos {_} _.
Arguments Zmap_neg {_} _.
Arguments ZMap {_} _ _ _.

Instance Zmap_eq_dec `{∀ x y : A, Decision (x = y)} (t1 t2 : Zmap A) :
  Decision (t1 = t2).
Proof.
 refine
  match t1, t2 with
  | ZMap x t1 t1', ZMap y t2 t2' =>
     cast_if_and3 (decide (x = y)) (decide (t1 = t2)) (decide (t1' = t2'))
  end; abstract congruence.
Defined.
Instance Zempty {A} : Empty (Zmap A) := ZMap None ∅ ∅.
Instance Zlookup {A} : Lookup Z A (Zmap A) := λ i t,
  match i with
  | Z0 => Zmap_0 t | Zpos p => Zmap_pos t !! p | Zneg p => Zmap_neg t !! p
  end.
Instance Zpartial_alter {A} : PartialAlter Z A (Zmap A) := λ f i t,
  match i, t with
  | Z0, ZMap o t t' => ZMap (f o) t t'
  | Zpos p, ZMap o t t' => ZMap o (partial_alter f p t) t'
  | Zneg p, ZMap o t t' => ZMap o t (partial_alter f p t')
  end.
Instance Zto_list {A} : FinMapToList Z A (Zmap A) := λ t,
  match t with
  | ZMap o t t' => default [] o (λ x, [(0,x)]) ++
     (prod_map Zpos id <$> map_to_list t) ++
     (prod_map Zneg id <$> map_to_list t')
  end.
Instance Zomap: OMap Zmap := λ A B f t,
  match t with ZMap o t t' => ZMap (o ≫= f) (omap f t) (omap f t') end.
Instance Zmerge: Merge Zmap := λ A B C f t1 t2,
  match t1, t2 with
  | ZMap o1 t1 t1', ZMap o2 t2 t2' =>
     ZMap (f o1 o2) (merge f t1 t2) (merge f t1' t2')
  end.
Instance Nfmap: FMap Zmap := λ A B f t,
  match t with ZMap o t t' => ZMap (f <$> o) (f <$> t) (f <$> t') end.

Instance: FinMap Z Zmap.
Proof.
  split.
  * intros ? [??] [??] H. f_equal.
    + apply (H 0).
    + apply map_eq. intros i. apply (H (Zpos i)).
    + apply map_eq. intros i. apply (H (Zneg i)).
  * by intros ? [].
  * intros ? f [] [|?|?]; simpl; [done| |]; apply lookup_partial_alter.
  * intros ? f [] [|?|?] [|?|?]; simpl; intuition congruence ||
      intros; apply lookup_partial_alter_ne; congruence.
  * intros ??? [??] []; simpl; [done| |]; apply lookup_fmap.
  * intros ? [o t t']; unfold map_to_list; simpl.
    assert (NoDup ((prod_map Z.pos id <$> map_to_list t) ++
      prod_map Z.neg id <$> map_to_list t')).
    { apply NoDup_app; split_ands.
      - apply (NoDup_fmap_2 _), NoDup_map_to_list.
      - intro. rewrite !elem_of_list_fmap. naive_solver.
      - apply (NoDup_fmap_2 _), NoDup_map_to_list. }
    destruct o; simpl; auto. constructor; auto.
    rewrite elem_of_app, !elem_of_list_fmap. naive_solver.
  * intros ? t i x. unfold map_to_list. split.
    + destruct t as [[y|] t t']; simpl.
      - rewrite elem_of_cons, elem_of_app, !elem_of_list_fmap.
        intros [?|[[[??][??]]|[[??][??]]]]; simplify_equality; simpl; [done| |];
          by apply elem_of_map_to_list.
      - rewrite elem_of_app, !elem_of_list_fmap. intros [[[??][??]]|[[??][??]]];
          simplify_equality'; by apply elem_of_map_to_list.
    + destruct t as [[y|] t t']; simpl.
      - rewrite elem_of_cons, elem_of_app, !elem_of_list_fmap.
        destruct i as [|i|i]; simpl; [intuition congruence| |].
        { right; left. exists (i, x). by rewrite elem_of_map_to_list. }
        right; right. exists (i, x). by rewrite elem_of_map_to_list.
      - rewrite elem_of_app, !elem_of_list_fmap.
        destruct i as [|i|i]; simpl; [done| |].
        { left; exists (i, x). by rewrite elem_of_map_to_list. }
        right; exists (i, x). by rewrite elem_of_map_to_list.
  * intros ?? f [??] [|?|?]; simpl; [done| |]; apply (lookup_omap f).
  * intros ??? f ? [??] [??] [|?|?]; simpl; [done| |]; apply (lookup_merge f).
Qed.

(** * Finite sets *)
(** We construct sets of [Z]s satisfying extensional equality. *)
Notation Zset := (mapset (Zmap unit)).
Instance Zmap_dom {A} : Dom (Zmap A) Zset := mapset_dom.
Instance: FinMapDom Z Zmap Zset := mapset_dom_spec.
