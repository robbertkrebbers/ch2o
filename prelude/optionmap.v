(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
From stdpp Require Import mapset.
Require Import tactics.

Record optionmap (M : Type → Type) (A : Type) : Type :=
  OptionMap { optionmap_None : option A; optionmap_Some : M A }.
Arguments optionmap_None {_ _} _.
Arguments optionmap_Some {_ _} _.
Arguments OptionMap {_ _} _ _.
#[global] Instance optionmap_eq_dec {M : Type → Type} `{EqDecision A} `{EqDecision (M A)}: 
  EqDecision (optionmap M A).
Proof. solve_decision. Defined.

Section optionmap.
Context `{FinMap K M}.

#[global] Instance optionmap_empty {A} : Empty (optionmap M A) := OptionMap None ∅.
Global Opaque optionmap_empty.
#[global] Instance optionmap_lookup {A} :
    Lookup (option K) A (optionmap M A) := λ i m,
  match i with
  | None => optionmap_None m
  | Some k => optionmap_Some m !! k
  end.
#[global] Instance optionmap_partial_alter {A} :
    PartialAlter (option K) A (optionmap M A) := λ f i m,
  match i, m with
  | None, OptionMap o m => OptionMap (f o) m
  | Some k, OptionMap o m => OptionMap o (partial_alter f k m)
  end.
#[global] Instance optionmap_to_list {A} :
    FinMapToList (option K) A (optionmap M A) := λ m,
  match m with
  | OptionMap o m =>
     (from_option (λ x, [(None,x)]) [] o) ++ (prod_map Some id <$> map_to_list m)
  end.
#[global] Instance optionmap_omap: OMap (optionmap M) := λ A B f m,
  match m with OptionMap o m => OptionMap (o ≫= f) (omap f m) end.
#[global] Instance optionmap_merge: Merge (optionmap M) := λ A B C f m1 m2,
  match m1, m2 with
  | OptionMap o1 m1, OptionMap o2 m2 => OptionMap (diag_None f o1 o2) (merge f m1 m2)
  end.
#[global] Instance optionmap_fmap: FMap (optionmap M) := λ A B f m,
  match m with OptionMap o m => OptionMap (f <$> o) (f <$> m) end.

#[global] Instance: FinMap (option K) (optionmap M).
Proof.
  split.
  * intros ? [??] [??] Hlookup. f_equal; [apply (Hlookup None)|].
    apply map_eq. intros k. apply (Hlookup (Some k)).
  * intros ? [?|]. apply (lookup_empty k). done.
  * intros ? f [? t] [k|]; simpl; [|done]. apply lookup_partial_alter.
  * intros ? f [? t] [k|] [|]; simpl; try intuition congruence.
    intros; apply lookup_partial_alter_ne; congruence.
  * intros ??? [??] []; simpl. apply lookup_fmap. done.
  * intros ? [[x|] m]; unfold map_to_list; simpl.
    + constructor.
      - rewrite elem_of_list_fmap. by intros [[??] [??]].
      - by apply (NoDup_fmap _), NoDup_map_to_list.
    + apply (NoDup_fmap _), NoDup_map_to_list.
  * intros ? m k x. unfold map_to_list. split.
    + destruct m as [[y|] m]; simpl.
      - rewrite elem_of_cons, elem_of_list_fmap.
        intros [? | [[??] [??]]]; simplify_equality'; [done |].
        by apply elem_of_map_to_list.
      - rewrite elem_of_list_fmap; intros [[??] [??]]; simplify_equality'.
        by apply elem_of_map_to_list.
    + destruct m as [[y|] m]; simpl.
      - rewrite elem_of_cons, elem_of_list_fmap.
        destruct k as [k|]; simpl; [|intuition congruence].
        intros. right. exists (k,x). by rewrite elem_of_map_to_list.
      - rewrite elem_of_list_fmap.
        destruct k as [k|]; simpl; [|done].
        intros. exists (k,x). by rewrite elem_of_map_to_list.
  * intros ?? f [??] [?|]; simpl; [|done]; apply (lookup_omap f).
  * intros ??? f [??] [??] [?|]; simpl; [|done]; apply (lookup_merge f). 
Qed.
End optionmap.

(** * Finite sets *)
Notation optionset M := (mapset (optionmap M)).
#[global] Instance optionmap_dom {M : Type → Type} `{∀ A, Empty (M A), Merge M} {A} :
  Dom (optionmap M A) (optionset M) := mapset_dom.
#[global] Instance optionmap_domspec `{FinMap K M} :
  FinMapDom (option K) (optionmap M) (optionset M) := mapset_dom_spec.
