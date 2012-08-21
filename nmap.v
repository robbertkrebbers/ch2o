Require Import pmap.
Require Export prelude fin_maps.

Local Open Scope N_scope.

Record Nmap A := { Nmap_0 : option A; Nmap_pos : Pmap A }.
Arguments Nmap_0 {_} _.
Arguments Nmap_pos {_} _.
Arguments Build_Nmap {_} _ _.

Global Instance Pmap_dec `{∀ x y : A, Decision (x = y)} : ∀ x y : Nmap A, Decision (x = y).
Proof. solve_decision. Defined.
Global Instance Nempty {A} : Empty (Nmap A) := Build_Nmap None ∅.
Global Instance Nlookup: Lookup N Nmap := λ A i t,
  match i with
  | N0 => Nmap_0 t
  | Npos p => Nmap_pos t !! p
  end.
Global Instance Npartial_alter: PartialAlter N Nmap := λ A f i t,
  match i, t with
  | N0, Build_Nmap o t => Build_Nmap (f o) t
  | Npos p, Build_Nmap o t => Build_Nmap o (partial_alter f p t)
  end.
Global Instance Ndom {A} : Dom N (Nmap A) := λ A _ _ _ t,
  match t with
  | Build_Nmap o t => option_case (λ _, {[ 0 ]}) ∅ o ∪ (Pdom_raw Npos (`t))
  end.
Global Instance Nmerge: Merge Nmap := λ A f t1 t2,
  match t1, t2 with
  | Build_Nmap o1 t1, Build_Nmap o2 t2 => Build_Nmap (f o1 o2) (merge f t1 t2)
  end.
Global Instance Nfmap: FMap Nmap := λ A B f t,
  match t with
  | Build_Nmap o t => Build_Nmap (fmap f o) (fmap f t)
  end.

Global Instance: FinMap N Nmap.
Proof.
  split.
  * intros ? [??] [??] H. f_equal.
    + now apply (H 0).
    + apply finmap_eq. intros i. now apply (H (Npos i)).
  * now intros ? [|?].
  * intros ? f [? t] [|i].
    + easy.
    + now apply (lookup_partial_alter f t i).
  * intros ? f [? t] [|i] [|j]; try intuition congruence.
    intros. apply (lookup_partial_alter_ne f t i j). congruence.
  * intros ??? [??] []. easy. apply lookup_fmap.
  * intros ?? ???????? [o t] n; unfold dom, lookup, Ndom, Nlookup; simpl.
    rewrite elem_of_union, Plookup_raw_dom.
    destruct o, n; esimplify_elem_of (simplify_is_Some; eauto).
  * intros ? f ? [o1 t1] [o2 t2] [|?].
    + easy.
    + apply (merge_spec f t1 t2).
Qed.
