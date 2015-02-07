(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This files implements an efficient implementation of finite maps whose keys
range over Coq's data type of strings [string]. The implementation uses radix-2
search trees (uncompressed Patricia trees) as implemented in the file [pmap]
and guarantees logarithmic-time operations. *)
Require Export fin_maps pretty.
Require Import Ascii String list pmap mapset.

(** * Encoding and decoding *)
(** In order to reuse or existing implementation of radix-2 search trees over
positive binary naturals [positive], we define an injection [string_to_pos]
from [string] into [positive]. *)
Fixpoint digits_to_pos (βs : list bool) : positive :=
  match βs with
  | [] => xH
  | false :: βs => (digits_to_pos βs)~0
  | true :: βs => (digits_to_pos βs)~1
  end%positive.
Definition ascii_to_digits (a : Ascii.ascii) : list bool :=
  match a with
  | Ascii.Ascii β1 β2 β3 β4 β5 β6 β7 β8 => [β1;β2;β3;β4;β5;β6;β7;β8]
  end.
Fixpoint string_to_pos (s : string) : positive :=
  match s with
  | EmptyString => xH
  | String a s => string_to_pos s ++ digits_to_pos (ascii_to_digits a)
  end%positive.
Fixpoint digits_of_pos (p : positive) : list bool :=
  match p with
  | xH => []
  | p~0 => false :: digits_of_pos p
  | p~1 => true :: digits_of_pos p
  end%positive.
Fixpoint ascii_of_digits (βs : list bool) : ascii :=
  match βs with
  | [] => zero
  | β :: βs => Ascii.shift β (ascii_of_digits βs)
  end.
Fixpoint string_of_digits (βs : list bool) : string :=
  match βs with
  | β1 :: β2 :: β3 :: β4 :: β5 :: β6 :: β7 :: β8 :: βs =>
     String (ascii_of_digits [β1;β2;β3;β4;β5;β6;β7;β8]) (string_of_digits βs)
  | _ => EmptyString
  end.
Definition string_of_pos (p : positive) : string :=
  string_of_digits (digits_of_pos p).
Lemma string_of_to_pos s : string_of_pos (string_to_pos s) = s.
Proof.
  unfold string_of_pos.
  by induction s as [|[[] [] [] [] [] [] [] []]]; simpl; f_equal.
Qed.
Instance: Injective (=) (=) string_to_pos.
Proof.
  intros s1 s2 Hs. by rewrite <-(string_of_to_pos s1), Hs, string_of_to_pos.
Qed.

(** * The data structure *)
(** We pack a [Pmap] together with a proof that ensures that all keys correspond
to actual strings. *)
Definition stringmap_wf {A} : Pmap A → Prop :=
  map_Forall (λ p _, string_to_pos (string_of_pos p) = p).
Record stringmap A := StringMap {
  stringmap_car : Pmap A;
  stringmap_prf : bool_decide (stringmap_wf stringmap_car)
}.
Arguments StringMap {_} _ _.
Arguments stringmap_car {_} _.
Lemma stringmap_eq {A} (m1 m2 : stringmap A) :
  m1 = m2 ↔ stringmap_car m1 = stringmap_car m2.
Proof.
  split; [by intros ->|intros]. destruct m1, m2; simplify_equality'.
  f_equal; apply proof_irrel.
Qed.
Instance stringmap_eq_eq {A} `{∀ x y : A, Decision (x = y)}
  (m1 m2 : stringmap A) : Decision (m1 = m2).
Proof.
 refine (cast_if (decide (stringmap_car m1 = stringmap_car m2)));
  abstract (by rewrite stringmap_eq).
Defined.

(** * Operations on the data structure *)
Instance stringmap_lookup {A} : Lookup string A (stringmap A) := λ s m,
  let (m,_) := m in m !! string_to_pos s.
Instance stringmap_empty {A} : Empty (stringmap A) := StringMap ∅ I.
Lemma stringmap_partial_alter_wf {A} (f : option A → option A) m s :
  stringmap_wf m → stringmap_wf (partial_alter f (string_to_pos s) m).
Proof.
  intros Hm p x. destruct (decide (string_to_pos s = p)) as [<-|?].
  * by rewrite string_of_to_pos.
  * rewrite lookup_partial_alter_ne by done. by apply Hm.
Qed.
Instance stringmap_partial_alter {A} :
    PartialAlter string A (stringmap A) := λ f s m,
  let (m,Hm) := m in StringMap (partial_alter f (string_to_pos s) m)
    (bool_decide_pack _ (stringmap_partial_alter_wf f m s
    (bool_decide_unpack _ Hm))).
Lemma stringmap_fmap_wf {A B} (f : A → B) m :
  stringmap_wf m → stringmap_wf (f <$> m).
Proof. intros ? p x. rewrite lookup_fmap, fmap_Some; intros (?&?&?); eauto. Qed.
Instance stringmap_fmap : FMap stringmap := λ A B f m,
  let (m,Hm) := m in StringMap (f <$> m)
    (bool_decide_pack _ (stringmap_fmap_wf f m (bool_decide_unpack _ Hm))).
Lemma stringmap_omap_wf {A B} (f : A → option B) m :
  stringmap_wf m → stringmap_wf (omap f m).
Proof. intros ? p x; rewrite lookup_omap, bind_Some; intros (?&?&?); eauto. Qed.
Instance stringmap_omap : OMap stringmap := λ A B f m,
  let (m,Hm) := m in StringMap (omap f m)
    (bool_decide_pack _ (stringmap_omap_wf f m (bool_decide_unpack _ Hm))).
Lemma stringmap_merge_wf {A B C} (f : option A → option B → option C) m1 m2 :
  let f' o1 o2 := match o1, o2 with None, None => None | _, _ => f o1 o2 end in
  stringmap_wf m1 → stringmap_wf m2 → stringmap_wf (merge f' m1 m2).
Proof.
  intros f' Hm1 Hm2 p z; rewrite lookup_merge by done; intros.
  destruct (m1 !! _) eqn:?, (m2 !! _) eqn:?; naive_solver.
Qed.
Instance stringmap_merge : Merge stringmap := λ A B C f m1 m2,
  let (m1,Hm1) := m1 in let (m2,Hm2) := m2 in
  let f' o1 o2 := match o1, o2 with None, None => None | _, _ => f o1 o2 end in
  StringMap (merge f' m1 m2) (bool_decide_pack _ (stringmap_merge_wf f _ _
    (bool_decide_unpack _ Hm1) (bool_decide_unpack _ Hm2))).
Instance stringmap_to_list {A} : FinMapToList string A (stringmap A) := λ m,
  let (m,_) := m in prod_map string_of_pos id <$> map_to_list m.

(** * Instantiation of the finite map interface *)
Instance: FinMap string stringmap.
Proof.
  split.
  * unfold lookup; intros A [m1 Hm1] [m2 Hm2] H.
    apply stringmap_eq, map_eq; intros i; simpl in *.
    apply bool_decide_unpack in Hm1; apply bool_decide_unpack in Hm2.
    apply option_eq; intros x; split; intros Hi.
    + generalize Hi. rewrite <-(Hm1 i x) by done; eauto using option_eq_1.
    + generalize Hi. rewrite <-(Hm2 i x) by done; eauto using option_eq_1.
  * done.
  * intros A f [m Hm] s; apply (lookup_partial_alter f m).
  * intros A f [m Hm] s s' Hs; apply (lookup_partial_alter_ne f m).
    by contradict Hs; apply (injective string_to_pos).
  * intros A B f [m Hm] s; apply (lookup_fmap f m).
  * intros A [m Hm]; unfold map_to_list; simpl.
    apply bool_decide_unpack, map_Forall_to_list in Hm; revert Hm.
    induction (NoDup_map_to_list m) as [|[p x] l Hpx];
      inversion 1 as [|??? Hm']; simplify_equality'; constructor; eauto.
    rewrite elem_of_list_fmap; intros ([p' x']&?&?); simplify_equality'.
    cut (string_to_pos (string_of_pos p') = p'); [congruence|].
    rewrite Forall_forall in Hm'. eapply (Hm' (_,_)); eauto.
  * intros A [m Hm] s x; unfold map_to_list, lookup; simpl.
    apply bool_decide_unpack in Hm; rewrite elem_of_list_fmap; split.
    + intros ([p' x']&?&Hp'); simplify_equality'.
      apply elem_of_map_to_list in Hp'. by rewrite (Hm p' x').
    + intros. exists (string_to_pos s,x); simpl.
      by rewrite elem_of_map_to_list, string_of_to_pos.
  * intros A B f [m Hm] s; apply (lookup_omap f m).
  * intros A B C f ? [m1 Hm1] [m2 Hm2] s; unfold merge, lookup; simpl.
    set (f' o1 o2 := match o1, o2 with None, None => None | _, _ => f o1 o2 end).
    rewrite lookup_merge by done. by destruct (m1 !! _), (m2 !! _).
Qed.

(** * Finite sets *)
(** We construct sets of [strings]s satisfying extensional equality. *)
Notation stringset := (mapset (stringmap unit)).
Instance stringmap_dom {A} : Dom (stringmap A) stringset := mapset_dom.
Instance: FinMapDom positive Pmap Pset := mapset_dom_spec.

(** * Generating fresh strings *)
Local Open Scope N_scope.
Let R {A} (s : string) (m : stringmap A) (n1 n2 : N) :=
  n2 < n1 ∧ is_Some (m !! (s +:+ pretty (n1 - 1))).
Lemma fresh_string_step {A} s (m : stringmap A) n x :
  m !! (s +:+ pretty n) = Some x → R s m (1 + n) n.
Proof. split; [lia|]. replace (1 + n - 1) with n by lia; eauto. Qed.
Lemma fresh_string_R_wf {A} s (m : stringmap A) : wf (R s m).
Proof.
  induction (map_wf m) as [m _ IH]. intros n1; constructor; intros n2 [Hn Hs].
  specialize (IH _ (delete_subset m (s +:+ pretty (n2 - 1)) Hs) n2).
  cut (n2 - 1 < n2); [|lia]. clear n1 Hn Hs; revert IH; generalize (n2 - 1).
  intros n1. induction 1 as [n2 _ IH]; constructor; intros n3 [??].
  apply IH; [|lia]; split; [lia|].
  by rewrite lookup_delete_ne by (intros ?; simplify_equality'; lia).
Qed.
Definition fresh_string_go {A} (s : string) (m : stringmap A) (n : N)
    (go : ∀ n', R s m n' n → string) : string :=
  let s' := s +:+ pretty n in
  match Some_dec (m !! s') with
  | inleft (_↾Hs') => go (1 + n)%N (fresh_string_step s m n _ Hs')
  | inright _ => s'
  end.
Definition fresh_string {A} (m : stringmap A) (s : string) : string :=
  match m !! s with
  | None => s
  | Some _ =>
     Fix_F _ (fresh_string_go s m) (wf_guard 32 (fresh_string_R_wf s m) 0)
  end.
Lemma fresh_string_fresh {A} (m : stringmap A) s : m !! fresh_string m s = None.
Proof.
  unfold fresh_string. destruct (m !! s) as [a|] eqn:Hs; [clear a Hs|done].
  generalize 0 (wf_guard 32 (fresh_string_R_wf s m) 0); revert m.
  fix 3; intros m n [?]; simpl; unfold fresh_string_go at 1; simpl.
  destruct (Some_dec (m !! _)) as [[??]|?]; auto.
Qed.
