(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export countable list.
Obligation Tactic := idtac.

Class Finite A `{∀ x y : A, Decision (x = y)} := {
  enum : list A;
  NoDup_enum : NoDup enum;
  elem_of_enum x : x ∈ enum
}.
Arguments enum _ {_ _} : clear implicits.
Arguments NoDup_enum _ {_ _} : clear implicits.
Definition card A `{Finite A} := length (enum A).
Program Instance finite_countable `{Finite A} : Countable A := {|
  encode := λ x, Pos.of_nat $ S $ from_option 0 $ list_find (x =) (enum A);
  decode := λ p, enum A !! pred (Pos.to_nat p)
|}.
Arguments Pos.of_nat _ : simpl never.
Next Obligation.
  intros ?? [xs Hxs HA] x; unfold encode, decode; simpl.
  destruct (list_find_eq_elem_of xs x) as [i Hi]; auto.
  rewrite Nat2Pos.id by done; simpl.
  rewrite Hi; eauto using list_find_eq_Some.
Qed.
Definition find `{Finite A} P `{∀ x, Decision (P x)} : option A :=
  list_find P (enum A) ≫= decode_nat.

Lemma encode_lt_card `{finA: Finite A} x : encode_nat x < card A.
Proof.
  destruct finA as [xs Hxs HA]; unfold encode_nat, encode, card; simpl.
  rewrite Nat2Pos.id by done; simpl. destruct (list_find _ xs) eqn:?; simpl.
  * eapply lookup_lt_Some, list_find_eq_Some; eauto.
  * destruct xs; simpl. exfalso; eapply not_elem_of_nil, (HA x). lia.
Qed.
Lemma encode_decode A `{finA: Finite A} i :
  i < card A → ∃ x, decode_nat i = Some x ∧ encode_nat x = i.
Proof.
  destruct finA as [xs Hxs HA].
  unfold encode_nat, decode_nat, encode, decode, card; simpl.
  intros Hi. apply lookup_lt_is_Some in Hi. destruct Hi as [x Hx].
  exists x. rewrite !Nat2Pos.id by done; simpl.
  destruct (list_find_eq_elem_of xs x) as [j Hj]; auto.
  rewrite Hj. eauto using list_find_eq_Some, NoDup_lookup.
Qed.
Lemma find_Some `{finA: Finite A} P `{∀ x, Decision (P x)} x :
  find P = Some x → P x.
Proof.
  destruct finA as [xs Hxs HA]; unfold find, decode_nat, decode; simpl.
  intros Hx. destruct (list_find _ _) as [i|] eqn:Hi; simplify_option_equality.
  rewrite !Nat2Pos.id in Hx by done.
  destruct (list_find_Some P xs i) as (?&?&?); simplify_option_equality; eauto.
Qed.
Lemma find_is_Some `{finA: Finite A} P `{∀ x, Decision (P x)} x :
  P x → ∃ y, find P = Some y ∧ P y.
Proof.
  destruct finA as [xs Hxs HA]; unfold find, decode; simpl.
  intros Hx. destruct (list_find_elem_of P xs x) as [i Hi]; auto.
  rewrite Hi. destruct (list_find_Some P xs i) as (y&?&?); subst; auto.
  exists y. simpl. by rewrite !Nat2Pos.id by done.
Qed.

Lemma card_0_inv P `{finA: Finite A} : card A = 0 → A → P.
Proof.
  intros ? x. destruct finA as [[|??] ??]; simplify_equality.
  by destruct (not_elem_of_nil x).
Qed.
Lemma finite_inhabited A `{finA: Finite A} : 0 < card A → Inhabited A.
Proof.
  unfold card. destruct finA as [[|x ?] ??]; simpl; auto with lia.
  constructor; exact x.
Qed.
Lemma finite_injective_contains `{finA: Finite A} `{finB: Finite B} (f: A → B)
  `{!Injective (=) (=) f} : f <$> enum A `contains` enum B.
Proof.
  intros. destruct finA, finB. apply NoDup_contains; auto using NoDup_fmap_2.
Qed.
Lemma finite_injective_Permutation `{Finite A} `{Finite B} (f : A → B)
  `{!Injective (=) (=) f} : card A = card B → f <$> enum A ≡ₚ enum B.
Proof.
  intros. apply contains_Permutation_length_eq.
  * by rewrite fmap_length.
  * by apply finite_injective_contains.
Qed.
Lemma finite_injective_surjective `{Finite A} `{Finite B} (f : A → B)
  `{!Injective (=) (=) f} : card A = card B → Surjective (=) f.
Proof.
  intros HAB y. destruct (elem_of_list_fmap_2 f (enum A) y) as (x&?&?); eauto.
  rewrite finite_injective_Permutation; auto using elem_of_enum.
Qed.

Lemma finite_surjective A `{Finite A} B `{Finite B} :
  0 < card A ≤ card B → ∃ g : B → A, Surjective (=) g.
Proof.
  intros [??]. destruct (finite_inhabited A) as [x']; auto with lia.
  exists (λ y : B, from_option x' (decode_nat (encode_nat y))).
  intros x. destruct (encode_decode B (encode_nat x)) as (y&Hy1&Hy2).
  { pose proof (encode_lt_card x); lia. }
  exists y. by rewrite Hy2, decode_encode_nat.
Qed.
Lemma finite_injective A `{Finite A} B `{Finite B} :
  card A ≤ card B ↔ ∃ f : A → B, Injective (=) (=) f.
Proof.
  split.
  * intros. destruct (decide (card A = 0)) as [HA|?].
    { exists (card_0_inv B HA). intros y. apply (card_0_inv _ HA y). }
    destruct (finite_surjective A B) as (g&?); auto with lia.
    destruct (surjective_cancel g) as (f&?). exists f. apply cancel_injective.
  * intros [f ?]. unfold card. rewrite <-(fmap_length f).
    by apply contains_length, (finite_injective_contains f).
Qed.
Lemma finite_bijective A `{Finite A} B `{Finite B} :
  card A = card B ↔ ∃ f : A → B, Injective (=) (=) f ∧ Surjective (=) f.
Proof.
  split.
  * intros; destruct (proj1 (finite_injective A B)) as [f ?]; auto with lia.
    exists f; auto using (finite_injective_surjective f).
  * intros (f&?&?). apply (anti_symmetric (≤)); apply finite_injective.
    + by exists f.
    + destruct (surjective_cancel f) as (g&?); eauto using cancel_injective.
Qed.
Lemma injective_card `{Finite A} `{Finite B} (f : A → B)
  `{!Injective (=) (=) f} : card A ≤ card B.
Proof. apply finite_injective. eauto. Qed.
Lemma surjective_card `{Finite A} `{Finite B} (f : A → B)
  `{!Surjective (=) f} : card B ≤ card A.
Proof.
  destruct (surjective_cancel f) as (g&?).
  apply injective_card with g, cancel_injective.
Qed.
Lemma bijective_card `{Finite A} `{Finite B} (f : A → B)
  `{!Injective (=) (=) f} `{!Surjective (=) f} : card A = card B.
Proof. apply finite_bijective. eauto. Qed.

(** Decidability of quantification over finite types *)
Section forall_exists.
  Context `{Finite A} (P : A → Prop) `{∀ x, Decision (P x)}.

  Lemma Forall_finite : Forall P (enum A) ↔ (∀ x, P x).
  Proof. rewrite Forall_forall. intuition auto using elem_of_enum. Qed.
  Lemma Exists_finite : Exists P (enum A) ↔ (∃ x, P x).
  Proof. rewrite Exists_exists. naive_solver eauto using elem_of_enum. Qed.

  Global Instance forall_dec: Decision (∀ x, P x).
  Proof.
   refine (cast_if (decide (Forall P (enum A))));
    abstract by rewrite <-Forall_finite.
  Defined.
  Global Instance exists_dec: Decision (∃ x, P x).
  Proof.
   refine (cast_if (decide (Exists P (enum A))));
    abstract by rewrite <-Exists_finite.
  Defined.
End forall_exists.

(** Instances *)
Section enc_finite.
  Context `{∀ x y : A, Decision (x = y)}.
  Context (to_nat : A → nat) (of_nat : nat → A) (c : nat).
  Context (of_to_nat : ∀ x, of_nat (to_nat x) = x).
  Context (to_nat_c : ∀ x, to_nat x < c).
  Context (to_of_nat : ∀ i, i < c → to_nat (of_nat i) = i).

  Program Instance enc_finite : Finite A := {| enum := of_nat <$> seq 0 c |}.
  Next Obligation.
    apply NoDup_alt. intros i j x. rewrite !list_lookup_fmap. intros Hi Hj.
    destruct (seq _ _ !! i) as [i'|] eqn:Hi',
      (seq _ _ !! j) as [j'|] eqn:Hj'; simplify_equality.
    destruct (lookup_seq_inv _ _ _ _ Hi'), (lookup_seq_inv _ _ _ _ Hj'); subst.
    rewrite <-(to_of_nat i), <-(to_of_nat j) by done. by f_equal.
  Qed.
  Next Obligation.
    intros x. rewrite elem_of_list_fmap. exists (to_nat x).
    split; auto. by apply elem_of_list_lookup_2 with (to_nat x), lookup_seq.
  Qed.
  Lemma enc_finite_card : card A = c.
  Proof. unfold card. simpl. by rewrite fmap_length, seq_length. Qed.
End enc_finite.

Section bijective_finite.
  Context `{Finite A} `{∀ x y : B, Decision (x = y)} (f : A → B) (g : B → A).
  Context `{!Injective (=) (=) f} `{!Cancel (=) f g}.

  Program Instance bijective_finite: Finite B := {| enum := f <$> enum A |}.
  Next Obligation. apply (NoDup_fmap_2 _), NoDup_enum. Qed.
  Next Obligation.
    intros y. rewrite elem_of_list_fmap. eauto using elem_of_enum.
  Qed.
End bijective_finite.

Program Instance option_finite `{Finite A} : Finite (option A) :=
  {| enum := None :: Some <$> enum A |}.
Next Obligation.
  constructor.
  * rewrite elem_of_list_fmap. by intros (?&?&?).
  * apply (NoDup_fmap_2 _); auto using NoDup_enum.
Qed.
Next Obligation.
  intros ??? [x|]; [right|left]; auto.
  apply elem_of_list_fmap. eauto using elem_of_enum.
Qed.
Lemma option_cardinality `{Finite A} : card (option A) = S (card A).
Proof. unfold card. simpl. by rewrite fmap_length. Qed.

Program Instance unit_finite : Finite () := {| enum := [tt] |}.
Next Obligation. apply NoDup_singleton. Qed.
Next Obligation. intros []. by apply elem_of_list_singleton. Qed.
Lemma unit_card : card unit = 1.
Proof. done. Qed.

Program Instance bool_finite : Finite bool := {| enum := [true; false] |}.
Next Obligation.
  constructor. by rewrite elem_of_list_singleton. apply NoDup_singleton.
Qed.
Next Obligation. intros [|]. left. right; left. Qed.
Lemma bool_card : card bool = 2.
Proof. done. Qed.

Program Instance sum_finite `{Finite A} `{Finite B} : Finite (A + B)%type :=
  {| enum := (inl <$> enum A) ++ (inr <$> enum B) |}.
Next Obligation.
  intros. apply NoDup_app; split_ands.
  * apply (NoDup_fmap_2 _). by apply NoDup_enum.
  * intro. rewrite !elem_of_list_fmap. intros (?&?&?) (?&?&?); congruence.
  * apply (NoDup_fmap_2 _). by apply NoDup_enum.
Qed.
Next Obligation.
  intros ?????? [x|y]; rewrite elem_of_app, !elem_of_list_fmap;
    eauto using @elem_of_enum.
Qed.
Lemma sum_card `{Finite A} `{Finite B} : card (A + B) = card A + card B.
Proof. unfold card. simpl. by rewrite app_length, !fmap_length. Qed.

Program Instance prod_finite `{Finite A} `{Finite B} : Finite (A * B)%type :=
  {| enum := foldr (λ x, (pair x <$> enum B ++)) [] (enum A) |}.
Next Obligation.
  intros ??????. induction (NoDup_enum A) as [|x xs Hx Hxs IH]; simpl.
  { constructor. }
  apply NoDup_app; split_ands.
  * by apply (NoDup_fmap_2 _), NoDup_enum.
  * intros [? y]. rewrite elem_of_list_fmap. intros (?&?&?); simplify_equality.
    clear IH. induction Hxs as [|x' xs ?? IH]; simpl.
    { rewrite elem_of_nil. tauto. }
    rewrite elem_of_app, elem_of_list_fmap.
    intros [(?&?&?)|?]; simplify_equality.
    + destruct Hx. by left.
    + destruct IH. by intro; destruct Hx; right. auto.
  * done.
Qed.
Next Obligation.
  intros ?????? [x y]. induction (elem_of_enum x); simpl.
  * rewrite elem_of_app, !elem_of_list_fmap. eauto using @elem_of_enum.
  * rewrite elem_of_app; eauto.
Qed.
Lemma prod_card `{Finite A} `{Finite B} : card (A * B) = card A * card B.
Proof.
  unfold card; simpl. induction (enum A); simpl; auto.
  rewrite app_length, fmap_length. auto.
Qed.

Let list_enum {A} (l : list A) : ∀ n, list { l : list A | length l = n } :=
  fix go n :=
  match n with
  | 0 => [[]↾eq_refl]
  | S n => foldr (λ x, (sig_map (x ::) (λ _ H, f_equal S H) <$> (go n) ++)) [] l
  end.
Program Instance list_finite `{Finite A} n : Finite { l | length l = n } :=
  {| enum := list_enum (enum A) n |}.
Next Obligation.
  intros ????. induction n as [|n IH]; simpl; [apply NoDup_singleton |].
  revert IH. generalize (list_enum (enum A) n). intros l Hl.
  induction (NoDup_enum A) as [|x xs Hx Hxs IH]; simpl; auto; [constructor |].
  apply NoDup_app; split_ands.
  * by apply (NoDup_fmap_2 _).
  * intros [k1 Hk1]. clear Hxs IH. rewrite elem_of_list_fmap.
    intros ([k2 Hk2]&?&?) Hxk2; simplify_equality. destruct Hx. revert Hxk2.
    induction xs as [|x' xs IH]; simpl in *; [by rewrite elem_of_nil |].
    rewrite elem_of_app, elem_of_list_fmap, elem_of_cons.
    intros [([??]&?&?)|?]; simplify_equality; auto.
  * apply IH.
Qed.
Next Obligation.
  intros ???? [l Hl]. revert l Hl.
  induction n as [|n IH]; intros [|x l] ?; simpl; simplify_equality.
  { apply elem_of_list_singleton. by apply (sig_eq_pi _). }
  revert IH. generalize (list_enum (enum A) n). intros k Hk.
  induction (elem_of_enum x) as [x xs|x xs]; simpl in *.
  * rewrite elem_of_app, elem_of_list_fmap. left. injection Hl. intros Hl'.
    eexists (l↾Hl'). split. by apply (sig_eq_pi _). done.
  * rewrite elem_of_app. eauto.
Qed.
Lemma list_card `{Finite A} n : card { l | length l = n } = card A ^ n.
Proof.
  unfold card; simpl. induction n as [|n IH]; simpl; auto.
  rewrite <-IH. clear IH. generalize (list_enum (enum A) n).
  induction (enum A) as [|x xs IH]; intros l; simpl; auto.
  by rewrite app_length, fmap_length, IH.
Qed.
