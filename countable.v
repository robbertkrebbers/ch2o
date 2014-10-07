(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export list.
Local Obligation Tactic := idtac.
Local Open Scope positive.

Class Countable A `{∀ x y : A, Decision (x = y)} := {
  encode : A → positive;
  decode : positive → option A;
  decode_encode x : decode (encode x) = Some x
}.

Definition encode_nat `{Countable A} (x : A) : nat :=
  pred (Pos.to_nat (encode x)).
Definition decode_nat `{Countable A} (i : nat) : option A :=
  decode (Pos.of_nat (S i)).
Lemma decode_encode_nat `{Countable A} x : decode_nat (encode_nat x) = Some x.
Proof.
  pose proof (Pos2Nat.is_pos (encode x)).
  unfold decode_nat, encode_nat. rewrite Nat.succ_pred by lia.
  by rewrite Pos2Nat.id, decode_encode.
Qed.

Section choice.
  Context `{Countable A} (P : A → Prop) `{∀ x, Decision (P x)}.

  Inductive choose_step: relation positive :=
    | choose_step_None {p} : decode p = None → choose_step (Psucc p) p
    | choose_step_Some {p x} :
       decode p = Some x → ¬P x → choose_step (Psucc p) p.

  Lemma choose_step_acc : (∃ x, P x) → Acc choose_step 1%positive.
  Proof.
    intros [x Hx]. cut (∀ i p,
      i ≤ encode x → 1 + encode x = p + i → Acc choose_step p).
    { intros help. by apply (help (encode x)). }
    induction i as [|i IH] using Pos.peano_ind; intros p ??.
    { constructor. intros j. assert (p = encode x) by lia; subst.
      inversion 1 as [? Hd|?? Hd]; subst;
        rewrite decode_encode in Hd; congruence. }
    constructor. intros j.
    inversion 1 as [? Hd|? y Hd]; subst; auto with lia.
  Qed.

  Fixpoint choose_go {i} (acc : Acc choose_step i) : A :=
    match Some_dec (decode i) with
    | inleft (x↾Hx) =>
      match decide (P x) with
      | left _ => x
      | right H => choose_go (Acc_inv acc (choose_step_Some Hx H))
      end
    | inright H => choose_go (Acc_inv acc (choose_step_None H))
    end.
  Fixpoint choose_go_correct {i} (acc : Acc choose_step i) : P (choose_go acc).
  Proof. destruct acc; simpl. repeat case_match; auto. Qed.
  Fixpoint choose_go_pi {i} (acc1 acc2 : Acc choose_step i) :
    choose_go acc1 = choose_go acc2.
  Proof. destruct acc1, acc2; simpl; repeat case_match; auto. Qed.

  Definition choose (H: ∃ x, P x) : A := choose_go (choose_step_acc H).
  Definition choose_correct (H: ∃ x, P x) : P (choose H) := choose_go_correct _.
  Definition choose_pi (H1 H2 : ∃ x, P x) :
    choose H1 = choose H2 := choose_go_pi _ _.
  Definition choice (HA : ∃ x, P x) : { x | P x } := _↾choose_correct HA.
End choice.

Lemma surjective_cancel `{Countable A} `{∀ x y : B, Decision (x = y)}
  (f : A → B) `{!Surjective (=) f} : { g : B → A & Cancel (=) f g }.
Proof.
  exists (λ y, choose (λ x, f x = y) (surjective f y)).
  intros y. by rewrite (choose_correct (λ _, _) (surjective f y)).
Qed.

(** ** Instances *)
Program Instance option_countable `{Countable A} : Countable (option A) := {|
  encode o :=
    match o with None => 1 | Some x => Pos.succ (encode x) end;
  decode p :=
    if decide (p = 1) then Some None else Some <$> decode (Pos.pred p)
|}.
Next Obligation.
  intros ??? [x|]; simpl; repeat case_decide; auto with lia.
  by rewrite Pos.pred_succ, decode_encode.
Qed.

Program Instance sum_countable `{Countable A} `{Countable B} :
  Countable (A + B)%type := {|
    encode xy :=
      match xy with inl x => (encode x)~0 | inr y => (encode y)~1 end;
    decode p :=
      match p with
      | 1 => None | p~0 => inl <$> decode p | p~1 => inr <$> decode p
      end
  |}.
Next Obligation. by intros ?????? [x|y]; simpl; rewrite decode_encode. Qed.

Fixpoint prod_encode_fst (p : positive) : positive :=
  match p with
  | 1 => 1
  | p~0 => (prod_encode_fst p)~0~0
  | p~1 => (prod_encode_fst p)~0~1
  end.
Fixpoint prod_encode_snd (p : positive) : positive :=
  match p with
  | 1 => 1~0
  | p~0 => (prod_encode_snd p)~0~0
  | p~1 => (prod_encode_snd p)~1~0
  end.
Fixpoint prod_encode (p q : positive) : positive :=
  match p, q with
  | 1, 1 => 1~1
  | p~0, 1 => (prod_encode_fst p)~1~0
  | p~1, 1 => (prod_encode_fst p)~1~1
  | 1, q~0 => (prod_encode_snd q)~0~1
  | 1, q~1 => (prod_encode_snd q)~1~1
  | p~0, q~0 => (prod_encode p q)~0~0
  | p~0, q~1 => (prod_encode p q)~1~0
  | p~1, q~0 => (prod_encode p q)~0~1
  | p~1, q~1 => (prod_encode p q)~1~1
  end.
Fixpoint prod_decode_fst (p : positive) : option positive :=
  match p with
  | p~0~0 => (~0) <$> prod_decode_fst p
  | p~0~1 => Some match prod_decode_fst p with Some q => q~1 | _ => 1 end
  | p~1~0 => (~0) <$> prod_decode_fst p
  | p~1~1 => Some match prod_decode_fst p with Some q => q~1 | _ => 1 end
  | 1~0 => None
  | 1~1 => Some 1
  | 1 => Some 1
  end.
Fixpoint prod_decode_snd (p : positive) : option positive :=
  match p with
  | p~0~0 => (~0) <$> prod_decode_snd p
  | p~0~1 => (~0) <$> prod_decode_snd p
  | p~1~0 => Some match prod_decode_snd p with Some q => q~1 | _ => 1 end
  | p~1~1 => Some match prod_decode_snd p with Some q => q~1 | _ => 1 end
  | 1~0 => Some 1
  | 1~1 => Some 1
  | 1 => None
  end.

Lemma prod_decode_encode_fst p q : prod_decode_fst (prod_encode p q) = Some p.
Proof.
  assert (∀ p, prod_decode_fst (prod_encode_fst p) = Some p).
  { intros p'. by induction p'; simplify_option_equality. }
  assert (∀ p, prod_decode_fst (prod_encode_snd p) = None).
  { intros p'. by induction p'; simplify_option_equality. }
  revert q. by induction p; intros [?|?|]; simplify_option_equality.
Qed.
Lemma prod_decode_encode_snd p q : prod_decode_snd (prod_encode p q) = Some q.
Proof.
  assert (∀ p, prod_decode_snd (prod_encode_snd p) = Some p).
  { intros p'. by induction p'; simplify_option_equality. }
  assert (∀ p, prod_decode_snd (prod_encode_fst p) = None).
  { intros p'. by induction p'; simplify_option_equality. }
  revert q. by induction p; intros [?|?|]; simplify_option_equality.
Qed.
Program Instance prod_countable `{Countable A} `{Countable B} :
  Countable (A * B)%type := {|
    encode xy := let (x,y) := xy in prod_encode (encode x) (encode y);
    decode p :=
     x ← prod_decode_fst p ≫= decode;
     y ← prod_decode_snd p ≫= decode; Some (x, y)
  |}.
Next Obligation.
  intros ?????? [x y]; simpl.
  rewrite prod_decode_encode_fst, prod_decode_encode_snd.
  csimpl. by rewrite !decode_encode.
Qed.

Fixpoint list_encode_ (l : list positive) : positive :=
  match l with [] => 1 | x :: l => prod_encode x (list_encode_ l) end.
Definition list_encode (l : list positive) : positive :=
  prod_encode (Pos.of_nat (S (length l))) (list_encode_ l).

Fixpoint list_decode_ (n : nat) (p : positive) : option (list positive) :=
  match n with
  | O => guard (p = 1); Some []
  | S n =>
     x ← prod_decode_fst p; pl ← prod_decode_snd p;
     l ← list_decode_ n pl; Some (x :: l)
  end.
Definition list_decode (p : positive) : option (list positive) :=
  pn ← prod_decode_fst p; pl ← prod_decode_snd p;
  list_decode_ (pred (Pos.to_nat pn)) pl.

Lemma list_decode_encode l : list_decode (list_encode l) = Some l.
Proof.
  cut (list_decode_ (length l) (list_encode_ l) = Some l).
  { intros help. unfold list_decode, list_encode.
    rewrite prod_decode_encode_fst, prod_decode_encode_snd; csimpl.
    by rewrite Nat2Pos.id by done; simpl. }
  induction l; simpl; auto.
  by rewrite prod_decode_encode_fst, prod_decode_encode_snd;
    simplify_option_equality.
Qed.

Program Instance list_countable `{Countable A} : Countable (list A) :=  {|
  encode l := list_encode (encode <$> l);
  decode p := list_decode p ≫= mapM decode
|}.
Next Obligation.
  intros ??? l. rewrite list_decode_encode. simpl.
  apply mapM_fmap_Some; auto using decode_encode.
Qed.

Program Instance pos_countable : Countable positive := {|
  encode := id; decode := Some; decode_encode x := eq_refl
|}.
Program Instance N_countable : Countable N := {|
  encode x := match x with N0 => 1 | Npos p => Pos.succ p end;
  decode p := if decide (p = 1) then Some 0%N else Some (Npos (Pos.pred p))
|}.
Next Obligation.
  intros [|p]; simpl; repeat case_decide; auto with lia.
  by rewrite Pos.pred_succ.
Qed.
Program Instance Z_countable : Countable Z := {|
  encode x :=
    match x with Z0 => 1 | Zpos p => p~0 | Zneg p => p~1 end;
  decode p := Some
    match p with 1 => Z0 | p~0 => Zpos p | p~1 => Zneg p end
|}.
Next Obligation. by intros [|p|p]. Qed.
Program Instance nat_countable : Countable nat := {|
  encode x := encode (N.of_nat x);
  decode p := N.to_nat <$> decode p
|}.
Next Obligation.
  intros x. rewrite decode_encode; csimpl. by rewrite Nat2N.id.
Qed.
