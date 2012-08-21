Require Import Permutation. 
Require Export base decidable option.

Arguments cons {_} _ _.
Arguments app {_} _ _.

Arguments In {_} _ _.
Arguments NoDup_nil {_}.
Arguments Permutation {_} _ _.

Notation "(::)" := cons (only parsing) : C_scope.
Notation "( x ::)" := (cons x) (only parsing) : C_scope.
Notation "(:: l )" := (λ x, cons x l) (only parsing) : C_scope.
Notation "(++)" := app (only parsing) : C_scope.
Notation "( l ++)" := (app l) (only parsing) : C_scope.
Notation "(++ k )" := (λ l, app l k) (only parsing) : C_scope.

Global Instance list_lookup: Lookup nat list :=
  fix list_lookup A (i : nat) (l : list A) {struct l} : option A :=
  match l with
  | [] => None
  | x :: l =>
    match i with
    | 0 => Some x
    | S i => @lookup _ _ list_lookup _ i l
    end
  end.

(* The [simpl] tactic does not unfold [list_lookup] as it is wrapped into
a type class. Therefore we use the following tactic. Bug: does not simplify
under binders.
*)
Ltac simplify_list_lookup := repeat
  match goal with
  | |- context f [@nil ?A !! _] => let X := (context f [@None A]) in change X
  | |- context f [(?x :: _) !! 0] => let X := (context f [Some x]) in change X
  | |- context f [(_ :: ?l) !! S ?i] => let X := (context f [l !! i]) in change X
  | H : context f [@nil ?A !! _] |- _ => let X := (context f [@None A]) in change X in H
  | H : context f [(?x :: _) !! 0] |- _ => let X := (context f [Some x]) in change X in H
  | H : context f [(_ :: ?l) !! S ?i] |- _  => let X := (context f [l !! i]) in change X in H
  end.

Global Instance list_alter: Alter nat list :=
  fix list_alter A (f : A → A) (i : nat) (l : list A) {struct l} :=
  match l with
  | [] => []
  | x :: l =>
    match i with
    | 0 => f x :: l
    | S i => x :: @alter _ _ list_alter _ f i l
    end
  end.

Definition option_list {A} : option A → list A := option_rect _ (λ x, [x]) [].
Definition prefix_of {A} (l1 l2 : list A) : Prop := ∃ k, l2 = l1 ++ k.
Definition suffix_of {A} (l1 l2 : list A) : Prop := ∃ k, l2 = k ++ l1.

Section list_properties.
Context {A : Type}.

Lemma list_eq (l1 l2 : list A) : (∀ i, l1 !! i = l2 !! i) → l1 = l2.
Proof.
  revert l2. induction l1; intros [|??] H.
  * easy.
  * discriminate (H 0).
  * discriminate (H 0).
  * f_equal. now injection (H 0). apply IHl1. intro. apply (H (S _)).
Qed.

Lemma list_lookup_nil i : @nil A !! i = None.
Proof. now destruct i. Qed.
Lemma list_lookup_tail (l : list A) i : tail l !! i = l !! S i.
Proof. now destruct l. Qed.

Lemma list_lookup_Some_In (l : list A) i x : l !! i = Some x → In x l.
Proof.
  revert i. induction l; intros [|i] ?;
    simplify_list_lookup; simplify_eqs; constructor (solve [eauto]).
Qed.

Lemma list_lookup_In_Some (l : list A) x : In x l → ∃ i, l !! i = Some x.
Proof.
  induction l; destruct 1; subst.
  * now exists 0.
  * destruct IHl as [i ?]; auto. now exists (S i).
Qed.
Lemma list_lookup_In (l : list A) x : In x l ↔ ∃ i, l !! i = Some x.
Proof. firstorder eauto using list_lookup_Some_In, list_lookup_In_Some. Qed.

Lemma list_lookup_app_length (l1 l2 : list A) (x : A) :
  (l1 ++ x :: l2) !! length l1 = Some x.
Proof. induction l1; simpl; now simplify_list_lookup. Qed.

Lemma list_lookup_lt_length (l : list A) i : is_Some (l !! i) ↔ i < length l.
Proof.
  revert i. induction l.
  * split; now inversion 1.
  * intros [|?]; simplify_list_lookup; simpl.
    + split; auto with arith.
    + now rewrite <-NPeano.Nat.succ_lt_mono.
Qed.
Lemma list_lookup_weaken (l l' : list A) i x :
  l !! i = Some x → (l ++ l') !! i = Some x.
Proof. revert i. induction l. discriminate. now intros []. Qed.

Lemma Forall_impl (P Q : A → Prop) l :
  Forall P l → (∀ x, P x → Q x) → Forall Q l.
Proof. induction 1; auto. Qed.

Lemma Forall2_length {B} (P : A → B → Prop) l1 l2 :
  Forall2 P l1 l2 → length l1 = length l2.
Proof. induction 1; simpl; auto. Qed.

Lemma Forall2_impl {B} (P Q : A → B → Prop) l1 l2 :
  Forall2 P l1 l2 → (∀ x y, P x y → Q x y) → Forall2 Q l1 l2.
Proof. induction 1; auto. Qed.

Lemma Forall2_unique {B} (P : A → B → Prop) l k1 k2 :
  Forall2 P l k1 → Forall2 P l k2 → (∀ x y1 y2, P x y1 → P x y2 → y1 = y2) → k1 = k2.
Proof. intros H. revert k2. induction H; inversion_clear 1; intros; f_equal; eauto. Qed.

Lemma NoDup_singleton (x : A) : NoDup [x].
Proof. constructor. easy. constructor. Qed.
Lemma NoDup_app (l k : list A) :
  NoDup l → NoDup k → (∀ x, In x l → ¬In x k) → NoDup (l ++ k).
Proof.
  induction 1; simpl.
  * easy.
  * constructor. rewrite in_app_iff. firstorder. firstorder.
Qed.

Global Instance: ∀ k : list A, Injective (=) (=) (k ++).
Proof. intros ???. apply app_inv_head. Qed.
Global Instance: ∀ k : list A, Injective (=) (=) (++ k).
Proof. intros ???. apply app_inv_tail. Qed.

Lemma in_nil_inv (l : list A) : (∀ x, ¬In x l) → l = [].
Proof. destruct l. easy. now edestruct 1; constructor. Qed.
Lemma nil_length (l : list A) : length l = 0 → l = [].
Proof. destruct l. easy. discriminate. Qed.
Lemma NoDup_inv_1 (x : A) (l : list A) : NoDup (x :: l) → ¬In x l.
Proof. now inversion_clear 1. Qed.
Lemma NoDup_inv_2 (x : A) (l : list A) : NoDup (x :: l) → NoDup l.
Proof. now inversion_clear 1. Qed.
Lemma Forall_inv_2 (P : A → Prop) x l : Forall P (x :: l) → Forall P l.
Proof. now inversion 1. Qed.
Lemma Exists_inv (P : A → Prop) x l : Exists P (x :: l) → P x ∨ Exists P l.
Proof. inversion 1; intuition. Qed.

Global Instance list_eq_dec {dec : ∀ x y : A, Decision (x = y)} : ∀ l k,
  Decision (l = k) := list_eq_dec dec.
Global Instance list_in_dec {dec : ∀ x y : A, Decision (x = y)} : ∀ x l,
  Decision (In x l) := in_dec dec.

Global Instance NoDup_dec {dec : ∀ x y : A, Decision (x = y)} :
    ∀ (l : list A), Decision (NoDup l) :=
  fix NoDup_dec l :=
  match l return Decision (NoDup l) with
  | [] => left NoDup_nil
  | x :: l =>
    match In_dec dec x l with
    | left Hin => right (λ H, NoDup_inv_1 _ _ H Hin)
    | right Hin =>
      match NoDup_dec l with
      | left H => left (NoDup_cons _ Hin H)
      | right H => right (H ∘ NoDup_inv_2 _ _)
      end
    end
  end.

Global Instance Forall_dec (P : A → Prop) {dec : ∀ x, Decision (P x)} :
    ∀ l, Decision (Forall P l) :=
  fix go (l : list A) :=
  match l return {Forall P l} + {¬Forall P l} with
  | [] => left (Forall_nil _)
  | x :: l =>
    match dec x with
    | left Hx =>
      match go l with
      | left Hl => left (Forall_cons _ Hx Hl)
      | right Hl => right (Hl ∘ Forall_inv_2 _ _ _)
      end
    | right Hx => right (Hx ∘ @Forall_inv _ _ _ _)
    end
  end.

Global Instance Exists_dec (P : A → Prop) {dec : ∀ x, Decision (P x)} :
    ∀ l, Decision (Exists P l) :=
  fix go (l : list A) :=
  match l return {Exists P l} + {¬Exists P l} with
  | [] => right (proj1 (Exists_nil _))
  | x :: l =>
    match dec x with
    | left Hx => left (Exists_cons_hd _ _ _ Hx)
    | right Hx =>
      match go l with
      | left Hl => left (Exists_cons_tl _ Hl)
      | right Hl => right (or_ind Hx Hl ∘ Exists_inv _ _ _)
      end
    end
  end.

Global Instance: PreOrder (@prefix_of A).
Proof.
  split.
   intros ?. eexists []. now rewrite app_nil_r.
  intros ??? [k1 ?] [k2 ?]. exists (k1 ++ k2). subst. now rewrite app_assoc.
Qed.

Lemma prefix_of_nil (l : list A) : prefix_of [] l.
Proof. now exists l. Qed.
Lemma prefix_of_nil_not x (l : list A) : ¬prefix_of (x :: l) [].
Proof. intros [k E]. discriminate. Qed.
Lemma prefix_of_cons x y (l1 l2 : list A) :
  x = y → prefix_of l1 l2 → prefix_of (x :: l1) (y :: l2).
Proof. intros ? [k E]. exists k. now subst. Qed.
Lemma prefix_of_cons_inv_1 x y (l1 l2 : list A) :
  prefix_of (x :: l1) (y :: l2) → x = y.
Proof. intros [k E]. now injection E. Qed.
Lemma prefix_of_cons_inv_2 x y (l1 l2 : list A) :
  prefix_of (x :: l1) (y :: l2) → prefix_of l1 l2.
Proof. intros [k E]. exists k. now injection E. Qed.

Lemma prefix_of_app_l (l1 l2 l3 : list A) :
  prefix_of (l1 ++ l3) l2 → prefix_of l1 l2.
Proof. intros [k ?]. red. exists (l3 ++ k). subst. now rewrite <-app_assoc. Qed.
Lemma prefix_of_app_r (l1 l2 l3 : list A) :
  prefix_of l1 l2 → prefix_of l1 (l2 ++ l3).
Proof. intros [k ?]. exists (k ++ l3). subst. now rewrite app_assoc. Qed.

Global Instance prefix_of_dec `{∀ x y : A, Decision (x = y)} :
    ∀ l1 l2, Decision (prefix_of l1 l2) :=
  fix prefix_of_dec l1 l2 :=
  match l1, l2 return { prefix_of l1 l2 } + { ¬prefix_of l1 l2 } with
  | [], _ => left (prefix_of_nil _)
  | _, [] => right (prefix_of_nil_not _ _)
  | x :: l1, y :: l2 =>
    match decide_rel (=) x y with
    | left Exy =>
      match prefix_of_dec l1 l2 with
      | left Hl1l2 => left (prefix_of_cons _ _ _ _ Exy Hl1l2)
      | right Hl1l2 => right (Hl1l2 ∘ prefix_of_cons_inv_2 _ _ _ _)
      end
    | right Exy => right (Exy ∘ prefix_of_cons_inv_1 _ _ _ _)
    end
  end.

Global Instance: PreOrder (@suffix_of A).
Proof.
  split.
  * intros ?. now eexists [].
  * intros ??? [k1 ?] [k2 ?].
    exists (k2 ++ k1). subst. now rewrite app_assoc.
Qed.

Lemma prefix_suffix_rev (l1 l2 : list A) :
  prefix_of l1 l2 ↔ suffix_of (rev l1) (rev l2).
Proof.
  split; intros [k E]; exists (rev k).
  * now rewrite E, rev_app_distr.
  * now rewrite <-(rev_involutive l2), E, rev_app_distr, rev_involutive.
Qed.
Lemma suffix_prefix_rev (l1 l2 : list A) :
  suffix_of l1 l2 ↔ prefix_of (rev l1) (rev l2).
Proof. now rewrite prefix_suffix_rev, !rev_involutive. Qed.

Lemma suffix_of_nil (l : list A) : suffix_of [] l.
Proof. exists l. now rewrite app_nil_r. Qed.
Lemma suffix_of_nil_not x (l : list A) : ¬suffix_of (x :: l) [].
Proof. intros [[] ?]; discriminate. Qed.
Lemma suffix_of_cons x y (l1 l2 : list A) :
  x = y → suffix_of l1 l2 → suffix_of (l1 ++ [x]) (l2 ++ [y]).
Proof. intros ? [k E]. exists k. subst. now rewrite app_assoc. Qed.
Lemma suffix_of_snoc_inv_1 x y (l1 l2 : list A) :
  suffix_of (l1 ++ [x]) (l2 ++ [y]) → x = y.
Proof. rewrite suffix_prefix_rev, !rev_unit. now apply prefix_of_cons_inv_1. Qed.
Lemma suffix_of_snoc_inv_2 x y (l1 l2 : list A) :
  suffix_of (l1 ++ [x]) (l2 ++ [y]) → suffix_of l1 l2.
Proof. rewrite !suffix_prefix_rev, !rev_unit. now apply prefix_of_cons_inv_2. Qed.

Lemma suffix_of_cons_l (l1 l2 : list A) x :
  suffix_of (x :: l1) l2 → suffix_of l1 l2.
Proof. intros [k ?]. exists (k ++ [x]). subst. now rewrite <-app_assoc. Qed.
Lemma suffix_of_app_l (l1 l2 l3 : list A) :
  suffix_of (l3 ++ l1) l2 → suffix_of l1 l2.
Proof. intros [k ?]. exists (k ++ l3). subst. now rewrite <-app_assoc. Qed.
Lemma suffix_of_cons_r (l1 l2 : list A) x :
  suffix_of l1 l2 → suffix_of l1 (x :: l2).
Proof. intros [k ?]. exists (x :: k). now subst. Qed.
Lemma suffix_of_app_r (l1 l2 l3 : list A) :
  suffix_of l1 l2 → suffix_of l1 (l3 ++ l2).
Proof. intros [k ?]. exists (l3 ++ k). subst. now rewrite app_assoc. Qed.

Lemma suffix_of_cons_inv (l1 l2 : list A) x y : 
  suffix_of (x :: l1) (y :: l2) → x :: l1 = y :: l2 ∨ suffix_of (x :: l1) l2.
Proof.
  intros [[|? k] E].
   now left.
  right. simplify_eqs. now apply suffix_of_app_r.
Qed.
Lemma suffix_of_cons_not x (l : list A) : ¬suffix_of (x :: l) l.
Proof.
  intros [k E]. change ([] ++ l = k ++ [x] ++ l) in E.
  rewrite app_assoc in E. apply app_inv_tail in E.
  destruct k; simplify_eqs.
Qed.

Global Program Instance suffix_of_dec `{∀ x y : A, Decision (x = y)} l1 l2 :
    Decision (suffix_of l1 l2) :=
  match decide_rel prefix_of (rev_append l1 []) (rev_append l2 []) with
  | left Hpre => left _
  | right Hpre => right _
  end.
Next Obligation. apply suffix_prefix_rev. now rewrite !rev_alt. Qed.
Next Obligation. 
  intro. destruct Hpre. rewrite <-!rev_alt. 
  now apply suffix_prefix_rev.
Qed.
End list_properties.

Hint Resolve suffix_of_nil suffix_of_cons_r suffix_of_app_r : list.
Hint Extern 0 (prefix_of _ _) => reflexivity : list.
Hint Extern 0 (suffix_of _ _) => reflexivity: list.
Hint Extern 0 (PropHolds (suffix_of _ _)) => red; auto with list : typeclass_instances.

Ltac simplify_suffix_of := repeat
  match goal with
  | H : suffix_of (_ :: _) _ |- _ => destruct (suffix_of_cons_not _ _ H)
  | H : suffix_of (_ :: _) [] |- _ => destruct (suffix_of_nil_not _ _ H)
  | H : suffix_of (_ :: _) (_ :: _) |- _ =>
    destruct (suffix_of_cons_inv _ _ _ _ H); clear H
  | H : suffix_of ?x ?x |- _ => clear H
  | H : suffix_of ?x (_ :: ?x) |- _ => clear H
  | H : suffix_of ?x (_ ++ ?x) |- _ => clear H
  | _ => progress simplify_eqs
  end.

(* Extremely dirty way to discrimate inconsistent suffix_of assumptions *)
Ltac discriminate_suffix_of := solve [repeat
  match goal with
  | _ => progress simplify_suffix_of
  | H1 : suffix_of ?x ?y, H2 : suffix_of ?y ?z |- _ =>
     match goal with
     | _ : suffix_of x z |- _ => fail 2
     | _ => assert (suffix_of x z) by (transitivity y; assumption);
                 clear H1; clear H2 (* to avoid loops *)
     end
  end].

Global Instance list_ret: MRet list := λ A a, [a].
Global Instance list_fmap: FMap list :=
  fix go A B (f : A → B) (l : list A) :=
  match l with
  | [] => []
  | x :: l => f x :: @fmap _ go _ _ f l
  end.
Global Instance list_join: MJoin list := 
  fix go A (l : list (list A)) : list A :=
  match l with
  | [] =>  []
  | x :: l => x ++ @mjoin _ go _ l
  end.
Global Instance list_bind: MBind list := λ A B f l, mjoin (f <$> l).

Local Arguments fmap _ _ _ _ _ !_ /.

Section list_fmap.
  Context {A B : Type} (f : A → B).

  Lemma fmap_length l : length (f <$> l) = length l.
  Proof. induction l; simpl; auto. Qed.

  Lemma list_lookup_fmap l i : (f <$> l) !! i = f <$> (l !! i).
  Proof. revert i. induction l; now intros [|]. Qed.

  Lemma in_fmap_1 l x : In x l → In (f x) (f <$> l).
  Proof. induction l; destruct 1; subst; constructor (solve [auto]). Qed.
  Lemma in_fmap_1_alt l x y : In x l → y = f x → In y (f <$> l).
  Proof. intros. subst. now apply in_fmap_1. Qed.
  Lemma in_fmap_2 l x : In x (f <$> l) → ∃ y, x = f y ∧ In y l.
  Proof.
    induction l as [|y l]; destruct 1; subst.
    * exists y; now intuition.
    * destruct IHl as [y' [??]]. easy. exists y'; now intuition.
  Qed.
  Lemma in_fmap l x : In x (f <$> l) ↔ ∃ y, x = f y ∧ In y l.
  Proof.
    split.
    * apply in_fmap_2.
    * intros [? [??]]. eauto using in_fmap_1_alt.
  Qed.
End list_fmap.

Lemma Forall_fst {A B} (l : list (A * B)) (P : A → Prop) :
  Forall (P ∘ fst) l ↔ Forall P (fst <$> l).
Proof. induction l; split; inversion 1; subst; constructor; firstorder auto. Qed.
Lemma Forall_snd {A B} (l : list (A * B)) (P : B → Prop) :
  Forall (P ∘ snd) l ↔ Forall P (snd <$> l).
Proof. induction l; split; inversion 1; subst; constructor; firstorder auto. Qed.

Definition imap_go {A B} (f : nat → A → B) : nat → list A → list B :=
  fix go (n : nat) (l : list A) :=
  match l with
  | [] => []
  | x :: l => f n x :: go (S n) l
  end.
Definition imap {A B} (f : nat → A → B) : list A → list B := imap_go f 0.

Lemma fold_right_permutation `(f : A → B → B) (b : B) :
  (∀ a1 a2 b, f a1 (f a2 b) = f a2 (f a1 b)) →
  Proper (Permutation ==> (=)) (fold_right f b).
Proof. intro. induction 1; simpl; congruence. Qed.

Definition ifold_right {A B} (f : nat → B → A → A) (a : nat → A) : nat → list B → A :=
  fix go (n : nat) (l : list B) : A :=
  match l with
  | nil => a n
  | b :: l => f n b (go (S n) l)
  end.

Lemma ifold_right_app {A B} (f : nat → B → A → A) (a : nat → A) (l1 l2 : list B) n :
  ifold_right f a n (l1 ++ l2) = ifold_right f (λ n, ifold_right f a n l2) n l1.
Proof. revert n a. induction l1 as [| b l1 IH ]; intros; simpl; f_equal; auto. Qed.

Section same_length.
  Context {A B : Type}.

  Inductive same_length : list A → list B → Prop :=
    | same_length_nil : same_length [] []
    | same_length_cons x y l k :
      same_length l k → same_length (x :: l) (y :: k).

  Lemma same_length_length l k :
    same_length l k ↔ length l = length k.
  Proof.
    split.
    * induction 1; simpl; auto.
    * revert k. induction l; intros [|??]; try discriminate;
      constructor; auto with arith.
  Qed.

  Lemma same_length_lookup l k i :
    same_length l k → is_Some (l !! i) → is_Some (k !! i).
  Proof.
    rewrite same_length_length.
    setoid_rewrite list_lookup_lt_length.
    intros E. now rewrite E.
  Qed.
End same_length.

Notation zip := combine.

Section zip.
  Context {A B : Type}.

  Lemma zip_fst_le (l1 : list A) (l2 : list B) :
    length l1 ≤ length l2 → fst <$> zip l1 l2 = l1.
  Proof.
    revert l2.
    induction l1; intros [|??] ?; simpl; f_equal; auto with arith.
    edestruct Le.le_Sn_0; eauto.
  Qed.
  Lemma zip_fst (l1 : list A) (l2 : list B) :
    same_length l1 l2 → fst <$> zip l1 l2 = l1.
  Proof.
    rewrite same_length_length. intros H.
    apply zip_fst_le. now rewrite H.
  Qed.

  Lemma zip_snd_le (l1 : list A) (l2 : list B) :
    length l2 ≤ length l1 → snd <$> zip l1 l2 = l2.
  Proof.
    revert l2.
    induction l1; intros [|??] ?; simpl; f_equal; auto with arith.
    edestruct Le.le_Sn_0; eauto.
  Qed.
  Lemma zip_snd (l1 : list A) (l2 : list B) :
    same_length l1 l2 → snd <$> zip l1 l2 = l2.
  Proof.
    rewrite same_length_length. intros H.
    apply zip_snd_le. now rewrite H.
  Qed.
End zip.
