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

Section list_properties.
Context {A : Type}.

Definition option_list : option A → list A := option_rect _ (λ x, [x]) [].

Lemma NoDup_singleton (x : A) : NoDup [x].
Proof. constructor. easy. constructor. Qed.
Lemma NoDup_app (l k : list A) :
  NoDup l → NoDup k → (∀ x, In x l → ¬In x k) → NoDup (l ++ k).
Proof.
  induction 1; simpl. easy.
  constructor. rewrite in_app_iff. firstorder. firstorder.
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

Global Instance list_eq_dec {dec : ∀ x y : A, Decision (x = y)} : ∀ l k : list A, Decision (l = k).
Proof. solve_decision. Qed.
Global Instance list_in_dec {dec : ∀ x y : A, Decision (x = y)} : ∀ x l,
  Decision (In x l) := in_dec dec.

Global Instance NoDup_dec {dec : ∀ x y : A, Decision (x = y)} : ∀ (l : list A), Decision (NoDup l) :=
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

Global Instance Forall_dec (P : A → Prop) {dec : ∀ x, Decision (P x)} : ∀ l, Decision (Forall P l) :=
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

Global Instance Exists_dec (P : A → Prop) {dec : ∀ x, Decision (P x)} : ∀ l, Decision (Exists P l) :=
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

Definition prefix_of (l1 l2 : list A) : Prop := ∃ k, l2 = l1 ++ k.
Definition suffix_of (l1 l2 : list A) : Prop := ∃ k, l2 = k ++ l1.

Global Instance: PreOrder prefix_of.
Proof.
  split.
   intros ?. eexists []. now rewrite app_nil_r.
  intros ??? [k1 ?] [k2 ?]. exists (k1 ++ k2). subst. now rewrite app_assoc.
Qed.

Lemma prefix_of_nil l : prefix_of [] l.
Proof. now exists l. Qed.
Lemma prefix_of_nil_not x l : ¬prefix_of (x :: l) [].
Proof. intros [k E]. discriminate. Qed.
Lemma prefix_of_cons x y l1 l2 : x = y → prefix_of l1 l2 → prefix_of (x :: l1) (y :: l2).
Proof. intros ? [k E]. exists k. now subst. Qed.
Lemma prefix_of_cons_inv_1 x y l1 l2 : prefix_of (x :: l1) (y :: l2) → x = y.
Proof. intros [k E]. now injection E. Qed.
Lemma prefix_of_cons_inv_2 x y l1 l2 : prefix_of (x :: l1) (y :: l2) → prefix_of l1 l2.
Proof. intros [k E]. exists k. now injection E. Qed.

Lemma prefix_of_app_l l1 l2 l3 : prefix_of (l1 ++ l3) l2 → prefix_of l1 l2.
Proof. intros [k ?]. red. exists (l3 ++ k). subst. now rewrite <-app_assoc. Qed.
Lemma prefix_of_app_r l1 l2 l3 : prefix_of l1 l2 → prefix_of l1 (l2 ++ l3).
Proof. intros [k ?]. exists (k ++ l3). subst. now rewrite app_assoc. Qed.

Global Instance prefix_of_dec `{∀ x y : A, Decision (x = y)} : ∀ l1 l2, Decision (prefix_of l1 l2) :=
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

Global Instance: PreOrder suffix_of.
Proof.
  split.
   intros ?. now eexists [].
  intros ??? [k1 ?] [k2 ?]. exists (k2 ++ k1). subst. now rewrite app_assoc.
Qed.

Lemma prefix_suffix_rev l1 l2 : prefix_of l1 l2 ↔ suffix_of (rev l1) (rev l2).
Proof.
  split; intros [k E]; exists (rev k).
   now rewrite E, rev_app_distr.
  now rewrite <-(rev_involutive l2), E, rev_app_distr, rev_involutive.
Qed.
Lemma suffix_prefix_rev l1 l2 : suffix_of l1 l2 ↔ prefix_of (rev l1) (rev l2).
Proof. now rewrite prefix_suffix_rev, !rev_involutive. Qed.

Lemma suffix_of_nil l : suffix_of [] l.
Proof. exists l. now rewrite app_nil_r. Qed.
Lemma suffix_of_nil_not x l : ¬suffix_of (x :: l) [].
Proof. intros [[] ?]; discriminate. Qed.
Lemma suffix_of_cons x y l1 l2 : x = y → suffix_of l1 l2 → suffix_of (l1 ++ [x]) (l2 ++ [y]).
Proof. intros ? [k E]. exists k. subst. now rewrite app_assoc. Qed.
Lemma suffix_of_snoc_inv_1 x y l1 l2 : suffix_of (l1 ++ [x]) (l2 ++ [y]) → x = y.
Proof. rewrite suffix_prefix_rev, !rev_unit. now apply prefix_of_cons_inv_1. Qed.
Lemma suffix_of_snoc_inv_2 x y l1 l2 : suffix_of (l1 ++ [x]) (l2 ++ [y]) → suffix_of l1 l2.
Proof. rewrite !suffix_prefix_rev, !rev_unit. now apply prefix_of_cons_inv_2. Qed.

Lemma suffix_of_cons_l l1 l2 x : suffix_of (x :: l1) l2 → suffix_of l1 l2.
Proof. intros [k ?]. exists (k ++ [x]). subst. now rewrite <-app_assoc. Qed.
Lemma suffix_of_app_l l1 l2 l3 : suffix_of (l3 ++ l1) l2 → suffix_of l1 l2.
Proof. intros [k ?]. exists (k ++ l3). subst. now rewrite <-app_assoc. Qed.
Lemma suffix_of_cons_r l1 l2 x : suffix_of l1 l2 → suffix_of l1 (x :: l2).
Proof. intros [k ?]. exists (x :: k). now subst. Qed.
Lemma suffix_of_app_r l1 l2 l3 : suffix_of l1 l2 → suffix_of l1 (l3 ++ l2).
Proof. intros [k ?]. exists (l3 ++ k). subst. now rewrite app_assoc. Qed.

Lemma suffix_of_cons_inv l1 l2 x y : 
  suffix_of (x :: l1) (y :: l2) → x :: l1 = y :: l2 ∨ suffix_of (x :: l1) l2.
Proof.
  intros [[|? k] E].
   now left.
  right. simplify_eqs. now apply suffix_of_app_r.
Qed.
Lemma suffix_of_cons_not x l : ¬suffix_of (x :: l) l.
Proof.
  intros [k E]. change ([] ++ l = k ++ [x] ++ l) in E.
  rewrite app_assoc in E. apply app_inv_tail in E.
  destruct k; simplify_eqs.
Qed.

Global Program Instance suffix_of_dec `{∀ x y : A, Decision (x = y)} l1 l2 : Decision (suffix_of l1 l2) :=
  match decide_rel prefix_of (rev_append l1 []) (rev_append l2 []) with
  | left Hpre => left _
  | right Hpre => right _
  end.
Next Obligation. apply suffix_prefix_rev. now rewrite !rev_alt. Qed.
Next Obligation. intro. destruct Hpre. rewrite <-!rev_alt. now apply suffix_prefix_rev. Qed.
End list_properties.

Hint Resolve suffix_of_nil suffix_of_cons_r suffix_of_app_r : list.
Hint Extern 0 (prefix_of _ _) => reflexivity : list.
Hint Extern 0 (suffix_of _ _) => reflexivity: list.
Hint Extern 0 (PropHolds (suffix_of _ _)) => red; auto with list : typeclass_instances.

Ltac simplify_suffix_of := repeat
  match goal with
  | H : suffix_of (_ :: _) _ |- _ => destruct (suffix_of_cons_not _ _ H); clear H
  | H : suffix_of (_ :: _) [] |- _ => destruct (suffix_of_nil_not _ _ H); clear H
  | H : suffix_of (_ :: _) (_ :: _) |- _ => destruct (suffix_of_cons_inv _ _ _ _ H); clear H
  | H : suffix_of ?x ?x |- _ => clear H
  | H : suffix_of ?x (_ :: ?x) |- _ => clear H
  | H : suffix_of ?x (_ ++ ?x) |- _ => clear H
  | _ => progress simplify_eqs
  end.

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
Local Arguments lookup _ _ _ _ _ !_ /.

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

Lemma list_eq {A} (l1 l2 : list A) : (∀ i, l1 !! i = l2 !! i) → l1 = l2.
Proof.
  revert l2. induction l1; intros [|??] H.
     easy.
    discriminate (H 0).
   discriminate (H 0).
  f_equal. now injection (H 0). apply IHl1. intro. apply (H (S _)).
Qed.

Lemma list_lookup_tail {A} (l : list A) i : tail l !! i = l !! S i.
Proof. now destruct l. Qed.

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

Lemma list_lookup_weaken {A} (l l' : list A) i x :
  l !! i = Some x → (l ++ l') !! i = Some x.
Proof. revert i. induction l. discriminate. now intros []. Qed.

Lemma list_lookup_fmap {A B} (f : A → B) l i : (f <$> l) !! i = f <$> (l !! i).
Proof. revert i. induction l; now intros [|]. Qed.

Lemma fold_right_permutation `(f : A → B → B) (b : B) :
  (∀ a1 a2 b, f a1 (f a2 b) = f a2 (f a1 b)) → Proper (Permutation ==> (=)) (fold_right f b).
Proof. intros Hflip. induction 1; simpl; try congruence. Qed.

(*
Section NoDupA.
  Fixpoint removeDups (l : list A) : list A :=
    match l with
    | [] => []
    | x :: l =>
      let k := removeDups l in
      if InA_dec dec x k then k else x :: k
    end.

  Lemma removeDups_NoDupA l : NoDupA R (removeDups l).
  Proof. induction l; simpl; try case InA_dec; intuition. Qed.

  Definition elem_removeDups x l : x ∈ removeDups l → x ∈ l.
  Proof.
    induction l; simpl; auto.
    case InA_dec; eauto.
    intros ? Hin. destruct (list_elem_inv _ _ _ Hin); subst; eauto.
  Qed.

  Lemma elem_InA x y l : x ∈ l → R y x → InA R y l.
  Proof. induction 1; subst; intuition. Qed.

  Lemma InA_elem x l : InA R x l → ∃ y, y ∈ l ∧ R x y.
  Proof. induction 1. eauto. destruct IHInA as [? [??]]; eauto. Qed.

  Context `{!Equivalence R}.

  Lemma in_removeDups_inv x l : x ∈ l → ∃ y, y ∈ l ∧ R x y ∧ y ∈ removeDups l.
  Proof.
    induction l as [|y l]; simpl.
     inversion 1.
    case InA_dec.
     inversion 2; subst.
      destruct (InA_elem y (removeDups l)) as [z [??]]; auto.
      exists z. intuition. right. now apply elem_removeDups.
     destruct IHl as [z [?[??]]]. auto. exists z. intuition.
    intros ? Hin. destruct (list_elem_inv _ _ _ Hin).
     subst. exists y. intuition.
    destruct IHl as [z [?[??]]]. easy. exists z. intuition.
  Qed.

  Lemma in_removeDups x l : InA R x l ↔ InA R x (removeDups l).
  Proof.
    split.
     induction 1 as [?? E|]; simpl; [rewrite E|]; case InA_dec; intuition.
    induction l; simpl; auto.
    case InA_dec. auto. inversion_clear 2; auto.
  Qed.
End NoDupA.

Lemma InA_lift_rel {A B} (R : relation A) (f : B → A) x l : InA R (f x) (f <$> l) ↔ InA (lift_rel R f) x l.
Proof. split; induction l; unfold fmap; simpl; inversion_clear 1; auto. Qed.

Lemma NoDupA_lift_rel {A B} (R : relation A) (f : B → A) l : NoDupA R (f <$> l) ↔ NoDupA (lift_rel R f) l.
Proof.
  split.
   induction l; [easy |].
   intros HnoDup. constructor.
    intro. destruct (NoDupA_inv_1 R _ _ HnoDup). now apply InA_lift_rel.
   eapply IHl, NoDupA_inv_2; eauto.
  induction 1; constructor. now rewrite InA_lift_rel. easy.
Qed.
*)
