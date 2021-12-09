From stdpp Require Export fin_maps.
Require Import tactics.

Definition map_Forall2 `{∀ A, Lookup K A (M A)} {A B}
    (R : A → B → Prop) (P : A → Prop) (Q : B → Prop)
    (m1 : M A) (m2 : M B) : Prop := ∀ i,
  match m1 !! i, m2 !! i with
  | Some x, Some y => R x y
  | Some x, None => P x
  | None, Some y => Q y
  | None, None => True
  end.

Section Forall2.
Context `{FinMap K M}.
Context {A B} (R : A → B → Prop) (P : A → Prop) (Q : B → Prop).
Context `{∀ x y, Decision (R x y), ∀ x, Decision (P x), ∀ y, Decision (Q y)}.

Let f (mx : option A) (my : option B) : option bool :=
  match mx, my with
  | Some x, Some y => Some (bool_decide (R x y))
  | Some x, None => Some (bool_decide (P x))
  | None, Some y => Some (bool_decide (Q y))
  | None, None => None
  end.
Lemma map_Forall2_alt (m1 : M A) (m2 : M B) :
  map_Forall2 R P Q m1 m2 ↔ map_Forall (λ _, Is_true) (merge f m1 m2).
Proof.
  split.
  * intros Hm i P'; rewrite lookup_merge by done; intros.
    specialize (Hm i). destruct (m1 !! i), (m2 !! i);
      simplify_equality'; auto using bool_decide_pack.
  * intros Hm i. specialize (Hm i). rewrite lookup_merge in Hm by done.
    destruct (m1 !! i), (m2 !! i); simplify_equality'; auto;
      by eapply bool_decide_unpack, Hm.
Qed.

#[global] Instance map_Forall2_dec `{∀ x y, Decision (R x y), ∀ x, Decision (P x),
  ∀ y, Decision (Q y)} (m1: M A) (m2: M B): Decision (map_Forall2 R P Q m1 m2).
Proof.
  refine (cast_if (decide (map_Forall (λ _, Is_true) (merge f m1 m2))));
    abstract by rewrite map_Forall2_alt.
Defined.
End Forall2.