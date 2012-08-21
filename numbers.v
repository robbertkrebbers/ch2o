Require Export PArith NArith ZArith.
Require Export base decidable fin_collections.

Infix "≤" := le : nat_scope.

Instance nat_eq_dec: ∀ x y : nat, Decision (x = y) := eq_nat_dec.
Instance positive_eq_dec: ∀ x y : positive, Decision (x = y) := Pos.eq_dec.
Notation "(~0)" := xO (only parsing) : positive_scope.
Notation "(~1)" := xI (only parsing) : positive_scope.

Infix "≤" := N.le : N_scope.
Notation "(≤)" := N.le (only parsing) : N_scope.

Instance N_eq_dec: ∀ x y : N, Decision (x = y) := N.eq_dec.
Program Instance N_le_dec (x y : N) : Decision (x ≤ y)%N :=
  match Ncompare x y with
  | Gt => right _
  | _ => left _
  end.
Next Obligation. congruence. Qed.

Infix "≤" := Z.le : Z_scope.
Notation "(≤)" := Z.le (only parsing) : Z_scope.
Instance Z_eq_dec: ∀ x y : Z, Decision (x = y) := Z.eq_dec.
Instance Z_le_dec: ∀ x y : Z, Decision (x ≤ y)%Z := Z_le_dec.

Definition Z_to_option_N (x : Z) :=
  match x with
  | Z0 => Some N0
  | Zpos p => Some (Npos p)
  | Zneg _ => None
  end.

Definition Nmax `{Elements N C} : C → N := collection_fold Nmax 0%N.

Instance Nmax_proper `{FinCollection N C} : Proper ((≡) ==> (=)) Nmax.
Proof.
  apply collection_fold_proper. intros.
  rewrite !N.max_assoc. f_equal. apply N.max_comm.
Qed.

Lemma Nmax_max `{FinCollection N C} X x : x ∈ X → (x ≤ Nmax X)%N.
Proof.
  change ((λ b X, x ∈ X → (x ≤ b)%N) (collection_fold N.max 0%N X) X).
  apply collection_fold_ind.
  * solve_proper.
  * simplify_elem_of.
  * simplify_elem_of. apply N.le_max_l. apply N.max_le_iff; auto.
Qed.

Instance Nfresh `{FinCollection N C} : Fresh N C := λ l, (1 + Nmax l)%N.
Instance Nfresh_spec `{FinCollection N C} : FreshSpec N C.
Proof.
  split.
  * intros. unfold fresh, Nfresh.
    setoid_replace X with Y; [easy |].
    now apply elem_of_equiv.
  * intros X E. assert (1 ≤ 0)%N as []; [| easy].
    apply N.add_le_mono_r with (Nmax X).
    now apply Nmax_max.
Qed.
