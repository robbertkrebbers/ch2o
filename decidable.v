Require Export base.

Definition decide_rel {A B} (R : A → B → Prop) 
  {dec : ∀ x y, Decision (R x y)} (x : A) (y : B) : Decision (R x y) := dec x y.

Ltac case_decide := 
  match goal with
  | H : context [@decide ?P ?dec] |- _ => case (@decide P dec) in *
  | H : context [@decide_rel _ _ ?R ?x ?y ?dec] |- _ => case (@decide_rel _ _ R x y dec) in *
  | |- context [@decide ?P ?dec] => case (@decide P dec) in *
  | |- context [@decide_rel _ _ ?R ?x ?y ?dec] => case (@decide_rel _ _ R x y dec) in *
  end.

Ltac solve_trivial_decision :=
  match goal with
  | [ |- Decision (?P) ] => apply _
  | [ |- sumbool ?P (¬?P) ] => change (Decision P); apply _
  end.
Ltac solve_decision :=
  first [solve_trivial_decision | unfold Decision; decide equality; solve_trivial_decision].

Program Instance True_dec: Decision True := left _.
Program Instance False_dec: Decision False := right _.
Program Instance prod_eq_dec `(A_dec : ∀ x y : A, Decision (x = y))
     `(B_dec : ∀ x y : B, Decision (x = y)) : ∀ x y : A * B, Decision (x = y) := λ x y,
  match A_dec (fst x) (fst y) with
  | left _ => match B_dec (snd x) (snd y) with left _ => left _ | right _ => right _ end
  | right _ => right _
  end.
Solve Obligations using (program_simpl; f_equal; firstorder).
Program Instance and_dec `(P_dec : Decision P) `(Q_dec : Decision Q) : Decision (P ∧ Q) :=
  match P_dec with
  | left _ => match Q_dec with left _ => left _ | right _ => right _ end
  | right _ => right _
  end.
Solve Obligations using (program_simpl; tauto).
Program Instance or_dec `(P_dec : Decision P) `(Q_dec : Decision Q) : Decision (P ∨ Q) :=
  match P_dec with
  | left _ => left _
  | right _ => match Q_dec with left _ => left _ | right _ => right _ end
  end.
Solve Obligations using (program_simpl; firstorder).

Definition bool_decide (P : Prop) {dec : Decision P} : bool := if dec then true else false.
Coercion Is_true : bool >-> Sortclass.
Lemma bool_decide_unpack (P : Prop) {dec : Decision P} : bool_decide P → P.
Proof. unfold bool_decide. now destruct dec. Qed.
Lemma bool_decide_pack (P : Prop) {dec : Decision P} : P → bool_decide P.
Proof. unfold bool_decide. now destruct dec. Qed.

Definition dsig `(P : A → Prop) `{∀ x : A, Decision (P x)} := { x | bool_decide (P x) }.
Definition proj2_dsig `{∀ x : A, Decision (P x)} (x : dsig P) : P (`x) := bool_decide_unpack _ (proj2_sig x).
Definition dexist `{∀ x : A, Decision (P x)} (x : A) (p : P x) : dsig P := x↾bool_decide_pack _ p.

Lemma proj1_dsig_inj {A} (P : A → Prop) x (Px : P x) y (Py : P y) : x↾Px = y↾Py → x = y.
Proof. now injection 1. Qed.
Lemma dsig_eq {A} (P : A → Prop) {dec : ∀ x, Decision (P x)} (x y : { x | bool_decide (P x) }) :
  `x = `y → x = y.
Proof.
  intros H1. destruct x as [x Hx], y as [y Hy]. simpl in *. subst.
  f_equal. revert Hx Hy. case (bool_decide (P y)). simpl. now intros [] []. easy.
Qed.
