Require Export base orders.

Section collection.
  Context `{Collection A B}.

  Lemma elem_of_empty_iff x : x ∈ ∅ ↔ False.
  Proof. split. apply elem_of_empty. easy. Qed.

  Lemma elem_of_union_l x X Y : x ∈ X → x ∈ X ∪ Y.
  Proof. intros. apply elem_of_union. auto. Qed.
  Lemma elem_of_union_r x X Y : x ∈ Y → x ∈ X ∪ Y.
  Proof. intros. apply elem_of_union. auto. Qed.

  Global Instance collection_subseteq: SubsetEq B := λ X Y, ∀ x, x ∈ X → x ∈ Y.
  Global Instance: BoundedJoinSemiLattice B.
  Proof. firstorder. Qed.
  Global Instance: MeetSemiLattice B.
  Proof. firstorder. Qed.

  Lemma elem_of_subseteq X Y : X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y.
  Proof. easy. Qed.
  Lemma elem_of_equiv X Y : X ≡ Y ↔ ∀ x, x ∈ X ↔ x ∈ Y.
  Proof. firstorder. Qed.
  Lemma elem_of_equiv_alt X Y :
    X ≡ Y ↔ (∀ x, x ∈ X → x ∈ Y) ∧ (∀ x, x ∈ Y → x ∈ X).
  Proof. firstorder. Qed.

  Global Instance: Proper ((=) ==> (≡) ==> iff) (∈).
  Proof. intros ???. subst. firstorder. Qed.

  Lemma empty_ne_singleton x :  ∅ ≢ {[ x ]}.
  Proof.
    intros [_ E]. destruct (elem_of_empty x).
    apply E. now apply elem_of_singleton.
  Qed. 
End collection.

Section cmap.
  Context `{Collection A C}.

  Lemma elem_of_map_1 (f : A → A) (X : C) (x : A) :
    x ∈ X → f x ∈ map f X.
  Proof. intros. apply (elem_of_map _). eauto. Qed.
  Lemma elem_of_map_1_alt (f : A → A) (X : C) (x : A) y :
    x ∈ X → y = f x → y ∈ map f X.
  Proof. intros. apply (elem_of_map _). eauto. Qed.
  Lemma elem_of_map_2 (f : A → A) (X : C) (x : A) :
    x ∈ map f X → ∃ y, x = f y ∧ y ∈ X.
  Proof. intros. now apply (elem_of_map _). Qed.
End cmap.

Definition fresh_sig `{FreshSpec A C} (X : C) : { x : A | x ∉ X } :=
  exist (∉ X) (fresh X) (is_fresh X).

Lemma elem_of_fresh_iff `{FreshSpec A C} (X : C) : fresh X ∈ X ↔ False.
Proof. split. apply is_fresh. easy. Qed.

Ltac split_elem_ofs := repeat
  match goal with
  | H : context [ _ ⊆ _ ] |- _ => setoid_rewrite elem_of_subseteq in H
  | H : context [ _ ≡ _ ] |- _ => setoid_rewrite elem_of_equiv_alt in H
  | H : context [ _ ∈ ∅ ] |- _ => setoid_rewrite elem_of_empty_iff in H
  | H : context [ _ ∈ {[ _ ]} ] |- _ => setoid_rewrite elem_of_singleton in H
  | H : context [ _ ∈ _ ∪ _ ] |- _ => setoid_rewrite elem_of_union in H
  | H : context [ _ ∈ _ ∩ _ ] |- _ => setoid_rewrite elem_of_intersection in H
  | H : context [ _ ∈ _ ∖ _ ] |- _ => setoid_rewrite elem_of_difference in H
  | H : context [ _ ∈ map _ _ ] |- _ => setoid_rewrite elem_of_map in H
  | |- context [ _ ⊆ _ ] => setoid_rewrite elem_of_subseteq
  | |- context [ _ ≡ _ ] => setoid_rewrite elem_of_equiv_alt
  | |- context [ _ ∈ ∅ ] => setoid_rewrite elem_of_empty_iff
  | |- context [ _ ∈ {[ _ ]} ] => setoid_rewrite elem_of_singleton
  | |- context [ _ ∈ _ ∪ _ ] => setoid_rewrite elem_of_union
  | |- context [ _ ∈ _ ∩ _ ] => setoid_rewrite elem_of_intersection
  | |- context [ _ ∈ _ ∖ _ ] => setoid_rewrite elem_of_difference
  | |- context [ _ ∈ map _ _ ] => setoid_rewrite elem_of_map
  end.

Ltac destruct_elem_ofs := repeat
  match goal with
  | H : context [ @elem_of (_ * _) _ _ ?x _ ] |- _ => is_var x; destruct x
  | H : context [ @elem_of (_ + _) _ _ ?x _] |- _ => is_var x; destruct x
  end.

Tactic Notation "simplify_elem_of" tactic(t) :=
  intros; (* due to bug #2790 *)
  simpl in *;
  split_elem_ofs;
  destruct_elem_ofs;
  intuition (simplify_eqs; t).
Tactic Notation "simplify_elem_of" := simplify_elem_of auto.

Ltac naive_firstorder t :=
  match goal with
  (* intros *)
  | |- ∀ _, _ => intro; naive_firstorder t
  (* destructs without information loss *)
  | H : False |- _ => destruct H
  | H : ?X, Hneg : ¬?X|- _ => now destruct Hneg
  | H : _ ∧ _ |- _ => destruct H; naive_firstorder t
  | H : ∃ _, _  |- _ => destruct H; naive_firstorder t
  (* simplification *)
  | |- _ => progress (simplify_eqs; simpl in *); naive_firstorder t
  (* constructs *)
  | |- _ ∧ _ => split; naive_firstorder t
  (* solve *)
  | |- _ => solve [t]
  (* dirty destructs *)
  | H : context [ ∃ _, _ ] |- _ =>
    edestruct H; clear H;naive_firstorder t || clear H; naive_firstorder t
  | H : context [ _ ∧ _ ] |- _ => 
    destruct H; clear H; naive_firstorder t || clear H; naive_firstorder t
  | H : context [ _ ∨ _ ] |- _ =>
    edestruct H; clear H; naive_firstorder t || clear H; naive_firstorder t
  (* dirty constructs *)
  | |- ∃ x, _ => eexists; naive_firstorder t
  | |- _ ∨ _ => left; naive_firstorder t || right; naive_firstorder t
  | H : _ → False |- _ => destruct H; naive_firstorder t
  end.
Tactic Notation "naive_firstorder" tactic(t) :=
  unfold iff, not in *; 
  naive_firstorder t.

Tactic Notation "esimplify_elem_of" tactic(t) := 
  (simplify_elem_of t); 
  try naive_firstorder t.
Tactic Notation "esimplify_elem_of" := esimplify_elem_of (eauto 5).

Section no_dup.
  Context `{Collection A B} (R : relation A) `{!Equivalence R}.

  Definition elem_of_upto (x : A) (X : B) := ∃ y, y ∈ X ∧ R x y.
  Definition no_dup (X : B) := ∀ x y, x ∈ X → y ∈ X → R x y → x = y.

  Global Instance: Proper ((≡) ==> iff) (elem_of_upto x).
  Proof. firstorder. Qed.
  Global Instance: Proper (R ==> (≡) ==> iff) elem_of_upto.
  Proof.
    intros ?? E1 ?? E2. split; intros [z [??]]; exists z.
    * rewrite <-E1, <-E2; intuition.
    * rewrite E1, E2; intuition.
  Qed.
  Global Instance: Proper ((≡) ==> iff) no_dup.
  Proof. firstorder. Qed.

  Lemma elem_of_upto_elem_of x X : x ∈ X → elem_of_upto x X.
  Proof. unfold elem_of_upto. esimplify_elem_of. Qed.
  Lemma elem_of_upto_empty x : ¬elem_of_upto x ∅.
  Proof. unfold elem_of_upto. esimplify_elem_of. Qed.
  Lemma elem_of_upto_singleton x y : elem_of_upto x {[ y ]} ↔ R x y.
  Proof. unfold elem_of_upto. esimplify_elem_of. Qed.

  Lemma elem_of_upto_union X Y x :
    elem_of_upto x (X ∪ Y) ↔ elem_of_upto x X ∨ elem_of_upto x Y.
  Proof. unfold elem_of_upto. esimplify_elem_of. Qed.
  Lemma not_elem_of_upto x X : ¬elem_of_upto x X → ∀ y, y ∈ X → ¬R x y.
  Proof. unfold elem_of_upto. esimplify_elem_of. Qed.

  Lemma no_dup_empty: no_dup ∅.
  Proof. unfold no_dup. simplify_elem_of. Qed.
  Lemma no_dup_add x X : ¬elem_of_upto x X → no_dup X → no_dup ({[ x ]} ∪ X).
  Proof. unfold no_dup, elem_of_upto. esimplify_elem_of. Qed.
  Lemma no_dup_inv_add x X : x ∉ X → no_dup ({[ x ]} ∪ X) → ¬elem_of_upto x X.
  Proof.
    intros Hin Hnodup [y [??]].
    rewrite (Hnodup x y) in Hin; simplify_elem_of.
  Qed.
  Lemma no_dup_inv_union_l X Y : no_dup (X ∪ Y) → no_dup X.
  Proof. unfold no_dup. simplify_elem_of. Qed.
  Lemma no_dup_inv_union_r X Y : no_dup (X ∪ Y) → no_dup Y.
  Proof. unfold no_dup. simplify_elem_of. Qed.
End no_dup.

Section quantifiers.
  Context `{Collection A B} (P : A → Prop).

  Definition cforall X := ∀ x, x ∈ X → P x.
  Definition cexists X := ∃ x, x ∈ X ∧ P x.

  Lemma cforall_empty : cforall ∅.
  Proof. unfold cforall. simplify_elem_of. Qed.
  Lemma cforall_singleton x : cforall {[ x ]} ↔ P x.
  Proof. unfold cforall. simplify_elem_of. Qed.
  Lemma cforall_union X Y : cforall X → cforall Y → cforall (X ∪ Y).
  Proof. unfold cforall. simplify_elem_of. Qed.
  Lemma cforall_union_inv_1 X Y : cforall (X ∪ Y) → cforall X.
  Proof. unfold cforall. simplify_elem_of. Qed.
  Lemma cforall_union_inv_2 X Y : cforall (X ∪ Y) → cforall Y.
  Proof. unfold cforall. simplify_elem_of. Qed.

  Lemma cexists_empty : ¬cexists ∅.
  Proof. unfold cexists. esimplify_elem_of. Qed.
  Lemma cexists_singleton x : cexists {[ x ]} ↔ P x.
  Proof. unfold cexists. esimplify_elem_of. Qed.
  Lemma cexists_union_1 X Y : cexists X → cexists (X ∪ Y).
  Proof. unfold cexists. esimplify_elem_of. Qed.
  Lemma cexists_union_2 X Y : cexists Y → cexists (X ∪ Y).
  Proof. unfold cexists. esimplify_elem_of. Qed.
  Lemma cexists_union_inv X Y : cexists (X ∪ Y) → cexists X ∨ cexists Y.
  Proof. unfold cexists. esimplify_elem_of. Qed.
End quantifiers.

Section more_quantifiers.
  Context `{Collection A B}.
  
  Lemma cforall_weak (P Q : A → Prop) (Hweak : ∀ x, P x → Q x) X :
    cforall P X → cforall Q X.
  Proof. firstorder. Qed.
  Lemma cexists_weak (P Q : A → Prop) (Hweak : ∀ x, P x → Q x) X :
    cexists P X → cexists Q X.
  Proof. firstorder. Qed.
End more_quantifiers.

Section fresh.
  Context `{Collection A C} `{Fresh A C} `{!FreshSpec A C} .

  Fixpoint fresh_list (n : nat) (X : C) : list A :=
    match n with
    | 0 => []
    | S n => let x := fresh X in x :: fresh_list n ({[ x ]} ∪ X)
    end.

  Lemma fresh_list_length n X : length (fresh_list n X) = n.
  Proof. revert X. induction n; simpl; auto. Qed.

  Lemma fresh_list_is_fresh n X x : In x (fresh_list n X) → x ∉ X.
  Proof.
    revert X. induction n; simpl.
    * easy.
    * intros X [?| Hin]. subst.
      + apply is_fresh.
      + apply IHn in Hin. simplify_elem_of.
  Qed.

  Lemma fresh_list_nodup n X : NoDup (fresh_list n X).
  Proof.
    revert X.
    induction n; simpl; constructor; auto.
    intros Hin. apply fresh_list_is_fresh in Hin.
    simplify_elem_of.
  Qed.
End fresh.
