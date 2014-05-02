(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export references.
Require Import fin_map_dom nmap mapset.

(** * Indexes into the memory *)
(** We define indexes into the memory as binary naturals and use the [Nmap]
implementation to obtain efficient finite maps and finite sets with these
indexes as keys. *)
Definition index := N.
Definition indexmap := Nmap.
Notation indexset := (mapset indexmap).

Instance index_dec: ∀ o1 o2 : index, Decision (o1 = o2) := decide_rel (=).
Instance index_fresh_`{FinCollection index C} : Fresh index C := _.
Instance index_fresh_spec `{FinCollection index C} : FreshSpec index C := _.
Instance index_inhabited: Inhabited index := populate 0%N.
Instance indexmap_dec {A} `{∀ a1 a2 : A, Decision (a1 = a2)} :
  ∀ m1 m2 : indexmap A, Decision (m1 = m2) := decide_rel (=).
Instance indexmap_empty {A} : Empty (indexmap A) := @empty (Nmap A) _.
Instance indexmap_lookup {A} : Lookup index A (indexmap A) :=
  @lookup _ _ (Nmap A) _.
Instance indexmap_partial_alter {A} : PartialAlter index A (indexmap A) :=
  @partial_alter _ _ (Nmap A) _.
Instance indexmap_to_list {A} : FinMapToList index A (indexmap A) :=
  @map_to_list _ _ (Nmap A) _.
Instance indexmap_omap: OMap indexmap := λ A B f, @omap Nmap _ _ f _.
Instance indexmap_merge: Merge indexmap := @merge Nmap _.
Instance indexmap_fmap: FMap indexmap := λ A B f, @fmap Nmap _ _ f _.
Instance: FinMap index indexmap := _.
Instance indexmap_dom {A} : Dom (indexmap A) indexset := mapset_dom.
Instance: FinMapDom index indexmap indexset := mapset_dom_spec.
Instance index_lexico : Lexico index := @lexico N _.
Instance index_lexico_order : StrictOrder (@lexico index _) := _.
Instance index_trichotomy: TrichotomyT (@lexico index _) := _.
Typeclasses Opaque index indexmap.

Inductive mem_inj (Ti : Set) :=
  | mem_inj_id : mem_inj Ti
  | mem_inj_map : indexmap (index * ref Ti) → mem_inj Ti.
Arguments mem_inj_id {_}.
Arguments mem_inj_map {_} _.
Instance mem_inj_dec {Ti : Set} `{∀ τi1 τi2 : Ti, Decision (τi1 = τi2)}
  (f g : mem_inj Ti) : Decision (f = g).
Proof. solve_decision. Defined.
Instance mem_inj_lookup {Ti} : Lookup index (index * ref Ti) (mem_inj Ti) :=
  λ o f, match f with mem_inj_id => Some (o, []) | mem_inj_map m => m !! o end.
Definition mem_inj_compose {Ti} (f g : mem_inj Ti) : mem_inj Ti :=
  match f, g with
  | mem_inj_id, mem_inj_id => mem_inj_id
  | mem_inj_map m, mem_inj_id => mem_inj_map m
  | mem_inj_id, mem_inj_map m => mem_inj_map m
  | mem_inj_map m1, mem_inj_map m2 => mem_inj_map $
     merge (λ yr _ : option (index * ref Ti),
       '(y1,r1) ← yr; '(y2,r2) ← m2 !! y1; Some (y2, r1 ++ r2)) m1 ∅
  end.
Arguments mem_inj_compose _ !_ !_ /.
Infix "◎" := mem_inj_compose (at level 40, left associativity) : C_scope.
Notation "(◎)" := mem_inj_compose (only parsing) : C_scope.

Definition mem_inj_injective {Ti} (f : mem_inj Ti) : Prop := ∀ o1 o2 o r1 r2,
  f !! o1 = Some (o,r1) → f !! o2 = Some (o,r2) → o1 = o2 ∨ r1 ⊥ r2.

Section mem_inj.
Context {Ti : Set}.
Implicit Types f g : mem_inj Ti.
Implicit Types o : index.
Implicit Types r : ref Ti.

Lemma mem_inj_eq f g : (∀ o, f !! o = g !! o) → f = g.
Proof.
  intros Hfg. destruct f as [|m1], g as [|m2].
  * done.
  * generalize (Hfg (fresh (dom _ m2))); unfold lookup; simpl.
    by rewrite (proj1 (not_elem_of_dom _ _)) by (apply is_fresh).
  * generalize (Hfg (fresh (dom _ m1))); unfold lookup; simpl.
    by rewrite (proj1 (not_elem_of_dom _ _)) by (apply is_fresh).
  * f_equal. apply map_eq, Hfg.
Qed.

Lemma lookup_mem_inj_id o : @mem_inj_id Ti !! o = Some (o, []).
Proof. done. Qed.
Lemma lookup_mem_inj_id_Some o1 o2 r :
  mem_inj_id !! o1 = Some (o2,r) ↔ o2 = o1 ∧ r = [].
Proof. naive_solver. Qed.
Lemma lookup_mem_inj_compose f g o :
  (f ◎ g) !! o = '(y1,r1) ← f !! o; '(y2,r2) ← g !! y1; Some (y2,r1 ++ r2).
Proof.
  unfold lookup; destruct f as [|m1], g as [|m2]; simpl.
  * done.
  * by destruct (_ !! o) as [[??]|].
  * by destruct (_ !! o) as [[??]|]; simpl; rewrite ?(right_id_L [] (++)).
  * by rewrite lookup_merge by done.
Qed.
Lemma lookup_mem_inj_compose_Some f g o1 o3 r :
  (f ◎ g) !! o1 = Some (o3,r) ↔
  ∃ o2 r2 r3, f !! o1 = Some (o2,r2) ∧ g !! o2 = Some (o3,r3) ∧ r = r2 ++ r3.
Proof.
  rewrite lookup_mem_inj_compose. split.
  * intros. destruct (f !! o1) as [[o2 r2]|] eqn:?; simplify_equality'.
    destruct (g !! o2) as [[??]|] eqn:?; naive_solver.
  * by intros (?&?&?&?&?&?); simplify_option_equality.
Qed.

Global Instance: LeftId (@eq (mem_inj Ti)) mem_inj_id (◎).
Proof. by intros []. Qed.
Global Instance: RightId (@eq (mem_inj Ti)) mem_inj_id (◎).
Proof. by intros []. Qed.
Global Instance: Associative (@eq (mem_inj Ti)) (◎).
Proof.
  intros f g h. apply mem_inj_eq. intros o1. rewrite !lookup_mem_inj_compose.
  destruct (f !! o1) as [[o2 r2]|]; simpl; [|done].
  rewrite !lookup_mem_inj_compose.
  destruct (g !! o2) as [[o3 r3]|]; simpl; [|done].
  by destruct (h !! o3) as [[??]|]; simpl; rewrite ?(associative_L (++)).
Qed.
Lemma mem_inj_positive_l f g : f ◎ g = mem_inj_id → f = mem_inj_id.
Proof. by destruct f, g. Qed.
Lemma mem_inj_positive_r f g : f ◎ g = mem_inj_id → g = mem_inj_id.
Proof. by destruct f, g. Qed.

Lemma mem_inj_id_injective : mem_inj_injective (@mem_inj_id Ti).
Proof. intros x1 x2 y r1 r2 ??; simplify_equality'; auto. Qed.
Lemma mem_inj_compose_injective f g :
  mem_inj_injective f → mem_inj_injective g → mem_inj_injective (f ◎ g).
Proof.
  intros Hf Hg o1 o2 o r1 r2; rewrite !lookup_mem_inj_compose_Some.
  intros (o1'&r1'&r1''&?&?&->) (o2'&r2'&r2''&?&?&->).
  destruct (decide (o1 = o2)); [by left|].
  destruct (Hg o1' o2' o r1'' r2'') as [->|?]; simplify_equality'; auto.
  { destruct (Hf o1 o2 o2' r1' r2') as [->|?]; auto.
    right. by apply ref_disjoint_here_app_1. }
  right. by apply ref_disjoint_app_l, ref_disjoint_app_r.
Qed.
Lemma mem_inj_injective_alt f o1 o2 o r1 r2 :
  mem_inj_injective f → f !! o1 = Some (o,r1) → f !! o2 = Some (o,r2) →
  o1 = o2 ∨ o1 ≠ o2 ∧ r1 ⊥ r2.
Proof.
  intros Hf ??. destruct (decide (o1 = o2)); [by left|].
  destruct (Hf o1 o2 o r1 r2); auto.
Qed.
Lemma mem_inj_injective_ne f o1 o2 o3 o4 r2 r4 :
  mem_inj_injective f → f !! o1 = Some (o2,r2) → f !! o3 = Some (o4,r4) →
  o1 ≠ o3 → o2 ≠ o4 ∨ o2 = o4 ∧ r2 ⊥ r4.
Proof.
  intros Hf ???. destruct (decide (o2 = o4)) as [->|]; auto.
  destruct (Hf o1 o3 o4 r2 r4); auto.
Qed.
End mem_inj.

Class Refine Ti A := refine: env Ti → mem_inj Ti → relation A.
Class RefineT Ti A T := refineT: env Ti → mem_inj Ti → A → A → T → Prop.
Instance: Params (@refine) 5.
Instance: Params (@refineT) 6.

Notation "X ⊑{ Γ , f } Y" := (refine Γ f X Y)
  (at level 70, format "X  ⊑{ Γ , f }  Y") : C_scope.
Notation "Xs ⊑{ Γ , f }* Ys" := (Forall2 (refine Γ f) Xs Ys)
  (at level 70, format "Xs  ⊑{ Γ , f }*  Ys") : C_scope.
Notation "Xss ⊑{ Γ , f }2** Yss" :=
  (Forall2 (λ Xs Ys, Xs.2 ⊑{Γ,f}* Ys.2) Xss Yss)
  (at level 70, format "Xss  ⊑{ Γ , f }2**  Yss") : C_scope.
Notation "X ⊑{ Γ } Y" := (X ⊑{Γ,mem_inj_id} Y)
  (at level 70, format "X  ⊑{ Γ }  Y") : C_scope.
Notation "Xs ⊑{ Γ }* Ys" := (Xs ⊑{Γ,mem_inj_id}* Ys)
  (at level 70, format "Xs  ⊑{ Γ }*  Ys") : C_scope.
Notation "Xs ⊑{ Γ }1* Ys" := (Xs ⊑{Γ,mem_inj_id}1* Ys)
  (at level 70, format "Xs  ⊑{ Γ }1*  Ys") : C_scope.
Notation "Xss ⊑{ Γ }2** Yss" := (Xss ⊑{Γ,mem_inj_id}2** Yss)
  (at level 70, format "Xss  ⊑{ Γ }2**  Yss") : C_scope.
Notation "X ⊑{ Γ , f } Y : τ" := (refineT Γ f X Y τ)
  (at level 70, Y at next level, format "X  ⊑{ Γ , f }  Y  :  τ") : C_scope.
Notation "Xs ⊑{ Γ , f }* Ys : τ" := (Forall2 (λ X Y, X ⊑{Γ,f} Y : τ) Xs Ys)
  (at level 70, Ys at next level, format "Xs  ⊑{ Γ , f }*  Ys  :  τ") : C_scope.
Notation "Xs ⊑{ Γ , f }* Ys :* τs" := (Forall3 (refineT Γ f) Xs Ys τs)
  (at level 70, Ys at next level,
   format "Xs  ⊑{ Γ , f }*  Ys  :*  τs") : C_scope.
Notation "Xs ⊑{ Γ , f }1* Ys :* τs" :=
  (Forall3 (λ X Y τ, X.1 ⊑{Γ,f} Y.1 : τ) Xs Ys τs)
  (at level 70, Ys at next level,
   format "Xs  ⊑{ Γ , f }1*  Ys  :*  τs") : C_scope.
Notation "X ⊑{ Γ } Y : τ" := (X ⊑{Γ,mem_inj_id} Y : τ)
  (at level 70, Y at next level, format "X  ⊑{ Γ }  Y  :  τ") : C_scope.
Notation "Xs ⊑{ Γ }* Ys : τ" := (Xs ⊑{Γ,mem_inj_id}* Ys : τ)
  (at level 70, Ys at next level, format "Xs  ⊑{ Γ }*  Ys  :  τ") : C_scope.
Notation "Xs ⊑{ Γ }* Ys :* τs" := (Xs ⊑{Γ,mem_inj_id}* Ys : τs)
  (at level 70, Ys at next level, format "Xs  ⊑{ Γ }*  Ys  :*  τs") : C_scope.
Notation "Xs ⊑{ Γ }1* Ys :* τs" := (Xs ⊑{Γ,mem_inj_id}1* Ys :* τs)
  (at level 70, Ys at next level, format "Xs  ⊑{ Γ }1*  Ys  :*  τs") : C_scope.

Class TypeOfIndex (Ti : Set) (M : Type) :=
  type_of_index : M → index → option (type Ti).
Class IndexAlive (M : Type) :=
  index_alive : M → index → Prop.
Definition type_of_object {Ti : Set} `{∀ τi1 τi2 : Ti, Decision (τi1 = τi2)}
    `{TypeOfIndex Ti M} (Γ : env Ti)
    (m : M) (o : index) (r : ref Ti) : option (type Ti) :=
  type_of_index m o ≫= lookupE Γ r.

Class MemSpec (Ti : Set) M `{TypeOfIndex Ti M,
    Refine Ti M, IndexAlive M, IntEnv Ti, PtrEnv Ti,
    ∀ m o, Decision (index_alive m o)} `{EnvSpec Ti} := {
  mem_refine_alive Γ m1 m2 f o1 o2 r :
    ✓ Γ → m1 ⊑{Γ,f} m2 → f !! o1 = Some (o2,r) →
    index_alive m1 o1 → index_alive m2 o2
}.

Section mem_spec.
Context `{MemSpec Ti}.
Implicit Types o : index.
Implicit Types m : M.
Implicit Types r : ref Ti.
Implicit Types τ σ : type Ti.

Lemma type_of_object_Some Γ m o r τ :
  type_of_object Γ m o r = Some τ ↔
    ∃ σ, type_of_index m o = Some σ ∧ Γ ⊢ r : σ ↣ τ.
Proof.
  unfold type_of_object. split.
  * intros; simplify_option_equality; eexists; split; eauto.
    by apply path_type_check_sound.
  * intros (?&->&?); by apply path_type_check_complete.
Qed.
Lemma type_of_object_Some_1 Γ m o r τ :
  type_of_object Γ m o r = Some τ →
    ∃ σ, type_of_index m o = Some σ ∧ Γ ⊢ r : σ ↣ τ.
Proof. by rewrite type_of_object_Some. Qed.
Lemma type_of_object_Some_2 Γ m o σ r τ :
  type_of_index m o = Some σ ∧ Γ ⊢ r : σ ↣ τ →
  type_of_object Γ m o r = Some τ.
Proof. rewrite type_of_object_Some; eauto. Qed.
Lemma type_of_object_nil Γ m o :
  type_of_object Γ m o (@nil (ref_seg Ti)) = type_of_index m o.
Proof.
  unfold type_of_object. by rewrite list_path_lookup_nil, bind_with_Some.
Qed.
Lemma type_of_object_cons Γ m o rs r :
  type_of_object Γ m o (rs :: r) = type_of_object Γ m o r ≫= lookupE Γ rs.
Proof.
  unfold type_of_object. by rewrite list_path_lookup_cons, option_bind_assoc.
Qed.
Lemma type_of_object_weaken Γ1 Γ2 m1 m2 o r σ :
  ✓ Γ1 → type_of_object Γ1 m1 o r = Some σ → Γ1 ⊆ Γ2 →
  (∀ o σ, type_of_index m1 o = Some σ → type_of_index m2 o = Some σ) →
  type_of_object Γ2 m2 o r = Some σ.
Proof.
  unfold type_of_object; intros ??? Hm; simplify_option_equality.
  eauto using ref_lookup_weaken.
Qed.
Lemma type_of_object_set_offset Γ m o r σ i :
  i < ref_size r → type_of_object Γ m o r = Some σ →
  type_of_object Γ m o (ref_set_offset i r) = Some σ.
Proof.
  unfold type_of_object; intros.
  destruct (type_of_index m o) as [τ|] eqn:?; simplify_equality'.
  apply path_type_check_correct, ref_set_offset_typed; auto.
  by apply path_type_check_correct.
Qed.
Lemma type_of_object_freeze Γ m q o r :
  type_of_object Γ m o (freeze q <$> r) = type_of_object Γ m o r.
Proof. unfold type_of_object. by rewrite ref_lookup_freeze. Qed.
End mem_spec.
