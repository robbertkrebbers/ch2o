(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export tactics.

CoInductive stream (A : Type) : Type := scons : A → stream A → stream A.
Arguments scons {_} _ _.
Delimit Scope stream_scope with stream.
Bind Scope stream_scope with stream.
Open Scope stream_scope.
Infix ":.:" := scons (at level 60, right associativity) : stream_scope.

Definition shead {A} (s : stream A) : A := match s with x :.: _ => x end.
Definition stail {A} (s : stream A) : stream A := match s with _ :.: s => s end.

CoInductive stream_equiv' {A} (s1 s2 : stream A) : Prop :=
  scons_equiv' :
    shead s1 = shead s2 → stream_equiv' (stail s1) (stail s2) →
    stream_equiv' s1 s2.
Instance stream_equiv {A} : Equiv (stream A) := stream_equiv'.

Reserved Infix "!.!" (at level 20).
Fixpoint slookup {A} (i : nat) (s : stream A) : A :=
  match i with O => shead s | S i => stail s !.! i end
where "s !.! i" := (slookup i s).

Global Instance stream_fmap : FMap stream := λ A B f,
  cofix go s := f (shead s) :.: go (stail s).

Fixpoint stake {A} (n : nat) (s : stream A) :=
  match n with 0 => [] | S n => shead s :: stake n (stail s) end.
CoFixpoint srepeat {A} (x : A) : stream A := x :.: srepeat x.

Section stream_properties.
Context {A : Type}.
Implicit Types x y : A.
Implicit Types s t : stream A.

Lemma scons_equiv s1 s2 : shead s1 = shead s2 → stail s1 ≡ stail s2 → s1 ≡ s2.
Proof. by constructor. Qed.
Global Instance equal_equivalence : Equivalence (@equiv (stream A) _).
Proof.
  split.
  * now cofix; intros [??]; constructor.
  * now cofix; intros ?? [??]; constructor.
  * cofix; intros ??? [??] [??]; constructor; etransitivity; eauto.
Qed.
Global Instance scons_proper x : Proper ((≡) ==> (≡)) (scons x).
Proof. by constructor. Qed.
Global Instance shead_proper : Proper ((≡) ==> (=)) (@shead A).
Proof. by intros ?? [??]. Qed.
Global Instance stail_proper : Proper ((≡) ==> (≡)) (@stail A).
Proof. by intros ?? [??]. Qed.
Global Instance slookup_proper : Proper ((≡) ==> eq) (@slookup A i).
Proof. by induction i as [|i IH]; intros s1 s2 Hs; simpl; rewrite Hs. Qed.
End stream_properties.
