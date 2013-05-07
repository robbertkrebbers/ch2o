(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** Given a finite set of binary naturals [N], we generate a fresh element by
taking the maximum, and adding one to it. We declare this operation as an
instance of the type class [Fresh]. *)
Require Export numbers fin_collections.

Definition Nmax `{Elements N C} : C → N := collection_fold Nmax 0%N.

Instance Nmax_proper `{FinCollection N C} : Proper ((≡) ==> (=)) Nmax.
Proof.
  apply (collection_fold_proper (=)).
  * solve_proper.
  * intros. rewrite !N.max_assoc. f_equal. apply N.max_comm.
Qed.

Lemma Nmax_max `{FinCollection N C} X x : x ∈ X → (x ≤ Nmax X)%N.
Proof.
  apply (collection_fold_ind (λ b X, x ∈ X → (x ≤ b)%N)).
  * solve_proper.
  * solve_elem_of.
  * solve_elem_of (eauto using N.le_max_l, N.le_max_r, N.le_trans).
Qed.

Instance Nfresh `{FinCollection N C} : Fresh N C := λ l, (1 + Nmax l)%N.
Instance Nfresh_spec `{FinCollection N C} : FreshSpec N C.
Proof.
  split.
  * apply _.
  * intros. unfold fresh, Nfresh.
    setoid_replace X with Y; [done |]. by apply elem_of_equiv.
  * intros X E. assert (1 ≤ 0)%N as []; [| done].
    apply N.add_le_mono_r with (Nmax X). by apply Nmax_max.
Qed.
