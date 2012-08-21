Require Import base.

Section monad_ops.
  Context (M : Type → Type).

  Class MRet := mret: ∀ {A}, A → M A.
  Class MBind := mbind: ∀ {A B}, (A → M B) → M A → M B.
  Class MJoin := mjoin: ∀ {A}, M (M A) → M A.
  Class FMap := fmap: ∀ {A B}, (A → B) → M A → M B.
End monad_ops.

Arguments mret {M MRet A} _.
Arguments mbind {M MBind A B} _ _.
Arguments mjoin {M MJoin A} _.
Arguments fmap {M FMap A B} _ _.

Notation "m ≫= f" := (mbind f m) (at level 60, right associativity) : C_scope.
Notation "x ← y ; z" := (y ≫= (λ x : _, z))
  (at level 65, next at level 35, right associativity) : C_scope.
Infix "<$>" := fmap (at level 65, right associativity, only parsing) : C_scope.
