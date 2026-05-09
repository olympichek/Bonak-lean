import Bonak.HSet

/-!
Small transport lemmas used by the main construction.

These are direct Lean counterparts of the Coq `rew` helper lemmas. They are
proved only by equality elimination.
-/

namespace Bonak

universe u v w

theorem rew_permute_ll_hset {A : Type u} (P Q : A -> HSet)
    (x y : A) (H : forall z : A, P z = Q z) (H' : x = y)
    (a : P x) :
    transport (fun X : HSet => X.Dom) (H y)
      (transport (fun z : A => (P z).Dom) H' a) =
    transport (fun z : A => (Q z).Dom) H'
      (transport (fun X : HSet => X.Dom) (H x) a) := by
  cases H'
  rfl

theorem rew_swap {A : Sort u} (P : A -> Sort v) (a b : A)
    (H : a = b) (x : P a) (y : P b) :
    x = transport P H.symm y <-> transport P H x = y := by
  cases H
  constructor
  · intro h
    exact h
  · intro h
    exact h

theorem rew_app_rl {A : Sort u} (P : A -> Sort v) (x y : A)
    (H H2 : x = y) (a : P x) :
    H = H2 -> transport P H.symm (transport P H2 a) = a := by
  intro h
  cases h
  cases H
  rfl

theorem map_subst_app {A : Sort u} {B : Sort v} {x y : B} {theta : A}
    (H : x = y) (P : A -> B -> Sort w) (f : forall theta, P theta x) :
    transport (P theta) H (f theta) =
      (transport (fun x => forall theta, P theta x) H f) theta := by
  cases H
  rfl

end Bonak
