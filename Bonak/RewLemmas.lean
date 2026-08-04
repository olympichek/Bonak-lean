import Bonak.SigT

/-!
Small transport lemmas used by the main construction.

These are direct Lean counterparts of the Coq `rew` helper lemmas. They are
proved only by equality elimination.
-/

namespace Bonak

universe u v w t

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

theorem rew_app_lr {A : Sort u} (P : A -> Sort v) (x y : A)
    (H : y = x) (H2 : x = y) (a : P x) :
    H.symm = H2 -> transport P H (transport P H2 a) = a := by
  intro h
  cases H
  cases h
  rfl

theorem map_subst {A : Sort u} {P : A -> Sort v} {Q : A -> Sort w}
    (f : forall x, P x -> Q x) {x y : A} (H : x = y) (z : P x) :
    transport Q H (f x z) = f y (transport P H z) := by
  cases H
  rfl

theorem rew_map {A : Sort u} {B : Sort v} (P : B -> Sort w)
    (f : A -> B) {x y : A} (H : x = y) (a : P (f x)) :
    transport (fun x => P (f x)) H a =
      transport P (congrArg f H) a := by
  cases H
  rfl

theorem map_subst_map {A : Sort u} {B : Sort v} {P : A -> Sort w}
    {Q : B -> Sort t} (f : A -> B)
    (g : forall x, P x -> Q (f x)) {x y : A}
    (H : x = y) (z : P x) :
    transport Q (congrArg f H) (g x z) =
      g y (transport P H z) := by
  cases H
  rfl

theorem rew_compose {A : Sort u} (P : A -> Sort v) {x y z : A}
    (H : x = y) (H2 : y = z) (a : P x) :
    transport P H2 (transport P H a) =
      transport P (H.trans H2) a := by
  cases H
  cases H2
  rfl

theorem map_subst_app {A : Sort u} {B : Sort v} {x y : B} {θ : A}
    (H : x = y) (P : A -> B -> Sort w) (f : forall a, P a x) :
    transport (P θ) H (f θ) =
      (transport (fun x => forall a, P a x) H f) θ := by
  cases H
  rfl

end Bonak
