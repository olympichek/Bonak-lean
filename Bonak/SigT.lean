/-!
Dependent pair compatibility layer for the port from Rocq/Coq.

The Coq source defines its own primitive-projection `sigT`. In Lean we use
`PSigma`, the universe-polymorphic dependent pair type, and provide the small
set of names and equality lemmas used by later files. `PSigma` matters here
because some later compatibility lemmas pair data with equality proofs in
`Prop`.
-/

namespace Bonak

universe u v w

abbrev sigT {A : Sort u} (P : A -> Sort v) : Sort (max (max 1 u) v) :=
  PSigma P

def existT {A : Sort u} (P : A -> Sort v) (a : A) (b : P a) : sigT P :=
  PSigma.mk a b

open Lean TSyntax.Compat

macro "{" xs:explicitBinders " &T " b:term "}" : term =>
  expandExplicitBinders ``sigT xs b

notation "(" x " ; " y ")" => existT _ x y

abbrev projT1 {A : Sort u} {P : A -> Sort v} (x : sigT P) : A :=
  x.1

abbrev projT2 {A : Sort u} {P : A -> Sort v} (x : sigT P) : P x.1 :=
  x.2

def transport {A : Sort u} (P : A -> Sort v) {x y : A} (p : x = y)
    (a : P x) : P y :=
  p ▸ a

theorem eq_existT_uncurried {A : Sort u} {P : A -> Sort v} {u1 v1 : A}
    {u2 : P u1} {v2 : P v1}
    (pq : PSigma (fun p : u1 = v1 => transport P p u2 = v2)) :
    existT P u1 u2 = existT P v1 v2 := by
  cases pq with
  | mk p q =>
      cases p
      cases q
      rfl

theorem eq_sigT_uncurried {A : Sort u} {P : A -> Sort v}
    (u v : sigT P)
    (pq : PSigma (fun p : projT1 u = projT1 v =>
      transport P p (projT2 u) = projT2 v)) :
    u = v := by
  cases u with
  | mk u1 u2 =>
      cases v with
      | mk v1 v2 =>
          exact eq_existT_uncurried pq

theorem eq_existT_curried {A : Sort u} {P : A -> Sort v} {u1 v1 : A}
    {u2 : P u1} {v2 : P v1} (p : u1 = v1)
    (q : transport P p u2 = v2) :
    existT P u1 u2 = existT P v1 v2 :=
  eq_existT_uncurried ⟨p, q⟩

notation "(= " p " ; " q ")" => eq_existT_curried p q

def projT1_eq {A : Sort u} {P : A -> Sort v} {u v : sigT P}
    (p : u = v) : projT1 u = projT1 v :=
  congrArg projT1 p

def projT2_eq {A : Sort u} {P : A -> Sort v} {u v : sigT P}
    (p : u = v) : transport P (projT1_eq p) (projT2 u) = projT2 v := by
  cases p
  rfl

theorem eq_existT_curried_dep {A : Type u} {x y : A} {P : A -> Type v}
    {Q : sigT P -> Type w} {H : x = y}
    {u : P x} {v : Q (existT P x u)}
    {u' : P y} {v' : Q (existT P y u')}
    {Hu : transport P H u = u'}
    {Hv : transport Q (eq_existT_curried H Hu) v = v'} :
    transport
      (fun x => sigT (fun a : P x => Q (existT P x a)))
      H
      (existT (fun a : P x => Q (existT P x a)) u v) =
    existT (fun a : P y => Q (existT P y a)) u' v' := by
  cases H
  cases Hu
  cases Hv
  rfl

end Bonak
