/-!
Dependent pair compatibility layer for the port from Rocq/Coq.

The Coq source defines its own primitive-projection `sigT`. In Lean this
role is played by the standard library's `PSigma` (universe-polymorphic, so
some components may live in `Prop`); `sigT`/`existT` are mere abbreviations
for it fixing the Rocq names and notations. The rest of the file defines
transport with an explicit motive under the Rocq `rew` syntax, and the few
dependent-pair equality lemmas used by the construction that the standard
library does not provide.
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

def transport {A : Sort u} (P : A -> Sort v) {x y : A} (p : x = y)
    (a : P x) : P y :=
  p ▸ a

scoped syntax (name := rewIn) "rew " term:61 " in " term:60 : term

scoped syntax (name := rewInExplicit)
  "rew " "[" term "]" term:61 " in " term:60 : term

macro_rules (kind := rewIn)
  | `(rew $p in $a) => `(transport _ $p $a)

macro_rules (kind := rewInExplicit)
  | `(rew [$P] $p in $a) => `(transport $P $p $a)

scoped infixl:75 " ⬝ " => Eq.trans

theorem eq_existT_curried {A : Sort u} {P : A -> Sort v} {u1 v1 : A}
    {u2 : P u1} {v2 : P v1} (p : u1 = v1)
    (q : transport P p u2 = v2) :
    existT P u1 u2 = existT P v1 v2 := by
  cases p
  cases q
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

/-- A Σ-type reconstructed from its first projection. -/
theorem eq_sigT_fst {A : Sort u} {B : A -> Sort v} {s : sigT B} {a : A}
    (e : s.1 = a) : s = (a ; rew [B] e in s.2) := by
  cases e
  rfl

end Bonak
