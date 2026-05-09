import Bonak.SigT

/-!
Sets with local uniqueness of identity proofs.

The Coq development packages a type with a UIP proof and then proves that this
structure is closed under dependent pairs and dependent functions. We keep the
same explicit structure even though Lean's equality lives in `Prop`.
-/

namespace Bonak

structure HSet where
  Dom : Type
  UIP : forall {x y : Dom}, (p q : x = y) -> p = q

instance : CoeSort HSet Type where
  coe X := X.Dom

theorem unit_UIP (x y : Unit) (h g : x = y) : h = g := by
  cases x
  cases y
  cases h
  cases g
  rfl

theorem bool_UIP (x y : Bool) (h g : x = y) : h = g := by
  cases x <;> cases y <;> cases h <;> cases g <;> rfl

def hunit : HSet :=
  { Dom := Unit
    UIP := unit_UIP _ _ }

def hbool : HSet :=
  { Dom := Bool
    UIP := bool_UIP _ _ }

theorem sigT_eq {A : Type} {B : A -> Type} {x y : sigT B} :
    existT B x.1 x.2 = existT B y.1 y.2 -> x = y := by
  intro h
  simpa using h

theorem sigT_decompose_eq {A : Type} {B : A -> Type}
    {x y : sigT B} {p : x = y} :
    p = eq_existT_curried (projT1_eq p) (projT2_eq p) := by
  cases p
  cases x
  rfl

theorem sigT_UIP {A : HSet} {B : A -> HSet}
    (x y : sigT (fun a : A => B a)) (p q : x = y) :
    p = q := by
  cases q
  cases p
  rfl

def hsigT {A : HSet} (B : A -> HSet) : HSet :=
  { Dom := sigT (fun a : A => B a)
    UIP := fun p q => sigT_UIP _ _ p q }

theorem hpiT_UIP {A : Type} (B : A -> HSet)
    (f g : forall a : A, B a) (p q : f = g) :
    p = q := by
  cases q
  cases p
  rfl

def hpiT {A : Type} (B : A -> HSet) : HSet :=
  { Dom := forall a : A, B a
    UIP := fun p q => hpiT_UIP B _ _ p q }

end Bonak
