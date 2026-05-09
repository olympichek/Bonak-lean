/-!
Recursive `Prop`-valued order used in the Bonak construction.

The Coq source uses `SProp` for this relation. Lean's `Prop` is proof
irrelevant, so the port keeps the same recursive definition while replacing
`SProp` with `Prop`.
-/

namespace Bonak

inductive SFalse : Prop

inductive STrue : Prop where
  | intro : STrue

def leR : Nat -> Nat -> Prop
  | 0, _ => STrue
  | _ + 1, 0 => SFalse
  | n + 1, m + 1 => leR n m

theorem leR_refl {n : Nat} : leR n n := by
  induction n with
  | zero => exact STrue.intro
  | succ _ ih => exact ih

theorem leR_O_contra {n : Nat} : leR (n + 1) 0 -> SFalse := by
  intro h
  exact h

theorem leR_O {n : Nat} : leR 0 n :=
  STrue.intro

theorem leR_trans {n m p : Nat} (Hnm : leR n m) (Hmp : leR m p) :
    leR n p := by
  induction m generalizing n p with
  | zero =>
      cases n with
      | zero => exact STrue.intro
      | succ _ => cases Hnm
  | succ m ih =>
      cases n with
      | zero => exact STrue.intro
      | succ n =>
          cases p with
          | zero => cases Hmp
          | succ p => exact ih (n := n) (p := p) Hnm Hmp

scoped infix:45 " ↕ " => leR_trans

theorem leR_up {n m : Nat} (Hnm : leR n m) : leR n (m + 1) := by
  induction n generalizing m with
  | zero => exact STrue.intro
  | succ _ ih =>
      cases m with
      | zero => cases Hnm
      | succ _ => exact ih Hnm

theorem leR_down {n m : Nat} (Hnm : leR (n + 1) m) : leR n m := by
  induction n generalizing m with
  | zero => exact STrue.intro
  | succ _ ih =>
      cases m with
      | zero => cases Hnm
      | succ _ => exact ih Hnm

theorem leR_lower_both {n m : Nat} (Hnm : leR (n + 1) (m + 1)) :
    leR n m :=
  Hnm

theorem leR_raise_both {n m : Nat} (Hnm : leR n m) :
    leR (n + 1) (m + 1) :=
  Hnm

end Bonak
