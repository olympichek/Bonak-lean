/-!
Level bounds for the Bonak construction.

The Rocq source needs a custom recursive `SProp`-valued order (`LeSProp.v`)
to make proofs of `n <= m` definitionally irrelevant. In Lean every `Prop`
is definitionally proof irrelevant, so the standard library's `Nat.le`
already plays that role; this file only provides the implicit-argument
variants and the compact combinator notations used by the construction.
-/

namespace Bonak

theorem leR_refl {n : Nat} : n ≤ n := Nat.le_refl n

theorem leR_O {n : Nat} : 0 ≤ n := Nat.zero_le n

theorem leR_O_contra {n : Nat} : n + 1 ≤ 0 -> False := Nat.not_succ_le_zero n

scoped infix:45 " ↕ " => Nat.le_trans

scoped prefix:70 "↑ᵣ " => Nat.le_succ_of_le

scoped prefix:70 "↓ᵣ " => Nat.le_of_succ_le

scoped prefix:70 "⇓ᵣ " => Nat.le_of_succ_le_succ

scoped prefix:70 "⇑ᵣ " => Nat.succ_le_succ

end Bonak
