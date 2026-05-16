import Lean

/-!
A small command for debugging computed types.

`#deep_reduce t` normalizes `t` under full transparency and then recursively
normalizes subterms. This is intentionally a display/debug command, not a proof
automation primitive.
-/

namespace Bonak
namespace DeepReduce

open Lean Elab Command Term Meta

partial def deepReduceExpr (e : Expr) : MetaM Expr :=
  transform e (pre := fun e => do
    let e' ← withTransparency .all <| whnf e
    if e' == e then
      return .continue
    else
      return .visit e')

elab "#deep_reduce " t:term : command => do
  let expr ← liftTermElabM <| do
    let expr ← elabTerm t none
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars expr
  let norm ← liftTermElabM <| deepReduceExpr expr
  logInfo m!"{norm}"

end DeepReduce
end Bonak
