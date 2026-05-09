import Bonak.RewLemmas
import Bonak.LeProp

/-!
Main Bonak construction.

This file starts with Layer A of the port: frame lists, painting lists,
restriction dependencies, and restriction painting types. Later coherence
layers will build on these explicit records.
-/

namespace Bonak

structure AritySig where
  arity : HSet

namespace VSet

def mkFrameTypes : Nat -> Nat -> Type 1
  | 0, _ => PUnit.{2}
  | p + 1, k => sigT (fun _ : mkFrameTypes p (k + 1) => HSet)

def mkPaintingTypes : (p k : Nat) -> mkFrameTypes p k -> Type 1
  | 0, _, _ => PUnit.{2}
  | p + 1, k, frames =>
      sigT (fun _ : mkPaintingTypes p (k + 1) frames.1 =>
        (frames.2 : Type) -> HSet)

structure RestrFrameTypeBlock (p k : Nat) where
  RestrFrameTypesDef : Type 1
  FrameDef : RestrFrameTypesDef -> mkFrameTypes p.succ k

def mkRestrFrameTypesStep (A : AritySig) {p k : Nat}
    (frames : mkFrameTypes p.succ k)
    (prev : RestrFrameTypeBlock p k.succ) : Type 1 :=
  sigT (fun R : prev.RestrFrameTypesDef =>
    forall q : Nat, leR q k -> A.arity -> (prev.FrameDef R).2 -> frames.2)

def mkLayer (A : AritySig) {p k : Nat} {frames : mkFrameTypes p.succ k}
    (paintings : mkPaintingTypes p.succ k frames)
    {prev : RestrFrameTypeBlock p k.succ}
    (restrFrames : mkRestrFrameTypesStep A frames prev)
    (d : (prev.FrameDef restrFrames.1).2) : HSet :=
  hpiT (fun eps : A.arity =>
    paintings.2 (restrFrames.2 0 (leR_O (n := k)) eps d))

def mkRestrFrameTypesAndFrames (A : AritySig) :
    {p k : Nat} -> (frames : mkFrameTypes p k) ->
      mkPaintingTypes p k frames -> RestrFrameTypeBlock p k
  | 0, _, _, _ =>
      { RestrFrameTypesDef := PUnit.{2}
        FrameDef := fun _ =>
          existT (fun _ : PUnit.{2} => HSet) PUnit.unit hunit }
  | p + 1, k, frames, paintings =>
      let prev := mkRestrFrameTypesAndFrames A
        (p := p) (k := k + 1) frames.1 paintings.1
      { RestrFrameTypesDef := mkRestrFrameTypesStep A frames prev
        FrameDef := fun R =>
          existT
            (fun _ : mkFrameTypes p.succ k.succ => HSet)
            (prev.FrameDef R.1)
            (hsigT (fun d : (prev.FrameDef R.1).2 =>
              mkLayer A paintings R d)) }

abbrev mkRestrFrameTypes (A : AritySig) {p k : Nat} {frames : mkFrameTypes p k}
    (paintings : mkPaintingTypes p k frames) : Type 1 :=
  (mkRestrFrameTypesAndFrames A frames paintings).RestrFrameTypesDef

structure DepsRestr (A : AritySig) (p k : Nat) where
  frames : mkFrameTypes p k
  paintings : mkPaintingTypes p k frames
  restrFrames : mkRestrFrameTypes A paintings

def toDepsRestr (A : AritySig) {p k : Nat} {frames : mkFrameTypes p k}
    {paintings : mkPaintingTypes p k frames}
    (restrFrames : mkRestrFrameTypes A paintings) : DepsRestr A p k :=
  { frames := frames
    paintings := paintings
    restrFrames := restrFrames }

def proj1DepsRestr (A : AritySig) {p k : Nat} (deps : DepsRestr A p.succ k) :
    DepsRestr A p k.succ :=
  { frames := deps.frames.1
    paintings := deps.paintings.1
    restrFrames := deps.restrFrames.1 }

abbrev mkFrames (A : AritySig) {p k : Nat} (deps : DepsRestr A p k) :
    mkFrameTypes p.succ k :=
  (mkRestrFrameTypesAndFrames A deps.frames deps.paintings).FrameDef
    deps.restrFrames

abbrev mkFrame (A : AritySig) {p k : Nat} (deps : DepsRestr A p k) : HSet :=
  (mkFrames A deps).2

abbrev mkLayerOf (A : AritySig) {p k : Nat} (deps : DepsRestr A p.succ k)
    (d : mkFrame A (proj1DepsRestr A deps)) : HSet :=
  hpiT (fun eps : A.arity =>
    deps.paintings.2 (deps.restrFrames.2 0 (leR_O (n := k)) eps d))

inductive DepsRestrExtension (A : AritySig) :
    (p k : Nat) -> DepsRestr A p k -> Type 1 where
  | TopRestrDep {p : Nat} {deps : DepsRestr A p 0}
      (E : mkFrame A deps -> HSet) :
      DepsRestrExtension A p 0 deps
  | AddRestrDep {p k : Nat} (deps : DepsRestr A p.succ k) :
      DepsRestrExtension A p.succ k deps ->
      DepsRestrExtension A p k.succ (proj1DepsRestr A deps)

noncomputable def mkPainting (A : AritySig) :
    {p k : Nat} -> {deps : DepsRestr A p k} ->
      DepsRestrExtension A p k deps -> mkFrame A deps -> HSet
  | _, _, _, extraDeps =>
      DepsRestrExtension.rec
        (motive := fun p k deps _ => mkFrame A (p := p) (k := k) deps -> HSet)
        (fun E => E)
        (fun deps _ ih =>
          fun d =>
        hsigT (fun l : mkLayerOf A deps d =>
          ih
            (existT (fun d : mkFrame A (proj1DepsRestr A deps) =>
              mkLayerOf A deps d) d l)))
        extraDeps

noncomputable def mkPaintingsPrefix (A : AritySig) :
    {p k : Nat} -> {deps : DepsRestr A p k} ->
      DepsRestrExtension A p k deps ->
      mkPaintingTypes p k.succ (mkFrames A deps).1
  | 0, _, _, _ => PUnit.unit
  | p + 1, k, deps, extraDeps =>
      let extraDeps' := DepsRestrExtension.AddRestrDep (A := A) deps extraDeps
      existT
        (fun _ : mkPaintingTypes p k.succ.succ (mkFrames A deps).1.1 =>
          (mkFrames A deps).1.2 -> HSet)
        (mkPaintingsPrefix A extraDeps')
        (mkPainting A extraDeps')

noncomputable def mkPaintings (A : AritySig) {p k : Nat} {deps : DepsRestr A p k}
    (extraDeps : DepsRestrExtension A p k deps) :
    mkPaintingTypes p.succ k (mkFrames A deps) :=
  existT
    (fun _ : mkPaintingTypes p k.succ (mkFrames A deps).1 =>
      (mkFrames A deps).2 -> HSet)
    (mkPaintingsPrefix A extraDeps)
    (mkPainting A extraDeps)

noncomputable def mkRestrPaintingType (A : AritySig) {p k : Nat} {deps : DepsRestr A p.succ k}
    (extraDeps : DepsRestrExtension A p.succ k deps) : Type :=
  forall (q : Nat) (Hq : leR q k) (eps : A.arity),
    (d : mkFrame A (proj1DepsRestr A deps)) ->
    (mkPaintings A (DepsRestrExtension.AddRestrDep (A := A) deps extraDeps)).2 d ->
    deps.paintings.2 (deps.restrFrames.2 q Hq eps d)

noncomputable def mkRestrPaintingTypes (A : AritySig) :
    {p k : Nat} -> {deps : DepsRestr A p k} ->
      DepsRestrExtension A p k deps -> Type 1
  | 0, _, _, _ => PUnit.{2}
  | _ + 1, _, deps, extraDeps =>
      sigT (fun _ : mkRestrPaintingTypes
          (A := A) (DepsRestrExtension.AddRestrDep (A := A) deps extraDeps) =>
        mkRestrPaintingType A extraDeps)

end VSet
end Bonak
