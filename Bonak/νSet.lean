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

namespace νSet

def mkFrameTypes : Nat -> Nat -> Type 1
  | 0, _ => PUnit.{2}
  | p + 1, k => { _ : mkFrameTypes p (k + 1) &T HSet }

def mkPaintingTypes : (p k : Nat) -> mkFrameTypes p k -> Type 1
  | 0, _, _ => PUnit.{2}
  | p + 1, k, frames =>
      { _ : mkPaintingTypes p (k + 1) frames.1 &T
        (frames.2 : Type) -> HSet }

structure RestrFrameTypeBlock (p k : Nat) where
  RestrFrameTypesDef : Type 1
  FrameDef : RestrFrameTypesDef -> mkFrameTypes p.succ k

def mkRestrFrameTypesStep (A : AritySig) {p k : Nat}
    (frames : mkFrameTypes p.succ k)
    (prev : RestrFrameTypeBlock p k.succ) : Type 1 :=
  { R : prev.RestrFrameTypesDef &T
    forall q : Nat, leR q k -> A.arity -> (prev.FrameDef R).2 -> frames.2 }

def mkLayer (A : AritySig) {p k : Nat} {frames : mkFrameTypes p.succ k}
    (paintings : mkPaintingTypes p.succ k frames)
    {prev : RestrFrameTypeBlock p k.succ}
    (restrFrames : mkRestrFrameTypesStep A frames prev)
    (d : (prev.FrameDef restrFrames.1).2) : HSet :=
  hforall eps : A.arity,
    paintings.2 (restrFrames.2 0 (leR_O (n := k)) eps d)

def mkRestrFrameTypesAndFrames (A : AritySig) :
    {p k : Nat} -> (frames : mkFrameTypes p k) ->
      mkPaintingTypes p k frames -> RestrFrameTypeBlock p k
  | 0, _, _, _ =>
      { RestrFrameTypesDef := PUnit.{2}
        FrameDef := fun _ =>
          (PUnit.unit ; hunit) }
  | p + 1, k, frames, paintings =>
      let prev := mkRestrFrameTypesAndFrames A
        (p := p) (k := k + 1) frames.1 paintings.1
      { RestrFrameTypesDef := mkRestrFrameTypesStep A frames prev
        FrameDef := fun R =>
          (prev.FrameDef R.1 ;
            { d : (prev.FrameDef R.1).2 & mkLayer A paintings R d }) }

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
  hforall eps : A.arity,
    deps.paintings.2 (deps.restrFrames.2 0 (leR_O (n := k)) eps d)

structure DepsRestrExtension (A : AritySig) (p k : Nat) where
  deps : DepsRestr A p k
  painting : mkFrame A deps -> HSet

def DepsRestrExtension.TopRestrDep {A : AritySig} {p : Nat}
    (deps : DepsRestr A p 0) (E : mkFrame A deps -> HSet) :
    DepsRestrExtension A p 0 :=
  { deps := deps
    painting := E }

def DepsRestrExtension.AddRestrDep {A : AritySig} {p k : Nat}
    (extraDeps : DepsRestrExtension A p.succ k) :
    DepsRestrExtension A p k.succ :=
  { deps := proj1DepsRestr A extraDeps.deps
    painting := fun d =>
      { l : mkLayerOf A extraDeps.deps d &
        extraDeps.painting
          (existT (fun d : mkFrame A (proj1DepsRestr A extraDeps.deps) =>
            mkLayerOf A extraDeps.deps d) d l) } }

abbrev mkPainting (A : AritySig) {p k : Nat}
    (extraDeps : DepsRestrExtension A p k) : mkFrame A extraDeps.deps -> HSet :=
  extraDeps.painting

def mkPaintingsPrefix (A : AritySig) :
    {p k : Nat} -> (extraDeps : DepsRestrExtension A p k) ->
      mkPaintingTypes p k.succ (mkFrames A extraDeps.deps).1
  | 0, _, _ => PUnit.unit
  | _ + 1, _, extraDeps =>
      let extraDeps' := DepsRestrExtension.AddRestrDep extraDeps
      (mkPaintingsPrefix A extraDeps' ; mkPainting A extraDeps')

def mkPaintings (A : AritySig) {p k : Nat}
    (extraDeps : DepsRestrExtension A p k) :
    mkPaintingTypes p.succ k (mkFrames A extraDeps.deps) :=
  (mkPaintingsPrefix A extraDeps ; mkPainting A extraDeps)

def mkRestrPaintingType (A : AritySig) {p k : Nat}
    (extraDeps : DepsRestrExtension A p.succ k) : Type :=
  forall (q : Nat) (Hq : leR q k) (eps : A.arity),
    (d : mkFrame A (proj1DepsRestr A extraDeps.deps)) ->
    (mkPaintings A (DepsRestrExtension.AddRestrDep extraDeps)).2 d ->
    extraDeps.deps.paintings.2 (extraDeps.deps.restrFrames.2 q Hq eps d)

def mkRestrPaintingTypes (A : AritySig) :
    {p k : Nat} -> DepsRestrExtension A p k -> Type 1
  | 0, _, _ => PUnit.{2}
  | _ + 1, _, extraDeps =>
      { _ : mkRestrPaintingTypes
          (A := A) (DepsRestrExtension.AddRestrDep extraDeps) &T
        mkRestrPaintingType A extraDeps }

structure CohFrameTypeBlock (A : AritySig) {p k : Nat}
    (extraDeps : DepsRestrExtension A p k) where
  CohFrameTypesDef : Type 1
  RestrFramesDef : CohFrameTypesDef -> mkRestrFrameTypes A (mkPaintings A extraDeps)

def mkCohFrameTypesStep (A : AritySig) {p k : Nat}
    (extraDeps : DepsRestrExtension A p.succ k)
    (prev : CohFrameTypeBlock A (DepsRestrExtension.AddRestrDep extraDeps)) :
    Type 1 :=
  { Q : prev.CohFrameTypesDef &T
    forall (q : Nat) (Hq : leR q k) (r : Nat) (Hr : leR r q)
      (eps omega : A.arity)
      (d : mkFrame A (proj1DepsRestr A (toDepsRestr A (prev.RestrFramesDef Q)))),
      extraDeps.deps.restrFrames.2 q Hq eps
        ((prev.RestrFramesDef Q).2 r (leR_trans Hr (leR_up Hq)) omega d) =
      extraDeps.deps.restrFrames.2 r (leR_trans Hr Hq) omega
        ((prev.RestrFramesDef Q).2 q.succ (leR_raise_both Hq) eps d) }

def mkRestrLayer (A : AritySig) {p k : Nat}
    {extraDeps : DepsRestrExtension A p.succ k}
    (restrPaintings : mkRestrPaintingTypes A extraDeps)
    {prev : CohFrameTypeBlock A (DepsRestrExtension.AddRestrDep extraDeps)}
    (cohFrames : mkCohFrameTypesStep A extraDeps prev)
    (q : Nat) (Hq : leR q k) (eps : A.arity)
    (d : mkFrame A (proj1DepsRestr A (toDepsRestr A (prev.RestrFramesDef cohFrames.1)))) :
    mkLayer A (mkPaintings A (DepsRestrExtension.AddRestrDep extraDeps))
      (prev.RestrFramesDef cohFrames.1) d ->
    mkLayer A extraDeps.deps.paintings extraDeps.deps.restrFrames
      ((prev.RestrFramesDef cohFrames.1).2 q.succ (leR_raise_both Hq) eps d) :=
  fun l omega =>
    transport (fun x => (extraDeps.deps.paintings.2 x).Dom)
      (cohFrames.2 q Hq 0 leR_O eps omega d)
      (restrPaintings.2 q Hq eps _ (l omega))

def mkCohFrameTypesAndRestrFrames (A : AritySig) :
    {p k : Nat} -> (extraDeps : DepsRestrExtension A p k) ->
      mkRestrPaintingTypes A extraDeps -> CohFrameTypeBlock A extraDeps
  | 0, _, _, _ =>
      { CohFrameTypesDef := PUnit.{2}
        RestrFramesDef := fun _ => (PUnit.unit ; fun _ _ _ _ => PUnit.unit) }
  | _ + 1, _, extraDeps, restrPaintings =>
      let prev := mkCohFrameTypesAndRestrFrames A
        (DepsRestrExtension.AddRestrDep extraDeps) restrPaintings.1
      let restrFrames := prev.RestrFramesDef
      { CohFrameTypesDef := mkCohFrameTypesStep A extraDeps prev
        RestrFramesDef := fun Q =>
          (restrFrames Q.1 ;
            fun q Hq eps d =>
              ((restrFrames Q.1).2 q.succ (leR_raise_both Hq) eps d.1 ;
                mkRestrLayer A restrPaintings Q q Hq eps d.1 d.2)) }

abbrev mkCohFrameTypes (A : AritySig) {p k : Nat}
    {extraDeps : DepsRestrExtension A p k}
    (restrPaintings : mkRestrPaintingTypes A extraDeps) : Type 1 :=
  (mkCohFrameTypesAndRestrFrames A extraDeps restrPaintings).CohFrameTypesDef

structure DepsCohs (A : AritySig) (p k : Nat) where
  extraDeps : DepsRestrExtension A p k
  restrPaintings : mkRestrPaintingTypes A extraDeps
  cohs : mkCohFrameTypes A restrPaintings

abbrev DepsCohs.deps {A : AritySig} {p k : Nat}
    (depsCohs : DepsCohs A p k) : DepsRestr A p k :=
  depsCohs.extraDeps.deps

def toDepsCohs (A : AritySig) {p k : Nat}
    {extraDeps : DepsRestrExtension A p k}
    {restrPaintings : mkRestrPaintingTypes A extraDeps}
    (cohs : mkCohFrameTypes A restrPaintings) : DepsCohs A p k :=
  { extraDeps := extraDeps
    restrPaintings := restrPaintings
    cohs := cohs }

def proj1DepsCohs (A : AritySig) {p k : Nat}
    (depsCohs : DepsCohs A p.succ k) : DepsCohs A p k.succ :=
  { extraDeps := DepsRestrExtension.AddRestrDep depsCohs.extraDeps
    restrPaintings := depsCohs.restrPaintings.1
    cohs := depsCohs.cohs.1 }

abbrev mkRestrFrames (A : AritySig) {p k : Nat}
    (depsCohs : DepsCohs A p k) :
    mkRestrFrameTypes A (mkPaintings A depsCohs.extraDeps) :=
  (mkCohFrameTypesAndRestrFrames A depsCohs.extraDeps
    depsCohs.restrPaintings).RestrFramesDef depsCohs.cohs

def mkDepsRestr (A : AritySig) {p k : Nat}
    (depsCohs : DepsCohs A p k) : DepsRestr A p.succ k :=
  toDepsRestr A (mkRestrFrames A depsCohs)

abbrev mkRestrFrame (A : AritySig) {p k : Nat}
    (depsCohs : DepsCohs A p k) :
    forall q : Nat, leR q k -> A.arity ->
      mkFrame A (proj1DepsRestr A (mkDepsRestr A depsCohs)) ->
      mkFrame A depsCohs.deps :=
  (mkRestrFrames A depsCohs).2

end νSet
end Bonak
