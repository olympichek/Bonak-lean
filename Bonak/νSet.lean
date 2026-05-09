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

section Arity

variable {A : AritySig}

def mkRestrFrameTypesStep {p k : Nat}
    (frames : mkFrameTypes p.succ k)
    (prev : RestrFrameTypeBlock p k.succ) : Type 1 :=
  { R : prev.RestrFrameTypesDef &T
    forall q : Nat, leR q k -> A.arity -> (prev.FrameDef R).2 -> frames.2 }

def mkLayer {p k : Nat} {frames : mkFrameTypes p.succ k}
    (paintings : mkPaintingTypes p.succ k frames)
    {prev : RestrFrameTypeBlock p k.succ}
    (restrFrames : mkRestrFrameTypesStep (A := A) frames prev)
    (d : (prev.FrameDef restrFrames.1).2) : HSet :=
  hforall eps : A.arity,
    paintings.2 (restrFrames.2 0 (leR_O (n := k)) eps d)

def mkRestrFrameTypesAndFrames {A : AritySig} :
    {p k : Nat} -> (frames : mkFrameTypes p k) ->
      mkPaintingTypes p k frames -> RestrFrameTypeBlock p k
  | 0, _, _, _ =>
      { RestrFrameTypesDef := PUnit.{2}
        FrameDef := fun _ =>
          (PUnit.unit ; hunit) }
  | p + 1, k, frames, paintings =>
      let prev := mkRestrFrameTypesAndFrames
        (A := A) (p := p) (k := k + 1) frames.1 paintings.1
      { RestrFrameTypesDef := mkRestrFrameTypesStep (A := A) frames prev
        FrameDef := fun R =>
          (prev.FrameDef R.1 ;
            { d : (prev.FrameDef R.1).2 &
              mkLayer paintings R d }) }

abbrev mkRestrFrameTypes {p k : Nat} {frames : mkFrameTypes p k}
    (paintings : mkPaintingTypes p k frames) : Type 1 :=
  (mkRestrFrameTypesAndFrames (A := A) frames paintings).RestrFrameTypesDef

structure DepsRestr (p k : Nat) where
  frames : mkFrameTypes p k
  paintings : mkPaintingTypes p k frames
  restrFrames : mkRestrFrameTypes (A := A) paintings

def toDepsRestr {p k : Nat} {frames : mkFrameTypes p k}
    {paintings : mkPaintingTypes p k frames}
    (restrFrames : mkRestrFrameTypes (A := A) paintings) :
    DepsRestr (A := A) p k :=
  { frames := frames
    paintings := paintings
    restrFrames := restrFrames }

def proj1DepsRestr {p k : Nat} (deps : DepsRestr (A := A) p.succ k) :
    DepsRestr (A := A) p k.succ :=
  { frames := deps.frames.1
    paintings := deps.paintings.1
    restrFrames := deps.restrFrames.1 }

abbrev mkFrames {p k : Nat} (deps : DepsRestr (A := A) p k) :
    mkFrameTypes p.succ k :=
  (mkRestrFrameTypesAndFrames deps.frames deps.paintings).FrameDef deps.restrFrames

abbrev mkFrame {p k : Nat} (deps : DepsRestr (A := A) p k) : HSet :=
  (mkFrames deps).2

abbrev mkLayerOf {p k : Nat} (deps : DepsRestr (A := A) p.succ k)
    (d : mkFrame (proj1DepsRestr deps)) : HSet :=
  hforall eps : A.arity,
    deps.paintings.2 (deps.restrFrames.2 0 (leR_O (n := k)) eps d)

structure DepsRestrExtension (p k : Nat) where
  deps : DepsRestr (A := A) p k
  painting : mkFrame deps -> HSet

def DepsRestrExtension.TopRestrDep {p : Nat}
    (deps : DepsRestr (A := A) p 0)
    (E : mkFrame deps -> HSet) :
    DepsRestrExtension (A := A) p 0 :=
  { deps := deps
    painting := E }

def DepsRestrExtension.AddRestrDep {p k : Nat}
    (extraDeps : DepsRestrExtension (A := A) p.succ k) :
    DepsRestrExtension (A := A) p k.succ :=
  { deps := proj1DepsRestr extraDeps.deps
    painting := fun d =>
      { l : mkLayerOf extraDeps.deps d &
        extraDeps.painting
          (existT
            (fun d : mkFrame (proj1DepsRestr extraDeps.deps) =>
              mkLayerOf extraDeps.deps d)
            d l) } }

abbrev mkPainting {p k : Nat}
    (extraDeps : DepsRestrExtension (A := A) p k) :
    mkFrame extraDeps.deps -> HSet :=
  extraDeps.painting

def mkPaintingsPrefix {A : AritySig} :
    {p k : Nat} -> (extraDeps : DepsRestrExtension (A := A) p k) ->
      mkPaintingTypes p k.succ (mkFrames extraDeps.deps).1
  | 0, _, _ => PUnit.unit
  | _ + 1, _, extraDeps =>
      let extraDeps' := DepsRestrExtension.AddRestrDep extraDeps
      (mkPaintingsPrefix extraDeps' ; mkPainting extraDeps')

def mkPaintings {p k : Nat}
    (extraDeps : DepsRestrExtension (A := A) p k) :
    mkPaintingTypes p.succ k (mkFrames extraDeps.deps) :=
  (mkPaintingsPrefix extraDeps ; mkPainting extraDeps)

def mkRestrPaintingType {p k : Nat}
    (extraDeps : DepsRestrExtension (A := A) p.succ k) : Type :=
  forall (q : Nat) (Hq : leR q k) (eps : A.arity),
    (d : mkFrame (proj1DepsRestr extraDeps.deps)) ->
    (mkPaintings (DepsRestrExtension.AddRestrDep extraDeps)).2 d ->
    extraDeps.deps.paintings.2 (extraDeps.deps.restrFrames.2 q Hq eps d)

def mkRestrPaintingTypes {A : AritySig} :
    {p k : Nat} -> DepsRestrExtension (A := A) p k -> Type 1
  | 0, _, _ => PUnit.{2}
  | _ + 1, _, extraDeps =>
      { _ : mkRestrPaintingTypes
          (DepsRestrExtension.AddRestrDep extraDeps) &T
        mkRestrPaintingType extraDeps }

structure CohFrameTypeBlock {p k : Nat}
    (extraDeps : DepsRestrExtension (A := A) p k) where
  CohFrameTypesDef : Type 1
  RestrFramesDef :
    CohFrameTypesDef -> mkRestrFrameTypes (A := A)
      (mkPaintings extraDeps)

def mkCohFrameTypesStep {p k : Nat}
    (extraDeps : DepsRestrExtension (A := A) p.succ k)
    (prev : CohFrameTypeBlock
      (DepsRestrExtension.AddRestrDep extraDeps)) :
    Type 1 :=
  { Q : prev.CohFrameTypesDef &T
    forall (q : Nat) (Hq : leR q k) (r : Nat) (Hr : leR r q)
      (eps omega : A.arity)
      (d : mkFrame (proj1DepsRestr
        (toDepsRestr (prev.RestrFramesDef Q)))),
      extraDeps.deps.restrFrames.2 q Hq eps
        ((prev.RestrFramesDef Q).2 r (leR_trans Hr (leR_up Hq)) omega d) =
      extraDeps.deps.restrFrames.2 r (leR_trans Hr Hq) omega
        ((prev.RestrFramesDef Q).2 q.succ (leR_raise_both Hq) eps d) }

def mkRestrLayer {p k : Nat}
    {extraDeps : DepsRestrExtension (A := A) p.succ k}
    (restrPaintings : mkRestrPaintingTypes extraDeps)
    {prev : CohFrameTypeBlock
      (DepsRestrExtension.AddRestrDep extraDeps)}
    (cohFrames : mkCohFrameTypesStep extraDeps prev)
    (q : Nat) (Hq : leR q k) (eps : A.arity)
    (d : mkFrame (proj1DepsRestr
      (toDepsRestr (prev.RestrFramesDef cohFrames.1)))) :
    mkLayer
      (mkPaintings (DepsRestrExtension.AddRestrDep extraDeps))
      (prev.RestrFramesDef cohFrames.1) d ->
    mkLayer extraDeps.deps.paintings extraDeps.deps.restrFrames
      ((prev.RestrFramesDef cohFrames.1).2 q.succ (leR_raise_both Hq) eps d) :=
  fun l omega =>
    transport (fun x => (extraDeps.deps.paintings.2 x).Dom)
      (cohFrames.2 q Hq 0 leR_O eps omega d)
      (restrPaintings.2 q Hq eps _ (l omega))

def mkCohFrameTypesAndRestrFrames {A : AritySig} :
    {p k : Nat} -> (extraDeps : DepsRestrExtension (A := A) p k) ->
      mkRestrPaintingTypes extraDeps ->
      CohFrameTypeBlock extraDeps
  | 0, _, _, _ =>
      { CohFrameTypesDef := PUnit.{2}
        RestrFramesDef := fun _ => (PUnit.unit ; fun _ _ _ _ => PUnit.unit) }
  | _ + 1, _, extraDeps, restrPaintings =>
      let prev := mkCohFrameTypesAndRestrFrames
        (DepsRestrExtension.AddRestrDep extraDeps) restrPaintings.1
      let restrFrames := prev.RestrFramesDef
      { CohFrameTypesDef := mkCohFrameTypesStep extraDeps prev
        RestrFramesDef := fun Q =>
          (restrFrames Q.1 ;
            fun q Hq eps d =>
              ((restrFrames Q.1).2 q.succ (leR_raise_both Hq) eps d.1 ;
                mkRestrLayer restrPaintings Q q Hq eps d.1 d.2)) }

abbrev mkCohFrameTypes {p k : Nat}
    {extraDeps : DepsRestrExtension (A := A) p k}
    (restrPaintings : mkRestrPaintingTypes extraDeps) : Type 1 :=
  (mkCohFrameTypesAndRestrFrames extraDeps restrPaintings).CohFrameTypesDef

structure DepsCohs (p k : Nat) where
  extraDeps : DepsRestrExtension (A := A) p k
  restrPaintings : mkRestrPaintingTypes extraDeps
  cohs : mkCohFrameTypes (extraDeps := extraDeps) restrPaintings

abbrev DepsCohs.deps {p k : Nat}
    (depsCohs : DepsCohs (A := A) p k) : DepsRestr (A := A) p k :=
  depsCohs.extraDeps.deps

def toDepsCohs {p k : Nat}
    {extraDeps : DepsRestrExtension (A := A) p k}
    {restrPaintings : mkRestrPaintingTypes extraDeps}
    (cohs : mkCohFrameTypes (extraDeps := extraDeps) restrPaintings) :
    DepsCohs (A := A) p k :=
  { extraDeps := extraDeps
    restrPaintings := restrPaintings
    cohs := cohs }

def proj1DepsCohs {p k : Nat}
    (depsCohs : DepsCohs (A := A) p.succ k) :
    DepsCohs (A := A) p k.succ :=
  { extraDeps := DepsRestrExtension.AddRestrDep depsCohs.extraDeps
    restrPaintings := depsCohs.restrPaintings.1
    cohs := depsCohs.cohs.1 }

abbrev mkRestrFrames {p k : Nat}
    (depsCohs : DepsCohs (A := A) p k) :
    mkRestrFrameTypes (A := A) (mkPaintings depsCohs.extraDeps) :=
  (mkCohFrameTypesAndRestrFrames
    depsCohs.extraDeps depsCohs.restrPaintings).RestrFramesDef
    depsCohs.cohs

def mkDepsRestr {p k : Nat}
    (depsCohs : DepsCohs (A := A) p k) :
    DepsRestr (A := A) p.succ k :=
  toDepsRestr (mkRestrFrames depsCohs)

abbrev mkRestrFrame {p k : Nat}
    (depsCohs : DepsCohs (A := A) p k) :
    forall q : Nat, leR q k -> A.arity ->
      mkFrame (proj1DepsRestr (mkDepsRestr depsCohs)) ->
      mkFrame (DepsCohs.deps depsCohs) :=
  (mkRestrFrames depsCohs).2

end Arity

end νSet
end Bonak
