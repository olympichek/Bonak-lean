import Bonak.RewLemmas
import Bonak.LeProp

/-!
Main Bonak construction.

This file starts with Layer A of the port: frame lists, painting lists,
restriction dependencies, and restriction painting types. Later coherence
layers will build on these explicit records.
-/

namespace Bonak

open scoped Bonak

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
    forall q : Nat, q ≤ᵣ k -> A.arity -> (prev.FrameDef R).2 -> frames.2 }

def mkLayer {p k : Nat} {frames : mkFrameTypes p.succ k}
    (paintings : mkPaintingTypes p.succ k frames)
    {prev : RestrFrameTypeBlock p k.succ}
    (restrFrames : mkRestrFrameTypesStep (A := A) frames prev)
    (d : (prev.FrameDef restrFrames.1).2) : HSet :=
  hforall ε : A.arity,
    paintings.2 (restrFrames.2 0 (leR_O (n := k)) ε d)

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
  hforall ε : A.arity,
    deps.paintings.2 (deps.restrFrames.2 0 (leR_O (n := k)) ε d)

structure DepsRestrExtension (p k : Nat) (deps : DepsRestr (A := A) p k) where
  painting : mkFrame deps -> HSet

def DepsRestrExtension.TopRestrDep {p : Nat}
    (deps : DepsRestr (A := A) p 0)
    (E : mkFrame deps -> HSet) :
    DepsRestrExtension (A := A) p 0 deps :=
  { painting := E }

def DepsRestrExtension.AddRestrDep {p k : Nat}
    {deps : DepsRestr (A := A) p.succ k}
    (extraDeps : DepsRestrExtension (A := A) p.succ k deps) :
    DepsRestrExtension (A := A) p k.succ (proj1DepsRestr deps) :=
  { painting := fun d =>
      { l : mkLayerOf deps d &
        extraDeps.painting
          (existT
            (fun d : mkFrame (proj1DepsRestr deps) =>
              mkLayerOf deps d)
            d l) } }

abbrev mkPainting {p k : Nat} {deps : DepsRestr (A := A) p k}
    (extraDeps : DepsRestrExtension (A := A) p k deps) :
    mkFrame deps -> HSet :=
  extraDeps.painting

def mkPaintingsPrefix {A : AritySig} :
    {p k : Nat} -> (deps : DepsRestr (A := A) p k) ->
      DepsRestrExtension (A := A) p k deps ->
      mkPaintingTypes p k.succ (mkFrames deps).1
  | 0, _, _, _ => PUnit.unit
  | _ + 1, _, deps, extraDeps =>
      let extraDeps' := DepsRestrExtension.AddRestrDep extraDeps
      (mkPaintingsPrefix (proj1DepsRestr deps) extraDeps' ;
        mkPainting extraDeps')

def mkPaintings {p k : Nat} (deps : DepsRestr (A := A) p k)
    (extraDeps : DepsRestrExtension (A := A) p k deps) :
    mkPaintingTypes p.succ k (mkFrames deps) :=
  (mkPaintingsPrefix deps extraDeps ; mkPainting extraDeps)

def mkRestrPaintingType {p k : Nat}
    {deps : DepsRestr (A := A) p.succ k}
    (extraDeps : DepsRestrExtension (A := A) p.succ k deps) : Type :=
  forall (q : Nat) (Hq : q ≤ᵣ k) (ε : A.arity),
    (d : mkFrame (proj1DepsRestr deps)) ->
    (mkPaintings (proj1DepsRestr deps)
      (DepsRestrExtension.AddRestrDep extraDeps)).2 d ->
    deps.paintings.2 (deps.restrFrames.2 q Hq ε d)

def mkRestrPaintingTypes {A : AritySig} :
    {p k : Nat} -> (deps : DepsRestr (A := A) p k) ->
      DepsRestrExtension (A := A) p k deps -> Type 1
  | 0, _, _, _ => PUnit.{2}
  | _ + 1, _, deps, extraDeps =>
      { _ : mkRestrPaintingTypes (proj1DepsRestr deps)
          (DepsRestrExtension.AddRestrDep extraDeps) &T
        mkRestrPaintingType extraDeps }

structure CohFrameTypeBlock {p k : Nat} {deps : DepsRestr (A := A) p k}
    (extraDeps : DepsRestrExtension (A := A) p k deps) where
  CohFrameTypesDef : Type 1
  RestrFramesDef :
    CohFrameTypesDef -> mkRestrFrameTypes (A := A)
      (mkPaintings deps extraDeps)

def mkCohFrameTypesStep {p k : Nat}
    {deps : DepsRestr (A := A) p.succ k}
    (extraDeps : DepsRestrExtension (A := A) p.succ k deps)
    (prev : CohFrameTypeBlock
      (DepsRestrExtension.AddRestrDep extraDeps)) :
    Type 1 :=
  { Q : prev.CohFrameTypesDef &T
    forall (q : Nat) (Hq : q ≤ᵣ k) (r : Nat) (Hr : r ≤ᵣ q)
      (ε ω : A.arity)
      (d : mkFrame (proj1DepsRestr
        (toDepsRestr (prev.RestrFramesDef Q)))),
      deps.restrFrames.2 q Hq ε
        ((prev.RestrFramesDef Q).2 r (Hr ↕ ↑ᵣ Hq) ω d) =
      deps.restrFrames.2 r (Hr ↕ Hq) ω
        ((prev.RestrFramesDef Q).2 q.succ (⇑ᵣ Hq) ε d) }

def mkRestrLayer {p k : Nat}
    {deps : DepsRestr (A := A) p.succ k}
    {extraDeps : DepsRestrExtension (A := A) p.succ k deps}
    (restrPaintings : mkRestrPaintingTypes deps extraDeps)
    {prev : CohFrameTypeBlock
      (DepsRestrExtension.AddRestrDep extraDeps)}
    (cohFrames : mkCohFrameTypesStep extraDeps prev)
    (q : Nat) (Hq : q ≤ᵣ k) (ε : A.arity)
    (d : mkFrame (proj1DepsRestr
      (toDepsRestr (prev.RestrFramesDef cohFrames.1)))) :
    mkLayer
      (mkPaintings (proj1DepsRestr deps)
        (DepsRestrExtension.AddRestrDep extraDeps))
      (prev.RestrFramesDef cohFrames.1) d ->
    mkLayer deps.paintings deps.restrFrames
      ((prev.RestrFramesDef cohFrames.1).2 q.succ (⇑ᵣ Hq) ε d) :=
  fun l ω =>
    transport (fun x => (deps.paintings.2 x).Dom)
      (cohFrames.2 q Hq 0 leR_O ε ω d)
      (restrPaintings.2 q Hq ε _ (l ω))

def mkCohFrameTypesAndRestrFrames {A : AritySig} :
    {p k : Nat} -> (deps : DepsRestr (A := A) p k) ->
      (extraDeps : DepsRestrExtension (A := A) p k deps) ->
      mkRestrPaintingTypes deps extraDeps ->
      CohFrameTypeBlock extraDeps
  | 0, _, _, _, _ =>
      { CohFrameTypesDef := PUnit.{2}
        RestrFramesDef := fun _ => (PUnit.unit ; fun _ _ _ _ => PUnit.unit) }
  | _ + 1, _, deps, extraDeps, restrPaintings =>
      let extraDeps' := DepsRestrExtension.AddRestrDep extraDeps
      let prev := mkCohFrameTypesAndRestrFrames
        (proj1DepsRestr deps) extraDeps' restrPaintings.1
      let restrFrames := prev.RestrFramesDef
      { CohFrameTypesDef := mkCohFrameTypesStep extraDeps prev
        RestrFramesDef := fun Q =>
          (restrFrames Q.1 ;
            fun q Hq ε d =>
              ((restrFrames Q.1).2 q.succ (⇑ᵣ Hq) ε d.1 ;
                mkRestrLayer restrPaintings Q q Hq ε d.1 d.2)) }

abbrev mkCohFrameTypes {p k : Nat} {deps : DepsRestr (A := A) p k}
    {extraDeps : DepsRestrExtension (A := A) p k deps}
    (restrPaintings : mkRestrPaintingTypes deps extraDeps) : Type 1 :=
  (mkCohFrameTypesAndRestrFrames deps extraDeps restrPaintings).CohFrameTypesDef

structure DepsCohs (p k : Nat) where
  deps : DepsRestr (A := A) p k
  extraDeps : DepsRestrExtension (A := A) p k deps
  restrPaintings : mkRestrPaintingTypes deps extraDeps
  cohs : mkCohFrameTypes (deps := deps) (extraDeps := extraDeps) restrPaintings

def toDepsCohs {p k : Nat} {deps : DepsRestr (A := A) p k}
    {extraDeps : DepsRestrExtension (A := A) p k deps}
    {restrPaintings : mkRestrPaintingTypes deps extraDeps}
    (cohs : mkCohFrameTypes (deps := deps)
      (extraDeps := extraDeps) restrPaintings) :
    DepsCohs (A := A) p k :=
  { deps := deps
    extraDeps := extraDeps
    restrPaintings := restrPaintings
    cohs := cohs }

def proj1DepsCohs {p k : Nat}
    (depsCohs : DepsCohs (A := A) p.succ k) :
    DepsCohs (A := A) p k.succ :=
  { deps := proj1DepsRestr depsCohs.deps
    extraDeps := DepsRestrExtension.AddRestrDep depsCohs.extraDeps
    restrPaintings := depsCohs.restrPaintings.1
    cohs := depsCohs.cohs.1 }

abbrev mkRestrFrames {p k : Nat}
    (depsCohs : DepsCohs (A := A) p k) :
    mkRestrFrameTypes (A := A)
      (mkPaintings depsCohs.deps depsCohs.extraDeps) :=
  (mkCohFrameTypesAndRestrFrames
    depsCohs.deps depsCohs.extraDeps depsCohs.restrPaintings).RestrFramesDef
    depsCohs.cohs

def mkDepsRestr {p k : Nat}
    (depsCohs : DepsCohs (A := A) p k) :
    DepsRestr (A := A) p.succ k :=
  toDepsRestr (mkRestrFrames depsCohs)

abbrev mkRestrFrame {p k : Nat}
    (depsCohs : DepsCohs (A := A) p k) :
    forall q : Nat, q ≤ᵣ k -> A.arity ->
      mkFrame (proj1DepsRestr (mkDepsRestr depsCohs)) ->
      mkFrame depsCohs.deps :=
  (mkRestrFrames depsCohs).2

structure DepsCohsExtension (p k : Nat)
    (depsCohs : DepsCohs (A := A) p k) where
  extraDeps : DepsRestrExtension (A := A) p.succ k (mkDepsRestr depsCohs)
  restrPainting : mkRestrPaintingType extraDeps

def DepsCohsExtension.TopCohDep {p : Nat}
    (depsCohs : DepsCohs (A := A) p 0)
    (E : mkFrame (mkDepsRestr depsCohs) -> HSet) :
    DepsCohsExtension (A := A) p 0 depsCohs :=
  let extraDeps := DepsRestrExtension.TopRestrDep (mkDepsRestr depsCohs) E
  { extraDeps := extraDeps
    restrPainting :=
      fun
      | 0, _, ε, _, c => c.1 ε
      | q + 1, Hq, _, _, _ => nomatch leR_O_contra (n := q) Hq }

def DepsCohsExtension.AddCohDep {p k : Nat}
    {depsCohs : DepsCohs (A := A) p.succ k}
    (extraDepsCohs : DepsCohsExtension (A := A) p.succ k depsCohs) :
    DepsCohsExtension (A := A) p k.succ (proj1DepsCohs depsCohs) :=
  { extraDeps := DepsRestrExtension.AddRestrDep extraDepsCohs.extraDeps
    restrPainting :=
      fun
      | 0, _, ε, _, c => c.1 ε
      | q + 1, Hq, ε, d, c =>
          (mkRestrLayer depsCohs.restrPaintings depsCohs.cohs
              q (⇓ᵣ Hq) ε d c.1 ;
            extraDepsCohs.restrPainting q (⇓ᵣ Hq) ε
              (d ; c.1) c.2) }

abbrev mkExtraDeps {p k : Nat} {depsCohs : DepsCohs (A := A) p k}
    (extraDepsCohs : DepsCohsExtension (A := A) p k depsCohs) :
    DepsRestrExtension (A := A) p.succ k (mkDepsRestr depsCohs) :=
  extraDepsCohs.extraDeps

abbrev mkRestrPainting {p k : Nat} {depsCohs : DepsCohs (A := A) p k}
    (extraDepsCohs : DepsCohsExtension (A := A) p k depsCohs) :
    mkRestrPaintingType (mkExtraDeps extraDepsCohs) :=
  extraDepsCohs.restrPainting

def mkRestrPaintingsPrefix {A : AritySig} :
    {p k : Nat} -> {depsCohs : DepsCohs (A := A) p k} ->
      (extraDepsCohs : DepsCohsExtension (A := A) p k depsCohs) ->
      mkRestrPaintingTypes (proj1DepsRestr (mkDepsRestr depsCohs))
        (DepsRestrExtension.AddRestrDep (mkExtraDeps extraDepsCohs))
  | 0, _, _, _ => PUnit.unit
  | _ + 1, _, _, extraDepsCohs =>
      let extraDepsCohs' := DepsCohsExtension.AddCohDep extraDepsCohs
      (mkRestrPaintingsPrefix extraDepsCohs' ;
        mkRestrPainting extraDepsCohs')

def mkRestrPaintings {p k : Nat}
    {depsCohs : DepsCohs (A := A) p k}
    (extraDepsCohs : DepsCohsExtension (A := A) p k depsCohs) :
    mkRestrPaintingTypes (mkDepsRestr depsCohs) (mkExtraDeps extraDepsCohs) :=
  (mkRestrPaintingsPrefix extraDepsCohs ;
    mkRestrPainting extraDepsCohs)

def mkCohPaintingType {p k : Nat}
    {depsCohs : DepsCohs (A := A) p.succ k}
    (extraDepsCohs :
      DepsCohsExtension (A := A) p.succ k depsCohs) : Prop :=
  let addedDepsCohs := DepsCohsExtension.AddCohDep extraDepsCohs
  forall (q : Nat) (Hq : q ≤ᵣ k) (r : Nat) (Hr : r ≤ᵣ q)
    (ε ω : A.arity)
    (d : mkFrame (proj1DepsRestr (mkDepsRestr (proj1DepsCohs depsCohs))))
    (c : (mkPaintings
      (proj1DepsRestr (mkDepsRestr (proj1DepsCohs depsCohs)))
      (DepsRestrExtension.AddRestrDep (mkExtraDeps addedDepsCohs))).2 d),
    transport (fun x => (depsCohs.deps.paintings.2 x).Dom)
      (depsCohs.cohs.2 q Hq r Hr ε ω d)
      (depsCohs.restrPaintings.2 q Hq ε _
        ((mkRestrPaintings addedDepsCohs).2 r
          (Hr ↕ ↑ᵣ Hq) ω d c)) =
    depsCohs.restrPaintings.2 r (Hr ↕ Hq) ω _
      ((mkRestrPaintings addedDepsCohs).2 q.succ
        (⇑ᵣ Hq) ε d c)

def mkCohPaintingTypes {A : AritySig} :
    {p k : Nat} -> {depsCohs : DepsCohs (A := A) p k} ->
      DepsCohsExtension (A := A) p k depsCohs -> Type 1
  | 0, _, _, _ => PUnit.{2}
  | _ + 1, _, _, extraDepsCohs =>
      { _ : mkCohPaintingTypes
          (DepsCohsExtension.AddCohDep extraDepsCohs) &T
        mkCohPaintingType extraDepsCohs }

end Arity

end νSet
end Bonak
