import Bonak.RewLemmas
import Bonak.LeProp
import Bonak.DeepReduce

/-!
Main Bonak construction.

This file ports the frame, painting, restriction, coherence, and final
semisimplicial-set construction from the Rocq source, using explicit records in
place of Rocq's class-based assembly.
-/

namespace Bonak

open scoped Bonak

structure AritySig where
  arity : Type

namespace νSet

def mkFrameTypes : Nat -> Nat -> Type 1
  | 0, _ => PUnit.{2}
  | p + 1, k => { _ : mkFrameTypes p (k + 1) &T Type }

def mkPaintingTypes : (p k : Nat) -> mkFrameTypes p k -> Type 1
  | 0, _, _ => PUnit.{2}
  | p + 1, k, frames =>
      { _ : mkPaintingTypes p (k + 1) frames.1 &T
        frames.2 -> Type }

structure RestrFrameTypeBlock (p k : Nat) where
  RestrFrameTypesDef : Type 1
  FrameDef : RestrFrameTypesDef -> mkFrameTypes p.succ k

section Arity

variable {A : AritySig}

def mkRestrFrameTypesStep {p k : Nat}
    (frames : mkFrameTypes p.succ k)
    (prev : RestrFrameTypeBlock p k.succ) : Type 1 :=
  { R : prev.RestrFrameTypesDef &T
    forall q : Nat, q ≤ k -> A.arity -> (prev.FrameDef R).2 -> frames.2 }

def mkLayer {p k : Nat} {frames : mkFrameTypes p.succ k}
    (paintings : mkPaintingTypes p.succ k frames)
    {prev : RestrFrameTypeBlock p k.succ}
    (restrFrames : mkRestrFrameTypesStep (A := A) frames prev)
    (d : (prev.FrameDef restrFrames.1).2) : Type :=
  (ε : A.arity) -> paintings.2 (restrFrames.2 0 (leR_O (n := k)) ε d)

def mkRestrFrameTypesAndFrames {A : AritySig} :
    {p k : Nat} -> (frames : mkFrameTypes p k) ->
      mkPaintingTypes p k frames -> RestrFrameTypeBlock p k
  | 0, _, _, _ =>
      { RestrFrameTypesDef := PUnit.{2}
        FrameDef := fun _ =>
          (PUnit.unit ; Unit) }
  | p + 1, k, frames, paintings =>
      let prev := mkRestrFrameTypesAndFrames
        (A := A) (p := p) (k := k + 1) frames.1 paintings.1
      { RestrFrameTypesDef := mkRestrFrameTypesStep (A := A) frames prev
        FrameDef := fun R =>
          (prev.FrameDef R.1 ;
            { d : (prev.FrameDef R.1).2 &T
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

abbrev mkFrame {p k : Nat} (deps : DepsRestr (A := A) p k) : Type :=
  (mkFrames deps).2

abbrev mkLayerOf {p k : Nat} (deps : DepsRestr (A := A) p.succ k)
    (d : mkFrame (proj1DepsRestr deps)) : Type :=
  (ε : A.arity) -> deps.paintings.2 (deps.restrFrames.2 0 (leR_O (n := k)) ε d)

inductive DepsRestrExtension :
    (p k : Nat) -> DepsRestr (A := A) p k -> Type 1 where
  | TopRestrDep {p : Nat} {deps : DepsRestr (A := A) p 0}
      (E : mkFrame deps -> Type) :
      DepsRestrExtension p 0 deps
  | AddRestrDep {p k : Nat} (deps : DepsRestr (A := A) p.succ k)
      (extraDeps : DepsRestrExtension p.succ k deps) :
      DepsRestrExtension p k.succ (proj1DepsRestr deps)

def mkPainting {p k : Nat} {deps : DepsRestr (A := A) p k}
    (extraDeps : DepsRestrExtension (A := A) p k deps) :
    mkFrame deps -> Type :=
  match extraDeps with
  | DepsRestrExtension.TopRestrDep E => E
  | DepsRestrExtension.AddRestrDep deps' extraDeps' =>
      fun d =>
        { l : mkLayerOf deps' d &T
          mkPainting extraDeps'
            (existT
              (fun d : mkFrame (proj1DepsRestr deps') =>
                mkLayerOf deps' d)
              d l) }

def mkPaintingsPrefix {A : AritySig} :
    {p k : Nat} -> (deps : DepsRestr (A := A) p k) ->
      DepsRestrExtension (A := A) p k deps ->
      mkPaintingTypes p k.succ (mkFrames deps).1
  | 0, _, _, _ => PUnit.unit
  | _ + 1, _, deps, extraDeps =>
      let extraDeps' := DepsRestrExtension.AddRestrDep deps extraDeps
      (mkPaintingsPrefix (proj1DepsRestr deps) extraDeps' ;
        mkPainting extraDeps')

def mkPaintings {p k : Nat} (deps : DepsRestr (A := A) p k)
    (extraDeps : DepsRestrExtension (A := A) p k deps) :
    mkPaintingTypes p.succ k (mkFrames deps) :=
  (mkPaintingsPrefix deps extraDeps ; mkPainting extraDeps)

def mkRestrPaintingType {p k : Nat}
    {deps : DepsRestr (A := A) p.succ k}
    (extraDeps : DepsRestrExtension (A := A) p.succ k deps) : Type :=
  forall (q : Nat) (Hq : q ≤ k) (ε : A.arity),
    (d : mkFrame (proj1DepsRestr deps)) ->
    (mkPaintings (proj1DepsRestr deps)
      (DepsRestrExtension.AddRestrDep deps extraDeps)).2 d ->
    deps.paintings.2 (deps.restrFrames.2 q Hq ε d)

def mkRestrPaintingTypes {A : AritySig} :
    {p k : Nat} -> (deps : DepsRestr (A := A) p k) ->
      DepsRestrExtension (A := A) p k deps -> Type 1
  | 0, _, _, _ => PUnit.{2}
  | _ + 1, _, deps, extraDeps =>
      { _ : mkRestrPaintingTypes (proj1DepsRestr deps)
          (DepsRestrExtension.AddRestrDep deps extraDeps) &T
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
      (DepsRestrExtension.AddRestrDep deps extraDeps)) :
    Type 1 :=
  { Q : prev.CohFrameTypesDef &T
    forall (q : Nat) (Hq : q ≤ k) (r : Nat) (Hr : r ≤ q)
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
      (DepsRestrExtension.AddRestrDep deps extraDeps)}
    (cohFrames : mkCohFrameTypesStep extraDeps prev)
    (q : Nat) (Hq : q ≤ k) (ε : A.arity)
    (d : mkFrame (proj1DepsRestr
      (toDepsRestr (prev.RestrFramesDef cohFrames.1)))) :
    mkLayer
      (mkPaintings (proj1DepsRestr deps)
        (DepsRestrExtension.AddRestrDep deps extraDeps))
      (prev.RestrFramesDef cohFrames.1) d ->
    mkLayer deps.paintings deps.restrFrames
      ((prev.RestrFramesDef cohFrames.1).2 q.succ (⇑ᵣ Hq) ε d) :=
  fun l ω =>
    rew [fun x => deps.paintings.2 x]
      (cohFrames.2 q Hq 0 leR_O ε ω d) in
    restrPaintings.2 q Hq ε _ (l ω)

def mkCohFrameTypesAndRestrFrames {A : AritySig} :
    {p k : Nat} -> (deps : DepsRestr (A := A) p k) ->
      (extraDeps : DepsRestrExtension (A := A) p k deps) ->
      mkRestrPaintingTypes deps extraDeps ->
      CohFrameTypeBlock extraDeps
  | 0, _, _, _, _ =>
      { CohFrameTypesDef := PUnit.{2}
        RestrFramesDef := fun _ => (PUnit.unit ; fun _ _ _ _ => PUnit.unit) }
  | _ + 1, _, deps, extraDeps, restrPaintings =>
      let extraDeps' := DepsRestrExtension.AddRestrDep deps extraDeps
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
    extraDeps := DepsRestrExtension.AddRestrDep
      depsCohs.deps depsCohs.extraDeps
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
    forall q : Nat, q ≤ k -> A.arity ->
      mkFrame (proj1DepsRestr (mkDepsRestr depsCohs)) ->
      mkFrame depsCohs.deps :=
  (mkRestrFrames depsCohs).2

inductive DepsCohsExtension :
    (p k : Nat) -> DepsCohs (A := A) p k -> Type 1 where
  | TopCohDep {p : Nat} {depsCohs : DepsCohs (A := A) p 0}
      (E : mkFrame (mkDepsRestr depsCohs) -> Type) :
      DepsCohsExtension p 0 depsCohs
  | AddCohDep {p k : Nat} (depsCohs : DepsCohs (A := A) p.succ k)
      (extraDepsCohs : DepsCohsExtension p.succ k depsCohs) :
      DepsCohsExtension p k.succ (proj1DepsCohs depsCohs)

def mkExtraDeps {p k : Nat} {depsCohs : DepsCohs (A := A) p k}
    (extraDepsCohs : DepsCohsExtension (A := A) p k depsCohs) :
    DepsRestrExtension (A := A) p.succ k (mkDepsRestr depsCohs) :=
  match extraDepsCohs with
  | DepsCohsExtension.TopCohDep E =>
      DepsRestrExtension.TopRestrDep E
  | DepsCohsExtension.AddCohDep depsCohs' extraDepsCohs' =>
      DepsRestrExtension.AddRestrDep
        (mkDepsRestr depsCohs') (mkExtraDeps extraDepsCohs')

def mkRestrPaintingAux :
    (q : Nat) -> {p k : Nat} -> {depsCohs : DepsCohs (A := A) p k} ->
      (extraDepsCohs : DepsCohsExtension (A := A) p k depsCohs) ->
      (Hq : q ≤ k) -> (ε : A.arity) ->
      (d : mkFrame (proj1DepsRestr (mkDepsRestr depsCohs))) ->
      (mkPaintings (proj1DepsRestr (mkDepsRestr depsCohs))
        (DepsRestrExtension.AddRestrDep
          (mkDepsRestr depsCohs) (mkExtraDeps extraDepsCohs))).2 d ->
      (mkDepsRestr depsCohs).paintings.2
        ((mkDepsRestr depsCohs).restrFrames.2 q Hq ε d)
  | 0, _, _, _, _, _, ε, _, c => c.1 ε
  | q + 1, _, _, _, DepsCohsExtension.TopCohDep _, Hq, _, _, _ =>
      nomatch leR_O_contra (n := q) Hq
  | q + 1, _, _, _, DepsCohsExtension.AddCohDep depsCohs' extraDepsCohs',
      Hq, ε, d, c =>
      (mkRestrLayer depsCohs'.restrPaintings depsCohs'.cohs
          q (⇓ᵣ Hq) ε d c.1 ;
        mkRestrPaintingAux q extraDepsCohs' (⇓ᵣ Hq) ε
          (d ; c.1) c.2)

def mkRestrPainting {p k : Nat}
    {depsCohs : DepsCohs (A := A) p k}
    (extraDepsCohs : DepsCohsExtension (A := A) p k depsCohs) :
    mkRestrPaintingType (mkExtraDeps extraDepsCohs) :=
  fun q Hq ε d c =>
    mkRestrPaintingAux q extraDepsCohs Hq ε d c

theorem mkRestrPainting_q0 {p k : Nat}
    {depsCohs : DepsCohs (A := A) p k}
    (extraDepsCohs : DepsCohsExtension (A := A) p k depsCohs)
    (ε : A.arity)
    (d : mkFrame (proj1DepsRestr (mkDepsRestr depsCohs)))
    (l : mkLayerOf (mkDepsRestr depsCohs) d)
    (c : mkPainting (mkExtraDeps extraDepsCohs) (d ; l)) :
    mkRestrPainting extraDepsCohs 0 leR_O ε d (l ; c) = l ε := by
  rfl

def mkRestrPaintingsPrefix {A : AritySig} :
    {p k : Nat} -> {depsCohs : DepsCohs (A := A) p k} ->
      (extraDepsCohs : DepsCohsExtension (A := A) p k depsCohs) ->
      mkRestrPaintingTypes (proj1DepsRestr (mkDepsRestr depsCohs))
        (DepsRestrExtension.AddRestrDep
          (mkDepsRestr depsCohs) (mkExtraDeps extraDepsCohs))
  | 0, _, _, _ => PUnit.unit
  | _ + 1, _, depsCohs, extraDepsCohs =>
      let extraDepsCohs' := DepsCohsExtension.AddCohDep depsCohs extraDepsCohs
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
  let addedDepsCohs := DepsCohsExtension.AddCohDep depsCohs extraDepsCohs
  forall (q : Nat) (Hq : q ≤ k) (r : Nat) (Hr : r ≤ q)
    (ε ω : A.arity)
    (d : mkFrame (proj1DepsRestr (mkDepsRestr (proj1DepsCohs depsCohs))))
    (c : (mkPaintings
      (proj1DepsRestr (mkDepsRestr (proj1DepsCohs depsCohs)))
      (DepsRestrExtension.AddRestrDep
        (mkDepsRestr (proj1DepsCohs depsCohs))
        (mkExtraDeps addedDepsCohs))).2 d),
    rew [fun x => depsCohs.deps.paintings.2 x]
      (depsCohs.cohs.2 q Hq r Hr ε ω d) in
    depsCohs.restrPaintings.2 q Hq ε _
      ((mkRestrPaintings addedDepsCohs).2 r (Hr ↕ ↑ᵣ Hq) ω d c) =
    depsCohs.restrPaintings.2 r (Hr ↕ Hq) ω _
      ((mkRestrPaintings addedDepsCohs).2 q.succ (⇑ᵣ Hq) ε d c)

def mkCohPaintingTypes {A : AritySig} :
    {p k : Nat} -> {depsCohs : DepsCohs (A := A) p k} ->
      DepsCohsExtension (A := A) p k depsCohs -> Type 1
  | 0, _, _, _ => PUnit.{2}
  | _ + 1, _, depsCohs, extraDepsCohs =>
      { _ : mkCohPaintingTypes
          (DepsCohsExtension.AddCohDep depsCohs extraDepsCohs) &T
        mkCohPaintingType extraDepsCohs }

/- In the Rocq source, the proof of `mkCohLayer` needs the 2-coherence
`mkCoh2Frame`, an equation between two composite frame-equality proofs,
established there by the local UIP of the frame `HSet`. In Lean, equality
proofs live in `Prop` and are definitionally irrelevant, so that lemma (and
the transport bookkeeping consuming it) disappears: once both sides are
reduced to transports of the same term, the paths need not be compared. -/
theorem mkCohLayer {p k : Nat}
    {depsCohs : DepsCohs (A := A) p.succ k}
    (extraDepsCohs :
      DepsCohsExtension (A := A) p.succ k depsCohs)
    (cohPaintings : mkCohPaintingTypes (A := A) extraDepsCohs)
    {prevCohFrames : mkCohFrameTypes
      (deps := proj1DepsRestr (mkDepsRestr depsCohs))
      (extraDeps := DepsRestrExtension.AddRestrDep
        (mkDepsRestr depsCohs) (mkExtraDeps extraDepsCohs))
      (mkRestrPaintings extraDepsCohs).1}
    (q : Nat) {Hq : q ≤ k} (r : Nat) {Hr : r ≤ q}
    (ε ω : A.arity)
    (d : mkFrame (proj1DepsRestr
      (mkDepsRestr (toDepsCohs prevCohFrames.1))))
    (l : mkLayer
      (mkPaintings (toDepsCohs prevCohFrames.1).deps
        (toDepsCohs prevCohFrames.1).extraDeps)
      (mkRestrFrames (toDepsCohs prevCohFrames.1)) d) :
    rew [fun x => mkLayer depsCohs.deps.paintings
        depsCohs.deps.restrFrames x]
      (prevCohFrames.2 q.succ (⇑ᵣ Hq) r.succ (⇑ᵣ Hr) ε ω d) in
    mkRestrLayer depsCohs.restrPaintings depsCohs.cohs q Hq ε _
      (mkRestrLayer (mkRestrPaintings extraDepsCohs).1
        prevCohFrames r (Hr ↕ ↑ᵣ Hq) ω d l) =
    mkRestrLayer depsCohs.restrPaintings depsCohs.cohs r (Hr ↕ Hq) ω _
      (mkRestrLayer (mkRestrPaintings extraDepsCohs).1
        prevCohFrames q.succ (⇑ᵣ Hq) ε d l) := by
  funext θ
  erw [← map_subst_app]
  simp only [mkRestrLayer]
  erw [← map_subst
    (P := fun x => (proj1DepsRestr (mkDepsRestr depsCohs)).paintings.2 x)
    (f := fun x z => depsCohs.restrPaintings.2 q Hq ε x z)]
  erw [← map_subst
    (P := fun x => (proj1DepsRestr (mkDepsRestr depsCohs)).paintings.2 x)
    (f := fun x z => depsCohs.restrPaintings.2 r (Hr ↕ Hq) ω x z)]
  erw [← cohPaintings.2 q Hq r Hr ε ω
    ((mkRestrFrames (toDepsCohs prevCohFrames.1)).2 0 leR_O θ d)
    (l θ)]
  erw [rew_map
    (P := fun x => depsCohs.deps.paintings.2 x)
    (f := fun x => depsCohs.deps.restrFrames.2 0 leR_O θ x)]
  erw [rew_map
    (P := fun x => depsCohs.deps.paintings.2 x)
    (f := fun x => depsCohs.deps.restrFrames.2 q Hq ε x)]
  erw [rew_map
    (P := fun x => depsCohs.deps.paintings.2 x)
    (f := fun x => depsCohs.deps.restrFrames.2 r (Hr ↕ Hq) ω x)]
  repeat erw [rew_compose]
  rfl

def mkCohFrames {A : AritySig} :
    {p k : Nat} -> {depsCohs : DepsCohs (A := A) p k} ->
      {extraDepsCohs : DepsCohsExtension (A := A) p k depsCohs} ->
      mkCohPaintingTypes (A := A) extraDepsCohs ->
      mkCohFrameTypes (deps := mkDepsRestr depsCohs)
        (extraDeps := mkExtraDeps extraDepsCohs)
        (mkRestrPaintings extraDepsCohs)
  | 0, _, _, _, _ =>
      (PUnit.unit ; fun _ _ _ _ _ _ _ => rfl)
  | _ + 1, _, depsCohs, extraDepsCohs, cohPaintings =>
      let extraDepsCohs' :=
        DepsCohsExtension.AddCohDep depsCohs extraDepsCohs
      let prevCohFrames :=
        mkCohFrames (depsCohs := proj1DepsCohs depsCohs)
          (extraDepsCohs := extraDepsCohs') cohPaintings.1
      (prevCohFrames ;
        fun q Hq r Hr ε ω d =>
          eq_existT_curried
            (prevCohFrames.2 q.succ (⇑ᵣ Hq) r.succ (⇑ᵣ Hr)
              ε ω d.1)
            (mkCohLayer extraDepsCohs cohPaintings q (Hq := Hq)
              r (Hr := Hr) ε ω d.1 d.2))

structure DepsCohs2 (p k : Nat) where
  depsCohs : DepsCohs (A := A) p k
  extraDepsCohs : DepsCohsExtension (A := A) p k depsCohs
  cohPaintings : mkCohPaintingTypes extraDepsCohs

def toDepsCohs2 {p k : Nat} {depsCohs : DepsCohs (A := A) p k}
    {extraDepsCohs : DepsCohsExtension (A := A) p k depsCohs}
    (cohPaintings : mkCohPaintingTypes extraDepsCohs) :
    DepsCohs2 (A := A) p k :=
  { depsCohs := depsCohs
    extraDepsCohs := extraDepsCohs
    cohPaintings := cohPaintings }

def proj1DepsCohs2 {p k : Nat}
    (depsCohs2 : DepsCohs2 (A := A) p.succ k) :
    DepsCohs2 (A := A) p k.succ :=
  { depsCohs := proj1DepsCohs depsCohs2.depsCohs
    extraDepsCohs :=
      DepsCohsExtension.AddCohDep
        depsCohs2.depsCohs depsCohs2.extraDepsCohs
    cohPaintings := depsCohs2.cohPaintings.1 }

def mkDepsCohs {p k : Nat}
    (depsCohs2 : DepsCohs2 (A := A) p k) :
    DepsCohs (A := A) p.succ k :=
  { deps := mkDepsRestr depsCohs2.depsCohs
    extraDeps := mkExtraDeps depsCohs2.extraDepsCohs
    restrPaintings := mkRestrPaintings depsCohs2.extraDepsCohs
    cohs := mkCohFrames depsCohs2.cohPaintings }

inductive DepsCohs2Extension :
    (p k : Nat) -> DepsCohs2 (A := A) p k -> Type 1 where
  | TopCoh2Dep {p : Nat} {depsCohs2 : DepsCohs2 (A := A) p 0}
      (E : mkFrame (mkDepsRestr (mkDepsCohs depsCohs2)) -> Type) :
      DepsCohs2Extension p 0 depsCohs2
  | AddCoh2Dep {p k : Nat} (depsCohs2 : DepsCohs2 (A := A) p.succ k)
      (extraDepsCohs2 : DepsCohs2Extension p.succ k depsCohs2) :
      DepsCohs2Extension p k.succ (proj1DepsCohs2 depsCohs2)

def mkExtraCohs {p k : Nat} {depsCohs2 : DepsCohs2 (A := A) p k}
    (extraDepsCohs2 :
      DepsCohs2Extension (A := A) p k depsCohs2) :
    DepsCohsExtension (A := A) p.succ k (mkDepsCohs depsCohs2) :=
  match extraDepsCohs2 with
  | DepsCohs2Extension.TopCoh2Dep E =>
      DepsCohsExtension.TopCohDep E
  | DepsCohs2Extension.AddCoh2Dep depsCohs2' extraDepsCohs2' =>
      DepsCohsExtension.AddCohDep
        (mkDepsCohs depsCohs2') (mkExtraCohs extraDepsCohs2')

theorem mkCohPainting {p k : Nat}
    {depsCohs2 : DepsCohs2 (A := A) p k}
    (extraDepsCohs2 :
      DepsCohs2Extension (A := A) p k depsCohs2) :
    mkCohPaintingType (mkExtraCohs extraDepsCohs2) := by
  intro q Hq r Hr ε ω d c
  cases c with
  | mk l c =>
      cases r with
      | zero =>
          rfl
      | succ r =>
          cases q with
          | zero =>
              exact nomatch leR_O_contra Hr
          | succ q =>
              cases extraDepsCohs2 with
              | TopCoh2Dep _ =>
                  exact nomatch leR_O_contra (n := q) Hq
              | AddCoh2Dep depsCohs2' extraDepsCohs2' =>
                  exact
                    eq_existT_curried_dep
                      (Q := fun x =>
                        mkPainting depsCohs2'.depsCohs.extraDeps x)
                      (Hu := mkCohLayer
                        depsCohs2'.extraDepsCohs depsCohs2'.cohPaintings
                        q (Hq := ⇓ᵣ Hq) r (Hr := ⇓ᵣ Hr) ε ω d l)
                      (Hv := mkCohPainting extraDepsCohs2'
                        q (⇓ᵣ Hq) r (⇓ᵣ Hr) ε ω (d ; l) c)

def mkCohPaintings {A : AritySig} :
    {p k : Nat} -> {depsCohs2 : DepsCohs2 (A := A) p k} ->
      (extraDepsCohs2 :
        DepsCohs2Extension (A := A) p k depsCohs2) ->
      mkCohPaintingTypes (mkExtraCohs extraDepsCohs2)
  | 0, _, _, extraDepsCohs2 =>
      (PUnit.unit ; mkCohPainting extraDepsCohs2)
  | _ + 1, _, depsCohs2, extraDepsCohs2 =>
      let extraDepsCohs2' :=
        DepsCohs2Extension.AddCoh2Dep depsCohs2 extraDepsCohs2
      (mkCohPaintings extraDepsCohs2' ;
        mkCohPainting extraDepsCohs2)

structure νSetData (p : Nat) where
  frames : mkFrameTypes p 0
  paintings : mkPaintingTypes p 0 frames
  restrFrames : mkRestrFrameTypes (A := A) paintings
  restrPaintings :
    (E : mkFrame (toDepsRestr (A := A) restrFrames) -> Type) ->
      mkRestrPaintingTypes (toDepsRestr (A := A) restrFrames)
        (DepsRestrExtension.TopRestrDep E)
  cohFrames :
    (E : mkFrame (toDepsRestr (A := A) restrFrames) -> Type) ->
      mkCohFrameTypes
        (deps := toDepsRestr (A := A) restrFrames)
        (extraDeps := DepsRestrExtension.TopRestrDep E)
        (restrPaintings E)
  cohPaintings :
    (E : mkFrame (toDepsRestr (A := A) restrFrames) -> Type) ->
      let deps := toDepsRestr (A := A) restrFrames
      let extraDeps := DepsRestrExtension.TopRestrDep E
      let depsCohs :=
        toDepsCohs (deps := deps) (extraDeps := extraDeps)
          (restrPaintings := restrPaintings E) (cohFrames E)
      (E' : mkFrame (mkDepsRestr depsCohs) -> Type) ->
        mkCohPaintingTypes
          (DepsCohsExtension.TopCohDep (depsCohs := depsCohs) E')

abbrev νSetData.depsRestr {p : Nat} (C : νSetData (A := A) p) :
    DepsRestr (A := A) p 0 :=
  toDepsRestr C.restrFrames

abbrev νSetData.depsCohs {p : Nat} (C : νSetData (A := A) p)
    (E : mkFrame C.depsRestr -> Type) :
    DepsCohs (A := A) p 0 :=
  toDepsCohs (deps := C.depsRestr)
    (extraDeps := DepsRestrExtension.TopRestrDep E)
    (restrPaintings := C.restrPaintings E) (C.cohFrames E)

abbrev νSetData.depsCohs2 {p : Nat} (C : νSetData (A := A) p)
    (E : mkFrame C.depsRestr -> Type)
    (E' : mkFrame (mkDepsRestr (C.depsCohs E)) -> Type) :
    DepsCohs2 (A := A) p 0 :=
  toDepsCohs2 (depsCohs := C.depsCohs E)
    (extraDepsCohs :=
      DepsCohsExtension.TopCohDep (depsCohs := C.depsCohs E) E')
    (C.cohPaintings E E')

def mkνSetData {p : Nat} (C : νSetData (A := A) p)
    (E : mkFrame C.depsRestr -> Type) : νSetData (A := A) p.succ :=
  let deps := C.depsRestr
  let extraDeps := DepsRestrExtension.TopRestrDep E
  let depsCohs := C.depsCohs E
  { frames := mkFrames deps
    paintings := mkPaintings deps extraDeps
    restrFrames := mkRestrFrames depsCohs
    restrPaintings := fun E' =>
      mkRestrPaintings
        (DepsCohsExtension.TopCohDep (depsCohs := depsCohs) E')
    cohFrames := fun E' =>
      mkCohFrames (C.cohPaintings E E')
    cohPaintings := fun E' E'' =>
      mkCohPaintings
        (DepsCohs2Extension.TopCoh2Dep
          (depsCohs2 := C.depsCohs2 E E') E'') }

structure νSet (p : Nat) where
  Prefix : Type 1
  data : Prefix -> νSetData (A := A) p

def mkPrefix {p : Nat} (C : νSet (A := A) p) : Type 1 :=
  { D : C.Prefix &T mkFrame (C.data D).depsRestr -> Type }

def mkνSet0 : νSet (A := A) 0 :=
  { Prefix := PUnit.{2}
    data := fun _ =>
      { frames := PUnit.unit
        paintings := PUnit.unit
        restrFrames := PUnit.unit
        restrPaintings := fun _ => PUnit.unit
        cohFrames := fun _ => PUnit.unit
        cohPaintings := fun _ _ => PUnit.unit } }

def mkνSet {p : Nat} (C : νSet (A := A) p) : νSet (A := A) p.succ :=
  { Prefix := mkPrefix C
    data := fun D => mkνSetData (C.data D.1) D.2 }

def νSetAt : (n : Nat) -> νSet (A := A) n
  | 0 => mkνSet0
  | n + 1 => mkνSet (νSetAt n)

/-! Closing the tower as an ω-limit. -/

/-- The type of level-`p` extensions of a prefix, i.e. the type of the
`this` component that a level-`p+1` prefix adds on top of a level-`p`
prefix. -/
def mkExtensionType {p : Nat} {C : νSet (A := A) p} (D : C.Prefix) :
    Type 1 :=
  mkFrame (C.data D).depsRestr -> Type

/-- Since `(νSetAt l.succ).Prefix` is definitionally a Σ-type over
`(νSetAt l).Prefix`, truncating a prefix to the previous level is plain
first projection; a coherent tower of prefixes above a given level-`n`
prefix `X` is thus an ω-limit presented with `.1` as the (definitional)
bonding maps, with no recursively defined truncation function. -/
structure νSetFrom (n : Nat) (X : (νSetAt (A := A) n).Prefix) :
    Type 1 where
  approx : (l : Nat) -> n ≤ l -> (νSetAt (A := A) l).Prefix
  approxO : approx n leR_refl = X
  approxS : forall (l : Nat) (Hl : n ≤ l) (HSl : n ≤ l.succ),
    (approx l.succ HSl).1 = approx l Hl

/-- The two destructors of the coinductive presentation: `this` observes
the level-`n` extension chosen by a tower over `X`... -/
def νSetFrom.«this» {n : Nat} {X : (νSetAt (A := A) n).Prefix}
    (ν : νSetFrom (A := A) n X) : mkExtensionType X :=
  rew [mkExtensionType]
    ν.approxS n leR_refl (↑ᵣ leR_refl) ⬝ ν.approxO in
  (ν.approx n.succ (↑ᵣ leR_refl)).2

/-- ...where the level-`n.succ` entry of the chain is exactly `X` paired
with that extension... -/
theorem νSetFrom.approxEta {n : Nat} {X : (νSetAt (A := A) n).Prefix}
    (ν : νSetFrom (A := A) n X) :
    ν.approx n.succ (↑ᵣ leR_refl) = (X ; ν.this) :=
  eq_sigT_fst (ν.approxS n leR_refl (↑ᵣ leR_refl) ⬝ ν.approxO)

/-- ...and `next` observes the tail: the same tower, one level up, over
the extended prefix (proofs of `n ≤ l` being definitionally irrelevant,
all coherences are inherited as such). -/
def νSetFrom.next {n : Nat} {X : (νSetAt (A := A) n).Prefix}
    (ν : νSetFrom (A := A) n X) :
    νSetFrom (A := A) n.succ (X ; ν.this) where
  approx l Hl := ν.approx l (↓ᵣ Hl)
  approxO := ν.approxEta
  approxS l Hl HSl := ν.approxS l (↓ᵣ Hl) (↓ᵣ HSl)

/-- The general introduction rule of the ω-limit: a tower above level `n`
is nothing but a globally coherent chain of prefixes, read from level `n`
on. Both destructors act on it without touching the chain: when the chain
is *definitionally* coherent (`HCh` pointwise `rfl`),
`(towerOfChain Ch HCh n).this` is `(Ch n.succ).2` and
`(towerOfChain Ch HCh n).next` is `towerOfChain Ch HCh n.succ`, by
conversion. -/
def towerOfChain (Ch : (l : Nat) -> (νSetAt (A := A) l).Prefix)
    (HCh : forall l : Nat, (Ch l.succ).1 = Ch l) (n : Nat) :
    νSetFrom (A := A) n (Ch n) where
  approx l _ := Ch l
  approxO := rfl
  approxS l _ _ := HCh l

/-- The anamorphism closing the tower from a step function: the analog,
for the ground tower, of building an element by `cofix`. -/
def mkApprox
    (F : forall (n : Nat) (X : (νSetAt (A := A) n).Prefix),
      mkExtensionType X) :
    (l : Nat) -> (νSetAt (A := A) l).Prefix
  | 0 => PUnit.unit
  | l + 1 => (mkApprox F l ; F l (mkApprox F l))

def ana
    (F : forall (n : Nat) (X : (νSetAt (A := A) n).Prefix),
      mkExtensionType X) : νSetFrom (A := A) 0 PUnit.unit :=
  towerOfChain (mkApprox F) (fun _ => rfl) 0

abbrev νSets : Type 1 :=
  νSetFrom (A := A) 0 PUnit.unit

end Arity

end νSet

def ArityUnit : AritySig :=
  { arity := Unit }

def ArityBool : AritySig :=
  { arity := Bool }

abbrev AugmentedSemiSimplicial : Type 1 :=
  νSet.νSets (A := ArityUnit)

abbrev SemiSimplicial : Type 1 :=
  νSet.νSetFrom (A := ArityUnit) 1
    (PUnit.unit ; fun _ => Unit)

abbrev SemiCubical : Type 1 :=
  νSet.νSets (A := ArityBool)

/- Some example. -/

def SemiSimplicial4 : Type 1 :=
  (νSet.νSetAt (A := ArityUnit) 4).Prefix

#deep_reduce SemiSimplicial4

end Bonak
