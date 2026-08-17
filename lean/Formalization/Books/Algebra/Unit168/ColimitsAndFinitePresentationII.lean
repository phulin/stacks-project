import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.RingTheory.RingHom.Smooth
import Formalization.Books.Algebra.Unit127.ColimitsAndFinitePresentation
import Formalization.Books.Algebra.Unit136.SyntomicMorphisms

/-!
# Commutative Algebra, Chapter 168: Colimits and maps of finite presentation, II

This file records the source-facing interfaces for the approximation, descent,
and eventual-colimit statements in the section.  The directed ring and module
diagrams reuse the canonical Chapter 127 presentations; the small structures
below add only the module base-change and finiteness data displayed in this
chapter.
-/

namespace Formalization.Books.Algebra.Unit168

open CategoryTheory
open Formalization.Books.Algebra.Unit127
open Formalization.Books.Algebra.Unit136
open scoped TensorProduct

universe u

noncomputable section

/-! ## Flat module approximation data -/

/--
The base-change data appearing in the approximation of a flat module.

The maps `baseToTarget`, `baseToStage`, and `stageToTarget` form the ring
square in the source.  The two equivalences record the displayed ring and
module base-change identifications, while `moduleMap` records the map from the
stage module to the target module.
-/
structure FlatModuleStageData
    {A R S M : Type u} [CommRing A] [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M]
    (a : A →+* R) (f : R →+* S) where
  stage : Type u
  [stageCommRing : CommRing stage]
  stageModule : Type u
  [stageModuleAddCommGroup : AddCommGroup stageModule]
  [stageModuleStructure : Module stage stageModule]
  baseToStage : A →+* stage
  stageToTarget : stage →+* S
  commutes : stageToTarget.comp baseToStage = f.comp a
  flat :
    letI : Module A stageModule := Module.compHom stageModule baseToStage
    Module.Flat A stageModule
  moduleMap :
    letI : Module stage M := Module.compHom M stageToTarget
    stageModule →ₗ[stage] M
  ringBaseChangeIsIso :
    letI : Algebra A R := a.toAlgebra
    letI : Algebra A stage := baseToStage.toAlgebra
    letI : Algebra A S := (f.comp a).toAlgebra
    IsIso (CommRingCat.ofHom
      (baseChangeRingHomOfCompatible a baseToStage f stageToTarget commutes.symm))
  moduleBaseChange :
    letI : Algebra stage S := stageToTarget.toAlgebra
    S ⊗[stage] stageModule ≃ₗ[S] M
  moduleBaseChange_spec :
    letI : Algebra stage S := stageToTarget.toAlgebra
    ∀ (s : S) (m : stageModule),
      moduleBaseChange (s ⊗ₜ[stage] m) = s • moduleMap m

/-- The absolute approximation in part (1), including finite type over the
integers, finite type of the stage algebra, and finite generation of the stage
module. -/
structure AbsoluteFlatModuleApproximation
    {R S M : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M] (f : R →+* S) where
  R₀ : Type u
  [commRingR₀ : CommRing R₀]
  baseToTarget : R₀ →+* R
  data : FlatModuleStageData (M := M) baseToTarget f
  finiteTypeOverIntegers : RingHom.FiniteType (Int.castRingHom R₀)
  stageMapFiniteType :
    letI : CommRing data.stage := data.stageCommRing
    RingHom.FiniteType data.baseToStage
  stageModuleFinite :
    letI : CommRing data.stage := data.stageCommRing
    letI : AddCommGroup data.stageModule := data.stageModuleAddCommGroup
    letI : Module data.stage data.stageModule := data.stageModuleStructure
    Module.Finite data.stage data.stageModule

/-- The stage data in part (2), where the stage algebra and module are
finitely presented. -/
structure FinitePresentationFlatModuleStage
    {A R S M : Type u} [CommRing A] [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M]
    (a : A →+* R) (f : R →+* S) where
  data : FlatModuleStageData (M := M) a f
  stageMapFinitePresentation :
    letI : CommRing data.stage := data.stageCommRing
    RingHom.FinitePresentation data.baseToStage
  stageModuleFinitePresentation :
    letI : CommRing data.stage := data.stageCommRing
    letI : AddCommGroup data.stageModule := data.stageModuleAddCommGroup
    letI : Module data.stage data.stageModule := data.stageModuleStructure
    Module.FinitePresentation data.stage data.stageModule

/-- A directed algebra colimit with the distinguished index `0` used in the
colimit lemmas of the source. -/
structure DirectedAlgebraColimitWithZero
    {A₀ A : Type u} [CommRing A₀] [CommRing A]
    (f : A₀ →+* A) where
  base : DirectedAlgebraColimit f
  zero : base.index

/-! ## The directed flat-module system in part (3) -/

/-- The source's directed colimit of ring maps and finitely presented modules.

`moduleColimit` is Chapter 127's canonical module-colimit package.  The extra
fields record precisely the finite-presentation hypotheses and the displayed
ring transition isomorphisms from the source.
-/
structure DirectedFinitelyPresentedFlatModuleSystem
    {R S M : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M] (f : R →+* S) where
  ringColimit : DirectedRingMapColimit f
  moduleColimit : DirectedModuleColimitPresentation ringColimit M
  ringMapFinitePresentation :
    ∀ i, letI : Preorder ringColimit.index := ringColimit.indexPreorder
      RingHom.FinitePresentation (ringColimit.stageMap i)
  stageModuleFinitePresentation :
    ∀ i, letI : Preorder ringColimit.index := ringColimit.indexPreorder
      Module.FinitePresentation (ringColimit.targetDiagram.obj i)
        (moduleColimit.stage i).module
  ringTransitionIsomorphism :
    ∀ {i j : ringColimit.index}
      (hij : ringColimit.indexPreorder.le i j),
      letI : Preorder ringColimit.index := ringColimit.indexPreorder
      IsIso (CommRingCat.ofHom (ringColimit.transitionBaseChange hij))

/-! ## Approximation of flat modules -/

/-- A finitely presented flat module admits the three approximations stated in
the source: an absolute finite-type approximation, a stage in every directed
ring colimit, and eventual flatness in a compatible finitely presented system.
-/
theorem flatFinitePresentationLimitFlat
    {R S M : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M]
    (f : R →+* S)
    (hS : RingHom.FinitePresentation f)
    (hM : Module.FinitePresentation S M)
    (hflat :
      letI : Module R M := Module.compHom M f
      Module.Flat R M) :
    Nonempty (AbsoluteFlatModuleApproximation (M := M) f) ∧
      (∀ (D : DirectedRingColimit (R := R)),
        ∃ i, letI : Preorder D.index := D.indexPreorder
          Nonempty
            (FinitePresentationFlatModuleStage (M := M)
              (D.stageToTarget i) f)) ∧
      (∀ (D : DirectedFinitelyPresentedFlatModuleSystem (M := M) f),
        ∃ i₀, letI : Preorder D.ringColimit.index :=
            D.ringColimit.indexPreorder
          ∀ i, i₀ ≤ i →
            letI : Module (D.ringColimit.sourceDiagram.obj i)
                (D.moduleColimit.stage i).module :=
              Module.compHom (D.moduleColimit.stage i).module
                (D.ringColimit.stageMap i)
            Module.Flat (D.ringColimit.sourceDiagram.obj i)
              (D.moduleColimit.stage i).module) := by
  sorry

/-! ## Descent of faithfully flat finite-presentation maps -/

/-- The commutative diagram and base-change identification in the second
source lemma. -/
structure FaithfullyFlatFinitePresentationDescent
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : A →+* B) where
  A₀ : Type u
  [commRingA₀ : CommRing A₀]
  B₀ : Type u
  [commRingB₀ : CommRing B₀]
  rToA₀ : R →+* A₀
  a₀ToA : A₀ →+* A
  a₀ToB₀ : A₀ →+* B₀
  b₀ToB : B₀ →+* B
  rTriangle : a₀ToA.comp rToA₀ = f
  square : b₀ToB.comp a₀ToB₀ = g.comp a₀ToA
  rToA₀FinitePresentation : RingHom.FinitePresentation rToA₀
  a₀ToB₀FaithfullyFlat : RingHom.FaithfullyFlat a₀ToB₀
  a₀ToB₀FinitePresentation : RingHom.FinitePresentation a₀ToB₀
  baseChangeIsIso :
    letI : Algebra A₀ A := a₀ToA.toAlgebra
    letI : Algebra A₀ B₀ := a₀ToB₀.toAlgebra
    letI : Algebra A₀ B := (g.comp a₀ToA).toAlgebra
    IsIso (CommRingCat.ofHom
      (baseChangeRingHomOfCompatible a₀ToA a₀ToB₀ g b₀ToB square.symm))

/-- Faithfully flat finite-presentation maps descend to a finite-presentation
faithfully flat stage after changing the base along `R → A₀`. -/
theorem descendFaithfullyFlatFinitePresentation
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : A →+* B)
    (hff : RingHom.FaithfullyFlat g)
    (hfp : RingHom.FinitePresentation g) :
    Nonempty (FaithfullyFlatFinitePresentationDescent f g) := by
  sorry

/-! ## Properties detected at a finite stage -/

/-- Finiteness of a base-changed algebra map is detected at a stage of a
directed colimit. -/
theorem colimitFinite
    {A₀ A B₀ C₀ : Type u}
    [CommRing A₀] [CommRing A] [CommRing B₀] [CommRing C₀]
    [Algebra A₀ B₀] [Algebra A₀ C₀]
    (f : A₀ →+* A) (D : DirectedAlgebraColimitWithZero f)
    (φ₀ : B₀ →ₐ[A₀] C₀)
    (hfinite : RingHom.Finite
      (directedAlgebraTensorMapTarget f φ₀).toRingHom)
    (hfiniteType : RingHom.FiniteType φ₀.toRingHom) :
    letI : Preorder D.base.index := D.base.indexPreorder
    ∃ i, D.zero ≤ i ∧
      RingHom.Finite (directedAlgebraTensorMapStage D.base i φ₀).toRingHom := by
  sorry

/-- Surjectivity of a base-changed algebra map is detected at a finite stage.
-/
theorem colimitSurjective
    {A₀ A B₀ C₀ : Type u}
    [CommRing A₀] [CommRing A] [CommRing B₀] [CommRing C₀]
    [Algebra A₀ B₀] [Algebra A₀ C₀]
    (f : A₀ →+* A) (D : DirectedAlgebraColimitWithZero f)
    (φ₀ : B₀ →ₐ[A₀] C₀)
    (hsurjective : Function.Surjective
      (directedAlgebraTensorMapTarget f φ₀).toRingHom)
    (hfiniteType : RingHom.FiniteType φ₀.toRingHom) :
    letI : Preorder D.base.index := D.base.indexPreorder
    ∃ i, D.zero ≤ i ∧
      Function.Surjective
        (directedAlgebraTensorMapStage D.base i φ₀).toRingHom := by
  sorry

/-- Unramifiedness of a base-changed algebra map is detected at a finite stage.
-/
/- Mathlib exposes formal unramifiedness directly; the finite-type conjunction
is the standard ring-map notion used by the source. -/
def IsUnramified
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  RingHom.FiniteType f ∧ RingHom.FormallyUnramified f

theorem colimitUnramified
    {A₀ A B₀ C₀ : Type u}
    [CommRing A₀] [CommRing A] [CommRing B₀] [CommRing C₀]
    [Algebra A₀ B₀] [Algebra A₀ C₀]
    (f : A₀ →+* A) (D : DirectedAlgebraColimitWithZero f)
    (φ₀ : B₀ →ₐ[A₀] C₀)
    (hunramified : IsUnramified
      (directedAlgebraTensorMapTarget f φ₀).toRingHom)
    (hfiniteType : RingHom.FiniteType φ₀.toRingHom) :
    letI : Preorder D.base.index := D.base.indexPreorder
    ∃ i, D.zero ≤ i ∧
      IsUnramified
        (directedAlgebraTensorMapStage D.base i φ₀).toRingHom := by
  sorry

/-- An isomorphism after base change is detected at a finite stage when the
original algebra map is finitely presented. -/
theorem colimitIsomorphism
    {A₀ A B₀ C₀ : Type u}
    [CommRing A₀] [CommRing A] [CommRing B₀] [CommRing C₀]
    [Algebra A₀ B₀] [Algebra A₀ C₀]
    (f : A₀ →+* A) (D : DirectedAlgebraColimitWithZero f)
    (φ₀ : B₀ →ₐ[A₀] C₀)
    (hiso : IsIso (CommRingCat.ofHom
      (directedAlgebraTensorMapTarget f φ₀).toRingHom))
    (hfinitePresentation : RingHom.FinitePresentation φ₀.toRingHom) :
    letI : Preorder D.base.index := D.base.indexPreorder
    ∃ i, D.zero ≤ i ∧
      IsIso (CommRingCat.ofHom
        (directedAlgebraTensorMapStage D.base i φ₀).toRingHom) := by
  sorry

/-- Étaleness of a finitely presented base-changed map is detected at a finite
stage. -/
theorem colimitEtale
    {A₀ A B₀ C₀ : Type u}
    [CommRing A₀] [CommRing A] [CommRing B₀] [CommRing C₀]
    [Algebra A₀ B₀] [Algebra A₀ C₀]
    (f : A₀ →+* A) (D : DirectedAlgebraColimitWithZero f)
    (φ₀ : B₀ →ₐ[A₀] C₀)
    (hetale : RingHom.Etale
      (directedAlgebraTensorMapTarget f φ₀).toRingHom)
    (hfinitePresentation : RingHom.FinitePresentation φ₀.toRingHom) :
    letI : Preorder D.base.index := D.base.indexPreorder
    ∃ i, D.zero ≤ i ∧
      RingHom.Etale
        (directedAlgebraTensorMapStage D.base i φ₀).toRingHom := by
  sorry

/-- Smoothness of a finitely presented base-changed map is detected at a finite
stage. -/
theorem colimitSmooth
    {A₀ A B₀ C₀ : Type u}
    [CommRing A₀] [CommRing A] [CommRing B₀] [CommRing C₀]
    [Algebra A₀ B₀] [Algebra A₀ C₀]
    (f : A₀ →+* A) (D : DirectedAlgebraColimitWithZero f)
    (φ₀ : B₀ →ₐ[A₀] C₀)
    (hsmooth : RingHom.Smooth
      (directedAlgebraTensorMapTarget f φ₀).toRingHom)
    (hfinitePresentation : RingHom.FinitePresentation φ₀.toRingHom) :
    letI : Preorder D.base.index := D.base.indexPreorder
    ∃ i, D.zero ≤ i ∧
      RingHom.Smooth
        (directedAlgebraTensorMapStage D.base i φ₀).toRingHom := by
  sorry

/-- Syntomic and relative-global-complete-intersection properties descend to
a sufficiently large stage. -/
theorem colimitLci
    {A₀ A B₀ C₀ : Type u}
    [CommRing A₀] [CommRing A] [CommRing B₀] [CommRing C₀]
    [Algebra A₀ B₀] [Algebra A₀ C₀]
    (f : A₀ →+* A) (D : DirectedAlgebraColimitWithZero f)
    (φ₀ : B₀ →ₐ[A₀] C₀)
    (hfinitePresentation : RingHom.FinitePresentation φ₀.toRingHom) :
    letI : Preorder D.base.index := D.base.indexPreorder
    (IsSyntomic (directedAlgebraTensorMapTarget f φ₀).toRingHom →
        ∃ i, D.zero ≤ i ∧
          IsSyntomic
            (directedAlgebraTensorMapStage D.base i φ₀).toRingHom) ∧
      (IsRelativeGlobalCompleteIntersection
          (directedAlgebraTensorMapTarget f φ₀).toRingHom →
        ∃ i, D.zero ≤ i ∧
          IsRelativeGlobalCompleteIntersection
            (directedAlgebraTensorMapStage D.base i φ₀).toRingHom) := by
  sorry

/-! ## The fppf-to-fpqf refinement -/

/-- The ring diagram and map properties in the final source lemma. -/
structure FppfFpqfRefinement
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) where
  S' : Type u
  [commRingS' : CommRing S']
  sToS' : S →+* S'
  rToS' : R →+* S'
  commutes : sToS'.comp f = rToS'
  quasiFinite : RingHom.QuasiFinite rToS'
  faithfullyFlat : RingHom.FaithfullyFlat rToS'
  finitePresentation : RingHom.FinitePresentation rToS'

/-- Every faithfully flat finitely presented map admits a quasi-finite
faithfully flat finitely presented refinement. -/
theorem fppfFpqf
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (hff : RingHom.FaithfullyFlat f)
    (hfp : RingHom.FinitePresentation f) :
    Nonempty (FppfFpqfRefinement f) := by
  sorry

end

end Formalization.Books.Algebra.Unit168
