import Formalization.Books.Cohomology.Unit34.InternalHom
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# Cohomology of Sheaves, Chapter 38: Strictly perfect complexes

This file records the definitions, warnings, and theorem interfaces in the
source section `Strictly perfect complexes`.  Complexes use the
commutative-ringed-space model already fixed by Chapters 33--34; categorical
retracts and finite free sheaves are the established module APIs transported
to that model.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open Opposite
open Set
open TopologicalSpace
open HomologicalComplex
open ComplexShape
open Formalization.Books.Cohomology.Unit19
open Formalization.Books.Cohomology.Unit33
open Formalization.Books.Cohomology.Unit34
open Formalization.Books.Modules.Unit03
open Formalization.Books.Modules.Unit22
open Formalization.Books.Sheaves.Unit17
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22

universe v

namespace Formalization.Books.Cohomology.Unit38

/-! ## The source categories and the finite-free summand predicate -/

abbrev RingedSpace := Formalization.Books.Cohomology.Unit34.RingedSpace

abbrev RingedSpaceHom := Formalization.Books.Cohomology.Unit34.RingedSpaceHom

abbrev SheafModule (X : RingedSpace.{v}) :=
  Formalization.Books.Cohomology.Unit33.SheafModule X

abbrev Complex (X : RingedSpace.{v}) :=
  Formalization.Books.Cohomology.Unit33.SheafComplex X

abbrev Derived (X : RingedSpace.{v}) :=
  Formalization.Books.Cohomology.Unit34.Derived X

abbrev DerivedQuotient (X : RingedSpace.{v}) :
    Complex X ⥤ Derived X :=
  Formalization.Books.Cohomology.Unit34.DerivedQuotient X

noncomputable abbrev derivedObjectOfComplex
    (X : RingedSpace.{v}) (K : Complex X) : Derived X :=
  Formalization.Books.Cohomology.Unit34.derivedObjectOfComplex X K

noncomputable def finiteFreeSheaf
    (X : RingedSpace.{v}) (n : ℕ) : SheafModule X :=
  sheafModuleCoproduct (commRingSheafToRingSheaf X.structureSheaf)
    (fun _ : ULift.{v} (Fin n) =>
      SheafOfModules.unit (commRingSheafToRingSheaf X.structureSheaf))

abbrev IsDirectSummand {X : RingedSpace.{v}}
    (F G : SheafModule X) : Prop :=
  Nonempty (Retract F G)

def IsDirectSummandOfFiniteFree {X : RingedSpace.{v}}
    (F : SheafModule X) : Prop :=
  ∃ n : ℕ, IsDirectSummand F (finiteFreeSheaf X n)

def IsomorphicToDirectSummandOfFiniteFree {X : RingedSpace.{v}}
    (F : SheafModule X) : Prop :=
  ∃ G : SheafModule X, ∃ n : ℕ,
    Nonempty (F ≅ G) ∧ IsDirectSummand G (finiteFreeSheaf X n)

def IsStrictlyPerfect {X : RingedSpace.{v}} (E : Complex X) : Prop :=
  Set.Finite {i : ℤ | ¬ IsZero (E.X i)} ∧
    ∀ i : ℤ, IsDirectSummandOfFiniteFree (E.X i)

/-! The source warning is retained as a proposition rather than silently
asserting local freeness: without a locally ringed-space hypothesis, this
implication need not hold. -/

def IsFiniteLocallyFreeSheaf {X : RingedSpace.{v}}
    (F : SheafModule X) : Prop :=
  ∃ q : SheafOfModules.LocalGeneratorsData.{v} F,
    q.IsLocallyFreeData ∧ ∀ i, Finite (q.generators i).I

def DirectSummandFiniteFreeMayFailToBeFiniteLocallyFree : Prop :=
  ¬ (∀ (X : RingedSpace.{v}) (F : SheafModule X),
      IsDirectSummandOfFiniteFree F →
        IsFiniteLocallyFreeSheaf F)

/-! ## Locality and cohomology predicates -/

def HoldsLocally (X : RingedSpace.{v})
    (P : Opens X.carrier → Prop) : Prop :=
  ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧ P U

noncomputable abbrev cohomologyFunctor
    (X : RingedSpace.{v}) (n : ℤ) : Complex X ⥤ SheafModule X :=
  HomologicalComplex.homologyFunctor (SheafModule X) (.up ℤ) n

abbrev IsCohomologicallyAcyclic {X : RingedSpace.{v}}
    (K : Complex X) : Prop :=
  Formalization.Books.Cohomology.Unit19.IsAcyclic K

def IsCohomologyZeroFrom {X : RingedSpace.{v}}
    (K : Complex X) (a : ℤ) : Prop :=
  ∀ n : ℤ, a ≤ n → IsZero ((cohomologyFunctor X n).obj K)

def IsZeroBelow {X : RingedSpace.{v}}
    (K : Complex X) (a : ℤ) : Prop :=
  ∀ n : ℤ, n < a → IsZero (K.X n)

def IsZeroAbove {X : RingedSpace.{v}}
    (K : Complex X) (b : ℤ) : Prop :=
  ∀ n : ℤ, b < n → IsZero (K.X n)

noncomputable def restrictionModule
    (X : RingedSpace.{v}) (U : Opens X.carrier) (F : SheafModule X) :
    SheafModule (openSpace X U) :=
  ((openRestrictionComplexFunctor X U).obj
    ((CochainComplex.singleFunctor (SheafModule X) 0).obj F)).X 0

noncomputable def restrictionModuleMap
    {X : RingedSpace.{v}} (U : Opens X.carrier)
    {F G : SheafModule X} (f : F ⟶ G) :
    restrictionModule X U F ⟶ restrictionModule X U G :=
  ((openRestrictionComplexFunctor X U).map
    ((CochainComplex.singleFunctor (SheafModule X) 0).map f)).f 0

def CohomologyMapIsIsoAboveAndEpiAt {X : RingedSpace.{v}}
    {K L : Complex X} (f : K ⟶ L) (a : ℤ) : Prop :=
  (∀ n : ℤ, a < n → IsIso ((cohomologyFunctor X n).map f)) ∧
    Epi ((cohomologyFunctor X a).map f)

/-! ## The cone, tensor, pullback, and finite-support statements -/

theorem cone_strictlyPerfect
    {X : RingedSpace.{v}} {K L : Complex X} (f : K ⟶ L)
    (hK : IsStrictlyPerfect K) (hL : IsStrictlyPerfect L) :
    IsStrictlyPerfect (CochainComplex.mappingCone f) := by
  sorry

theorem tensor_strictlyPerfect
    (X : RingedSpace.{v}) (K L : Complex X)
    (hK : IsStrictlyPerfect K) (hL : IsStrictlyPerfect L) :
    IsStrictlyPerfect
      (Formalization.Books.Cohomology.Unit19.sheafTensorComplex
        (O := X.structureSheaf) K L) := by
  sorry

structure PullbackData {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) where
  pullback : SheafModule Y ⥤ SheafModule X
  pullback_additive : pullback.Additive

theorem exists_pullbackData {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) : Nonempty (PullbackData f) := by
  sorry

noncomputable def pullbackData {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) : PullbackData f :=
  Classical.choice (exists_pullbackData f)

noncomputable def pullbackComplexFunctor
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    Complex Y ⥤ Complex X := by
  let P := pullbackData f
  letI : P.pullback.Additive := P.pullback_additive
  exact P.pullback.mapHomologicalComplex (ComplexShape.up ℤ)

theorem pullback_strictlyPerfect
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K : Complex Y) (hK : IsStrictlyPerfect K) :
    IsStrictlyPerfect ((pullbackComplexFunctor f).obj K) := by
  sorry

/-! The local lifting lemma uses the commutative-model restriction functor on
single-term complexes, which is the module-level construction already used by
the preceding hom-complex chapter. -/

def LocallyLiftsModuleMap {X : RingedSpace.{v}}
    {E F G : SheafModule X} (α : E ⟶ F) (p : G ⟶ F) : Prop :=
  HoldsLocally X (fun U =>
    ∃ β : restrictionModule X U E ⟶ restrictionModule X U G,
      β ≫ restrictionModuleMap U p = restrictionModuleMap U α)

theorem local_lift_map
    {X : RingedSpace.{v}} {E F G : SheafModule X}
    (α : E ⟶ F) (p : G ⟶ F)
    (hE : IsDirectSummandOfFiniteFree E) [Epi p] :
    LocallyLiftsModuleMap α p := by
  sorry

def LocallyHomotopicToZero {X : RingedSpace.{v}}
    {K L : Complex X} (α : K ⟶ L) : Prop :=
  HoldsLocally X (fun U =>
    Nonempty (Homotopy
      ((openRestrictionComplexFunctor X U).map α)
      (0 : (openRestrictionComplexFunctor X U).obj K ⟶
        (openRestrictionComplexFunctor X U).obj L)))

theorem local_homotopy_of_acyclic
    {X : RingedSpace.{v}} {K L : Complex X} (α : K ⟶ L)
    (hK : IsStrictlyPerfect K) (hL : IsCohomologicallyAcyclic L) :
    LocallyHomotopicToZero α := by
  sorry

theorem local_homotopy_of_vanishing
    {X : RingedSpace.{v}} {K L : Complex X} (α : K ⟶ L)
    (a : ℤ) (hK : IsStrictlyPerfect K) (hKzero : IsZeroBelow K a)
    (hL : IsCohomologyZeroFrom L a) :
    LocallyHomotopicToZero α := by
  sorry

def LocallyLiftsComplexMap {X : RingedSpace.{v}}
    {K L M : Complex X} (α : K ⟶ L) (f : M ⟶ L) : Prop :=
  HoldsLocally X (fun U =>
    ∃ β : (openRestrictionComplexFunctor X U).obj K ⟶
        (openRestrictionComplexFunctor X U).obj M,
      Nonempty (Homotopy
        ((openRestrictionComplexFunctor X U).map α)
        (β ≫ (openRestrictionComplexFunctor X U).map f)))

theorem lift_through_quasi_isomorphism
    {X : RingedSpace.{v}} {K L M : Complex X}
    (α : K ⟶ L) (f : M ⟶ L) (a : ℤ)
    (hK : IsStrictlyPerfect K) (hKzero : IsZeroBelow K a)
    (hf : CohomologyMapIsIsoAboveAndEpiAt f a) :
    LocallyLiftsComplexMap α f := by
  sorry

/-! ## Actual representatives in the derived category -/

noncomputable def derivedRestrictionComplexIso
    {X : RingedSpace.{v}} (U : Opens X.carrier) (K : Complex X) :
    (derivedRestriction X U).obj (derivedObjectOfComplex X K) ≅
      (openSheafDerivedQuotient X U).obj
        ((openRestrictionComplexFunctor X U).obj K) :=
  Classical.choice ((derivedRestrictionData X U).computed_on_complex K)

def LocallyActualDerivedMap
    {X : RingedSpace.{v}} {K L : Complex X}
    (α : (DerivedQuotient X).obj K ⟶ (DerivedQuotient X).obj L) : Prop :=
  HoldsLocally X (fun U =>
    ∃ β : (openRestrictionComplexFunctor X U).obj K ⟶
        (openRestrictionComplexFunctor X U).obj L,
      (derivedRestrictionComplexIso U K).hom ≫
          (openSheafDerivedQuotient X U).map
            β =
        (derivedRestriction X U).map α ≫
          (derivedRestrictionComplexIso U L).hom)

theorem local_actual_representative
    {X : RingedSpace.{v}} {K L : Complex X}
    (hK : IsStrictlyPerfect K)
    (α : (DerivedQuotient X).obj K ⟶ (DerivedQuotient X).obj L) :
    LocallyActualDerivedMap α := by
  sorry

theorem local_actual_zero
    {X : RingedSpace.{v}} {K L : Complex X} (hK : IsStrictlyPerfect K)
    (α : K ⟶ L) (hα : (DerivedQuotient X).map α = 0) :
    LocallyHomotopicToZero α := by
  sorry

/-! ## The internal-Hom formulas -/

abbrev HomSupport {X : RingedSpace.{v}}
    (K L : Complex X) (n : ℤ) :=
  {q : ℤ // ¬ IsZero (K.X (-q)) ∧ ¬ IsZero (L.X (n - q))}

noncomputable def directSumHomTerm
    {X : RingedSpace.{v}} (K L : Complex X) (n : ℤ) : SheafModule X :=
  sheafModuleCoproduct (commRingSheafToRingSheaf X.structureSheaf)
    (fun q : ULift.{v} (HomSupport K L n) =>
      internalHom X.structureSheaf
        (K.X (-(q.down : ℤ))) (L.X (n - q.down)))

def HasDirectSumHomFormula
    {X : RingedSpace.{v}} (K L H : Complex X) : Prop :=
  ∀ n : ℤ, Nonempty (H.X n ≅ directSumHomTerm K L n)

def RepresentsDerivedSheafHom
    {X : RingedSpace.{v}} (K L H : Complex X) : Prop :=
  Nonempty (derivedObjectOfComplex X H ≅
    derivedSheafHom X (derivedObjectOfComplex X K)
      (derivedObjectOfComplex X L))

theorem rhom_strictlyPerfect
    {X : RingedSpace.{v}} (K L : Complex X)
    (hK : IsStrictlyPerfect K) :
    RepresentsDerivedSheafHom K L (sheafHomComplex X K L) ∧
      HasDirectSumHomFormula K L (sheafHomComplex X K L) := by
  sorry

theorem rhom_strictlyPerfect_KFlat
    {X : RingedSpace.{v}} (K L : Complex X)
    (hK : IsStrictlyPerfect K) (hL : IsKFlat L) :
    IsKFlat (sheafHomComplex X K L) := by
  sorry

theorem rhom_directSummands_finiteFree
    {X : RingedSpace.{v}} (K L : Complex X)
    (hL : ∃ a : ℤ, IsZeroBelow L a)
    (hK : ∃ b : ℤ, IsZeroAbove K b)
    (hKterms : ∀ n : ℤ,
      IsomorphicToDirectSummandOfFiniteFree (K.X n)) :
    RepresentsDerivedSheafHom K L (sheafHomComplex X K L) ∧
      HasDirectSumHomFormula K L (sheafHomComplex X K L) := by
  sorry

end Formalization.Books.Cohomology.Unit38
