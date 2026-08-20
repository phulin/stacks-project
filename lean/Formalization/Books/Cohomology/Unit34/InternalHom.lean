import Formalization.Books.Cohomology.Unit33.HomComplexes

/-!
# Cohomology of Sheaves, Chapter 34: Internal hom in the derived category

This file records the derived internal-Hom construction and the canonical maps
listed in the source section.  The chain-level construction is inherited from
Chapter 33, and the derived tensor product is the one constructed in Chapter 19.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Opposite
open TopologicalSpace
open Formalization.Books.Cohomology.Unit19
open Formalization.Books.Cohomology.Unit33

universe v

namespace Formalization.Books.Cohomology.Unit34

/-! ## The derived categories and the source-facing notation -/

abbrev RingedSpace :=
  Formalization.Books.Modules.Unit28.CommutativeRingedSpace

abbrev RingedSpaceHom :=
  Formalization.Books.Modules.Unit28.CommutativeRingedSpaceHom

abbrev Complex (X : RingedSpace.{v}) := SheafComplex X

abbrev Derived (X : RingedSpace.{v}) := SheafDerived X

abbrev DerivedQuotient (X : RingedSpace.{v}) : Complex X ⥤ Derived X :=
  sheafDerivedQuotient X

noncomputable abbrev derivedObjectOfComplex
    (X : RingedSpace.{v}) (K : Complex X) : Derived X :=
  (DerivedQuotient X).obj K

noncomputable abbrev derivedTensor
    (X : RingedSpace.{v}) (K L : Derived X) : Derived X :=
  Formalization.Books.Cohomology.Unit19.derivedTensor X.structureSheaf K L

abbrev DerivedHomDomain (X : RingedSpace.{v}) :=
  (Derived X)ᵒᵖ × Derived X

/-! ## The derived internal Hom and its representing property -/

structure DerivedSheafHomData (X : RingedSpace.{v}) where
  functor : DerivedHomDomain X ⥤ Derived X
  computed_by_complex : ∀ L M : Derived X, ∃ K I : Complex X,
    Nonempty ((DerivedQuotient X).obj K ≅ L) ∧
      Nonempty ((DerivedQuotient X).obj I ≅ M) ∧
      I.IsKInjective ∧
      Nonempty (functor.obj (op L, M) ≅
        (DerivedQuotient X).obj (sheafHomComplex X K I))

theorem exists_derivedSheafHomData (X : RingedSpace.{v}) :
    Nonempty (DerivedSheafHomData X) := by
  sorry

noncomputable def derivedSheafHomData (X : RingedSpace.{v}) :
    DerivedSheafHomData X :=
  Classical.choice (exists_derivedSheafHomData X)

noncomputable abbrev derivedSheafHomFunctor (X : RingedSpace.{v}) :
    DerivedHomDomain X ⥤ Derived X :=
  (derivedSheafHomData X).functor

noncomputable abbrev derivedSheafHom
    (X : RingedSpace.{v}) (L M : Derived X) : Derived X :=
  (derivedSheafHomFunctor X).obj (op L, M)

structure DerivedSheafHomRepresentation
    (X : RingedSpace.{v}) (L M : Derived X) where
  source : Complex X
  target : Complex X
  source_iso : Nonempty ((DerivedQuotient X).obj source ≅ L)
  target_iso : Nonempty ((DerivedQuotient X).obj target ≅ M)
  target_isKInjective : target.IsKInjective
  comparison : Nonempty (derivedSheafHom X L M ≅
    (DerivedQuotient X).obj (sheafHomComplex X source target))

theorem exists_derivedSheafHomRepresentation
    (X : RingedSpace.{v}) (L M : Derived X) :
    Nonempty (DerivedSheafHomRepresentation X L M) := by
  sorry

noncomputable def derivedSheafHomRepresentation
    (X : RingedSpace.{v}) (L M : Derived X) :
    DerivedSheafHomRepresentation X L M :=
  Classical.choice (exists_derivedSheafHomRepresentation X L M)

def RepresentsDerivedSheafHom
    (X : RingedSpace.{v}) (L M H : Derived X) : Prop :=
  ∀ K : Derived X,
    Nonempty ((K ⟶ H) ≃ (derivedTensor X K L ⟶ M))

theorem derivedSheafHom_represents
    (X : RingedSpace.{v}) (L M : Derived X) :
    RepresentsDerivedSheafHom X L M (derivedSheafHom X L M) := by
  sorry

theorem exists_internalHomAdjunctionEquiv
    (X : RingedSpace.{v}) (K L M : Derived X) :
    Nonempty ((K ⟶ derivedSheafHom X L M) ≃
      (derivedTensor X K L ⟶ M)) := by
  exact (derivedSheafHom_represents X L M K)

noncomputable def internalHomAdjunctionEquiv
    (X : RingedSpace.{v}) (K L M : Derived X) :
    (K ⟶ derivedSheafHom X L M) ≃ (derivedTensor X K L ⟶ M) :=
  Classical.choice (exists_internalHomAdjunctionEquiv X K L M)

theorem internalHom_unique
    (X : RingedSpace.{v}) (L M H H' : Derived X)
    (hH : RepresentsDerivedSheafHom X L M H)
    (hH' : RepresentsDerivedSheafHom X L M H') :
    Nonempty (H ≅ H') := by
  sorry

/-! ## Restriction to an open and the cohomology calculation -/

structure DerivedRestrictionData
    (X : RingedSpace.{v}) (U : Opens X.carrier) where
  functor : Derived X ⥤ openSheafDerived X U
  computed_on_complex : ∀ K : Complex X,
    Nonempty (functor.obj (derivedObjectOfComplex X K) ≅
      (openSheafDerivedQuotient X U).obj
        ((openRestrictionComplexFunctor X U).obj K))

theorem exists_derivedRestrictionData
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    Nonempty (DerivedRestrictionData X U) := by
  sorry

noncomputable def derivedRestrictionData
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    DerivedRestrictionData X U :=
  Classical.choice (exists_derivedRestrictionData X U)

noncomputable abbrev derivedRestriction
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    Derived X ⥤ openSheafDerived X U :=
  (derivedRestrictionData X U).functor

theorem derivedSheafHom_restriction
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (L M : Derived X) :
    Nonempty ((derivedRestriction X U).obj (derivedSheafHom X L M) ≅
      derivedSheafHom (openSpace X U)
        ((derivedRestriction X U).obj L)
        ((derivedRestriction X U).obj M)) := by
  sorry

noncomputable def derivedSheafHom_restrictionIso
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (L M : Derived X) :
    (derivedRestriction X U).obj (derivedSheafHom X L M) ≅
      derivedSheafHom (openSpace X U)
        ((derivedRestriction X U).obj L)
        ((derivedRestriction X U).obj M) :=
  Classical.choice (derivedSheafHom_restriction X U L M)

noncomputable abbrev sectionsCohomology
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (K : Complex X) (n : ℤ) :=
  ((sheafSectionsComplexFunctor X U).obj K).homology n

theorem sections_derivedSheafHom_equiv
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (L M : Derived X) :
    Nonempty (sectionsCohomology X U
        (sheafHomComplex X
          (derivedSheafHomRepresentation X L M).source
          (derivedSheafHomRepresentation X L M).target) 0 ≃+
      ((openSheafDerivedQuotient X U).obj
          ((openRestrictionComplexFunctor X U).obj
            (derivedSheafHomRepresentation X L M).source) ⟶
        (openSheafDerivedQuotient X U).obj
          ((openRestrictionComplexFunctor X U).obj
            (derivedSheafHomRepresentation X L M).target))) := by
  exact ⟨sheafHomIntoKInjective X U
    (derivedSheafHomRepresentation X L M).source
    (derivedSheafHomRepresentation X L M).target
    (derivedSheafHomRepresentation X L M).target_isKInjective⟩

noncomputable def sections_derivedSheafHomEquiv
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (L M : Derived X) :
    sectionsCohomology X U
        (sheafHomComplex X
          (derivedSheafHomRepresentation X L M).source
          (derivedSheafHomRepresentation X L M).target) 0 ≃+
      ((openSheafDerivedQuotient X U).obj
          ((openRestrictionComplexFunctor X U).obj
            (derivedSheafHomRepresentation X L M).source) ⟶
        (openSheafDerivedQuotient X U).obj
          ((openRestrictionComplexFunctor X U).obj
            (derivedSheafHomRepresentation X L M).target)) :=
  Classical.choice (sections_derivedSheafHom_equiv X U L M)

theorem global_sections_derivedSheafHom_equiv
    (X : RingedSpace.{v}) (L M : Derived X) :
    Nonempty (sectionsCohomology X (⊤ : Opens X.carrier)
        (sheafHomComplex X
          (derivedSheafHomRepresentation X L M).source
          (derivedSheafHomRepresentation X L M).target) 0 ≃+
      ((openSheafDerivedQuotient X (⊤ : Opens X.carrier)).obj
          ((openRestrictionComplexFunctor X (⊤ : Opens X.carrier)).obj
            (derivedSheafHomRepresentation X L M).source) ⟶
        (openSheafDerivedQuotient X (⊤ : Opens X.carrier)).obj
          ((openRestrictionComplexFunctor X (⊤ : Opens X.carrier)).obj
            (derivedSheafHomRepresentation X L M).target))) := by
  exact sections_derivedSheafHom_equiv X (⊤ : Opens X.carrier) L M

noncomputable def global_sections_derivedSheafHomEquiv
    (X : RingedSpace.{v}) (L M : Derived X) :
    sectionsCohomology X (⊤ : Opens X.carrier)
        (sheafHomComplex X
          (derivedSheafHomRepresentation X L M).source
          (derivedSheafHomRepresentation X L M).target) 0 ≃+
      ((openSheafDerivedQuotient X (⊤ : Opens X.carrier)).obj
          ((openRestrictionComplexFunctor X (⊤ : Opens X.carrier)).obj
            (derivedSheafHomRepresentation X L M).source) ⟶
        (openSheafDerivedQuotient X (⊤ : Opens X.carrier)).obj
          ((openRestrictionComplexFunctor X (⊤ : Opens X.carrier)).obj
            (derivedSheafHomRepresentation X L M).target)) :=
  Classical.choice (global_sections_derivedSheafHom_equiv X L M)

theorem global_sections_derivedSheafHom_to_hom_exists
    (X : RingedSpace.{v}) (L M : Derived X) :
    Nonempty (
      sectionsCohomology X (⊤ : Opens X.carrier)
          (sheafHomComplex X
            (derivedSheafHomRepresentation X L M).source
            (derivedSheafHomRepresentation X L M).target) 0 ≃+
        (L ⟶ M)) := by
  sorry

noncomputable def global_sections_derivedSheafHom_to_hom
    (X : RingedSpace.{v}) (L M : Derived X) :
    sectionsCohomology X (⊤ : Opens X.carrier)
        (sheafHomComplex X
          (derivedSheafHomRepresentation X L M).source
          (derivedSheafHomRepresentation X L M).target) 0 ≃+
      (L ⟶ M) :=
  Classical.choice (global_sections_derivedSheafHom_to_hom_exists X L M)

/-! ## Triangulated behavior and the canonical maps -/

structure DerivedSheafHomPrecompositionData
    (X : RingedSpace.{v}) (M : Derived X) where
  functor : (Derived X)ᵒᵖ ⥤ Derived X
  object_formula : ∀ K : (Derived X)ᵒᵖ,
    functor.obj K = (derivedSheafHomFunctor X).obj (K, M)

theorem exists_derivedSheafHomPrecompositionData
    (X : RingedSpace.{v}) (M : Derived X) :
    Nonempty (DerivedSheafHomPrecompositionData X M) := by
  sorry

noncomputable def derivedSheafHomPrecompositionFunctor
    (X : RingedSpace.{v}) (M : Derived X) :
    (Derived X)ᵒᵖ ⥤ Derived X :=
  (Classical.choice (exists_derivedSheafHomPrecompositionData X M)).functor

structure DerivedSheafHomPostcompositionData
    (X : RingedSpace.{v}) (K : Derived X) where
  functor : Derived X ⥤ Derived X
  object_formula : ∀ L : Derived X,
    functor.obj L = (derivedSheafHomFunctor X).obj (op K, L)

theorem exists_derivedSheafHomPostcompositionData
    (X : RingedSpace.{v}) (K : Derived X) :
    Nonempty (DerivedSheafHomPostcompositionData X K) := by
  sorry

noncomputable def derivedSheafHomPostcompositionFunctor
    (X : RingedSpace.{v}) (K : Derived X) :
    Derived X ⥤ Derived X :=
  (Classical.choice (exists_derivedSheafHomPostcompositionData X K)).functor

theorem derivedSheafHom_triangulated_in_first
    (X : RingedSpace.{v}) (M : Derived X) :
    Nonempty (Formalization.Books.Derived.Unit10.ExactTriangulatedFunctorData
      (derivedSheafHomPrecompositionFunctor X M)) := by
  sorry

theorem derivedSheafHom_triangulated_in_second
    (X : RingedSpace.{v}) (K : Derived X) :
    Nonempty (Formalization.Books.Derived.Unit10.ExactTriangulatedFunctorData
      (derivedSheafHomPostcompositionFunctor X K)) := by
  sorry

theorem exists_derivedSheafHomTensorIso
    (X : RingedSpace.{v}) (K L M : Derived X) :
    Nonempty (derivedSheafHom X K
        (derivedSheafHom X L M) ≅
      derivedSheafHom X (derivedTensor X K L) M) := by
  sorry

noncomputable def derivedSheafHomTensorIso
    (X : RingedSpace.{v}) (K L M : Derived X) :
    derivedSheafHom X K (derivedSheafHom X L M) ≅
      derivedSheafHom X (derivedTensor X K L) M :=
  Classical.choice (exists_derivedSheafHomTensorIso X K L M)

theorem exists_derivedSheafHomComposition
    (X : RingedSpace.{v}) (K L M : Derived X) :
    Nonempty (derivedTensor X (derivedSheafHom X L M)
        (derivedSheafHom X K L) ⟶ derivedSheafHom X K M) := by
  sorry

noncomputable def derivedSheafHomComposition
    (X : RingedSpace.{v}) (K L M : Derived X) :
    derivedTensor X (derivedSheafHom X L M)
        (derivedSheafHom X K L) ⟶ derivedSheafHom X K M :=
  Classical.choice (exists_derivedSheafHomComposition X K L M)

theorem exists_derivedSheafHomDiagonalBetter
    (X : RingedSpace.{v}) (K L M : Derived X) :
    Nonempty (derivedTensor X K (derivedSheafHom X M L) ⟶
      derivedSheafHom X M (derivedTensor X K L)) := by
  sorry

noncomputable def derivedSheafHomDiagonalBetter
    (X : RingedSpace.{v}) (K L M : Derived X) :
    derivedTensor X K (derivedSheafHom X M L) ⟶
      derivedSheafHom X M (derivedTensor X K L) :=
  Classical.choice (exists_derivedSheafHomDiagonalBetter X K L M)

theorem exists_derivedSheafHomDiagonal
    (X : RingedSpace.{v}) (K L : Derived X) :
    Nonempty (K ⟶ derivedSheafHom X L (derivedTensor X K L)) := by
  sorry

noncomputable def derivedSheafHomDiagonal
    (X : RingedSpace.{v}) (K L : Derived X) :
    K ⟶ derivedSheafHom X L (derivedTensor X K L) :=
  Classical.choice (exists_derivedSheafHomDiagonal X K L)

/-! ## Duals and evaluation -/

noncomputable abbrev structureSheafModule (X : RingedSpace.{v}) :
    SheafModule X :=
  Formalization.Books.Modules.Unit22.restrictedStructureModule
    (𝟙 X.structureSheaf)

noncomputable abbrev structureSheafObject (X : RingedSpace.{v}) : Derived X :=
  (DerivedCategory.singleFunctor (SheafModule X) 0).obj
    (structureSheafModule X)

noncomputable abbrev derivedSheafHomDual
    (X : RingedSpace.{v}) (L : Derived X) : Derived X :=
  derivedSheafHom X L (structureSheafObject X)

theorem exists_derivedSheafHomDualEvaluation
    (X : RingedSpace.{v}) (L M : Derived X) :
    Nonempty (derivedTensor X M (derivedSheafHomDual X L) ⟶
      derivedSheafHom X L M) := by
  sorry

noncomputable def derivedSheafHomDualEvaluation
    (X : RingedSpace.{v}) (L M : Derived X) :
    derivedTensor X M (derivedSheafHomDual X L) ⟶
      derivedSheafHom X L M :=
  Classical.choice (exists_derivedSheafHomDualEvaluation X L M)

abbrev GlobalModule (X : RingedSpace.{v}) :=
  ModuleCat.{v} (X.structureSheaf.obj.obj (op (⊤ : Opens X.carrier)))

abbrev GlobalDerived (X : RingedSpace.{v}) :=
  DerivedCategory (GlobalModule X)

structure DerivedGlobalSectionsData (X : RingedSpace.{v}) where
  functor : Derived X ⥤ GlobalDerived X

theorem exists_derivedGlobalSectionsData (X : RingedSpace.{v}) :
    Nonempty (DerivedGlobalSectionsData X) := by
  sorry

noncomputable def derivedGlobalSections (X : RingedSpace.{v}) :
    Derived X ⥤ GlobalDerived X :=
  (Classical.choice (exists_derivedGlobalSectionsData X)).functor

noncomputable abbrev globalCohomologyObject
    (X : RingedSpace.{v}) (n : ℤ) : Derived X ⥤ GlobalModule X :=
  derivedGlobalSections X ⋙ DerivedCategory.homologyFunctor (GlobalModule X) n

theorem exists_derivedSheafHomDualEvaluation_on_global_sections
    (X : RingedSpace.{v}) (L M : Derived X) :
    Nonempty ((globalCohomologyObject X 0).obj
        (derivedTensor X M (derivedSheafHomDual X L)) →+
      (L ⟶ M)) := by
  sorry

noncomputable def derivedSheafHomDualEvaluation_on_global_sections
    (X : RingedSpace.{v}) (L M : Derived X) :
    (globalCohomologyObject X 0).obj
        (derivedTensor X M (derivedSheafHomDual X L)) →+
      (L ⟶ M) :=
  Classical.choice (exists_derivedSheafHomDualEvaluation_on_global_sections X L M)

theorem exists_derivedSheafHomEvaluate
    (X : RingedSpace.{v}) (K L M : Derived X) :
    Nonempty (derivedTensor X (derivedSheafHom X L M) K ⟶
      derivedSheafHom X (derivedSheafHom X K L) M) := by
  sorry

noncomputable def derivedSheafHomEvaluate
    (X : RingedSpace.{v}) (K L M : Derived X) :
    derivedTensor X (derivedSheafHom X L M) K ⟶
      derivedSheafHom X (derivedSheafHom X K L) M :=
  Classical.choice (exists_derivedSheafHomEvaluate X K L M)

theorem exists_derivedSheafHomTensorMap
    (X : RingedSpace.{v}) (K K' M M' : Derived X) :
    Nonempty (derivedTensor X (derivedSheafHom X K K')
        (derivedSheafHom X M M') ⟶
      derivedSheafHom X (derivedTensor X K M)
        (derivedTensor X K' M')) := by
  sorry

noncomputable def derivedSheafHomTensorMap
    (X : RingedSpace.{v}) (K K' M M' : Derived X) :
    derivedTensor X (derivedSheafHom X K K')
        (derivedSheafHom X M M') ⟶
      derivedSheafHom X (derivedTensor X K M)
        (derivedTensor X K' M') :=
  Classical.choice (exists_derivedSheafHomTensorMap X K K' M M')

/-! ## Pushforward, projection formula, and base change -/

structure DerivedPullbackPushforwardData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) where
  pullback : Derived Y ⥤ Derived X
  pushforward : Derived X ⥤ Derived Y
  adjunction : pullback ⊣ pushforward

theorem exists_derivedPullbackPushforwardData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    Nonempty (DerivedPullbackPushforwardData f) := by
  sorry

noncomputable def derivedPullback
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    Derived Y ⥤ Derived X :=
  (Classical.choice (exists_derivedPullbackPushforwardData f)).pullback

noncomputable def derivedPushforward
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    Derived X ⥤ Derived Y :=
  (Classical.choice (exists_derivedPullbackPushforwardData f)).pushforward

theorem exists_relativeCupProduct
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K L : Derived X) :
    Nonempty (derivedTensor Y ((derivedPushforward f).obj K)
        ((derivedPushforward f).obj L) ⟶
      (derivedPushforward f).obj (derivedTensor X K L)) := by
  sorry

noncomputable def relativeCupProduct
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K L : Derived X) :
    derivedTensor Y ((derivedPushforward f).obj K)
        ((derivedPushforward f).obj L) ⟶
      (derivedPushforward f).obj (derivedTensor X K L) :=
  Classical.choice (exists_relativeCupProduct f K L)

theorem exists_projectionFormulaInternalHomMap
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K L : Derived X) :
    Nonempty ((derivedPushforward f).obj (derivedSheafHom X L K) ⟶
      derivedSheafHom Y ((derivedPushforward f).obj L)
        ((derivedPushforward f).obj K)) := by
  sorry

noncomputable def projectionFormulaInternalHomMap
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K L : Derived X) :
    (derivedPushforward f).obj (derivedSheafHom X L K) ⟶
      derivedSheafHom Y ((derivedPushforward f).obj L)
        ((derivedPushforward f).obj K) :=
  Classical.choice (exists_projectionFormulaInternalHomMap f K L)

structure RelativeCupCompositionData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K M : Derived X) where
  top : derivedTensor Y
      ((derivedPushforward f).obj (derivedSheafHom X K M))
      ((derivedPushforward f).obj K) ⟶
    (derivedPushforward f).obj
      (derivedTensor X (derivedSheafHom X K M) K)
  left : derivedTensor Y
      ((derivedPushforward f).obj (derivedSheafHom X K M))
      ((derivedPushforward f).obj K) ⟶
    derivedTensor Y
      (derivedSheafHom Y ((derivedPushforward f).obj K)
        ((derivedPushforward f).obj M))
      ((derivedPushforward f).obj K)
  right : (derivedPushforward f).obj
      (derivedTensor X (derivedSheafHom X K M) K) ⟶
    (derivedPushforward f).obj M
  bottom : derivedTensor Y
      (derivedSheafHom Y ((derivedPushforward f).obj K)
        ((derivedPushforward f).obj M))
      ((derivedPushforward f).obj K) ⟶
    (derivedPushforward f).obj M
  commutes : top ≫ right = left ≫ bottom

theorem relativeCupProduct_composition
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K M : Derived X) :
    Nonempty (RelativeCupCompositionData f K M) := by
  sorry

theorem exists_derivedPullbackInternalHomMap
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K L : Derived Y) :
    Nonempty ((derivedPullback f).obj (derivedSheafHom Y K L) ⟶
      derivedSheafHom X ((derivedPullback f).obj K)
        ((derivedPullback f).obj L)) := by
  sorry

noncomputable def derivedPullbackInternalHomMap
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K L : Derived Y) :
    (derivedPullback f).obj (derivedSheafHom Y K L) ⟶
      derivedSheafHom X ((derivedPullback f).obj K)
        ((derivedPullback f).obj L) :=
  Classical.choice (exists_derivedPullbackInternalHomMap f K L)

abbrev CommutativeRingedSpaceSquare
    (X' X S' S : RingedSpace.{v}) :=
  Formalization.Books.Modules.Unit28.RingedSpaceDifferentialSquare X' X S' S

theorem exists_derivedInternalHomBaseChangeMap
    {X' X S' S : RingedSpace.{v}}
    (B : CommutativeRingedSpaceSquare X' X S' S)
    (K L : Derived X) :
    Nonempty ((derivedPullback B.g).obj
        ((derivedPushforward B.h).obj
          (derivedSheafHom X K L)) ⟶
      (derivedPushforward B.f').obj
        (derivedSheafHom X'
          ((derivedPullback B.f).obj K)
          ((derivedPullback B.f).obj L))) := by
  sorry

end Formalization.Books.Cohomology.Unit34
