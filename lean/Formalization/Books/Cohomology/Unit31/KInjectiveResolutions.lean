import Formalization.Books.Cohomology.Unit30
import Formalization.Books.Derived.Unit34.DerivedLimits
import Formalization.Books.Cohomology.Unit03.DerivedFunctors
import Formalization.Books.Homology.Unit13.Complexes

/-!
# Cohomology of Sheaves, Chapter 31: producing K-injective resolutions

This file records the two source results in the chapter.  The bounded-below
injective inverse system, its canonical truncation comparisons, its limit,
and the K-injectivity of that limit are taken from the established derived
category interfaces.  The source's cohomological hypotheses are kept as
explicit predicates so that the two quasi-isomorphism criteria and the
inverse-limit cohomology statement remain usable without reproving them.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open Formalization.Books.Cohomology.Unit20
open Formalization.Books.Cohomology.Unit21
open Formalization.Books.Cohomology.Unit30
open Formalization.Books.Cohomology.Unit03
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit29
open Formalization.Books.Derived.Unit31
open Formalization.Books.Derived.Unit34
open Formalization.Books.Homology.Unit03
open Formalization.Books.Homology.Unit07
open Formalization.Books.Homology.Unit15
open Formalization.Books.Homology.Unit13
open Formalization.Books.MoreAlgebra.Unit87
open Formalization.Books.Sheaves.Unit10

universe v u

namespace Formalization.Books.Cohomology.Unit31

/-! ## The ringed-space module category and the resolution tower -/

abbrev RingedSpace := Formalization.Books.Sheaves.Unit25.RingedSpace

abbrev ModuleCategory (X : RingedSpace.{v}) := Mod X.structureSheaf

abbrev ModuleComplex (X : RingedSpace.{v}) :=
  Formalization.Books.Cohomology.Unit21.ModuleComplex X

abbrev ModuleDerived (X : RingedSpace.{v}) :=
  Formalization.Books.Cohomology.Unit21.ModuleDerived X

/- The source begins by using that `Mod(O_X)` has enough injectives.  The
   Grothendieck-category result from the preceding unbounded-complex chapter
   supplies this instance through Mathlib's standard implication. -/
theorem moduleCategory_hasEnoughInjectives (X : RingedSpace.{v}) :
    EnoughInjectives (ModuleCategory X) := by
  letI : IsGrothendieckAbelian (ModuleCategory X) :=
    Classical.choice
      (Formalization.Books.Cohomology.Unit21.ringedSpaceModule_isGrothendieck X)
  infer_instance

/- `SpecialInverseSystem` is the established package for the diagram
   `τ_{≥ -(n+1)} F → I_n`: it records the canonical truncation comparison,
   quasi-isomorphism, bounded-below injective terms, and split-surjective
   successive maps.  The extra field stores the termwise limit explicitly. -/
structure KInjectiveResolutionData
    (X : RingedSpace.{v}) (F : ModuleComplex X) where
  system : SpecialInverseSystem (isInjective (ModuleCategory X)) F
  hasLimit : HasLimit (specialInverseSystemFunctor system)

theorem exists_kInjectiveResolutionData
    (X : RingedSpace.{v}) (F : ModuleComplex X) :
    Nonempty (KInjectiveResolutionData X F) := by
  letI : EnoughInjectives (ModuleCategory X) :=
    moduleCategory_hasEnoughInjectives X
  obtain ⟨S⟩ := exists_injectiveSpecialInverseSystem (K := F)
  exact ⟨{
    system := S
    hasLimit := specialInverseSystem_hasLimit S
  }⟩

/- The source's termwise inverse limit of the injective tower. -/
noncomputable def resolutionCandidate
    (R : KInjectiveResolutionData X F) : ModuleComplex X := by
  letI := R.hasLimit
  exact specialInverseSystemLimit R.system

/- The canonical map from the original complex to the candidate limit. -/
noncomputable def resolutionMap
    (R : KInjectiveResolutionData X F) : F ⟶ resolutionCandidate R := by
  letI := R.hasLimit
  exact Classical.choose (specialInverseSystem_limit_map_exists R.system)

theorem resolutionMap_compatibility
    (R : KInjectiveResolutionData X F) (n : ℕ) :
    resolutionMap R ≫
        limit.π (specialInverseSystemFunctor R.system) (Opposite.op n) =
      Formalization.Books.Homology.Unit15.CochainComplex.canonicalTruncGEπ
        F (-((n : ℤ) + 1)) ≫
        R.system.comparison n := by
  letI := R.hasLimit
  simpa [resolutionMap, resolutionCandidate] using
    (Classical.choose_spec
      (specialInverseSystem_limit_map_exists R.system) n)

theorem resolutionCandidate_isKInjective
    (R : KInjectiveResolutionData X F) :
    (resolutionCandidate R).IsKInjective := by
  letI := R.hasLimit
  exact specialInverseSystem_limit_isKInjective R.system

/-! ## Cohomology sheaves and the two convergence criteria -/

abbrev cohomologySheafOfComplex
    (X : RingedSpace.{v}) (F : ModuleComplex X) (q : ℤ) :
    ModuleCategory X :=
  (DerivedCategory.homologyFunctor (ModuleCategory X) q).obj
    (derivedObjectOfComplex X F)

abbrev openCohomologyGroup
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : ModuleCategory X) (p : ℤ) : AddCommGrpCat.{v} :=
  Formalization.Books.Cohomology.Unit30.openSheafCohomologyGroup X U F p

/- This is the source's uniform dimension bound
 `H^p(U, H^q(F)) = 0` for `p > d` and `q < 0`. -/
def UniformNegativeCohomologyVanishing
    (X : RingedSpace.{v}) (F : ModuleComplex X)
    (B : Set (Opens X.carrier)) (d : ℕ) : Prop :=
  ∀ U, U ∈ B → ∀ p q : ℤ, (d : ℤ) < p → q < 0 →
    IsZero (openCohomologyGroup X U
      (cohomologySheafOfComplex X F q) p)

theorem resolutionMap_quasiIso_of_uniform_vanishing
    (R : KInjectiveResolutionData X F)
    (B : Set (Opens X.carrier)) (d : ℕ)
    (hcover : OpenCoveringBy X B)
    (hvanish : UniformNegativeCohomologyVanishing X F B d) :
    QuasiIso (resolutionMap R) := by
  sorry

/- The footnote's stronger-looking but more flexible diagonal condition is
   made explicit.  The omitted quantifiers in the prose are interpreted in
   the only source-faithful way: the bound is uniform over the chosen opens
   and all larger cohomological degrees. -/
def EventualDiagonalCohomologyVanishing
    (X : RingedSpace.{v}) (F : ModuleComplex X)
    (B : Set (Opens X.carrier)) : Prop :=
  ∀ m : ℤ, ∃ p₀ : ℤ, ∀ U, U ∈ B → ∀ p : ℤ, p₀ < p →
    IsZero (openCohomologyGroup X U
      (cohomologySheafOfComplex X F (m - p)) p)

theorem resolutionMap_quasiIso_of_eventual_diagonal_vanishing
    (R : KInjectiveResolutionData X F)
    (B : Set (Opens X.carrier))
    (hcover : OpenCoveringBy X B)
    (hvanish : EventualDiagonalCohomologyVanishing X F B) :
    QuasiIso (resolutionMap R) := by
  sorry

/- The source warns that the displayed canonical map need not be a
   quasi-isomorphism without a cohomological vanishing condition; no
   unconditional quasi-isomorphism declaration is made here. -/

/-! ## Inverse limits of complexes and cohomology sheaves -/

abbrev ComplexInverseSystem (X : RingedSpace.{v}) :=
  DerivedInverseSystem (ModuleComplex X)

noncomputable def sectionsComplexFunctor
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    ModuleComplex X ⥤ CochainComplex
      (ModuleCat.{v} (X.structureSheaf.obj.obj (op U))) ℤ := by
  letI : (ringedSpaceModuleSectionsFunctor X U).Additive :=
    left_or_right_exact_additive
      (ringedSpaceModuleSectionsFunctor X U)
      (Or.inl (ringedSpaceModuleSectionsFunctor_isLeftExact X U))
  exact (ringedSpaceModuleSectionsFunctor X U).mapHomologicalComplex
    (ComplexShape.up ℤ)

noncomputable def termSectionsSystem
    (X : RingedSpace.{v}) (F : ComplexInverseSystem X)
    (U : Opens X.carrier) (q : ℤ) :
    ℕᵒᵖ ⥤ AddCommGrpCat.{v} :=
  F ⋙ sectionsComplexFunctor X U ⋙
    HomologicalComplex.eval
      (ModuleCat.{v} (X.structureSheaf.obj.obj (op U)))
      (ComplexShape.up ℤ) q ⋙
    forget₂ (ModuleCat.{v} (X.structureSheaf.obj.obj (op U))) AddCommGrpCat

noncomputable def sectionsCohomologySystem
    (X : RingedSpace.{v}) (F : ComplexInverseSystem X)
    (U : Opens X.carrier) (q : ℤ) :
    ℕᵒᵖ ⥤ AddCommGrpCat.{v} :=
  F ⋙ sectionsComplexFunctor X U ⋙
    cochainCohomologyFunctor
      (ModuleCat.{v} (X.structureSheaf.obj.obj (op U))) q ⋙
    forget₂ (ModuleCat.{v} (X.structureSheaf.obj.obj (op U))) AddCommGrpCat

noncomputable def cohomologySheafSystem
    (X : RingedSpace.{v}) (F : ComplexInverseSystem X) (m : ℤ) :
    ℕᵒᵖ ⥤ ModuleCategory X :=
  F ⋙ (DerivedCategory.Q : ModuleComplex X ⥤ ModuleDerived X) ⋙
    DerivedCategory.homologyFunctor (ModuleCategory X) m

abbrev FirstDerivedLimitVanishing
    (A : ℕᵒᵖ ⥤ AddCommGrpCat.{v})
    [HasInjectiveResolutions (ℕᵒᵖ ⥤ AddCommGrpCat.{v})] : Prop :=
  Formalization.Books.MoreAlgebra.Unit87.FirstDerivedLimitVanishing A

theorem mittagLeffler_implies_firstDerivedLimitVanishing
    (A : ℕᵒᵖ ⥤ AddCommGrpCat.{v})
    [HasInjectiveResolutions (ℕᵒᵖ ⥤ AddCommGrpCat.{v})]
    (hA : IsMittagLefflerSystem A) :
    FirstDerivedLimitVanishing A := by
  exact (Rlim_MittagLeffler_is_rightAcyclic A hA) 1 (by simp)

/- The three local hypotheses in Lemma `inverse-limit-complexes`: two
   degreewise R¹lim conditions, one cohomology R¹lim condition, and eventual
   stabilization of the m-th cohomology groups. -/
structure InverseLimitCohomologyHypotheses
    (X : RingedSpace.{v}) (F : ComplexInverseSystem X)
    (B : Set (Opens X.carrier)) (m : ℤ) (n₀ : ℕ)
    [HasInjectiveResolutions (ℕᵒᵖ ⥤ AddCommGrpCat.{v})] where
  covering : OpenCoveringBy X B
  term_m2 : ∀ U, U ∈ B →
    FirstDerivedLimitVanishing (termSectionsSystem X F U (m - 2))
  term_m1 : ∀ U, U ∈ B →
    FirstDerivedLimitVanishing (termSectionsSystem X F U (m - 1))
  cohomology_m1 : ∀ U, U ∈ B →
    FirstDerivedLimitVanishing (sectionsCohomologySystem X F U (m - 1))
  stabilized : ∀ U, U ∈ B → ∀ n : ℕ, n₀ ≤ n →
    (sectionsCohomologySystem X F U m).obj (Opposite.op n) =
      (sectionsCohomologySystem X F U m).obj (Opposite.op n₀)

/- The canonical map from the cohomology of the termwise limit to the limit
   of the cohomology sheaves is characterized by its limit projections. -/
noncomputable def cohomologyMapOfLimitProjection
    (X : RingedSpace.{v}) (F : ComplexInverseSystem X) (m : ℤ)
    [HasLimit F] (n : ℕ) :
    cohomologySheafOfComplex X (limit F) m ⟶
      (cohomologySheafSystem X F m).obj (Opposite.op n) :=
  (DerivedCategory.homologyFunctor (ModuleCategory X) m).map
    ((DerivedCategory.Q : ModuleComplex X ⥤ ModuleDerived X).map
      (limit.π F (Opposite.op n)))

structure InverseLimitCohomologyComparison
    (X : RingedSpace.{v}) (F : ComplexInverseSystem X)
    (m : ℤ) (n₀ : ℕ)
    [HasLimit F]
    [HasLimit (cohomologySheafSystem X F m)] where
  firstMap : cohomologySheafOfComplex X (limit F) m ⟶
    limit (cohomologySheafSystem X F m)
  firstMap_fac : ∀ n : ℕ,
    firstMap ≫ limit.π (cohomologySheafSystem X F m) (Opposite.op n) =
      cohomologyMapOfLimitProjection X F m n
  firstMap_isIso : IsIso firstMap
  stabilization_isIso : IsIso
    (limit.π (cohomologySheafSystem X F m) (Opposite.op n₀))

theorem inverseLimit_cohomology_comparison
    (X : RingedSpace.{v}) (F : ComplexInverseSystem X)
    (B : Set (Opens X.carrier)) (m : ℤ) (n₀ : ℕ)
    [HasInjectiveResolutions (ℕᵒᵖ ⥤ AddCommGrpCat.{v})]
    [HasLimit F]
    [HasLimit (cohomologySheafSystem X F m)]
    (h : InverseLimitCohomologyHypotheses X F B m n₀) :
    Nonempty (InverseLimitCohomologyComparison X F m n₀) := by
  sorry

end Formalization.Books.Cohomology.Unit31
