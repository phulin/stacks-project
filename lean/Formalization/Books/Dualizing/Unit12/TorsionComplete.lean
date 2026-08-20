import Formalization.Books.Dualizing.Unit09.LocalCohomology
import Formalization.Books.MoreAlgebra.Unit92
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.RingTheory.Finiteness.Defs

/-!
# Dualizing Complexes, Chapter 12: Torsion versus complete modules

This file records the Greenlees--May comparison, the induced equivalence of
torsion and derived-complete subcategories, the comparison on derived Hom,
and the Noetherian completion/local-cohomology calculation.  It uses the
canonical torsion, local-cohomology, derived-completion, and derived-limit
interfaces from earlier chapters; the new theorem proofs are deferred.
-/

namespace Formalization.Books.Dualizing.Unit12

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Dualizing.Unit09
open Formalization.Books.MoreAlgebra.Unit67
open Formalization.Books.MoreAlgebra.Unit92
open scoped CategoryTheory.Pretriangulated.Opposite

universe u w

noncomputable section

/-! ## Derived torsion and derived completeness -/

abbrev torsionCategory {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (I : Ideal A) :=
  iPowerTorsionDerivedCategory I

abbrev completeCategory {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (I : Ideal A) :=
  DerivedCompleteDerivedCategory I

/-! The two functors in the source's equivalence are obtained by lifting the
canonical completion through its full subcategory and by restricting the
canonical local-cohomology functor to the complete full subcategory. -/

noncomputable def torsionToCompleteFunctor {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (I : Ideal A) (hI : I.FG) :
    torsionCategory I ⥤ completeCategory I :=
  (derivedCompleteDerivedProperty I).lift
    (iPowerTorsionDerivedInclusion I ⋙ derivedCompletion I hI)
    (fun K => derivedCompletion_is_complete I hI
      ((iPowerTorsionDerivedInclusion I).obj K))

noncomputable def completeToTorsionFunctor {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (I : Ideal A) (hI : I.FG) :
    completeCategory I ⥤ torsionCategory I :=
  (derivedCompleteDerivedProperty I).ι ⋙ localCohomologyFunctor I hI

/-- The unit and counit data expressing that completion and local cohomology
are quasi-inverse on the two full subcategories. -/
structure TorsionCompleteEquivalenceData {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (I : Ideal A) (hI : I.FG) where
  unitIso : 𝟭 (torsionCategory I) ≅
    torsionToCompleteFunctor I hI ⋙ completeToTorsionFunctor I hI
  counitIso : completeToTorsionFunctor I hI ⋙ torsionToCompleteFunctor I hI ≅
    𝟭 (completeCategory I)

/-! ## The comparison identities and equivalence -/

/-- Applying local cohomology after derived completion does not change the
local-cohomology object. -/
theorem localCohomology_completed_iso {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (I : Ideal A) (hI : I.FG)
    (K : Formalization.Books.Dualizing.Unit09.D A) :
    Nonempty
      ((localCohomologyAmbient I hI).obj (completedObject I hI K) ≅
        (localCohomologyAmbient I hI).obj K) := by
  sorry

/-- Derived completion after local cohomology does not change the completed
object. -/
theorem completed_localCohomology_iso {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (I : Ideal A) (hI : I.FG)
    (K : Formalization.Books.Dualizing.Unit09.D A) :
    Nonempty
      (completedObject I hI ((localCohomologyAmbient I hI).obj K) ≅
        completedObject I hI K) := by
  sorry

/-- The derived torsion and derived-complete categories are equivalent, with
the displayed local-cohomology and completion functors as quasi-inverses. -/
theorem torsion_complete_equivalence {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (I : Ideal A) (hI : I.FG) :
    Nonempty (TorsionCompleteEquivalenceData I hI) := by
  sorry

theorem torsionToCompleteFunctor_isEquivalence {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (I : Ideal A) (hI : I.FG) :
    (torsionToCompleteFunctor I hI).IsEquivalence := by
  let e := Classical.choice (torsion_complete_equivalence I hI)
  exact Functor.IsEquivalence.mk' (completeToTorsionFunctor I hI)
    e.unitIso e.counitIso

theorem completeToTorsionFunctor_isEquivalence {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (I : Ideal A) (hI : I.FG) :
    (completeToTorsionFunctor I hI).IsEquivalence := by
  let e := Classical.choice (torsion_complete_equivalence I hI)
  exact Functor.IsEquivalence.mk' (torsionToCompleteFunctor I hI)
    e.counitIso.symm e.unitIso.symm

/-- The derived Hom comparison induced by the torsion/complete equivalence. -/
theorem completed_RHom_iso_localCohomology_RHom {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (I : Ideal A) (hI : I.FG)
    (K L : Formalization.Books.Dualizing.Unit09.D A) :
    Nonempty
      (Formalization.Books.MoreAlgebra.Unit74.RHom
          (completedObject I hI K) (completedObject I hI L) ≅
        Formalization.Books.MoreAlgebra.Unit74.RHom
          ((localCohomologyAmbient I hI).obj K)
          ((localCohomologyAmbient I hI).obj L)) := by
  sorry

/-! ## The Noetherian completion/local-cohomology calculation -/

def idealPowerQuotientModule {A : Type u} [CommRing A]
    (I : Ideal A) (M : ModuleCat.{u} A) (n : ℕ) : ModuleCat.{u} A :=
  ModuleCat.of A
    ((M : Type u) ⧸ ((I ^ (n + 1)) • (⊤ : Submodule A (M : Type u))))

noncomputable abbrev idealPowerQuotientObject {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (I : Ideal A)
    (M : ModuleCat.{u} A) (n : ℕ) :
      Formalization.Books.Dualizing.Unit09.D A :=
  moduleInDerived A (idealPowerQuotientModule I M n)

/-- A derived inverse system presenting the local cohomology of the positive
ideal-power quotients.  The index starts at `n + 1`, as in the standard
positive-power inverse system. -/
structure LocalCohomologyQuotientSystem {A : Type u} [CommRing A]
    [IsNoetherianRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (I J : Ideal A)
    (M : ModuleCat.{u} A) where
  system : Formalization.Books.Derived.Unit34.DerivedInverseSystem
    (Formalization.Books.Dualizing.Unit09.D A)
  stage_iso : ∀ n : ℕ,
    Nonempty (system.obj (Opposite.op n) ≅
      (localCohomologyAmbient J J.fg_of_isNoetherianRing).obj
        (idealPowerQuotientObject I M n))
  hasProduct : HasProduct (fun n : ℕ => system.obj (Opposite.op n))

/-- The derived inverse-limit formula for completed local cohomology. -/
theorem completion_localCohomology_derivedLimit {A : Type u} [CommRing A]
    [IsNoetherianRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (I J : Ideal A)
    (M : ModuleCat.{u} A) [Module.Finite A (M : Type u)] :
    ∃ S : LocalCohomologyQuotientSystem I J M,
      Nonempty
        (completedObject I I.fg_of_isNoetherianRing
            ((localCohomologyAmbient J J.fg_of_isNoetherianRing).obj
              (moduleInDerived A M)) ≅
          derivedLimitWithProduct S.system S.hasProduct) := by
  sorry

/-- A module inverse system presenting the cohomology modules occurring in
the `R¹ lim` short exact sequence. -/
structure LocalCohomologyCohomologySystem {A : Type u} [CommRing A]
    [IsNoetherianRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (I J : Ideal A)
    (M : ModuleCat.{u} A) (i : ℤ) where
  system : (ℕᵒᵖ ⥤ ModuleCat.{u} A)
  stage_iso : ∀ n : ℕ,
    Nonempty (system.obj (Opposite.op n) ≅
      localCohomologyModule J J.fg_of_isNoetherianRing
        (idealPowerQuotientObject I M n) i)
  firstDerivedLimit : ModuleCat.{u} A

/-- The source's short exact sequence
`0 → R¹ lim H^(i-1) → H^i(RΓ_Z(M)^) → lim H^i → 0`.
`firstDerivedLimit` is the chosen module-level realization of `R¹ lim`. -/
structure LocalCohomologyCompletionExactSequence {A : Type u} [CommRing A]
    [IsNoetherianRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (I J : Ideal A)
    (M : ModuleCat.{u} A) (i : ℤ) [Module.Finite A (M : Type u)] where
  cohomologySystem : LocalCohomologyCohomologySystem I J M (i - 1)
  left : cohomologySystem.firstDerivedLimit ⟶
    (Formalization.Books.MoreAlgebra.Unit67.derivedCohomology A i).obj
      (completedObject I I.fg_of_isNoetherianRing
        ((localCohomologyAmbient J J.fg_of_isNoetherianRing).obj
          (moduleInDerived A M)))
  right :
    (Formalization.Books.MoreAlgebra.Unit67.derivedCohomology A i).obj
      (completedObject I I.fg_of_isNoetherianRing
        ((localCohomologyAmbient J J.fg_of_isNoetherianRing).obj
          (moduleInDerived A M))) ⟶
    limit cohomologySystem.system
  zero : left ≫ right = 0
  exact : CategoryTheory.ShortComplex.ShortExact
    { f := left, g := right, zero := zero }

/-- The short exact sequence in each cohomological degree. -/
theorem completion_localCohomology_shortExact {A : Type u} [CommRing A]
    [IsNoetherianRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (I J : Ideal A)
    (M : ModuleCat.{u} A) [Module.Finite A (M : Type u)] (i : ℤ) :
    Nonempty (LocalCohomologyCompletionExactSequence I J M i) := by
  sorry

/-- Completed local cohomology of a finite module has no negative
cohomology. -/
theorem completion_localCohomology_negative_vanishing {A : Type u}
    [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (I J : Ideal A)
    (M : ModuleCat.{u} A) [Module.Finite A (M : Type u)] :
    ∀ i : ℤ, i < 0 →
      IsZero ((Formalization.Books.MoreAlgebra.Unit67.derivedCohomology A i).obj
        (completedObject I I.fg_of_isNoetherianRing
          ((localCohomologyAmbient J J.fg_of_isNoetherianRing).obj
            (moduleInDerived A M)))) := by
  sorry

/-! ## Degree zero over an adically complete ring -/

abbrev H0SupportIndex {A : Type u} [CommRing A]
    (I J : Ideal A) : Type u :=
  {J' : Ideal A // J' ≤ J ∧
    PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)}

/-- A filtered diagram realizing the colimit of the degree-zero local
cohomology modules in the source's H⁰ formula. -/
structure H0SupportColimitData {A : Type u} [CommRing A]
    [IsNoetherianRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (I J : Ideal A) (M : ModuleCat.{u} A) where
  indexFiltered : IsFiltered (H0SupportIndex I J)
  system : H0SupportIndex I J ⥤ ModuleCat.{u} A
  stage_iso : ∀ J' : H0SupportIndex I J,
    Nonempty (system.obj J' ≅
      localCohomologyModule J'.1 J'.1.fg_of_isNoetherianRing
        (moduleInDerived A M) 0)

noncomputable def H0SupportColimit {A : Type u} [CommRing A]
    [IsNoetherianRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    {I J : Ideal A} {M : ModuleCat.{u} A}
    (C : H0SupportColimitData I J M) : ModuleCat.{u} A :=
  letI := C.indexFiltered
  colimit C.system

/-- The degree-zero completed local cohomology is the filtered colimit over
the ideals appearing in the source. -/
theorem completion_localCohomology_H0 {A : Type u} [CommRing A]
    [IsNoetherianRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (I J : Ideal A) [IsAdicComplete I (A : Type u)]
    (M : ModuleCat.{u} A) [Module.Finite A (M : Type u)] :
    ∃ C : H0SupportColimitData I J M,
      Nonempty
        ((Formalization.Books.MoreAlgebra.Unit67.derivedCohomology A 0).obj
            (completedObject I I.fg_of_isNoetherianRing
              ((localCohomologyAmbient J J.fg_of_isNoetherianRing).obj
                (moduleInDerived A M))) ≅
          H0SupportColimit C) := by
  sorry

end

end Formalization.Books.Dualizing.Unit12
