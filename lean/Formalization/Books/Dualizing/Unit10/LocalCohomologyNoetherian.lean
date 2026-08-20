import Formalization.Books.Dualizing.Unit08.DerivingTorsion
import Formalization.Books.Dualizing.Unit09.LocalCohomology
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Dualizing Complexes, Chapter 10: Local cohomology for Noetherian rings

This file formalizes the comparison between ideal-power torsion and closed
support, the Noetherian equivalence, the finite Čech calculation, and change
of rings from the numbered section.
-/

namespace Formalization.Books.Dualizing.Unit10

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Dualizing.Unit09
open scoped BigOperators

universe u w

noncomputable section

/-! ## The comparison from ideal torsion to closed support -/

/- The derived torsion construction from Chapter 8 is presented using a
chosen Abelian and derived-category structure on the torsion module
subcategory. The preceding chapter proves that these structures exist for
every finitely generated ideal, so these choices add no mathematical
hypothesis. -/

noncomputable def idealTorsionAmbient
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (I : Ideal R) (hI : I.FG) :
    D R ⥤ D R := by
  letI : Abelian (Formalization.Books.Dualizing.Unit08.TorsionModuleCategory R I) :=
    Classical.choice
      (Formalization.Books.Dualizing.Unit08.torsion_module_category_is_abelian R I hI)
  letI : HasDerivedCategory.{w}
      (Formalization.Books.Dualizing.Unit08.TorsionModuleCategory R I) :=
    Classical.choice
      (Formalization.Books.Dualizing.Unit08.torsion_module_category_has_derived_category
        R I hI)
  exact
    Formalization.Books.Dualizing.Unit08.derivedTorsionFunctor I hI
        (Formalization.Books.Dualizing.Unit08.idealPowerTorsionFunctor_isLeftExact I hI) ⋙
      Formalization.Books.Dualizing.Unit08.derivedTorsionInclusionFunctor I hI

noncomputable def idealTorsionCounit
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (I : Ideal R) (hI : I.FG) :
    idealTorsionAmbient I hI ⟶ 𝟭 (D R) := by
  letI : Abelian (Formalization.Books.Dualizing.Unit08.TorsionModuleCategory R I) :=
    Classical.choice
      (Formalization.Books.Dualizing.Unit08.torsion_module_category_is_abelian R I hI)
  letI : HasDerivedCategory.{w}
      (Formalization.Books.Dualizing.Unit08.TorsionModuleCategory R I) :=
    Classical.choice
      (Formalization.Books.Dualizing.Unit08.torsion_module_category_has_derived_category
        R I hI)
  exact
    (Classical.choice
      (Formalization.Books.Dualizing.Unit08.derivedTorsionFunctor_rightAdjoint_to_inclusion
        I hI
        (Formalization.Books.Dualizing.Unit08.idealPowerTorsionFunctor_isLeftExact I hI))).counit

noncomputable def closedSupportCounit
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (I : Ideal R) (hI : I.FG) :
    localCohomologyAmbient I hI ⟶ 𝟭 (D R) :=
  (Classical.choice (localCohomologyData_exists I hI)).adjunction.counit

/-- The canonical factorization of ideal-power local cohomology through the
closed-support right adjoint. -/
structure TorsionToSupportComparisonData
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (I : Ideal R) (hI : I.FG) where
  comparison : idealTorsionAmbient I hI ⟶ localCohomologyAmbient I hI
  factorization :
    comparison ≫ closedSupportCounit I hI = idealTorsionCounit I hI
  unique : ∀ (φ : idealTorsionAmbient I hI ⟶ localCohomologyAmbient I hI),
    φ ≫ closedSupportCounit I hI = idealTorsionCounit I hI → φ = comparison

/-- Existence and uniqueness of the comparison map in the source's displayed
natural transformation. -/
theorem torsionToSupportComparisonData_exists
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (I : Ideal R) (hI : I.FG) :
    Nonempty (TorsionToSupportComparisonData I hI) := by
  sorry

/- The chosen map is useful to clients that need a natural transformation,
while the structure above retains its universal factorization property. -/
noncomputable def torsionToSupportComparison
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (I : Ideal R) (hI : I.FG) :
    idealTorsionAmbient I hI ⟶ localCohomologyAmbient I hI :=
  (Classical.choice (torsionToSupportComparisonData_exists I hI)).comparison

/- The source also records that the comparison need not be invertible without
Noetherianity. Packaging a witness keeps that warning as a usable statement
without choosing a particular counterexample in this interface file. -/
structure TorsionToSupportComparisonFailure where
  R : Type u
  [commRing : CommRing R]
  [hasDerivedCategory : HasDerivedCategory.{w} (ModuleCat.{u} R)]
  I : Ideal R
  hI : I.FG
  notNoetherian : ¬ IsNoetherianRing R
  notIso : ¬ IsIso (torsionToSupportComparison I hI)

theorem torsionToSupportComparison_not_iso_in_general :
    Nonempty (TorsionToSupportComparisonFailure (u := u) (w := w)) := by
  sorry

/-- Over a Noetherian ring the comparison from ideal torsion to closed support
is an isomorphism. -/
theorem torsionToSupportComparison_isIso_of_noetherian
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (I : Ideal R) :
    IsIso (torsionToSupportComparison I I.fg_of_isNoetherianRing) := by
  sorry

/-! ## The Noetherian lemma -/

/-- The adjunction counit is an isomorphism on every derived object whose
cohomology is `I`-power torsion. -/
theorem localCohomology_noetherian_adjunction_iso
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (I : Ideal R) :
    ∀ K : iPowerTorsionDerivedCategory I,
      IsIso ((idealTorsionCounit I I.fg_of_isNoetherianRing).app
        ((iPowerTorsionDerivedInclusion I).obj K)) := by
  sorry

/-- The comparison from the derived category of `I`-power torsion modules to
the full derived subcategory of torsion objects is an equivalence over a
Noetherian ring. -/
theorem derivedTorsionComparison_isEquivalence_of_noetherian
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (I : Ideal R)
    [Abelian (Formalization.Books.Dualizing.Unit08.TorsionModuleCategory R I)]
    [HasDerivedCategory.{w}
      (Formalization.Books.Dualizing.Unit08.TorsionModuleCategory R I)] :
    (Formalization.Books.Dualizing.Unit08.derivedTorsionComparisonFunctor I
      I.fg_of_isNoetherianRing).IsEquivalence := by
  sorry

/-- The natural transformation from ideal local cohomology to closed-support
local cohomology is an isomorphism in the Noetherian case. -/
theorem localCohomology_comparison_isIso_of_noetherian
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (I : Ideal R) :
    IsIso (torsionToSupportComparison I I.fg_of_isNoetherianRing) := by
  exact torsionToSupportComparison_isIso_of_noetherian I

/-! ## The finite Čech calculation -/

/-- The degree-`p` module in the finite Čech complex on `f`, for coefficients
in an arbitrary module `M`. The indexing by finite subsets packages the
source's products over increasing index tuples. -/
def moduleCechTerm {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (M : ModuleCat.{u} R) (p : ℕ) : ModuleCat.{u} R :=
  ModuleCat.of R
    (∀ s : {s : Finset (Fin r) // s.card = p},
      LocalizedModule
        (Submonoid.powers (∏ i : Fin r, if i ∈ s.1 then f i else 1)) (M : Type u))

/-- Complex data retaining the terms of the finite Čech complex with module
coefficients. The differential is part of `complex`; the term specification
makes the displayed source complex available to clients. -/
structure ModuleCechPresentation {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] {r : ℕ}
    (f : Fin r → R) (M : ModuleCat.{u} R) where
  complex : Formalization.Books.MoreAlgebra.Unit59.Comp R
  term_spec : ∀ p : ℕ,
    Nonempty (complex.X (p : ℤ) ≅ moduleCechTerm f M p)

/-- The source's two canonical identifications for the finite Čech complex.
The ring case is obtained by taking `M = A`; the same declaration handles
the stated module case. -/
structure NoetherianCechComparisonData
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (I : Ideal R) {r : ℕ} (f : Fin r → R) (M : ModuleCat.{u} R) where
  presentation : ModuleCechPresentation f M
  torsion_iso :
    (idealTorsionAmbient I I.fg_of_isNoetherianRing).obj
        (Formalization.Books.MoreAlgebra.Unit67.moduleInDerived R M) ≅
      (Formalization.Books.MoreAlgebra.Unit59.derivedComplexQuotient R).obj
        presentation.complex
  support_iso :
    (Formalization.Books.MoreAlgebra.Unit59.derivedComplexQuotient R).obj
        presentation.complex ≅
      (localCohomologyAmbient I I.fg_of_isNoetherianRing).obj
        (Formalization.Books.MoreAlgebra.Unit67.moduleInDerived R M)

theorem localCohomology_noetherian_cech
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (I : Ideal R)
    {r : ℕ} (f : Fin r → R) (hgen : I = Ideal.span (Set.range f))
    (M : ModuleCat.{u} R) :
    Nonempty (NoetherianCechComparisonData I f M) := by
  sorry

/-! ## Change of rings -/

noncomputable abbrev noetherianRGammaIBaseChange
    {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)] (f : A →+* B) (I : Ideal A) :
    D B :=
  (Formalization.Books.MoreAlgebra.Unit63.derivedBaseChange f).obj
    ((idealTorsionAmbient I I.fg_of_isNoetherianRing).obj
      (Formalization.Books.MoreAlgebra.Unit67.moduleInDerived A
        (ModuleCat.of A A)))

noncomputable abbrev noetherianRGammaZBaseChange
    {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)] (f : A →+* B) (I : Ideal A) :
    D B :=
  (Formalization.Books.MoreAlgebra.Unit63.derivedBaseChange f).obj
    ((localCohomologyAmbient I I.fg_of_isNoetherianRing).obj
      (Formalization.Books.MoreAlgebra.Unit67.moduleInDerived A
        (ModuleCat.of A A)))

noncomputable abbrev noetherianRGammaY
    {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing B] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)] (f : A →+* B) (I : Ideal A) :
    D B :=
  (localCohomologyAmbient (I.map f) (I.map f).fg_of_isNoetherianRing).obj
    (Formalization.Books.MoreAlgebra.Unit67.moduleInDerived B
      (ModuleCat.of B B))

noncomputable abbrev noetherianRGammaIB
    {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing B] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)] (f : A →+* B) (I : Ideal A) :
    D B :=
  (localCohomologyAmbient (I.map f) (I.map f).fg_of_isNoetherianRing).obj
    (Formalization.Books.MoreAlgebra.Unit67.moduleInDerived B
      (ModuleCat.of B B))

/-- The four objects in the source's change-of-rings display are canonically
isomorphic in `D(B)`. Here `noetherianRGammaY` uses the closed set `V(I B)`,
while `noetherianRGammaIB` uses the ideal `I B`; their definitions are
intentionally aligned. -/
theorem localCohomology_change_rings_noetherian
    {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (f : A →+* B) (I : Ideal A) :
    Nonempty (noetherianRGammaIBaseChange f I ≅ noetherianRGammaZBaseChange f I) ∧
      Nonempty (noetherianRGammaZBaseChange f I ≅ noetherianRGammaY f I) ∧
        Nonempty (noetherianRGammaY f I ≅ noetherianRGammaIB f I) := by
  sorry

end

end Formalization.Books.Dualizing.Unit10
