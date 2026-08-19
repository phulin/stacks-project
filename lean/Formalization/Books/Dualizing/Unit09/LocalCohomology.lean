import Formalization.Books.MoreAlgebra.Unit89.TorsionModules
import Formalization.Books.MoreAlgebra.Unit74.DerivedHom
import Formalization.Books.Derived.Unit22.CompositionRightDerivedFunctors
import Formalization.Books.Algebra.Unit71.ExtGroups
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Dualizing Complexes, Chapter 9: Local cohomology

This file records the source-facing local-cohomology functor, its Čech
presentation, and the change-of-rings, tensor, spectral-sequence, and Ext
interfaces in the numbered section of the chapter.  The constructions and
theorem interfaces use the earlier ideal-power torsion and derived-category
APIs; proofs of the new mathematical assertions are deferred.
-/

namespace Formalization.Books.Dualizing.Unit09

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit71
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit22
open Formalization.Books.Homology.Unit24
open Formalization.Books.MoreAlgebra.Unit53
open Formalization.Books.MoreAlgebra.Unit56
open Formalization.Books.MoreAlgebra.Unit59
open Formalization.Books.MoreAlgebra.Unit89
open scoped BigOperators

universe u w

noncomputable section

/-! ## Derived torsion and local cohomology -/

/- The source distinguishes this closed-support right adjoint from the
naive ideal-torsion functor `RΓ_I`.  The latter belongs to the earlier
bad-local-cohomology discussion, which has no canonical declaration in the
available project API; the comparison is therefore recorded here as a
source-facing warning rather than duplicated under a new name. -/

abbrev D (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :=
  DerivedModule R

abbrev DPlus (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :=
  Formalization.Books.MoreAlgebra.Unit56.DPlus R

/-- The closed subset cut out by an ideal. -/
def closedSetOfIdeal {R : Type u} [CommRing R] (I : Ideal R) : Set (PrimeSpectrum R) :=
  PrimeSpectrum.zeroLocus (I : Set R)

/-- The full derived subcategory whose cohomology modules are `I`-power torsion. -/
def iPowerTorsionDerivedProperty {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (I : Ideal R) :
    ObjectProperty (D R) :=
  fun K => ∀ i : ℤ,
    IsIPowerTorsion I
      ((Formalization.Books.MoreAlgebra.Unit67.derivedCohomology R i).obj K : Type u)

abbrev iPowerTorsionDerivedCategory {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (I : Ideal R) :=
  (iPowerTorsionDerivedProperty I).FullSubcategory

/-- The inclusion of the derived `I`-power-torsion subcategory. -/
abbrev iPowerTorsionDerivedInclusion {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (I : Ideal R) :
    iPowerTorsionDerivedCategory I ⥤ D R :=
  (iPowerTorsionDerivedProperty I).ι

/-- Data expressing that the inclusion of derived torsion objects has the
right adjoint called `RΓ_Z`. -/
structure LocalCohomologyData {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (I : Ideal R) where
  functor : D R ⥤ iPowerTorsionDerivedCategory I
  adjunction : iPowerTorsionDerivedInclusion I ⊣ functor

/-- Existence of the right adjoint to the inclusion of derived torsion. -/
theorem localCohomologyData_exists {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (I : Ideal R) (hI : I.FG) :
    Nonempty (LocalCohomologyData I) := by
  sorry

/-- The source's `RΓ_Z`, chosen from the right-adjoint existence theorem. -/
noncomputable def localCohomologyFunctor {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (I : Ideal R) (hI : I.FG) :
    D R ⥤ iPowerTorsionDerivedCategory I :=
  (Classical.choice (localCohomologyData_exists I hI)).functor

def localCohomologyRightAdjoint {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (I : Ideal R) (hI : I.FG) :
    Prop := Nonempty (iPowerTorsionDerivedInclusion I ⊣ localCohomologyFunctor I hI)

theorem localCohomology_rightAdjoint {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (I : Ideal R) (hI : I.FG) :
    localCohomologyRightAdjoint I hI := by
  exact ⟨(Classical.choice (localCohomologyData_exists I hI)).adjunction⟩

/-- The `R`-module `H^i_Z(K)`, represented by the cohomology of `RΓ_Z(K)`. -/
noncomputable def localCohomologyModule {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (I : Ideal R) (hI : I.FG)
    (K : D R) (i : ℤ) : ModuleCat.{u} R :=
  (Formalization.Books.MoreAlgebra.Unit67.derivedCohomology R i).obj
    ((iPowerTorsionDerivedInclusion I).obj
      ((localCohomologyFunctor I hI).obj K))

/-- The underlying type of `H^i_Z(K)`. -/
abbrev localCohomologyGroup {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (I : Ideal R) (hI : I.FG)
    (K : D R) (i : ℤ) : Type u :=
  localCohomologyModule I hI K i

/-- The ambient derived-category endofunctor underlying `RΓ_Z`. -/
noncomputable abbrev localCohomologyAmbient {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (I : Ideal R) (hI : I.FG) :
    D R ⥤ D R :=
  localCohomologyFunctor I hI ⋙ iPowerTorsionDerivedInclusion I

/-- The module version of local cohomology used in the `E₂` page. -/
noncomputable abbrev localCohomologyModuleGroup {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (I : Ideal R) (hI : I.FG)
    (M : ModuleCat.{u} R) (i : ℤ) : ModuleCat.{u} R :=
  localCohomologyModule I hI
    (Formalization.Books.MoreAlgebra.Unit67.moduleInDerived R M) i

/-! ### The extended Čech object -/

/-- The module in Čech degree `p` obtained by taking the product over all
`p`-fold intersections of the principal localizations associated to `f`. -/
def extendedCechTerm {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (p : ℕ) : ModuleCat.{u} R :=
  ModuleCat.of R
    (∀ s : {s : Finset (Fin r) // s.card = p},
      LocalizedModule
        (Submonoid.powers (∏ i : Fin r, if i ∈ s.1 then f i else 1)) R)

/-- The source's extended alternating Čech complex, retaining its terms and
the cochain differential as the data needed by the derived presentation. -/
structure ExtendedCechPresentation {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] {r : ℕ} (f : Fin r → R) where
  complex : Formalization.Books.MoreAlgebra.Unit59.Comp R
  term_spec : ∀ p : ℕ,
    Nonempty (complex.X (p : ℤ) ≅ extendedCechTerm f p)
  augmentation : Nonempty (complex ⟶
    (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))

/-- The derived object represented by an extended Čech presentation. -/
noncomputable abbrev extendedCechObject
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] {r : ℕ} {f : Fin r → R}
    (C : ExtendedCechPresentation f) : D R :=
  (Formalization.Books.MoreAlgebra.Unit59.derivedComplexQuotient R).obj C.complex

/-- The Čech formula for `RΓ_Z`, functorially in the derived object. -/
theorem localCohomology_cech_formula {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (I : Ideal R) (hI : I.FG)
    {r : ℕ} (f : Fin r → R) (hgen : I = Ideal.span (Set.range f)) :
    ∃ C : ExtendedCechPresentation f,
      Nonempty (Formalization.Books.MoreAlgebra.Unit59.derivedTensorFunctor
          (extendedCechObject C) ≅
        localCohomologyAmbient I hI) := by
  sorry

/-! ## Restriction, base change, and vanishing -/

/-- Restriction of scalars on derived categories, obtained from the exact
restriction functor on module categories. -/
noncomputable abbrev derivedRestriction {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)] (f : A →+* B) :
    D B ⥤ D A :=
  (ModuleCat.restrictScalars f).mapDerivedCategory

theorem localCohomology_restrict_scalars {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (f : A →+* B) (I : Ideal A) (hI : I.FG) :
    Nonempty (
      (derivedRestriction f ⋙ localCohomologyAmbient I hI) ≅
        (localCohomologyAmbient (I.map f) (hI.map f) ⋙
          derivedRestriction f)) := by
  sorry

theorem localCohomology_base_change {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (f : A →+* B) (I : Ideal A) (hI : I.FG) :
    Nonempty (
      (localCohomologyAmbient I hI ⋙
          Formalization.Books.MoreAlgebra.Unit63.derivedBaseChange f) ≅
        (Formalization.Books.MoreAlgebra.Unit63.derivedBaseChange f ⋙
          localCohomologyAmbient (I.map f) (hI.map f))) := by
  sorry

/-- Multiplication by `a` on the `i`th cohomology module of a derived object. -/
def derivedScalarMap {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (a : R) (K : D R) (i : ℤ) :
  (Formalization.Books.MoreAlgebra.Unit67.derivedCohomology R i).obj K ⟶
      (Formalization.Books.MoreAlgebra.Unit67.derivedCohomology R i).obj K :=
  ModuleCat.ofHom
    (LinearMap.lsmul R
      ((Formalization.Books.MoreAlgebra.Unit67.derivedCohomology R i).obj K) a)

/-- A derived object is localized at `a` when multiplication by `a` is an
isomorphism on every cohomology module. -/
def IsDerivedLocalizedAt {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (a : R) (K : D R) : Prop :=
  ∀ i : ℤ, IsIso (derivedScalarMap a K i)

theorem localCohomology_vanishes_of_localized {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (I : Ideal R) (hI : I.FG)
    (a : R) (ha : a ∈ I) (K : D R) (hK : IsDerivedLocalizedAt a K) :
    IsZero ((localCohomologyAmbient I hI).obj K) := by
  sorry

/-! ## Tensor products and intersections -/

theorem localCohomology_tensor_product {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (I : Ideal R) (hI : I.FG)
    (K L : D R) :
    Nonempty ((localCohomologyAmbient I hI).obj
        (Formalization.Books.MoreAlgebra.Unit59.derivedTensor K L) ≅
          Formalization.Books.MoreAlgebra.Unit59.derivedTensor K
          ((localCohomologyAmbient I hI).obj L)) ∧
      Nonempty ((localCohomologyAmbient I hI).obj
        (Formalization.Books.MoreAlgebra.Unit59.derivedTensor K L) ≅
          Formalization.Books.MoreAlgebra.Unit59.derivedTensor
          ((localCohomologyAmbient I hI).obj K) L) ∧
      Nonempty ((localCohomologyAmbient I hI).obj
        (Formalization.Books.MoreAlgebra.Unit59.derivedTensor K L) ≅
          Formalization.Books.MoreAlgebra.Unit59.derivedTensor
          ((localCohomologyAmbient I hI).obj K)
          ((localCohomologyAmbient I hI).obj L)) := by
  sorry

theorem iPowerTorsionDerived_tensor_closed {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (I : Ideal R) (hI : I.FG)
    (K L : D R)
    (hKL : iPowerTorsionDerivedProperty I K ∨
      iPowerTorsionDerivedProperty I L) :
    iPowerTorsionDerivedProperty I
      (Formalization.Books.MoreAlgebra.Unit59.derivedTensor K L) := by
  sorry

theorem closedSetOfIdeal_inter {R : Type u} [CommRing R]
    (I J : Ideal R) :
    closedSetOfIdeal I ∩ closedSetOfIdeal J = closedSetOfIdeal (I + J) := by
  sorry

theorem localCohomology_composition {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (I J : Ideal R) (hI : I.FG) (hJ : J.FG) :
    Nonempty ((localCohomologyAmbient I hI ⋙
        localCohomologyAmbient J hJ) ≅
      localCohomologyAmbient (I + J) (Submodule.FG.sup hI hJ)) := by
  sorry

/-! ### The Grothendieck spectral sequence -/

/-- Filtered-complex data for the spectral sequence
`E₂^{p,q} = H^p_Y(H^q_Z(K)) ⇒ H^{p+q}_{Y∩Z}(K)`. -/
structure LocalCohomologySpectralSequenceData
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (I J : Ideal R) (hI : I.FG) (hJ : J.FG) (K : DPlus R) where
  filteredComplex : FilteredComplex (ModuleCat.{u} R)
  spectralSequence : FilteredComplexSpectralSequence filteredComplex
  e₂_page : ∀ p q : ℤ,
    Nonempty (spectralSequence.page 2 (p, q) ≅
      localCohomologyModuleGroup J hJ
          ((DerivedCategory.Plus.homologyFunctor
              (C := ModuleCat.{u} R) q).obj K) p)
  bounded : filteredComplexBounded spectralSequence
  converges :
    filteredComplexRegular spectralSequence ∧
      filteredComplexAbuts filteredComplex ∧
      FilteredComplexCohomologyComplete filteredComplex
  abutment : ∀ n : ℤ,
    Nonempty (filteredComplexCohomology filteredComplex n ≅
      localCohomologyModule (I + J) (Submodule.FG.sup hI hJ)
          ((DerivedCategory.Plus.ι (C := ModuleCat.{u} R)).obj K) n)

theorem localCohomology_spectral_sequence {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (I J : Ideal R) (hI : I.FG) (hJ : J.FG) (K : DPlus R) :
    Nonempty (LocalCohomologySpectralSequenceData I J hI hJ K) := by
  sorry

/-! ## Flat change of rings and Ext -/

noncomputable def idealQuotientBaseChangeMap {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) : A ⧸ I →+* B ⧸ I.map f :=
  Ideal.quotientMap (I.map f) f Ideal.le_comap_map

structure TorsionChangeOfRingsEquivalenceData
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (f : A →+* B) (I : Ideal A) (hI : I.FG) where
  baseChange : iPowerTorsionDerivedCategory I ⥤
    iPowerTorsionDerivedCategory (I.map f)
  restriction : iPowerTorsionDerivedCategory (I.map f) ⥤
    iPowerTorsionDerivedCategory I
  baseChange_ambient : Nonempty (
    baseChange ⋙ iPowerTorsionDerivedInclusion (I.map f) ≅
      iPowerTorsionDerivedInclusion I ⋙
        Formalization.Books.MoreAlgebra.Unit63.derivedBaseChange f)
  restriction_ambient : Nonempty (
    restriction ⋙ iPowerTorsionDerivedInclusion I ≅
      iPowerTorsionDerivedInclusion (I.map f) ⋙ derivedRestriction f)
  left_inverse : Nonempty (baseChange ⋙ restriction ≅ 𝟭 _)
  right_inverse : Nonempty (restriction ⋙ baseChange ≅ 𝟭 _)

theorem torsion_flat_change_of_rings {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (f : A →+* B) (I : Ideal A) (hI : I.FG)
    (hflat : RingHom.Flat f)
    (hquot : Function.Bijective (idealQuotientBaseChangeMap f I)) :
    Nonempty (TorsionChangeOfRingsEquivalenceData f I hI) := by
  sorry

theorem localCohomology_neighborhood_ext {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (f : A →+* B) (I : Ideal A) (hI : I.FG)
    (hflat : RingHom.Flat f)
    (hquot : Function.Bijective (idealQuotientBaseChangeMap f I))
    (K L : D A)
    (hK : iPowerTorsionDerivedProperty I K) :
    Nonempty (
      Formalization.Books.MoreAlgebra.Unit74.RHom (R := A) K L ≅
        (derivedRestriction f).obj
          (Formalization.Books.MoreAlgebra.Unit74.RHom (R := B)
            ((Formalization.Books.MoreAlgebra.Unit63.derivedBaseChange f).obj K)
            ((Formalization.Books.MoreAlgebra.Unit63.derivedBaseChange f).obj L))) := by
  sorry

theorem ext_group_flat_change_of_rings {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) (hI : I.FG)
    (hflat : RingHom.Flat f)
    (hquot : Function.Bijective (idealQuotientBaseChangeMap f I))
    (M N : ModuleCat.{u} A) (hM : IsIPowerTorsion I (M : Type u))
    (i : ℕ) :
    Nonempty (ExtGroup M N i ≃+
      ExtGroup ((ModuleCat.extendScalars f).obj M)
        ((ModuleCat.extendScalars f).obj N) i) := by
  sorry

end

end Formalization.Books.Dualizing.Unit09
