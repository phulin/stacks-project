import Formalization.Books.Categories.Unit43.MonoidalCategories
import Formalization.Books.MoreAlgebra.Unit75.PerfectComplexes
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# More on Algebra, Chapter 127: invertible objects in the derived category

This file records the statements in the chapter using the derived tensor,
derived Hom, perfect-complex, cohomology, and change-of-rings interfaces
already established in earlier chapters.  The two small structures below
package the source's finite subcomplex and finite product decompositions.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open Formalization.Books.Categories.Unit43
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.MoreAlgebra.Unit65
open Formalization.Books.MoreAlgebra.Unit74
open Formalization.Books.MoreAlgebra.Unit75
open scoped CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Preadditive CategoryTheory.Pretriangulated

universe u w

namespace Formalization.Books.MoreAlgebra.Unit127

abbrev Mod (R : Type u) [CommRing R] := ModuleCat.{u} R

abbrev Comp (R : Type u) [CommRing R] := Unit75.Comp R

abbrev D (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] := Unit75.D R

/-! ## Symmetric monoidality -/

/- The source's derived tensor product is the tensor operation in this
   monoidal structure.  Keeping the monoidal and symmetric structures in one
   package lets the chosen structure be installed as the canonical instance
   used by the later duality and invertibility statements. -/
structure DerivedSymmetricMonoidalData
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] where
  monoidal : MonoidalCategory (D R)
  tensor_obj_eq : ∀ K L : D R,
    @MonoidalCategoryStruct.tensorObj (D R) _
        monoidal.toMonoidalCategoryStruct K L =
      Unit74.derivedTensor K L
  symmetric : @SymmetricCategory (D R) _ monoidal

theorem derivedCategory_symmetricMonoidal_exists
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] :
    Nonempty (DerivedSymmetricMonoidalData R) := by
  sorry

noncomputable def derivedSymmetricMonoidalData
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] :
    DerivedSymmetricMonoidalData R :=
  Classical.choice (derivedCategory_symmetricMonoidal_exists R)

noncomputable instance derivedCategoryMonoidalCategory
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] : MonoidalCategory (D R) :=
  (derivedSymmetricMonoidalData R).monoidal

noncomputable instance derivedCategorySymmetricCategory
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] : SymmetricCategory (D R) :=
  (derivedSymmetricMonoidalData R).symmetric

theorem derivedCategory_tensor_obj_eq
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K L : D R) :
    K ⊗ L = Unit74.derivedTensor K L :=
  (derivedSymmetricMonoidalData R).tensor_obj_eq K L

/-! ## Finite free subcomplexes -/

def BoundedAboveFreeComplex
    (R : Type u) [CommRing R] (F : Comp R) : Prop :=
  IsBoundedAbove F ∧ ∀ n : ℤ, Module.Free R (F.X n : Type u)

structure FiniteFreeSubcomplex
    (R : Type u) [CommRing R] (F : Comp R) where
  complex : Comp R
  inclusion : complex ⟶ F
  inclusion_injective : ∀ n : ℤ, Function.Injective (inclusion.f n).hom
  bounded : IsBounded complex
  finite_free : ∀ n : ℤ, FiniteFreeModule R (complex.X n)

theorem boundedAboveFree_has_finiteFreeSubcomplex
    (R : Type u) [CommRing R] (F : Comp R)
    (hF : BoundedAboveFreeComplex R F)
    (N : ℕ) (degree : Fin N → ℤ)
    (element : ∀ i : Fin N, (F.X (degree i) : Type u)) :
    ∃ G : FiniteFreeSubcomplex R F,
      ∀ i : Fin N, ∃ x : (G.complex.X (degree i) : Type u),
        (G.inclusion.f (degree i)).hom x = element i := by
  sorry

/-! ## Duals and perfect objects -/

theorem hasLeftDual_iff_perfect
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M : D R) :
    (∃ N : D R, Nonempty (IsLeftDual M N)) ↔ Perfect R M := by
  sorry

theorem perfectDual_isLeftDual
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M : D R)
    (hM : Perfect R M) :
    Nonempty (IsLeftDual M (perfectDual R M)) := by
  sorry

/-! ## Invertibility and the local criterion -/

noncomputable def localizedShiftedUnit
    (R : Type u) [CommRing R] (f : R) (n : ℤ)
    [HasDerivedCategory.{w} (Mod (Localization.Away f))] :
    D (Localization.Away f) :=
  (shiftFunctor (D (Localization.Away f)) (-n)).obj
    (Unit75.moduleInDerived (Localization.Away f)
      (ModuleCat.of (Localization.Away f) (Localization.Away f)))

def IsLocallyShiftedUnit
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M : D R)
    (hlocalDC : ∀ f : R,
      HasDerivedCategory.{w} (Mod (Localization.Away f))) : Prop :=
  ∀ p : PrimeSpectrum R, ∃ f : R, f ∉ p.asIdeal ∧ ∃ n : ℤ,
    letI := hlocalDC f
    Nonempty
      (((derivedBaseChange (algebraMap R (Localization.Away f))).obj M) ≅
        localizedShiftedUnit R f n)

theorem invertible_iff_locallyShiftedUnit
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M : D R)
    (hlocalDC : ∀ f : R,
      HasDerivedCategory.{w} (Mod (Localization.Away f))) :
    IsInvertible M ↔ IsLocallyShiftedUnit R M hlocalDC := by
  sorry

/-! ## The four consequences for an invertible object -/

noncomputable def cohomologyDirectSum
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M : D R) (a b : ℤ) : D R :=
  ⨁ fun n : Finset.Icc a b =>
    (Unit75.moduleInDerived R
      ((derivedCohomologyFunctor (Mod R) (n : ℤ)).obj M))⟦(-(n : ℤ))⟧

theorem invertible_perfect
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M : D R)
    (hM : IsInvertible M) : Perfect R M := by
  sorry

theorem invertible_cohomology_decomposition
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M : D R)
    (hM : IsInvertible M) :
    ∃ a b : ℤ, Nonempty (M ≅ cohomologyDirectSum R M a b) := by
  sorry

theorem invertible_cohomology_finiteProjective
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M : D R)
    (hM : IsInvertible M) :
    ∀ n : ℤ,
      FiniteProjectiveModule R
        ((derivedCohomologyFunctor (Mod R) n).obj M) := by
  sorry

abbrev ProductIndex (a b : ℤ) := Finset.Icc a b

abbrev ProductRing (a b : ℤ) (S : ProductIndex a b → CommRingCat.{u}) :=
  ∀ i, (S i : Type u)

/- A component module is viewed as an `R`-module through the projection from
   the finite product decomposition. -/
noncomputable def productComponentRingHom
    {R : Type u} [CommRing R] {a b : ℤ}
    {S : ProductIndex a b → CommRingCat.{u}}
    (e : R ≃+* ProductRing a b S) (i : ProductIndex a b) :
    R →+* (S i : Type u) :=
  (Pi.evalRingHom (fun j => (S j : Type u)) i).comp e.toRingHom

structure CohomologyProductDecomposition
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M : D R) where
  lower : ℤ
  upper : ℤ
  componentRing : ↥(ProductIndex lower upper) → CommRingCat.{u}
  ringEquiv : R ≃+* ProductRing lower upper componentRing
  componentModule : ∀ i, ModuleCat.{u} (componentRing i)
  component_invertible : ∀ i,
    IsInvertible (componentModule i)
  cohomology_vanishes_outside : ∀ n : ℤ, n < lower ∨ upper < n →
    IsZero ((derivedCohomologyFunctor (Mod R) n).obj M)
  cohomology_component_equiv : ∀ i : ↥(ProductIndex lower upper),
    Nonempty
      (((derivedCohomologyFunctor (Mod R) (i : ℤ)).obj M : Type u) ≃ₗ[R]
        ((ModuleCat.restrictScalars
          (productComponentRingHom ringEquiv i)).obj
          (componentModule i) : Type u))

theorem invertible_cohomology_product_decomposition
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M : D R)
    (hM : IsInvertible M) :
    Nonempty (CohomologyProductDecomposition R M) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit127
