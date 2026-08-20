import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RingHom.EssFiniteType
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Formalization.Books.Algebra.Unit96.Completion
import Formalization.Books.Algebra.Unit147.IntegralClosureSmoothBaseChange
import Formalization.Books.Algebra.Unit166.GeometricallyRegular
import Formalization.Books.MoreAlgebra.Unit41.RegularRingMaps
import Formalization.Books.MoreAlgebra.Unit52.ExcellentRings

/-!
# Smoothing Ring Maps, Chapter 1: Introduction

The introductory section records the main theorem, the reduction through
nilpotent deformations, Artin's approximation property, and the standard
completion examples.  Proposition proofs are intentionally postponed.
-/

namespace Formalization.Books.Smoothing.Unit01

open CategoryTheory
open CategoryTheory.Limits

open Formalization.Books.Algebra.Unit96
open Formalization.Books.Algebra.Unit147
open Formalization.Books.Algebra.Unit166
open Formalization.Books.MoreAlgebra.Unit41
open Formalization.Books.MoreAlgebra.Unit50
open Formalization.Books.MoreAlgebra.Unit52

noncomputable section

universe u

/-! ## The main theorem and its reductions -/

/- The source's phrase “filtered colimit of smooth algebras” is the established
   directed-system structure from Algebra, Chapter 147. -/

/-- Popescu's main theorem: a regular map of Noetherian rings is a filtered
colimit of smooth algebras over its source. -/
theorem popescu_main_theorem
    {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) (hregular : IsRegularRingMap f) :
    letI : Algebra R S := f.toAlgebra
    Nonempty (FilteredSmoothAlgebraColimit R S) := by
  sorry

/- The overview's nilpotent deformation is written using the canonical
   quotient algebra on the target. -/
abbrev infinitesimalTarget
    {R Λ : Type u} [CommRing R] [CommRing Λ] [Algebra R Λ]
    (I : Ideal R) : Type u :=
  Λ ⧸ Ideal.map (algebraMap R Λ) I

noncomputable instance infinitesimalTarget.algebraQuotient
    {R Λ : Type u} [CommRing R] [CommRing Λ] [Algebra R Λ]
    (I : Ideal R) : Algebra (R ⧸ I) (infinitesimalTarget (Λ := Λ) I) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (R := R) (A := Λ) (p := I)
    (P := Ideal.map (algebraMap R Λ) I) Ideal.le_comap_map

/-- The source's “flat infinitesimal deformation of a filtered colimit of
smooth algebras” hypothesis: the base ideal is nilpotent, the target map is
flat, and the infinitesimal reduction already has a filtered smooth-colimit
presentation. -/
def IsFlatInfinitesimalDeformation
    {R Λ : Type u} [CommRing R] [CommRing Λ] [Algebra R Λ]
    (I : Ideal R) : Prop :=
  IsNilpotent I ∧
    RingHom.Flat (algebraMap R Λ) ∧
      Nonempty (FilteredSmoothAlgebraColimit
        (R ⧸ I) (infinitesimalTarget (Λ := Λ) I))

/-- Filtered colimits of smooth algebras are stable under flat nilpotent
deformations. -/
theorem filteredSmooth_of_flatInfinitesimalDeformation
    {R Λ : Type u} [CommRing R] [CommRing Λ] [Algebra R Λ]
    (I : Ideal R)
    (hdeformation : IsFlatInfinitesimalDeformation (Λ := Λ) I) :
    Nonempty (FilteredSmoothAlgebraColimit R Λ) := by
  sorry

/-- It is enough for the main theorem to be known for maps between reduced
Noetherian rings. -/
theorem popescu_main_theorem_of_reduced_case
    (hreduced :
      ∀ (R S : Type u) [CommRing R] [CommRing S]
        [IsNoetherianRing R] [IsNoetherianRing S]
        [IsReduced R] [IsReduced S]
        (f : R →+* S), IsRegularRingMap f →
          letI : Algebra R S := f.toAlgebra
          Nonempty (FilteredSmoothAlgebraColimit R S)) :
    ∀ (R S : Type u) [CommRing R] [CommRing S]
      [IsNoetherianRing R] [IsNoetherianRing S]
      (f : R →+* S), IsRegularRingMap f →
        letI : Algebra R S := f.toAlgebra
        Nonempty (FilteredSmoothAlgebraColimit R S) := by
  sorry

/-- The lifting and desingularization reductions reduce the main theorem to
Noetherian geometrically regular algebras over fields. -/
theorem popescu_main_theorem_of_geometricallyRegular_field_case
    (hfield :
      ∀ (k Λ : Type u) [Field k] [CommRing Λ] [Algebra k Λ]
        [IsNoetherianRing Λ]
        (hΛ : IsGeometricallyRegular k Λ),
        Nonempty (FilteredSmoothAlgebraColimit k Λ)) :
    ∀ (R S : Type u) [CommRing R] [CommRing S]
      [IsNoetherianRing R] [IsNoetherianRing S]
      (f : R →+* S), IsRegularRingMap f →
        letI : Algebra R S := f.toAlgebra
        Nonempty (FilteredSmoothAlgebraColimit R S) := by
  sorry

/-! ## Artin's approximation property -/

/-- A tuple solves a finite system of multivariate polynomial equations after
applying the coefficient map `coeff`. -/
def SolvesPolynomialSystem
    {A B : Type u} [CommRing A] [CommRing B]
    (coeff : A →+* B) {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) A) (x : Fin n → B) : Prop :=
  ∀ i, MvPolynomial.eval₂Hom coeff x (f i) = 0

/-- Artin's approximation property for a henselian Noetherian local ring:
every finite polynomial system has a solution in the adic completion exactly
when it has a solution in the ring. -/
def HasApproximationProperty
    (A : Type u) [CommRing A] [HenselianLocalRing A]
    [IsNoetherianRing A] : Prop :=
  ∀ (n m : ℕ) (f : Fin m → MvPolynomial (Fin n) A),
    (∃ x : Fin n → ringCompletion (IsLocalRing.maximalIdeal A),
      SolvesPolynomialSystem (algebraMap A
        (ringCompletion (IsLocalRing.maximalIdeal A))) f x) ↔
    ∃ x : Fin n → A, SolvesPolynomialSystem (RingHom.id A) f x

/-- A filtered smooth-colimit presentation of the completion implies Artin's
approximation property. -/
theorem approximationProperty_of_completion_filteredSmooth
    {A : Type u} [CommRing A] [HenselianLocalRing A]
    [IsNoetherianRing A]
    (hcompletion :
      Nonempty (FilteredSmoothAlgebraColimit A
        (ringCompletion (IsLocalRing.maximalIdeal A)))) :
    HasApproximationProperty A := by
  sorry

/-! ## The standard completion cases and the converse -/

/-- The completion of a local ring essentially of finite type over a field is
a filtered colimit of smooth algebras. -/
theorem completion_filteredSmooth_of_essFiniteType_over_field
    {k R : Type u} [Field k] [CommRing R] [IsLocalRing R]
    (f : k →+* R) (hfinite : RingHom.EssFiniteType f) :
    Nonempty (FilteredSmoothAlgebraColimit R
      (ringCompletion (IsLocalRing.maximalIdeal R))) := by
  sorry

/-- The completion of a local ring essentially of finite type over an
excellent discrete valuation ring is a filtered colimit of smooth algebras. -/
theorem completion_filteredSmooth_of_essFiniteType_over_excellent_dvr
    {D R : Type u} [CommRing D] [IsDomain D]
    [IsDiscreteValuationRing D]
    [CommRing R] [IsLocalRing R]
    (hD : IsExcellent D) (f : D →+* R)
    (hfinite : RingHom.EssFiniteType f) :
    Nonempty (FilteredSmoothAlgebraColimit R
      (ringCompletion (IsLocalRing.maximalIdeal R))) := by
  sorry

/-- For an excellent local ring, the map to its completion is regular; this
is the application of Popescu's theorem mentioned in the introduction. -/
theorem completion_map_isRegular_of_excellent
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : IsExcellent A) :
    IsRegularRingMap
      (algebraMap A (ringCompletion (IsLocalRing.maximalIdeal A))) := by
  sorry

/-- Excellent local rings have geometrically regular formal fibres, the
condition used to recognize the regularity of the completion map. -/
theorem excellent_has_geometricallyRegular_formalFibers
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : IsExcellent A) :
    HasGeometricallyRegularLocalFormalFibers A := by
  sorry

/-- The approximation property holds for excellent henselian Noetherian
local rings, as conjectured by Artin and obtained here from the completion
case of the main theorem. -/
theorem approximationProperty_of_excellent
    {A : Type u} [CommRing A] [HenselianLocalRing A]
    [IsNoetherianRing A] (hA : IsExcellent A) :
    HasApproximationProperty A := by
  sorry

/-- A Noetherian local henselian ring with Artin's approximation property is
excellent. -/
theorem isExcellent_of_approximationProperty
    {A : Type u} [CommRing A] [HenselianLocalRing A]
    [IsNoetherianRing A] (hA : HasApproximationProperty A) :
    IsExcellent A := by
  sorry

end

end Formalization.Books.Smoothing.Unit01
