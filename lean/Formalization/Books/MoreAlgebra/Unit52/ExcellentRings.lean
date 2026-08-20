import Formalization.Books.MoreAlgebra.Unit51
import Formalization.Books.Algebra.Unit105.CatenaryRings
import Formalization.Books.Algebra.Unit162.NagataRings
import Mathlib.RingTheory.DedekindDomain.Basic

/-!
# More on Algebra, Chapter 52: Excellent rings

This file records the definitions and theorem interfaces in the section
“Excellent rings”.  The G-ring and formal-fibre predicates are reused from
Chapters 50–51, while `IsJ2`, universal catenarity, Nagata rings, and normal
rings use the established earlier-book declarations.
-/

namespace Formalization.Books.MoreAlgebra.Unit52

open Formalization.Books.Algebra.Unit96
open Formalization.Books.Algebra.Unit37
open Formalization.Books.Algebra.Unit105
open Formalization.Books.Algebra.Unit162
open Formalization.Books.MoreAlgebra.Unit47
open Formalization.Books.MoreAlgebra.Unit50
open Formalization.Books.MoreAlgebra.Unit51

noncomputable section

universe u

/-! ## Definitions -/

/-- A Noetherian ring which is a G-ring and a J-2 ring. -/
def IsQuasiExcellent (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧ IsGRing R ∧ IsJ2 R

/-- A quasi-excellent universally catenary ring. -/
def IsExcellent (R : Type u) [CommRing R] : Prop :=
  IsQuasiExcellent R ∧ IsUniversallyCatenary R

/-- Normality of a field algebra, viewed as a property of formal fibres.

Unlike `GeometricallyNormalProperty`, this records ordinary normality of the
fibre ring, which is the hypothesis in the final completion theorem of the
source section.
-/
def NormalRingProperty : RingMapProperty :=
  fun _ R _ _ _ => IsNormalRing R

/-! ## Basic consequences and permanence -/

/-- The expanded formal-fibre and J-2 description of quasi-excellence. -/
theorem isQuasiExcellent_iff_geometricallyRegularFormalFibers_and_isJ2
    {R : Type u} [CommRing R] :
    IsQuasiExcellent R ↔
      IsNoetherianRing R ∧
        HasGeometricallyRegularFormalFibers R ∧ IsJ2 R := by
  sorry

/-- A finite-type algebra over a quasi-excellent ring remains
quasi-excellent after any localization of its target. -/
theorem isQuasiExcellent_localization_of_finiteType
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (M : Submonoid S)
    (hR : IsQuasiExcellent R) (hfinite : RingHom.FiniteType f) :
    IsQuasiExcellent (Localization M) := by
  sorry

/-- A finite-type algebra over an excellent ring remains excellent after any
localization of its target. -/
theorem isExcellent_localization_of_finiteType
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (M : Submonoid S)
    (hR : IsExcellent R) (hfinite : RingHom.FiniteType f) :
    IsExcellent (Localization M) := by
  sorry

/-! ## Standard excellent rings -/

/-- Fields, complete local Noetherian rings, `ℤ`, and characteristic-zero
Dedekind domains are excellent. -/
theorem isExcellent_ubiquity :
    (∀ (K : Type u) [Field K], IsExcellent K) ∧
    (∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [IsAdicComplete (IsLocalRing.maximalIdeal A) A], IsExcellent A) ∧
    IsExcellent ℤ ∧
    (∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
      [IsDedekindDomain R] [CharZero (FractionRing R)], IsExcellent R) := by
  sorry

/-- Finite-type extensions of excellent rings are excellent. -/
theorem isExcellent_of_finiteType
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hR : IsExcellent R)
    (hfinite : RingHom.FiniteType f) :
    IsExcellent S := by
  sorry

/-! ## Nagata rings -/

/-- For a Noetherian local ring, being Nagata is equivalent to having
geometrically reduced formal fibres. -/
theorem isNagataRing_iff_geometricallyReducedFormalFibres
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    IsNagataRing A ↔
      HasFormalFibresProperty GeometricallyReducedProperty A := by
  sorry

/-- Every quasi-excellent ring is Nagata. -/
theorem isNagataRing_of_isQuasiExcellent
    {R : Type u} [CommRing R] (hR : IsQuasiExcellent R) :
    IsNagataRing R := by
  sorry

/-! ## Normal completions -/

/-- Excellent and quasi-excellent local rings have normal formal fibres. -/
theorem normalFormalFibres_of_isExcellent_or_isQuasiExcellent
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : IsExcellent A ∨ IsQuasiExcellent A) :
    HasFormalFibresProperty NormalRingProperty A := by
  sorry

/-- A Noetherian local normal ring with normal formal fibres has normal
completion. -/
theorem completion_normal_of_normal_of_normalFormalFibres
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : IsNormalRing A)
    (hfib : HasFormalFibresProperty NormalRingProperty A) :
    IsNormalRing (ringCompletion (IsLocalRing.maximalIdeal A)) := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit52
