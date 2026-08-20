import Formalization.Books.Algebra.Unit37.NormalRings
import Formalization.Books.Algebra.Unit96.Completion
import Formalization.Books.Algebra.Unit105.CatenaryRings
import Formalization.Books.Algebra.Unit155.Henselization
import Formalization.Books.MoreAlgebra.Unit51
import Formalization.Books.MoreAlgebra.Unit107.LocalIrreducibility
import Formalization.Books.Topology.Unit10.KrullDimension
import Mathlib.RingTheory.RingHom.Flat

/-!
# More on Algebra, Chapter 110: Formally catenary rings

This file formalizes the source definition of formal catenarity and the
interfaces for Ratliff's characterization, the flat equidimensional lemma,
and the geometrically normal formal-fibre consequence.
-/

namespace Formalization.Books.MoreAlgebra.Unit110

open Formalization.Books.Algebra.Unit37
open Formalization.Books.Algebra.Unit96
open Formalization.Books.Algebra.Unit105
open Formalization.Books.Algebra.Unit155
open Formalization.Books.MoreAlgebra.Unit51
open Formalization.Books.MoreAlgebra.Unit107
open Formalization.Books.Topology.Unit10

noncomputable section

universe u

/-! ## The formal-catenarity predicate -/

/-- A Noetherian local ring is formally catenary when every minimal
component of its completion is equidimensional. -/
def FormallyCatenary
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] : Prop :=
  ∀ p : PrimeSpectrum A, p.asIdeal ∈ minimalPrimes A →
    Equidimensional (X := PrimeSpectrum
      ((ringCompletion (IsLocalRing.maximalIdeal A)) ⧸
        Ideal.map
          (algebraMap A (ringCompletion (IsLocalRing.maximalIdeal A)))
          p.asIdeal))

/-- Quotients of formally catenary Noetherian local rings are formally
catenary. -/
theorem formallyCatenary_quotient
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : FormallyCatenary A) (I : Ideal A) (hI : I ≠ ⊤) :
    letI : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
    letI : IsLocalRing (A ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective
    FormallyCatenary (A ⧸ I) := by
  sorry

/-- The completion quotient attached to every prime of a formally catenary
ring has equidimensional spectrum. -/
theorem equidimensional_completion_quotient_of_formallyCatenary
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : FormallyCatenary A) (p : PrimeSpectrum A) :
    Equidimensional (X := PrimeSpectrum
      ((ringCompletion (IsLocalRing.maximalIdeal A)) ⧸
        Ideal.map
          (algebraMap A (ringCompletion (IsLocalRing.maximalIdeal A)))
          p.asIdeal)) := by
  sorry

/-! ## Failure of formal catenarity -/

/-- A Noetherian local ring which is not formally catenary is not universally
catenary. -/
theorem not_isUniversallyCatenary_of_not_formallyCatenary
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : ¬ FormallyCatenary A) :
    ¬ IsUniversallyCatenary A := by
  sorry

/-! ## Flat maps with equidimensional target -/

/-- A flat local map with catenary equidimensional target has equidimensional
fibres, and its source is catenary and equidimensional. -/
theorem flat_under_catenary_equidimensional
    {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) [IsLocalHom f]
    (hflat : RingHom.Flat f)
    (hBcat : IsCatenaryRing B)
    (hBeq : Equidimensional (X := PrimeSpectrum B)) :
    (∀ p : PrimeSpectrum A,
      Equidimensional (X := PrimeSpectrum
        (B ⧸ Ideal.map f p.asIdeal))) ∧
      IsCatenaryRing A ∧ Equidimensional (X := PrimeSpectrum A) := by
  sorry

/-! ## Ratliff's theorem -/

/-- A formally catenary Noetherian local ring is universally catenary. -/
theorem isUniversallyCatenary_of_formallyCatenary
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : FormallyCatenary A) :
    IsUniversallyCatenary A := by
  sorry

/-- Ratliff's characterization of formally catenary Noetherian local rings. -/
theorem isUniversallyCatenary_iff_formallyCatenary
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    IsUniversallyCatenary A ↔ FormallyCatenary A := by
  sorry

/-! ## Geometrically normal formal fibres -/

/-- Geometrically normal formal fibres make the henselization universally
catenary, and make the original ring universally catenary when it is
unibranch. -/
theorem henselization_universallyCatenary_of_geometricallyNormalFormalFibres
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : HasFormalFibresProperty GeometricallyNormalProperty A)
    (D : HenselizationData A) :
    IsUniversallyCatenary D.carrier ∧
      (IsUnibranch A → IsUniversallyCatenary A) := by
  sorry

/-- In the normal case from the source's parenthetical example, geometrically
normal formal fibres imply universal catenarity. -/
theorem isUniversallyCatenary_of_geometricallyNormalFormalFibres_of_isNormalRing
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : HasFormalFibresProperty GeometricallyNormalProperty A)
    (hnormal : IsNormalRing A) :
    IsUniversallyCatenary A := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit110
