import Formalization.Books.Algebra.Unit106.RegularLocalRings
import Formalization.Books.Algebra.Unit120.Factorization
import Formalization.Books.MoreAlgebra.Unit119.Determinants
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# More on Algebra, Chapter 122: A regular local ring is a UFD

This file records the three source lemmas in the section.  Picard groups are
Mathlib's `CommRing.Pic`, a UFD is represented by the established pair
`IsDomain` and `UniqueFactorizationMonoid`, and the generic-fibre hypotheses
use Mathlib's canonical flatness, essential-finite-type, valuation-ring, and
regular-ring interfaces.
-/

namespace Formalization.Books.MoreAlgebra.Unit122

open scoped TensorProduct

universe u v

noncomputable section

/-! ## Picard groups of regular local rings -/

/- The source writes `Pic(R_f) = 0`; the canonical group-theoretic form is
   subsingletonity of the Picard group. -/
/-- The Picard group of a localization of a regular local ring is trivial. -/
theorem picard_group_localization_regular_local
    {R : Type u} [CommRing R] [IsRegularLocalRing R] (f : R) :
    Subsingleton (CommRing.Pic (Localization.Away f)) := by
  sorry

/-! ## The UFD theorem -/

/- A UFD is represented as a domain together with Mathlib's unique
   factorization class, following Chapter 120's established interface. -/
/-- A regular local ring is a unique factorization domain. -/
theorem regular_local_ring_is_ufd
    {R : Type u} [CommRing R] [IsRegularLocalRing R] :
    IsDomain R ∧ UniqueFactorizationMonoid R := by
  sorry

/-! ## Picard groups of generic fibres -/

/-- The Picard group of the generic fibre is trivial under the source's
valuation-ring, flat, essentially-finite-type, and regular-fibre hypotheses. -/
theorem picard_group_generic_fiber_regular
    {R A K : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    [CommRing A] [Algebra R A] [IsLocalRing A]
    [IsLocalHom (algebraMap R A)] [Module.Flat R A]
    [Algebra.EssFiniteType R A]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [IsRegularRing (A ⊗[R] IsLocalRing.ResidueField R)] :
    Subsingleton (CommRing.Pic (A ⊗[R] K)) := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit122
