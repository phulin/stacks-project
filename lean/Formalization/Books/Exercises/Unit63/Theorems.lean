import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Noetherian.Basic

import Formalization.Books.Algebra.Unit105.CatenaryRings
import Formalization.Books.Dualizing.Unit06.ArtinianDuality
import Formalization.Books.Exercises.Unit63.Definitions

/-!
# Exercises, Chapter 63: Theorems

The source permits any one substantial lecture theorem for each topic. The
interfaces below choose standard forms that are directly usable with the
canonical Mathlib and earlier-project definitions.
-/

namespace Formalization.Books.Exercises.Unit63

open CategoryTheory

universe u v

noncomputable section

/-! ## Artinian rings -/

/-- Every prime ideal of a commutative Artinian ring is maximal. -/
theorem prime_isMaximal_of_artinian
    (A : Type u) [CommRing A] [IsArtinianRing A]
    {p : Ideal A} (hp : p.IsPrime) : p.IsMaximal := by
  sorry

/-! ## Flatness and prime ideals -/

/-- Flat ring maps satisfy going down for prime ideals. -/
theorem flat_ringHom_goingDown
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (hflat : RingHom.Flat f)
    {p₁ p₂ : PrimeSpectrum A} (hp : p₁ < p₂)
    (q₂ : PrimeSpectrum B)
    (hq₂ : PrimeSpectrum.comap f q₂ = p₂) :
    ∃ q₁ : PrimeSpectrum B,
      q₁ < q₂ ∧ PrimeSpectrum.comap f q₁ = p₁ := by
  sorry

/-! ## Lengths of powers of the maximal ideal -/

/-- The quotient by every power of the maximal ideal has finite length. -/
theorem power_quotient_has_finite_length
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (n : ℕ) :
    Module.length A (A ⧸ (IsLocalRing.maximalIdeal A) ^ n) < ⊤ := by
  sorry

/-! ## Dimension formula -/

/-- The height formula for a chain of primes in a universally catenary
Noetherian ring. The quotient prime is the image of `q` in `A / p`. -/
theorem universally_catenary_height_formula
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (hcat : Formalization.Books.Algebra.Unit105.IsUniversallyCatenary A)
    {p q : PrimeSpectrum A} (hpq : p ≤ q) :
    q.asIdeal.height = p.asIdeal.height +
      (Ideal.map (Ideal.Quotient.mk p.asIdeal) q.asIdeal).height := by
  sorry

/-! ## Completion -/

/-- The completion of a Noetherian local ring is complete for its maximal
ideal topology. -/
theorem noetherian_local_completion_is_adic_complete
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    IsAdicComplete (IsLocalRing.maximalIdeal A)
      (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
  sorry

/-! ## Matlis duality -/

/-- Matlis duality over an Artinian local ring identifies a finite module with
its double dual. -/
theorem matlis_double_dual_artinian_local
    (A : Type u) [CommRing A] [IsArtinianRing A] [IsLocalRing A]
    (E : ModuleCat A)
    (hE : Formalization.Books.Dualizing.Unit06.IsInjectiveHull E)
    (M : ModuleCat A) [Module.Finite A (M : Type u)] :
    Nonempty (M ≅ Formalization.Books.Dualizing.Unit06.dual E
      (Formalization.Books.Dualizing.Unit06.dual E M)) := by
  exact Formalization.Books.Dualizing.Unit06.double_dual_iso E M hE inferInstance

end

end Formalization.Books.Exercises.Unit63
