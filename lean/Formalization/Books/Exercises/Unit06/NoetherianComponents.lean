import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.NoetherianSpace

import Formalization.Books.Exercises.Unit06.Irreducibility

/-!
# Exercises, Chapter 6: Noetherian spaces and irreducible components

`NoetherianSpace` and `irreducibleComponents` are Mathlib's canonical
interfaces.  The source's optional Artinian terminology is recorded by the
dual well-foundedness predicate on closed sets.
-/

noncomputable section

universe u

open Set Topology TopologicalSpace

namespace Formalization.Books.Exercises.Unit06

/-! ## Noetherian and Artinian spaces -/

/-- The source's descending-closed-set definition of a Noetherian space. -/
theorem noetherian_space_iff_descending_closed {X : Type u} [TopologicalSpace X] :
    NoetherianSpace X ↔ WellFoundedLT (TopologicalSpace.Closeds X) :=
  (noetherianSpace_TFAE X).out 0 1

/-- The source's Artinian condition: increasing chains of closed sets
stabilize. -/
abbrev ArtinianSpace (X : Type u) [TopologicalSpace X] : Prop :=
  WellFoundedGT (TopologicalSpace.Closeds X)

/-- A Noetherian ring has a Noetherian prime spectrum. -/
theorem spectrum_noetherian_of_noetherian_ring {A : Type u} [CommRing A]
    [IsNoetherianRing A] :
    NoetherianSpace (PrimeSpectrum A) := by
  infer_instance

/-- The converse fails for an infinite square-zero extension of a field: its
spectrum is a one-point-type spectrum while its square-zero ideal is not
finitely generated. -/
abbrev infiniteSquareZeroRing : Type :=
  TrivSqZeroExt ℚ (ℕ → ℚ)

theorem noetherian_spectrum_not_noetherian_ring_example :
    NoetherianSpace (PrimeSpectrum infiniteSquareZeroRing) ∧
      ¬ IsNoetherianRing infiniteSquareZeroRing := by
  sorry

/-! ## Irreducible components -/

/-- Every irreducible subset is contained in a maximal irreducible subset. -/
theorem irreducible_subset_contained_in_component {X : Type u} [TopologicalSpace X]
    (T : Set X) (hT : IsIrreducible T) :
    ∃ C ∈ irreducibleComponents X, T ⊆ C := by
  exact exists_mem_irreducibleComponents_subset_of_isIrreducible T hT

/-- Every irreducible component is closed. -/
theorem irreducible_component_is_closed {X : Type u} [TopologicalSpace X]
    {C : Set X} (hC : C ∈ irreducibleComponents X) :
    IsClosed C := by
  exact isClosed_of_mem_irreducibleComponents C hC

/-- Irreducible components cover every topological space. -/
theorem irreducible_components_cover {X : Type u} [TopologicalSpace X] :
    ⋃₀ irreducibleComponents X = (Set.univ : Set X) := by
  exact sUnion_irreducibleComponents

/-- A Noetherian space has finitely many irreducible components, and they
cover the space. -/
theorem noetherian_finite_irreducible_components {X : Type u} [TopologicalSpace X]
    [NoetherianSpace X] :
    (irreducibleComponents X).Finite ∧
      ⋃₀ irreducibleComponents X = (Set.univ : Set X) := by
  exact ⟨NoetherianSpace.finite_irreducibleComponents,
    sUnion_irreducibleComponents⟩

/-- In the usual topology on `ℝ`, the irreducible components are the one-point
subsets. -/
theorem real_irreducible_components_are_singletons :
    irreducibleComponents ℝ = {C : Set ℝ | ∃ x : ℝ, C = {x}} := by
  sorry

/-! ## Components and minimal primes -/

/-- Irreducible components of an affine spectrum correspond to minimal
prime ideals. -/
noncomputable def spectrum_irreducible_components_minimal_primes_equiv
    {A : Type u} [CommRing A] :
    minimalPrimes A ≃o
      (irreducibleComponents (PrimeSpectrum A))ᵒᵈ :=
  minimalPrimes.equivIrreducibleComponents A

end Formalization.Books.Exercises.Unit06
