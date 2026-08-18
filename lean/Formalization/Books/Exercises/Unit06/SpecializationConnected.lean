import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Topology.Connected.Basic

/-!
# Exercises, Chapter 6: Specialization and connected components

The source's closed-point, specialization/generalization, connectedness, and
connected-component notions are expressed with Mathlib's canonical topology
predicates and the prime-spectrum order API.
-/

noncomputable section

universe u

open Set Topology TopologicalSpace

namespace Formalization.Books.Exercises.Unit06

/-! ## Closed points and specialization -/

/-- A point is closed exactly when its singleton is closed. -/
theorem closed_point_iff_closed_singleton {X : Type u} [TopologicalSpace X] (x : X) :
    closure ({x} : Set X) = {x} ↔ IsClosed ({x} : Set X) := by
  constructor
  · intro h
    rw [← h]
    exact isClosed_closure
  · intro h
    exact h.closure_eq

/-- Closed points of an affine spectrum correspond to maximal ideals. -/
theorem spectrum_closed_point_iff_maximal {A : Type u} [CommRing A]
    (p : PrimeSpectrum A) :
    IsClosed ({p} : Set (PrimeSpectrum A)) ↔ p.asIdeal.IsMaximal := by
  exact PrimeSpectrum.isClosed_singleton_iff_isMaximal p

/-- In the spectrum, specialization/generalization is inclusion of prime
ideals.  The displayed relation is oriented as `p` generalizing `q`. -/
theorem spectrum_generalization_iff_ideal_inclusion {A : Type u} [CommRing A]
    (p q : PrimeSpectrum A) :
    p ⤳ q ↔ p.asIdeal ≤ q.asIdeal := by
  exact (PrimeSpectrum.le_iff_specializes p q).symm

/-- A prime is closed exactly when it has no proper specialization. -/
theorem spectrum_closed_point_iff_no_proper_specialization {A : Type u} [CommRing A]
    (p : PrimeSpectrum A) :
    IsClosed ({p} : Set (PrimeSpectrum A)) ↔
      ∀ q : PrimeSpectrum A, p ⤳ q → q = p := by
  sorry

/-- Maximal ideals are the primes with no proper specialization. -/
theorem spectrum_maximal_iff_no_proper_specialization {A : Type u} [CommRing A]
    (p : PrimeSpectrum A) :
    p.asIdeal.IsMaximal ↔
      ∀ q : PrimeSpectrum A, p ⤳ q → q = p := by
  sorry

/-- Minimal primes are exactly the points with no proper generalization. -/
theorem spectrum_minimal_prime_iff_no_proper_generalization {A : Type u} [CommRing A]
    (p : PrimeSpectrum A) :
    p.asIdeal ∈ minimalPrimes A ↔
      ∀ q : PrimeSpectrum A, q ⤳ p → q = p := by
  sorry

/-- A generic point of a reducible spectrum is a generic point of one of its
irreducible components, exactly at a minimal prime. -/
theorem spectrum_generic_point_iff_minimal_prime {A : Type u} [CommRing A]
    (p : PrimeSpectrum A) :
    p.asIdeal ∈ minimalPrimes A ↔
      ∃ C : Set (PrimeSpectrum A),
        C ∈ irreducibleComponents (PrimeSpectrum A) ∧
          IsGenericPoint p C := by
  sorry

/-! ## Disjoint closed subsets -/

/-- Two vanishing sets are disjoint exactly when the sum of their ideals is
the unit ideal. -/
theorem zeroLocus_disjoint_iff_sup_eq_top {A : Type u} [CommRing A]
    (I J : Ideal A) :
    Disjoint (PrimeSpectrum.zeroLocus (I : Set A))
      (PrimeSpectrum.zeroLocus (J : Set A)) ↔ I ⊔ J = ⊤ := by
  sorry

/-! ## Connected spaces and components -/

/-- The source's connected-space definition is the canonical `ConnectedSpace`
class, equivalently connectedness of the whole space. -/
theorem connected_space_iff_connected_univ {X : Type u} [TopologicalSpace X] :
    ConnectedSpace X ↔ IsConnected (Set.univ : Set X) := by
  sorry

/-- For a nonzero ring, disconnectedness of the spectrum is equivalent to a
nontrivial product decomposition of the ring. -/
theorem spectrum_disconnected_iff_product {A : Type u} [CommRing A] [Nontrivial A] :
    ¬ ConnectedSpace (PrimeSpectrum A) ↔
      ∃ (B C : Type u) (_ : CommRing B) (_ : CommRing C),
        Nontrivial B ∧ Nontrivial C ∧ Nonempty (A ≃+* B × C) := by
  sorry

/-- Mathlib's `connectedComponent` contains its defining point, is connected,
and is closed. -/
theorem connected_component_basic_properties {X : Type u} [TopologicalSpace X] (x : X) :
    x ∈ connectedComponent x ∧
      IsConnected (connectedComponent x) ∧
        IsClosed (connectedComponent x) := by
  exact ⟨mem_connectedComponent, isConnected_connectedComponent,
    isClosed_connectedComponent⟩

/-- The canonical connected component is maximal among connected subsets that
contain its point. -/
theorem connected_component_is_maximal {X : Type u} [TopologicalSpace X] (x : X)
    {T : Set X} (hT : IsConnected T) (hx : x ∈ T) :
    T ⊆ connectedComponent x := by
  exact hT.subset_connectedComponent hx

/-! ## Stability and the infinite-product warning -/

/-- Connected components of an affine spectrum are stable under
generalization. -/
theorem spectrum_connected_component_stable_under_generalization
    {A : Type u} [CommRing A] (x : PrimeSpectrum A) :
    StableUnderGeneralization (connectedComponent x) := by
  sorry

/-- For a Noetherian ring, connected components of the spectrum are open. -/
theorem spectrum_connected_component_is_open_of_noetherian
    {A : Type u} [CommRing A] [IsNoetherianRing A] (x : PrimeSpectrum A) :
    IsOpen (connectedComponent x) := by
  sorry

/-- The infinite product of copies of `𝔽₂` used in the source warning. -/
abbrev infiniteBooleanProductRing : Type := ℕ → ZMod 2

/-- This infinite product has infinitely many points, all of which are
closed; it is the source's counterexample to openness of components without
Noetherian hypotheses. -/
theorem infinite_boolean_product_spectrum_warning :
    Infinite (PrimeSpectrum infiniteBooleanProductRing) ∧
      ∀ p : PrimeSpectrum infiniteBooleanProductRing,
        IsClosed ({p} : Set (PrimeSpectrum infiniteBooleanProductRing)) := by
  sorry

/-- The same infinite product has a connected component which is not open,
so the Noetherian openness conclusion cannot be extended to arbitrary rings. -/
theorem infinite_boolean_product_has_nonopen_connected_component :
    ∃ p : PrimeSpectrum infiniteBooleanProductRing,
      connectedComponent p = {p} ∧
        ¬ IsOpen (connectedComponent p) := by
  sorry

end Formalization.Books.Exercises.Unit06
