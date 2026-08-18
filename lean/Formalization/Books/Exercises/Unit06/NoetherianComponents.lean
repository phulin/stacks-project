import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.StdBasis
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
  let K : Ideal infiniteSquareZeroRing :=
    TrivSqZeroExt.kerIdeal ℚ (ℕ → ℚ)
  have hK_le (p : PrimeSpectrum infiniteSquareZeroRing) :
      K ≤ p.asIdeal := by
    intro x hx
    apply p.2.mem_of_pow_mem 2
    have hxpow : x ^ 2 ∈ K ^ 2 := Ideal.pow_mem_pow hx 2
    change x ^ 2 ∈ (TrivSqZeroExt.kerIdeal ℚ (ℕ → ℚ)) ^ 2 at hxpow
    rw [TrivSqZeroExt.kerIdeal_sq] at hxpow
    have hxzero : x ^ 2 = 0 := by simpa using hxpow
    rw [hxzero]
    exact p.asIdeal.zero_mem
  have hIdeal (p : PrimeSpectrum infiniteSquareZeroRing) :
      p.asIdeal = K := by
    apply le_antisymm
    · intro x hx
      by_contra hnot
      have hfst : x.fst ≠ 0 := by
        intro hzero
        apply hnot
        change x.fst = 0
        exact hzero
      have hunit : IsUnit x :=
        (TrivSqZeroExt.isUnit_iff_isUnit_fst).mpr (isUnit_iff_ne_zero.mpr hfst)
      exact (p.2.ne_top (p.asIdeal.eq_top_of_isUnit_mem hx hunit)).elim
    · exact hK_le p
  have hsub : Subsingleton (PrimeSpectrum infiniteSquareZeroRing) := by
    constructor
    intro p q
    apply PrimeSpectrum.ext
    rw [hIdeal p, hIdeal q]
  constructor
  · have hfin : Finite (PrimeSpectrum infiniteSquareZeroRing) :=
      Finite.of_injective (fun _ : PrimeSpectrum infiniteSquareZeroRing => ())
        (fun p q _ => hsub.elim p q)
    exact @Finite.to_noetherianSpace (PrimeSpectrum infiniteSquareZeroRing) _ hfin
  · intro hN
    have hfg : K.FG := (isNoetherianRing_iff_ideal_fg infiniteSquareZeroRing).mp hN K
    rcases hfg with ⟨S, hS⟩
    let V : Submodule ℚ (ℕ → ℚ) :=
      Submodule.span ℚ
        ((fun x : infiniteSquareZeroRing => x.snd) '' (↑S : Set infiniteSquareZeroRing))
    have hspan : ∀ (x : infiniteSquareZeroRing),
        x ∈ Ideal.span (↑S : Set infiniteSquareZeroRing) →
          x ∈ K ∧ x.snd ∈ V := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
          refine ⟨hS ▸ Ideal.subset_span hx, ?_⟩
          apply Submodule.subset_span
          exact ⟨x, hx, rfl⟩
      | zero =>
          exact ⟨K.zero_mem, by simp [V]⟩
      | add x y hx hy hx' hy' =>
          exact ⟨K.add_mem hx'.1 hy'.1,
            by simpa [V] using V.add_mem hx'.2 hy'.2⟩
      | smul a x hx hx' =>
          have hxK : x ∈ K := hx'.1
          have hxsnd : x.snd ∈ V := hx'.2
          have hxfst : x.fst = 0 := by
            change x.fst = 0 at hxK
            exact hxK
          refine ⟨K.mul_mem_left a hxK, ?_⟩
          change (a * x).snd ∈ V
          simpa [TrivSqZeroExt.snd_mul, hxfst] using V.smul_mem a.fst hxsnd
    have htop : V = ⊤ := by
      apply top_unique
      intro m _
      have hmK : TrivSqZeroExt.inr m ∈ K := by
        change (TrivSqZeroExt.inr m).fst = 0
        simp
      have hmspan := hspan (TrivSqZeroExt.inr m) (hS.symm ▸ hmK)
      simpa [V] using hmspan.2
    have hVfg : V.FG := by
      apply Submodule.fg_span
      exact S.finite_toSet.image _
    have hfd : FiniteDimensional ℚ (ℕ → ℚ) := ⟨htop ▸ hVfg⟩
    have hli : LinearIndependent ℚ (fun n : ℕ => Pi.single n (1 : ℚ)) :=
      Pi.linearIndependent_single_one ℕ ℚ
    have hcard : Cardinal.mk ℕ < Cardinal.aleph0 :=
      @LinearIndependent.lt_aleph0_of_finiteDimensional ℚ (ℕ → ℚ) _ _ _ ℕ hfd _ hli
    rw [Cardinal.mk_nat] at hcard
    exact (lt_irrefl _ hcard)

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
  ext C
  constructor
  · intro hC
    exact isIrreducible_iff_singleton.mp hC.1
  · rintro ⟨x, rfl⟩
    refine ⟨isIrreducible_singleton, ?_⟩
    intro S hS hsubset
    obtain ⟨y, rfl⟩ := isIrreducible_iff_singleton.mp hS
    have hxy : x = y := by simpa using hsubset
    subst y
    exact subset_rfl

/-! ## Components and minimal primes -/

/-- Irreducible components of an affine spectrum correspond to minimal
prime ideals. -/
noncomputable def spectrum_irreducible_components_minimal_primes_equiv
    {A : Type u} [CommRing A] :
    minimalPrimes A ≃o
      (irreducibleComponents (PrimeSpectrum A))ᵒᵈ :=
  minimalPrimes.equivIrreducibleComponents A

end Formalization.Books.Exercises.Unit06
