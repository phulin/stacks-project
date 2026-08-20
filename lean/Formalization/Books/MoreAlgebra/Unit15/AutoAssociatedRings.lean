import Formalization.Books.Algebra.Unit66.WeaklyAssociatedPrimes
import Formalization.Books.Algebra.Unit82.UniversallyInjective
import Formalization.Books.Algebra.Unit84.TransfiniteDevissage
import Formalization.Books.Algebra.Unit88.MittagLefflerModules
import Formalization.Books.Algebra.Unit102.WhatMakesAComplexExact
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.Defs

/-!
# More on Algebra, Chapter 15: Auto-associated rings

This file records the definitions and theorem interfaces in the section
“Auto-associated rings”.  Weak association, universal injectivity, finite
generation, projectivity, and Mittag--Lefflerness use the canonical APIs from
the earlier algebra chapters.
-/

namespace Formalization.Books.MoreAlgebra.Unit15

open Formalization.Books.Algebra.Unit66
open Formalization.Books.Algebra.Unit82
open Formalization.Books.Algebra.Unit88
open scoped TensorProduct

universe u v w

noncomputable section

/-! ## Auto-associated rings -/

/-- The point of the spectrum defined by the maximal ideal of a local ring. -/
def maximalIdealPoint (R : Type u) [CommRing R] [IsLocalRing R] : PrimeSpectrum R :=
  ⟨IsLocalRing.maximalIdeal R, inferInstance⟩

/-- A ring is auto-associated when it is local and its maximal ideal is weakly
associated to the ring itself. -/
def AutoAssociated (R : Type u) [CommRing R] : Prop :=
  ∃ hR : IsLocalRing R,
    letI : IsLocalRing R := hR
    maximalIdealPoint R ∈ weaklyAssociatedPrimes R R

/-- The annihilator of an ideal is nonzero. -/
def HasPropertyP (R : Type u) [CommRing R] : Prop :=
  ∀ I : Ideal R, I ≠ ⊤ → I.FG → Module.annihilator R I ≠ ⊥

/-- Every proper finitely generated ideal in an auto-associated ring has a
nonzero annihilator. -/
theorem autoAssociated_hasPropertyP
    {R : Type u} [CommRing R] (hR : AutoAssociated R) :
    HasPropertyP R := by
  sorry

/-- The projective-module formulation of property (P). -/
def ProjectiveInjectivityCondition (R : Type u) [CommRing R] : Prop :=
  ∀ {N : Type v} {M : Type w} [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M]
    [Module.Projective R N] [Module.Projective R M]
    (u : N →ₗ[R] M), Function.Injective u → universallyInjective u

/-- For a fixed map of projective modules over a ring with property (P),
universal injectivity is equivalent to injectivity. -/
theorem universallyInjective_iff_injective_of_hasPropertyP
    {R : Type u} [CommRing R] (hP : HasPropertyP R)
    {N : Type v} {M : Type w} [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M]
    [Module.Projective R N] [Module.Projective R M]
    (u : N →ₗ[R] M) :
    universallyInjective u ↔ Function.Injective u := by
  sorry

/-- The finite-projective cokernel formulation of property (P). -/
def FiniteProjectiveCokernelCondition (R : Type u) [CommRing R] : Prop :=
  ∀ {N : Type v} {M : Type w} [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M]
    [Module.Finite R N] [Module.Projective R N]
    [Module.Finite R M] [Module.Projective R M]
    (u : N →ₗ[R] M), Function.Injective u →
      Module.Finite R (M ⧸ LinearMap.range u) ∧
        Module.Projective R (M ⧸ LinearMap.range u)

/-- The direct-summand formulation of property (P). -/
def FiniteProjectiveDirectSummandCondition (R : Type u) [CommRing R] : Prop :=
  ∀ {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (N : Submodule R M),
    Module.Finite R N → Module.Projective R N →
      IsComplemented N

/-- The split-injection formulation of property (P). -/
def FreeRankOneSplitCondition (R : Type u) [CommRing R] : Prop :=
  ∀ (n : ℕ) (u : R →ₗ[R] (Fin n → R)),
    Function.Injective u →
      ∃ g : (Fin n → R) →ₗ[R] R,
        g.comp u = LinearMap.id

/-- Property (P) is equivalent to the four finite-projective and split-map
formulations in the source lemma. -/
theorem hasPropertyP_iff_finiteProjective_conditions
    {R : Type u} [CommRing R] :
    HasPropertyP R ↔
      (ProjectiveInjectivityCondition R ∧
        FiniteProjectiveCokernelCondition R ∧
        FiniteProjectiveDirectSummandCondition R ∧
        FreeRankOneSplitCondition R) := by
  sorry

/-! ### The countable square-zero example -/

/-! The source indexes the variables and basis vectors by the positive
integers; this file uses `ℕ`, reindexing the first source index to `0`. -/

/-- The polynomial relations imposing `x_i ^ 2 = 0` for every variable. -/
def squareZeroRelations (k : Type u) [CommRing k] : Set (MvPolynomial ℕ k) :=
  Set.range (fun i : ℕ => (MvPolynomial.X i : MvPolynomial ℕ k) ^ 2)

/-- The polynomial ring `k[x_1, x_2, ...]/(x_i^2)`, with the source's positive
indices reindexed by `ℕ`. -/
abbrev squareZeroRing (k : Type u) [CommRing k] :=
  MvPolynomial ℕ k ⧸ Ideal.span (squareZeroRelations k)

/-- The image of the `i`-th polynomial variable in the square-zero ring. -/
def squareZeroVariable (k : Type u) [CommRing k] (i : ℕ) : squareZeroRing k :=
  Ideal.Quotient.mk (Ideal.span (squareZeroRelations k)) (MvPolynomial.X i)

/-- The residue map which sends every polynomial variable to zero. -/
def squareZeroResidueMap (k : Type u) [CommRing k] : squareZeroRing k →+* k :=
  Ideal.Quotient.lift (Ideal.span (squareZeroRelations k))
    (MvPolynomial.eval₂Hom (RingHom.id k) (fun _ : ℕ => 0)) (by
      change Ideal.span (squareZeroRelations k) ≤
        RingHom.ker (MvPolynomial.eval₂Hom (RingHom.id k) (fun _ : ℕ => 0))
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp)

/-- The map on the countable free module sending `e_i` to
`f_i - x_i f_(i+1)` (with the source's positive indices reindexed by `ℕ`). -/
def squareZeroMap (k : Type u) [CommRing k] :
    (ℕ →₀ squareZeroRing k) →ₗ[squareZeroRing k] (ℕ →₀ squareZeroRing k) :=
  Finsupp.linearCombination (squareZeroRing k)
    (fun i : ℕ =>
      Finsupp.single i (1 : squareZeroRing k) -
        squareZeroVariable k i • Finsupp.single (i + 1) (1 : squareZeroRing k))

/-- The finite restriction of the square-zero map. -/
def squareZeroFiniteMap (k : Type u) [CommRing k] (n : ℕ) :
    (Fin n →₀ squareZeroRing k) →ₗ[squareZeroRing k] (ℕ →₀ squareZeroRing k) :=
  Finsupp.linearCombination (squareZeroRing k)
    (fun i : Fin n =>
      Finsupp.single i.1 (1 : squareZeroRing k) -
        squareZeroVariable k i.1 • Finsupp.single (i.1 + 1) (1 : squareZeroRing k))

/-- The countable square-zero ring is auto-associated. -/
theorem squareZeroRing_autoAssociated
    (k : Type u) [Field k] :
    AutoAssociated (squareZeroRing k) := by
  sorry

/-- Every finite restriction of the displayed map is injective. -/
theorem squareZeroFiniteMap_injective
    (k : Type u) [Field k] (n : ℕ) :
    Function.Injective (squareZeroFiniteMap k n) := by
  sorry

/-- The displayed finite images are linearly independent. -/
theorem squareZeroFiniteMap_linearIndependent
    (k : Type u) [Field k] (n : ℕ) :
    LinearIndependent (squareZeroRing k)
      (fun i : Fin n =>
        Finsupp.single i.1 (1 : squareZeroRing k) -
          squareZeroVariable k i.1 •
            Finsupp.single (i.1 + 1) (1 : squareZeroRing k)) := by
  sorry

/-- The displayed map on the countable free module is injective. -/
theorem squareZeroMap_injective
    (k : Type u) [Field k] : Function.Injective (squareZeroMap k) := by
  sorry

/-- The displayed map is universally injective. -/
theorem squareZeroMap_universallyInjective
    (k : Type u) [Field k] : universallyInjective (squareZeroMap k) := by
  sorry

/-- The residue-field tensor of the displayed map is bijective; the ring map
to the coefficient field supplies the scalar restriction used for the tensor. -/
theorem squareZeroMap_residueTensor_bijective
    (k : Type u) [Field k] :
    letI : Module (squareZeroRing k) k :=
      Module.compHom k (squareZeroResidueMap k)
    Function.Bijective ((squareZeroMap k).rTensor k) := by
  sorry

/-- The displayed map is not surjective. -/
theorem squareZeroMap_not_surjective
    (k : Type u) [Field k] : ¬ Function.Surjective (squareZeroMap k) := by
  sorry

/-- The first basis vector has no preimage under the displayed map. -/
theorem squareZeroMap_firstBasis_no_preimage
    (k : Type u) [Field k] :
    ¬ ∃ x : ℕ →₀ squareZeroRing k,
      squareZeroMap k x = Finsupp.single 0 (1 : squareZeroRing k) := by
  sorry

/-- A splitting of the displayed map would make it surjective. -/
theorem squareZeroMap_split_implies_surjective
    (k : Type u) [Field k]
    (g : (ℕ →₀ squareZeroRing k) →ₗ[squareZeroRing k] (ℕ →₀ squareZeroRing k))
    (hg : g.comp (squareZeroMap k) = LinearMap.id) :
    Function.Surjective (squareZeroMap k) := by
  sorry

/-- The cokernel of the displayed map is flat, countably generated, and not
projective; consequently it is not Mittag--Leffler. -/
theorem squareZeroMap_cokernel_properties
    (k : Type u) [Field k] :
    Module.Flat (squareZeroRing k)
        ((ℕ →₀ squareZeroRing k) ⧸ LinearMap.range (squareZeroMap k)) ∧
      Formalization.Books.Algebra.Unit84.Module.IsCountablyGenerated
        (squareZeroRing k)
        ((ℕ →₀ squareZeroRing k) ⧸ LinearMap.range (squareZeroMap k)) ∧
      ¬ Module.Projective (squareZeroRing k)
        ((ℕ →₀ squareZeroRing k) ⧸ LinearMap.range (squareZeroMap k)) ∧
      ¬ IsMittagLefflerModule
        (ModuleCat.of (squareZeroRing k)
          ((ℕ →₀ squareZeroRing k) ⧸ LinearMap.range (squareZeroMap k))) := by
  sorry

/-! ### Maps of finite free modules -/

/-- For a map of finite free modules, injectivity is equivalent to full rank
and zero annihilator of its determinantal ideal. -/
theorem exactLengthOne_iff
    {R : Type u} [CommRing R] [IsLocalRing R] {m n : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    Function.Injective φ ↔
      Formalization.Books.Algebra.Unit102.rank φ = m ∧
        Module.annihilator R
            (Formalization.Books.Algebra.Unit102.rankIdeal φ) = ⊥ := by
  sorry

/-- In the Noetherian local case, the nonzerodivisor formulation is equivalent
to the two preceding formulations. -/
theorem exactLengthOne_noetherian_tfae
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {m n : ℕ} (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    List.TFAE [
      Function.Injective φ,
      Formalization.Books.Algebra.Unit102.rank φ = m ∧
        Module.annihilator R
            (Formalization.Books.Algebra.Unit102.rankIdeal φ) = ⊥,
      Formalization.Books.Algebra.Unit102.rank φ = m ∧
        (Formalization.Books.Algebra.Unit102.rankIdeal φ = ⊤ ∨
          ∃ x : R, x ∈ Formalization.Books.Algebra.Unit102.rankIdeal φ ∧
            x ∈ nonZeroDivisors R)] := by
  sorry

/-- The dual of the cokernel of an injective endomorphism of a finite free
module is zero. -/
theorem coker_injective_free_dual_eq_zero
    {R : Type u} [CommRing R] {n : ℕ}
    (φ : (Fin n → R) →ₗ[R] (Fin n → R)) (hφ : Function.Injective φ) :
    ∀ f : ((Fin n → R) ⧸ LinearMap.range φ) →ₗ[R] R, f = 0 := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit15
