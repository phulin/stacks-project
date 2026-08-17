import Formalization.Books.Algebra.Unit59.NoetherianLocalRings
import Formalization.Books.Algebra.Unit114.DimensionFiniteTypeAlgebras
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Commutative Algebra, Chapter 117: Dimension of graded algebras over a field

The graded algebra is Mathlib's canonical `GradedAlgebra` on a family of
`k`-submodules.  The source-facing Hilbert function records the dimensions of
the homogeneous pieces, while the local Hilbert function is the one from
Chapter 59 applied to the localization at the irrelevant ideal.
-/

namespace Formalization.Books.Algebra.Unit117

open Set
open Formalization.Books.Topology.Unit10

universe u v

noncomputable section

/-! ## Source-facing graded-algebra interfaces -/

/-- The irrelevant ideal of a graded algebra, viewed through the ordinary ideal API. -/
abbrev gradedIrrelevantIdeal
    {k : Type u} {S : Type v} [CommSemiring k] [Semiring S]
    [Algebra k S] (𝒜 : ℕ → Submodule k S) [GradedAlgebra 𝒜] : Ideal S :=
  (HomogeneousIdeal.irrelevant 𝒜).toIdeal

/-- The Hilbert function of a graded algebra over a field. -/
def gradedHilbertFunction
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    (𝒜 : ℕ → Submodule k S) : ℕ → ℕ :=
  fun d => Module.finrank k (𝒜 d)

/-- Eventual agreement of the graded Hilbert function with a rational polynomial. -/
def IsGradedHilbertPolynomial
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    (𝒜 : ℕ → Submodule k S) (P : Polynomial ℚ) : Prop :=
  ∀ᶠ d : ℕ in Filter.atTop,
    (gradedHilbertFunction 𝒜 d : ℚ) = P.eval (d : ℚ)

/-- The source's finite-generation hypothesis in degree one. -/
def IsGeneratedInDegreeOne
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    (𝒜 : ℕ → Submodule k S) [GradedAlgebra 𝒜] : Prop :=
  ∃ n : ℕ, ∃ x : Fin n → S,
    (∀ i, x i ∈ 𝒜 1) ∧ Algebra.adjoin k (Set.range x) = ⊤

/-- The dimension contribution of a rational polynomial, with `deg 0 = -1`.

The zero branch makes `deg(P) + 1` equal to zero when `P = 0`, as in the
source convention; nonzero degrees are transported to Mathlib's
`WithBot ℕ∞` dimension type.
-/
def polynomialDegreePlusOne (P : Polynomial ℚ) : WithBot ℕ∞ :=
  if _hP : P = 0 then 0
  else WithBot.map (fun n : ℕ => (n : ℕ∞)) P.degree + 1

/-! ## Dimension of a standard graded algebra -/

/--
For a finitely generated standard graded algebra over a field, the irrelevant
ideal is maximal, minimal primes are homogeneous and lie in it, the global and
local dimensions are the degree of the Hilbert polynomial plus one, and the
graded and local Hilbert functions agree.
-/
theorem dimension_graded
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Nontrivial S]
    [Algebra k S] (𝒜 : ℕ → Submodule k S) [GradedAlgebra 𝒜]
    (hzero : (Set.range (algebraMap k S) : Set S) = (𝒜 0 : Set S))
    (hgen : IsGeneratedInDegreeOne 𝒜)
    (P : Polynomial ℚ) (_hP : IsGradedHilbertPolynomial 𝒜 P) :
    let m : Ideal S := gradedIrrelevantIdeal 𝒜
    ∃ hm : m.IsMaximal,
      (∀ p : Ideal S, p ∈ minimalPrimes S →
        p.IsHomogeneous 𝒜 ∧ p ≤ m) ∧
        ((ringKrullDim S = polynomialDegreePlusOne P) ∧
          (let x : PrimeSpectrum S := ⟨m, hm.isPrime⟩;
            polynomialDegreePlusOne P = krullDimensionAt x)) ∧
        (letI : m.IsPrime := hm.isPrime
          ∀ d : ℕ,
            Formalization.Books.Algebra.Unit59.hilbertFunction
                (Localization.AtPrime m) (Localization.AtPrime m) d =
              gradedHilbertFunction 𝒜 d) := by
  sorry

end

end Formalization.Books.Algebra.Unit117
