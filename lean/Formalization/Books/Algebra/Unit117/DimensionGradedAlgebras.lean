import Formalization.Books.Algebra.Unit59.NoetherianLocalRings
import Formalization.Books.Algebra.Unit62.SupportAndDimension
import Formalization.Books.Algebra.Unit114.DimensionFiniteTypeAlgebras
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.GradedAlgebra.Radical
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

/-
Proof roadmap for `dimension_graded`.

1. Unpack `hgen` as `⟨n, x, hx, hxgen⟩`.  Install
   `Algebra.FiniteType k S` from
   `Subalgebra.fg_def.mpr ⟨Set.range x, Set.finite_range x, hxgen⟩`, and then
   install `IsNoetherianRing S` with
   `Algebra.FiniteType.isNoetherianRing k S` (both APIs are in
   `Mathlib/RingTheory/FiniteType.lean`).  These instances also supply the
   noetherian instance for `R := Localization.AtPrime m` below.

2. Put `m := gradedIrrelevantIdeal 𝒜`.  Prove `hm : m.IsMaximal` with
   `Ideal.isMaximal_iff`.  The test for membership in `m` is
   `HomogeneousIdeal.mem_irrelevant_iff` from
   `Mathlib/RingTheory/GradedAlgebra/Homogeneous/Ideal.lean`.  For `z ∈ 𝒜 0`,
   rewrite `hzero` to obtain `c : k` with `algebraMap k S c = z`.  Thus an
   element outside `m` has a nonzero, hence invertible, scalar degree-zero
   part; subtracting its positive-degree part proves that every proper ideal
   above `m` is top.

3. For `p ∈ minimalPrimes S`, let `hp : p.IsPrime := p.1.1`.  The ideal
   `(p.homogeneousCore 𝒜).toIdeal` is prime by
   `Ideal.IsPrime.homogeneousCore` (in
   `Mathlib/RingTheory/GradedAlgebra/Radical.lean`) and lies below `p` by
   `Ideal.toIdeal_homogeneousCore_le`.  Apply the minimality field `p.2` to
   get equality, hence `p.IsHomogeneous 𝒜`.  Then
   `Ideal.IsHomogeneous.mem_iff` puts the degree-zero component of every
   element of `p` back in `p`; `hzero` and `hp.ne_top` force that component
   to vanish.  Conclude `p ≤ m` with
   `HomogeneousIdeal.mem_irrelevant_iff`.  Retain the conjunction of
   homogeneity and containment as `hmin`.

4. The one genuinely new bridge is the following local claim (keep it local
   to this proof unless it is useful elsewhere):

     `hHF : ∀ d : ℕ, Unit59.hilbertFunction R R d =
       gradedHilbertFunction 𝒜 d`,

   where first set `letI : m.IsMaximal := hm` (so the prime instance is
   derived) and
   `R := Localization.AtPrime m`.  Construct it in these stages.

   * Prove the standard-grading filtration formula
     `z ∈ m ^ d ↔ ∀ e < d, GradedAlgebra.proj 𝒜 e z = 0`.  The reverse
     implication uses `hxgen` and the fact `hx i ∈ 𝒜 1`; the forward
     implication uses `GradedRing.proj_apply` and graded multiplication.
     In particular every `z ∈ 𝒜 d` belongs to `m ^ d`.
   * Restrict `GradedAlgebra.proj 𝒜 d` to `m ^ d`.  The filtration formula
     identifies its kernel with `m ^ (d + 1)`, and the preceding containment
     makes it surjective onto `𝒜 d`.  Use
     `LinearMap.quotKerEquivOfSurjective` from
     `Mathlib/LinearAlgebra/Isomorphisms.lean` (after the routine
     `Submodule.quotEquivOfEq` normalization) to obtain the `k`-linear
     equivalence `m ^ d / m ^ (d + 1) ≃ₗ[k] 𝒜 d`.
   * Transport the successive quotient to `R`.  Do not define maps on
     fractions by hand: use
     `IsLocalization.AtPrime.equivQuotMaximalIdealPow m R (d + 1)` and
     `IsLocalization.AtPrime.under_maximalIdeal_pow m R`, from
     `Mathlib/RingTheory/Localization/AtPrime/Basic.lean`, and restrict the
     former equivalence to the images of the `d`-th powers.  Normalize
     `Unit59.idealPowerPiece` with `Ideal.smul_eq_mul`, `Ideal.mul_top`, and
     `IsLocalization.AtPrime.map_eq_maximalIdeal`.
   * For the length calculation, first build
     `k ≃+* S ⧸ m` from `Ideal.Quotient.mk m ∘ algebraMap k S`: injectivity
     and surjectivity are exactly `hzero` plus
     `HomogeneousIdeal.mem_irrelevant_iff`.  Compose it with
     `IsLocalization.AtPrime.equivQuotMaximalIdeal m R` to identify `k` with
     the residue field of `R`.  The power piece is killed by the maximal
     ideal, so `Unit52.dimension_is_length` (Unit52/Length.lean), followed by
     `Module.length_eq_finrank` and the two linear equivalences above, gives
     its length as `Module.finrank k (𝒜 d)`.  Taking `ENat.toNat` is precisely
     the definition of `Unit59.hilbertFunction`.

5. Let `Q := Unit59.hilbertPolynomial R R`.  From `_hP` and `hHF`, reversing
   the displayed equality in `_hP`, apply `Unit59.hilbertPolynomial_unique`
   (Unit59/NoetherianLocalRings.lean) to get `hPQ : P = Q`.

   Prove `ringKrullDim R = polynomialDegreePlusOne P` by cases on `P = 0`.
   In the zero case, `Unit59.hilbertPolynomial_spec` makes a power piece have
   length zero.  Its finite length is supplied by
   `Unit59.hilbertPowerPiece_isFiniteLength`; use
   `Module.length_eq_zero_iff` and Nakayama's lemma
   `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot` to make a power of the
   maximal ideal zero.  Then use `isArtinianRing_iff_isNilpotent_maximalIdeal`
   and `Unit60.noetherian_ringKrullDim_eq_zero_iff_artinian`.
   In the nonzero case, first show every maximal-ideal power is nonzero:
   otherwise all later Hilbert values vanish and
   `Unit59.hilbertPolynomial_unique R R 0` contradicts `hPQ`.  Apply
   `Unit59.d_eq_hilbertPolynomial_degree_add_one`, map the equality along
   `WithBot.map (fun n : ℕ => (n : ℕ∞))`, and finish with
   `Unit62.d_eq_supportDim` (Unit62/SupportAndDimension.lean) and
   `Module.supportDim_self_eq_ringKrullDim`.  A final simp using `hPQ` and
   `polynomialDegreePlusOne` handles the two `WithBot` degree types.

6. Set `ms : MaximalSpectrum S := ⟨m, hm⟩`.  The formerly reported
   global/local API gap is stale: Unit114/DimensionFiniteTypeAlgebras.lean now
   provides both
   `Unit114.ringKrullDim_eq_krullDimensionAt_of_minimalPrimes_le
      (k := k) (S := S) ms` and
   `Unit114.dimension_closed_point_finite_type_field
      (k := k) (S := S) ms`.
   Apply the first to `fun p hp => (hmin p hp).2`, then compose the second
   with the local equality from step 5.  `simpa [ms]` identifies
   `MaximalSpectrum.toPrimeSpectrum ms` with
   `⟨m, hm.isPrime⟩ : PrimeSpectrum S`.  Assemble `hm`, `hmin`, the two
   dimension equalities, and `hHF` in the nesting required by the conclusion.

Do not route step 4 through Unit58's `GradedRingData` or its `KPrimeZero`
Hilbert function.  `Unit58.sPlus_generated_iff` and
`Unit58.field_kprimeZero_length_eq_finrank` use that legacy wrapper and do not
provide a conversion from this theorem's canonical `GradedAlgebra 𝒜`; this
was the previous dead end.
-/

/--
For a finitely generated standard graded algebra over a field, the irrelevant
ideal is maximal, minimal primes are homogeneous and lie in it, the global and
local dimensions are the degree of the Hilbert polynomial plus one, and the
graded and local Hilbert functions agree.
-/
theorem dimension_graded
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Nontrivial S]
    [Algebra k S] (𝒜 : ℕ → Submodule k S) [GradedAlgebra 𝒜]
    (hzero : LinearMap.range (Algebra.linearMap k S) = 𝒜 0)
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
