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

/-! ## Powers of the irrelevant ideal -/

/-- Multiplicativity of ideal-power membership. -/
theorem mul_mem_pow_pow {R : Type*} [CommRing R] (I : Ideal R) {a b : R} {r s : ℕ}
    (ha : a ∈ I ^ r) (hb : b ∈ I ^ s) : a * b ∈ I ^ (r + s) := by
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    simpa using Ideal.mul_mem_right b (I := I ^ r) ha
  · rw [Submodule.pow_add I hs.ne']
    exact Ideal.mul_mem_mul ha hb

section IrrelevantPowers

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Nontrivial S]
  [Algebra k S] (𝒜 : ℕ → Submodule k S) [GradedAlgebra 𝒜]

theorem mem_irrelevant_iff_proj (z : S) :
    z ∈ gradedIrrelevantIdeal 𝒜 ↔ GradedRing.proj 𝒜 0 z = 0 :=
  HomogeneousIdeal.mem_irrelevant_iff 𝒜 z

theorem pow_mem_degree {j : ℕ} {y : S} (hy : y ∈ 𝒜 j) :
    ∀ r : ℕ, y ^ r ∈ 𝒜 (j * r) := by
  intro r
  induction r with
  | zero => simpa using SetLike.GradedOne.one_mem
  | succ r ih =>
    rw [pow_succ, Nat.mul_succ]
    exact SetLike.GradedMul.mul_mem ih hy

/-- The image of a monomial in the degree-one generators is graded of the
monomial degree and lies in the corresponding power of the irrelevant ideal. -/
theorem monomialGenerator_prod_mem {n : ℕ} {x : Fin n → S}
    (hx : ∀ i, x i ∈ 𝒜 1) (d : Fin n →₀ ℕ) :
    d.prod (fun i t => x i ^ t) ∈ 𝒜 (d.sum fun _ t => t) ∧
      d.prod (fun i t => x i ^ t) ∈ gradedIrrelevantIdeal 𝒜 ^ (d.sum fun _ t => t) := by
  classical
  induction d using Finsupp.induction_linear with
  | zero =>
    constructor
    · simpa using SetLike.GradedOne.one_mem
    · simp
  | single a r =>
    by_cases hr : r = 0
    · subst hr
      constructor
      · simpa using SetLike.GradedOne.one_mem
      · simp
    · have hxm : x a ∈ gradedIrrelevantIdeal 𝒜 := by
        have hp0 : GradedRing.proj 𝒜 0 (x a) = 0 := by
          rw [GradedRing.proj_apply, DirectSum.decompose_of_mem _ (hx a),
            DirectSum.of_apply]
          simp
        rw [mem_irrelevant_iff_proj]
        exact hp0
      have h1 : (Finsupp.single a r).sum (fun _ t => t) = r := by simp [hr]
      have h2 : (Finsupp.single a r).prod (fun i t => x i ^ t) = x a ^ r := by
        simp [hr]
      rw [h1, h2]
      have hpow := pow_mem_degree (𝒜 := 𝒜) (hx a) r
      rw [one_mul] at hpow
      exact ⟨hpow, Ideal.pow_mem_pow hxm r⟩
  | add f g ihf ihg =>
    have h1 : (f + g).prod (fun i t => x i ^ t)
        = f.prod (fun i t => x i ^ t) * g.prod (fun i t => x i ^ t) :=
      Finsupp.prod_add_index' (by intro i; simp)
        (by intro i u v; exact pow_add (x i) u v)
    have h2 : (f + g).sum (fun _ t => t)
        = f.sum (fun _ t => t) + g.sum (fun _ t => t) := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
    rw [h1, h2]
    exact ⟨SetLike.GradedMul.mul_mem ihf.1 ihg.1,
      mul_mem_pow_pow _ ihf.2 ihg.2⟩



/-- The degree of a monomial index is the sum of its entries. -/
theorem degree_eq_sumSupport {n : ℕ} (d : Fin n →₀ ℕ) :
    Finsupp.degree d = ∑ i ∈ d.support, d i :=
  Finsupp.degree_apply d

/-- Projections commute with evaluation of polynomials in the degree-one
generators, picking out the homogeneous component. -/
theorem proj_aeval_monomialGenerator {n : ℕ} {x : Fin n → S}
    (hx : ∀ i, x i ∈ 𝒜 1) (p : MvPolynomial (Fin n) k) (e : ℕ) :
    GradedRing.proj 𝒜 e (MvPolynomial.aeval x p)
      = MvPolynomial.aeval x (MvPolynomial.homogeneousComponent e p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    by_cases hc0 : c = 0
    · subst hc0
      rw [show MvPolynomial.monomial d (0:k) = 0 from MvPolynomial.monomial_zero,
        map_zero, map_zero, MvPolynomial.homogeneousComponent_apply,
        MvPolynomial.support_zero, Finset.filter_empty, Finset.sum_empty,
        map_zero]
    · have hsupp : (MvPolynomial.monomial d c).support = {d} := by
        rw [MvPolynomial.support_monomial, if_neg hc0]
      have hcoef : MvPolynomial.coeff d (MvPolynomial.monomial d c) = c := by
        simp
      by_cases hdeg : Finsupp.degree d = e
      · have hD : d.prod (fun i t => x i ^ t)
            ∈ gradedIrrelevantIdeal 𝒜 ^ (∑ i ∈ d.support, d i) :=
          (monomialGenerator_prod_mem 𝒜 hx d).2
        have key : (∑ i ∈ d.support, d i) = e := by
          rw [← degree_eq_sumSupport]
          exact hdeg
        rw [key] at hD
        have heq : MvPolynomial.aeval x (MvPolynomial.monomial d c) ∈ 𝒜 e := by
          have hD1 : d.prod (fun i t => x i ^ t) ∈ 𝒜 (∑ i ∈ d.support, d i) :=
            (monomialGenerator_prod_mem 𝒜 hx d).1
          rw [← degree_eq_sumSupport, hdeg] at hD1
          rw [MvPolynomial.aeval_monomial, ← Algebra.smul_def]
          exact Submodule.smul_mem _ _ hD1
        have hu : GradedRing.proj 𝒜 e (MvPolynomial.aeval x (MvPolynomial.monomial d c))
            = MvPolynomial.aeval x (MvPolynomial.monomial d c) := by
          rw [GradedRing.proj_apply, DirectSum.decompose_of_mem _ heq]
          simp [hdeg]
        have hfilter : ((MvPolynomial.monomial d c).support.filter
            fun d' => Finsupp.degree d' = e) = {d} := by
          simp [hsupp, hdeg]
        rw [MvPolynomial.homogeneousComponent_apply, hfilter,
          Finset.sum_singleton, hcoef, hu]
      · have hD : d.prod (fun i t => x i ^ t) ∈ 𝒜 (∑ i ∈ d.support, d i) :=
          (monomialGenerator_prod_mem 𝒜 hx d).1
        have heq : MvPolynomial.aeval x (MvPolynomial.monomial d c)
            ∈ 𝒜 (Finsupp.degree d) := by
          rw [MvPolynomial.aeval_monomial, degree_eq_sumSupport, ← Algebra.smul_def]
          exact Submodule.smul_mem _ _ hD
        have hu : GradedRing.proj 𝒜 e (MvPolynomial.aeval x (MvPolynomial.monomial d c))
            = 0 := by
          rw [GradedRing.proj_apply, DirectSum.decompose_of_mem _ heq,
            DirectSum.of_apply, dif_neg hdeg]
          rfl
        have hfilter : ((MvPolynomial.monomial d c).support.filter
            fun d' => Finsupp.degree d' = e) = ∅ := by
          simp [hsupp, hdeg]
        rw [MvPolynomial.homogeneousComponent_apply, hfilter,
          Finset.sum_empty, map_zero]
        exact hu
  | add p q ihp ihq =>
    rw [map_add, map_add, map_add, map_add, ihp, ihq]

/-- Every homogeneous element of positive degree lies in the corresponding
power of the irrelevant ideal. -/
theorem homogeneous_mem_pow_irrelevant {n : ℕ} {x : Fin n → S}
    (hx : ∀ i, x i ∈ 𝒜 1)
    (hxgen : Algebra.adjoin k (Set.range x) = ⊤)
    {e : ℕ} (he : 0 < e) :
    ∀ y ∈ 𝒜 e, y ∈ gradedIrrelevantIdeal 𝒜 ^ e := by
  intro y hy
  have hyad : y ∈ Algebra.adjoin k (Set.range x) := by
    rw [hxgen]
    trivial
  rw [Algebra.adjoin_range_eq_range_aeval] at hyad
  obtain ⟨p, hp⟩ := hyad
  have hp' : MvPolynomial.aeval x p = y := hp
  have hpe : GradedRing.proj 𝒜 e (MvPolynomial.aeval x p)
      = MvPolynomial.aeval x p := by
    rw [hp', GradedRing.proj_apply, DirectSum.decompose_of_mem _ hy,
      DirectSum.of_apply]
    simp
  rw [← hp', ← hpe, proj_aeval_monomialGenerator 𝒜 hx p e,
    MvPolynomial.homogeneousComponent_apply, map_sum]
  refine Ideal.sum_mem _ fun d hd => ?_
  simp only [Finset.mem_filter, MvPolynomial.mem_support_iff] at hd
  obtain ⟨-, hdeg⟩ := hd
  have hdegS : (∑ i ∈ d.support, d i) = e := by
    rw [← degree_eq_sumSupport]
    exact hdeg
  have hcc : MvPolynomial.coeff d (MvPolynomial.homogeneousComponent e p)
      = MvPolynomial.coeff d p := by
    rw [MvPolynomial.coeff_homogeneousComponent, if_pos hdeg]
  have hD : d.prod (fun i t => x i ^ t)
      ∈ gradedIrrelevantIdeal 𝒜 ^ (∑ i ∈ d.support, d i) :=
    (monomialGenerator_prod_mem 𝒜 hx d).2
  rw [hdegS] at hD
  rw [MvPolynomial.aeval_monomial]
  exact Ideal.mul_mem_left (gradedIrrelevantIdeal 𝒜 ^ e) _ hD

end IrrelevantPowers

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
  classical
  obtain ⟨n, x, hx, hxgen⟩ := hgen
  haveI hft : Algebra.FiniteType k S :=
    ⟨Subalgebra.fg_def.mpr ⟨Set.range x, Set.finite_range x, hxgen⟩⟩
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  set m : Ideal S := gradedIrrelevantIdeal 𝒜 with hmdef
  have hmem : ∀ z : S, z ∈ m ↔ GradedRing.proj 𝒜 0 z = 0 := fun z => by
    rw [hmdef]
    exact HomogeneousIdeal.mem_irrelevant_iff 𝒜 z
  have hp0mem : ∀ (z : S) (i : ℕ), GradedRing.proj 𝒜 i z ∈ 𝒜 i := by
    intro z i
    rw [GradedRing.proj_apply]
    exact SetLike.coe_mem _
  have hproj0 : ∀ w : S, w ∈ 𝒜 0 → GradedRing.proj 𝒜 0 w = w := by
    intro w hw
    rw [GradedRing.proj_apply, DirectSum.decompose_of_mem _ hw, DirectSum.of_eq_same]
  have hprojmul : ∀ a b : S, GradedRing.proj 𝒜 0 (a * b) =
      GradedRing.proj 𝒜 0 a * GradedRing.proj 𝒜 0 b := fun a b =>
    map_mul (GradedRing.projZeroRingHom 𝒜) a b
  have hprojone : GradedRing.proj 𝒜 0 (1 : S) = 1 :=
    map_one (GradedRing.projZeroRingHom 𝒜)
  have hprojscaledge : ∀ c : k,
      GradedRing.proj 𝒜 0 (algebraMap k S c) = algebraMap k S c := by
    intro c
    refine hproj0 _ ?_
    rw [← hzero]
    exact LinearMap.mem_range.mpr ⟨c, rfl⟩
  -- Step 2: the irrelevant ideal is maximal.
  have hmax : m.IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨?_, ?_⟩
    · intro h1
      rw [hmem, hprojone] at h1
      exact one_ne_zero h1
    · intro J x hJx hxm hxJ
      have hpz : GradedRing.proj 𝒜 0 x ≠ 0 := fun h => hxm ((hmem x).mpr h)
      obtain ⟨c, hc⟩ : ∃ c : k, algebraMap k S c = GradedRing.proj 𝒜 0 x := by
        have hIn : GradedRing.proj 𝒜 0 x ∈ 𝒜 0 := hp0mem x 0
        rw [← hzero] at hIn
        exact LinearMap.mem_range.mp hIn
      have hcne : c ≠ 0 := by
        intro h; rw [h, map_zero] at hc; exact hpz hc.symm
      have h1m : 1 - x * algebraMap k S c⁻¹ ∈ m := by
        rw [hmem, map_sub, hprojmul, hprojscaledge c⁻¹, ← hc, hprojone,
          ← map_mul, mul_inv_cancel₀ hcne, map_one, sub_self]
      have h2 : x * algebraMap k S c⁻¹ ∈ J :=
        Ideal.mul_mem_right (algebraMap k S c⁻¹) J hxJ
      have h3 : 1 - x * algebraMap k S c⁻¹ ∈ J := hJx h1m
      have h4 : (1:S) = (1 - x * algebraMap k S c⁻¹) + x * algebraMap k S c⁻¹ := by
        ring
      rw [h4]
      exact add_mem h3 h2
  refine ⟨hmax, ?_, ?_, ?_⟩
  · -- Step 3: minimal primes are homogeneous and contained in m.
    intro p hp
    rw [minimalPrimes_eq_minimals, Set.mem_setOf_eq] at hp
    obtain ⟨hpp, hminp⟩ := hp
    have hcorele : (p.homogeneousCore 𝒜).toIdeal ≤ p :=
      Ideal.toIdeal_homogeneousCore_le 𝒜 p
    have hcore : (p.homogeneousCore 𝒜).toIdeal = p :=
      le_antisymm hcorele (hminp (Ideal.IsPrime.homogeneousCore hpp) hcorele)
    have hhomo : Ideal.IsHomogeneous 𝒜 p := by
      rw [← hcore]; exact (p.homogeneousCore 𝒜).isHomogeneous
    refine ⟨hhomo, fun z hzp => ?_⟩
    have h0 : GradedRing.proj 𝒜 0 z ∈ p := by
      rw [GradedRing.proj_apply]
      have hzcore : z ∈ (p.homogeneousCore 𝒜).toIdeal := by rw [hcore]; exact hzp
      have hcomp := ((Ideal.IsHomogeneous.mem_iff 𝒜
        ((p.homogeneousCore 𝒜).isHomogeneous)).mp hzcore) 0
      exact hcore ▸ hcomp
    obtain ⟨c, hc⟩ : ∃ c : k, algebraMap k S c = GradedRing.proj 𝒜 0 z := by
      have hIn : GradedRing.proj 𝒜 0 z ∈ 𝒜 0 := hp0mem z 0
      rw [← hzero] at hIn
      exact LinearMap.mem_range.mp hIn
    have hc0 : c = 0 := by
      by_contra hcne
      exfalso
      have hunit : algebraMap k S c * algebraMap k S c⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hcne, map_one]
      have h1p : (1:S) ∈ p := by
        have hcmem : algebraMap k S c ∈ p := by rw [hc]; exact h0
        have h2 : algebraMap k S c * algebraMap k S c⁻¹ ∈ p :=
          Ideal.mul_mem_right (algebraMap k S c⁻¹) p hcmem
        rwa [hunit] at h2
      exact hpp.ne_top (Ideal.eq_top_iff_one p |>.mpr h1p)
    rw [(hmem z), ← hc, hc0, map_zero]
  · -- Steps 5 and 6: dimension computations.
    sorry
  · intro d
    sorry

end

end Formalization.Books.Algebra.Unit117
