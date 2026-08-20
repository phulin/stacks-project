import Formalization.Books.Algebra.Unit25.ZerodivisorsAndTotalRingsOfFractions
import Formalization.Books.Algebra.Unit23.GlueingProperties
import Formalization.Books.Algebra.Unit53.ArtinianRings
import Formalization.Books.Algebra.Unit119.AroundKrullAkizuki
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.LinearAlgebra.TensorProduct.Subalgebra
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Varieties, Chapter 37: Glueing dimension one rings

The source section gives a common-field pullback situation and a sequence of
one-dimensional commutative-algebra lemmas.  Subalgebras of a field are used
for the source's subrings; this makes the intersection, inclusions, and
canonical tensor-product multiplication maps available from Mathlib.
-/

namespace Formalization.Books.Varieties.Unit37

open Set
open AlgebraicGeometry
open scoped TensorProduct

universe u v

noncomputable section

/-! ## The common-field situation and its canonical maps -/

/-- The common-field situation from the source.

`A` and `B` are subrings of the field `K`, represented by `ℤ`-subalgebras.
The two `IsFractionRing` fields record that the displayed ambient field is
the fraction field of each subring.
-/
structure GlueingSituation (K : Type u) [Field K] where
  A : Subalgebra ℤ K
  B : Subalgebra ℤ K
  A_isFractionRing : IsFractionRing (A : Type u) K
  B_isFractionRing : IsFractionRing (B : Type u) K

/-- The pullback/intersection ring `R = A ×_K B = A ∩ B`. -/
abbrev GlueingSituation.R {K : Type u} [Field K]
    (s : GlueingSituation K) : Subalgebra ℤ K := s.A ⊓ s.B

/-- The canonical tensor-product map `A ⊗ B → K` for subrings of `K`. -/
abbrev GlueingSituation.tensorProductMap {K : Type u} [Field K]
    (s : GlueingSituation K) : (s.A : Type u) ⊗[ℤ] (s.B : Type u) →ₐ[ℤ] K :=
  s.A.mulMap s.B

/-- A tensor-product map to a field when the left ring is abstract and the
right ring is a subalgebra of the field.  This is the canonical multiplication
map used by the source's `A ⊗ B → K` assertions.
-/
def tensorProductMapToField
    {A : Type u} {K : Type v} [CommRing A] [Field K] [Algebra A K]
    (B : Subalgebra ℤ K) : A ⊗[ℤ] (B : Type v) →ₐ[ℤ] K :=
  Algebra.TensorProduct.lift (algebraMap A K).toIntAlgHom B.val
    (fun _ _ => Commute.all _ _)

/-- The canonical multiplication map `A ⊗[R] B → K` in the glueing
situation, where `R = A ∩ B`.  The scalar algebra structures are the ones
induced by the inclusions of the infimum subalgebra into `A` and `B`. -/
def GlueingSituation.tensorProductMapOverR {K : Type u} [Field K]
    (s : GlueingSituation K) :
    (s.A : Type u) ⊗[s.R] (s.B : Type u) →ₐ[s.R] K :=
  Algebra.TensorProduct.lift
    { toRingHom := s.A.val
      commutes' := by intro r; rfl }
    { toRingHom := s.B.val
      commutes' := by intro r; rfl }
    (fun _ _ => Commute.all _ _)

/-- The spectrum map induced by an inclusion of two `ℤ`-subalgebras. -/
def specMapOfLe {K : Type u} [Field K]
    {S T : Subalgebra ℤ K} (h : S ≤ T) :
    Spec (CommRingCat.of (T : Type u)) ⟶ Spec (CommRingCat.of (S : Type u)) :=
  Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom)

/-- The map `Spec(A) → Spec(R)` in a glueing situation. -/
abbrev GlueingSituation.specMapA {K : Type u} [Field K]
    (s : GlueingSituation K) :=
  specMapOfLe (K := K) (S := s.R) (T := s.A) inf_le_left

/-- The map `Spec(B) → Spec(R)` in a glueing situation. -/
abbrev GlueingSituation.specMapB {K : Type u} [Field K]
    (s : GlueingSituation K) :=
  specMapOfLe (K := K) (S := s.R) (T := s.B) inf_le_right

/-- “`B` dominates the localization of `A` at `m`”, written inside the
common field `K`.  The first clause says that the localization embeds in
`B`; the second says that this embedding is local. -/
def GlueingSituation.dominatesAtMaximal {K : Type u} [Field K]
    (s : GlueingSituation K) (m : MaximalSpectrum (s.A : Type u)) : Prop :=
  ∃ n : Ideal (s.B : Type u), n.IsMaximal ∧
    (∀ a t : s.A, t ∉ m.asIdeal → (a : K) * (t : K)⁻¹ ∈ s.B) ∧
      (∀ a : s.A, a ∈ m.asIdeal ↔
        ∃ b : s.B, (b : K) = (a : K) ∧ b ∈ n)

/-- Membership in the Jacobson radical of a subalgebra of `K`, for an element
of the ambient field. -/
def IsInJacobsonRadical {K : Type u} [Field K]
    (B : Subalgebra ℤ K) (x : K) : Prop :=
  ∃ y : B, (y : K) = x ∧ y ∈ Ring.jacobson (B : Type u)

/-! ## The localization used in the final lemma -/

/-- The multiplicative system outside a finite family of prime ideals. -/
def primeFamilyComplement
    {A : Type u} [CommRing A] {n : ℕ}
    (p : Fin n → PrimeSpectrum A) : Submonoid A :=
  ⨅ i, (p i).asIdeal.primeCompl

@[simp]
theorem mem_primeFamilyComplement
    {A : Type u} [CommRing A] {n : ℕ}
    (p : Fin n → PrimeSpectrum A) (x : A) :
    x ∈ primeFamilyComplement p ↔
      x ∉ ⋃ i, (p i).asIdeal := by
  simp [primeFamilyComplement]

/-- The maximal elements of a finite family of prime ideals. -/
def maximalElementsOfPrimeFamily
    {A : Type u} [CommRing A] {n : ℕ}
    (p : Fin n → PrimeSpectrum A) : Set (Ideal A) :=
  {q | q ∈ Set.range (fun i => (p i).asIdeal) ∧
    ∀ r, r ∈ Set.range (fun i => (p i).asIdeal) → q ≤ r → r = q}

/-- The intersection of the minimal primes of `A`, as used in the two
nilpotent-thickening lemmas. -/
abbrev minimalPrimeIntersection
    {A : Type u} [CommRing A] : Ideal A :=
  ⨅ p : Formalization.Books.Algebra.Unit25.MinimalPrimeSpectrum A, p.1.asIdeal

/-! ## Source lemmas -/

/-- Lemma `lemma-glue-valuation-ring`. -/
theorem glue_valuation_ring
    {K : Type u} [Field K] (s : GlueingSituation K)
    [ValuationRing (s.B : Type u)] :
    ∀ u : (s.A : Type u)ˣ,
      (u : K) ∈ s.R ∨ (u : K)⁻¹ ∈ s.R := by
  intro u
  rcases @ValuationRing.isInteger_or_isInteger (s.B : Type u) _ _ K _ _
      s.B_isFractionRing inferInstance (u : K) with h | h
  · left
    have huB : (u : K) ∈ s.B := by
      rcases h with ⟨b, hb⟩
      rw [← hb]
      exact b.property
    change (u : K) ∈ s.A ∧ (u : K) ∈ s.B
    constructor
    · exact u.val.property
    · exact huB
  · right
    have huB : (u : K)⁻¹ ∈ s.B := by
      rcases h with ⟨b, hb⟩
      rw [← hb]
      exact b.property
    have huA : (u : K)⁻¹ ∈ s.A := by
      change (algebraMap (s.A : Type u) K (u : s.A))⁻¹ ∈ s.A
      rw [← map_units_inv]
      exact u⁻¹.val.property
    change (u : K)⁻¹ ∈ s.A ∧ (u : K)⁻¹ ∈ s.B
    constructor
    · exact huA
    · exact huB

/-- Lemma `lemma-glue-separated`. -/
theorem glue_separated
    {K : Type u} [Field K] (s : GlueingSituation K)
    [IsNoetherianRing (s.A : Type u)]
    (hA_dimension : ringKrullDim (s.A : Type u) = 1) :
    (¬ Function.Surjective s.tensorProductMap) ↔
      ∃ O : Subalgebra ℤ K,
        IsDiscreteValuationRing (O : Type u) ∧ s.A ≤ O ∧ s.B ≤ O := by
  /-
  Proof roadmap.

  * Put `C := s.tensorProductMap.range : Subalgebra ℤ K`.  Tensor-product
    induction gives `s.A ≤ C`, `s.B ≤ C`, and, for every common overring
    `O`, `C ≤ O`.  Use `AlgHom.range_eq_top` from
    `Mathlib/Algebra/Algebra/Subalgebra/Lattice.lean` to translate
    surjectivity into `C = ⊤`.
  * For the reverse implication, the preceding containment puts the image in
    the proposed DVR.  Surjectivity would make `O = ⊤`, hence `IsField O`,
    contradicting `IsDiscreteValuationRing.not_isField` from
    `Mathlib/RingTheory/DiscreteValuationRing/Basic.lean`.
  * Conversely assume `C ≠ ⊤`.  First prove `¬ IsField C`: if `C` were a
    field, write each `z : K` as `a / b` with `a b : s.A` by
    `IsFractionRing.div_surjective` in
    `Mathlib/RingTheory/Localization/FractionRing.lean`; closure under the
    inverse of the nonzero image of `b` would put every `z` in `C`.
    Choose a maximal ideal `m` of `C` using `Ideal.exists_le_maximal`; it is
    nonzero because `C` is a domain but not a field.
  * Apply `IsLocalRing.exists_factor_valuationRing` from
    `Mathlib/RingTheory/Valuation/LocalSubring.lean` to the canonical map
    `Localization.AtPrime m →+* K`.  Its valuation subring `V` contains `C`
    and its maximal ideal lies over `m`.  Set
    `O := Subalgebra.subalgebraOfSubring V.toSubring`; then `s.A ≤ O` and
    `s.B ≤ O`.
  * Regard the same carrier as an `s.A`-subalgebra of `K` (define the
    `algebraMap_mem'` field from `s.A ≤ O`).  Instantiate
    `Formalization.Books.Algebra.Unit119.krull_akizuki` from
    `Formalization/Books/Algebra/Unit119/AroundKrullAkizuki.lean` with
    `R := s.A`, `K := K`, `L := K` to get `IsNoetherianRing O`.
    The valuation-subring instance gives `ValuationRing O`, and the nonzero
    ideal over `m` shows `¬ IsField O`; finish with
    `(IsDiscreteValuationRing.TFAE O hnotfield).out 1 0` from
    `Mathlib/RingTheory/DiscreteValuationRing/TFAE.lean`.
  -/
  sorry

/-- Lemma `lemma-semi-local`. -/
theorem semi_local
    {K : Type u} [Field K] (s : GlueingSituation K)
    [IsNoetherianRing (s.A : Type u)]
    [Finite (MaximalSpectrum (s.A : Type u))]
    (hA_dimension : ringKrullDim (s.A : Type u) = 1)
    [IsDiscreteValuationRing (s.B : Type u)] :
    ((¬ ∀ u : (s.A : Type u)ˣ, (u : K) ∈ s.R) ∧
      IsNoetherianRing (s.R : Type u) ∧
      Finite (MaximalSpectrum (s.R : Type u)) ∧
      ringKrullDim (s.R : Type u) = 1 ∧
      IsOpenImmersion s.specMapA ∧ IsOpenImmersion s.specMapB ∧
        Set.range s.specMapA.base ∪ Set.range s.specMapB.base = Set.univ ∧
        Function.Bijective s.tensorProductMapOverR) ∨
    ((∀ u : (s.A : Type u)ˣ, (u : K) ∈ s.R) ∧
      (∃ m : MaximalSpectrum (s.A : Type u), s.dominatesAtMaximal m) ∧
      ¬ Function.Surjective s.tensorProductMap) := by
  /-
  Proof roadmap.  Keep the following parameter lemma separate so that the
  localization and scheme calculations do not repeatedly unfold `s.R`:

  `caseA_parameters : ∃ u x : s.R, IsLocalization.Away u s.A ∧
    IsLocalization.Away x s.B ∧ IsLocalization.Away (u * x) K ∧
    Ideal.span ({u, x} : Set s.R) = ⊤`.

  To prove it, choose a unit of `s.A` outside `s.R`.  Apply
  `glue_valuation_ring` to its inverse so that the resulting `u : s.R` is a
  unit in `s.A` and belongs to the maximal ideal of the DVR `s.B`.  The usual
  fraction argument proves `s.A = R_u`.  Choose a nonzero `x` in the
  Jacobson radical of the semilocal domain `s.A` (enumerate
  `MaximalSpectrum s.A` with `Fintype.ofFinite` and use prime avoidance).
  Dimension one and `IsFractionRing.div_surjective` give `K = A_x`; adjust
  `x` by positive powers of `x` and integral powers of `u` so its image is a
  unit in `s.B`.  The DVR factorization API in
  `Mathlib/RingTheory/DiscreteValuationRing/Basic.lean` then proves
  `s.B = R_x`.  Finally, any maximal ideal containing both `u` and `x`
  would contract to a maximal ideal of `A` and to the maximal ideal of `B`;
  this is impossible, so the displayed span is top.

  From `caseA_parameters`, use `IsOpenImmersion.of_isLocalization` in
  `Mathlib/AlgebraicGeometry/OpenImmersion.lean` for the two spectrum maps;
  `Scheme.Hom.opensRange_localizationAway` identifies their ranges with
  `D(u)` and `D(x)`.  Use
  `IsLocalization.Away.tensorProductEquivTMulRight` from
  `Mathlib/RingTheory/Localization/BaseChange.lean`, followed by the
  uniqueness of localization at `u*x`, to identify its underlying map with
  `s.tensorProductMapOverR` and obtain bijectivity.  Descend Noetherianity
  from the two-element standard cover with
  `Formalization.Books.Algebra.Unit23.standard_cover_noetherian` in
  `Formalization/Books/Algebra/Unit23/GlueingProperties.lean`; the localization
  prime correspondence `IsLocalization.orderIsoOfPrime` gives finiteness of
  the maximal spectrum and dimension one (non-fieldness follows from either
  closed point).

  In case every unit of `s.A` lies in `s.R`, first show
  `Ring.jacobson s.A ≤ s.R`: for `a` in the Jacobson radical, both `1+a` and
  `1` are units.  The CRT decomposition of a semilocal ring modulo its
  Jacobson radical then shows `s.A` is integral over `s.R`.  Since the DVR
  `s.B` is integrally closed, fraction-field induction puts `s.A ≤ s.B`.
  For nonzero `x` in the Jacobson radical of `s.A`, dimension one gives
  `K = A_x`, hence `x⁻¹ ∉ s.B`; thus `x` lies in the maximal ideal of `s.B`.
  Contract that ideal to the required `m`, and fill both clauses of
  `dominatesAtMaximal` using `IsLocalization.AtPrime` and this contraction.
  Finally invoke the reverse direction of `glue_separated` with `O := s.B`.
  -/
  sorry

/-- Lemma `lemma-semi-local-dimension-one-conductor`. -/
theorem semi_local_dimension_one_conductor
    {B : Type u} [CommRing B] [IsDomain B]
    {K : Type u} [Field K] [Algebra B K] [IsFractionRing B K]
    [IsNoetherianRing B] [Finite (MaximalSpectrum B)]
    (hB_dimension : ringKrullDim B = 1) :
    IsDedekindDomain (integralClosure B K) ∧
      Finite (MaximalSpectrum (integralClosure B K)) ∧
      ∀ x : integralClosure B K,
        x ≠ 0 → x ∈ Ring.jacobson (integralClosure B K) →
        ∀ y : integralClosure B K, ∃ n : ℕ, ∃ b : B,
          algebraMap B (integralClosure B K) b = x ^ n * y := by
  /-
  Proof roadmap.  Let `B' := integralClosure B K` throughout and install
  important instances once with `letI`.

  * Obtain `IsDedekindDomain B'` from
    `Formalization.Books.Algebra.Unit119.integral_closure_is_dedekind` in
    `Formalization/Books/Algebra/Unit119/AroundKrullAkizuki.lean`, instantiated
    with `R := B`, `K := K`, `L := K` (the identity extension supplies
    `Module.Finite K K`).
  * Prove semilocality fibrewise.  Enumerate `MaximalSpectrum B`.  For each
    `m`, localize `B'` at the image of `m.primeCompl`; under
    `IsLocalization.orderIsoOfPrime`, its maximal ideals are precisely the
    primes of `B'` over `m`.  Apply
    `Formalization.Books.Algebra.Unit119.finite_residue_field_fibres` to the
    local domain `Localization.AtPrime m.asIdeal` and this localized
    overring (fraction fields are both `K`) to make that fibre finite.
    Every maximal ideal of `B'` contracts to a maximal ideal of `B` by
    `Ideal.IsIntegral.isMaximal_of_isMaximal_comap` in
    `Mathlib/RingTheory/Ideal/GoingUp.lean`; a finite union of the finite
    fibres gives `Finite (MaximalSpectrum B')`.
  * For the conductor assertion set
    `C := Algebra.adjoin B ({x, y} : Set B')`.  Integrality of `B'` and
    `Algebra.finite_adjoin_of_finite_of_isIntegral` from
    `Mathlib/RingTheory/IntegralClosure/IsIntegral/Basic.lean` make `C` a
    finite `B`-module.  Define the finite quotient module
    `Q := C ⧸ LinearMap.range (Algebra.linearMap B C)`.  At the generic point
    it vanishes because `B` and `C` have fraction field `K`; by
    `Ring.krullDimLE_one_iff` every prime in `Module.support B Q` is maximal.
    Since `B` is semilocal, finite generation plus
    `Ideal.exists_radical_pow_le_of_fg` yields
    `(Ring.jacobson B)^N • C ≤ algebraMap B C '' Set.univ` for some `N`.
  * Lying over for the integral map `C → B'`
    (`Algebra.IsIntegral.comap_surjective` in
    `Mathlib/RingTheory/Spectrum/Prime/Topology.lean`) shows that `x` belongs
    to `Ring.jacobson C`.  Prove
    `Ring.jacobson C = (Ring.jacobson B).map (algebraMap B C) |>.radical`;
    then some positive power `x^M` lies in that mapped ideal.  Raising once
    more to the `N`th power and multiplying by `y` puts `x^(M*N) * y` in the
    image of `B`.  Unpack image membership to obtain the required `b` and
    take `n := M*N`.
  -/
  sorry

/-- Lemma `lemma-semi-local-both-side`. -/
theorem semi_local_both_side
    {K : Type u} [Field K] (s : GlueingSituation K)
    [IsNoetherianRing (s.A : Type u)]
    [Finite (MaximalSpectrum (s.A : Type u))]
    (hA_dimension : ringKrullDim (s.A : Type u) = 1)
    [IsNoetherianRing (s.B : Type u)]
    [Finite (MaximalSpectrum (s.B : Type u))]
    (hB_dimension : ringKrullDim (s.B : Type u) = 1)
    (h_surjective : Function.Surjective s.tensorProductMap) :
    IsNoetherianRing (s.R : Type u) ∧
      Finite (MaximalSpectrum (s.R : Type u)) ∧
      ringKrullDim (s.R : Type u) = 1 ∧
      IsOpenImmersion s.specMapA ∧ IsOpenImmersion s.specMapB ∧
      Set.range s.specMapA.base ∪ Set.range s.specMapB.base = Set.univ ∧
      Function.Bijective s.tensorProductMapOverR := by
  /-
  Proof roadmap.

  First handle integrally closed `s.B`.  Build `IsDedekindDomain s.B` from
  Noetherianity, integrally closedness, and `hB_dimension` using
  `isDedekindDomain_iff` in
  `Mathlib/RingTheory/DedekindDomain/Basic.lean`.  Enumerate
  `MaximalSpectrum s.B`; for `m`, use
  `Localization.subalgebra.ofField K _ m.asIdeal.primeCompl_le_nonZeroDivisors`
  as the copy of `B_m` inside `K`.  It is a DVR by
  `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain` in
  `Mathlib/RingTheory/DedekindDomain/Dvr.lean`.  Inductively intersect the
  current ring with these `B_m`.  Surjectivity of `A ⊗ B_m → K` follows from
  `h_surjective` because `B ≤ B_m`; therefore the second branch of
  `semi_local` is impossible.  Its strengthened first branch supplies the
  Noetherian, semilocal, and dimension-one hypotheses for the next step.
  Use `MaximalSpectrum.iInf_localization_eq_bot` from
  `Mathlib/RingTheory/Spectrum/Maximal/Localization.lean`, transported from
  `B`-subalgebras to `ℤ`-subalgebras, to identify the final intersection with
  `s.B`.  Compose the open immersions and localization equivalences produced
  at each step; use `IsLocalization.map_under` to identify the complementary
  maximal ideals and hence the final ranges.

  For general `s.B`, put `B' := integralClosure s.B K` and apply
  `semi_local_dimension_one_conductor`.  Apply the normalized case to
  `R' := s.A ⊓ B'`.  By finite prime avoidance/CRT choose `x : R'` outside
  every maximal ideal coming from `s.A` and inside every maximal ideal of
  `B'`.  The conductor lemma first replaces `x` by a positive power in
  `s.R`, and then clears denominators of every `y : R'`; conclude
  `IsLocalization.Away x s.A`.  Exchange `A` and `B` to obtain `y : s.R`
  with `IsLocalization.Away y s.B`.  No prime contains both parameters, so
  `Ideal.span {x,y}=⊤`, and `K` is the localization away from `x*y`.
  Finish exactly as in the first branch of `semi_local`: use
  `IsOpenImmersion.of_isLocalization`,
  `IsLocalization.Away.tensorProductEquivTMulRight`, and
  `Unit23.standard_cover_noetherian`; the prime-localization order isomorphism
  gives semilocality and dimension one.
  -/
  sorry

/-- Lemma `lemma-glue-a-bunch-of-local-rings`. -/
theorem glue_a_bunch_of_local_rings
    {K : Type u} [Field K] (r : ℕ) (hr : 0 < r)
    (A : Fin r → Subalgebra ℤ K)
    (hA_noetherian : ∀ i, IsNoetherianRing (A i : Type u))
    (hA_semilocal : ∀ i, Finite (MaximalSpectrum (A i : Type u)))
    (hA_dimension : ∀ i, ringKrullDim (A i : Type u) = 1)
    (hA_fractionField : ∀ i, IsFractionRing (A i : Type u) K)
    (h_pairwise : ∀ i j, i ≠ j →
      Function.Surjective ((A i).mulMap (A j))) :
    let A₀ : Subalgebra ℤ K := ⨅ i, A i
    IsNoetherianRing (A₀ : Type u) ∧
      Finite (MaximalSpectrum (A₀ : Type u)) ∧
      ringKrullDim (A₀ : Type u) = 1 ∧
      (∀ i, IsOpenImmersion
        (specMapOfLe (K := K) (S := A₀) (T := A i) (iInf_le _ i))) ∧
      (Set.iUnion (fun i => Set.range
        (specMapOfLe (K := K) (S := A₀) (T := A i) (iInf_le _ i)).base) = Set.univ) ∧
      (∀ p : PrimeSpectrum (A₀ : Type u), p.asIdeal.IsMaximal →
        ∃! i : Fin r, p ∈ Set.range
          (specMapOfLe (K := K) (S := A₀) (T := A i) (iInf_le _ i)).base) := by
  /-
  Proof roadmap.  Induct on the positive natural `r`, using `Fin.cases` to
  separate `A 0` from the tail and an explicit order isomorphism between the
  tail infimum and `⨅ i : Fin (r-1), A i.succ`.

  For `r = 1`, prove `A₀ = A 0` by `le_antisymm` and `le_iInf`/`iInf_le`.
  Transport the supplied instances across this equality; `specMapOfLe` is
  the identity map, so all six conclusions reduce to `Set.range_id` and
  subsingletonness of `Fin 1`.

  In the successor step apply the induction hypothesis to the tail and call
  its intersection `B`.  It supplies `IsNoetherianRing B`,
  `Finite (MaximalSpectrum B)`, and `ringKrullDim B = 1`.  The nontrivial
  intermediate claim is

  `Function.Surjective ((A 0).mulMap B)`.

  Prove it by contradiction with `glue_separated`.  A DVR `O` containing
  both `A 0` and `B` has a centre on `Spec B`.  The tail open immersions cover
  `Spec B`, so that centre lies in the image of one `Spec (A i.succ)`.
  Express that open immersion as a localization (the induction construction
  records its parameter); the parameter is a unit in `O`, hence
  `A i.succ ≤ O`.  The reverse implication of `glue_separated`, now for
  `A 0` and `A i.succ`, contradicts `h_pairwise 0 i.succ`.

  Apply the strengthened `semi_local_both_side` to `A 0` and `B`.  Identify
  their intersection with `A₀` by extensionality and associativity of `⊓`.
  Its first three conjuncts are the required ring properties, and composition
  of the new two-open cover with the tail cover gives the displayed `iUnion`.
  For uniqueness at a closed point, use the tail induction hypothesis when
  both indices are successors.  If one index is `0`, a point in both images
  gives a map of both `A 0` and `A j` to the local ring at that point; the
  induced factorization of `(A 0).mulMap (A j)` through this nonfield local
  ring contradicts its surjectivity.  This also proves existence by the
  assembled cover.
  -/
  sorry

/-- Lemma `lemma-create-globally-generated`. -/
theorem create_globally_generated
    {A : Type u} [CommRing A] [IsDomain A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
    (r : ℕ) (B : Fin r → Subalgebra ℤ K)
    (hB_noetherian : ∀ i, IsNoetherianRing (B i : Type v))
    (hB_semilocal : ∀ i, Finite (MaximalSpectrum (B i : Type v)))
    (hB_dimension : ∀ i, ringKrullDim (B i : Type v) = 1)
    (hB_fractionField : ∀ i, IsFractionRing (B i : Type v) K)
    (h_surjective : ∀ i,
      Function.Surjective (tensorProductMapToField (A := A) (B i))) :
    ∃ x : A, x ≠ 0 ∧
      ∀ i, IsInJacobsonRadical (B i) (algebraMap A K x)⁻¹ := by
  /-
  Proof roadmap.

  Normalize each `B i` inside `K`.  The preceding conductor theorem gives a
  semilocal Dedekind domain.  Enumerate its maximal ideals and replace it by
  the finite family of localizations at those ideals.  Each is a DVR by
  `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain` from
  `Mathlib/RingTheory/DedekindDomain/Dvr.lean`.  Surjectivity of
  `A ⊗ B_i → K` persists after localization.  It is therefore enough to prove
  the following finite-DVR helper (state it immediately before this theorem
  if elaboration becomes large):

  `exists_negative_at_dvrs (O : Fin n → Subalgebra ℤ K)
    [∀ j, IsDiscreteValuationRing (O j)]
    (h : ∀ j, Function.Surjective
      (tensorProductMapToField (A := A) (O j))) :
    ∃ x : A, x ≠ 0 ∧ ∀ j, (algebraMap A K x)⁻¹ ∈
      IsLocalRing.maximalIdeal (O j)`.

  For one DVR, failure says every nonzero image from `A` is integral in the
  DVR, hence `A ≤ O`; the tensor-product range is then contained in `O`,
  contradicting surjectivity and `IsDiscreteValuationRing.not_isField`.
  For the induction, use the fraction-field valuation
  `(IsDiscreteValuationRing.maximalIdeal (O j)).valuation K` (values in
  `ℤᵐ⁰`).  If `x` works for the first `n` valuations and `y` for the last,
  replace `x` by a large positive power so its values are strictly dominant
  at the first `n`; then `x+y` works everywhere by
  `Valuation.map_add_eq_of_lt_left/right` from
  `Mathlib/RingTheory/Valuation/Basic.lean`.  Record nonzeroness from the
  nonzero valuation values.

  The helper produces `x⁻¹` in the Jacobson radical of every normalized
  `B'_i`.  Apply `semi_local_dimension_one_conductor` with this element and
  `y := 1`; after taking one common positive power over the finite index set,
  `(x^N)⁻¹` belongs to every original `B i`.  Lying over for
  `B i → B'_i` shows it lies in every maximal ideal of `B i`.  Package the
  actual subtype element and equality in `IsInJacobsonRadical`, and return
  `x^N`; its nonzeroness follows from `map_ne_zero_iff` and the fraction-ring
  injectivity of `A → K`.
  -/
  sorry

/-- Lemma `lemma-power-equal`. -/
theorem power_equal
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA_dimension : ringKrullDim A = 1)
    (a₁ a₂ : A)
    (ha₁ : a₁ ∈ IsLocalRing.maximalIdeal A)
    (ha₂ : a₂ ∈ IsLocalRing.maximalIdeal A)
    (h_equal : Formalization.Books.Algebra.Unit25.mapToMinimalPrimeLocalizations a₁ =
      Formalization.Books.Algebra.Unit25.mapToMinimalPrimeLocalizations a₂) :
    ∃ n : ℕ, 0 < n ∧ a₁ ^ n = a₂ ^ n := by
  /-
  Proof roadmap.  Set `d := a₁ - a₂`, `I := Ideal.ann {d}`, and
  `m := IsLocalRing.maximalIdeal A`.

  For every minimal prime `p`, apply `congrFun h_equal p`; after rewriting
  `map_sub`, the image of `d` in `Localization.AtPrime p.asIdeal` is zero.
  `IsLocalization.map_eq_zero_iff` supplies `s ∉ p` with `s*d=0`, so primality
  gives `d ∈ p`.  Thus `d` lies in every prime (reduce an arbitrary prime to
  a minimal one with `Ideal.exists_minimalPrimes_le` from
  `Mathlib/RingTheory/Ideal/MinimalPrime/Basic.lean`), and
  `nilpotent_iff_mem_prime` yields `d^k=0` for some positive `k`.

  Next show every prime containing `I` is `m`.  Such a prime cannot be
  minimal, since the preceding localization witness lies in `I` but outside
  that minimal prime.  Install `Ring.KrullDimLE 1 A` from `hA_dimension` and
  use `Ring.krullDimLE_one_iff` in
  `Mathlib/RingTheory/KrullDimension/Basic.lean`: a nonminimal prime is
  maximal, hence equals the unique maximal ideal.  Consequently
  `I.radical = m`.  Since `m` is finitely generated in the Noetherian ring,
  `Ideal.exists_radical_pow_le_of_fg` gives `m^N ≤ I`.

  Rewrite `a₁ = a₂ + d` and expand `(a₂+d)^(N+k)` with `Commute.add_pow` from
  `Mathlib/Data/Nat/Choose/Sum.lean`.  Terms with `d`-exponent at least `k`
  vanish; in every remaining nonconstant term the `a₂`-exponent is at least
  `N`, hence that factor lies in `m^N ≤ I` and annihilates `d` (and therefore
  every positive power of `d`).  Only `a₂^(N+k)` remains.  Return `N+k`; use
  the chosen positive `k` for positivity.
  -/
  sorry

/-- Lemma `lemma-power-works`. -/
theorem power_works
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA_dimension : ringKrullDim A = 1)
    (f : Formalization.Books.Algebra.Unit25.minimalPrimeLocalizations A)
    (i : Formalization.Books.Algebra.Unit25.minimalPrimeLocalizations A)
    (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A)
    (hi : i ∈ (minimalPrimeIntersection (A := A)).map
      (Formalization.Books.Algebra.Unit25.mapToMinimalPrimeLocalizations (R := A)))
    (hf : f = i + Formalization.Books.Algebra.Unit25.mapToMinimalPrimeLocalizations a) :
    ∃ n : ℕ, 0 < n ∧ ∃ b : A,
      Formalization.Books.Algebra.Unit25.mapToMinimalPrimeLocalizations b = f ^ n := by
  /-
  Proof roadmap.  Abbreviate
  `L := Unit25.minimalPrimeLocalizations A`,
  `φ := Unit25.mapToMinimalPrimeLocalizations (R := A)`, and
  `I := minimalPrimeIntersection`.

  First prove two reusable local helpers.

  1. `I = nilradical A`: one inclusion is immediate; for the other, put an
     element in every prime by choosing a minimal prime below it with
     `Ideal.exists_minimalPrimes_le`.  Then use
     `IsNoetherianRing.isNilpotent_nilradical` from
     `Mathlib/RingTheory/Noetherian/Nilpotent.lean` to choose `t > 0` with
     `I^t = ⊥`.
  2. Choose `g : A` outside all minimal primes but in the maximal ideal by
     `minimalPrimes.finite_of_isNoetherianRing` and finite prime avoidance.
     `Ring.krullDimLE_one_iff` gives
     `(Ideal.span {g}).radical = IsLocalRing.maximalIdeal A`.  Prove
     `IsLocalization.Away g L`: each component is a localization where `g`
     is a unit, and surjectivity follows by applying
     `IsNoetherianRing.isArtinianRing_of_krullDimLE_zero` to `A_g` and its
     finite product decomposition (`IsArtinianRing.equivPi` in
     `Mathlib/RingTheory/Artinian/Module.lean`).  Ensure the canonical map of
     this localization instance is definitionally `φ`.

  Induct on `k = 1,...,t`, maintaining
  `∃ N > 0, ∃ b : A, ∃ j ∈ (I^k).map φ, f^N = φ b + j`.
  The input `hf` and `hi` initialize `k=1`, `N=1`, `b=a`.  At the induction
  step expand `(φ b+j)^n` modulo `(I^(k+1)).map φ`.  All terms containing at
  least two copies of `j` lie there because `2*k ≥ k+1`; only
  `n * φ(b^(n-1)) * j` remains.  The radical equality for `g` gives a power
  of `b` divisible by `g`.  Use `IsLocalization.surj (Submonoid.powers g)`
  for a representative of `j` and take `n` large enough to clear its
  denominator; the linear error then lies in the actual image under `φ` of
  `I^k`, so absorb it into the new `b`.  The unabsorbed error is in
  `(I^(k+1)).map φ`.  At `k=t`, rewrite `I^t=⊥`; the error is zero and the
  maintained equality, reversed, is the desired conclusion.  Keep `N` and
  all induction exponents explicitly positive so the final positivity is
  immediate.
  -/
  sorry

/-- Lemma `lemma-good-intersection`. -/
theorem good_intersection
    {A : Type u} {K : Type v} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing K]
    (hA_dimension : ringKrullDim A = 1)
    (f : K →+* Formalization.Books.Algebra.Unit25.minimalPrimeLocalizations A)
    (hf : f.IsIntegral) :
    ∃ a : A, a ∈ IsLocalRing.maximalIdeal A ∧
      ∃ x : K,
        Formalization.Books.Algebra.Unit25.mapToMinimalPrimeLocalizations a = f x ∧
          IsLocalRing.maximalIdeal A = (Ideal.span ({a} : Set A)).radical := by
  /-
  Proof roadmap.  Write `L` and `φ` as in `power_works`, and let
  `I := minimalPrimeIntersection`.

  Reduce first to the reduced quotient `A/I`.  Use the proof that
  `I = nilradical A` from the preceding roadmap and
  `Unit25.isField_localizationAt_minimalPrime_of_isReduced` in
  `Formalization/Books/Algebra/Unit25/ZerodivisorsAndTotalRingsOfFractions.lean`
  to identify the new `L` with a finite product of fields.  Any equality
  obtained modulo `I L` lifts, after taking a positive power, by
  `power_works`; use `power_equal` to make the chosen lift and the original
  representative agree in `A`.  This is the only nilpotent bookkeeping and
  should be isolated as a helper that transports the final radical equality.

  Replace `K` by the subring `f.range ≤ L`; `hf` restricts to an integral
  inclusion.  `Algebra.IsIntegral.comap_surjective` from
  `Mathlib/RingTheory/Spectrum/Prime/Topology.lean` makes
  `Spec L → Spec(f.range)` surjective and closed.  Since the minimal primes
  are finite (`minimalPrimes.finite_of_isNoetherianRing`) and the factors of
  `L` are fields, `Spec(f.range)` is finite discrete.  Install the resulting
  Artinian and reduced instances and use `IsArtinianRing.equivPi` from
  `Mathlib/RingTheory/Artinian/Module.lean` to express `f.range` as a finite
  product of fields.

  Enumerate the minimal primes `p_j` of the reduced `A`.  For each, let
  `L_j := Localization.AtPrime p_j` (a field) and let
  `A_j := integralClosure (A ⧸ p_j) L_j`.  Apply
  `semi_local_dimension_one_conductor` to make `A_j` a semilocal Dedekind
  domain.  Enumerate all `m : MaximalSpectrum A_j`; the localizations at `m`
  are DVRs by
  `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`.
  Their fraction-field valuations, composed with `L → L_j`, form one finite
  family `v_i : L → ℤᵐ⁰`.

  For each `v_i`, find `x` in `f.range` outside its valuation ring.  Otherwise
  the relevant field factor of `f.range` would lie in that DVR; integrality
  makes `L_j` algebraic over it, contradicting
  `Formalization.Books.Algebra.Unit50.algebraicFieldIntersection_not_isField`
  in `Formalization/Books/Algebra/Unit50/ValuationRings.lean`.  Combine the
  finitely many witnesses by the power-and-sum induction using
  `Valuation.map_add_eq_of_lt_left/right`, exactly as in
  `create_globally_generated`.  The inverse of the resulting unit of the
  product of fields has strictly positive value at every `m`.

  Apply the conductor theorem in every `A_j` and take a common power.  This
  yields `x₀ : f.range` whose image in every `L_j` lies in the image of the
  maximal ideal of `A/p_j`.  The cokernel of
  `IsLocalRing.maximalIdeal A → ∏ j, maximalIdeal A / p_j` is finite and
  supported only at the closed point; the same annihilator-power argument as
  in `power_equal` clears it after another power.  Obtain
  `a ∈ IsLocalRing.maximalIdeal A` with `φ a = f x`.  The value at every
  normalized branch is positive, so every nonminimal prime contains `a`,
  while no minimal prime does; `Ring.krullDimLE_one_iff` then gives
  `(Ideal.span {a}).radical = IsLocalRing.maximalIdeal A`.  Reverse this
  equality to match the conclusion.
  -/
  sorry

/-- Lemma `lemma-localization-semi-local`. -/
theorem localization_semi_local
    {A : Type u} [CommRing A] (r : ℕ) (hr : 0 < r)
    (p : Fin r → PrimeSpectrum A) :
    Finite (MaximalSpectrum (Localization (primeFamilyComplement p))) ∧
      ∃ e : MaximalSpectrum (Localization (primeFamilyComplement p)) ≃
          {q : Ideal A // q ∈ maximalElementsOfPrimeFamily p},
        ∀ m, (e m).1 =
          m.1.comap (algebraMap A (Localization (primeFamilyComplement p))) := by
  /-
  Proof roadmap.  Put `M := primeFamilyComplement p` and
  `S := Localization M`.

  Use `IsLocalization.orderIsoOfPrime M S` from
  `Mathlib/RingTheory/Localization/Ideal.lean`.  Its value on a prime of `S`
  is contraction along `algebraMap A S`, and its inverse is ideal map.  Prove
  the key characterization

  `q.IsPrime → Disjoint (M : Set A) q ↔ ∃ i, q ≤ (p i).asIdeal`.

  The reverse direction is immediate from
  `mem_primeFamilyComplement`.  For the forward direction, disjointness says
  `q ⊆ ⋃ i, (p i).asIdeal`; rewrite the union over `Finset.univ` and apply
  `Ideal.subset_union_prime` (used in
  `Formalization/Books/Algebra/Unit25/ZerodivisorsAndTotalRingsOfFractions.lean`)
  to obtain one `i`.

  Next prove that a prime `q` maximal among primes disjoint from `M` is
  literally a maximal member of the displayed finite family.  Choose `i`
  with `q ≤ p_i`; since `p_i` is also disjoint from `M`, maximality gives
  `q=p_i`, and comparison with any `p_j` above it proves the defining
  maximal-element property.  Conversely, if `p_i` is maximal in the family,
  any disjoint prime above it lies below some `p_j`; maximality forces
  `p_i=p_j`, and antisymmetry closes the comparison.

  Define `e` by contracting `m.1`; the preceding paragraph supplies its
  subtype proof.  Injectivity follows from `IsLocalization.map_under M S`.
  For surjectivity, map a maximal family member `q` to `S`; primality and the
  contraction equation are
  `IsLocalization.under_map_of_isPrime_disjoint M S`, and maximality follows
  by transporting comparisons through `IsLocalization.orderIsoOfPrime`.
  Use `Equiv.ofBijective` to package `e`; its requested equation is then
  `rfl` (or `Ideal.under_def` if the abbreviation does not unfold).

  Finally, `maximalElementsOfPrimeFamily p` is a subset of the finite range
  of `fun i => (p i).asIdeal`, hence its subtype is finite.  Transport that
  instance back across `e.symm` with `Finite.of_injective`/`Finite.of_equiv`
  to prove the first conjunct.  The hypothesis `hr` is not needed after the
  order-theoretic proof; retain it because it records the source's nonempty
  finite family.
  -/
  sorry
