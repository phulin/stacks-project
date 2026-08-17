import Formalization.Books.Algebra.Unit25.ZerodivisorsAndTotalRingsOfFractions
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
  (∀ a t : s.A, t ∉ m.asIdeal → (a : K) * (t : K)⁻¹ ∈ s.B) ∧
    (∃ n : Ideal (s.B : Type u), n.IsMaximal ∧
      ∀ a : s.A, a ∈ m.asIdeal →
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
    (hB : ValuationRing (s.B : Type u)) :
    ∀ u : (s.A : Type u)ˣ,
      (u : K) ∈ s.R ∨ (u : K)⁻¹ ∈ s.R := by
  sorry

/-- Lemma `lemma-glue-separated`. -/
theorem glue_separated
    {K : Type u} [Field K] (s : GlueingSituation K)
    (hA_noetherian : IsNoetherianRing (s.A : Type u))
    (hA_dimension : ringKrullDim (s.A : Type u) = 1) :
    (¬ Function.Surjective s.tensorProductMap) ↔
      ∃ O : Subalgebra ℤ K,
        IsDiscreteValuationRing (O : Type u) ∧ s.A ≤ O ∧ s.B ≤ O := by
  sorry

/-- Lemma `lemma-semi-local`. -/
theorem semi_local
    {K : Type u} [Field K] (s : GlueingSituation K)
    (hA_noetherian : IsNoetherianRing (s.A : Type u))
    (hA_semilocal : Finite (MaximalSpectrum (s.A : Type u)))
    (hA_dimension : ringKrullDim (s.A : Type u) = 1)
    (hB : IsDiscreteValuationRing (s.B : Type u)) :
    ((¬ ∀ u : (s.A : Type u)ˣ, (u : K) ∈ s.R) ∧
      IsOpenImmersion s.specMapA ∧ IsOpenImmersion s.specMapB ∧
        Set.range s.specMapA.base ∪ Set.range s.specMapB.base = Set.univ ∧
        Nonempty ((s.A : Type u) ⊗[s.R] (s.B : Type u) ≃ₐ[s.R] K)) ∨
    ((∀ u : (s.A : Type u)ˣ, (u : K) ∈ s.R) ∧
      (∃ m : MaximalSpectrum (s.A : Type u), s.dominatesAtMaximal m) ∧
      ¬ Function.Surjective s.tensorProductMap) := by
  sorry

/-- Lemma `lemma-semi-local-dimension-one-conductor`. -/
theorem semi_local_dimension_one_conductor
    {B : Type u} [CommRing B] [IsDomain B]
    {K : Type v} [Field K] [Algebra B K] [IsFractionRing B K]
    (hB_noetherian : IsNoetherianRing B)
    (hB_semilocal : Finite (MaximalSpectrum B))
    (hB_dimension : ringKrullDim B = 1) :
    IsDedekindDomain (integralClosure B K) ∧
      Finite (MaximalSpectrum (integralClosure B K)) ∧
      ∀ x : integralClosure B K,
        x ≠ 0 → x ∈ Ring.jacobson (integralClosure B K) →
        ∀ y : integralClosure B K, ∃ n : ℕ, ∃ b : B,
          algebraMap B (integralClosure B K) b = x ^ n * y := by
  sorry

/-- Lemma `lemma-semi-local-both-side`. -/
theorem semi_local_both_side
    {K : Type u} [Field K] (s : GlueingSituation K)
    (hA_noetherian : IsNoetherianRing (s.A : Type u))
    (hA_semilocal : Finite (MaximalSpectrum (s.A : Type u)))
    (hA_dimension : ringKrullDim (s.A : Type u) = 1)
    (hB_noetherian : IsNoetherianRing (s.B : Type u))
    (hB_semilocal : Finite (MaximalSpectrum (s.B : Type u)))
    (hB_dimension : ringKrullDim (s.B : Type u) = 1)
    (h_surjective : Function.Surjective s.tensorProductMap) :
    IsOpenImmersion s.specMapA ∧ IsOpenImmersion s.specMapB ∧
      Set.range s.specMapA.base ∪ Set.range s.specMapB.base = Set.univ ∧
      Nonempty ((s.A : Type u) ⊗[s.R] (s.B : Type u) ≃ₐ[s.R] K) := by
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
    ∃ n : ℕ, ∃ b : A,
      Formalization.Books.Algebra.Unit25.mapToMinimalPrimeLocalizations b = f ^ n := by
  sorry

/-- Lemma `lemma-good-intersection`. -/
theorem good_intersection
    {A K : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing K]
    (hA_dimension : ringKrullDim A = 1)
    (f : K →+* Formalization.Books.Algebra.Unit25.minimalPrimeLocalizations A)
    (hf : f.IsIntegral) :
    ∃ a : A, a ∈ IsLocalRing.maximalIdeal A ∧
      ∃ x : K,
        Formalization.Books.Algebra.Unit25.mapToMinimalPrimeLocalizations a = f x ∧
          IsLocalRing.maximalIdeal A = (Ideal.span ({a} : Set A)).radical := by
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
  sorry
