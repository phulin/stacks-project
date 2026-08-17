import Formalization.Books.Algebra.Unit112.HomomorphismsAndDimension
import Formalization.Books.Algebra.Unit114.DimensionFiniteTypeAlgebras
import Formalization.Books.Algebra.Unit115.NoetherNormalization
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.SetTheory.Cardinal.ENat

/-!
# Commutative Algebra, Chapter 116: Dimension of finite type algebras over fields, reprise

The source's Krull dimensions use Mathlib's `ringKrullDim`, local dimensions
of spectra use the topological `krullDimensionAt`, and transcendence degrees
use the cardinal-valued `Algebra.trdeg`.  The tensor-product fibre in the
last statement uses the canonical `Unit112.tensorLocalRingOfFibre` interface.
-/

namespace Formalization.Books.Algebra.Unit116

universe u v

noncomputable section

open Set
open scoped TensorProduct
open Formalization.Books.Topology.Unit10

/-! ## Dimension and transcendence degree -/

/- The field of fractions is supplied as a field carrying the canonical
   algebra and scalar-tower structures over the finite-type domain. -/
theorem dimension_prime_polynomial_ring
    {k S : Type u} {K : Type v}
    [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [IsDomain S]
    [Field K] [Algebra S K] [IsFractionRing S K]
    [Algebra k K] [IsScalarTower k S K] :
    ∃ r : ℕ, Algebra.trdeg k K = r ∧
      ringKrullDim S = r ∧
        ∀ m : MaximalSpectrum S,
          ringKrullDim (Localization.AtPrime m.asIdeal) = r := by
  sorry

/- The residue-field transcendence degree strictly decreases along a proper
   specialization. -/
theorem tr_deg_specialization
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S]
    (q q' : PrimeSpectrum S) (hqq' : q < q') :
    Algebra.trdeg k q'.asIdeal.ResidueField <
      Algebra.trdeg k q.asIdeal.ResidueField := by
  sorry

/- The local dimension formula at an arbitrary point of a finite-type affine
   algebra over a field. -/
theorem dimension_at_a_point_finite_type_field
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (p : PrimeSpectrum S) :
    krullDimensionAt p =
      ringKrullDim (Localization.AtPrime p.asIdeal) +
        ((Cardinal.toENat (Algebra.trdeg k p.asIdeal.ResidueField) : ℕ∞) :
          WithBot ℕ∞) := by
  sorry

/- The codimension formula for a surjective finite-type map is written using
   the canonical comap point and the corresponding prime heights. -/
theorem codimension
    {k S' S : Type u} [Field k]
    [CommRing S'] [CommRing S] [Algebra k S'] [Algebra k S]
    [Algebra.FiniteType k S'] [Algebra.FiniteType k S]
    (f : S' →ₐ[k] S) (hf : Function.Surjective f)
    (p : PrimeSpectrum S) :
    WithBot.unbotD 0 (krullDimensionAt (PrimeSpectrum.comap f.toRingHom p)) -
        WithBot.unbotD 0 (krullDimensionAt p) =
      (PrimeSpectrum.comap f.toRingHom p).asIdeal.height - p.asIdeal.height := by
  sorry

/-! ## Base change by a field extension -/

/- The global Krull dimension is unchanged by extension of the ground field. -/
theorem dimension_preserved_field_extension
    {k S K : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [Field K] [Algebra k K] :
    ringKrullDim S = ringKrullDim (K ⊗[k] S) := by
  sorry

/- The local dimension is unchanged at corresponding points after base change.
   The right tensor inclusion is the map defining “lying over” here. -/
theorem dimension_at_a_point_preserved_field_extension
    {k S K : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [Field K] [Algebra k K]
    (q : PrimeSpectrum S)
    (qK : PrimeSpectrum (K ⊗[k] S))
    (hlying :
      PrimeSpectrum.comap
          (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := S)).toRingHom qK =
        q) :
    krullDimensionAt q = krullDimensionAt qK := by
  sorry

/- The local fibre dimension is both the difference of local Krull
   dimensions and the difference of the corresponding transcendence degrees;
   a prime minimal over the extended prime gives fibre dimension zero. -/
theorem inequalities_under_field_extension
    {k S K : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [Field K] [Algebra k K]
    (q : PrimeSpectrum S)
    (qK : PrimeSpectrum (K ⊗[k] S))
    (hlying :
      PrimeSpectrum.comap
          (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := S)).toRingHom qK =
        q) :
    WithBot.unbotD 0
          (ringKrullDim
            (Formalization.Books.Algebra.Unit112.tensorLocalRingOfFibre
              (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := S)).toRingHom
              q qK hlying)) =
        WithBot.unbotD 0 (ringKrullDim (Localization.AtPrime qK.asIdeal)) -
          WithBot.unbotD 0 (ringKrullDim (Localization.AtPrime q.asIdeal)) ∧
      WithBot.unbotD 0 (ringKrullDim (Localization.AtPrime qK.asIdeal)) -
          WithBot.unbotD 0 (ringKrullDim (Localization.AtPrime q.asIdeal)) =
        Cardinal.toENat (Algebra.trdeg k q.asIdeal.ResidueField) -
          Cardinal.toENat (Algebra.trdeg K qK.asIdeal.ResidueField) ∧
      ∃ qK' : PrimeSpectrum (K ⊗[k] S),
        ∃ hlying' : PrimeSpectrum.comap
              (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := S)).toRingHom qK' =
            q,
          WithBot.unbotD 0
              (ringKrullDim
                (Formalization.Books.Algebra.Unit112.tensorLocalRingOfFibre
                  (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := S)).toRingHom
                  q qK' hlying')) = 0 := by
  sorry

end

end Formalization.Books.Algebra.Unit116
