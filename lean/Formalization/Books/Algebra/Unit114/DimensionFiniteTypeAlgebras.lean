import Formalization.Books.Algebra.Unit104.CohenMacaulayRings
import Formalization.Books.Algebra.Unit110.RegularRingsAndGlobalDimension
import Formalization.Books.Algebra.Unit113.DimensionFormula
import Formalization.Books.Topology.Unit10.KrullDimension
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.Topology.Clopen

/-!
# Commutative Algebra, Chapter 114: Dimension of finite type algebras over fields

The polynomial algebra in `n` variables is represented by
`MvPolynomial (Fin n) k`.  Krull dimensions use Mathlib's `ringKrullDim`,
prime heights use `Ideal.height`, and local dimensions of spectra use the
topological `krullDimensionAt` from Topology, Chapter 10.
-/

namespace Formalization.Books.Algebra.Unit114

universe u v

noncomputable section

open Set
open Formalization.Books.Topology.Unit10
open Formalization.Books.Topology.Unit11

/-! ## Local dimensions and components -/

/- The source's maximum over irreducible components through a point is the
   set of their canonical topological Krull dimensions. -/
def componentDimensionsAtPoint
    {X : Type u} [TopologicalSpace X] (x : X) : Set (WithBot ℕ∞) :=
  {d | ∃ Z : Set X,
    Z ∈ irreducibleComponents X ∧ x ∈ Z ∧ topologicalKrullDim Z = d}

/- The source's minimum over maximal localizations above a prime is recorded
   using the canonical maximal spectrum and localization at that ideal. -/
def maximalLocalDimensionsAbove
    {S : Type u} [CommRing S] (p : PrimeSpectrum S) : Set (WithBot ℕ∞) :=
  {d | ∃ m : MaximalSpectrum S,
    p.asIdeal ≤ m.asIdeal ∧
      ringKrullDim (Localization.AtPrime m.asIdeal) = d}

/-! ## The dimension of affine space -/

/-- A maximal ideal of affine `n`-space has `n` generators and its local ring
has dimension `n` and is regular local. -/
theorem dim_affine_space
    {k : Type u} [Field k] (n : ℕ)
    (m : MaximalSpectrum (MvPolynomial (Fin n) k)) :
    (∃ x : Fin n → MvPolynomial (Fin n) k,
        Ideal.span (Set.range x) = m.asIdeal) ∧
      ringKrullDim (Localization.AtPrime m.asIdeal) = n ∧
        IsRegularLocalRing (Localization.AtPrime m.asIdeal) := by
  sorry

/-- A polynomial algebra over a field is regular of global dimension `n`, and
all of its maximal localizations are regular local rings of dimension `n`. -/
theorem finite_gl_dim_polynomial_ring
    {k : Type u} [Field k] (n : ℕ) :
    Formalization.Books.Algebra.Unit110.IsRegularRing
        (MvPolynomial (Fin n) k) ∧
      Formalization.Books.Algebra.Unit109.globalDimension
          (MvPolynomial (Fin n) k) =
        ((n : ℕ∞) : WithBot ℕ∞) ∧
        ∀ m : MaximalSpectrum (MvPolynomial (Fin n) k),
          IsRegularLocalRing (Localization.AtPrime m.asIdeal) ∧
            ringKrullDim (Localization.AtPrime m.asIdeal) =
              ((n : ℕ∞) : WithBot ℕ∞) := by
  sorry

/-! ## Heights and chains in a polynomial algebra -/

/-- In a polynomial algebra over a field, every maximal prime chain between
two primes has length equal to the difference of their heights. -/
theorem dimension_height_polynomial_ring
    {k : Type u} [Field k] {n : ℕ}
    (p q : Ideal (MvPolynomial (Fin n) k))
    (hp : p.IsPrime) (hq : q.IsPrime) (hpq : p < q) :
    ∀ C : LTSeries
        (Set.Iic (⟨q, hq⟩ : PrimeSpectrum (MvPolynomial (Fin n) k))),
      IsMaximalChainBetween
          (⟨p, hp⟩ : PrimeSpectrum (MvPolynomial (Fin n) k))
          (⟨q, hq⟩ : PrimeSpectrum (MvPolynomial (Fin n) k))
          (le_of_lt hpq) C →
        (C.length : ℕ∞) = q.height - p.height := by
  sorry

/-! ## Finite type domains and local dimensions -/

/-- The dimension of a finite-type domain over a field is the dimension of any
of its localizations at maximal ideals. -/
theorem dimension_spell_it_out
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [IsDomain S]
    (m : MaximalSpectrum S) :
    ringKrullDim S = ringKrullDim (Localization.AtPrime m.asIdeal) := by
  sorry

/-- At a point of the spectrum of a finite-type algebra over a field, the
topological local dimension is the maximum component dimension through the
point and the minimum dimension of a maximal localization above it. -/
theorem dimension_at_a_point_finite_type_over_field
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (p : Ideal S) (hp : p.IsPrime) :
    let x : PrimeSpectrum S := ⟨p, hp⟩
    ∃ d : WithBot ℕ∞,
      krullDimensionAt x = d ∧
        IsGreatest (componentDimensionsAtPoint x) d ∧
          IsLeast (maximalLocalDimensionsAbove x) d := by
  sorry

/-- The local dimension at a closed point of a finite-type affine algebra over
a field is the dimension of the corresponding maximal localization. -/
theorem dimension_closed_point_finite_type_field
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (m : MaximalSpectrum S) :
    krullDimensionAt (MaximalSpectrum.toPrimeSpectrum m) =
      ringKrullDim (Localization.AtPrime m.asIdeal) := by
  sorry

/-! ## Cohen--Macaulay finite-type algebras -/

/- The first form of the final lemma is indexed by `Fin (d + 1)`, which is a
   finite presentation of the source's `T₀, ..., T_d`. -/
def HasDisjointEquidimensionalDecomposition
    (S : Type u) [CommRing S] : Prop :=
  ∃ d : ℕ, ringKrullDim S = d ∧
    ∃ T : Fin (d + 1) → Set (PrimeSpectrum S),
      (∀ i, IsClopen (T i) ∧
        ∀ C ∈ irreducibleComponents (T i),
          topologicalKrullDim C = (i.1 : WithBot ℕ∞)) ∧
        (⋃ i, T i) = (Set.univ : Set (PrimeSpectrum S)) ∧
          (∀ i j, i ≠ j → Disjoint (T i) (T j))

/- The equivalent product form of the source's decomposition.  The explicit
   family of commutative-ring structures keeps the product factors usable as
   ordinary Lean types. -/
def HasDimensionProductDecomposition
    (S : Type u) [CommRing S] : Prop :=
  ∃ d : ℕ, ringKrullDim S = d ∧
    ∃ (R : Fin (d + 1) → Type u) (hR : ∀ i, CommRing (R i)),
      letI : ∀ i, CommRing (R i) := hR
      Nonempty (S ≃+* (∀ i, R i)) ∧
        ∀ i : Fin (d + 1),
          ∀ m : MaximalSpectrum (R i),
            m.asIdeal.height = (i.1 : ℕ∞)

/-- A finite-type Cohen--Macaulay algebra over a field decomposes into open
and closed equidimensional pieces, equivalently into ring factors whose
maximal ideals have the corresponding heights. -/
theorem disjoint_decomposition_CM_algebra
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [IsNoetherianRing S]
    (hS : Formalization.Books.Algebra.Unit104.IsCohenMacaulayRing S) :
    HasDisjointEquidimensionalDecomposition S ∧
      (HasDisjointEquidimensionalDecomposition S ↔
        HasDimensionProductDecomposition S) := by
  sorry

end

end Formalization.Books.Algebra.Unit114
