import Formalization.Books.Algebra.Unit17.Spectrum
import Formalization.Books.Algebra.Unit50.ValuationRings
import Formalization.Books.Algebra.Unit112.HomomorphismsAndDimension
import Formalization.Books.Algebra.Unit113.DimensionFormula
import Formalization.Books.Algebra.Unit115.NoetherNormalization
import Formalization.Books.Algebra.Unit116.DimensionFiniteTypeAlgebrasReprise
import Formalization.Books.Algebra.Unit123.ZariskiMain
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.RingHom.QuasiFinite

/-!
# Commutative Algebra, Chapter 125: Dimension of fibres

The relative dimension at a point is the topological Krull dimension of the
canonical point of the canonical tensor-product fibre.  Polynomial algebras
use `MvPolynomial (Fin n)`, and quasi-finiteness uses Mathlib's canonical
`RingHom.QuasiFinite` and `RingHom.QuasiFiniteAt` predicates.
-/

namespace Formalization.Books.Algebra.Unit125

open Set
open Formalization.Books.Topology.Unit10
open scoped TensorProduct

universe u v

noncomputable section

/-! ### Relative dimension -/

/-- The relative dimension of `S/R` at a prime `q` over `p`. -/
noncomputable def relativeDimensionAt
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (_hfinite : RingHom.FiniteType f)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) : WithBot ℕ∞ :=
  krullDimensionAt
    (Formalization.Books.Algebra.Unit112.tensorFibrePrime f p q hq)

/-- The supremum of the relative dimensions of all fibres of `S/R`. -/
noncomputable def relativeDimension
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : RingHom.FiniteType f) : WithBot ℕ∞ :=
  ⨆ q : PrimeSpectrum S,
    relativeDimensionAt f hfinite (PrimeSpectrum.comap f q) q rfl

/-- The locus where the relative fibre dimension is at most `n`. -/
noncomputable def relativeDimensionLocus
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : RingHom.FiniteType f) (n : ℕ) :
    Set (PrimeSpectrum S) :=
  {q | relativeDimensionAt f hfinite (PrimeSpectrum.comap f q) q rfl ≤ n}

/-- The prime obtained by extending a prime to a standard localization. -/
noncomputable def localizedPrimeAway
    {S : Type u} [CommRing S] (q : PrimeSpectrum S) (g : S)
    (hg : g ∉ q.asIdeal) : PrimeSpectrum (Localization.Away g) :=
  Formalization.Books.Algebra.Unit17.standardOpenSpectrumInverse g
    ⟨q, (PrimeSpectrum.mem_basicOpen g q).mpr hg⟩

/- A base map into a target standard localization.  The divisibility witness
   is the compatibility needed to extend `R → S` across the two localizations. -/
noncomputable def localizedBaseMap
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (a : R) (g : S) (hdiv : f a ∣ g) :
    Localization.Away a →+* Localization.Away g :=
  Localization.awayLift
    ((algebraMap S (Localization.Away g)).comp f) a
    (IsLocalization.Away.isUnit_of_dvd
      (S := Localization.Away g) (x := g) (r := f a) hdiv)

/-- For a finite-type map, quasi-finiteness at a point is equivalent to zero
relative dimension there. -/
theorem quasiFiniteAt_iff_relativeDimensionAt_eq_zero
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : RingHom.FiniteType f)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) :
    RingHom.QuasiFiniteAt f q.asIdeal ↔
      relativeDimensionAt f hfinite p q hq = 0 := by
  sorry

/-! ### Quasi-finite polynomial covers -/

/-- A point of relative dimension `n` has a standard neighbourhood which is
quasi-finite over an `n`-variable polynomial algebra over the base. -/
theorem quasiFinite_over_polynomial_algebra
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : RingHom.FiniteType f)
    (q : PrimeSpectrum S) {n : ℕ}
    (hdim :
      relativeDimensionAt f hfinite (PrimeSpectrum.comap f q) q rfl = n) :
    letI : Algebra R S := f.toAlgebra
    ∃ g : S, g ∉ q.asIdeal ∧
      ∃ φ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g,
        RingHom.QuasiFinite φ.toRingHom := by
  sorry

/-- The refined polynomial cover whose point contracts to the base prime and
the variables after the residue-field transcendence degree. -/
theorem refined_quasiFinite_over_polynomial_algebra
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : RingHom.FiniteType f)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
      (Formalization.Books.Algebra.Unit113.residueFieldMapAt f p q hq).toAlgebra
    ∀ {n r : ℕ},
      relativeDimensionAt f hfinite p q hq = n →
        Algebra.trdeg p.asIdeal.ResidueField q.asIdeal.ResidueField = r →
          ∃ a : R, a ∉ p.asIdeal ∧
            ∃ g : S, ∃ hg : g ∉ q.asIdeal, ∃ hdiv : f a ∣ g,
              let α := localizedBaseMap f a g hdiv
              letI : Algebra (Localization.Away a) (Localization.Away g) :=
                α.toAlgebra
              ∃ φ : MvPolynomial (Fin n) (Localization.Away a) →ₐ[
                  Localization.Away a] Localization.Away g,
                RingHom.QuasiFinite φ.toRingHom ∧
                  Ideal.comap φ.toRingHom
                      (localizedPrimeAway q g hg).asIdeal =
                    (p.asIdeal.map (algebraMap R (Localization.Away a))).map
                        (MvPolynomial.C : Localization.Away a →+*
                          MvPolynomial (Fin n) (Localization.Away a)) +
                      Formalization.Books.Algebra.Unit115.tailVariableIdeal
                        (Localization.Away a) n r := by
  sorry

/-! ### Dimension inequalities -/

/-- A quasi-finite finite-type map cannot increase the dimension of a local
ring. -/
theorem ringKrullDim_localization_le_of_quasiFiniteAt
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (_hfinite : RingHom.FiniteType f)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p)
    (hquasi : RingHom.QuasiFiniteAt f q.asIdeal) :
    ringKrullDim (Localization.AtPrime q.asIdeal) ≤
      ringKrullDim (Localization.AtPrime p.asIdeal) := by
  sorry

/-- A quasi-finite cover of affine `n`-space has Krull dimension at most `n`. -/
theorem ringKrullDim_le_of_quasiFinite_polynomial
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (n : ℕ)
    (φ : MvPolynomial (Fin n) k →ₐ[k] S)
    (hquasi : RingHom.QuasiFinite φ.toRingHom) :
    ringKrullDim S ≤ n := by
  sorry

/-! ### Openness and base change of bounded fibre dimension -/

/-- Around a point where the fibre has dimension `n`, the fibre dimensions are
bounded above by `n` on an open neighbourhood. -/
theorem relativeDimensionLocus_isOpen_near
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : RingHom.FiniteType f)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) {n : ℕ}
    (hdim : relativeDimensionAt f hfinite p q hq = n) :
    ∃ V : Set (PrimeSpectrum S), IsOpen V ∧ q ∈ V ∧
      ∀ q' : PrimeSpectrum S, q' ∈ V →
        relativeDimensionAt f hfinite (PrimeSpectrum.comap f q') q' rfl ≤ n := by
  sorry

/-- The bounded relative-dimension locus is open. -/
theorem isOpen_relativeDimensionLocus
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : RingHom.FiniteType f) (n : ℕ) :
    IsOpen (relativeDimensionLocus f hfinite n) := by
  sorry

/-- Formation of the bounded relative-dimension locus commutes with arbitrary
base change. -/
theorem relativeDimensionLocus_baseChange
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (hfinite : RingHom.FiniteType f)
    (n : ℕ) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    (PrimeSpectrum.comap
        (Formalization.Books.Algebra.Unit14.baseChangeAlgebraMap f g)) ⁻¹'
        relativeDimensionLocus f hfinite n =
      relativeDimensionLocus
        (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g)
        (Formalization.Books.Algebra.Unit14.baseChange_finite_type f g hfinite) n := by
  sorry

/-- For a finitely presented map, the bounded relative-dimension locus is a
quasi-compact open. -/
theorem isOpen_isCompact_relativeDimensionLocus_of_finitePresentation
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinitePresentation : RingHom.FinitePresentation f)
    (n : ℕ) :
    IsOpen
        (relativeDimensionLocus f
          (RingHom.FiniteType.of_finitePresentation hfinitePresentation) n) ∧
      IsCompact
        (relativeDimensionLocus f
          (RingHom.FiniteType.of_finitePresentation hfinitePresentation) n) := by
  sorry

/-! ### Finite-type domains over valuation rings -/

/-- For a finite-type domain over a valuation ring, the generic and special
fibres have the same dimension; the special fibre is equidimensional. -/
theorem finiteType_domain_over_valuationRing_dimension_fibres
    {R S : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    [CommRing S] [IsDomain S] [Algebra R S]
    (hinjective : Function.Injective (algebraMap R S))
    (hfinite : RingHom.FiniteType (algebraMap R S))
    (hnonzero : Nontrivial (S ⊗[R] IsLocalRing.ResidueField R)) :
    ringKrullDim (S ⊗[R] IsLocalRing.ResidueField R) =
        ringKrullDim (S ⊗[R] FractionRing R) ∧
      Formalization.Books.Topology.Unit10.Equidimensional
        (X := PrimeSpectrum (S ⊗[R] IsLocalRing.ResidueField R)) := by
  sorry

end

end Formalization.Books.Algebra.Unit125
