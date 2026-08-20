import Formalization.Books.Algebra.Unit14.BaseChange
import Formalization.Books.Algebra.Unit17.Spectrum
import Formalization.Books.Algebra.Unit50.ValuationRings
import Formalization.Books.Algebra.Unit112.HomomorphismsAndDimension
import Formalization.Books.Algebra.Unit113.DimensionFormula
import Formalization.Books.Algebra.Unit115.NoetherNormalization
import Formalization.Books.Algebra.Unit116.DimensionFiniteTypeAlgebrasReprise
import Formalization.Books.Algebra.Unit122.QuasiFinite
import Formalization.Books.Algebra.Unit123.ZariskiMain
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.RingHom.QuasiFinite

/-!
# Commutative Algebra, Chapter 125: Dimension of fibres

The relative dimension at a point is the topological Krull dimension of the
canonical point of the canonical tensor-product fibre.  Polynomial algebras
use `MvPolynomial (Fin n)`, and quasi-finiteness uses the source-facing
predicates from Chapter 122, which retain the finite-type component of the
source definition while delegating the fibre condition to Mathlib.
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

/-- For a finite-type map, quasi-finiteness at a point is equivalent to zero
relative dimension there. -/
theorem quasiFiniteAt_iff_relativeDimensionAt_eq_zero
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : RingHom.FiniteType f)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) :
    Formalization.Books.Algebra.Unit122.IsQuasiFiniteAt f q ↔
      relativeDimensionAt f hfinite p q hq = 0 := by
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra.FiniteType R S := hfinite
  have hp : PrimeSpectrum.comap (algebraMap R S) q = p := by
    simpa [RingHom.algebraMap_toAlgebra] using hq
  cases hp
  let e := PrimeSpectrum.preimageHomeomorphFiber R S
    (PrimeSpectrum.comap (algebraMap R S) q)
  let x : PrimeSpectrum.comap (algebraMap R S) ⁻¹'
      {PrimeSpectrum.comap (algebraMap R S) q} :=
    ⟨q, rfl⟩
  have hx : e x = Formalization.Books.Algebra.Unit112.tensorFibrePrime f
      (PrimeSpectrum.comap (algebraMap R S) q) q hq := by
    rfl
  have ht := Formalization.Books.Algebra.Unit122.isolated_point_fibre_criteria f
    (PrimeSpectrum.comap (algebraMap R S) q) q hq hfinite
  have hqf := Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber (R := R) q
  have hqf' : Algebra.QuasiFiniteAt R q.asIdeal ↔ IsOpen ({x} : Set _) := by
    convert hqf using 1
  have hdim : IsOpen ({x} : Set _) ↔
      relativeDimensionAt f hfinite (PrimeSpectrum.comap (algebraMap R S) q) q hq = 0 := by
    rw [← e.isOpen_image, Set.image_singleton]
    change Formalization.Books.Topology.Unit26.IsolatedPoint (e x) ↔ _
    rw [hx]
    simpa [relativeDimensionAt] using ht.out 0 3
  change (RingHom.FiniteType f ∧ Algebra.QuasiFiniteAt R q.asIdeal) ↔ _
  constructor
  · intro h
    exact hdim.mp (hqf'.mp h.2)
  · intro h
    exact ⟨hfinite, hqf'.mpr (hdim.mpr h)⟩

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
        Formalization.Books.Algebra.Unit122.IsQuasiFinite φ.toRingHom := by
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
          ∃ a : R, ∃ ha : a ∉ p.asIdeal,
            ∃ b : S, ∃ hb : b ∉ q.asIdeal,
              let α :=
                Formalization.Books.Algebra.Unit30.localizationAwayMulMap f a b
              letI : Algebra (Localization.Away a)
                  (Localization.Away (f a * b)) := α.toAlgebra
              ∃ φ : MvPolynomial (Fin n) (Localization.Away a) →ₐ[
                  Localization.Away a] Localization.Away (f a * b),
                Formalization.Books.Algebra.Unit122.IsQuasiFinite φ.toRingHom ∧
                  Ideal.comap φ.toRingHom
                      (Formalization.Books.Algebra.Unit122.localizedPrimeAwayMul
                        f p q hq a b ha hb).asIdeal =
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
    (f : R →+* S)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p)
    (hquasi : Formalization.Books.Algebra.Unit122.IsQuasiFiniteAt f q) :
    ringKrullDim (Localization.AtPrime q.asIdeal) ≤
      ringKrullDim (Localization.AtPrime p.asIdeal) := by
  let _ : Algebra R S := f.toAlgebra
  rcases hquasi with ⟨hfinite, hqf⟩
  let _ : Algebra.QuasiFiniteAt R q.asIdeal := hqf
  have hqp : q.asIdeal.comap f = p.asIdeal := by
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hq
  let F : Set.Iic q → Set.Iic p := fun r =>
    ⟨PrimeSpectrum.comap f r.1, by
      apply (PrimeSpectrum.asIdeal_le_asIdeal _ _).mp
      change r.1.asIdeal.comap f ≤ p.asIdeal
      calc
        r.1.asIdeal.comap f ≤ q.asIdeal.comap f :=
          Ideal.comap_mono ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr r.2)
        _ = p.asIdeal := hqp⟩
  have hF : StrictMono F := by
    intro a b hab
    change PrimeSpectrum.comap f a.1 < PrimeSpectrum.comap f b.1
    apply lt_of_le_of_ne
    · exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mp
        (Ideal.comap_mono ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hab.le))
    · intro heq
      have hbeq : b.1.asIdeal ≤ q.asIdeal :=
        (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr b.2
      let _ : Algebra.QuasiFiniteAt R b.1.asIdeal :=
        Algebra.QuasiFiniteAt.of_le hbeq
      have habideal : a.1.asIdeal ≤ b.1.asIdeal :=
        (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hab.le
      have hunder : a.1.asIdeal.under R = b.1.asIdeal.under R := by
        rw [Ideal.under_def, Ideal.under_def]
        simpa [PrimeSpectrum.comap_asIdeal, RingHom.algebraMap_toAlgebra] using
          congrArg PrimeSpectrum.asIdeal heq
      have hab' : a.1 = b.1 := by
        apply PrimeSpectrum.ext
        exact Algebra.QuasiFiniteAt.eq_of_le_of_under_eq habideal hunder
      exact hab.ne (Subtype.ext hab')
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height
      q.asIdeal (Localization.AtPrime q.asIdeal),
    IsLocalization.AtPrime.ringKrullDim_eq_height
      p.asIdeal (Localization.AtPrime p.asIdeal)]
  rw [PrimeSpectrum.height_eq_orderHeight q, PrimeSpectrum.height_eq_orderHeight p]
  rw [Order.height_eq_krullDim_Iic q, Order.height_eq_krullDim_Iic p]
  exact Order.krullDim_le_of_strictMono F hF

/-- A quasi-finite cover of affine `n`-space has Krull dimension at most `n`. -/
theorem ringKrullDim_le_of_quasiFinite_polynomial
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (n : ℕ)
    (φ : MvPolynomial (Fin n) k →ₐ[k] S)
    (hquasi : Formalization.Books.Algebra.Unit122.IsQuasiFinite φ.toRingHom) :
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
