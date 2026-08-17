import Formalization.Books.Algebra.Unit143.EtaleRingMaps
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Commutative Algebra, Chapter 144: Local structure of étale ring maps

The source's standard étale presentation is expressed using the canonical
polynomial quotient and principal localization.  The map-level predicate
`IsStandardEtale` records an arbitrary algebra which is isomorphic to such a
presentation; this is needed for the localization and neighborhood statements
in the section.
-/

namespace Formalization.Books.Algebra.Unit144

open Set
open scoped TensorProduct

noncomputable section

universe u v

/-! ## Standard étale presentations -/

/-- The quotient `R[X] / (f)` used in a standard étale presentation. -/
abbrev PolynomialQuotient (R : Type u) [CommRing R] (f : Polynomial R) : Type u :=
  Polynomial R ⧸ Ideal.span ({f} : Set (Polynomial R))

/-- The image of a polynomial in the quotient by `(f)`. -/
def polynomialQuotientMk
    {R : Type u} [CommRing R] {f : Polynomial R} (p : Polynomial R) :
    PolynomialQuotient R f :=
  Ideal.Quotient.mk _ p

/-- The algebra `R[X]_g/(f)`, written as the localization of the polynomial
quotient at the image of `g`. -/
abbrev StandardEtaleAlgebra
    (R : Type u) [CommRing R] (f g : Polynomial R) : Type u :=
  Localization.Away (polynomialQuotientMk (f := f) g)

/-- The image of the derivative of `f` in a standard étale algebra. -/
def standardEtaleDerivative
    {R : Type u} [CommRing R] (f g : Polynomial R) :
    StandardEtaleAlgebra R f g :=
  algebraMap (PolynomialQuotient R f) (StandardEtaleAlgebra R f g)
    (polynomialQuotientMk (f := f) (Polynomial.derivative f))

/-- The polynomial condition in the source definition of standard étale. -/
def IsStandardEtalePresentation
    {R : Type u} [CommRing R] (f g : Polynomial R) : Prop :=
  f.Monic ∧ IsUnit (standardEtaleDerivative f g)

/-- The canonical ring map in a standard étale presentation. -/
def standardEtaleMap
    (R : Type u) [CommRing R] (f g : Polynomial R) :
    R →+* StandardEtaleAlgebra R f g :=
  algebraMap R (StandardEtaleAlgebra R f g)

/-- A ring map is standard étale when its target is algebra-isomorphic to a
standard étale polynomial presentation. -/
def IsStandardEtale
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  ∃ (p q : Polynomial R),
    IsStandardEtalePresentation p q ∧
      Nonempty (S ≃ₐ[R] StandardEtaleAlgebra R p q)

/-- The source's standard étale map is standard étale by its presentation. -/
theorem standardEtaleMap_isStandardEtale
    {R : Type u} [CommRing R] (f g : Polynomial R)
    (h : IsStandardEtalePresentation f g) :
    IsStandardEtale (standardEtaleMap R f g) := by
  sorry

/-- A standard étale presentation gives an étale ring map. -/
theorem standardEtaleMap_isEtale
    {R : Type u} [CommRing R] (f g : Polynomial R)
    (h : IsStandardEtalePresentation f g) :
    RingHom.Etale (standardEtaleMap R f g) := by
  sorry

/-- Standard étale maps are stable under base change, with coefficients
mapped along the base ring map. -/
theorem standardEtale_baseChange
    {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
    (f g : Polynomial R) (h : IsStandardEtalePresentation f g) :
    IsStandardEtale
      (algebraMap R'
        (StandardEtaleAlgebra R'
          (f.map (algebraMap R R')) (g.map (algebraMap R R')))) := by
  sorry

/-- A principal localization of a standard étale algebra is standard étale. -/
theorem standardEtale_localization
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (h : IsStandardEtale f) :
    letI : Algebra R S := f.toAlgebra
    ∀ s : S, IsStandardEtale (algebraMap R (Localization.Away s)) := by
  sorry

/-! ## The composition warning -/

/-- The diagonal map into a four-fold product. -/
def diagonalFourRingHom (R : Type u) [CommRing R] :
    R →+* R × R × R × R :=
  { toFun := fun r => (r, r, r, r)
    map_one' := by rfl
    map_mul' := by intro x y; rfl
    map_zero' := by rfl
    map_add' := by intro x y; rfl }

/-- The finite quadratic-field data used by the source's
`\mathbf{F}_2 \subset \mathbf{F}_{2^2}` composition example. -/
structure StandardEtaleCompositionCounterexample where
  k : Type u
  K : Type u
  [fieldk : Field k]
  [fieldK : Field K]
  [algebraK : Algebra k K]
  [finiteDimensional : FiniteDimensional k K]
  [separable : Algebra.IsSeparable k K]
  [fintypek : Fintype k]
  [fintypeK : Fintype K]
  card_k : Fintype.card k = 2
  card_K : Fintype.card K = 4
  finrank : Module.finrank k K = 2
  first_standard : IsStandardEtale (algebraMap k K)
  second_standard : IsStandardEtale (diagonalFourRingHom K)
  composite_not_standard :
    ¬ IsStandardEtale ((diagonalFourRingHom K).comp (algebraMap k K))

/-- The composition of standard étale maps need not be standard étale. -/
theorem standardEtale_composition_counterexample :
    Nonempty StandardEtaleCompositionCounterexample := by
  sorry

/-! ## Prescribed residue fields -/

/-- Data for an étale extension with a prescribed finite separable residue
field at a prime. -/
structure PrescribedResidueFieldEtaleData
    (R : Type u) [CommRing R] (p : PrimeSpectrum R)
    (L : Type v) [Field L] [Algebra p.asIdeal.ResidueField L] where
  R' : Type v
  [commRingR' : CommRing R']
  [algebraRR' : Algebra R R']
  etale : RingHom.Etale (algebraMap R R')
  p' : PrimeSpectrum R'
  liesOver : PrimeSpectrum.comap (algebraMap R R') p' = p
  residueEquiv :
    letI : Algebra p.asIdeal.ResidueField p'.asIdeal.ResidueField :=
      (Formalization.Books.Algebra.Unit113.residueFieldMapAt
        (algebraMap R R') p p' liesOver).toAlgebra
    Nonempty
      (p'.asIdeal.ResidueField ≃ₐ[p.asIdeal.ResidueField] L)

/-- Every finite separable extension of a residue field occurs as the residue
field extension of an étale map. -/
theorem exists_etale_with_prescribed_residue_field
    {R : Type u} [CommRing R] (p : PrimeSpectrum R)
    (L : Type v) [Field L] [Algebra p.asIdeal.ResidueField L]
    [Module.Finite p.asIdeal.ResidueField L]
    [Algebra.IsSeparable p.asIdeal.ResidueField L] :
    Nonempty (PrescribedResidueFieldEtaleData R p L) := by
  sorry

/-! ## Local standard étale structure -/

/-- Étaleness at a prime has a standard étale principal neighborhood. -/
theorem etaleAt_standardEtale_neighborhood
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) (h : Formalization.Books.Algebra.Unit143.IsEtaleAt R S q) :
    ∃ g : S, g ∉ q.asIdeal ∧
      IsStandardEtale (algebraMap R (Localization.Away g)) := by
  sorry

/-! ## Finite flat covers -/

/-- Common finiteness and surjectivity data for the finite flat algebras in the
last two lemmas of the source section. -/
structure FiniteFlatZariskiCover
    {R : Type u} [CommRing R] where
  S' : Type v
  [commRingS' : CommRing S']
  [algebraRS' : Algebra R S']
  finite : RingHom.Finite (algebraMap R S')
  finitePresentation : RingHom.FinitePresentation (algebraMap R S')
  flat : RingHom.Flat (algebraMap R S')
  finiteProjective : Formalization.Books.Algebra.Unit78.FiniteProjective R S'
  specSurjective :
    Function.Surjective (PrimeSpectrum.comap (algebraMap R S'))

/-- A finite flat cover adapted to a standard étale map. -/
structure StandardEtaleFiniteFlatZariskiData
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) extends FiniteFlatZariskiCover (R := R) where
  localFactor :
    ∀ (q : PrimeSpectrum S) (q' : PrimeSpectrum S'),
      PrimeSpectrum.comap f q =
        PrimeSpectrum.comap (algebraMap R S') q' →
      ∃ g' : S', g' ∉ q'.asIdeal ∧
        ∃ φ : S →+* Localization.Away g',
          φ.comp f = algebraMap R (Localization.Away g') ∧
          Ideal.comap φ
              (Ideal.map (algebraMap S' (Localization.Away g')) q'.asIdeal) =
            q.asIdeal

/-- A standard étale map admits the finite flat/Zariski cover described in the
source. -/
theorem standardEtale_finiteFlatZariski
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (h : IsStandardEtale f) :
    Nonempty (StandardEtaleFiniteFlatZariskiData f) := by
  sorry

/-- A surjective étale map admits a finite flat/Zariski cover which locally
factors through the original map. -/
structure EtaleFiniteFlatZariskiData
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) extends FiniteFlatZariskiCover (R := R) where
  localFactor :
    ∀ q' : PrimeSpectrum S',
      ∃ g' : S', g' ∉ q'.asIdeal ∧
        ∃ φ : S →+* Localization.Away g',
          φ.comp f = algebraMap R (Localization.Away g')

theorem etale_finiteFlatZariski
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hEtale : RingHom.Etale f)
    (hsurjective : Function.Surjective (PrimeSpectrum.comap f)) :
    Nonempty (EtaleFiniteFlatZariskiData f) := by
  sorry

end

end Formalization.Books.Algebra.Unit144
