import Formalization.Books.Algebra.Unit143.EtaleRingMaps
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Etale.StandardEtale

/-!
# Commutative Algebra, Chapter 144: Local structure of étale ring maps

The source's standard étale presentation is expressed through Mathlib's
canonical `StandardEtalePair` and `Algebra.IsStandardEtale` interfaces.  The
canonical pair also supplies the equivalent polynomial-quotient/localization
presentations used by the source.
-/

namespace Formalization.Books.Algebra.Unit144

open Set
open scoped TensorProduct

noncomputable section

universe u v

/-! ## Standard étale presentations -/

/- The source's pair `(f, g)` is Mathlib's `StandardEtalePair`; its `Ring`
   is the canonical presentation, with equivalences to both
   `R[X][1/g]/(f)` and `R[X]/(f)[1/g]`.  Using that API avoids a parallel
   quotient/localization construction and retains the source's polynomial
   condition in the pair's `cond` field. -/

/-- The canonical ring map in a standard étale presentation. -/
def standardEtaleMap
    {R : Type u} [CommRing R] (P : StandardEtalePair R) :
    R →+* P.Ring :=
  algebraMap R P.Ring

/-- The standard étale algebra attached to a standard étale pair is standard
étale in Mathlib's presentation-independent sense. -/
theorem standardEtaleMap_isStandardEtale
    {R : Type u} [CommRing R] (P : StandardEtalePair R) :
    Algebra.IsStandardEtale R P.Ring := by
  infer_instance

/-- A standard étale presentation gives an étale ring map. -/
theorem standardEtaleMap_isEtale
    {R : Type u} [CommRing R] (P : StandardEtalePair R) :
    RingHom.Etale (standardEtaleMap P) := by
  sorry

/-- Standard étale algebras are stable under base change. -/
theorem standardEtale_baseChange
    {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
    (P : StandardEtalePair R) :
    Algebra.IsStandardEtale R' (R' ⊗[R] P.Ring) := by
  sorry

/-- A principal localization of a standard étale algebra is standard étale. -/
theorem standardEtale_localization
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (h : Algebra.IsStandardEtale R S) :
    ∀ s : S, Algebra.IsStandardEtale R (Localization.Away s) := by
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
  first_standard : Algebra.IsStandardEtale k K
  second_standard : Algebra.IsStandardEtale K (K × K × K × K)
  composite_not_standard :
    letI : Algebra k (K × K × K × K) :=
      ((diagonalFourRingHom K).comp (algebraMap k K)).toAlgebra
    ¬ Algebra.IsStandardEtale k (K × K × K × K)

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
  R' : Type u
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
      Algebra.IsStandardEtale R (Localization.Away g) := by
  sorry

/-! ## Finite flat covers -/

/-- Common finiteness and surjectivity data for the finite flat algebras in the
last two lemmas of the source section. -/
structure FiniteFlatZariskiCover
    {R : Type u} [CommRing R] where
  S' : Type u
  [commRingS' : CommRing S']
  [algebraRS' : Algebra R S']
  finite : RingHom.Finite (algebraMap R S')
  finitePresentation : RingHom.FinitePresentation (algebraMap R S')
  flat : RingHom.Flat (algebraMap R S')
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
    (f : R →+* S)
    (h : letI : Algebra R S := f.toAlgebra; Algebra.IsStandardEtale R S) :
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
