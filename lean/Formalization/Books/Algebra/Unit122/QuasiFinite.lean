import Formalization.Books.Algebra.Unit14.BaseChange
import Formalization.Books.Algebra.Unit17.Spectrum
import Formalization.Books.Topology.Unit26.Miscellany
import Formalization.Books.Algebra.Unit30.MoreOnImages
import Formalization.Books.Algebra.Unit99.CriteriaForFlatness
import Formalization.Books.Algebra.Unit112.HomomorphismsAndDimension
import Formalization.Books.Algebra.Unit113.DimensionFormula
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Commutative Algebra, Chapter 122: Quasi-finite maps

The fibre of a ring map at a prime is represented by Mathlib's canonical
`Ideal.Fiber` construction.  The point of that fibre corresponding to a prime
of the target is the earlier `tensorFibrePrime` interface, and its local ring
is `tensorLocalRingOfFibre`.  The quasi-finite predicates below use those
canonical constructions and Mathlib's `RingHom.FiniteType` and `Module.Finite`.
-/

namespace Formalization.Books.Algebra.Unit122

open Set
open Formalization.Books.Topology.Unit26
open scoped TensorProduct

universe u v

noncomputable section

/-! ## Isolated points and fibres -/

/- The decomposition and localization assertions at the end of the source
   lemma are included with the six equivalent conditions rather than hidden
   in a proof-only interface. -/
theorem isolated_point_criteria
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (q : PrimeSpectrum S) :
    List.TFAE
        [ IsolatedPoint q,
          Module.Finite k (Localization.AtPrime q.asIdeal),
          ∃ g : S, g ∉ q.asIdeal ∧
            (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) = {q},
          Formalization.Books.Topology.Unit10.krullDimensionAt q = 0,
          IsClosed ({q} : Set (PrimeSpectrum S)) ∧
            ringKrullDim (Localization.AtPrime q.asIdeal) = 0,
          Module.Finite k q.asIdeal.ResidueField ∧
            ringKrullDim (Localization.AtPrime q.asIdeal) = 0 ] ∧
      (∀ hq : IsolatedPoint q,
        ∃ (S' : Type u) (hS' : CommRing S') (hA' : Algebra k S'),
          letI : CommRing S' := hS'
          letI : Algebra k S' := hA'
          Nonempty
              (S ≃+* (Localization.AtPrime q.asIdeal × S')) ∧
            Algebra.FiniteType k S' ∧
              ∀ g : S, g ∉ q.asIdeal →
                (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) = {q} →
                  Nonempty
                    (Localization.AtPrime q.asIdeal ≃+*
                      Localization.Away g)) := by
  sorry

/- The map from `R_f` to `S_{f g}` is the canonical localization map from
   Chapter 30.  The target prime is the unique extension of `q` to the
   standard open, written using the Chapter 17 homeomorphism. -/
noncomputable def localizedPrimeAwayMul
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) (a : R) (b : S)
    (ha : a ∉ p.asIdeal) (hb : b ∉ q.asIdeal) :
    PrimeSpectrum (Localization.Away (f a * b)) := by
  have hfa : f a ∉ q.asIdeal := by
    intro hfa
    apply ha
    have hmem : a ∈ (PrimeSpectrum.comap f q).asIdeal := by
      simpa [PrimeSpectrum.comap_asIdeal] using hfa
    simpa [hq] using hmem
  have hprod : f a * b ∉ q.asIdeal := by
    intro hprod
    rcases q.isPrime.mem_or_mem hprod with hfa' | hb'
    · exact hfa hfa'
    · exact hb hb'
  exact Formalization.Books.Algebra.Unit17.standardOpenSpectrumInverse
    (f a * b) ⟨q, (PrimeSpectrum.mem_basicOpen (f a * b) q).mpr hprod⟩

theorem isolated_point_fibre_criteria
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p)
    (hfinite : RingHom.FiniteType f) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
      (Formalization.Books.Algebra.Unit113.residueFieldMapAt f p q hq).toAlgebra
    List.TFAE
      [ IsolatedPoint
          (Formalization.Books.Algebra.Unit112.tensorFibrePrime f p q hq),
        Module.Finite p.asIdeal.ResidueField
          (Formalization.Books.Algebra.Unit112.tensorLocalRingOfFibre f p q hq),
        ∃ g : S, g ∉ q.asIdeal ∧
          ∀ q' : PrimeSpectrum S,
            q' ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) →
              PrimeSpectrum.comap f q' = p → q' = q,
        Formalization.Books.Topology.Unit10.krullDimensionAt
            (Formalization.Books.Algebra.Unit112.tensorFibrePrime f p q hq) = 0,
        IsClosed
            ({Formalization.Books.Algebra.Unit112.tensorFibrePrime f p q hq} :
              Set (PrimeSpectrum (p.asIdeal.Fiber S))) ∧
          ringKrullDim
              (Formalization.Books.Algebra.Unit112.tensorLocalRingOfFibre f p q hq) = 0,
        Module.Finite p.asIdeal.ResidueField q.asIdeal.ResidueField ∧
          ringKrullDim
              (Formalization.Books.Algebra.Unit112.tensorLocalRingOfFibre f p q hq) = 0 ] := by
  sorry

/-! ## Quasi-finite maps -/

/- The source defines quasi-finiteness at a prime only after assuming finite
   type.  The standalone predicate retains that hypothesis and records the
   isolated point of the canonical fibre. -/
def IsQuasiFiniteAt
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (q : PrimeSpectrum S) : Prop :=
  RingHom.FiniteType f ∧
    ∃ p : PrimeSpectrum R, ∃ hq : PrimeSpectrum.comap f q = p,
      IsolatedPoint
        (Formalization.Books.Algebra.Unit112.tensorFibrePrime f p q hq)

def IsQuasiFinite
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  RingHom.FiniteType f ∧ ∀ q : PrimeSpectrum S, IsQuasiFiniteAt f q

theorem quasiFiniteAt_above_prime_criteria
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R)
    (hfinite : RingHom.FiniteType f) :
    letI : Algebra R S := f.toAlgebra
    List.TFAE
      [ ∀ q : PrimeSpectrum S,
          PrimeSpectrum.comap f q = p → IsQuasiFiniteAt f q,
        Module.Finite p.asIdeal.ResidueField (p.asIdeal.Fiber S),
        Finite (PrimeSpectrum (p.asIdeal.Fiber S)) ] := by
  sorry

theorem isQuasiFinite_iff_finite_fibres
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : RingHom.FiniteType f) :
    letI : Algebra R S := f.toAlgebra
    IsQuasiFinite f ↔
      ∀ p : PrimeSpectrum R,
        Module.Finite p.asIdeal.ResidueField (p.asIdeal.Fiber S) := by
  sorry

theorem quasiFiniteAt_localization_iff
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p)
    (a : R) (ha : a ∉ p.asIdeal) (b : S) (hb : b ∉ q.asIdeal)
    (hfinite : RingHom.FiniteType f) :
    IsQuasiFiniteAt f q ↔
      IsQuasiFiniteAt (Formalization.Books.Algebra.Unit30.localizationAwayMulMap f a b)
        (localizedPrimeAwayMul f p q hq a b ha hb) := by
  sorry

/- The four-ring diagram uses the canonical tensor-product map already
   supplied by Chapter 99. -/
theorem quasiFiniteAt_of_surjective_tensorProduct
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (g : R →+* R') (h : S →+* S') (k : R' →+* S')
    (compat : h.comp f = k.comp g)
    (hfinite : RingHom.FiniteType f)
    (hsurj : Function.Surjective
      (Formalization.Books.Algebra.Unit99.tensorProductToSquareTarget
        f g h k compat))
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (p' : PrimeSpectrum R') (q' : PrimeSpectrum S')
    (hqp : PrimeSpectrum.comap f q = p)
    (hp'p : PrimeSpectrum.comap g p' = p)
    (hq'q : PrimeSpectrum.comap h q' = q)
    (hq'p' : PrimeSpectrum.comap k q' = p')
    (hq : IsQuasiFiniteAt f q) :
    IsQuasiFiniteAt k q' := by
  sorry

theorem isQuasiFinite_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (hf : IsQuasiFinite f) (hg : IsQuasiFinite g) :
    IsQuasiFinite (g.comp f) := by
  sorry

theorem isQuasiFinite_baseChange
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (hfinite : RingHom.FiniteType f) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    ({q' : PrimeSpectrum (S ⊗[R] R') |
        IsQuasiFiniteAt
          (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g) q'} :
        Set (PrimeSpectrum (S ⊗[R] R'))) =
      (PrimeSpectrum.comap
          (Formalization.Books.Algebra.Unit14.baseChangeAlgebraMap f g)) ⁻¹'
        {q : PrimeSpectrum S | IsQuasiFiniteAt f q} ∧
      (Function.Surjective (PrimeSpectrum.comap g) →
        (IsQuasiFinite f ↔
          IsQuasiFinite
            (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g))) ∧
      (IsQuasiFinite f →
        IsQuasiFinite
          (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g)) := by
  sorry

theorem quasiFiniteAt_of_finite_composite
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (hfinite : RingHom.FiniteType (g.comp f))
    (p : PrimeSpectrum A) (q : PrimeSpectrum B) (r : PrimeSpectrum C)
    (hqp : PrimeSpectrum.comap f q = p)
    (hrq : PrimeSpectrum.comap g r = q)
    (hquasi : IsQuasiFiniteAt (g.comp f) r) :
    IsQuasiFiniteAt g r := by
  sorry

/- A minimal prime is represented by membership in the canonical
   `minimalPrimes` set, and the localized finite map is Mathlib's
   `Localization.awayMap`. -/
theorem exists_finite_localization_of_finite_fibre_over_minimal_prime
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R)
    (hp : p.asIdeal ∈ minimalPrimes R)
    (hfiniteType : RingHom.FiniteType f)
    (hfibre : Set.Finite
      {q : PrimeSpectrum S | PrimeSpectrum.comap f q = p}) :
    ∃ a : R, a ∉ p.asIdeal ∧ RingHom.Finite (Localization.awayMap f a) := by
  sorry

end

end Formalization.Books.Algebra.Unit122
