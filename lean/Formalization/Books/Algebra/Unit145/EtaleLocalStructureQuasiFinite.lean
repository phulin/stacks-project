import Formalization.Books.Algebra.Unit113.DimensionFormula
import Formalization.Books.Algebra.Unit122.QuasiFinite
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.RingHom.Etale

/-!
# Commutative Algebra, Chapter 145: Étale local structure of quasi-finite ring maps

The four lemmas in the source section are stated below.  The product
presentations keep the algebra structures and the maps from the original
tensor product explicit, so that the assertions about primes are usable by
later chapters.
-/

namespace Formalization.Books.Algebra.Unit145

open Set
open scoped TensorProduct

noncomputable section

universe u

/-! ## 145.1 Étale local structure of quasi-finite ring maps -/

/- The introductory remarks recall the openness and base-change properties of
quasi-finite loci from the preceding quasi-finite chapter; they are not
duplicated here. -/

/-- The source localization map `S'_g → S_g` is represented by the canonical
map between localizations away from an element. -/
abbrev localizedMap
    {S' S : Type u} [CommRing S'] [CommRing S]
    (g : S' →+* S) (s : S') :
    Localization.Away s →+* Localization.Away (g s) :=
  Localization.awayMap g s

/-- A binary product presentation of an algebra over `R`, with its factor
maps retained for transporting primes from the original algebra. -/
structure BinaryAlgebraProduct
    (R X : Type u) [CommRing R] [CommRing X] [Algebra R X] where
  A : Type u
  [commRingA : CommRing A]
  [algebraA : Algebra R A]
  B : Type u
  [commRingB : CommRing B]
  [algebraB : Algebra R B]
  equiv : X ≃ₐ[R] A × B

def BinaryAlgebraProduct.leftMap
    {R X : Type u} [CommRing R] [CommRing X] [Algebra R X]
    (D : BinaryAlgebraProduct R X) :
    letI : CommRing D.A := D.commRingA
    letI : CommRing D.B := D.commRingB
    X →+* D.A := by
  letI : CommRing D.A := D.commRingA
  letI : CommRing D.B := D.commRingB
  exact
    { toFun := fun x => (D.equiv x).1
      map_one' := by simp
      map_mul' := by intro x y; simp
      map_zero' := by simp
      map_add' := by intro x y; simp }

def BinaryAlgebraProduct.rightMap
    {R X : Type u} [CommRing R] [CommRing X] [Algebra R X]
    (D : BinaryAlgebraProduct R X) :
    letI : CommRing D.A := D.commRingA
    letI : CommRing D.B := D.commRingB
    X →+* D.B := by
  letI : CommRing D.A := D.commRingA
  letI : CommRing D.B := D.commRingB
  exact
    { toFun := fun x => (D.equiv x).2
      map_one' := by simp
      map_mul' := by intro x y; simp
      map_zero' := by simp
      map_add' := by intro x y; simp }

/-- After localizing at an element, the finite map supplied by the first
source lemma.  The bijectivity assumption is stronger than the surjectivity
used by Mathlib's `Localization.exists_finite_awayMapₐ_of_surjective_awayMapₐ`,
and records the source's stated isomorphism exactly at the ring-map level. -/
theorem produce_finite
    {R S' S : Type u} [CommRing R] [CommRing S'] [CommRing S]
    (f : R →+* S') (g : S' →+* S) (p : PrimeSpectrum R) (s : S')
    (hintegral : f.IsIntegral)
    (hfiniteType : (g.comp f).FiniteType)
    (hloc : Function.Bijective (localizedMap g s))
    (hinvertible :
      letI : Algebra R S' := f.toAlgebra
      IsUnit (algebraMap S' (S' ⊗[R] p.asIdeal.ResidueField) s)) :
    ∃ r : R, r ∉ p.asIdeal ∧
      RingHom.Finite (Localization.awayMap (g.comp f) r) := by
  sorry

/-- Data for the étale neighborhood and product decomposition around one
quasi-finite prime.  Bijectivity of the canonical residue-field map records
the source's notation `κ(p) = κ(p')`. -/
structure EtaleFiniteAtPrimeData
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) where
  R' : Type u
  [commRingR' : CommRing R']
  [algebraRR' : Algebra R R']
  etale : RingHom.Etale (algebraMap R R')
  p' : PrimeSpectrum R'
  liesOver : PrimeSpectrum.comap (algebraMap R R') p' = p
  residueFieldMapBijective :
    Function.Bijective
      (Formalization.Books.Algebra.Unit113.residueFieldMapAt
        (algebraMap R R') p p' liesOver)
  decomposition : BinaryAlgebraProduct R' (R' ⊗[R] S)
  finiteA : letI : CommRing decomposition.A := decomposition.commRingA
    letI : Algebra R' decomposition.A := decomposition.algebraA
    RingHom.Finite (algebraMap R' decomposition.A)
  uniquePrime : letI : CommRing decomposition.A := decomposition.commRingA
    letI : Algebra R' decomposition.A := decomposition.algebraA
    ∃! r : PrimeSpectrum decomposition.A,
      PrimeSpectrum.comap (algebraMap R' decomposition.A) r = p'
  primeOverQ : letI : CommRing decomposition.A := decomposition.commRingA
    letI : Algebra R' decomposition.A := decomposition.algebraA
    ∀ r : PrimeSpectrum decomposition.A,
      PrimeSpectrum.comap (algebraMap R' decomposition.A) r = p' →
        PrimeSpectrum.comap
            (decomposition.leftMap.comp
              Algebra.TensorProduct.includeRight.toRingHom) r = q
  noPrimeB : letI : CommRing decomposition.B := decomposition.commRingB
    letI : Algebra R' decomposition.B := decomposition.algebraB
    ∀ r : PrimeSpectrum decomposition.B,
      PrimeSpectrum.comap (algebraMap R' decomposition.B) r = p' →
        PrimeSpectrum.comap
            (decomposition.rightMap.comp
              Algebra.TensorProduct.includeRight.toRingHom) r ≠ q

/-- Étale local structure at one quasi-finite prime. -/
theorem etale_makes_quasiFinite_finite_one_prime
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p)
    (hfiniteType : f.FiniteType)
    (hquasi : Formalization.Books.Algebra.Unit122.IsQuasiFiniteAt f q) :
    letI : Algebra R S := f.toAlgebra
    Nonempty (EtaleFiniteAtPrimeData f p q hq) := by
  sorry

/-! The finite-product version is indexed by the finite set of isolated
closed points in the fibre. -/

/-- A finite product presentation of an algebra over `R`. -/
structure FiniteAlgebraProduct
    (R X : Type u) [CommRing R] [CommRing X] [Algebra R X] where
  n : ℕ
  A : Fin n → Type u
  [commRingA : ∀ i, CommRing (A i)]
  [algebraA : ∀ i, Algebra R (A i)]
  B : Type u
  [commRingB : CommRing B]
  [algebraB : Algebra R B]
  equiv : X ≃ₐ[R] (∀ i, A i) × B

def FiniteAlgebraProduct.factorMap
    {R X : Type u} [CommRing R] [CommRing X] [Algebra R X]
    (D : FiniteAlgebraProduct R X) (i : Fin D.n) :
    letI : CommRing (D.A i) := D.commRingA i
    X →+* D.A i := by
  letI : CommRing (D.A i) := D.commRingA i
  letI : ∀ j, CommRing (D.A j) := D.commRingA
  letI : CommRing D.B := D.commRingB
  exact
    { toFun := fun x => (D.equiv x).1 i
      map_one' := by
        change (D.equiv 1).1 i = 1
        exact congrArg (fun z => z.1 i) D.equiv.map_one
      map_mul' := by
        intro x y
        change (D.equiv (x * y)).1 i = (D.equiv x).1 i * (D.equiv y).1 i
        exact congrArg (fun z => z.1 i) (D.equiv.map_mul x y)
      map_zero' := by
        change (D.equiv 0).1 i = 0
        exact congrArg (fun z => z.1 i) D.equiv.map_zero
      map_add' := by
        intro x y
        change (D.equiv (x + y)).1 i = (D.equiv x).1 i + (D.equiv y).1 i
        exact congrArg (fun z => z.1 i) (D.equiv.map_add x y) }

def FiniteAlgebraProduct.remainderMap
    {R X : Type u} [CommRing R] [CommRing X] [Algebra R X]
    (D : FiniteAlgebraProduct R X) :
    letI : CommRing D.B := D.commRingB
    X →+* D.B := by
  letI : CommRing D.B := D.commRingB
  letI : ∀ i, CommRing (D.A i) := D.commRingA
  exact
    { toFun := fun x => (D.equiv x).2
      map_one' := by
        change (D.equiv 1).2 = 1
        exact congrArg (fun z => z.2) D.equiv.map_one
      map_mul' := by
        intro x y
        change (D.equiv (x * y)).2 = (D.equiv x).2 * (D.equiv y).2
        exact congrArg (fun z => z.2) (D.equiv.map_mul x y)
      map_zero' := by
        change (D.equiv 0).2 = 0
        exact congrArg (fun z => z.2) D.equiv.map_zero
      map_add' := by
        intro x y
        change (D.equiv (x + y)).2 = (D.equiv x).2 + (D.equiv y).2
        exact congrArg (fun z => z.2) (D.equiv.map_add x y) }

/-- The étale neighborhood and finite product around all quasi-finite primes
over a fixed prime. -/
structure EtaleFiniteOverPrimeData
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (f : R →+* S) (p : PrimeSpectrum R) where
  R' : Type u
  [commRingR' : CommRing R']
  [algebraRR' : Algebra R R']
  etale : RingHom.Etale (algebraMap R R')
  p' : PrimeSpectrum R'
  liesOver : PrimeSpectrum.comap (algebraMap R R') p' = p
  residueFieldMapBijective :
    Function.Bijective
      (Formalization.Books.Algebra.Unit113.residueFieldMapAt
        (algebraMap R R') p p' liesOver)
  decomposition : FiniteAlgebraProduct R' (R' ⊗[R] S)
  finiteFactors : ∀ i, letI : CommRing (decomposition.A i) := decomposition.commRingA i
    letI : Algebra R' (decomposition.A i) := decomposition.algebraA i
    RingHom.Finite (algebraMap R' (decomposition.A i))
  uniquePrime : ∀ i, letI : CommRing (decomposition.A i) := decomposition.commRingA i
    letI : Algebra R' (decomposition.A i) := decomposition.algebraA i
    ∃! r : PrimeSpectrum (decomposition.A i),
      PrimeSpectrum.comap (algebraMap R' (decomposition.A i)) r = p'
  noQuasiFiniteB : letI : CommRing decomposition.B := decomposition.commRingB
    letI : Algebra R' decomposition.B := decomposition.algebraB
    ∀ r : PrimeSpectrum decomposition.B,
      PrimeSpectrum.comap (algebraMap R' decomposition.B) r = p' →
        ¬ Formalization.Books.Algebra.Unit122.IsQuasiFiniteAt
          (algebraMap R' decomposition.B) r

/-- Étale local structure after collecting all quasi-finite points over a
prime into finitely many finite factors. -/
theorem etale_makes_quasiFinite_finite
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (hfiniteType : f.FiniteType) :
    letI : Algebra R S := f.toAlgebra
    Nonempty (EtaleFiniteOverPrimeData f p) := by
  sorry

/-- The variant in which the residue-field extensions of the finite factors
are purely inseparable. -/
structure EtaleFinitePurelyInseparableData
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (f : R →+* S) (p : PrimeSpectrum R) where
  R' : Type u
  [commRingR' : CommRing R']
  [algebraRR' : Algebra R R']
  etale : RingHom.Etale (algebraMap R R')
  p' : PrimeSpectrum R'
  liesOver : PrimeSpectrum.comap (algebraMap R R') p' = p
  decomposition : FiniteAlgebraProduct R' (R' ⊗[R] S)
  finiteFactors : ∀ i, letI : CommRing (decomposition.A i) := decomposition.commRingA i
    letI : Algebra R' (decomposition.A i) := decomposition.algebraA i
    RingHom.Finite (algebraMap R' (decomposition.A i))
  uniquePrime : ∀ i, letI : CommRing (decomposition.A i) := decomposition.commRingA i
    letI : Algebra R' (decomposition.A i) := decomposition.algebraA i
    ∃! r : PrimeSpectrum (decomposition.A i),
      PrimeSpectrum.comap (algebraMap R' (decomposition.A i)) r = p'
  residuePurelyInseparable : ∀ i,
    letI : CommRing (decomposition.A i) := decomposition.commRingA i
    letI : Algebra R' (decomposition.A i) := decomposition.algebraA i
    ∀ r : PrimeSpectrum (decomposition.A i),
    ∀ hr : PrimeSpectrum.comap (algebraMap R' (decomposition.A i)) r = p',
      letI : Algebra p'.asIdeal.ResidueField r.asIdeal.ResidueField :=
        (Formalization.Books.Algebra.Unit113.residueFieldMapAt
          (algebraMap R' (decomposition.A i)) p' r hr).toAlgebra
      Module.Finite p'.asIdeal.ResidueField r.asIdeal.ResidueField ∧
        IsPurelyInseparable p'.asIdeal.ResidueField r.asIdeal.ResidueField
  noQuasiFiniteB : letI : CommRing decomposition.B := decomposition.commRingB
    letI : Algebra R' decomposition.B := decomposition.algebraB
    ∀ r : PrimeSpectrum decomposition.B,
      PrimeSpectrum.comap (algebraMap R' decomposition.B) r = p' →
        ¬ Formalization.Books.Algebra.Unit122.IsQuasiFiniteAt
          (algebraMap R' decomposition.B) r

theorem etale_makes_quasiFinite_finite_variant
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (hfiniteType : f.FiniteType) :
    letI : Algebra R S := f.toAlgebra
    Nonempty (EtaleFinitePurelyInseparableData f p) := by
  sorry

end

end Formalization.Books.Algebra.Unit145
