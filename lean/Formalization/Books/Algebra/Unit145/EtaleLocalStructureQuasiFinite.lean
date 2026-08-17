import Formalization.Books.Algebra.Unit122.QuasiFinite
import Formalization.Books.Algebra.Unit123.ZariskiMain
import Formalization.Books.Algebra.Unit127.ColimitsAndFinitePresentation
import Formalization.Books.Algebra.Unit131.Differentials
import Formalization.Books.Algebra.Unit133.FiniteOrderDifferentialOperators
import Formalization.Books.Algebra.Unit137.SmoothRingMaps
import Formalization.Books.Algebra.Unit144.LocalStructureEtaleRingMaps
import Formalization.Books.Algebra.Unit91.ExamplesAndNonExamples
import Formalization.Books.Algebra.Unit126.AlgebrasAndModulesFinitePresentation
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Smooth.IntegralClosure

/-!
# Commutative Algebra, Chapter 145: Étale local structure of quasi-finite ring maps

The chapter uses the canonical predicates for étale, quasi-finite, formally
unramified, integrality, and filtered algebra colimits.  The structures below
only package the product decompositions, local presentations, and universal
properties that are explicit in the source.
-/

namespace Formalization.Books.Algebra.Unit145

open Set
open Polynomial
open scoped TensorProduct
open Formalization.Books.Algebra.Unit131
open Formalization.Books.Algebra.Unit133
open Formalization.Books.Algebra.Unit144
open Formalization.Books.Categories.Unit21

noncomputable section

universe u v w

/-! ## Common maps and product presentations -/

/-- The map from a base ring to a principal localization of its target. -/
def targetLocalizationMap
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (g : S) : R →+* Localization.Away g :=
  (algebraMap S (Localization.Away g)).comp f

/-- A binary product presentation equipped with an algebra structure over `R`.

The algebra equivalence is retained so that the induced maps to the two
factors can be used in prime-lifting statements.
-/
structure BinaryAlgebraProduct
    (R X : Type u) [CommRing R] [CommRing X] [Algebra R X] where
  A : CommRingCat.{u}
  algebraA : Algebra R A
  B : CommRingCat.{u}
  algebraB : Algebra R B
  equiv : X ≃+* A × B

def BinaryAlgebraProduct.leftMap
    {R X : Type u} [CommRing R] [CommRing X] [Algebra R X]
    (D : BinaryAlgebraProduct R X) : X →+* D.A :=
  (RingHom.fst D.A D.B).comp D.equiv.toRingHom

def BinaryAlgebraProduct.rightMap
    {R X : Type u} [CommRing R] [CommRing X] [Algebra R X]
    (D : BinaryAlgebraProduct R X) : X →+* D.B :=
  (RingHom.snd D.A D.B).comp D.equiv.toRingHom

/-! ## 145.1 Étale local structure of quasi-finite ring maps -/

theorem produce_finite
    {R S' S : Type u} [CommRing R] [CommRing S'] [CommRing S]
    (f : R →+* S') (g : S' →+* S) (p : PrimeSpectrum R) (s : S')
    (hintegral : f.IsIntegral)
    (hfiniteType : (g.comp f).FiniteType)
    (hloc : Nonempty
      (Localization.Away s ≃+* Localization.Away (g s)))
    (hinvertible :
      letI : Algebra R S' := f.toAlgebra
      IsUnit (algebraMap S' (S' ⊗[R] p.asIdeal.ResidueField) s)) :
    ∃ r : R, r ∉ p.asIdeal ∧
      RingHom.Finite (Localization.awayMap (g.comp f) r) := by
  sorry

/-- The product data produced around a quasi-finite point. -/
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
  residueEquiv :
    letI : Algebra p.asIdeal.ResidueField p'.asIdeal.ResidueField :=
      (Formalization.Books.Algebra.Unit113.residueFieldMapAt
        (algebraMap R R') p p' liesOver).toAlgebra
    Nonempty
      (p.asIdeal.ResidueField ≃ₐ[p.asIdeal.ResidueField]
        p'.asIdeal.ResidueField)
  decomposition : BinaryAlgebraProduct R' (R' ⊗[R] S)
  finiteA : letI : Algebra R' decomposition.A := decomposition.algebraA
    RingHom.Finite (algebraMap R' decomposition.A)
  uniquePrime : letI : Algebra R' decomposition.A := decomposition.algebraA
    ∃! r : PrimeSpectrum decomposition.A,
      PrimeSpectrum.comap (algebraMap R' decomposition.A) r = p'
  primeOverQ : letI : Algebra R' decomposition.A := decomposition.algebraA
    ∀ r : PrimeSpectrum decomposition.A,
      PrimeSpectrum.comap (algebraMap R' decomposition.A) r = p' →
        PrimeSpectrum.comap
            (decomposition.leftMap.comp
              Algebra.TensorProduct.includeRight.toRingHom) r = q
  noPrimeB : letI : Algebra R' decomposition.B := decomposition.algebraB
    ∀ r : PrimeSpectrum decomposition.B,
      PrimeSpectrum.comap (algebraMap R' decomposition.B) r = p' →
        PrimeSpectrum.comap
            (decomposition.rightMap.comp
              Algebra.TensorProduct.includeRight.toRingHom) r ≠ q

theorem etale_makes_quasiFinite_finite_one_prime
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p)
    (hfiniteType : f.FiniteType)
    (hquasi : RingHom.QuasiFiniteAt f q.asIdeal) :
    letI : Algebra R S := f.toAlgebra
    Nonempty (EtaleFiniteAtPrimeData f p q hq) := by
  sorry

/-! The finite-product version is expressed by a finite family of factors. -/

structure FiniteAlgebraProduct
    (R X : Type u) [CommRing R] [CommRing X] [Algebra R X] where
  n : ℕ
  A : Fin n → CommRingCat.{u}
  algebraA : ∀ i, Algebra R (A i)
  B : CommRingCat.{u}
  algebraB : Algebra R B
  equiv : X ≃+* (∀ i, A i) × B

def FiniteAlgebraProduct.factorMap
    {R X : Type u} [CommRing R] [CommRing X] [Algebra R X]
    (D : FiniteAlgebraProduct R X) (i : Fin D.n) : X →+* D.A i :=
  { toFun := fun x => (D.equiv x).1 i
    map_one' := by simp
    map_mul' := by intro x y; simp
    map_zero' := by simp
    map_add' := by intro x y; simp }

def FiniteAlgebraProduct.remainderMap
    {R X : Type u} [CommRing R] [CommRing X] [Algebra R X]
    (D : FiniteAlgebraProduct R X) : X →+* D.B :=
  { toFun := fun x => (D.equiv x).2
    map_one' := by simp
    map_mul' := by intro x y; simp
    map_zero' := by simp
    map_add' := by intro x y; simp }

structure EtaleFiniteOverPrimeData
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (f : R →+* S) (p : PrimeSpectrum R) where
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
      (p.asIdeal.ResidueField ≃ₐ[p.asIdeal.ResidueField]
        p'.asIdeal.ResidueField)
  decomposition : FiniteAlgebraProduct R' (R' ⊗[R] S)
  finiteFactors : ∀ i, letI : Algebra R' (decomposition.A i) := decomposition.algebraA i
    RingHom.Finite (algebraMap R' (decomposition.A i))
  uniquePrime : ∀ i, letI : Algebra R' (decomposition.A i) := decomposition.algebraA i
    ∃! r : PrimeSpectrum (decomposition.A i),
      PrimeSpectrum.comap (algebraMap R' (decomposition.A i)) r = p'
  noPrimeB : letI : Algebra R' decomposition.B := decomposition.algebraB
    ∀ r : PrimeSpectrum decomposition.B,
      PrimeSpectrum.comap (algebraMap R' decomposition.B) r ≠ p'

theorem etale_makes_quasiFinite_finite
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (hfiniteType : f.FiniteType) :
    letI : Algebra R S := f.toAlgebra
    Nonempty (EtaleFiniteOverPrimeData f p) := by
  sorry

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
  finiteFactors : ∀ i, letI : Algebra R' (decomposition.A i) := decomposition.algebraA i
    RingHom.Finite (algebraMap R' (decomposition.A i))
  uniquePrime : ∀ i, letI : Algebra R' (decomposition.A i) := decomposition.algebraA i
    ∃! r : PrimeSpectrum (decomposition.A i),
      PrimeSpectrum.comap (algebraMap R' (decomposition.A i)) r = p'
  residuePurelyInseparable : ∀ i (r : PrimeSpectrum (decomposition.A i)),
    letI : Algebra R' (decomposition.A i) := decomposition.algebraA i
    ∀ hr : PrimeSpectrum.comap (algebraMap R' (decomposition.A i)) r = p',
      letI : Algebra p'.asIdeal.ResidueField r.asIdeal.ResidueField :=
        (Formalization.Books.Algebra.Unit113.residueFieldMapAt
          (algebraMap R' (decomposition.A i)) p' r hr).toAlgebra
      IsPurelyInseparable p'.asIdeal.ResidueField r.asIdeal.ResidueField
  noPrimeB : letI : Algebra R' decomposition.B := decomposition.algebraB
    ∀ r : PrimeSpectrum decomposition.B,
      PrimeSpectrum.comap (algebraMap R' decomposition.B) r ≠ p'

theorem etale_makes_quasiFinite_finite_variant
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (hfiniteType : f.FiniteType) :
    letI : Algebra R S := f.toAlgebra
    Nonempty (EtaleFinitePurelyInseparableData f p) := by
  sorry

/-! ## 145.2 Local homomorphisms -/

/-- The canonical map on quotients induced by a ring map and a principal
power ideal.  It is the map appearing in Lindel's lemma. -/
def powerQuotientMap
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (t : R) (n : ℕ) :
    R ⧸ Ideal.span ({t ^ n} : Set R) →+*
      S ⧸ Ideal.map f (Ideal.span ({t ^ n} : Set R)) :=
  Ideal.Quotient.lift (Ideal.span ({t ^ n} : Set R))
    ((Ideal.Quotient.mk (Ideal.map f (Ideal.span ({t ^ n} : Set R)))).comp f)
    (by
      intro a ha
      change Ideal.Quotient.mk (Ideal.map f (Ideal.span ({t ^ n} : Set R))) (f a) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem f ha)

structure LocalEtaleCompletionData
    (R S : Type u) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] where
  map : R →+* S
  localHom : IsLocalHom map
  etaleLocalization :
    ∃ (T : Type u) (hT : CommRing T),
      letI : CommRing T := hT
      ∃ q : PrimeSpectrum T,
      ∃ g : R →+* T, RingHom.Etale g ∧
        Nonempty (Localization.AtPrime q.asIdeal ≃+* S)
  residueEquiv : ∃ e : IsLocalRing.ResidueField R ≃+*
      IsLocalRing.ResidueField S,
    e.toRingHom.comp (algebraMap R (IsLocalRing.ResidueField R)) =
      (algebraMap S (IsLocalRing.ResidueField S)).comp map

theorem lindel
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) (hlocal : IsLocalHom f)
    (hEtaleLocal : ∃ (T : Type u) (hT : CommRing T),
      letI : CommRing T := hT
      ∃ q : PrimeSpectrum T,
      ∃ g : R →+* T, RingHom.Etale g ∧
        Nonempty (Localization.AtPrime q.asIdeal ≃+* S))
    (hresidue : ∃ e : IsLocalRing.ResidueField R ≃+*
        IsLocalRing.ResidueField S,
      e.toRingHom.comp (algebraMap R (IsLocalRing.ResidueField R)) =
        (algebraMap S (IsLocalRing.ResidueField S)).comp f) :
    ∃ t : R, t ∈ IsLocalRing.maximalIdeal R ∧
      ∀ n : ℕ, 1 ≤ n →
        ∃ e : (R ⧸ (Ideal.span ({t ^ n} : Set R))) ≃+*
          (S ⧸ Ideal.map f (Ideal.span ({t ^ n} : Set R))),
          e.toRingHom = powerQuotientMap f t n := by
  sorry

theorem etale_under_finite_flat
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) (hlocal : IsLocalHom f)
    (hEtaleLocal : ∃ (T : Type u) (hT : CommRing T),
      letI : CommRing T := hT
      ∃ q : PrimeSpectrum T,
      ∃ g : R →+* T, RingHom.Etale g ∧
        Nonempty (Localization.AtPrime q.asIdeal ≃+* S)) :
    ∃ S' : Type u, ∃ hS' : CommRing S', ∃ hAlg : Algebra R S',
      letI : CommRing S' := hS'
      letI : Algebra R S' := hAlg
      RingHom.Finite (algebraMap R S') ∧
        RingHom.FinitePresentation (algebraMap R S') ∧
        RingHom.Flat (algebraMap R S') ∧
        RingHom.FaithfullyFlat (algebraMap R S') ∧
        Function.Surjective (PrimeSpectrum.comap (algebraMap R S')) ∧
        ∀ m' : PrimeSpectrum S', m'.asIdeal.IsMaximal →
          ∃ φ : S →+* Localization.AtPrime m'.asIdeal,
            φ.comp f = algebraMap R (Localization.AtPrime m'.asIdeal) := by
  sorry

/-! ## 145.3 Integral closure and smooth base change -/

abbrev integralClosureBaseChangeMap
    {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B]
    :
    S ⊗[R] (integralClosure R B) →ₐ[S]
      integralClosure S (S ⊗[R] B) :=
  TensorProduct.toIntegralClosure R S B

theorem integral_closure_trick
    {R B : Type u} [CommRing R] [CommRing B]
    (f : R[X]) (hf : f.Monic) (φ : R →+* B)
    (h : B[X] ⧸ Ideal.span ({Polynomial.map φ f} : Set (B[X])))
    (hintegral :
      (Ideal.Quotient.mk _).comp (Polynomial.C.comp φ) |>.IsIntegralElem h) :
    ∃ p : B[X],
      (∀ n : ℕ, φ.IsIntegralElem (p.coeff n)) ∧
        Ideal.Quotient.mk _ (Polynomial.map φ (Polynomial.derivative f)) * h =
          Ideal.Quotient.mk _ p := by
  sorry

theorem integral_closure_commutes_etale
    {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [Algebra.Etale R S] :
      Function.Bijective (integralClosureBaseChangeMap (R := R) (S := S) (B := B)) := by
  sorry

abbrev cyclotomicFourierBase (p : ℕ) : Type :=
  Localization.Away (p : ℤ)

def cyclotomicFourierPolynomial (p : ℕ) :
    Polynomial (cyclotomicFourierBase p) :=
  Finset.sum (Finset.range p) (fun i => Polynomial.X ^ i)

abbrev cyclotomicFourierRing (p : ℕ) : Type :=
  AdjoinRoot (cyclotomicFourierPolynomial p)

def cyclotomicFourierMap (p : ℕ) :
    cyclotomicFourierBase p →+* cyclotomicFourierRing p :=
  AdjoinRoot.of (cyclotomicFourierPolynomial p)

def cyclotomicFourierRoot (p : ℕ) : cyclotomicFourierRing p :=
  AdjoinRoot.root (cyclotomicFourierPolynomial p)

structure CyclotomicFourierData (p d : ℕ) where
  alpha : Fin d → cyclotomicFourierRing p
  alpha_is_power : ∀ i, alpha i = cyclotomicFourierRoot p ^ (i : ℕ)
  difference_unit :
    IsUnit (∏ i : Fin d,
      Finset.prod (Finset.univ.filter (fun j : Fin d => i < j))
        (fun j => alpha i - alpha j))

theorem cyclotomic_fourier_example
    (p : ℕ) (hp : Nat.Prime p) (d : ℕ) (hd : d < p) :
    Nonempty (CyclotomicFourierData p d) := by
  sorry

theorem integral_closure_commutes_smooth
    {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [Algebra.Smooth R S] :
    Function.Bijective (integralClosureBaseChangeMap (R := R) (S := S) (B := B)) := by
  sorry

theorem integral_closure_commutes_filtered_colimit_smooth
    {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B]
    (hcolim : Nonempty
      (Formalization.Books.Algebra.Unit127.FilteredAlgebraColimitIn
        (algebraMap R S)
        {X | letI : Algebra R X.right := X.hom.hom.toAlgebra
          Algebra.Smooth R X.right})) :
    Function.Bijective (integralClosureBaseChangeMap (R := R) (S := S) (B := B)) := by
  sorry

/-! ## 145.4 Formally unramified maps -/

abbrev FormallyUnramified
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  RingHom.FormallyUnramified f

/- The source's localization-at-a-prime map is needed already for the
   source-local form of formal unramifiedness. -/
def localizationAtPrimeMap
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) :
    Localization.AtPrime p.asIdeal →+*
      Localization.AtPrime q.asIdeal :=
  let hcomap : p.asIdeal = q.asIdeal.comap f := by
    simpa [PrimeSpectrum.comap_asIdeal] using
      (congrArg PrimeSpectrum.asIdeal hq).symm
  Localization.localRingHom p.asIdeal q.asIdeal f hcomap

theorem baseChange_formallyUnramified
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (h : FormallyUnramified f) :
    FormallyUnramified
      (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g) := by
  sorry

theorem formallyUnramified_iff_differentials_zero
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    FormallyUnramified f ↔
      letI : Algebra R S := f.toAlgebra
      Subsingleton (KaehlerDifferential R S) := by
  sorry

theorem formallyUnramified_local
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    FormallyUnramified f ↔
      (∀ q : PrimeSpectrum S, FormallyUnramified
        ((algebraMap S (Localization.AtPrime q.asIdeal)).comp f)) := by
  sorry

theorem formallyUnramified_local_source_target
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    FormallyUnramified f ↔
      (∀ q : PrimeSpectrum S,
        FormallyUnramified
          (localizationAtPrimeMap f (PrimeSpectrum.comap f q) q rfl)) := by
  sorry

theorem formallyUnramified_localize
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (h : FormallyUnramified f) :
    (∀ M : Submonoid A, FormallyUnramified
        (Formalization.Books.Algebra.Unit126.localizedRingHom f M)) ∧
      (∀ M : Submonoid B, FormallyUnramified
        ((algebraMap B (Localization M)).comp f)) := by
  sorry

theorem colimit_formallyUnramified
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (h : Nonempty
      (Formalization.Books.Algebra.Unit127.FilteredAlgebraColimitIn f
        {X | FormallyUnramified X.hom.hom})) :
    FormallyUnramified f := by
  sorry

/-! ## 145.5 Conormal modules and universal thickenings -/

/-- An ideal is a square-zero ideal when its product with itself vanishes. -/
def SquareZeroIdeal {A : Type u} [CommRing A] (I : Ideal A) : Prop :=
  I ^ 2 = ⊥

/-- The source's universal first-order thickening, with its lifting property
recorded explicitly.  The kernel of `thickening` is the conormal object. -/
structure UniversalFirstOrderThickening
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : FormallyUnramified f) where
  S' : Type u
  [commRingS' : CommRing S']
  [algebraRS' : Algebra R S']
  thickening : S' →+* S
  thickening_surjective : Function.Surjective thickening
  thickening_comp : thickening.comp (algebraMap R S') = f
  kernel_square_zero : SquareZeroIdeal (RingHom.ker thickening)
  lift : ∀ (A : Type v) [CommRing A] (I : Ideal A), SquareZeroIdeal I →
    ∀ (b : R →+* A) (a : S →+* (A ⧸ I)),
    a.comp f = (Ideal.Quotient.mk I).comp b →
    ∃! a' : S' →+* A,
      a'.comp (algebraMap R S') = b ∧
        (Ideal.Quotient.mk I).comp a' = a.comp thickening

/-- The conormal module attached to a universal thickening is its kernel.
The canonical scalar action is supplied by the universal property. -/
abbrev conormalModule
    {R S : Type u} [CommRing R] [CommRing S]
    {f : R →+* S} {hf : FormallyUnramified f}
    (D : UniversalFirstOrderThickening f hf) : Type u := by
  letI : CommRing D.S' := D.commRingS'
  exact ↥(RingHom.ker D.thickening)

theorem universal_first_order_thickening
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : FormallyUnramified f) :
    Nonempty (UniversalFirstOrderThickening f hf) := by
  sorry

theorem universal_first_order_thickening_unique
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : FormallyUnramified f)
    (D E : UniversalFirstOrderThickening f hf) :
    letI : CommRing D.S' := D.commRingS'
    letI : CommRing E.S' := E.commRingS'
    letI : Algebra R D.S' := D.algebraRS'
    letI : Algebra R E.S' := E.algebraRS'
    ∃! e : D.S' ≃+* E.S',
      e.toRingHom.comp (algebraMap R D.S') = algebraMap R E.S' ∧
        E.thickening.comp e.toRingHom = D.thickening := by
  sorry

theorem universal_thickening_quotient
    {R : Type u} [CommRing R] (I : Ideal R) :
    FormallyUnramified (Ideal.Quotient.mk I) ∧
      Function.Surjective (Ideal.Quotient.factorPow I (Nat.le_succ 1)) := by
  sorry

theorem universal_thickening_quotient_conormal
    {R : Type u} [CommRing R] (I : Ideal R) :
    Nonempty (I.Cotangent ≃ₗ[R] I.cotangentIdeal) ∧
      RingHom.ker (Ideal.Quotient.factorPow I (Nat.le_succ 1)) =
        I.cotangentIdeal := by
  refine ⟨⟨Ideal.cotangentEquivIdeal I⟩, ?_⟩
  sorry

theorem universal_thickening_localize_source
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : FormallyUnramified f)
    (D : UniversalFirstOrderThickening f hf) (M : Submonoid R)
    (hM : FormallyUnramified
      (Formalization.Books.Algebra.Unit126.localizedRingHom f M)) :
    Nonempty (UniversalFirstOrderThickening
      (Formalization.Books.Algebra.Unit126.localizedRingHom f M) hM) := by
  sorry

theorem universal_thickening_localize_target
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : FormallyUnramified f)
    (D : UniversalFirstOrderThickening f hf) (M : Submonoid S)
    (hM : FormallyUnramified ((algebraMap S (Localization M)).comp f)) :
    Nonempty (UniversalFirstOrderThickening
      ((algebraMap S (Localization M)).comp f) hM) := by
  sorry

/- A fixed thickening is useful when the intermediate ring is named in a
   statement.  This is the universal property from the source with all maps
   bundled into one proposition. -/
def IsUniversalFirstOrderThickeningOver
    {A B B' : Type u} [CommRing A] [CommRing B] [CommRing B']
    [Algebra A B] [Algebra A B'] [Algebra B' B]
    (g : B' →+* B) : Prop :=
  Function.Surjective g ∧
    SquareZeroIdeal (RingHom.ker g) ∧
      g.comp (algebraMap A B') = algebraMap A B ∧
        ∀ (C : Type v) [CommRing C] (I : Ideal C), SquareZeroIdeal I →
          ∀ (b : A →+* C) (a : B →+* (C ⧸ I)),
          a.comp (algebraMap A B) = (Ideal.Quotient.mk I).comp b →
          ∃! a' : B' →+* C,
            a'.comp (algebraMap A B') = b ∧
              (Ideal.Quotient.mk I).comp a' = a.comp g

/- The source's comparison is stated using the two canonical maps into
   `Ω_{B/R}`. -/
theorem differentials_universal_thickening
    {R A B B' : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing B']
    [Algebra R A] [Algebra R B] [Algebra R B']
    [Algebra A B] [Algebra A B'] [Algebra B' B]
    [IsScalarTower R A B] [IsScalarTower R A B'] [IsScalarTower R B' B]
    (hform : FormallyUnramified (algebraMap A B))
    (g : B' →+* B)
    (hthick : IsUniversalFirstOrderThickeningOver
      (A := A) (B := B) (B' := B') g) :
    FormallyUnramified (algebraMap A B') ∧
      ∃ e : B ⊗[A] ModuleOfDifferentials R A →ₗ[B]
          B ⊗[B'] ModuleOfDifferentials R B',
        Function.Bijective e ∧
          (KaehlerDifferential.mapBaseChange R B' B).comp e =
            KaehlerDifferential.mapBaseChange R A B := by
  sorry

/-! ## 145.6 Formally étale maps -/

abbrev FormallyEtale
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  RingHom.FormallyEtale f

theorem formallyEtale_iff_formallySmooth_formallyUnramified
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    FormallyEtale f ↔ RingHom.FormallySmooth f ∧ FormallyUnramified f := by
  sorry

theorem baseChange_formallyEtale
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (h : FormallyEtale f) :
    FormallyEtale
      (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g) := by
  sorry

theorem formallyEtale_iff_etale_of_finitePresentation
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfp : f.FinitePresentation) :
    FormallyEtale f ↔ RingHom.Etale f := by
  sorry

theorem colimit_formallyEtale
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (h : Nonempty
      (Formalization.Books.Algebra.Unit127.FilteredAlgebraColimitIn f
        {X | FormallyEtale X.hom.hom})) :
    FormallyEtale f := by
  sorry

theorem localization_formallyEtale
    {R : Type u} [CommRing R] (M : Submonoid R) :
    FormallyEtale (algebraMap R (Localization M)) := by
  sorry

/-- The compatible levelwise equivalences occurring in the infinitesimal
lifting lemma.  The level maps are required to respect the original ring map. -/
structure InfinitesimalPowerEquivalence
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (J : Ideal S) where
  I : Ideal R
  I_def : I = RingHom.ker ((Ideal.Quotient.mk J).comp f)
  level : ∀ n : ℕ, (R ⧸ I ^ n) ≃+* (S ⧸ J ^ n)
  level_comp : ∀ n : ℕ,
    (level n).toRingHom.comp (Ideal.Quotient.mk (I ^ n)) =
      (Ideal.Quotient.mk (J ^ n)).comp f

theorem formallyEtale_lift_infinitesimal
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (J : Ideal S)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk J).comp f))
    (hformal : FormallyEtale f) :
    Nonempty (InfinitesimalPowerEquivalence f J) := by
  sorry

/- The source's `lemma-formally-etale-omega` is the diagonal/principal-parts
   comparison for every order, together with its degree-one differential
   consequence.  The quotient rings are recorded with the canonical
   diagonal ideals from Chapter 133. -/
structure FormallyEtaleOmegaComparison
    {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S']
    [IsScalarTower R S S'] where
  level : ∀ k : ℕ, Nonempty
    (S' ⊗[S]
        ((S ⊗[R] S) ⧸
          (Formalization.Books.Algebra.Unit133.diagonalIdeal
            (R := R) (S := S)) ^ (k + 1)) ≃+*
      ((S' ⊗[R] S') ⧸
        (Formalization.Books.Algebra.Unit133.diagonalIdeal
          (R := R) (S := S')) ^ (k + 1)))
  differential : Nonempty
    (S' ⊗[S] ModuleOfDifferentials R S ≃ₗ[S']
      ModuleOfDifferentials R S')

theorem formallyEtale_omega
    {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S']
    [IsScalarTower R S S']
    (hformal : FormallyEtale (algebraMap S S')) :
    Nonempty (FormallyEtaleOmegaComparison (R := R) (S := S)
      (S' := S')) := by
  sorry

theorem formallyEtale_principal_parts
    {R S S' M : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R S'] [Algebra S S']
    [IsScalarTower R S S'] [AddCommGroup M] [Module S M] [Module R M]
    [IsScalarTower R S M]
    (f : S →+* S') (hformal : FormallyEtale f) (k : ℕ) :
    Nonempty
      (S' ⊗[S] PrincipalParts (R := R) (S := S) (M := M) k ≃ₗ[S']
        PrincipalParts (R := R) (S := S') (M := S' ⊗[S] M) k) := by
  sorry

theorem formallyEtale_differential_operator_extension
    {A A' B B' M M' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A B] [Algebra A A'] [Algebra B B'] [Algebra A' B']
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [AddCommGroup M'] [Module B' M'] [Module A' M']
    [IsScalarTower A' B' M']
    (f : M →+ M')
    (hf : ∀ b m, f (b • m) = algebraMap B B' b • f m)
    (hcomm : (algebraMap A' B').comp (algebraMap A A') =
      (algebraMap B B').comp (algebraMap A B))
    (hformal : FormallyEtale (algebraMap B B')) :
    Nonempty (PrincipalPartsFunctoriality
      (A := A) (A' := A') (B := B) (B' := B') (M := M) (M' := M')) := by
  sorry

theorem formallyEtale_differential_operator_composition
    {A A' A'' B B' B'' M M' M'' : Type u}
    [CommRing A] [CommRing A'] [CommRing A'']
    [CommRing B] [CommRing B'] [CommRing B'']
    [Algebra A B] [Algebra A A'] [Algebra B B'] [Algebra A' B']
    [Algebra A' A''] [Algebra B' B''] [Algebra A'' B'']
    [Algebra A A''] [Algebra B B'']
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [AddCommGroup M'] [Module B' M'] [Module A' M']
    [IsScalarTower A' B' M'] [AddCommGroup M''] [Module B'' M'']
    [Module A'' M''] [IsScalarTower A'' B'' M'']
    (F : PrincipalPartsFunctoriality
      (A := A) (A' := A') (B := B) (B' := B') (M := M) (M' := M'))
    (G : PrincipalPartsFunctoriality
      (A := A') (A' := A'') (B := B') (B' := B'') (M := M') (M' := M'')) :
    Nonempty (PrincipalPartsFunctorialityComposition F G) := by
  sorry

/-! ## 145.7 Unramified ring maps -/

/-- The finite-type version of formal unramifiedness. -/
def IsUnramified
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  f.FiniteType ∧ FormallyUnramified f

/-- The finite-presentation (EGA) version of formal unramifiedness. -/
def IsGUnramified
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  f.FinitePresentation ∧ FormallyUnramified f

def atPrimeLocalizationMap
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (q : PrimeSpectrum S) :
    R →+* Localization.AtPrime q.asIdeal :=
  (algebraMap S (Localization.AtPrime q.asIdeal)).comp f

def IsUnramifiedAt
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (q : PrimeSpectrum S) : Prop :=
  ∃ g : S, g ∉ q.asIdeal ∧ IsUnramified (targetLocalizationMap f g)

def IsGUnramifiedAt
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (q : PrimeSpectrum S) : Prop :=
  ∃ g : S, g ∉ q.asIdeal ∧ IsGUnramified (targetLocalizationMap f g)

def localCotangentZeroAt
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (q : PrimeSpectrum S) : Prop := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R (Localization.AtPrime q.asIdeal) :=
    Algebra.compHom (Localization.AtPrime q.asIdeal)
      f
  exact Subsingleton (ModuleOfDifferentials R
    (Localization.AtPrime q.asIdeal))

def residueCotangentZeroAt
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) : Prop := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    (Formalization.Books.Algebra.Unit113.residueFieldMapAt f p q hq).toAlgebra
  exact Subsingleton (ModuleOfDifferentials
    p.asIdeal.ResidueField q.asIdeal.ResidueField)

def fiberCotangentZeroAt
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) : Prop := by
  letI : Algebra R S := f.toAlgebra
  exact ∃ qf : PrimeSpectrum (p.asIdeal.Fiber S),
    PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom qf = q ∧
      Subsingleton
        (qf.asIdeal.ResidueField ⊗[p.asIdeal.Fiber S]
          ModuleOfDifferentials p.asIdeal.ResidueField (p.asIdeal.Fiber S))

/- The next two predicates keep the two intermediate differential criteria
   from the source distinct: total cotangents are tensor products with the
   target residue field, while fibre cotangents are computed on the fibre
   ring at a prime mapping to `q`. -/
def totalCotangentFiberZeroAt
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (q : PrimeSpectrum S) : Prop := by
  letI : Algebra R S := f.toAlgebra
  exact Subsingleton
    (q.asIdeal.ResidueField ⊗[S] ModuleOfDifferentials R S)

def fiberLocalizationCotangentZeroAt
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) : Prop := by
  letI : Algebra R S := f.toAlgebra
  exact ∃ qf : PrimeSpectrum (p.asIdeal.Fiber S),
    PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom qf = q ∧
      Subsingleton (ModuleOfDifferentials p.asIdeal.ResidueField
        (Localization.AtPrime qf.asIdeal))

theorem formallyUnramified_iff_unramified
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    (FormallyUnramified f ∧ f.FiniteType) ↔ IsUnramified f := by
  sorry

theorem formallyUnramified_iff_gUnramified
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    (FormallyUnramified f ∧ f.FinitePresentation) ↔ IsGUnramified f := by
  sorry

theorem gUnramified_is_unramified
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (h : IsGUnramified f) :
    IsUnramified f := by
  sorry

theorem baseChange_unramified
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (h : IsUnramified f) :
    IsUnramified (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g) := by
  sorry

theorem baseChange_gUnramified
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (h : IsGUnramified f) :
    IsGUnramified (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g) := by
  sorry

theorem comp_unramified
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (hf : IsUnramified f) (hg : IsUnramified g) :
    IsUnramified (g.comp f) := by
  sorry

theorem comp_gUnramified
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (hf : IsGUnramified f) (hg : IsGUnramified g) :
    IsGUnramified (g.comp f) := by
  sorry

theorem localization_unramified
    {R : Type u} [CommRing R] (r : R) :
    IsUnramified (algebraMap R (Localization.Away r)) ∧
      IsGUnramified (algebraMap R (Localization.Away r)) := by
  sorry

theorem quotient_unramified
    {R : Type u} [CommRing R] (I : Ideal R) :
    IsUnramified (Ideal.Quotient.mk I) := by
  sorry

theorem quotient_gUnramified
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) :
    IsGUnramified (Ideal.Quotient.mk I) := by
  sorry

theorem etale_unramified
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (h : RingHom.Etale f) :
    IsUnramified f ∧ IsGUnramified f := by
  sorry

theorem unramified_at_of_local_cotangent
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : f.FiniteType) (q : PrimeSpectrum S)
    (hzero : localCotangentZeroAt f q) :
    IsUnramifiedAt f q := by
  sorry

theorem gUnramified_at_of_local_cotangent
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : f.FinitePresentation) (q : PrimeSpectrum S)
    (hzero : localCotangentZeroAt f q) :
    IsGUnramifiedAt f q := by
  sorry

theorem unramified_at_of_residue_cotangent
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : f.FiniteType) (p : PrimeSpectrum R)
    (q : PrimeSpectrum S) (hq : PrimeSpectrum.comap f q = p)
    (hzero : residueCotangentZeroAt f p q hq) :
    IsUnramifiedAt f q := by
  sorry

theorem gUnramified_at_of_residue_cotangent
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : f.FinitePresentation) (p : PrimeSpectrum R)
    (q : PrimeSpectrum S) (hq : PrimeSpectrum.comap f q = p)
    (hzero : residueCotangentZeroAt f p q hq) :
    IsGUnramifiedAt f q := by
  sorry

theorem unramified_at_of_total_cotangent
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : f.FiniteType) (q : PrimeSpectrum S)
    (hzero : totalCotangentFiberZeroAt f q) :
    IsUnramifiedAt f q := by
  sorry

theorem gUnramified_at_of_total_cotangent
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : f.FinitePresentation) (q : PrimeSpectrum S)
    (hzero : totalCotangentFiberZeroAt f q) :
    IsGUnramifiedAt f q := by
  sorry

theorem unramified_at_of_fiber_localization_cotangent
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : f.FiniteType) (p : PrimeSpectrum R)
    (q : PrimeSpectrum S) (hq : PrimeSpectrum.comap f q = p)
    (hzero : fiberLocalizationCotangentZeroAt f p q hq) :
    IsUnramifiedAt f q := by
  sorry

theorem gUnramified_at_of_fiber_localization_cotangent
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : f.FinitePresentation) (p : PrimeSpectrum R)
    (q : PrimeSpectrum S) (hq : PrimeSpectrum.comap f q = p)
    (hzero : fiberLocalizationCotangentZeroAt f p q hq) :
    IsGUnramifiedAt f q := by
  sorry

theorem unramified_at_of_fiber_cotangent
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : f.FiniteType) (p : PrimeSpectrum R)
    (q : PrimeSpectrum S) (hq : PrimeSpectrum.comap f q = p)
    (hzero : fiberCotangentZeroAt f p q hq) :
    IsUnramifiedAt f q := by
  sorry

theorem gUnramified_at_of_fiber_cotangent
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : f.FinitePresentation) (p : PrimeSpectrum R)
    (q : PrimeSpectrum S) (hq : PrimeSpectrum.comap f q = p)
    (hzero : fiberCotangentZeroAt f p q hq) :
    IsGUnramifiedAt f q := by
  sorry

theorem unramified_of_principal_cover
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (g : Fin n → S) (hcover : Ideal.span (Set.range g) = ⊤)
    (hlocal : ∀ i, IsUnramified (targetLocalizationMap f (g i))) :
    IsUnramified f := by
  sorry

theorem gUnramified_of_principal_cover
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (g : Fin n → S) (hcover : Ideal.span (Set.range g) = ⊤)
    (hlocal : ∀ i, IsGUnramified (targetLocalizationMap f (g i))) :
    IsGUnramified f := by
  sorry

theorem unramified_of_unramifiedAt_all_primes
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (h : ∀ q : PrimeSpectrum S, IsUnramifiedAt f q) :
    IsUnramified f := by
  sorry

theorem gUnramified_of_gUnramifiedAt_all_primes
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (h : ∀ q : PrimeSpectrum S, IsGUnramifiedAt f q) :
    IsGUnramified f := by
  sorry

structure GUnramifiedApproximation
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) where
  R₀ : Type u
  [commRingR₀ : CommRing R₀]
  [algebraZR₀ : Algebra ℤ R₀]
  [algebraR₀R : Algebra R₀ R]
  S₀ : Type u
  [commRingS₀ : CommRing S₀]
  [algebraR₀S₀ : Algebra R₀ S₀]
  map₀ : R₀ →+* S₀
  map₀_isGUnramified : IsGUnramified map₀
  R₀_finiteType : (algebraMap ℤ R₀).FiniteType
  baseChange : S ≃+* (R ⊗[R₀] S₀)
  baseChange_commutes :
    baseChange.toRingHom.comp f =
      (Algebra.TensorProduct.includeLeftRingHom :
        R →+* (R ⊗[R₀] S₀))

theorem gUnramified_approximation
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (h : IsGUnramified f) :
    Nonempty (GUnramifiedApproximation f) := by
  sorry

structure UnramifiedApproximation
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) where
  R₀ : Type u
  [commRingR₀ : CommRing R₀]
  [algebraZR₀ : Algebra ℤ R₀]
  [algebraR₀R : Algebra R₀ R]
  S₀ : Type u
  [commRingS₀ : CommRing S₀]
  [algebraR₀S₀ : Algebra R₀ S₀]
  map₀ : R₀ →+* S₀
  map₀_isUnramified : IsUnramified map₀
  R₀_finiteType : (algebraMap ℤ R₀).FiniteType
  quotientBaseChange : ∃ I : Ideal (R ⊗[R₀] S₀),
    ∃ e : S ≃+* ((R ⊗[R₀] S₀) ⧸ I),
      e.toRingHom.comp f =
        (Ideal.Quotient.mk I).comp
          (Algebra.TensorProduct.includeLeftRingHom :
            R →+* (R ⊗[R₀] S₀))

theorem unramified_approximation
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (h : IsUnramified f) :
    Nonempty (UnramifiedApproximation f) := by
  sorry

theorem diagonal_unramified
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (h : IsUnramified f) :
    letI : Algebra R S := f.toAlgebra
    ∃ e : S ⊗[R] S, IsIdempotentElem e ∧
      ∃ e' : Localization.Away e ≃+* S,
        e'.toRingHom.comp (algebraMap (S ⊗[R] S) (Localization.Away e)) =
          (Algebra.TensorProduct.lmul' R).toRingHom := by
  sorry

theorem unramified_at_prime
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) (h : IsUnramifiedAt f q) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R (Localization.AtPrime q.asIdeal) :=
      Algebra.compHom (Localization.AtPrime q.asIdeal)
        f
    Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) p.asIdeal =
        IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ∧
      letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
        (Formalization.Books.Algebra.Unit113.residueFieldMapAt f p q hq).toAlgebra
      Module.Finite p.asIdeal.ResidueField q.asIdeal.ResidueField ∧
        Algebra.IsSeparable p.asIdeal.ResidueField q.asIdeal.ResidueField := by
  sorry

theorem unramified_quasiFiniteAt
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : f.FiniteType) (q : PrimeSpectrum S)
    (h : IsUnramifiedAt f q) :
    RingHom.QuasiFiniteAt f q.asIdeal := by
  sorry

theorem unramified_is_quasiFinite
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (h : IsUnramified f) :
    ∀ q : PrimeSpectrum S, RingHom.QuasiFiniteAt f q.asIdeal := by
  sorry

theorem characterize_unramified_at
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) (hfinite : f.FiniteType)
    (hmax : letI : Algebra R S := f.toAlgebra
      letI : Algebra R (Localization.AtPrime q.asIdeal) :=
        Algebra.compHom (Localization.AtPrime q.asIdeal)
          f
      Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) p.asIdeal =
        IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal))
    (hsep : letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
      (Formalization.Books.Algebra.Unit113.residueFieldMapAt f p q hq).toAlgebra
      Module.Finite p.asIdeal.ResidueField q.asIdeal.ResidueField ∧
        Algebra.IsSeparable p.asIdeal.ResidueField q.asIdeal.ResidueField) :
    IsUnramifiedAt f q := by
  sorry

theorem etale_iff_flat_gUnramified
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    RingHom.Etale f ↔ RingHom.Flat f ∧ IsGUnramified f := by
  sorry

theorem etale_iff_flat_unramified_finitePresentation
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    RingHom.Etale f ↔
      RingHom.Flat f ∧ IsUnramified f ∧ f.FinitePresentation := by
  sorry

def PolynomialEtaleDimensionCondition
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    (_a : Fin n → A) : Prop :=
  ∀ m : PrimeSpectrum A, m.asIdeal.IsMaximal →
    ringKrullDim (Localization.AtPrime m.asIdeal) =
      (((n : ℕ∞) : WithBot ℕ∞))

def PolynomialEtaleCotangentCondition
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    (a : Fin n → A) : Prop :=
  Submodule.span A (Set.range (fun i =>
    universalDifferential k A (a i))) = ⊤

theorem characterize_etale_over_polynomial
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    {n : ℕ} (φ : MvPolynomial (Fin n) k →ₐ[k] A)
    (hfinite : φ.toRingHom.FiniteType) :
    RingHom.Etale φ.toRingHom ↔
      PolynomialEtaleDimensionCondition (k := k) (A := A)
          (fun i => φ (MvPolynomial.X i)) ∧
        PolynomialEtaleCotangentCondition (k := k) (A := A)
          (fun i => φ (MvPolynomial.X i)) := by
  sorry

/-! ## 145.8 Local structure of unramified ring maps -/

theorem unramified_locally_standard
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (q : PrimeSpectrum S) (h : IsUnramifiedAt f q) :
    letI : Algebra R S := f.toAlgebra
    ∃ g : S, g ∉ q.asIdeal ∧
      ∃ (S' : Type u) (hS' : CommRing S') (hAlg : Algebra R S'),
        letI : CommRing S' := hS'
        letI : Algebra R S' := hAlg
        IsStandardEtale (algebraMap R S') ∧
          ∃ φ : S' →+* Localization.Away g,
            Function.Surjective φ ∧
              φ.comp (algebraMap R S') = targetLocalizationMap f g := by
  sorry

theorem etale_makes_unramified_closed_at_prime
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) (hfinite : f.FiniteType)
    (hunram : IsUnramifiedAt f q) :
    letI : Algebra R S := f.toAlgebra
    ∃ (R' : Type u) (hR' : CommRing R') (hAlg : Algebra R R'),
      letI : CommRing R' := hR'
      letI : Algebra R R' := hAlg
      RingHom.Etale (algebraMap R R') ∧
            ∃ p' : PrimeSpectrum R',
          PrimeSpectrum.comap (algebraMap R R') p' = p ∧
            ∃ D : BinaryAlgebraProduct R' (R' ⊗[R] S),
              letI : Algebra R' D.A := D.algebraA
              Function.Surjective (algebraMap R' D.A) ∧
                ∃ r : PrimeSpectrum D.A,
                  r.asIdeal = Ideal.map (algebraMap R' D.A) p'.asIdeal ∧
                    PrimeSpectrum.comap
                      (D.leftMap.comp Algebra.TensorProduct.includeRight.toRingHom) r = q := by
  sorry

theorem etale_makes_unramified_closed
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (h : IsUnramified f) :
    letI : Algebra R S := f.toAlgebra
    ∃ (R' : Type u) (hR' : CommRing R') (hAlg : Algebra R R'),
      letI : CommRing R' := hR'
      letI : Algebra R R' := hAlg
      RingHom.Etale (algebraMap R R') ∧
        ∃ p' : PrimeSpectrum R',
          PrimeSpectrum.comap (algebraMap R R') p' = p ∧
            ∃ (D : FiniteAlgebraProduct R' (R' ⊗[R] S)),
              (∀ i, letI : Algebra R' (D.A i) := D.algebraA i
                Function.Surjective (algebraMap R' (D.A i))) ∧
              (letI : Algebra R' D.B := D.algebraB
                ∀ r : PrimeSpectrum D.B,
                  PrimeSpectrum.comap (algebraMap R' D.B) r ≠ p') := by
  sorry

/-! ## 145.9 Henselian local rings -/

abbrev IsHenselian
    (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  HenselianLocalRing R

def IsStrictlyHenselian
    (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  HenselianLocalRing R ∧ IsSepClosed (IsLocalRing.ResidueField R)

def residuePolynomial
    {R : Type u} [CommRing R] [IsLocalRing R]
    (f : Polynomial R) : Polynomial (IsLocalRing.ResidueField R) :=
  Polynomial.map (algebraMap R (IsLocalRing.ResidueField R)) f

def HenselRootLifting
    (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ (f : Polynomial R), f.Monic →
    ∀ a₀ : IsLocalRing.ResidueField R,
      Polynomial.eval a₀ (residuePolynomial f) = 0 →
      Polynomial.eval a₀ (residuePolynomial f.derivative) ≠ 0 →
      ∃ a : R, Polynomial.eval a f = 0 ∧
        algebraMap R (IsLocalRing.ResidueField R) a = a₀

theorem henselian_iff_root_lifting
    (R : Type u) [CommRing R] [IsLocalRing R] :
    IsHenselian R ↔ HenselRootLifting R := by
  sorry

theorem hensel_root_unique
    (R : Type u) [CommRing R] [IsLocalRing R]
    (f : Polynomial R) (a b : R)
    (hfa : Polynomial.eval a f = 0) (hfb : Polynomial.eval b f = 0)
    (hres : a - b ∈ IsLocalRing.maximalIdeal R)
    (hderiv : Polynomial.eval a f.derivative ∉ IsLocalRing.maximalIdeal R) :
    a = b := by
  sorry

def HenselianMonicFactorization
    (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ (f : Polynomial R) (g₀ h₀ : Polynomial (IsLocalRing.ResidueField R)),
    f.Monic → residuePolynomial f = g₀ * h₀ → IsCoprime g₀ h₀ →
    ∃ g h : Polynomial R,
      f = g * h ∧ residuePolynomial g = g₀ ∧ residuePolynomial h = h₀

def HenselianMonicDegreeFactorization
    (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ (f : Polynomial R) (g₀ h₀ : Polynomial (IsLocalRing.ResidueField R)),
    f.Monic → residuePolynomial f = g₀ * h₀ → IsCoprime g₀ h₀ →
    ∃ g h : Polynomial R,
      f = g * h ∧ residuePolynomial g = g₀ ∧ residuePolynomial h = h₀ ∧
        g.natDegree = g₀.natDegree

def HenselianFactorization
    (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ (f : Polynomial R) (g₀ h₀ : Polynomial (IsLocalRing.ResidueField R)),
    residuePolynomial f = g₀ * h₀ → IsCoprime g₀ h₀ →
    ∃ g h : Polynomial R,
      f = g * h ∧ residuePolynomial g = g₀ ∧ residuePolynomial h = h₀

def HenselianDegreeFactorization
    (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ (f : Polynomial R) (g₀ h₀ : Polynomial (IsLocalRing.ResidueField R)),
    residuePolynomial f = g₀ * h₀ → IsCoprime g₀ h₀ →
    ∃ g h : Polynomial R,
      f = g * h ∧ residuePolynomial g = g₀ ∧ residuePolynomial h = h₀ ∧
        g.natDegree = g₀.natDegree

def HenselianEtaleRetractionExists
    (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ (S : Type u) [CommRing S] (f : R →+* S), RingHom.Etale f →
    ∀ (p : PrimeSpectrum R) (q : PrimeSpectrum S),
      p.asIdeal = IsLocalRing.maximalIdeal R →
      PrimeSpectrum.comap f q = p →
      Nonempty (p.asIdeal.ResidueField ≃+* q.asIdeal.ResidueField) →
      ∃ τ : S →+* R, τ.comp f = RingHom.id R

def HenselianEtaleRetractionUnique
    (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ (S : Type u) [CommRing S] (f : R →+* S), RingHom.Etale f →
    ∀ (p : PrimeSpectrum R) (q : PrimeSpectrum S),
      p.asIdeal = IsLocalRing.maximalIdeal R →
      PrimeSpectrum.comap f q = p →
      Nonempty (p.asIdeal.ResidueField ≃+* q.asIdeal.ResidueField) →
      ∃! τ : S →+* R,
        τ.comp f = RingHom.id R ∧
          Ideal.comap τ (IsLocalRing.maximalIdeal R) = q.asIdeal

structure FiniteLocalProductData
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] where
  n : ℕ
  A : Fin n → CommRingCat.{u}
  algebraA : ∀ i, Algebra R (A i)
  localA : ∀ i, IsLocalRing (A i)
  finiteA : ∀ i, letI : Algebra R (A i) := algebraA i
    RingHom.Finite (algebraMap R (A i))
  equiv : S ≃+* (∀ i, A i)

structure HenselianFiniteTypeDecomposition
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] where
  decomposition : BinaryAlgebraProduct R S
  finiteA : letI : Algebra R decomposition.A := decomposition.algebraA
    RingHom.Finite (algebraMap R decomposition.A)
  noQuasiFiniteB : letI : Algebra R decomposition.B := decomposition.algebraB
    ∀ q : PrimeSpectrum decomposition.B,
      ¬ RingHom.QuasiFiniteAt (algebraMap R decomposition.B) q.asIdeal

structure LocalProductData
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] where
  index : Type u
  A : index → CommRingCat.{u}
  algebraA : ∀ i, Algebra R (A i)
  localA : ∀ i, IsLocalRing (A i)
  equiv : S ≃+* (∀ i, A i)

structure HenselianPositiveFiberDecomposition
    (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S] where
  decomposition : BinaryAlgebraProduct R S
  finiteA : letI : Algebra R decomposition.A := decomposition.algebraA
    RingHom.Finite (algebraMap R decomposition.A)
  positiveFiber : letI : Algebra R decomposition.B := decomposition.algebraB
    ∀ q : PrimeSpectrum decomposition.B,
      (PrimeSpectrum.comap (algebraMap R decomposition.B) q).asIdeal =
        IsLocalRing.maximalIdeal R →
      1 ≤ ringKrullDim (Localization.AtPrime q.asIdeal)

structure HenselianQuasiFiniteDecomposition
    (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S] where
  decomposition : BinaryAlgebraProduct R S
  finiteA : letI : Algebra R decomposition.A := decomposition.algebraA
    RingHom.Finite (algebraMap R decomposition.A)
  fiberB_zero : letI : Algebra R decomposition.B := decomposition.algebraB
    Subsingleton (decomposition.B ⊗[R] IsLocalRing.ResidueField R)

structure HenselianCharacterizationData
    (R : Type u) [CommRing R] [IsLocalRing R] where
  condition1 : HenselRootLifting R
  condition2 : ∀ (f : Polynomial R) (a₀ : IsLocalRing.ResidueField R),
    Polynomial.eval a₀ (residuePolynomial f) = 0 →
      Polynomial.eval a₀ (residuePolynomial f.derivative) ≠ 0 →
      ∃ a : R, Polynomial.eval a f = 0 ∧
        algebraMap R (IsLocalRing.ResidueField R) a = a₀
  condition3 : HenselianMonicFactorization R
  condition4 : HenselianMonicDegreeFactorization R
  condition5 : HenselianFactorization R
  condition6 : HenselianDegreeFactorization R
  condition7 : HenselianEtaleRetractionExists R
  condition8 : HenselianEtaleRetractionUnique R
  condition9 : ∀ (S : Type u) [CommRing S] (f : R →+* S), RingHom.Finite f →
    letI : Algebra R S := f.toAlgebra
    Nonempty (LocalProductData R S)
  condition10 : ∀ (S : Type u) [CommRing S] (f : R →+* S), RingHom.Finite f →
    letI : Algebra R S := f.toAlgebra
    Nonempty (FiniteLocalProductData R S)
  condition11 : ∀ (S : Type u) [CommRing S] (f : R →+* S), RingHom.FiniteType f →
    letI : Algebra R S := f.toAlgebra
    Nonempty (HenselianFiniteTypeDecomposition R S)
  condition12 : ∀ (S : Type u) [CommRing S] (f : R →+* S), RingHom.FiniteType f →
    letI : Algebra R S := f.toAlgebra
    Nonempty (HenselianPositiveFiberDecomposition R S)
  condition13 : ∀ (S : Type u) [CommRing S] (f : R →+* S),
    RingHom.QuasiFinite f →
    letI : Algebra R S := f.toAlgebra
    Nonempty (HenselianQuasiFiniteDecomposition R S)

theorem characterize_henselian
    (R : Type u) [CommRing R] [IsLocalRing R] :
    IsHenselian R ↔ Nonempty (HenselianCharacterizationData R) := by
  sorry

structure HenselianFiniteProductData
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [HenselianLocalRing R] where
  product : FiniteLocalProductData R S
  henselianA : ∀ i, HenselianLocalRing (product.A i)

theorem finite_over_henselian
    {R S : Type u} [CommRing R] [HenselianLocalRing R]
    [CommRing S] (f : R →+* S) (hfinite : RingHom.Finite f) :
    letI : Algebra R S := f.toAlgebra
    Nonempty (HenselianFiniteProductData R S) := by
  sorry

theorem finite_local_over_henselian
    {R S : Type u} [CommRing R] [HenselianLocalRing R]
    [CommRing S] [IsLocalRing S]
    (f : R →+* S) (hfinite : RingHom.Finite f) :
    HenselianLocalRing S ∧ IsLocalHom f := by
  sorry

theorem quasiFiniteAt_localization_henselian
    {R S : Type u} [CommRing R] [HenselianLocalRing R]
    [CommRing S] (f : R →+* S) (q : PrimeSpectrum S)
    (hq : (PrimeSpectrum.comap f q).asIdeal = IsLocalRing.maximalIdeal R)
    (hquasi : RingHom.QuasiFiniteAt f q.asIdeal) :
    HenselianLocalRing (Localization.AtPrime q.asIdeal) ∧
      RingHom.Finite (atPrimeLocalizationMap f q) := by
  sorry

theorem quasiFinite_localization_henselian
    {R S : Type u} [CommRing R] [HenselianLocalRing R]
    [CommRing S] (f : R →+* S) (hquasi : RingHom.QuasiFinite f) :
    ∀ (q : PrimeSpectrum S),
      (PrimeSpectrum.comap f q).asIdeal = IsLocalRing.maximalIdeal R →
      HenselianLocalRing (Localization.AtPrime q.asIdeal) ∧
        RingHom.Finite (atPrimeLocalizationMap f q) := by
  sorry

structure HenselianMopUpData
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [HenselianLocalRing R] where
  product : FiniteAlgebraProduct R S
  localFactors : ∀ i, IsLocalRing (product.A i)
  finiteFactors : ∀ i, letI : Algebra R (product.A i) := product.algebraA i
    RingHom.Finite (algebraMap R (product.A i))
  noQuasiFiniteB : letI : Algebra R product.B := product.algebraB
    ∀ q : PrimeSpectrum product.B,
      (PrimeSpectrum.comap (algebraMap R product.B) q).asIdeal ≠
        IsLocalRing.maximalIdeal R

theorem mop_up_henselian
    {R S : Type u} [CommRing R] [HenselianLocalRing R]
    [CommRing S] (f : R →+* S) (hfiniteType : RingHom.FiniteType f) :
    letI : Algebra R S := f.toAlgebra
    Nonempty (HenselianMopUpData R S) := by
  sorry

structure StrictHenselianMopUpData
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)] where
  product : FiniteAlgebraProduct R S
  localFactors : ∀ i, IsLocalRing (product.A i)
  finiteFactors : ∀ i, letI : Algebra R (product.A i) := product.algebraA i
    RingHom.Finite (algebraMap R (product.A i))
  purelyInseparableResidues : ∀ i (q : PrimeSpectrum (product.A i)),
    letI : Algebra R (product.A i) := product.algebraA i
    ∀ hq : (PrimeSpectrum.comap (algebraMap R (product.A i)) q).asIdeal =
      IsLocalRing.maximalIdeal R,
      let p : PrimeSpectrum R :=
        ⟨IsLocalRing.maximalIdeal R, inferInstance⟩
      let hp : PrimeSpectrum.comap (algebraMap R (product.A i)) q = p := by
        apply PrimeSpectrum.ext
        exact hq
      letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
        (Formalization.Books.Algebra.Unit113.residueFieldMapAt
          (algebraMap R (product.A i)) p q hp).toAlgebra
      IsPurelyInseparable p.asIdeal.ResidueField q.asIdeal.ResidueField
  noQuasiFiniteB : letI : Algebra R product.B := product.algebraB
    ∀ q : PrimeSpectrum product.B,
      (PrimeSpectrum.comap (algebraMap R product.B) q).asIdeal ≠
        IsLocalRing.maximalIdeal R

theorem mop_up_strictly_henselian
    {R S : Type u} [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)] [CommRing S]
    (f : R →+* S) (hfiniteType : RingHom.FiniteType f) :
    letI : Algebra R S := f.toAlgebra
    Nonempty (StrictHenselianMopUpData R S) := by
  sorry

/- The source's finite étale/residue-field category equivalence is exposed
   as a fully faithful and essentially surjective correspondence. -/
structure FiniteEtaleResidueAlgebraData
    (R S : Type u) [CommRing R] [IsLocalRing R] [CommRing S]
    (f : R →+* S) where
  residueMap : IsLocalRing.ResidueField R →+*
    S ⧸ Ideal.map f (IsLocalRing.maximalIdeal R)
  finite : RingHom.Finite residueMap
  etale : RingHom.Etale residueMap
  factor : ∀ r : R,
    residueMap (algebraMap R (IsLocalRing.ResidueField R) r) =
      Ideal.Quotient.mk (Ideal.map f (IsLocalRing.maximalIdeal R)) (f r)

structure FiniteEtaleResidueLiftData
    (R L : Type u) [CommRing R] [IsLocalRing R] [HenselianLocalRing R]
    [CommRing L] [Algebra (IsLocalRing.ResidueField R) L]
    (hfinite : RingHom.Finite (algebraMap
      (IsLocalRing.ResidueField R) L))
    (hetale : RingHom.Etale (algebraMap
      (IsLocalRing.ResidueField R) L)) where
  S : Type u
  [commRingS : CommRing S]
  map : R →+* S
  finite : RingHom.Finite map
  etale : RingHom.Etale map
  residue : FiniteEtaleResidueAlgebraData R S map
  residueEquiv : L ≃+* S ⧸ Ideal.map map (IsLocalRing.maximalIdeal R)
  residueEquiv_compatible :
    residueEquiv.toRingHom.comp
        (algebraMap (IsLocalRing.ResidueField R) L) =
      residue.residueMap

theorem henselian_finite_etale_residue_lift
    (R L : Type u) [CommRing R] [HenselianLocalRing R]
    [CommRing L] [Algebra (IsLocalRing.ResidueField R) L]
    (hfinite : RingHom.Finite
      (algebraMap (IsLocalRing.ResidueField R) L))
    (hetale : RingHom.Etale
      (algebraMap (IsLocalRing.ResidueField R) L)) :
    Nonempty (FiniteEtaleResidueLiftData R L hfinite hetale) := by
  sorry

structure FiniteEtaleResidueHom
    (R S T : Type u) [CommRing R] [IsLocalRing R]
    [CommRing S] [CommRing T]
    (f : R →+* S) (g : R →+* T)
    (residueS : FiniteEtaleResidueAlgebraData R S f)
    (residueT : FiniteEtaleResidueAlgebraData R T g) where
  map : S →+* T
  commutes : map.comp f = g
  residueMap :
    (S ⧸ Ideal.map f (IsLocalRing.maximalIdeal R)) →+*
      T ⧸ Ideal.map g (IsLocalRing.maximalIdeal R)
  residue_commutes :
    residueMap.comp
        (Ideal.Quotient.mk (Ideal.map f (IsLocalRing.maximalIdeal R))) =
      (Ideal.Quotient.mk (Ideal.map g (IsLocalRing.maximalIdeal R))).comp map

structure FiniteEtaleResidueCorrespondence
    (R : Type u) [CommRing R] [HenselianLocalRing R] where
  residue : ∀ (S : Type u) [CommRing S] (f : R →+* S),
    RingHom.Etale f → RingHom.Finite f →
    FiniteEtaleResidueAlgebraData R S f
  fullyFaithful :
    ∀ (S T : Type u) [CommRing S] [CommRing T]
      (f : R →+* S) (g : R →+* T)
      (hf : RingHom.Etale f) (hfinitef : RingHom.Finite f)
      (hg : RingHom.Etale g) (hfinteg : RingHom.Finite g),
      Nonempty
        (({h : S →+* T // h.comp f = g}) ≃
          FiniteEtaleResidueHom R S T f g
            (residue S f hf hfinitef) (residue T g hg hfinteg))
  essentiallySurjective :
    ∀ (L : Type u) [CommRing L]
      [Algebra (IsLocalRing.ResidueField R) L]
      (hfinite : RingHom.Finite
        (algebraMap (IsLocalRing.ResidueField R) L))
      (hetale : RingHom.Etale
        (algebraMap (IsLocalRing.ResidueField R) L)),
      Nonempty (FiniteEtaleResidueLiftData R L hfinite hetale)

theorem henselian_finite_etale_residue_correspondence
    (R : Type u) [CommRing R] [HenselianLocalRing R] :
    Nonempty (FiniteEtaleResidueCorrespondence R) := by
  sorry

theorem unramified_over_strictly_henselian
    {R S : Type u} [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)] [CommRing S]
    (f : R →+* S) (h : IsUnramified f) :
    letI : Algebra R S := f.toAlgebra
    ∃ D : FiniteAlgebraProduct R S,
      (∀ i, letI : Algebra R (D.A i) := D.algebraA i
        Function.Surjective (algebraMap R (D.A i))) ∧
      (letI : Algebra R D.B := D.algebraB
        ∀ q : PrimeSpectrum D.B,
          (PrimeSpectrum.comap (algebraMap R D.B) q).asIdeal ≠
            IsLocalRing.maximalIdeal R) := by
  sorry

def IsCompleteLocalRing
    (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  IsAdicComplete (IsLocalRing.maximalIdeal R) R

theorem complete_local_henselian
    (R : Type u) [CommRing R] [IsLocalRing R]
    (hcomplete : IsCompleteLocalRing R) :
    HenselianLocalRing R := by
  sorry

theorem local_dimension_zero_henselian
    (R : Type u) [CommRing R] [IsLocalRing R]
    (hdim : ringKrullDim R = 0) :
    HenselianLocalRing R := by
  sorry

/-! The remaining assertions in the section use the canonical residue-field
maps from Chapter 113. -/

def maximalPrimeSpectrum
    (R : Type u) [CommRing R] [IsLocalRing R] : PrimeSpectrum R :=
  ⟨IsLocalRing.maximalIdeal R, inferInstance⟩

theorem map_into_henselian
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [HenselianLocalRing S]
    (g : R →+* S) (f : R →+* A) (hetale : RingHom.Etale f)
    (p : PrimeSpectrum R) (q : PrimeSpectrum A)
    (s : PrimeSpectrum S)
    (hs : s.asIdeal = IsLocalRing.maximalIdeal S)
    (hp : PrimeSpectrum.comap g s = p)
    (hq : PrimeSpectrum.comap f q = p)
    (τ : q.asIdeal.ResidueField →+* s.asIdeal.ResidueField)
    (hτ : τ.comp
        (Formalization.Books.Algebra.Unit113.residueFieldMapAt f p q hq) =
      Formalization.Books.Algebra.Unit113.residueFieldMapAt g p s hp) :
    ∃! φ : A →+* S,
      φ.comp f = g ∧
        ∃ hφ : PrimeSpectrum.comap φ s = q,
          Formalization.Books.Algebra.Unit113.residueFieldMapAt φ q s hφ = τ := by
  sorry

def MvPolynomialSolutionSet
    {R : Type u} [CommRing R] {n : ℕ}
    (P : Fin n → MvPolynomial (Fin n) R) : Set (Fin n → R) :=
  {x | ∀ i, MvPolynomial.eval x (P i) = 0}

def mapMvPolynomialSystem
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) {n : ℕ} (P : Fin n → MvPolynomial (Fin n) R) :
    Fin n → MvPolynomial (Fin n) S :=
  fun i => MvPolynomial.map φ (P i)

def polynomialRelationsIdeal
    {R : Type u} [CommRing R] {n : ℕ}
    (P : Fin n → MvPolynomial (Fin n) R) :
    Ideal (MvPolynomial (Fin n) R) :=
  Ideal.span (Set.range P)

abbrev polynomialRelationsRing
    {R : Type u} [CommRing R] {n : ℕ}
    (P : Fin n → MvPolynomial (Fin n) R) : Type u :=
  MvPolynomial (Fin n) R ⧸ polynomialRelationsIdeal P

def EtalePolynomialSystem
    {R : Type u} [CommRing R] {n : ℕ}
    (P : Fin n → MvPolynomial (Fin n) R) : Prop :=
  RingHom.Etale (algebraMap R (polynomialRelationsRing P))

theorem strictly_henselian_solutions
    {R S : Type u} [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    [CommRing S] [HenselianLocalRing S]
    [IsSepClosed (IsLocalRing.ResidueField S)]
    (φ : R →+* S) (hlocal : IsLocalHom φ)
    {n : ℕ} (P : Fin n → MvPolynomial (Fin n) R)
    (hetale : EtalePolynomialSystem P) :
    ∃ e :
        {x : Fin n → R // x ∈ MvPolynomialSolutionSet P} ≃
          {y : Fin n → S //
            y ∈ MvPolynomialSolutionSet (mapMvPolynomialSystem φ P)},
      ∀ x, (e x : Fin n → S) = fun i => φ (x.1 i) := by
  sorry

/- The exact countably generated Mittag--Leffler splitting statement is
   already available as
   `Unit91.split_mittagLeffler_over_henselian_local`; the earlier chapter
   declaration has the same hypotheses and conclusion, so no parallel
   wrapper is introduced here. -/

/-! ## 145.10 Filtered colimits of étale ring maps -/

def IsFilteredColimitOfEtale
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A) : Prop :=
  Nonempty (Formalization.Books.Algebra.Unit127.FilteredAlgebraColimitIn f
    {X | RingHom.Etale X.hom.hom})

theorem baseChange_colimit_etale
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    (f : R →+* A) (g : R →+* R')
    (hA : IsFilteredColimitOfEtale f) :
    IsFilteredColimitOfEtale
      (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g) := by
  sorry

theorem composition_colimit_etale
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (hB : IsFilteredColimitOfEtale f)
    (hC : IsFilteredColimitOfEtale g) :
    IsFilteredColimitOfEtale (g.comp f) := by
  sorry

theorem colimit_colimit_etale
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A)
    (D : Formalization.Books.Algebra.Unit127.DirectedAlgebraColimit f)
    (hstage : letI : Preorder D.index := D.indexPreorder
      ∀ i, IsFilteredColimitOfEtale (D.diagram.obj i).hom.hom) :
    IsFilteredColimitOfEtale f := by
  sorry

theorem colimit_colimit_etale_better
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A)
    (D : Formalization.Books.Algebra.Unit127.DirectedRingMapColimit f)
    (hstage : letI : Preorder D.index := D.indexPreorder
      ∀ i, IsFilteredColimitOfEtale (D.stageMap i)) :
    IsFilteredColimitOfEtale f := by
  sorry

theorem colimits_of_etale
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : R →+* B) (φ : A →+* B)
    (hcompat : φ.comp f = g)
    (hA : IsFilteredColimitOfEtale f)
    (hB : IsFilteredColimitOfEtale g) :
    IsFilteredColimitOfEtale φ := by
  sorry

theorem map_into_henselian_colimit
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [HenselianLocalRing S]
    (g : R →+* S) (f : R →+* A)
    (hcolimit : IsFilteredColimitOfEtale f)
    (p : PrimeSpectrum R) (q : PrimeSpectrum A)
    (s : PrimeSpectrum S)
    (hs : s.asIdeal = IsLocalRing.maximalIdeal S)
    (hp : PrimeSpectrum.comap g s = p)
    (hq : PrimeSpectrum.comap f q = p)
    (τ : q.asIdeal.ResidueField →+* s.asIdeal.ResidueField)
    (hτ : τ.comp
        (Formalization.Books.Algebra.Unit113.residueFieldMapAt f p q hq) =
      Formalization.Books.Algebra.Unit113.residueFieldMapAt g p s hp) :
    ∃! φ : A →+* S,
      φ.comp f = g ∧
        ∃ hφ : PrimeSpectrum.comap φ s = q,
          Formalization.Books.Algebra.Unit113.residueFieldMapAt φ q s hφ = τ := by
  sorry

theorem uniqueness_henselian
    {R S S' K : Type u} [CommRing R] [CommRing S] [CommRing S']
    [HenselianLocalRing S] [HenselianLocalRing S'] [Field K]
    (f : R →+* S) (f' : R →+* S')
    (u : S →+* K) (u' : S' →+* K)
    (hcompat : u.comp f = u'.comp f')
    (hS : IsFilteredColimitOfEtale f)
    (hS' : IsFilteredColimitOfEtale f')
    (hu_surj : Function.Surjective u)
    (hu'_surj : Function.Surjective u')
    (hu_ker : RingHom.ker u = IsLocalRing.maximalIdeal S)
    (hu'_ker : RingHom.ker u' = IsLocalRing.maximalIdeal S') :
    ∃! e : S ≃+* S',
      e.toRingHom.comp f = f' ∧ u'.comp e.toRingHom = u := by
  sorry

theorem colimit_henselian
    {S : Type u} [CommRing S]
    (D : Formalization.Books.Algebra.Unit127.DirectedRingColimit (R := S))
    (hlocal : letI : Preorder D.index := D.indexPreorder
      ∀ i, IsLocalRing (D.diagram.obj i))
    (hhenselian : letI : Preorder D.index := D.indexPreorder
      ∀ i, HenselianLocalRing (D.diagram.obj i))
    (htransition : letI : Preorder D.index := D.indexPreorder
      ∀ {i j} (hij : D.indexPreorder.le i j),
        IsLocalHom (D.transitionMap hij)) :
    IsLocalRing S ∧ HenselianLocalRing S := by
  sorry

theorem colimit_strictly_henselian
    {S : Type u} [CommRing S]
    (D : Formalization.Books.Algebra.Unit127.DirectedRingColimit (R := S))
    (hlocal : letI : Preorder D.index := D.indexPreorder
      ∀ i, IsLocalRing (D.diagram.obj i))
    (hhenselian : letI : Preorder D.index := D.indexPreorder
      ∀ i, HenselianLocalRing (D.diagram.obj i))
    (htransition : letI : Preorder D.index := D.indexPreorder
      ∀ {i j} (hij : D.indexPreorder.le i j),
        IsLocalHom (D.transitionMap hij))
    (hsep : letI : Preorder D.index := D.indexPreorder
      ∀ i, IsSepClosed
        (IsLocalRing.ResidueField (D.diagram.obj i))) :
    ∃ hS : IsLocalRing S,
      letI : IsLocalRing S := hS
      HenselianLocalRing S ∧ IsSepClosed (IsLocalRing.ResidueField S) := by
  sorry

/-! ## 145.11 Henselization and strict henselization -/

def ResidueFieldEquivalenceOver
    {R S : Type u} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S]
    (f : R →+* S) (e : IsLocalRing.ResidueField R ≃+*
      IsLocalRing.ResidueField S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  e.toRingHom.comp (algebraMap R (IsLocalRing.ResidueField R)) =
    (algebraMap S (IsLocalRing.ResidueField S)).comp f

def StrictResidueFieldData
    {R S K : Type u} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    (f : R →+* S) (e : K ≃+* IsLocalRing.ResidueField S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R K :=
    Algebra.compHom K (algebraMap R (IsLocalRing.ResidueField R))
  e.toRingHom.comp (algebraMap R K) =
    (algebraMap S (IsLocalRing.ResidueField S)).comp f

def IsHenselization
    {R S : Type u} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S]
    (f : R →+* S) : Prop :=
  IsLocalHom f ∧ HenselianLocalRing S ∧
    IsFilteredColimitOfEtale f ∧
      Ideal.map f (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S ∧
        ∃ e : IsLocalRing.ResidueField R ≃+*
            IsLocalRing.ResidueField S,
          ResidueFieldEquivalenceOver f e

def IsStrictHenselization
    {R S K : Type u} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    (f : R →+* S) : Prop :=
  IsLocalHom f ∧ HenselianLocalRing S ∧
    IsSepClosed (IsLocalRing.ResidueField S) ∧
      IsFilteredColimitOfEtale f ∧
        Ideal.map f (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S ∧
          ∃ e : K ≃+* IsLocalRing.ResidueField S,
            StrictResidueFieldData f e

structure HenselizationWitness
    (R : Type u) [CommRing R] [IsLocalRing R] where
  S : Type u
  [commRingS : CommRing S]
  [localS : IsLocalRing S]
  map : R →+* S
  property : IsHenselization map

structure StrictHenselizationWitness
    (R K : Type u) [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField R) K]
    [IsSepClosed K] where
  S : Type u
  [commRingS : CommRing S]
  [localS : IsLocalRing S]
  map : R →+* S
  property : IsStrictHenselization (K := K) map

theorem henselization_exists
    (R : Type u) [CommRing R] [IsLocalRing R] :
    Nonempty (HenselizationWitness R) := by
  sorry

theorem strict_henselization_exists
    (R K : Type u) [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField R) K]
    [IsSepClosed K] :
    Nonempty (StrictHenselizationWitness R K) := by
  sorry

def ResidueEquivCompatible
    {S S' : Type u} [CommRing S] [IsLocalRing S]
    [CommRing S'] [IsLocalRing S']
    (e : S ≃+* S')
    (ρ : IsLocalRing.ResidueField S ≃+*
      IsLocalRing.ResidueField S') : Prop :=
  ∀ x : S,
    ρ (algebraMap S (IsLocalRing.ResidueField S) x) =
      algebraMap S' (IsLocalRing.ResidueField S') (e x)

theorem henselization_unique
    {R S S' : Type u} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [CommRing S'] [IsLocalRing S']
    (f : R →+* S) (f' : R →+* S')
    (hf : IsHenselization f) (hf' : IsHenselization f') :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R S' := f'.toAlgebra
    ∃! e : S ≃ₐ[R] S', e.toRingHom.comp f = f' := by
  sorry

theorem strict_henselization_unique
    {R S S' K : Type u} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [CommRing S'] [IsLocalRing S']
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField R) K]
    [IsSepClosed K]
    (f : R →+* S) (f' : R →+* S')
    (hf : IsStrictHenselization (K := K) f)
    (hf' : IsStrictHenselization (K := K) f')
    (ρ : IsLocalRing.ResidueField S ≃+*
      IsLocalRing.ResidueField S') :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R S' := f'.toAlgebra
    ∃! e : S ≃ₐ[R] S',
      e.toRingHom.comp f = f' ∧ ResidueEquivCompatible e.toRingEquiv ρ := by
  sorry

structure HenselizationAtPrimeWitness
    (A T : Type u) [CommRing A] [CommRing T] [IsLocalRing T]
    (q : PrimeSpectrum A) where
  map : Localization.AtPrime q.asIdeal →+* T
  property : IsHenselization map

theorem henselization_functorial_prepare
    {R S A T : Type u} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [CommRing A]
    [CommRing T] [IsLocalRing T]
    (φ : R →+* S) (hφ : IsLocalHom φ)
    (sh : S →+* T) (hsh : IsHenselization sh)
    (f : R →+* A) (hetale : RingHom.Etale f)
    (q : PrimeSpectrum A)
    (hq : PrimeSpectrum.comap f q = maximalPrimeSpectrum R)
    (hres : Nonempty
      (q.asIdeal.ResidueField ≃+* IsLocalRing.ResidueField R)) :
    ∃! ψ : A →+* T,
      ψ.comp f = sh.comp φ ∧
        Ideal.comap ψ (IsLocalRing.maximalIdeal T) = q.asIdeal := by
  sorry

theorem henselization_functorial
    {R S Rh Sh : Type u} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [CommRing Rh] [IsLocalRing Rh]
    [CommRing Sh] [IsLocalRing Sh]
    (φ : R →+* S) (hφ : IsLocalHom φ)
    (f : R →+* Rh) (hf : IsHenselization f)
    (g : S →+* Sh) (hg : IsHenselization g) :
    ∃! ψ : Rh →+* Sh,
      ψ.comp f = g.comp φ ∧ IsLocalHom ψ := by
  sorry

structure HenselizationDifferentData
    (R : Type u) [CommRing R] (p : PrimeSpectrum R) where
  localHenselization : HenselizationWitness (Localization.AtPrime p.asIdeal)
  target : Type u
  [commRingTarget : CommRing target]
  map : R →+* target
  colimit : Formalization.Books.Algebra.Unit127.DirectedAlgebraColimit map
  stageEtale : letI : Preorder colimit.index := colimit.indexPreorder
    ∀ i, RingHom.Etale (colimit.diagram.obj i).hom.hom
  stagePrime : letI : Preorder colimit.index := colimit.indexPreorder
    ∀ i, PrimeSpectrum (colimit.diagram.obj i).right
  stageLiesOver : letI : Preorder colimit.index := colimit.indexPreorder
    ∀ i, PrimeSpectrum.comap (colimit.diagram.obj i).hom.hom (stagePrime i) = p
  stageResidue : letI : Preorder colimit.index := colimit.indexPreorder
    ∀ i, Nonempty (p.asIdeal.ResidueField ≃+*
      (stagePrime i).asIdeal.ResidueField)
  targetEquiv :
    letI : CommRing localHenselization.S := localHenselization.commRingS
    letI : IsLocalRing localHenselization.S := localHenselization.localS
    target ≃+* localHenselization.S
  targetEquiv_commutes :
    letI : CommRing localHenselization.S := localHenselization.commRingS
    letI : IsLocalRing localHenselization.S := localHenselization.localS
    targetEquiv.toRingHom.comp map =
      localHenselization.map.comp
        (algebraMap R (Localization.AtPrime p.asIdeal))
  localizedStageEquiv : letI : Preorder colimit.index := colimit.indexPreorder
    ∀ i, Nonempty ((colimit.diagram.obj i).right ≃+*
      Localization.AtPrime (stagePrime i).asIdeal)

theorem henselization_different
    (R : Type u) [CommRing R] (p : PrimeSpectrum R) :
    Nonempty (HenselizationDifferentData R p) := by
  sorry

structure HenselizationStrictDiagramData
    (R K : Type u) [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField R) K]
    [IsSepClosed K] where
  henselization : HenselizationWitness R
  strictHenselization : StrictHenselizationWitness R K
  comparison :
    letI : CommRing henselization.S := henselization.commRingS
    letI : IsLocalRing henselization.S := henselization.localS
    letI : CommRing strictHenselization.S := strictHenselization.commRingS
    letI : IsLocalRing strictHenselization.S := strictHenselization.localS
    henselization.S →+* strictHenselization.S
  comparison_property :
    letI : CommRing henselization.S := henselization.commRingS
    letI : IsLocalRing henselization.S := henselization.localS
    letI : CommRing strictHenselization.S := strictHenselization.commRingS
    letI : IsLocalRing strictHenselization.S := strictHenselization.localS
    IsLocalHom comparison ∧
      comparison.comp henselization.map = strictHenselization.map
  residue_lift :
    letI : CommRing henselization.S := henselization.commRingS
    letI : IsLocalRing henselization.S := henselization.localS
    IsLocalRing.ResidueField henselization.S →+* K
  residue_lift_property :
    letI : CommRing henselization.S := henselization.commRingS
    letI : IsLocalRing henselization.S := henselization.localS
    letI : Algebra R henselization.S := henselization.map.toAlgebra
    letI : Algebra R K :=
      Algebra.compHom K (algebraMap R (IsLocalRing.ResidueField R))
    residue_lift.comp (algebraMap R
      (IsLocalRing.ResidueField henselization.S)) = algebraMap R K

theorem henselization_strict_henselization_exists
    (R K : Type u) [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField R) K]
    [IsSepClosed K] :
    Nonempty (HenselizationStrictDiagramData R K) := by
  sorry

theorem henselization_map_flat_local
    {R S : Type u} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S]
    (f : R →+* S) (hf : IsHenselization f) :
    RingHom.Flat f ∧ IsLocalHom f := by
  sorry

theorem strict_henselization_map_flat_local
    {R S K : Type u} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    (f : R →+* S) (hf : IsStrictHenselization (K := K) f) :
    RingHom.Flat f ∧ IsLocalHom f := by
  sorry

theorem henselization_strict_comparison_flat_local
    {R K : Type u} [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField R) K]
    [IsSepClosed K]
    (D : HenselizationStrictDiagramData R K) :
    letI : CommRing D.henselization.S := D.henselization.commRingS
    letI : IsLocalRing D.henselization.S := D.henselization.localS
    letI : CommRing D.strictHenselization.S := D.strictHenselization.commRingS
    letI : IsLocalRing D.strictHenselization.S := D.strictHenselization.localS
    RingHom.Flat D.henselization.map ∧
      RingHom.Flat D.comparison ∧ RingHom.Flat D.strictHenselization.map ∧
        IsLocalHom D.henselization.map ∧ IsLocalHom D.comparison ∧
          IsLocalHom D.strictHenselization.map := by
  sorry

structure StrictHenselizationUnionData
    (Rh Rsh : Type u) [CommRing Rh] [CommRing Rsh]
    [Algebra Rh Rsh] where
  index : Type u
  [indexPreorder : Preorder index]
  directed : IsDirectedSet index
  stage : index → Subring Rsh
  stageMap : ∀ i, Rh →+* stage i
  stageFinite : ∀ i, RingHom.Finite (stageMap i)
  stageEtale : ∀ i, RingHom.Etale (stageMap i)
  stageLocal : ∀ i, IsLocalRing (stage i)
  stageIntoTarget : ∀ i,
    (stage i).subtype.comp (stageMap i) = algebraMap Rh Rsh
  stageMonotone : ∀ {i j}, indexPreorder.le i j →
    (stage i : Set Rsh) ⊆ stage j
  union : ⋃ i, (stage i : Set Rsh) = Set.univ

theorem strict_henselization_is_union_of_finite_etale_local_extensions
    {R Rh Rsh K : Type u} [CommRing R] [IsLocalRing R]
    [CommRing Rh] [IsLocalRing Rh] [CommRing Rsh] [IsLocalRing Rsh]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField R) K]
    [IsSepClosed K]
    (f : R →+* Rh) (hf : IsHenselization f)
    (g : R →+* Rsh) (hg : IsStrictHenselization (K := K) g)
    (lift : Rh →+* Rsh) (hlift : lift.comp f = g) :
    letI : Algebra Rh Rsh := lift.toAlgebra
    Nonempty (StrictHenselizationUnionData Rh Rsh) := by
  sorry

theorem henselization_improve
    {R S Rh Sh : Type u} [CommRing R] [CommRing S]
    [CommRing Rh] [IsLocalRing Rh] [CommRing Sh] [IsLocalRing Sh]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p)
    (rh : Localization.AtPrime p.asIdeal →+* Rh)
    (sh : Localization.AtPrime q.asIdeal →+* Sh)
    (hrh : IsHenselization rh) (hsh : IsHenselization sh) :
    letI : Algebra R (Localization.AtPrime p.asIdeal) :=
      (algebraMap R (Localization.AtPrime p.asIdeal)).toAlgebra
    letI : Algebra R Rh :=
      Algebra.compHom Rh (rh.comp
        (algebraMap R (Localization.AtPrime p.asIdeal)))
    letI : Algebra R S := f.toAlgebra
    ∃ r : PrimeSpectrum (Rh ⊗[R] S),
      PrimeSpectrum.comap
          (Algebra.TensorProduct.includeLeft (R := R) (S := R)
            (A := Rh) (B := S)).toRingHom r =
          maximalPrimeSpectrum Rh ∧
        PrimeSpectrum.comap
            (Algebra.TensorProduct.includeRight (R := R) (A := Rh) (B := S)).toRingHom r = q ∧
          (∀ r' : PrimeSpectrum (Rh ⊗[R] S),
            PrimeSpectrum.comap
                (Algebra.TensorProduct.includeLeft (R := R) (S := R)
                  (A := Rh) (B := S)).toRingHom r' =
                maximalPrimeSpectrum Rh →
              PrimeSpectrum.comap
                  (Algebra.TensorProduct.includeRight (R := R) (A := Rh) (B := S)).toRingHom r' = q →
              r' = r) ∧
            Nonempty (HenselizationAtPrimeWitness (Rh ⊗[R] S) Sh r) := by
  sorry

structure StrictHenselizationAtPrimeWitness
    (A T K : Type u) [CommRing A] [CommRing T] [IsLocalRing T]
    [Field K] (q : PrimeSpectrum A)
    [Algebra (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) K] where
  map : Localization.AtPrime q.asIdeal →+* T
  property : IsStrictHenselization (K := K) map

structure ResidueFieldEmbeddingOver
    {R A K : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (p : PrimeSpectrum R) (q : PrimeSpectrum A)
    (hq : PrimeSpectrum.comap f q = p) [Field K]
    [Algebra p.asIdeal.ResidueField K] where
  map : q.asIdeal.ResidueField →+* K
  compatible :
    map.comp
        (Formalization.Books.Algebra.Unit113.residueFieldMapAt f p q hq) =
      algebraMap p.asIdeal.ResidueField K

theorem strict_henselization_functorial_prepare
    {R S A T K : Type u} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [CommRing A]
    [CommRing T] [IsLocalRing T] [Field K]
    [Algebra (IsLocalRing.ResidueField S) K]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField S) K]
    [IsSepClosed K]
    (φ : R →+* S) (hφ : IsLocalHom φ)
    (sh : S →+* T)
    (hsh : IsStrictHenselization (K := K) sh)
    (f : R →+* A) (hetale : RingHom.Etale f)
    (q : PrimeSpectrum A)
    (hq : PrimeSpectrum.comap f q = maximalPrimeSpectrum R)
    (s : PrimeSpectrum S) (hs : s.asIdeal = IsLocalRing.maximalIdeal S)
    (t : PrimeSpectrum T) (ht : t.asIdeal = IsLocalRing.maximalIdeal T)
    (hφs : PrimeSpectrum.comap φ s = maximalPrimeSpectrum R)
    (τ : q.asIdeal.ResidueField →+* K)
    (σ : s.asIdeal.ResidueField →+* K)
    (hτ : τ.comp
        (Formalization.Books.Algebra.Unit113.residueFieldMapAt f
          (maximalPrimeSpectrum R) q hq) =
      σ.comp
        (Formalization.Books.Algebra.Unit113.residueFieldMapAt φ
          (maximalPrimeSpectrum R) s hφs))
    (e : K ≃+* t.asIdeal.ResidueField) :
    ∃! ψ : A →+* T,
      ψ.comp f = sh.comp φ ∧
        ∃ hψ : PrimeSpectrum.comap ψ t = q,
          Formalization.Books.Algebra.Unit113.residueFieldMapAt ψ q t hψ =
            e.toRingHom.comp τ := by
  sorry

theorem strict_henselization_functorial
    {R S Rh Sh K₁ K₂ : Type u} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [CommRing Rh] [IsLocalRing Rh]
    [CommRing Sh] [IsLocalRing Sh] [Field K₁] [Field K₂]
    [Algebra (IsLocalRing.ResidueField R) K₁]
    [Algebra (IsLocalRing.ResidueField S) K₂]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField R) K₁]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField S) K₂]
    [IsSepClosed K₁] [IsSepClosed K₂]
    (φ : R →+* S) (hφ : IsLocalHom φ)
    (f : R →+* Rh) (g : S →+* Sh)
    (hf : IsStrictHenselization (K := K₁) f)
    (hg : IsStrictHenselization (K := K₂) g)
    (r : PrimeSpectrum Rh) (hr : r.asIdeal = IsLocalRing.maximalIdeal Rh)
    (s : PrimeSpectrum Sh) (hs : s.asIdeal = IsLocalRing.maximalIdeal Sh)
    (e₁ : K₁ ≃+* r.asIdeal.ResidueField)
    (e₂ : K₂ ≃+* s.asIdeal.ResidueField)
    (ρ : K₁ →+* K₂)
    (β : IsLocalRing.ResidueField R →+*
      IsLocalRing.ResidueField S)
    (hβ : β.comp (algebraMap R (IsLocalRing.ResidueField R)) =
      (algebraMap S (IsLocalRing.ResidueField S)).comp φ)
    (hρ : ρ.comp (algebraMap (IsLocalRing.ResidueField R) K₁) =
      (algebraMap (IsLocalRing.ResidueField S) K₂).comp β) :
    ∃! ψ : Rh →+* Sh,
      ψ.comp f = g.comp φ ∧ IsLocalHom ψ ∧
        ∃ hψ : PrimeSpectrum.comap ψ s = r,
          (Formalization.Books.Algebra.Unit113.residueFieldMapAt ψ r s hψ).comp
              e₁.toRingHom = e₂.toRingHom.comp ρ := by
  sorry

structure StrictLocalHenselizationWitness
    (A : Type u) [CommRing A] [IsLocalRing A] where
  S : Type u
  [commRingS : CommRing S]
  [localS : IsLocalRing S]
  map : A →+* S
  property : IsStrictlyHenselian S

structure StrictHenselizationDifferentData
    (R K : Type u) [CommRing R] (p : PrimeSpectrum R) [Field K]
    [Algebra p.asIdeal.ResidueField K]
    [Algebra.IsAlgebraic p.asIdeal.ResidueField K]
    [IsSepClosed K] where
  localStrictHenselization :
    StrictLocalHenselizationWitness (Localization.AtPrime p.asIdeal)
  target : Type u
  [commRingTarget : CommRing target]
  map : R →+* target
  colimit : Formalization.Books.Algebra.Unit127.DirectedAlgebraColimit map
  stageEtale : letI : Preorder colimit.index := colimit.indexPreorder
    ∀ i, RingHom.Etale (colimit.diagram.obj i).hom.hom
  stagePrime : letI : Preorder colimit.index := colimit.indexPreorder
    ∀ i, PrimeSpectrum (colimit.diagram.obj i).right
  stageLiesOver : letI : Preorder colimit.index := colimit.indexPreorder
    ∀ i, PrimeSpectrum.comap (colimit.diagram.obj i).hom.hom (stagePrime i) = p
  stageResidue : letI : Preorder colimit.index := colimit.indexPreorder
    ∀ i, Nonempty (ResidueFieldEmbeddingOver (K := K)
      (colimit.diagram.obj i).hom.hom p (stagePrime i) (stageLiesOver i))
  targetEquiv :
    letI : CommRing localStrictHenselization.S :=
      localStrictHenselization.commRingS
    letI : IsLocalRing localStrictHenselization.S :=
      localStrictHenselization.localS
    target ≃+* localStrictHenselization.S
  targetEquiv_commutes :
    letI : CommRing localStrictHenselization.S :=
      localStrictHenselization.commRingS
    letI : IsLocalRing localStrictHenselization.S :=
      localStrictHenselization.localS
    targetEquiv.toRingHom.comp map =
      localStrictHenselization.map.comp
        (algebraMap R (Localization.AtPrime p.asIdeal))
  localizedStageEquiv : letI : Preorder colimit.index := colimit.indexPreorder
    ∀ i, Nonempty ((colimit.diagram.obj i).right ≃+*
      Localization.AtPrime (stagePrime i).asIdeal)

theorem strict_henselization_different
    (R K : Type u) [CommRing R] (p : PrimeSpectrum R) [Field K]
    [Algebra p.asIdeal.ResidueField K]
    [Algebra.IsAlgebraic p.asIdeal.ResidueField K]
    [IsSepClosed K] :
    Nonempty (StrictHenselizationDifferentData R K p) := by
  sorry

structure StrictHenselizationAtPrimeLocalWitness
    (A T : Type u) [CommRing A] [CommRing T] [IsLocalRing T]
    (q : PrimeSpectrum A) where
  map : Localization.AtPrime q.asIdeal →+* T
  henselian : IsHenselization map
  strict : IsStrictlyHenselian T

theorem strict_henselization_improve
    {R S Rsh Ssh K₁ K₂ : Type u} [CommRing R] [CommRing S]
    [CommRing Rsh] [IsLocalRing Rsh] [CommRing Ssh] [IsLocalRing Ssh]
    [Field K₁] [Field K₂]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p)
    [Algebra p.asIdeal.ResidueField K₁]
    [Algebra q.asIdeal.ResidueField K₂]
    [Algebra.IsAlgebraic p.asIdeal.ResidueField K₁]
    [Algebra.IsAlgebraic q.asIdeal.ResidueField K₂]
    [IsSepClosed K₁] [IsSepClosed K₂]
    (rsh : Localization.AtPrime p.asIdeal →+* Rsh)
    (ssh : Localization.AtPrime q.asIdeal →+* Ssh)
    (hrsh : IsHenselization rsh)
    (hssh : IsHenselization ssh)
    (hstrictRsh : IsStrictlyHenselian Rsh)
    (hstrictSsh : IsStrictlyHenselian Ssh)
    (β : p.asIdeal.ResidueField →+* q.asIdeal.ResidueField)
    (ρ : K₁ →+* K₂)
    (hρ : ρ.comp (algebraMap p.asIdeal.ResidueField K₁) =
      (algebraMap q.asIdeal.ResidueField K₂).comp β) :
    letI : Algebra R (Localization.AtPrime p.asIdeal) :=
      (algebraMap R (Localization.AtPrime p.asIdeal)).toAlgebra
    letI : Algebra R Rsh :=
      Algebra.compHom Rsh (rsh.comp
        (algebraMap R (Localization.AtPrime p.asIdeal)))
    letI : Algebra R S := f.toAlgebra
    ∃ r : PrimeSpectrum (Rsh ⊗[R] S),
      PrimeSpectrum.comap
          (Algebra.TensorProduct.includeLeft (R := R) (S := R)
            (A := Rsh) (B := S)).toRingHom r = maximalPrimeSpectrum Rsh ∧
        PrimeSpectrum.comap
            (Algebra.TensorProduct.includeRight (R := R) (A := Rsh) (B := S)).toRingHom r = q ∧
          (∀ r' : PrimeSpectrum (Rsh ⊗[R] S),
            PrimeSpectrum.comap
                (Algebra.TensorProduct.includeLeft (R := R) (S := R)
                  (A := Rsh) (B := S)).toRingHom r' =
                maximalPrimeSpectrum Rsh →
              PrimeSpectrum.comap
                  (Algebra.TensorProduct.includeRight (R := R)
                    (A := Rsh) (B := S)).toRingHom r' = q →
              r' = r) ∧
            Nonempty (StrictHenselizationAtPrimeLocalWitness
              (Rsh ⊗[R] S) Ssh r) := by
  sorry

theorem strict_henselization_from_henselization
    {R S Rh Rsh Sh K : Type u} [CommRing R] [IsLocalRing R]
    [CommRing S] [CommRing Rh] [IsLocalRing Rh]
    [CommRing Rsh] [IsLocalRing Rsh] [CommRing Sh] [IsLocalRing Sh]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField R) K]
    [IsSepClosed K]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p)
    (hres : Nonempty (p.asIdeal.ResidueField ≃+* q.asIdeal.ResidueField))
    (rh : Localization.AtPrime p.asIdeal →+* Rh)
    (hrh : IsHenselization rh)
    (rsh : Localization.AtPrime p.asIdeal →+* Rsh)
    (hrsh : IsHenselization rsh)
    (hstrictRsh : IsStrictlyHenselian Rsh)
    (sh : Localization.AtPrime q.asIdeal →+* Sh)
    (hsh : IsHenselization sh)
    (hstrictSh : IsStrictlyHenselian Sh)
    [Algebra Rh Sh] [Algebra Rh Rsh]
    (hRhSh : (algebraMap Rh Sh).comp rh =
      sh.comp (localizationAtPrimeMap f p q hq))
    (hRhRsh : (algebraMap Rh Rsh).comp rh = rsh) :
    Nonempty (Sh ≃ₐ[Rh] Sh ⊗[Rh] Rsh) := by
  sorry

/-! ## 145.12 Henselization and quasi-finite ring maps -/

/-- The data in the quasi-finite henselization lemma, including the unique
prime of the tensor product and the finite local comparison map. -/
structure QuasiFiniteHenselizationData
    {R S Rh Sh : Type u} [CommRing R] [CommRing S]
    [CommRing Rh] [IsLocalRing Rh] [CommRing Sh] [IsLocalRing Sh]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p)
    (rh : Localization.AtPrime p.asIdeal →+* Rh)
    (sh : Localization.AtPrime q.asIdeal →+* Sh)
    [Algebra R Rh]
    [Algebra R (Localization.AtPrime q.asIdeal)] where
  prime : PrimeSpectrum (Rh ⊗[R] Localization.AtPrime q.asIdeal)
  prime_over_source :
    PrimeSpectrum.comap
        (Algebra.TensorProduct.includeLeft (R := R) (S := R)
          (A := Rh) (B := Localization.AtPrime q.asIdeal)).toRingHom prime =
      maximalPrimeSpectrum Rh
  prime_over_target :
    PrimeSpectrum.comap
        (Algebra.TensorProduct.includeRight (R := R)
          (A := Rh) (B := Localization.AtPrime q.asIdeal)).toRingHom prime =
      maximalPrimeSpectrum (Localization.AtPrime q.asIdeal)
  unique_prime : ∀ r : PrimeSpectrum (Rh ⊗[R] Localization.AtPrime q.asIdeal),
    PrimeSpectrum.comap
          (Algebra.TensorProduct.includeLeft (R := R) (S := R)
            (A := Rh) (B := Localization.AtPrime q.asIdeal)).toRingHom r =
        maximalPrimeSpectrum Rh →
    PrimeSpectrum.comap
          (Algebra.TensorProduct.includeRight (R := R)
            (A := Rh) (B := Localization.AtPrime q.asIdeal)).toRingHom r =
        maximalPrimeSpectrum (Localization.AtPrime q.asIdeal) →
      r = prime
  henselization :
    HenselizationAtPrimeWitness
      (Rh ⊗[R] Localization.AtPrime q.asIdeal) Sh prime
  comparison : Rh →+* Sh
  comparison_commutes :
    comparison.comp rh = sh.comp (localizationAtPrimeMap f p q hq)
  henselization_commutes_left :
    henselization.map.comp
        ((algebraMap (Rh ⊗[R] Localization.AtPrime q.asIdeal)
          (Localization.AtPrime prime.asIdeal)).comp
          (Algebra.TensorProduct.includeLeft (R := R) (S := R)
            (A := Rh) (B := Localization.AtPrime q.asIdeal)).toRingHom) =
      comparison
  henselization_commutes_right :
    henselization.map.comp
        ((algebraMap (Rh ⊗[R] Localization.AtPrime q.asIdeal)
          (Localization.AtPrime prime.asIdeal)).comp
          (Algebra.TensorProduct.includeRight (R := R)
            (A := Rh) (B := Localization.AtPrime q.asIdeal)).toRingHom) =
      sh
  comparison_finite : RingHom.Finite comparison
  comparison_local : IsLocalHom comparison
  localization_equiv : ∃ e : Localization.AtPrime prime.asIdeal ≃+* Sh,
    e.toRingHom = henselization.map

theorem quasi_finite_henselization
    {R S Rh Sh : Type u} [CommRing R] [CommRing S]
    [CommRing Rh] [IsLocalRing Rh] [CommRing Sh] [IsLocalRing Sh]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p)
    (rh : Localization.AtPrime p.asIdeal →+* Rh)
    (sh : Localization.AtPrime q.asIdeal →+* Sh)
    (hrh : IsHenselization rh) (hsh : IsHenselization sh)
    (hquasi : RingHom.QuasiFiniteAt f q.asIdeal) :
    letI : Algebra R (Localization.AtPrime p.asIdeal) :=
      (algebraMap R (Localization.AtPrime p.asIdeal)).toAlgebra
    letI : Algebra R Rh :=
      Algebra.compHom Rh (rh.comp
        (algebraMap R (Localization.AtPrime p.asIdeal)))
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R (Localization.AtPrime q.asIdeal) :=
      (atPrimeLocalizationMap f q).toAlgebra
    Nonempty (QuasiFiniteHenselizationData f p q hq rh sh) := by
  sorry

/-- The quotient map induced by a henselization map and an ideal. -/
def quotientHenselizationMap
    {R Rh : Type u} [CommRing R] [CommRing Rh]
    (rh : R →+* Rh) (I : Ideal R) :
    R ⧸ I →+* Rh ⧸ Ideal.map rh I :=
  Ideal.Quotient.lift I
    ((Ideal.Quotient.mk (Ideal.map rh I)).comp rh)
    (by
      intro a ha
      change Ideal.Quotient.mk (Ideal.map rh I) (rh a) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem rh ha)

structure QuotientHenselizationData
    {R Rh : Type u} [CommRing R] [IsLocalRing R]
    [CommRing Rh] [IsLocalRing Rh]
    (rh : R →+* Rh) (I : Ideal R) where
  [local_source : IsLocalRing (R ⧸ I)]
  [local_target : IsLocalRing (Rh ⧸ Ideal.map rh I)]
  property : IsHenselization (quotientHenselizationMap rh I)

theorem quotient_henselization
    {R Rh : Type u} [CommRing R] [IsLocalRing R]
    [CommRing Rh] [IsLocalRing Rh]
    (rh : R →+* Rh) (hrh : IsHenselization rh)
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) :
    Nonempty (QuotientHenselizationData rh I) := by
  sorry

structure QuotientStrictHenselizationData
    {R Rsh K : Type u} [CommRing R] [IsLocalRing R]
    [CommRing Rsh] [IsLocalRing Rsh] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    (rsh : R →+* Rsh) (I : Ideal R) where
  [local_source : IsLocalRing (R ⧸ I)]
  [local_target : IsLocalRing (Rsh ⧸ Ideal.map rsh I)]
  quotient_residue_algebra :
    Algebra (IsLocalRing.ResidueField (R ⧸ I)) K
  property :
    letI : Algebra (IsLocalRing.ResidueField (R ⧸ I)) K :=
      quotient_residue_algebra
    IsStrictHenselization (K := K) (quotientHenselizationMap rsh I)

theorem quotient_strict_henselization
    {R Rsh K : Type u} [CommRing R] [IsLocalRing R]
    [CommRing Rsh] [IsLocalRing Rsh] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField R) K]
    [IsSepClosed K]
    (rsh : R →+* Rsh) (hrsh : IsStrictHenselization (K := K) rsh)
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) :
    Nonempty (QuotientStrictHenselizationData (K := K) rsh I) := by
  sorry

/-- The residue-field condition used in the local tensor lemma. -/
def MaximalResidueFieldPurelyInseparable
    {A B : Type u} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B]
    (f : A →+* B)
    (h : PrimeSpectrum.comap f (maximalPrimeSpectrum B) =
      maximalPrimeSpectrum A) : Prop :=
  letI : Algebra (maximalPrimeSpectrum A).asIdeal.ResidueField
      (maximalPrimeSpectrum B).asIdeal.ResidueField :=
    (Formalization.Books.Algebra.Unit113.residueFieldMapAt f
      (maximalPrimeSpectrum A) (maximalPrimeSpectrum B) h).toAlgebra
  IsPurelyInseparable (maximalPrimeSpectrum A).asIdeal.ResidueField
    (maximalPrimeSpectrum B).asIdeal.ResidueField

structure LocalTensorWithIntegralData
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] where
  [local_tensor : IsLocalRing (B ⊗[A] C)]
  left_local : IsLocalHom
    (Algebra.TensorProduct.includeLeft (R := A) (S := A)
      (A := B) (B := C)).toRingHom
  right_local : IsLocalHom
    (Algebra.TensorProduct.includeRight (R := A)
      (A := B) (B := C)).toRingHom

theorem local_tensor_with_integral
    {A B C : Type u} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C]
    (f : A →+* B) (g : A →+* C)
    (hf : IsLocalHom f) (hg : IsLocalHom g)
    (hintegral : g.IsIntegral)
    (hB : PrimeSpectrum.comap f (maximalPrimeSpectrum B) =
      maximalPrimeSpectrum A)
    (hC : PrimeSpectrum.comap g (maximalPrimeSpectrum C) =
      maximalPrimeSpectrum A)
    (hpure : MaximalResidueFieldPurelyInseparable g hC ∨
      MaximalResidueFieldPurelyInseparable f hB) :
    letI : Algebra A B := f.toAlgebra
    letI : Algebra A C := g.toAlgebra
    Nonempty (LocalTensorWithIntegralData (A := A) (B := B) (C := C)) := by
  sorry

/-- A ring map whose target is presented as a filtered colimit of
quasi-finite algebras over its source. -/
def IsFilteredColimitOfQuasiFinite
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) : Prop :=
  Nonempty (Formalization.Books.Algebra.Unit127.FilteredAlgebraColimitIn f
    {X | RingHom.QuasiFinite X.hom.hom})

/-- The localized version of `IsFilteredColimitOfQuasiFinite`. -/
def IsFilteredColimitOfQuasiFiniteAt
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (p : PrimeSpectrum A) (q : PrimeSpectrum B)
    (hq : PrimeSpectrum.comap f q = p) : Prop :=
  IsFilteredColimitOfQuasiFinite (localizationAtPrimeMap f p q hq)

/-- The four hypotheses in the strict henselization base-change lemma. -/
def QuasiFiniteBaseChangeCondition
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (p : PrimeSpectrum A) (q : PrimeSpectrum B)
    (hq : PrimeSpectrum.comap f q = p) : Prop :=
  RingHom.QuasiFiniteAt f q.asIdeal ∨
    IsFilteredColimitOfQuasiFinite f ∨
      IsFilteredColimitOfQuasiFiniteAt f p q hq ∨ f.IsIntegral

/-- The commutative diagram and tensor-product identification supplied by the
strict henselization base-change lemma. -/
structure StrictHenselizationBaseChangeData
    {A B C Ash Bsh Csh Dsh K : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [CommRing Ash] [IsLocalRing Ash]
    [CommRing Bsh] [IsLocalRing Bsh]
    [CommRing Csh] [IsLocalRing Csh]
    [CommRing Dsh] [IsLocalRing Dsh]
    [Field K] [Algebra A B] [Algebra A C]
    (f : A →+* B) (g : A →+* C)
    (pA : PrimeSpectrum A) (pB : PrimeSpectrum B)
    (pC : PrimeSpectrum C)
    (pD : PrimeSpectrum (B ⊗[A] C))
    (hpB : PrimeSpectrum.comap f pB = pA)
    (hpC : PrimeSpectrum.comap g pC = pA)
    (hpBD : PrimeSpectrum.comap
      (Algebra.TensorProduct.includeLeft (R := A) (S := A)
        (A := B) (B := C)).toRingHom pD = pB)
    (hpCD : PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight (R := A)
        (A := B) (B := C)).toRingHom pD = pC)
    (point : (B ⊗[A] C) →+* K)
    (hpoint : RingHom.ker point = pD.asIdeal)
    (ash : Localization.AtPrime pA.asIdeal →+* Ash)
    (bsh : Localization.AtPrime pB.asIdeal →+* Bsh)
    (csh : Localization.AtPrime pC.asIdeal →+* Csh)
    (dsh : Localization.AtPrime pD.asIdeal →+* Dsh)
    [Algebra Ash Bsh] [Algebra Ash Csh] where
  base_to_B : Ash →+* Bsh
  base_to_C : Ash →+* Csh
  base_to_B_commutes :
    base_to_B.comp ash = bsh.comp (localizationAtPrimeMap f pA pB hpB)
  base_to_C_commutes :
    base_to_C.comp ash = csh.comp (localizationAtPrimeMap g pA pC hpC)
  B_to_D : Bsh →+* Dsh
  C_to_D : Csh →+* Dsh
  B_to_D_commutes :
    B_to_D.comp bsh = dsh.comp (localizationAtPrimeMap
      (Algebra.TensorProduct.includeLeft (R := A) (S := A)
        (A := B) (B := C)).toRingHom pB pD hpBD)
  C_to_D_commutes :
    C_to_D.comp csh = dsh.comp (localizationAtPrimeMap
      (Algebra.TensorProduct.includeRight (R := A)
        (A := B) (B := C)).toRingHom pC pD hpCD)
  comparison : Bsh ⊗[Ash] Csh ≃+* Dsh
  comparison_left :
    comparison.toRingHom.comp
        (Algebra.TensorProduct.includeLeft (R := Ash) (S := Ash)
          (A := Bsh) (B := Csh)).toRingHom = B_to_D
  comparison_right :
    comparison.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := Ash)
          (A := Bsh) (B := Csh)).toRingHom = C_to_D

theorem base_change_strict_henselization_quasiFinite
    {A B C Ash Bsh Csh Dsh K_A K_B K_C K_D : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [CommRing Ash] [IsLocalRing Ash]
    [CommRing Bsh] [IsLocalRing Bsh]
    [CommRing Csh] [IsLocalRing Csh]
    [CommRing Dsh] [IsLocalRing Dsh]
    [Field K_A] [Field K_B] [Field K_C] [Field K_D]
    [Algebra A B] [Algebra A C] [Algebra Ash Bsh] [Algebra Ash Csh]
    (f : A →+* B) (g : A →+* C)
    (hf : f = algebraMap A B) (hg : g = algebraMap A C)
    (pA : PrimeSpectrum A) (pB : PrimeSpectrum B)
    (pC : PrimeSpectrum C)
    (pD : PrimeSpectrum (B ⊗[A] C))
    (hpB : PrimeSpectrum.comap f pB = pA)
    (hpC : PrimeSpectrum.comap g pC = pA)
    (hpBD : PrimeSpectrum.comap
      (Algebra.TensorProduct.includeLeft (R := A) (S := A)
        (A := B) (B := C)).toRingHom pD = pB)
    (hpCD : PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight (R := A)
        (A := B) (B := C)).toRingHom pD = pC)
    (point : (B ⊗[A] C) →+* K_D)
    (hpoint : RingHom.ker point = pD.asIdeal)
    [Algebra (IsLocalRing.ResidueField (Localization.AtPrime pA.asIdeal)) K_A]
    [Algebra (IsLocalRing.ResidueField (Localization.AtPrime pB.asIdeal)) K_B]
    [Algebra (IsLocalRing.ResidueField (Localization.AtPrime pC.asIdeal)) K_C]
    [Algebra (IsLocalRing.ResidueField (Localization.AtPrime pD.asIdeal)) K_D]
    [Algebra.IsAlgebraic
      (IsLocalRing.ResidueField (Localization.AtPrime pA.asIdeal)) K_A]
    [Algebra.IsAlgebraic
      (IsLocalRing.ResidueField (Localization.AtPrime pB.asIdeal)) K_B]
    [Algebra.IsAlgebraic
      (IsLocalRing.ResidueField (Localization.AtPrime pC.asIdeal)) K_C]
    [Algebra.IsAlgebraic
      (IsLocalRing.ResidueField (Localization.AtPrime pD.asIdeal)) K_D]
    [IsSepClosed K_A] [IsSepClosed K_B] [IsSepClosed K_C] [IsSepClosed K_D]
    (ash : Localization.AtPrime pA.asIdeal →+* Ash)
    (bsh : Localization.AtPrime pB.asIdeal →+* Bsh)
    (csh : Localization.AtPrime pC.asIdeal →+* Csh)
    (dsh : Localization.AtPrime pD.asIdeal →+* Dsh)
    (hash : IsStrictHenselization (K := K_A) ash)
    (hbsh : IsStrictHenselization (K := K_B) bsh)
    (hcsh : IsStrictHenselization (K := K_C) csh)
    (hdsh : IsStrictHenselization (K := K_D) dsh)
    (hcondition : QuasiFiniteBaseChangeCondition f pA pB hpB) :
    Nonempty (StrictHenselizationBaseChangeData f g pA pB pC pD hpB hpC
      hpBD hpCD point hpoint ash bsh csh dsh) := by
  sorry
