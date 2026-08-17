import Formalization.Books.Algebra.Unit14.BaseChange
import Formalization.Books.Algebra.Unit78.FiniteProjectiveModules
import Formalization.Books.Algebra.Unit112.HomomorphismsAndDimension
import Formalization.Books.Algebra.Unit135.LocalCompleteIntersections
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Commutative Algebra, Chapter 136: Syntomic morphisms

This file follows the source order of the section.  The local-complete-
intersection condition on a fibre reuses
`Formalization.Books.Algebra.Unit135.IsLocalCompleteIntersection`; ring maps,
base change, localization, conormal modules, and finite projectivity likewise
use the canonical Mathlib and earlier-chapter interfaces.
-/

namespace Formalization.Books.Algebra.Unit136

open Set
open Module
open scoped BigOperators TensorProduct

noncomputable section

universe u v

/-! ## Syntomic maps and their first permanence properties -/

/-- The affine fibre of `R → S` over `p : Spec R`. -/
abbrev Fiber (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) : Type _ :=
  p.asIdeal.Fiber S

/-- A syntomic ring map: flat, finitely presented, with lci fibres. -/
def IsSyntomic
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  RingHom.Flat f ∧ RingHom.FinitePresentation f ∧
    ∀ p : PrimeSpectrum R,
      letI : Algebra p.asIdeal.ResidueField (Fiber R S p) :=
        Algebra.TensorProduct.leftAlgebra
      Formalization.Books.Algebra.Unit135.IsLocalCompleteIntersection
        p.asIdeal.ResidueField (Fiber R S p)

theorem syntomic_over_field_iff_local_complete_intersection
    {k S : Type u} [Field k] [CommRing S] [Algebra k S] :
    IsSyntomic (algebraMap k S) ↔
      Formalization.Books.Algebra.Unit135.IsLocalCompleteIntersection k S := by
  sorry

theorem syntomic_descends
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (hff : RingHom.FaithfullyFlat g) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    IsSyntomic f ↔
      IsSyntomic (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g) := by
  sorry

theorem syntomic_base_change
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (hf : IsSyntomic f) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    IsSyntomic (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g) := by
  sorry

theorem syntomic_local_on_source
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (m : ℕ) (gs : Fin m → S)
    (hgen : Ideal.span (Set.range gs) = (⊤ : Ideal S)) :
    letI : Algebra R S := f.toAlgebra
    (∀ i, IsSyntomic (algebraMap R (Localization.Away (gs i)))) →
      IsSyntomic f := by
  sorry

/-! ## Relative global complete intersections -/

/-- A finite polynomial presentation with named relations. -/
def IsPolynomialQuotientPresentation
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {n c : ℕ} (P : Formalization.Books.Algebra.Unit134.Presentation
      R S (Fin n)) (fs : Fin c → P.Ring) : Prop :=
  P.ker = Ideal.ofList (List.ofFn fs)

/-- A relative global complete intersection presentation over a ring. -/
def IsRelativeGlobalCompleteIntersection
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  ∃ (n c : ℕ) (P : Formalization.Books.Algebra.Unit134.Presentation
      R S (Fin n)) (fs : Fin c → P.Ring),
    IsPolynomialQuotientPresentation P fs ∧
      ∀ p : PrimeSpectrum R,
        Nonempty (PrimeSpectrum (Fiber R S p)) →
          ringKrullDim (Fiber R S p) =
            (((n - c : ℕ) : ℕ∞) : WithBot ℕ∞)

/-- A map out of `R / I` induced by a map out of `R`. -/
def QuotientMapOfIdeal
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (I : Ideal R) (fbar : (R ⧸ I) →+* T) : Prop :=
  ∃ q : S →+* T, q.comp f = fbar.comp (Ideal.Quotient.mk I)

/-- Every nonempty fibre of a ring map has the displayed dimension. -/
def HasFiberDimension
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (d : WithBot ℕ∞) : Prop :=
  letI : Algebra R S := f.toAlgebra
  ∀ p : PrimeSpectrum R,
    Nonempty (PrimeSpectrum (Fiber R S p)) →
      ringKrullDim (Fiber R S p) = d

/-- The image of an element of `S` in the canonical fibre over `p`. -/
def IsUnitInFiber
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (p : PrimeSpectrum R) (g : S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  IsUnit ((Algebra.TensorProduct.includeRight :
    S →ₐ[R] Fiber R S p) g)

/-- The dimension of the local fibre at a prime of `S` over a prime of `R`. -/
def LocalFiberDimensionAt
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hlying : PrimeSpectrum.comap f q = p) : WithBot ℕ∞ :=
  letI : Algebra R S := f.toAlgebra
  ringKrullDim
    (Formalization.Books.Algebra.Unit112.localRingOfFibre f p q hlying)

theorem relative_global_complete_intersection_is_finite_presentation
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (h : IsRelativeGlobalCompleteIntersection f) :
    RingHom.FinitePresentation f := by
  sorry

theorem relative_global_complete_intersection_base_change
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (h : IsRelativeGlobalCompleteIntersection f) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    IsRelativeGlobalCompleteIntersection
      (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g) := by
  sorry

theorem relative_global_complete_intersection_localization
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (h : IsRelativeGlobalCompleteIntersection f) :
    letI : Algebra R S := f.toAlgebra
    ∀ (g₀ : S) (n : ℕ)
      (P : Formalization.Books.Algebra.Unit134.Presentation R S (Fin n))
      (c : ℕ) (fs : Fin c → P.Ring),
      IsPolynomialQuotientPresentation P fs →
      ∀ (h₀ : P.Ring), algebraMap P.Ring S h₀ = g₀ →
        IsRelativeGlobalCompleteIntersection
          (algebraMap R (Localization.Away g₀)) := by
  sorry

theorem relative_global_complete_intersection_localization_of_base
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (r : R) (g : Localization.Away r →+* S)
    (hfactor : g.comp (algebraMap R (Localization.Away r)) = f)
    (h : IsRelativeGlobalCompleteIntersection f) :
    IsRelativeGlobalCompleteIntersection g := by
  sorry

/-! ## Huber's presentation lemma -/

/-- The conormal module of a finite polynomial presentation is free. -/
def HasFreeConormalPresentation
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  ∃ (n : ℕ)
    (P : Formalization.Books.Algebra.Unit134.Presentation R S (Fin n)),
    Module.Free S P.toExtension.Cotangent

/-- The classes of named relations form the indicated conormal basis. -/
def HasConormalBasisPresentation
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {n c : ℕ}
    (P : Formalization.Books.Algebra.Unit134.Presentation R S (Fin n))
    (fs : Fin c → P.Ring) : Prop :=
  ∃ hmem : ∀ i, fs i ∈ P.toExtension.ker,
    ∃ b : Basis (Fin c) S P.toExtension.Cotangent,
      ∀ i, b i = Algebra.Extension.Cotangent.mk ⟨fs i, hmem i⟩

theorem huber_presentation
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hfp : RingHom.FinitePresentation f)
    (hconormal : HasFreeConormalPresentation f) :
    letI : Algebra R S := f.toAlgebra
    ∃ (m c : ℕ)
      (P : Formalization.Books.Algebra.Unit134.Presentation R S (Fin m))
      (fs : Fin c → P.Ring),
      IsPolynomialQuotientPresentation P fs ∧
        HasConormalBasisPresentation P fs := by
  sorry

/-! ## Polynomial examples -/

/-- The monic polynomial with coefficient list `a₁, ..., aₙ`. -/
def monicPolynomial
    {A : Type u} [Semiring A] (n : ℕ) (a : Fin n → A) : Polynomial A :=
  Polynomial.X ^ n +
    ∑ i : Fin n, Polynomial.C (a i) * Polynomial.X ^ (n - i.1 - 1)

abbrev FactorPolynomialBase (n m : ℕ) := MvPolynomial (Fin (n + m)) ℤ

abbrev FactorPolynomialTarget (n m : ℕ) :=
  MvPolynomial (Sum (Fin n) (Fin m)) ℤ

noncomputable def factorTargetPolynomial (n m : ℕ) :
    Polynomial (FactorPolynomialTarget n m) :=
  monicPolynomial n (fun i => MvPolynomial.X (Sum.inl i)) *
    monicPolynomial m (fun j => MvPolynomial.X (Sum.inr j))

noncomputable def factorPolynomialMap (n m : ℕ) :
    FactorPolynomialBase n m →ₐ[ℤ] FactorPolynomialTarget n m :=
  MvPolynomial.aeval (fun k =>
    (factorTargetPolynomial n m).coeff (n + m - k.1 - 1))

theorem factorPolynomialMap_spec (n m : ℕ) (k : Fin (n + m)) :
    factorPolynomialMap n m (MvPolynomial.X k) =
      (factorTargetPolynomial n m).coeff (n + m - k.1 - 1) := by
  sorry

theorem factorPolynomialMap_factorization (n m : ℕ) :
    Polynomial.map (factorPolynomialMap n m).toRingHom
        (monicPolynomial (n + m) (fun k => MvPolynomial.X k)) =
      factorTargetPolynomial n m := by
  sorry

theorem factorPolynomialMap_has_expected_presentation
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    letI : Algebra (FactorPolynomialBase n m) (FactorPolynomialTarget n m) :=
      (factorPolynomialMap n m).toAlgebra
    ∃ (P : Formalization.Books.Algebra.Unit134.Presentation
        (FactorPolynomialBase n m) (FactorPolynomialTarget n m) (Fin (n + m)))
      (fs : Fin (n + m) → P.Ring),
      IsPolynomialQuotientPresentation P fs := by
  sorry

theorem factorPolynomialMap_fibre_dimension_zero
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (p : PrimeSpectrum (FactorPolynomialBase n m)) :
    letI : Algebra (FactorPolynomialBase n m) (FactorPolynomialTarget n m) :=
      (factorPolynomialMap n m).toAlgebra
    Nonempty (PrimeSpectrum
        (p.asIdeal.Fiber (FactorPolynomialTarget n m))) →
      ringKrullDim
          (p.asIdeal.Fiber (FactorPolynomialTarget n m)) = 0 := by
  sorry

theorem factorPolynomialMap_is_finite
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    RingHom.Finite (factorPolynomialMap n m).toRingHom := by
  sorry

theorem factorPolynomialMap_is_integral
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    (factorPolynomialMap n m).toRingHom.IsIntegral := by
  sorry

theorem factorPolynomialMap_is_relative_global_complete_intersection
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    IsRelativeGlobalCompleteIntersection (factorPolynomialMap n m).toRingHom := by
  sorry

/-! ## The universal polynomial and its roots -/

abbrev RootsPolynomialBase (n : ℕ) := MvPolynomial (Fin n) ℤ

abbrev RootsPolynomialTarget (n : ℕ) :=
  MvPolynomial (Sum (Fin n) (Fin n)) ℤ

def elementarySymmetric
    {A : Type u} [CommRing A] (n k : ℕ) (a : Fin n → A) : A :=
  (Finset.univ.powerset.filter (fun t => t.card = k)).sum
    (fun t => t.prod a)

noncomputable def rootsPolynomialMap (n : ℕ) :
    RootsPolynomialBase n →ₐ[ℤ] RootsPolynomialTarget n :=
  MvPolynomial.aeval (fun k =>
    elementarySymmetric n k.1 (fun i => MvPolynomial.X (Sum.inr i)))

noncomputable def rootsTargetPolynomial (n : ℕ) :
    Polynomial (RootsPolynomialTarget n) :=
  ∏ i : Fin n, (Polynomial.X +
    Polynomial.C (MvPolynomial.X (Sum.inr i)))

def RootMonomialIndex (n : ℕ) :=
  ∀ i : Fin n, Fin (n - i.1)

def rootMonomial (n : ℕ) (e : RootMonomialIndex n) :
    RootsPolynomialTarget n :=
  ∏ i : Fin n, MvPolynomial.X (Sum.inr i) ^ (e i).1

theorem rootsPolynomialMap_spec (n : ℕ) (k : Fin n) :
    rootsPolynomialMap n (MvPolynomial.X k) =
      elementarySymmetric n k.1 (fun i => MvPolynomial.X (Sum.inr i)) := by
  sorry

theorem rootsPolynomial_factorization (n : ℕ) :
    Polynomial.map (rootsPolynomialMap n).toRingHom
        (monicPolynomial n (fun k => MvPolynomial.X k)) =
      rootsTargetPolynomial n := by
  sorry

theorem rootsPolynomialMap_finite_free
    {n : ℕ} (hn : 1 ≤ n) :
    letI : Algebra (RootsPolynomialBase n) (RootsPolynomialTarget n) :=
      (rootsPolynomialMap n).toAlgebra
    Module.Finite (RootsPolynomialBase n) (RootsPolynomialTarget n) ∧
      Module.Free (RootsPolynomialBase n) (RootsPolynomialTarget n) ∧
      (∃ b : Basis (RootMonomialIndex n) (RootsPolynomialBase n)
          (RootsPolynomialTarget n),
        (∀ e, b e = rootMonomial n e) ∧
          Nonempty (RootMonomialIndex n)) := by
  sorry

theorem rootsPolynomialMap_is_finite_faithfully_flat
    {n : ℕ} (hn : 1 ≤ n) :
    RingHom.Finite (rootsPolynomialMap n).toRingHom ∧
      RingHom.FaithfullyFlat (rootsPolynomialMap n).toRingHom := by
  sorry

theorem rootsPolynomialMap_fibre_dimension_zero
    {n : ℕ} (hn : 1 ≤ n) (p : PrimeSpectrum (RootsPolynomialBase n)) :
    letI : Algebra (RootsPolynomialBase n) (RootsPolynomialTarget n) :=
      (rootsPolynomialMap n).toAlgebra
    Nonempty (PrimeSpectrum
        (p.asIdeal.Fiber (RootsPolynomialTarget n))) →
      ringKrullDim
          (p.asIdeal.Fiber (RootsPolynomialTarget n)) = 0 := by
  sorry

theorem rootsPolynomialMap_is_relative_global_complete_intersection
    {n : ℕ} (hn : 1 ≤ n) :
    IsRelativeGlobalCompleteIntersection (rootsPolynomialMap n).toRingHom := by
  sorry

/-! ## Base change, localization, approximation, and conormal modules -/

theorem localize_relative_complete_intersection
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    : letI : Algebra R S := f.toAlgebra
      ∀ {n c : ℕ}
      (P : Formalization.Books.Algebra.Unit134.Presentation R S (Fin n))
      (fs : Fin c → P.Ring),
      IsPolynomialQuotientPresentation P fs →
      ∀ (I : Ideal R),
      (∃ fbar : (R ⧸ I) →+* (S ⧸ Ideal.map f I),
        QuotientMapOfIdeal f I fbar ∧
          HasFiberDimension fbar (((n - c : ℕ) : ℕ∞) : WithBot ℕ∞)) →
      ∃ (g : S) (h : P.Ring),
        algebraMap P.Ring S h = g ∧
          Ideal.Quotient.mk (Ideal.map f I) g = 1 ∧
          IsRelativeGlobalCompleteIntersection
            (algebraMap R (Localization.Away g)) := by
  sorry

theorem localize_relative_complete_intersection_at_fibre
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    : letI : Algebra R S := f.toAlgebra
      ∀ {n c : ℕ}
      (P : Formalization.Books.Algebra.Unit134.Presentation R S (Fin n))
      (fs : Fin c → P.Ring),
      IsPolynomialQuotientPresentation P fs →
      (p : PrimeSpectrum R) →
      (hdim : Nonempty (PrimeSpectrum (Fiber R S p)) →
      ringKrullDim (Fiber R S p) =
        (((n - c : ℕ) : ℕ∞) : WithBot ℕ∞)) →
    ∃ (g : S) (h : P.Ring),
      algebraMap P.Ring S h = g ∧
        IsUnitInFiber f p g ∧
        IsRelativeGlobalCompleteIntersection
          (algebraMap R (Localization.Away g)) := by
  sorry

theorem localize_relative_complete_intersection_at_prime
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    : letI : Algebra R S := f.toAlgebra
      ∀ {n c : ℕ}
      (P : Formalization.Books.Algebra.Unit134.Presentation R S (Fin n))
      (fs : Fin c → P.Ring),
      IsPolynomialQuotientPresentation P fs →
      (p : PrimeSpectrum R) → (q' : PrimeSpectrum P.Ring) →
      (q : PrimeSpectrum S) →
      (hlying : PrimeSpectrum.comap f q = p) →
      (hq : PrimeSpectrum.comap (algebraMap P.Ring S) q = q') →
      (hdim : LocalFiberDimensionAt f p q hlying =
      (((n - c : ℕ) : ℕ∞) : WithBot ℕ∞)) →
    ∃ (g : S) (h : P.Ring),
      algebraMap P.Ring S h = g ∧
        g ∉ q.asIdeal ∧
        IsRelativeGlobalCompleteIntersection
          (algebraMap R (Localization.Away g)) := by
  sorry

def NoetherianApproximationData
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {n c : ℕ}
    (P : Formalization.Books.Algebra.Unit134.Presentation R S (Fin n))
    (fs : Fin c → P.Ring) : Prop :=
  ∃ (R₀ : Subalgebra ℤ R) (fs₀ : Fin c → MvPolynomial (Fin n) R₀),
    RingHom.FiniteType (algebraMap ℤ R₀) ∧
      (∀ i, MvPolynomial.map R₀.val (fs₀ i) = fs i) ∧
      ∃ (S₀ : Type u) (hS₀ : CommRing S₀) (hA₀ : Algebra R₀ S₀),
        letI : CommRing S₀ := hS₀
        letI : Algebra R₀ S₀ := hA₀
        ∃ (P₀ : Formalization.Books.Algebra.Unit134.Presentation
            R₀ S₀ (Fin n)),
          IsPolynomialQuotientPresentation P₀ fs₀ ∧
            IsRelativeGlobalCompleteIntersection (algebraMap R₀ S₀)

theorem relative_global_complete_intersection_noetherian_approximation
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hrel : IsRelativeGlobalCompleteIntersection f) :
    letI : Algebra R S := f.toAlgebra
    ∀ {n c : ℕ}
      (P : Formalization.Books.Algebra.Unit134.Presentation R S (Fin n))
      (fs : Fin c → P.Ring),
      IsPolynomialQuotientPresentation P fs →
      NoetherianApproximationData P fs := by
  sorry

def PrefixRelations {A : Type u} [AddMonoid A]
    {c : ℕ} (fs : Fin c → A) (i : ℕ) (hi : i ≤ c) : List A :=
  List.ofFn (fun j : Fin i => fs ⟨j.1, lt_of_lt_of_le j.isLt hi⟩)

def LocalFiberMap
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hlying : PrimeSpectrum.comap f q = p) :
    R →+* Formalization.Books.Algebra.Unit112.localRingOfFibre f p q hlying :=
  (Ideal.Quotient.mk
      (Formalization.Books.Algebra.Unit112.fibreIdealInLocalization f p q)).comp
    ((algebraMap S (Localization.AtPrime q.asIdeal)).comp f)

def IsCompleteIntersectionOverResidueField
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hlying : PrimeSpectrum.comap f q = p) : Prop :=
  let L := Formalization.Books.Algebra.Unit112.localRingOfFibre f p q hlying
  letI : Algebra R L := (LocalFiberMap f p q hlying).toAlgebra
  ∃ hL : IsLocalRing L, ∃ hKL : Algebra p.asIdeal.ResidueField L,
    letI : IsLocalRing L := hL
    letI : Algebra p.asIdeal.ResidueField L := hKL
    IsScalarTower R p.asIdeal.ResidueField L ∧
      Formalization.Books.Algebra.Unit135.IsCompleteIntersection
        p.asIdeal.ResidueField L

def FlatQuotientOfRingHom
    {R L : Type u} [CommRing R] [CommRing L]
    (I : Ideal L) (b : R →+* L) : Prop :=
  ∃ (Q : Type u) (hQ : CommRing Q),
    letI : CommRing Q := hQ
    ∃ (φ : R →+* Q) (e : Q ≃+* (L ⧸ I)),
      RingHom.Flat φ ∧
        e.toRingHom.comp φ = (Ideal.Quotient.mk I).comp b

theorem relative_global_complete_intersection_conormal
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hrel : IsRelativeGlobalCompleteIntersection f) :
    letI : Algebra R S := f.toAlgebra
    ∀ {n c : ℕ}
      (P : Formalization.Books.Algebra.Unit134.Presentation R S (Fin n))
      (fs : Fin c → P.Ring),
      IsPolynomialQuotientPresentation P fs →
      (q : PrimeSpectrum S) → (q' : PrimeSpectrum P.Ring) →
      PrimeSpectrum.comap (algebraMap P.Ring S) q = q' →
    RingTheory.Sequence.IsRegular (Localization.AtPrime q'.asIdeal)
        (List.ofFn (fun i =>
          algebraMap P.Ring (Localization.AtPrime q'.asIdeal) (fs i))) ∧
      (∀ (i : ℕ) (hi : i ≤ c),
        FlatQuotientOfRingHom
          (Ideal.map (algebraMap P.Ring (Localization.AtPrime q'.asIdeal))
            (Ideal.ofList (PrefixRelations fs i hi)))
          (algebraMap R (Localization.AtPrime q'.asIdeal))) ∧
      HasConormalBasisPresentation P fs := by
  sorry

theorem relative_global_complete_intersection_is_syntomic
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hrel : IsRelativeGlobalCompleteIntersection f) :
    IsSyntomic f := by
  sorry

/-! ## Finite free root extensions -/

def PolynomialSplitsIntoRoots
    {A A' : Type u} [CommRing A] [CommRing A']
    (f : A →+* A') {n : ℕ} (P : Polynomial A) (β : Fin n → A') : Prop :=
  Polynomial.map f P =
    ∏ i : Fin n, (Polynomial.X - Polynomial.C (β i) : Polynomial A')

theorem adjoin_roots
    {A : Type u} [CommRing A] (n : ℕ) (b : Fin n → A) :
    ∃ (A' : Type u) (hA' : CommRing A'),
      letI : CommRing A' := hA'
      ∃ (f : A →+* A'),
        letI : Algebra A A' := f.toAlgebra
        ∃ (β : Fin n → A'),
        IsSyntomic f ∧
            Module.Finite A A' ∧ Module.Free A A' ∧
            RingHom.FaithfullyFlat f ∧
              PolynomialSplitsIntoRoots f (monicPolynomial n b) β := by
  sorry

/-! ## The local criterion for syntomicity -/

def IsFlatAtPrime
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (_hlying : PrimeSpectrum.comap f q = p) : Prop :=
  letI : Algebra R S := f.toAlgebra
  let hcomap : p.asIdeal = q.asIdeal.comap f := by
    simpa [PrimeSpectrum.comap_asIdeal] using
      (congrArg PrimeSpectrum.asIdeal _hlying).symm
  RingHom.Flat (Localization.localRingHom p.asIdeal q.asIdeal f hcomap)

theorem syntomic_local_criterion
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hlying : PrimeSpectrum.comap f q = p) :
    letI : Algebra R S := f.toAlgebra
    List.TFAE
      [ (∃ g : S, g ∉ q.asIdeal ∧
          IsSyntomic (algebraMap R (Localization.Away g))),
        (∃ g : S, g ∉ q.asIdeal ∧
          IsRelativeGlobalCompleteIntersection
            (algebraMap R (Localization.Away g))),
        (∃ g : S, g ∉ q.asIdeal ∧
          RingHom.FinitePresentation (algebraMap R (Localization.Away g)) ∧
          IsFlatAtPrime f p q hlying ∧
          IsCompleteIntersectionOverResidueField f p q hlying) ] := by
  sorry

/-! ## Conormal modules and composition -/

theorem syntomic_presentation_ideal_mod_squares
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    :
    letI : Algebra R S := f.toAlgebra
    ∀ {n : ℕ} (P : Formalization.Books.Algebra.Unit134.Presentation
      R S (Fin n))
      (hP : RingHom.FinitePresentation (algebraMap P.Ring S)) (g : S),
    IsSyntomic (algebraMap R (Localization.Away g)) →
    Formalization.Books.Algebra.Unit78.FiniteProjective
      (Localization.Away g)
      (LocalizedModule.Away g P.toExtension.Cotangent) := by
  sorry

theorem composition_relative_global_complete_intersection
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (hf : IsRelativeGlobalCompleteIntersection f)
    (hg : IsRelativeGlobalCompleteIntersection g) :
    IsRelativeGlobalCompleteIntersection (g.comp f) := by
  sorry

theorem composition_syntomic
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (hf : IsSyntomic f) (hg : IsSyntomic g) :
    IsSyntomic (g.comp f) := by
  sorry

/-! ## Lifting a syntomic map through a quotient -/

def SyntomicLiftPiece
    {R I : Type u} [CommRing R] [CommRing I]
    (J : Ideal R) (fbar : (R ⧸ J) →+* I) (g : I) : Prop :=
  letI : Algebra (R ⧸ J) I := fbar.toAlgebra
  ∃ (T : Type u) (hT : CommRing T) (f : R →+* T),
    letI : CommRing T := hT
    IsRelativeGlobalCompleteIntersection f ∧
      ∃ e : (T ⧸ Ideal.map f J) ≃+* Localization.Away g,
        ∃ h : (R ⧸ J) →+* (T ⧸ Ideal.map f J),
          h.comp (Ideal.Quotient.mk J) =
              (Ideal.Quotient.mk (Ideal.map f J)).comp f ∧
            e.toRingHom.comp h =
              algebraMap (R ⧸ J) (Localization.Away g)

theorem lift_syntomic
    {R S : Type u} [CommRing R] [CommRing S] (J : Ideal R)
    (fbar : (R ⧸ J) →+* S)
    (hfbar : IsSyntomic fbar) :
    ∃ (m : ℕ) (gs : Fin m → S),
      Ideal.span (Set.range gs) = (⊤ : Ideal S) ∧
      (∀ i, SyntomicLiftPiece J fbar (gs i)) := by
  sorry

end

end Formalization.Books.Algebra.Unit136
