import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# More on Morphisms, Chapter 42: Étale localization of integral morphisms

This file formalizes the integral-morphism splitting lemma in the chapter's
section `Étale localization of integral morphisms`.
-/

namespace MoreMorphisms.Unit42

open scoped TensorProduct

noncomputable section

universe u v

/-! ## Residue-field extensions at primes -/

/-- The canonical residue-field map associated to a prime lying over another
prime. -/
noncomputable def residueFieldMap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (h : PrimeSpectrum.comap f q = p) :
    p.asIdeal.ResidueField →+* q.asIdeal.ResidueField :=
  Ideal.ResidueField.map p.asIdeal q.asIdeal f (by
    simpa [PrimeSpectrum.comap_asIdeal] using
      congrArg PrimeSpectrum.asIdeal h.symm)

/-- Finiteness of the maximal separable subextension of a residue-field
extension.  The `separableClosure` is Mathlib's canonical maximal separable
subextension. -/
noncomputable def FiniteSeparableResidueExtension
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (h : PrimeSpectrum.comap f q = p) : Prop :=
  letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    (residueFieldMap f p q h).toAlgebra
  Module.Finite p.asIdeal.ResidueField
    (separableClosure p.asIdeal.ResidueField q.asIdeal.ResidueField)

/-- Pure inseparability of a residue-field extension, expressed using the
canonical residue-field map at primes. -/
noncomputable def PurelyInseparableResidueExtension
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (h : PrimeSpectrum.comap f q = p) : Prop :=
  letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    (residueFieldMap f p q h).toAlgebra
  IsPurelyInseparable p.asIdeal.ResidueField q.asIdeal.ResidueField

/-! ## The étale splitting datum -/

/-- Data expressing the product decomposition supplied by étale localization
of an integral ring map at a prime. -/
structure EtaleIntegralSplittingData
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) where
  R' : Type u
  [commRingR' : CommRing R']
  [algebraRR' : Algebra R R']
  [etale : Algebra.Etale R R']
  p' : PrimeSpectrum R'
  p'_over : PrimeSpectrum.comap (algebraMap R R') p' = p
  m : ℕ
  A : Fin m → Type max u v
  [commRingA : ∀ j, CommRing (A j)]
  [algebraR'A : ∀ j, Algebra R' (A j)]
  decomposition :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R' (S ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
    (S ⊗[R] R') ≃ₐ[R'] (∀ j, A j)
  integral : ∀ j, RingHom.IsIntegral (algebraMap R' (A j))
  r : ∀ j, PrimeSpectrum (A j)
  r_over : ∀ j,
    PrimeSpectrum.comap (algebraMap R' (A j)) (r j) = p'
  unique_prime_over : ∀ j (q : PrimeSpectrum (A j)),
    PrimeSpectrum.comap (algebraMap R' (A j)) q = p' ↔ q = r j
  residue_purely_inseparable : ∀ j,
    PurelyInseparableResidueExtension
      (algebraMap R' (A j)) p' (r j) (r_over j)

/-! ## Étale localization of integral morphisms -/

/-- An integral ring map with finitely many primes over `p`, whose residue
fields have finite maximal separable subextensions, becomes a finite product
of integral algebras with unique purely inseparable primes after an étale base
change. -/
theorem lemma_etale_makes_integral_split
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R)
    (h_integral : RingHom.IsIntegral f)
    (n : ℕ) (q : Fin n → PrimeSpectrum S)
    (q_over : ∀ i, PrimeSpectrum.comap f (q i) = p)
    (q_injective : Function.Injective q)
    (q_complete : ∀ q' : PrimeSpectrum S,
      PrimeSpectrum.comap f q' = p → ∃ i, q' = q i)
    (q_separable : ∀ i,
      FiniteSeparableResidueExtension f p (q i) (q_over i)) :
    Nonempty (EtaleIntegralSplittingData f p) := by
  sorry

end

end MoreMorphisms.Unit42
