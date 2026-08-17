import Formalization.Books.Algebra.Unit102.WhatMakesAComplexExact
import Formalization.Books.Algebra.Unit112.HomomorphismsAndDimension
import Formalization.Books.Algebra.Unit128.MoreFlatnessCriteria
import Formalization.Books.Topology.Unit10.KrullDimension
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.RingHom.Flat

/-!
# Commutative Algebra, Chapter 129: Openness of the flat locus

This file records the source-facing interfaces for the chapter.  Vanishing
loci, local fibre rings, finite free complexes, and flatness at a prime use the
canonical constructions from earlier chapters.  The small predicates below
only package the source's fibre hypotheses and its localized fibre complex.
-/

namespace Formalization.Books.Algebra.Unit129

open Set
open Formalization.Books.Algebra.Unit99
open Formalization.Books.Algebra.Unit102
open Formalization.Books.Algebra.Unit104
open Formalization.Books.Algebra.Unit112
open Formalization.Books.Topology.Unit10
open scoped TensorProduct

universe u

noncomputable section

/-! ## Fibre hypotheses and local fibre complexes -/

/- The existing Cohen--Macaulay ring predicate carries a Noetherian-ring
  typeclass argument.  This package makes that implicit finiteness part of a
  fibre hypothesis without replacing the canonical predicate itself. -/
def IsCohenMacaulayEquidimensionalOfDimension
    (A : Type u) [CommRing A] (d : ℕ) : Prop :=
  ∃ hA : IsNoetherianRing A,
    letI : IsNoetherianRing A := hA
    Formalization.Books.Algebra.Unit104.IsCohenMacaulayRing A ∧
      Equidimensional (X := PrimeSpectrum A) ∧
        ringKrullDim A = (((d : ℕ∞) : WithBot ℕ∞))

/- The source's assertion that all fibres have a common Cohen--Macaulay,
  equidimensional dimension, with the algebra structure induced by `f`. -/
def AllFibresCohenMacaulayEquidimensional
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (d : ℕ) : Prop :=
  letI : Algebra R S := f.toAlgebra
  ∀ p : PrimeSpectrum R,
    IsCohenMacaulayEquidimensionalOfDimension
      (S ⊗[R] p.asIdeal.ResidueField) d

/- The quotient presentation `S_q / p S_q` is the canonical local-ring model
  for `F_{\bullet,q} ⊗_R κ(p)` used in the source. -/
noncomputable def localFibreRingMap
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (q : PrimeSpectrum S) :
    S →+* localRingOfFibre f (PrimeSpectrum.comap f q) q rfl :=
  (Ideal.Quotient.mk
      (fibreIdealInLocalization f (PrimeSpectrum.comap f q) q)).comp
    (algebraMap S (Localization.AtPrime q.asIdeal))

/- The elements of `S` occurring in a regular-sequence assertion on the local
  fibre. -/
noncomputable def localFibreSequence
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (fs : List S) (q : PrimeSpectrum S) :
    List (localRingOfFibre f (PrimeSpectrum.comap f q) q rfl) :=
  (fs.map (algebraMap S (Localization.AtPrime q.asIdeal))).map
    (Ideal.Quotient.mk
      (fibreIdealInLocalization f (PrimeSpectrum.comap f q) q))

/- A differential of the finite free complex after passing to the local fibre.
  `mapCoordinateLinearMap` is the canonical scalar-extension operation on the
  coordinate matrices. -/
noncomputable def localFibreDifferential
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) {e : ℕ}
    (C : Formalization.Books.Algebra.Unit102.FiniteFreeComplex S e)
    (q : PrimeSpectrum S) (i : ℕ) :
    (Fin (C.termRank (i + 1)) →
        localRingOfFibre f (PrimeSpectrum.comap f q) q rfl) →ₗ[
      localRingOfFibre f (PrimeSpectrum.comap f q) q rfl]
      (Fin (C.termRank i) →
        localRingOfFibre f (PrimeSpectrum.comap f q) q rfl) :=
  Formalization.Books.Algebra.Unit102.mapCoordinateLinearMap
    (localFibreRingMap f q) (C.differential i)

/- The preceding differential with the source reindexed from `i - 1 + 1` to
  `i`, as required by exactness at a positive degree. -/
noncomputable def localFibrePreviousDifferential
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) {e : ℕ}
    (C : Formalization.Books.Algebra.Unit102.FiniteFreeComplex S e)
    (q : PrimeSpectrum S) (i : ℕ) (hi : 0 < i) :
    (Fin (C.termRank i) →
        localRingOfFibre f (PrimeSpectrum.comap f q) q rfl) →ₗ[
      localRingOfFibre f (PrimeSpectrum.comap f q) q rfl]
      (Fin (C.termRank (i - 1)) →
        localRingOfFibre f (PrimeSpectrum.comap f q) q rfl) := by
  have h : i - 1 + 1 = i := Nat.sub_add_cancel hi
  exact h ▸ localFibreDifferential f C q (i - 1)

/- Exactness of the displayed finite complex on the fibre at `q`.  The
  endpoint and interior clauses are the same exactness convention as the
  earlier finite-free-complex interface. -/
def FiniteFreeComplexIsExactOnLocalFibre
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) {e : ℕ}
    (C : Formalization.Books.Algebra.Unit102.FiniteFreeComplex S e)
    (q : PrimeSpectrum S) : Prop :=
  ∀ i : ℕ,
    if hi0 : i = 0 then
      True
    else if _hiL : i = e then
      e ≠ 0 ∧ Function.Injective
        (localFibrePreviousDifferential f C q i (Nat.pos_of_ne_zero hi0))
    else if _hi_lt : i < e then
      Function.Exact (localFibreDifferential f C q i)
        (localFibrePreviousDifferential f C q i (Nat.pos_of_ne_zero hi0))
    else
      True

/- The source's pointwise flatness condition, expressed using Chapter 99's
  canonical localization and restriction-of-scalars construction. -/
noncomputable def flatAtPrimeOverBaseRingHom
    {R S M : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M]
    (f : R →+* S) (q : PrimeSpectrum S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  letI : Module R M := Module.compHom M f
  letI : IsScalarTower R S M := SMul.comp.isScalarTower f
  Formalization.Books.Algebra.Unit99.flatAtPrimeOverBase
    (R := R) (S := S) (M := M) q

/-! ## Dimension and regular sequences -/

/- The first lemma: a dimension bound on a vanishing locus in a finite-type
  Cohen--Macaulay equidimensional algebra is sharp and gives regular
  sequences in all local rings on that locus. -/
theorem cm_dim_finite_type
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [IsNoetherianRing S]
    (fs : List S) (d : ℕ)
    (hS : Formalization.Books.Algebra.Unit104.IsCohenMacaulayRing S)
    (hequidim : Equidimensional (X := PrimeSpectrum S))
    (hdim : ringKrullDim S = (((d : ℕ∞) : WithBot ℕ∞)))
    (hVdim :
      topologicalKrullDim
          (PrimeSpectrum.zeroLocus (Ideal.ofList fs : Set S)) ≤
        ((((d - fs.length : ℕ) : ℕ∞) : WithBot ℕ∞))) :
    topologicalKrullDim
          (PrimeSpectrum.zeroLocus (Ideal.ofList fs : Set S)) =
        ((((d - fs.length : ℕ) : ℕ∞) : WithBot ℕ∞)) ∧
      ∀ q : PrimeSpectrum S,
        q ∈ PrimeSpectrum.zeroLocus (Ideal.ofList fs : Set S) →
          RingTheory.Sequence.IsRegular
            (Localization.AtPrime q.asIdeal)
            (fs.map (algebraMap S (Localization.AtPrime q.asIdeal))) := by
  sorry

/- The second lemma: regularity on the local fibres is an open condition inside
  the vanishing locus. -/
theorem open_regular_sequence
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : RingHom.FiniteType f) (d : ℕ)
    (hfibres : AllFibresCohenMacaulayEquidimensional f d)
    (fs : List S) :
    IsOpen
      {q : PrimeSpectrum S |
        q ∈ PrimeSpectrum.zeroLocus (Ideal.ofList fs : Set S) ∧
          RingTheory.Sequence.IsRegular
            (localRingOfFibre f (PrimeSpectrum.comap f q) q rfl)
            (localFibreSequence f fs q)} := by
  sorry

/-! ## Exact complexes on fibres -/

/- The third lemma: for a finite free complex over a finite-type flat map with
  Cohen--Macaulay equidimensional fibres, exactness on fibres is open. -/
theorem exact_on_fibres_open
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : RingHom.FiniteType f)
    (hflat : RingHom.Flat f) [IsNoetherianRing R] (d : ℕ)
    (hfibres : AllFibresCohenMacaulayEquidimensional f d)
    {e : ℕ}
    (C : Formalization.Books.Algebra.Unit102.FiniteFreeComplex S e) :
    IsOpen
      {q : PrimeSpectrum S |
        FiniteFreeComplexIsExactOnLocalFibre f C q} := by
  sorry

/-! ## Openness of the flat locus -/

/- The final theorem: finite presentation of both the algebra and the module
  makes the locus where the localized module is flat over the base open. -/
theorem openness_flatness
    {R S M : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinitePresentation : RingHom.FinitePresentation f)
    [AddCommGroup M] [Module S M] [Module.FinitePresentation S M] :
    IsOpen
      {q : PrimeSpectrum S |
        flatAtPrimeOverBaseRingHom (R := R) (S := S) (M := M) f q} := by
  sorry

end

end Formalization.Books.Algebra.Unit129
