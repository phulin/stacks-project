import Formalization.Books.Topology.Unit11.CodimensionAndCatenary

import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Exercises, Chapter 18: Catenary rings

This file contains the canonical relative-height, prime-chain, and
topological-space interfaces used by the chapter's definition and exercises.
The topological catenary predicate itself is reused from Topology, Chapter 11.
-/

noncomputable section

universe u

namespace Formalization.Books.Exercises.Unit18

/-! ## The chapter's relative height -/

/-
For ideals `q ≤ p`, the source's `ht(p / q)` is the height of the image of
`p` in the quotient ring `A ⧸ q`.  The quotient map and `Ideal.height` are
Mathlib's canonical constructions.
-/
noncomputable def relativeHeight
    {A : Type u} [CommRing A] (p q : Ideal A) (_hqp : q ≤ p) : ℕ∞ :=
  (p.map (Ideal.Quotient.mk q)).height

/- The prime `p / q` in `A / q`, used for the displayed localization formula. -/
def quotientPrime
    {A : Type u} [CommRing A]
    (p q : PrimeSpectrum A) (hqp : q ≤ p) : PrimeSpectrum (A ⧸ q.asIdeal) :=
  ⟨p.asIdeal.map (Ideal.Quotient.mk q.asIdeal),
    Ideal.isPrime_map_quotientMk_of_isPrime
      ((PrimeSpectrum.asIdeal_le_asIdeal q p).mpr hqp)⟩

/-! ## Ring-theoretic catenarity -/

/-
The three prime ideals in the source definition are represented by points of
the canonical prime spectrum.  This avoids duplicating a prime-ideal subtype
and keeps the inclusions in the same order used by `PrimeSpectrum`.
-/
def IsCatenaryRing (A : Type u) [CommRing A] : Prop :=
  ∀ ⦃p₁ p₂ p₃ : PrimeSpectrum A⦄
    (h₁₂ : p₁ ≤ p₂) (h₂₃ : p₂ ≤ p₃),
    relativeHeight p₃.asIdeal p₁.asIdeal
        ((PrimeSpectrum.asIdeal_le_asIdeal p₁ p₃).mpr (h₁₂.trans h₂₃)) =
      relativeHeight p₃.asIdeal p₂.asIdeal
          ((PrimeSpectrum.asIdeal_le_asIdeal p₂ p₃).mpr h₂₃) +
        relativeHeight p₂.asIdeal p₁.asIdeal
          ((PrimeSpectrum.asIdeal_le_asIdeal p₁ p₂).mpr h₁₂)

/-! ## The earlier algebraic chain formulation -/

/- A finite strict chain in `Spec A` with prescribed endpoints. -/
def IsPrimeChainBetween
    {A : Type u} [CommRing A]
    (p q : PrimeSpectrum A) (hpq : p ≤ q)
    (c : LTSeries (Set.Iic q)) : Prop :=
  c.head = (⟨p, hpq⟩ : Set.Iic q) ∧
    c.last = (⟨q, Set.mem_Iic.mpr le_rfl⟩ : Set.Iic q)

/-
This is the chain-bounded/equal-maximal-chain definition cited from the
earlier Algebra chapter.  `LTSeries` supplies the finite strict chains and
Topology Chapter 11 supplies the canonical maximal-chain predicate.
-/
def IsAlgebraCatenaryRing (A : Type u) [CommRing A] : Prop :=
  ∀ (p q : PrimeSpectrum A) (hpq : p ≤ q),
    ∃ n : ℕ,
      (∀ c : LTSeries (Set.Iic q),
        IsPrimeChainBetween p q hpq c → c.length ≤ n) ∧
      ∀ c d : LTSeries (Set.Iic q),
        IsPrimeChainBetween p q hpq c →
        IsPrimeChainBetween p q hpq d →
        Formalization.Books.Topology.Unit11.IsMaximalChainBetween
          p q hpq c →
        Formalization.Books.Topology.Unit11.IsMaximalChainBetween
          p q hpq d →
          c.length = d.length

/-!
The source's topological definition is already the canonical
`Formalization.Books.Topology.Unit11.IsCatenary`: it quantifies over
`IrreducibleCloseds`, finite relative codimension, and maximal strict chains.
The bundled predicate below only records the additional adjective “finite,
sober” used in the final exercise.
-/
def IsFiniteSoberCatenarySpace
    (X : Type u) [TopologicalSpace X] : Prop :=
  Finite X ∧ QuasiSober X ∧ T0Space X ∧
    Formalization.Books.Topology.Unit11.IsCatenary X

end Formalization.Books.Exercises.Unit18
