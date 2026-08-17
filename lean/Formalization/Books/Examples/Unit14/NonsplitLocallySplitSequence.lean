import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Localization
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Examples, Chapter 14: Nonsplit locally split sequence

This file formalizes the sequence
`0 → M → ⨁ p, ℤ_(p) → ℚ → 0`, where `p` ranges over the prime
integers and `M` is the kernel of the map induced by the inclusions into
`ℚ`.  The sequence, its localization on a principal open, and the general
Zariski-local splitting interface are recorded as theorem statements.
-/

noncomputable section

open scoped DirectSum

namespace Formalization.Books.Examples.Unit14

universe u

/-! ## The prime-indexed sequence -/

/-- The type of positive prime integers indexing the direct sum. -/
abbrev PrimeIndex := Nat.Primes

/- The prime ideal `(p)` of the integers. -/
def primeIdeal (p : PrimeIndex) : Ideal ℤ :=
  Ideal.span ({(p.1 : ℤ)} : Set ℤ)

instance primeIdeal_isPrime (p : PrimeIndex) : (primeIdeal p).IsPrime := by
  simpa [primeIdeal] using
    (Ideal.isPrime_span_singleton_of_prime (Nat.prime_iff_prime_int.mp p.2))

/- The localization `ℤ_(p)` of the integers at the prime ideal `(p)`. -/
abbrev primeLocalizedInteger (p : PrimeIndex) : Type :=
  Localization.AtPrime (primeIdeal p)

/-- The canonical inclusion `ℤ_(p) → ℚ`. -/
noncomputable def primeLocalizedIntegerToRat (p : PrimeIndex) :
    primeLocalizedInteger p →+* ℚ :=
  IsLocalization.lift (M := (primeIdeal p).primeCompl)
    (S := primeLocalizedInteger p) (g := algebraMap ℤ ℚ) (by
      intro s
      have hs : (s : ℤ) ≠ 0 := by
        intro hs
        exact s.2 (hs ▸ (primeIdeal p).zero_mem)
      exact isUnit_iff_ne_zero.mpr (by
        simpa using (Int.cast_ne_zero.mpr hs : ((s : ℤ) : ℚ) ≠ 0)))

/-- The preceding inclusion, viewed as a `ℤ`-linear map. -/
def primeLocalizedIntegerToRatLinearMap (p : PrimeIndex) :
    primeLocalizedInteger p →ₗ[ℤ] ℚ :=
  { toFun := primeLocalizedIntegerToRat p
    map_add' := (primeLocalizedIntegerToRat p).map_add
    map_smul' := by
      intro n x
      simp [Algebra.smul_def, primeLocalizedIntegerToRat] }

/-- The middle term `⨁ₚ ℤ_(p)` in the source sequence. -/
abbrev primeLocalizedIntegerDirectSum : Type :=
  ⨁ p : PrimeIndex, primeLocalizedInteger p

/-- The map from the middle term to `ℚ`, induced componentwise by inclusion. -/
def primeLocalizedIntegerSumToRat :
    primeLocalizedIntegerDirectSum →ₗ[ℤ] ℚ :=
  DirectSum.toModule ℤ PrimeIndex ℚ
    (fun p => primeLocalizedIntegerToRatLinearMap p)

/-- The kernel `M` of the map on the right. -/
abbrev primeLocalizedIntegerKernel : Type :=
  LinearMap.ker primeLocalizedIntegerSumToRat

/-- The inclusion of `M` into the direct sum. -/
def primeLocalizedIntegerKernelInclusion :
    primeLocalizedIntegerKernel →ₗ[ℤ] primeLocalizedIntegerDirectSum :=
  (LinearMap.ker primeLocalizedIntegerSumToRat).subtype

/-- The displayed sequence, as a short complex of `ℤ`-modules. -/
noncomputable def primeLocalizedIntegerShortComplex :
    CategoryTheory.ShortComplex (ModuleCat.{0} ℤ) :=
  primeLocalizedIntegerSumToRat.shortComplexKer

/-- The source's short-exactness assertion for the displayed sequence. -/
theorem primeLocalizedIntegerShortComplex_shortExact :
    (primeLocalizedIntegerShortComplex).ShortExact := by
  apply LinearMap.shortExact_shortComplexKer
  sorry

/-! ## Nonsplitting and localization -/

/-- There are no nonzero `ℤ`-linear maps `ℚ → ℤ_(p)`. -/
theorem primeLocalizedInteger_no_nonzero_hom (p : PrimeIndex)
    (φ : ℚ →ₗ[ℤ] primeLocalizedInteger p) :
    φ = 0 := by
  sorry

/-- The displayed short-exact sequence is nonsplit. -/
theorem primeLocalizedIntegerShortComplex_not_split :
    ¬ Nonempty primeLocalizedIntegerShortComplex.Splitting := by
  sorry

/- The localization of the displayed sequence on the principal open `D(p)`,
   obtained by inverting `p`. -/
def primeLocalizedIntegerShortComplexAt (p : PrimeIndex) :
    CategoryTheory.ShortComplex
      (ModuleCat.{0} (Localization (Submonoid.powers (p.1 : ℤ)))) :=
  primeLocalizedIntegerShortComplex.map
    (ModuleCat.localizedModuleFunctor
      (Submonoid.powers (p.1 : ℤ)))

/-- Localization preserves the short-exactness of the displayed sequence. -/
theorem primeLocalizedIntegerShortComplexAt_shortExact (p : PrimeIndex) :
  (primeLocalizedIntegerShortComplexAt p).ShortExact := by
  exact primeLocalizedIntegerShortComplex_shortExact.map_of_exact
    (ModuleCat.localizedModuleFunctor (Submonoid.powers (p.1 : ℤ)))

/-- After inverting every prime `p`, the localized sequence is split. -/
theorem primeLocalizedIntegerShortComplexAt_split (p : PrimeIndex) :
    Nonempty (primeLocalizedIntegerShortComplexAt p).Splitting := by
  sorry

/-! ## The general Zariski-local formulation -/

/-- A short complex becomes split on a principal-open Zariski cover. -/
def IsZariskiLocallySplit {R : Type u} [CommRing R]
    (S : CategoryTheory.ShortComplex (ModuleCat.{u} R)) : Prop :=
  ∃ U : Set R, Ideal.span U = ⊤ ∧
    ∀ f ∈ U,
      Nonempty
        (S.map (ModuleCat.localizedModuleFunctor
          (Submonoid.powers f))).Splitting

/-- A nonsplit short-exact sequence which becomes split on a Zariski cover. -/
structure NonsplitZariskiLocallySplitSequence where
  R : Type
  [commRingR : CommRing R]
  S : CategoryTheory.ShortComplex (ModuleCat R)
  shortExact : S.ShortExact
  nonsplit : ¬ Nonempty S.Splitting
  locallySplit : IsZariskiLocallySplit S

/-- There exists a nonsplit short-exact sequence that is split Zariski locally. -/
theorem exists_nonsplit_zariski_locally_split_sequence :
    Nonempty NonsplitZariskiLocallySplitSequence := by
  sorry

end Formalization.Books.Examples.Unit14
