import Formalization.Books.Algebra.Unit106.RegularLocalRings
import Formalization.Books.Algebra.Unit160.CohenStructureTheorem
import Formalization.Books.MoreAlgebra.Unit37
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# More Algebra, Chapter 39: Some results on power series rings

This file records the definitions and theorem interfaces in the first section of
Chapter 39.  Multivariable formal power series are Mathlib's
`MvPowerSeries (Fin n) R`; regular systems of parameters reuse the minimal
maximal-ideal generating lists from the regular-local-ring chapter.
-/

namespace Formalization.Books.MoreAlgebra.Unit39

open Formalization.Books.Algebra.Unit106
open Formalization.Books.Algebra.Unit160
open Formalization.Books.MoreAlgebra.Unit37
open IsLocalRing

universe u

noncomputable section

/-! ## Common interfaces -/

/-- The multivariable formal power series ring in `n` variables. -/
abbrev PowerSeriesRing (R : Type u) (n : ℕ) [CommRing R] :=
  MvPowerSeries (Fin n) R

/-- A complete Noetherian local ring, with all of its structure made explicit so
it can occur as a witness in the Cohen-style diagram of this chapter. -/
structure CompleteNoetherianLocalRing where
  carrier : Type u
  commRing : CommRing carrier
  localRing : @IsLocalRing carrier commRing.toSemiring
  noetherianRing : @IsNoetherianRing carrier commRing.toSemiring
  complete : @IsCompleteLocalRing carrier commRing localRing

/-- Being a power series ring over a field.  The explicit `CommRing` argument
allows this predicate to be used for the carriers of
`CompleteNoetherianLocalRing` without manufacturing a parallel bundled ring. -/
def IsPowerSeriesOverField (R : Type u) (hR : CommRing R) : Prop :=
  ∃ (K : Type u) (hK : Field K) (n : ℕ),
    letI : CommRing R := hR
    letI : Field K := hK
    Nonempty (R ≃+* MvPowerSeries (Fin n) K)

/-- Being a power series ring over a Cohen ring. -/
def IsPowerSeriesOverCohenRing (R : Type u) (hR : CommRing R) : Prop :=
  ∃ (Λ : Type u) (hΛ : CommRing Λ)
      (hΛlocal : @IsLocalRing Λ hΛ.toSemiring)
      (_hΛcohen : @IsCohenRing Λ hΛ hΛlocal) (n : ℕ),
    letI : CommRing R := hR
    letI : CommRing Λ := hΛ
    letI : IsLocalRing Λ := hΛlocal
    Nonempty (R ≃+* MvPowerSeries (Fin n) Λ)

/-! ## Power series over coefficient rings -/

/-- The three formal-smoothness assertions for power series over a field or a
Cohen ring.  `ZMod p` is the canonical prime field used for the residue
characteristic `p` case. -/
theorem powerSeries_formallySmooth
    {K L Λ : Type u} [Field K] [CharZero K] [Field L]
    [CommRing Λ] [IsLocalRing Λ]
    (p : ℕ) (hp : Nat.Prime p) [CharP L p]
    (hΛ : IsCohenRing Λ) (n : ℕ) :
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    letI : Algebra (ZMod p) L := ZMod.algebra L p
    FormallySmoothForIdeal
        (algebraMap ℚ (PowerSeriesRing K n))
        (IsLocalRing.maximalIdeal (PowerSeriesRing K n)) ∧
      FormallySmoothForIdeal
        (algebraMap (ZMod p) (PowerSeriesRing L n))
        (IsLocalRing.maximalIdeal (PowerSeriesRing L n)) ∧
      FormallySmoothForIdeal
        (algebraMap ℤ (PowerSeriesRing Λ n))
        (IsLocalRing.maximalIdeal (PowerSeriesRing Λ n)) := by
  sorry

/-! ## Changing regular systems of parameters -/

/-- A regular system of parameters in the field-coefficient case gives the
corresponding power-series coordinate change. -/
theorem powerSeries_equiv_of_regular_parameters
    {K : Type u} [Field K] (n : ℕ)
    (y : Fin n → PowerSeriesRing K n)
    (hy : IsMinimalIdealGeneratingList
      (IsLocalRing.maximalIdeal (PowerSeriesRing K n)) (List.ofFn y)) :
    ∃ e : PowerSeriesRing K n ≃ₐ[K] PowerSeriesRing K n,
      ∀ i : Fin n, e (MvPowerSeries.X i) = y i := by
  sorry

/-- A part of a regular system of parameters cuts out a smaller power-series
ring after quotienting.  The length equation records that the displayed list
has exactly `n` parameters and therefore also yields `r ≤ n`. -/
theorem powerSeries_quotient_equiv_of_parameters
    {K : Type u} [Field K] (n r : ℕ)
    (z : Fin r → PowerSeriesRing K n)
    (hz : ∃ ys : List (PowerSeriesRing K n),
      IsMinimalIdealGeneratingList
          (IsLocalRing.maximalIdeal (PowerSeriesRing K n))
          (List.ofFn z ++ ys) ∧
    (List.ofFn z ++ ys).length = n) :
    r ≤ n ∧
      Nonempty (PowerSeriesRing K (n - r) ≃ₐ[K]
        (PowerSeriesRing K n ⧸ Ideal.ofList (List.ofFn z))) := by
  sorry

/-- The Cohen-ring analogue of the coordinate-change statement.  The
coefficient `p` is required to be the Cohen prime/uniformizer. -/
theorem cohenPowerSeries_equiv_of_regular_parameters
    {Λ : Type u} [CommRing Λ] [IsLocalRing Λ]
    (hΛ : IsCohenRing Λ) (p n : ℕ)
    (hp : Nat.Prime p ∧ CharP (IsLocalRing.ResidueField Λ) p ∧
      Ideal.span ({(p : Λ)} : Set Λ) = IsLocalRing.maximalIdeal Λ)
    (y : Fin n → PowerSeriesRing Λ n)
    (hy : IsMinimalIdealGeneratingList
      (IsLocalRing.maximalIdeal (PowerSeriesRing Λ n))
      ((p : PowerSeriesRing Λ n) :: List.ofFn y)) :
    ∃ e : PowerSeriesRing Λ n ≃ₐ[Λ] PowerSeriesRing Λ n,
      ∀ i : Fin n, e (MvPowerSeries.X i) = y i := by
  sorry

/-- Quotienting by part of a regular system of parameters in a
Cohen-coefficient power series ring leaves a Cohen-coefficient power series
ring in the remaining variables. -/
theorem cohenPowerSeries_quotient_equiv_of_parameters
    {Λ : Type u} [CommRing Λ] [IsLocalRing Λ]
    (hΛ : IsCohenRing Λ) (p n r : ℕ)
    (hp : Nat.Prime p ∧ CharP (IsLocalRing.ResidueField Λ) p ∧
      Ideal.span ({(p : Λ)} : Set Λ) = IsLocalRing.maximalIdeal Λ)
    (z : Fin r → PowerSeriesRing Λ n)
    (hz : ∃ ys : List (PowerSeriesRing Λ n),
      IsMinimalIdealGeneratingList
          (IsLocalRing.maximalIdeal (PowerSeriesRing Λ n))
          ((p : PowerSeriesRing Λ n) :: (List.ofFn z ++ ys)) ∧
        ((p : PowerSeriesRing Λ n) :: (List.ofFn z ++ ys)).length = n + 1) :
    r ≤ n ∧
      Nonempty (PowerSeriesRing Λ (n - r) ≃ₐ[Λ]
        (PowerSeriesRing Λ n ⧸ Ideal.ofList (List.ofFn z))) := by
  sorry

/-! ## Cohen-style diagrams -/

/-- A local homomorphism of complete Noetherian local rings admits the
power-series diagram from the source.  The characteristic split is expressed
using the characteristic of the residue field of `A`; the final conjuncts
also record flatness and regularity of the fibre. -/
theorem exists_powerSeries_dominating_diagram
    {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) [IsLocalHom f]
    (hA : IsCompleteLocalRing A) (hB : IsCompleteLocalRing B) :
    ∃ R S : CompleteNoetherianLocalRing,
      letI : CommRing R.carrier := R.commRing
      letI : CommRing S.carrier := S.commRing
      letI : IsLocalRing R.carrier := R.localRing
      letI : IsLocalRing S.carrier := S.localRing
      letI : IsNoetherianRing R.carrier := R.noetherianRing
      letI : IsNoetherianRing S.carrier := S.noetherianRing
      ∃ (r : R.carrier →+* A) (s : S.carrier →+* B)
        (g : R.carrier →+* S.carrier),
        Function.Surjective r ∧ Function.Surjective s ∧
        f.comp r = s.comp g ∧
        ((ringChar (IsLocalRing.ResidueField A) = 0 ∧
            IsPowerSeriesOverField R.carrier R.commRing ∧
            IsPowerSeriesOverField S.carrier S.commRing) ∨
          (∃ p : ℕ,
            0 < p ∧ CharP (IsLocalRing.ResidueField A) p ∧
            IsPowerSeriesOverCohenRing R.carrier R.commRing ∧
            IsPowerSeriesOverCohenRing S.carrier S.commRing)) ∧
        (∃ xs : List R.carrier, ∃ ys : List S.carrier,
          IsMinimalIdealGeneratingList (IsLocalRing.maximalIdeal R.carrier) xs ∧
          IsMinimalIdealGeneratingList (IsLocalRing.maximalIdeal S.carrier) ys ∧
          xs.length ≤ ys.length ∧ ys.take xs.length = xs.map g) ∧
        RingHom.Flat g ∧
        IsRegularLocalRing (S.carrier ⧸
          Ideal.map g (IsLocalRing.maximalIdeal R.carrier)) := by
  sorry

/-! ## Fibre products of surjections -/

/-- The fibre product of two surjections of complete Noetherian local rings is
again complete Noetherian local.  The pullback is Mathlib's canonical
`RingHom.pullback`, so its projections and commutative square remain available
to downstream chapters. -/
theorem pullback_completeNoetherianLocal
    {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    [IsNoetherianRing R] [IsNoetherianRing S] [IsNoetherianRing S']
    (f : S →+* R) (g : S' →+* R)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hR : IsCompleteLocalRing R) (hS : IsCompleteLocalRing S)
    (hS' : IsCompleteLocalRing S') :
    ∃ hP : IsLocalRing (f.pullback g),
      @IsNoetherianRing (f.pullback g) inferInstance ∧
        @IsCompleteLocalRing (f.pullback g) inferInstance hP := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit39
