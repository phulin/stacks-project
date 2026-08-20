import Formalization.Books.Algebra.Unit59.NoetherianLocalRings
import Formalization.Books.Algebra.Unit62.SupportAndDimension
import Formalization.Books.MoreAlgebra.Unit30.KoszulRegularSequences
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Intersection Theory, Chapter 15: Algebraic multiplicities

This file records the definitions and theorem interfaces in the chapter's
section on algebraic multiplicities.  Hilbert functions, numerical
polynomials, module length, support dimension, and coefficient Koszul
complexes are the canonical interfaces from earlier chapters.
-/

namespace Formalization.Books.Intersection.Unit15

open Formalization.Books.Algebra.Unit59
open Formalization.Books.Algebra.Unit62
open Formalization.Books.Algebra.Unit58
open Formalization.Books.MoreAlgebra.Unit29
open Formalization.Books.MoreAlgebra.Unit30
open scoped BigOperators

universe u v

noncomputable section

/-! ## Hilbert functions and multiplicities -/

/-- The submodule `I^n M`, expressed using the canonical ideal action. -/
abbrev idealPowerSubmodule
    (A : Type u) (M : Type v) [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) (n : ℕ) : Submodule A M :=
  I ^ n • (⊤ : Submodule A M)

/-- The quotient `M/I^nM` occurring in the chapter's Hilbert function. -/
abbrev idealPowerQuotient
    (A : Type u) (M : Type v) [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) (n : ℕ) : Type v :=
  M ⧸ idealPowerSubmodule A M I n

/-- The numerical function `χ_{I,M}(n) = length(M/I^nM)`. -/
def hilbertCumulativeFunction
    (A : Type u) (M : Type v) [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) (n : ℕ) : ℕ :=
  (Module.length A (idealPowerQuotient A M I n)).toNat

/-- The successive-power piece `I^nM/I^(n+1)M`. -/
abbrev idealPowerPiece
    (A : Type u) (M : Type v) [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) (n : ℕ) : Type v :=
  let N : Submodule A M := I ^ n • (⊤ : Submodule A M)
  N ⧸ Submodule.comap N.subtype (I ^ (n + 1) • (⊤ : Submodule A M))

/-- The numerical function `length(I^nM/I^(n+1)M)`. -/
def hilbertPieceFunction
    (A : Type u) (M : Type v) [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) (n : ℕ) : ℕ :=
  (Module.length A (idealPowerPiece A M I n)).toNat

theorem hilbertCumulativeFunction_eq_sum
    (A : Type u) (M : Type v) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (hI : IsIdealOfDefinition A I) (n : ℕ) :
    hilbertCumulativeFunction A M I n =
      ∑ p ∈ Finset.range n, hilbertPieceFunction A M I p := by
  sorry

def hilbertCumulativeFunctionInteger
    (A : Type u) (M : Type v) [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) : ℤ → ℤ :=
  natFunctionToInteger (hilbertCumulativeFunction A M I)

theorem hilbertCumulativeFunction_isNumericalPolynomial
    (A : Type u) (M : Type v) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (hI : IsIdealOfDefinition A I) :
    IsNumericalPolynomial (hilbertCumulativeFunctionInteger A M I) := by
  sorry

theorem hilbertCumulativeFunction_degree_eq_supportDim
    (A : Type u) (M : Type v) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (hI : IsIdealOfDefinition A I) :
    WithBot.map (fun n : ℕ => (n : ℕ∞))
        (numericalPolynomialDegree (hilbertCumulativeFunctionInteger A M I)) =
      Module.supportDim A M := by
  sorry

/-- The rational polynomial agreeing eventually with `χ_{I,M}`. -/
noncomputable def hilbertPolynomialForIdeal
    (A : Type u) (M : Type v) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) : Polynomial ℚ :=
  eventuallyRationalPolynomial (hilbertCumulativeFunctionInteger A M I)

theorem hilbertPolynomialForIdeal_spec
    (A : Type u) (M : Type v) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (hilbertPolynomialForIdeal A M I).eval (n : ℚ) =
        (hilbertCumulativeFunction A M I n : ℚ) := by
  sorry

/-- `e_I(M,d)`, with the convention that it vanishes above the Hilbert degree. -/
noncomputable def multiplicity
    (A : Type u) (M : Type v) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (d : ℕ) : ℚ :=
  if numericalPolynomialDegree (hilbertCumulativeFunctionInteger A M I) =
      (d : WithBot ℕ) then
    (Nat.factorial d : ℚ) * (hilbertPolynomialForIdeal A M I).coeff d
  else 0

/-- The multiplicity at the Hilbert degree, with zero multiplicity for the zero module. -/
noncomputable def moduleMultiplicity
    (A : Type u) (M : Type v) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) : ℚ :=
  by
    classical
    exact if h : ∃ d : ℕ,
        numericalPolynomialDegree (hilbertCumulativeFunctionInteger A M I) =
          (d : WithBot ℕ) then
      multiplicity A M I (Classical.choose h)
    else 0

theorem multiplicity_eq_zero_of_supportDim_lt
    (A : Type u) (M : Type v) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (hI : IsIdealOfDefinition A I) (d : ℕ)
    (hd : Module.supportDim A M < ((d : ℕ∞) : WithBot ℕ∞)) :
    multiplicity A M I d = 0 := by
  sorry

theorem multiplicity_eq_factorial_coeff_of_supportDim_eq
    (A : Type u) (M : Type v) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (hI : IsIdealOfDefinition A I) (d : ℕ)
    (hd : Module.supportDim A M = ((d : ℕ∞) : WithBot ℕ∞)) :
    multiplicity A M I d =
      (Nat.factorial d : ℚ) * (hilbertPolynomialForIdeal A M I).coeff d := by
  sorry

theorem hilbertPolynomialForIdeal_has_lower_order_decomposition
    (A : Type u) (M : Type v) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (hI : IsIdealOfDefinition A I) (d : ℕ)
    (hd : Module.supportDim A M ≤ ((d : ℕ∞) : WithBot ℕ∞)) :
    ∃ Q : Polynomial ℚ,
      Q.degree < (d : WithBot ℕ) ∧
        hilbertPolynomialForIdeal A M I =
          Polynomial.monomial d
              (multiplicity A M I d / (Nat.factorial d : ℚ)) + Q := by
  sorry

theorem multiplicity_short_exact
    (A : Type u) {M' M M'' : Type v} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [AddCommGroup M'] [Module A M'] [Module.Finite A M']
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup M''] [Module A M''] [Module.Finite A M'']
    (I : Ideal A) (hI : IsIdealOfDefinition A I) (d : ℕ)
    (f : M' →ₗ[A] M) (g : M →ₗ[A] M'')
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : Function.Exact f g)
    (hd : Module.supportDim A M ≤ ((d : ℕ∞) : WithBot ℕ∞)) :
    multiplicity A M I d = multiplicity A M' I d + multiplicity A M'' I d := by
  sorry

/-- The contribution of a prime to the top-dimensional multiplicity sum. -/
noncomputable def primeMultiplicityContribution
    (A : Type u) (M : Type v) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (d : ℕ) (p : PrimeSpectrum A) : ℚ :=
  ((Module.length (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal M)).toNat : ℚ) *
    multiplicity A (A ⧸ p.asIdeal) I d

/-- The source's finite sum over primes, written as a tsum with zero terms off
the top-dimensional support. -/
noncomputable def primeMultiplicitySum
    (A : Type u) (M : Type v) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (d : ℕ) (s : Finset (PrimeSpectrum A)) : ℚ :=
  by
    classical
    exact ∑ p ∈ s,
      if p ∈ Module.support A M ∧
          ringKrullDim (A ⧸ p.asIdeal) = ((d : ℕ∞) : WithBot ℕ∞) then
        primeMultiplicityContribution A M I d p
      else 0

theorem multiplicity_as_prime_sum
    (A : Type u) (M : Type v) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (hI : IsIdealOfDefinition A I) (d : ℕ)
    (hd : Module.supportDim A M ≤ ((d : ℕ∞) : WithBot ℕ∞))
    (s : Finset (PrimeSpectrum A))
    (hs : ∀ p, p ∈ s ↔ p ∈ Module.support A M ∧
      ringKrullDim (A ⧸ p.asIdeal) = ((d : ℕ∞) : WithBot ℕ∞)) :
    multiplicity A M I d = primeMultiplicitySum A M I d s := by
  sorry

theorem exists_prime_multiplicity_finset
    (A : Type u) (M : Type v) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (hI : IsIdealOfDefinition A I) (d : ℕ)
    (hd : Module.supportDim A M ≤ ((d : ℕ∞) : WithBot ℕ∞)) :
    ∃ s : Finset (PrimeSpectrum A),
      (∀ p, p ∈ s ↔ p ∈ Module.support A M ∧
        ringKrullDim (A ⧸ p.asIdeal) = ((d : ℕ∞) : WithBot ℕ∞)) ∧
      multiplicity A M I d = primeMultiplicitySum A M I d s := by
  sorry

/-! ## Finite differences -/

/-- The backward finite-difference operator used in the leading-coefficient lemma. -/
def finiteDifference (f : ℚ → ℚ) (t : ℚ) : ℚ :=
  f t - f (t - 1)

/-- Iterated backward finite differences. -/
def iteratedFiniteDifference : ℕ → (ℚ → ℚ) → ℚ → ℚ
  | 0, f => f
  | n + 1, f => iteratedFiniteDifference n (fun t => finiteDifference f t)

theorem iteratedFiniteDifference_eq_binomial_sum
    (f : ℚ → ℚ) (r : ℕ) (t : ℚ) :
    iteratedFiniteDifference r f t =
      ∑ i ∈ Finset.range (r + 1),
        (-1 : ℚ) ^ i * (Nat.choose r i : ℚ) * f (t - i) := by
  sorry

theorem leading_coefficient_finite_difference
    (P : Polynomial ℚ) (r : ℕ) (a t : ℚ)
    (hdegree : P.degree = (r : WithBot ℕ)) (ha : P.coeff r = a) :
    (Nat.factorial r : ℚ) * a =
      ∑ i ∈ Finset.range (r + 1),
        (-1 : ℚ) ^ i * (Nat.choose r i : ℚ) * P.eval (t - i) := by
  sorry

/-! ## The Koszul formula -/

/-- The ideal generated by a finite sequence. -/
def idealOfSequence (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) : Ideal A :=
  Ideal.span (Set.range f)

/-- The ideal generated by a finite list. -/
def idealOfList (A : Type u) [CommRing A] (f : List A) : Ideal A :=
  Ideal.span (Set.range (fun i : Fin f.length => f.get i))

/-- The coefficient Koszul complex `K_•(A,f) ⊗_A M`. -/
noncomputable def koszulComplexWithCoefficients
    (A M : Type u) [CommRing A] [AddCommGroup M] [Module A M]
    (f : List A) : ChainComplex (ModuleCat.{u} A) ℕ :=
  koszulComplexOnListWithCoefficients A M f

/-- The alternating sum of the lengths of the coefficient Koszul homology. -/
noncomputable def koszulEulerCharacteristic
    (A M : Type u) [CommRing A] [AddCommGroup M] [Module A M]
    (f : List A) : ℤ :=
  ∑ i : Fin (f.length + 1),
    (-1 : ℤ) ^ (i : ℕ) *
      (Module.length A
        ((koszulComplexWithCoefficients A M f).homology (i : ℕ))).toNat

theorem koszul_homology_is_finiteLength
    (A M : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (f : List A) (hI : IsIdealOfDefinition A (idealOfList A f))
    (n : ℕ) :
      IsFiniteLength A
      ((koszulComplexWithCoefficients A M f).homology n) := by
  sorry

theorem koszul_homology_annihilated
    (A M : Type u) [CommRing A] [AddCommGroup M] [Module A M]
    (f : List A) (n : ℕ) :
    Module.IsTorsionBySet A
      ((koszulComplexWithCoefficients A M f).homology n)
      (Ideal.span (Set.range (fun i : Fin f.length => f.get i)) : Set A) := by
  sorry

theorem multiplicity_eq_koszulEulerCharacteristic
    (A M : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (r : ℕ) (f : Fin r → A)
    (hI : IsIdealOfDefinition A (idealOfSequence A r f)) :
    multiplicity A M (idealOfSequence A r f) r =
      (koszulEulerCharacteristic A M (List.ofFn f) : ℚ) := by
  sorry

/-! ## The generalization by the annihilator of the module -/

/-- The quotient module by the submodule `IM`. -/
abbrev quotientByIdeal
    (A : Type u) (M : Type v) [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) : Type v :=
  M ⧸ (I • (⊤ : Submodule A M))

def annihilatorExtendedIdeal
    (A M : Type u) [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) : Ideal A :=
  I + Module.annihilator A M

def annihilatorQuotientIdeal
    (A M : Type u) [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) : Ideal (A ⧸ Module.annihilator A M) :=
  I.map (Ideal.Quotient.mk (Module.annihilator A M))

/-- The annihilator quotient is nontrivial when the module is nontrivial. -/
theorem annihilatorQuotientNontrivial
    (A M : Type u) [CommRing A] [AddCommGroup M] [Module A M]
    [Nontrivial M] : Nontrivial (A ⧸ Module.annihilator A M) := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  intro htop
  have hsub : Subsingleton M := Module.annihilator_eq_top_iff.mp htop
  exact (not_nontrivial_iff_subsingleton.mpr hsub) inferInstance

/-- The canonical local-ring structure on the annihilator quotient. -/
theorem annihilatorQuotientIsLocalRing
    (A M : Type u) [CommRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Nontrivial M] :
    IsLocalRing (A ⧸ Module.annihilator A M) := by
  exact @IsLocalRing.of_surjective' A (A ⧸ Module.annihilator A M)
    _ _ _ (annihilatorQuotientNontrivial A M)
    (Ideal.Quotient.mk (Module.annihilator A M)) Ideal.Quotient.mk_surjective

/- The source's five-way equivalence is stated with no nonzero hypothesis;
   the `Nontrivial M` parameter is needed because `Ann(0) = ⊤`. -/
theorem annihilator_generalization_iff
    (A M : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M]
    (I : Ideal A) :
    (IsIdealOfDefinition A (annihilatorExtendedIdeal A M I) ↔
      @IsIdealOfDefinition (A ⧸ Module.annihilator A M) _
        (annihilatorQuotientIsLocalRing A M)
        (annihilatorQuotientIdeal A M I)) ∧
    (IsIdealOfDefinition A (annihilatorExtendedIdeal A M I) ↔
      Module.support A (quotientByIdeal A M I) ⊆
        {IsLocalRing.closedPoint A}) ∧
    (Module.support A (quotientByIdeal A M I) ⊆
        {IsLocalRing.closedPoint A} ↔
      Module.supportDim A (quotientByIdeal A M I) ≤ 0) ∧
    (Module.supportDim A (quotientByIdeal A M I) ≤ 0 ↔
      Module.length A (quotientByIdeal A M I) < ⊤) := by
  sorry

theorem annihilator_extended_power_eq
    (A M : Type u) [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) (n : ℕ) :
    idealPowerSubmodule A M I n =
      idealPowerSubmodule A M (annihilatorExtendedIdeal A M I) n := by
  sorry

theorem annihilator_quotient_power_equiv
    (A M : Type u) [CommRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Nontrivial M]
    (I : Ideal A) (n : ℕ) :
    let hTorsion : Module.IsTorsionBySet A M (Module.annihilator A M) := by
      exact (Module.isTorsionBySet_iff_subset_annihilator (R := A) (M := M)).mpr le_rfl
    letI : Module (A ⧸ Module.annihilator A M) M := hTorsion.module
    letI : Module A
        (idealPowerQuotient (A ⧸ Module.annihilator A M) M
          (annihilatorQuotientIdeal A M I) n) :=
      Module.compHom _ (Ideal.Quotient.mk (Module.annihilator A M))
    Nonempty
      (idealPowerQuotient A M I n ≃ₗ[A]
        idealPowerQuotient (A ⧸ Module.annihilator A M) M
          (annihilatorQuotientIdeal A M I) n) := by
  sorry

theorem annihilator_generalization_hilbert_invariant
    (A M : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) :
    hilbertCumulativeFunction A M I =
      hilbertCumulativeFunction A M (annihilatorExtendedIdeal A M I) := by
  sorry

theorem annihilator_generalization_quotient_hilbert_invariant
    (A M : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M]
    (I : Ideal A)
    (hI : IsIdealOfDefinition A (annihilatorExtendedIdeal A M I)) :
    let hTorsion : Module.IsTorsionBySet A M (Module.annihilator A M) := by
      exact (Module.isTorsionBySet_iff_subset_annihilator (R := A) (M := M)).mpr le_rfl
    letI : Module (A ⧸ Module.annihilator A M) M := hTorsion.module
    hilbertCumulativeFunction A M I =
      hilbertCumulativeFunction (A ⧸ Module.annihilator A M) M
        (annihilatorQuotientIdeal A M I) := by
  sorry

end

end Formalization.Books.Intersection.Unit15
