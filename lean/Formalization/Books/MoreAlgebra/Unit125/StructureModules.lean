/-
# More on Algebra, Chapter 125: Structure of modules over a PID
-/

import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
This file records the definitions and theorem interfaces in the source chapter.
The standard module, localization, torsion, direct-sum, and matrix APIs are used
directly; the proofs of the structural results are left to the proving stage.
-/

namespace Formalization.Books.MoreAlgebra.Unit125

noncomputable section

open Set
open CategoryTheory
open scoped DirectSum

universe u v w

/-! ## Cyclic modules and summands -/

/-- The module denoted by `R / fR` in the source. -/
abbrev principalQuotient (R : Type u) [CommRing R] (f : R) : Type u :=
  R ⧸ Ideal.span ({f} : Set R)

/-- A finite direct sum of principal cyclic modules. -/
abbrev finiteCyclicDirectSum (R : Type u) [CommRing R] (n : ℕ)
    (f : Fin n → R) : Type u :=
  ⨁ i : Fin n, principalQuotient R (f i)

/-- A module is a linear direct summand of another module. -/
def IsLinearSummandOf (R : Type u) (T : Type v) (N : Type w) [CommRing R]
    [AddCommGroup T] [Module R T] [AddCommGroup N] [Module R N] : Prop :=
  ∃ K : Submodule R N,
    IsComplemented K ∧ Nonempty (T ≃ₗ[R] K)

/-- A module is a summand of a possibly infinite direct sum of cyclic modules. -/
def IsCyclicDirectSummand (R : Type u) (T : Type v) [CommRing R]
    [AddCommGroup T] [Module R T] : Prop :=
  ∃ (ι : Type (max u v)) (f : ι → R),
    IsLinearSummandOf R T (⨁ i : ι, principalQuotient R (f i))

/-- A module is a summand of a finite direct sum of cyclic modules. -/
def IsFiniteCyclicSummand (R : Type u) (T : Type v) [CommRing R]
    [AddCommGroup T] [Module R T] : Prop :=
  ∃ (n : ℕ) (f : Fin n → R),
    IsLinearSummandOf R T (finiteCyclicDirectSum R n f)

/-- A module is a summand of a finite direct sum of cyclic torsion modules
whose defining scalars are nonzero. -/
def IsFiniteNonzeroCyclicSummand (R : Type u) (T : Type v) [CommRing R]
    [AddCommGroup T] [Module R T] : Prop :=
  ∃ (n : ℕ) (f : Fin n → R),
    (∀ i, f i ≠ 0) ∧
      IsLinearSummandOf R T (finiteCyclicDirectSum R n f)

/-! ## The PD-module lifting criterion -/

/-- The condition `fA = A ∩ fB` for the first map of a module short complex. -/
def IsPureFirstMap {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{v} R)) : Prop :=
  ∀ f : R, ∀ x : (S.X₁ : Type v),
    (∃ y : (S.X₁ : Type v), f • y = x) ↔
      ∃ y : (S.X₂ : Type v), f • y = S.f.hom x

/-- Postcomposition with the second map of a module short complex. -/
def homToThirdMap {R : Type u} {P : Type v} [CommRing R]
    [AddCommGroup P] [Module R P]
    (S : ShortComplex (ModuleCat.{v} R)) :
    (P →ₗ[R] (S.X₂ : Type v)) → (P →ₗ[R] (S.X₃ : Type v)) :=
  fun φ => S.g.hom.comp φ

/-- The source's characterization of modules which are summands of sums of cyclic modules. -/
theorem characterize_pd_modules
    {R : Type u} {P : Type v} [CommRing R] [AddCommGroup P] [Module R P] :
    IsCyclicDirectSummand R P ↔
      ∀ (S : ShortComplex (ModuleCat.{v} R)),
        S.ShortExact → IsPureFirstMap S →
          Function.Surjective (homToThirdMap (P := P) S) := by
  sorry

/-! ## Generalized valuation rings -/

/- The source's generalized valuation-ring condition is Mathlib's
`PreValuationRing`, which deliberately does not require a domain. -/

/-- The divisibility characterization is equivalent to locality and the Bézout property. -/
theorem generalizedValuationRing_iff_local_bezout
    (R : Type u) [CommRing R] [Nontrivial R] :
    PreValuationRing R ↔ IsLocalRing R ∧ IsBezout R := by
  sorry

/-- The divisibility characterization is equivalent to the linear order on ideals. -/
theorem generalizedValuationRing_iff_ideal_chain
    (R : Type u) [CommRing R] [Nontrivial R] :
    PreValuationRing R ↔
      ∀ I J : Ideal R, I ≤ J ∨ J ≤ I := by
  sorry

/-- A valuation ring satisfies the generalized valuation-ring condition. -/
theorem valuationRing_isGeneralizedValuationRing
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] :
    PreValuationRing R := by
  sorry

/-! ## Finitely presented modules over generalized valuation rings -/

/-- A finitely presented module over a generalized valuation ring is a finite
direct sum of principal cyclic modules. -/
theorem generalizedValuationRing_finitePresentation
    {R : Type u} {M : Type v} [CommRing R] [Nontrivial R]
    [AddCommGroup M] [Module R M]
    (hR : PreValuationRing R)
    [Module.FinitePresentation R M] :
    ∃ (n : ℕ) (f : Fin n → R),
      Nonempty (M ≃ₗ[R] finiteCyclicDirectSum R n f) := by
  sorry

/-! ## Warfield's local-to-global summand theorem -/

/-- Warfield's theorem: the local generalized valuation-ring hypothesis makes
a finitely presented module a summand of a finite cyclic direct sum. -/
theorem warfield
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    (hlocal : ∀ m : MaximalSpectrum R,
      PreValuationRing (Localization.AtPrime m.asIdeal))
    [Module.FinitePresentation R M] :
    IsFiniteCyclicSummand R M := by
  sorry

/-! ## Bézout and elementary divisor domains -/

/-- A Bézout domain, using Mathlib's canonical Bézout predicate. -/
def IsBezoutDomain (R : Type u) [CommRing R] : Prop :=
  IsDomain R ∧ IsBezout R

/-- The rectangular diagonal matrix with diagonal entries indexed by
`Fin (min n m)`. -/
def rectangularDiagonal {n m : ℕ} {R : Type u} [CommRing R]
    (f : Fin (min n m) → R) : Matrix (Fin n) (Fin m) R :=
  fun i j =>
    if _h : i.1 = j.1 then
      if h' : i.1 < min n m then f ⟨i.1, h'⟩ else 0
    else 0

/-- An elementary divisor domain, expressed by Smith normal forms of matrices. -/
def IsElementaryDivisorDomain (R : Type u) [CommRing R] : Prop :=
  IsDomain R ∧
    ∀ {n m : ℕ}, 0 < n → 0 < m →
      ∀ A : Matrix (Fin n) (Fin m) R,
        ∃ U : Matrix.GeneralLinearGroup (Fin n) R,
          ∃ V : Matrix.GeneralLinearGroup (Fin m) R,
            ∃ f : Fin (min n m) → R,
              (∀ ⦃i j : Fin (min n m)⦄, i.1 ≤ j.1 → f i ∣ f j) ∧
                (U : Matrix (Fin n) (Fin n) R) * A *
                    (V : Matrix (Fin m) (Fin m) R) = rectangularDiagonal f

/-- The module-theoretic formulation equivalent to the elementary-divisor property. -/
def EveryFinitelyPresentedModuleIsFiniteCyclicSum
    (R : Type u) [CommRing R] : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module R M],
    Module.FinitePresentation R M →
      ∃ (n : ℕ) (f : Fin n → R),
        Nonempty (M ≃ₗ[R] finiteCyclicDirectSum R n f)

/-- The open-question formulation in the source is equivalent over a Bézout domain. -/
theorem elementaryDivisorDomain_iff_finiteCyclicDecomposition
    {R : Type u} [CommRing R] (hR : IsBezoutDomain R) :
    IsElementaryDivisorDomain R ↔
      EveryFinitelyPresentedModuleIsFiniteCyclicSum R := by
  sorry

/-- An elementary divisor domain is a Bézout domain. -/
theorem elementaryDivisorDomain_isBezoutDomain
    {R : Type u} [CommRing R]
    (hR : IsElementaryDivisorDomain R) :
    IsBezoutDomain R := by
  sorry

/-- A PID is an elementary divisor domain. -/
theorem principalIdealDomain_isElementaryDivisorDomain
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] :
    IsElementaryDivisorDomain R := by
  sorry

/-! ## Localizations and valuation rings -/

/-- Localization preserves the Bézout ideal property. -/
theorem localization_isBezout
    {R : Type u} [CommRing R] (hR : IsBezoutDomain R) (S : Submonoid R) :
    IsBezout (Localization S) := by
  sorry

/-- A localization away from zero divisors of a Bézout domain is again a
Bézout domain.  The explicit hypothesis excludes the zero localization. -/
theorem localization_isBezoutDomain
    {R : Type u} [CommRing R] (hR : IsBezoutDomain R) (S : Submonoid R)
    (hS : S ≤ nonZeroDivisors R) :
    IsBezoutDomain (Localization S) := by
  sorry

/-- Localizations at maximal ideals of a Bézout domain are valuation rings. -/
theorem localizations_of_bezoutDomain_are_valuationRings
    {R : Type u} [CommRing R] [IsDomain R]
    (hR : IsBezoutDomain R) :
    ∀ m : MaximalSpectrum R, ValuationRing (Localization.AtPrime m.asIdeal) := by
  sorry

/-- For a local domain, the Bézout and valuation-ring conditions coincide. -/
theorem localDomain_isBezout_iff_valuationRing
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R] :
    IsBezout R ↔ ValuationRing R := by
  sorry

/-! ## Splitting off the free and torsion parts -/

/-- A finite submodule of a free module over a Bézout domain is free. -/
theorem finite_submodule_of_free_isFree
    {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M]
    (hR : IsBezoutDomain R) (N : Submodule R M)
    [Module.Finite R N] [Module.Free R M] :
    Module.Free R N := by
  sorry

/-- A finitely presented module over a Bézout domain splits as a finite free
module and its canonical torsion submodule, which is a finite cyclic summand. -/
theorem finitelyPresented_split_free_torsion
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    (hR : IsBezoutDomain R)
    [Module.FinitePresentation R M] :
    ∃ r : ℕ,
        Nonempty
            (M ≃ₗ[R] (Fin r →₀ R) × (Submodule.torsion R M)) ∧
        Module.IsTorsion R (Submodule.torsion R M) ∧
        IsFiniteNonzeroCyclicSummand R (Submodule.torsion R M) := by
  sorry

/-! ## The structure theorem over a PID -/

/-- Every finite module over a PID is a finite free module plus finitely many
cyclic torsion modules. -/
theorem finiteModule_over_pid_structure
    {R : Type u} {M : Type v} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ (r n : ℕ) (f : Fin n → R),
      (∀ i, f i ≠ 0) ∧
        Nonempty
          (M ≃ₗ[R] (Fin r →₀ R) × finiteCyclicDirectSum R n f) := by
  sorry

/-! ## Unimodular vectors -/

/-- The first index in a nonempty finite index type. -/
def firstIndex {n : ℕ} (hn : 0 < n) : Fin n :=
  ⟨0, hn⟩

/-- A unimodular row over a Bézout domain extends to an invertible matrix. -/
theorem unimodular_vector
    {R : Type u} [CommRing R] (hR : IsBezoutDomain R)
    {n : ℕ} (hn : 0 < n) (f : Fin n → R)
    (hgen : Ideal.span (Set.range f) = ⊤) :
    ∃ U : Matrix.GeneralLinearGroup (Fin n) R,
      ∀ j : Fin n,
        (U : Matrix (Fin n) (Fin n) R) (firstIndex hn) j = f j := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit125
