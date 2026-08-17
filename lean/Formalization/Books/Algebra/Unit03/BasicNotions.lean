import Mathlib.Algebra.EuclideanDomain.Defs
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Data.Finset.Sort
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

/-!
# Basic notions

This file records the precise declarations from Chapter 3 of the algebra book.
The standard notions in the list are represented by Mathlib's existing classes,
predicates, and constructions; the declarations below expose the source-facing
assertions which are not already a single canonical declaration.
-/

namespace Formalization.Books.Algebra.Unit03

open Set

universe u v w

/-! ### Rings, elements, finiteness, and fields -/

-- A ring, nilpotent element, zerodivisor, unit, idempotent, and ring homomorphism
-- are respectively `CommRing`, `IsNilpotent`, membership in `zeroDivisors`,
-- `IsUnit`, `IsIdempotentElem`, and `RingHom`.

def trivialIdempotent {R : Type u} [MulOneClass R] [Zero R] (e : R) : Prop :=
  IsIdempotentElem e ∧ (e = 1 ∨ e = 0)

-- The finiteness notions in the list are `RingHom.FinitePresentation`,
-- `RingHom.FiniteType`, and `RingHom.Finite`.
-- Domain, reduced, and Noetherian are represented by `IsDomain`, `IsReduced`,
-- and `IsNoetherianRing`.  A PID is `IsDomain` together with
-- `IsPrincipalIdealRing`; a UFD is `IsDomain` together with
-- `UniqueFactorizationMonoid`; Euclidean domains, DVRs, fields, and field
-- extensions use `EuclideanDomain`, `IsDiscreteValuationRing`, `Field`, and
-- `Algebra`, respectively.

-- Algebraicity and transcendence use `Algebra.IsAlgebraic`, `IsAlgebraic`,
-- `IsTranscendenceBasis`, `Algebra.trdeg`, and `IsAlgClosed`.

theorem exists_algHom_of_algebraic_of_algClosed
    {K L Ω : Type*} [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [IsAlgClosed Ω]
    (hL : Algebra.IsAlgebraic K L) : Nonempty (L →ₐ[K] Ω) := by
  let _ : Algebra.IsAlgebraic K L := hL
  exact ⟨IsAlgClosed.lift⟩

/-! ### Ideals -/

-- `Ideal` and `Ideal.IsRadical` are the canonical ideal and radical-ideal
-- notions, while `Ideal.radical` is the radical construction.
-- The nilpotence of an ideal is the existing predicate `IsNilpotent I`,
-- which unfolds to `∃ n : ℕ, I ^ n = 0`.

def locallyNilpotentIdeal {R : Type u} [CommRing R] (I : Ideal R) : Prop :=
  ∀ x : R, x ∈ I → IsNilpotent x

theorem prime_mul_le_iff
    {R : Type u} [CommRing R] {p I J : Ideal R} (hp : p.IsPrime) :
    I * J ≤ p ↔ I ≤ p ∨ J ≤ p := by
  exact hp.mul_le

theorem exists_maximal_ideal (R : Type u) [CommRing R] [Nontrivial R] :
    ∃ I : Ideal R, I.IsMaximal := by
  exact Ideal.exists_maximal R

theorem jacobson_radical_eq_sInf_maximal
    (R : Type u) [CommRing R] :
    Ring.jacobson R = sInf {I : Ideal R | I.IsMaximal} := by
  exact Ring.jacobson_eq_sInf_isMaximal R

-- `Ideal.span`, `R ⧸ I`, `Ideal.comap`, and `Ideal.map` are the generated
-- ideal, quotient ring, inverse-image ideal, and extended ideal.

theorem ideal_isPrime_iff_quotient_isDomain
    {R : Type u} [CommRing R] (I : Ideal R) :
    I.IsPrime ↔ IsDomain (R ⧸ I) := by
  exact (Ideal.Quotient.isDomain_iff_prime (I := I)).symm

theorem ideal_isMaximal_iff_quotient_isField
    {R : Type u} [CommRing R] (I : Ideal R) :
    I.IsMaximal ↔ IsField (R ⧸ I) := by
  exact Ideal.Quotient.maximal_ideal_iff_isField_quotient I

theorem comap_prime_ideal
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (p : Ideal S)
    [p.IsPrime] :
    (p.comap f).IsPrime := by
  exact Ideal.comap_isPrime f p

/-! ### Modules -/

-- `Module`, `Submodule`, `IsNoetherian`, `Module.Finite`,
-- `Module.FinitePresentation`, and `Module.Free` are the canonical module
-- notions.  The annihilator of an element is a span-annihilator.

def annihilatorOf {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (m : M) : Ideal R :=
  (Submodule.span R ({m} : Set M)).annihilator

theorem annihilatorOf_mem_iff {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (m : M) (r : R) :
    r ∈ annihilatorOf m ↔ r • m = 0 := by
  exact Submodule.mem_annihilator_span_singleton m r

theorem free_of_short_exact
    {R : Type u} {K L M : Type*} [Ring R]
    [AddCommGroup K] [AddCommGroup L] [AddCommGroup M]
    [Module R K] [Module R L] [Module R M]
    (f : K →ₗ[R] L) (g : L →ₗ[R] M)
    (hf : Function.Injective f) (hexact : Function.Exact f g)
    (hg : Function.Surjective g) [Module.Free R K] [Module.Free R M] :
    Module.Free R L := by
  sorry

-- The module third isomorphism theorem is Mathlib's canonical
-- `Submodule.quotientQuotientEquivQuotient`.

/-! ### Localization -/

-- A multiplicative subset is a `Submonoid`; `Localization S` and
-- `LocalizedModule S M` are the canonical ring and module localizations.
-- For a ring homomorphism `f`, `S.map f` is the image multiplicative subset.

def productSubmonoid {R : Type u} [CommMonoid R]
    (S T : Submonoid R) : Submonoid R := S ⊔ T

theorem localization_isZero_iff
    {R : Type u} [CommSemiring R] (S : Submonoid R) :
    Subsingleton (Localization S) ↔ (0 : R) ∈ S := by
  exact IsLocalization.subsingleton_iff

theorem localization_algebraMap_injective_of_nonZeroDivisors
    {R : Type u} [CommRing R] (S : Submonoid R)
    (hS : S ≤ nonZeroDivisors R) :
    Function.Injective (algebraMap R (Localization S)) := by
  exact IsLocalization.injective (Localization S) hS

theorem iterated_localization_isLocalization
    {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]
    (M : Submonoid R) (N : Submonoid S)
    [Algebra R S] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [IsLocalization M S] [IsLocalization N T] :
    IsLocalization (IsLocalization.localizationLocalizationSubmodule M N) T := by
  exact IsLocalization.localization_localization_isLocalization M N T

theorem localizedModule_map_injective
    {R M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    (S : Submonoid R) (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Function.Injective (LocalizedModule.map S f) := by
  exact LocalizedModule.map_injective S f hf

theorem localizedModule_map_surjective
    {R M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    (S : Submonoid R) (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Function.Surjective (LocalizedModule.map S f) := by
  exact LocalizedModule.map_surjective S f hf

theorem localizedModule_map_exact
    {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (S : Submonoid R) (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (h : Function.Exact f g) :
    Function.Exact (LocalizedModule.map S f) (LocalizedModule.map S g) := by
  exact LocalizedModule.map_exact S f g h

theorem iterated_localizedModule_equiv
    {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (S T : Submonoid R) :
    Nonempty
      (LocalizedModule (productSubmonoid T S) M ≃ₗ[R]
        LocalizedModule (T.map (algebraMap R (Localization S)))
          (LocalizedModule S M)) := by
  sorry

theorem localized_ideal_quotient_equiv
    {R : Type u} [CommRing R] (S : Submonoid R) (I : Ideal R) :
    Nonempty
      ((Localization S ⧸ Ideal.map (algebraMap R (Localization S)) I) ≃+*
        Localization (S.map (Ideal.Quotient.mk I))) := by
  sorry

theorem ideal_in_localization_eq_map_under
    {R : Type u} [CommRing R] (S : Submonoid R) (J : Ideal (Localization S)) :
    Ideal.map (algebraMap R (Localization S)) (J.under R) = J := by
  exact IsLocalization.map_under S (Localization S) J

theorem submodule_in_localizedModule_eq_localized
    {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (S : Submonoid R)
    (N' : Submodule (Localization S) (LocalizedModule S M)) :
    N' =
      Submodule.localized' (Localization S) S (LocalizedModule.mkLinearMap S M)
        ((N'.restrictScalars R).comap (LocalizedModule.mkLinearMap S M)) := by
  sorry

abbrev localizationAway {R : Type u} [CommSemiring R] (f : R) : Type u :=
  Localization.Away f

abbrev localizedModuleAway {R M : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] (f : R) : Type _ :=
  LocalizedModule (Submonoid.powers f) M

abbrev localizationAtPrime {R : Type u} [CommSemiring R]
    (p : Ideal R) [p.IsPrime] : Type u :=
  Localization.AtPrime p

abbrev localizedModuleAtPrime {R M : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] (p : Ideal R) [p.IsPrime] : Type _ :=
  LocalizedModule p.primeCompl M

/-! ### Local and semilocal rings, residue fields, and tensor products -/

theorem isLocalRing_iff_unique_maximalIdeal
    {R : Type u} [CommSemiring R] :
    IsLocalRing R ↔ ∃! I : Ideal R, I.IsMaximal := by
  constructor
  · intro h
    exact @IsLocalRing.maximal_ideal_unique R _ h
  · exact IsLocalRing.of_unique_max_ideal

def IsSemilocalRing (R : Type u) [CommRing R] : Prop :=
  Set.Finite {I : Ideal R | I.IsMaximal}

theorem localization_atPrime_isLocalRing
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :
    IsLocalRing (Localization.AtPrime p) := by
  infer_instance

theorem localization_atPrime_maximalIdeal_eq
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :
    Ideal.map (algebraMap R (Localization.AtPrime p)) p =
      IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
  exact IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization.AtPrime p)

theorem residueField_isFractionRing
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :
    IsFractionRing (R ⧸ p) p.ResidueField := by
  infer_instance

theorem residueField_eq_atPrime_quotient
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :
    p.ResidueField =
      (Localization.AtPrime p ⧸
        Ideal.map (algebraMap R (Localization.AtPrime p)) p) := by
  calc
    p.ResidueField =
        (Localization.AtPrime p ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime p)) := rfl
    _ = (Localization.AtPrime p ⧸
        Ideal.map (algebraMap R (Localization.AtPrime p)) p) := by
      rw [localization_atPrime_maximalIdeal_eq p]

-- The tensor product is Mathlib's `TensorProduct R M₁ M₂`, written
-- `M₁ ⊗[R] M₂`.

/-! ### Cauchy--Binet -/

noncomputable def columnMinor
    {R : Type u} [CommRing R] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R)
    (S : {s : Finset (Fin n) // s.card = m}) : R :=
  (A.submatrix id (fun i => (S.1.orderIsoOfFin S.2 i : Fin n))).det

noncomputable def rowMinor
    {R : Type u} [CommRing R] {m n : ℕ}
    (B : Matrix (Fin n) (Fin m) R)
    (S : {s : Finset (Fin n) // s.card = m}) : R :=
  (B.submatrix (fun i => (S.1.orderIsoOfFin S.2 i : Fin n)) id).det

theorem cauchyBinet
    {R : Type u} [CommRing R] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
    (A * B).det =
      ∑ S : {s : Finset (Fin n) // s.card = m},
        columnMinor A S * rowMinor B S := by
  sorry

end Formalization.Books.Algebra.Unit03
