import Formalization.Books.Algebra.Unit03.BasicNotions
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Commutative Algebra, Chapter 78: Finite projective modules

The open-cover definitions in the source are recorded explicitly using basic
opens of the spectrum.  Freeness at prime and maximal stalks, and the rank
function, use Mathlib's canonical `Module.freeLocus` and `Module.rankAtStalk`.
-/

namespace Formalization.Books.Algebra.Unit78

open Set
open scoped TensorProduct

universe u v

noncomputable section

/-! ## Locally free modules -/

/- The source uses a covering by standard opens.  A set `s` with
`Ideal.span s = ⊤` is the canonical affine formulation of such a covering. -/

/-- A module which is free on a basic-open cover of `Spec R`. -/
def LocallyFree (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  ∃ s : Set R, Ideal.span s = ⊤ ∧
    ∀ f ∈ s,
      Module.Free (Localization.Away f) (LocalizedModule.Away f M)

/-- A module which is finite free on a basic-open cover of `Spec R`. -/
def FiniteLocallyFree (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  ∃ s : Set R, Ideal.span s = ⊤ ∧
    ∀ f ∈ s,
      Module.Finite (Localization.Away f) (LocalizedModule.Away f M) ∧
        Module.Free (Localization.Away f) (LocalizedModule.Away f M)

/-- A module which is free of the fixed rank `r` on a basic-open cover. -/
def FiniteLocallyFreeOfRank
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] (r : ℕ) : Prop :=
  ∃ s : Set R, Ideal.span s = ⊤ ∧
    ∀ f ∈ s,
      Nonempty
        (LocalizedModule.Away f M ≃ₗ[Localization.Away f]
          (Fin r →₀ Localization.Away f))

/-- A finite locally free module has a finite presentation. -/
theorem finitePresentation_of_finiteLocallyFree
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (hM : FiniteLocallyFree R M) :
    Module.FinitePresentation R M := by
  sorry

/-- The rank in a finite locally free rank condition is unique over a nonzero ring. -/
theorem finiteLocallyFree_rank_unique
    {R M : Type*} [CommRing R] [Nontrivial R]
    [AddCommGroup M] [Module R M] {r s : ℕ}
    (hr : FiniteLocallyFreeOfRank R M r)
    (hs : FiniteLocallyFreeOfRank R M s) :
    r = s := by
  sorry

/-! ## The finite projective characterization -/

/- `Module.Finite` and `Module.Projective` are the canonical finiteness and
projectivity predicates; this conjunction is the source's “finite projective”. -/

/-- A finite projective module. -/
def FiniteProjective
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  Module.Finite R M ∧ Module.Projective R M

/- A direct summand of a finite free module is represented using the canonical
finite free module `Fin n →₀ R` and a retraction. -/

/-- `M` is a direct summand of a finite free `R`-module. -/
def FiniteFreeSummand
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  ∃ n : ℕ, ∃ i : M →ₗ[R] (Fin n →₀ R),
    ∃ p : (Fin n →₀ R) →ₗ[R] M,
      p.comp i = LinearMap.id

/-- Mathlib's canonical rank-at-stalk function, used for the source's `ρ_M`. -/
noncomputable def rankFunction
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] :
    PrimeSpectrum R → ℤ :=
  fun p => Module.rankAtStalk M p

/-- The rank-at-stalk function agrees with the fiber dimension in the source. -/
theorem rankFunction_eq_fiber_finrank
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Flat R M] [Module.Finite R M]
    (p : PrimeSpectrum R) :
    rankFunction R M p =
      (Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M) : ℤ) := by
  simpa [rankFunction] using congrArg Int.ofNat
    (Module.rankAtStalk_eq (R := R) (M := M) p)

/-- The eight conditions in the finite-projective characterization. -/
def finiteProjectiveConditions
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] : List Prop :=
  [ Module.FinitePresentation R M ∧ Module.Flat R M,
    FiniteProjective R M,
    FiniteFreeSummand R M,
    Module.FinitePresentation R M ∧
      ∀ p : PrimeSpectrum R, p ∈ Module.freeLocus R M,
    Module.FinitePresentation R M ∧
      ∀ m : MaximalSpectrum R,
        Module.Free (Localization.AtPrime m.asIdeal)
          (LocalizedModule m.asIdeal.primeCompl M),
    Module.Finite R M ∧ LocallyFree R M,
    FiniteLocallyFree R M,
    Module.Finite R M ∧
      (∀ p : PrimeSpectrum R, p ∈ Module.freeLocus R M) ∧
        IsLocallyConstant (rankFunction R M) ]

/-- The source's eight equivalent characterizations of finite projectivity. -/
theorem finite_projective_characterization
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    List.TFAE (finiteProjectiveConditions R M) := by
  sorry

/-! ## The reduced-ring criterion and the warning -/

/-- The ninth condition in the reduced-ring variant. -/
def FiniteLocallyConstantRank
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  Module.Finite R M ∧ IsLocallyConstant (rankFunction R M)

/-- Over a reduced ring, the ninth rank criterion is equivalent to the eight conditions above. -/
theorem finite_projective_reduced_characterization
    {R M : Type*} [CommRing R] [IsReduced R] [AddCommGroup M] [Module R M] :
    List.TFAE
      (finiteProjectiveConditions R M ++ [FiniteLocallyConstantRank R M]) := by
  sorry

/-- The property exhibited by the warning's finite flat non-projective example. -/
def IsFiniteFlatNotProjective
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  Module.Finite R M ∧ Module.Flat R M ∧ ¬ Module.Projective R M

/- The source gives the concrete example `C^∞(ℝ)` and its local quotient.  The
abstract existence statement records the mathematical warning without adding a
non-canonical smooth-function-ring model to this algebra chapter. -/

/-- Finite flat modules need not be projective. -/
theorem exists_finite_flat_not_projective :
    ∃ (R : Type u) (_ : CommRing R) (M : Type v)
      (_ : AddCommGroup M) (_ : Module R M),
      IsFiniteFlatNotProjective R M := by
  sorry

/-! ## Local finite flatness and descent -/

/-- A finite flat module over a local ring is finite free. -/
theorem finite_flat_local_is_free
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M] :
    Module.Free R M :=
  Module.free_of_flat_of_isLocalRing

/-- Finite projectivity descends and ascends along a flat local map of local rings. -/
theorem finite_projective_descends
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R S] :
    FiniteProjective R M ↔ FiniteProjective S (S ⊗[R] M) := by
  sorry

/-! ## Semilocal freeness -/

/-- A finite locally free module has constant rank if it has one fixed local rank. -/
def ConstantRank
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  ∃ r : ℕ, FiniteLocallyFreeOfRank R M r

/-- A constant-rank finite locally free module over a semilocal ring is free. -/
theorem free_of_finiteLocallyFree_of_constantRank
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (hR : Formalization.Books.Algebra.Unit03.IsSemilocalRing R)
    (hM : FiniteLocallyFree R M) (hr : ConstantRank R M) :
    Module.Free R M := by
  sorry

/-- A finite locally free module over a semilocal ring with connected spectrum is free. -/
theorem free_of_finiteLocallyFree_of_connectedSpectrum
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [ConnectedSpace (PrimeSpectrum R)]
    (hR : Formalization.Books.Algebra.Unit03.IsSemilocalRing R)
    (hM : FiniteLocallyFree R M) :
    Module.Free R M := by
  sorry

/-! ## A basis in a generating submodule -/

/--
If a finite free module over a semilocal algebra is generated by an
`R`-submodule and the extended maximal ideal lies in the Jacobson radical,
the submodule contains an `S`-basis.
-/
theorem exists_basis_subset_of_semilocal
    {R S M : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [Infinite (IsLocalRing.ResidueField R)]
    [Algebra R S] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [Module.Finite S M] [Module.Free S M]
    (N : Submodule R M)
    (hS : Formalization.Books.Algebra.Unit03.IsSemilocalRing S)
    (hm : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) ≤ Ring.jacobson S)
    (hN : Submodule.span S (N : Set M) = ⊤) :
    ∃ (ι : Type*) (b : Module.Basis ι S M), ∀ i, b i ∈ N := by
  sorry

/-! ## Evaluation and tensor products -/

/-- The canonical evaluation map from `Hom(M, N) ⊗ L` to `Hom(M, N ⊗ L)`. -/
noncomputable def evaluationMap
    {R L M N : Type*} [CommRing R]
    [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] :
    ((M →ₗ[R] N) ⊗[R] L) →ₗ[R] (M →ₗ[R] (N ⊗[R] L)) :=
  (LinearMap.compRight R (TensorProduct.comm R L N).toLinearMap).comp
    ((TensorProduct.lTensorHomToHomLTensor (RingHom.id R) M L N).comp
      (TensorProduct.comm R (M →ₗ[R] N) L).toLinearMap)

/-- The canonical equivalence behind `evaluationMap` when `M` is finite projective. -/
noncomputable def evaluationEquiv
    {R L M N : Type*} [CommRing R]
    [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Projective R M] :
    ((M →ₗ[R] N) ⊗[R] L) ≃ₗ[R] (M →ₗ[R] (N ⊗[R] L)) :=
  (TensorProduct.comm R (M →ₗ[R] N) L).trans
    ((lTensorHomEquivHomLTensor R M L N).trans
      ((LinearEquiv.refl R M).arrowCongr (TensorProduct.comm R L N)))

/-- The displayed equivalence has the same underlying map as `evaluationMap`. -/
theorem evaluationMap_eq_evaluationEquiv_toLinearMap
    {R L M N : Type*} [CommRing R]
    [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Projective R M] :
    evaluationMap (R := R) (L := L) (M := M) (N := N) =
      (evaluationEquiv (R := R) (L := L) (M := M) (N := N)).toLinearMap := by
  sorry

/-- The evaluation map is an isomorphism when `M` is finite projective. -/
theorem evaluationMap_isomorphism
    {R L M N : Type*} [CommRing R]
    [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Projective R M] :
    Function.Bijective (evaluationMap (R := R) (L := L) (M := M) (N := N)) := by
  rw [evaluationMap_eq_evaluationEquiv_toLinearMap]
  exact (evaluationEquiv (R := R) (L := L) (M := M) (N := N)).bijective

end

end Formalization.Books.Algebra.Unit78
