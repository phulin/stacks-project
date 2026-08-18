import Formalization.Books.Algebra.Unit03.BasicNotions
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.Projective
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.LocallyFree
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.LocalProperties.FinitePresentation
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.IdempotentFG
import Mathlib.RingTheory.Ideal.Pure
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.Tactic.TFAE
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Commutative Algebra, Chapter 78: Finite projective modules

The open-cover definitions in the source are recorded explicitly using basic
opens of the spectrum.  Freeness at prime and maximal stalks, and the fiber
dimension function, use Mathlib's canonical `Module.freeLocus` and fiber API.
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
  obtain ⟨s, hs, h⟩ := hM
  apply Module.FinitePresentation.of_localizationSpan s hs
  intro f
  letI := h f f.property |>.1
  letI := h f f.property |>.2
  exact Module.finitePresentation_of_free_of_surjective LinearMap.id
    (by exact Function.surjective_id) (by exact Submodule.fg_bot)

/-- The rank in a finite locally free rank condition is unique over a nonzero ring. -/
theorem finiteLocallyFree_rank_unique
    {R M : Type*} [CommRing R] [Nontrivial R]
    [AddCommGroup M] [Module R M] {r s : ℕ}
    (hr : FiniteLocallyFreeOfRank R M r)
    (hs : FiniteLocallyFreeOfRank R M s) :
    r = s := by
  classical
  rcases hr with ⟨u, hu, hru⟩
  rcases hs with ⟨v, hv, hsv⟩
  obtain ⟨I, hI⟩ := Formalization.Books.Algebra.Unit03.exists_maximal_ideal R
  letI : I.IsPrime := hI.isPrime
  have pick (w : Set R) (hw : Ideal.span w = ⊤) : ∃ a ∈ w, a ∉ I := by
    by_contra h
    push_neg at h
    have hle : Ideal.span w ≤ I := Ideal.span_le.mpr h
    exact hI.ne_top (by
      apply top_unique
      rw [← hw]
      exact hle)
  obtain ⟨a, hau, haI⟩ := pick u hu
  obtain ⟨b, hbv, hbI⟩ := pick v hv
  have rank_at (a : R) (haI : a ∉ I) {n : ℕ}
      (he : Nonempty
        (LocalizedModule.Away a M ≃ₗ[Localization.Away a]
          (Fin n →₀ Localization.Away a))) :
      Module.finrank (Localization.AtPrime I)
        (LocalizedModule I.primeCompl M) = n := by
    have hle : Submonoid.powers a ≤ I.primeCompl := by
      rintro _ ⟨k, rfl⟩
      exact I.primeCompl.pow_mem haI k
    let Rₚ := Localization.AtPrime I
    let Mₚ := LocalizedModule I.primeCompl M
    let p' := Algebra.algebraMapSubmonoid (Localization.Away a) I.primeCompl
    let : Algebra (Localization.Away a) Rₚ :=
      IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers a)
        I.primeCompl hle
    letI : Nontrivial (Localization.Away a) :=
      (IsLocalization.toLocalizationMap (Submonoid.powers a)
        (Localization.Away a)).nontrivial (by
          rintro ⟨k, hk⟩
          exact (I.primeCompl.pow_mem haI k) (by
            change a ^ k = 0 at hk
            rw [hk]
            exact I.zero_mem))
    have : IsScalarTower R (Localization.Away a) Rₚ :=
      IsLocalization.localization_isScalarTower_of_submonoid_le ..
    let : Module (Localization.Away a) Mₚ := Module.compHom Mₚ (algebraMap _ Rₚ)
    have hRM : IsScalarTower R Rₚ Mₚ := by infer_instance
    have : IsScalarTower R (Localization.Away a) Mₚ :=
      ⟨fun r r' m ↦ by
        change algebraMap (Localization.Away a) Rₚ (r • r') • m =
          r • (algebraMap (Localization.Away a) Rₚ r' • m)
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, mul_smul]
        simpa only [Algebra.smul_def, mul_smul] using
          hRM.smul_assoc r (algebraMap (Localization.Away a) Rₚ r') m⟩
    have : IsScalarTower (Localization.Away a) Rₚ Mₚ :=
      ⟨fun r r' m ↦ show (r • r') • m =
          algebraMap (Localization.Away a) Rₚ r • r' • m by
        rw [← mul_smul, ← Algebra.smul_def]⟩
    let l :=
      (IsLocalizedModule.liftOfLE _ _ hle
        (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
        (LocalizedModule.mkLinearMap I.primeCompl M)).extendScalarsOfIsLocalization
        (Submonoid.powers a) (Localization.Away a)
    have : IsLocalization p' Rₚ :=
      IsLocalization.isLocalization_of_submonoid_le (Localization.Away a) Rₚ _ _ hle
    have : IsLocalizedModule I.primeCompl (l.restrictScalars R) :=
      inferInstanceAs (IsLocalizedModule I.primeCompl
        (IsLocalizedModule.liftOfLE _ _ hle
          (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
          (LocalizedModule.mkLinearMap I.primeCompl M)))
    have : IsLocalizedModule (Algebra.algebraMapSubmonoid (Localization.Away a)
        I.primeCompl) l := IsLocalizedModule.of_restrictScalars I.primeCompl ..
    obtain ⟨e⟩ := he
    letI : Module.Free (Localization.Away a) (LocalizedModule.Away a M) :=
      Module.Free.of_equiv e.symm
    have hloc : Module.finrank Rₚ Mₚ =
        Module.finrank (Localization.Away a)
          (LocalizedModule.Away a M) :=
      Module.finrank_of_isLocalizedModule_of_free Rₚ p' l
    have heq : Module.finrank (Localization.Away a)
        (LocalizedModule.Away a M) = n := by
      calc
        _ = Module.finrank (Localization.Away a)
            (Fin n →₀ Localization.Away a) := e.finrank_eq
        _ = Module.finrank (Localization.Away a)
            (Fin n → Localization.Away a) :=
          (Finsupp.linearEquivFunOnFinite (Localization.Away a)
            (Localization.Away a) (Fin n)).finrank_eq
        _ = Fintype.card (Fin n) :=
          Module.finrank_fintype_fun_eq_card (Localization.Away a)
        _ = n := Fintype.card_fin n
    simpa [Rₚ, Mₚ] using hloc.trans heq
  have hru' := rank_at a haI (hru a hau)
  have hsv' := rank_at b hbI (hsv b hbv)
  exact hru'.symm.trans hsv'

/-! ## The finite projective characterization -/

/- `Module.Finite` and `Module.Projective` are the canonical finiteness and
projectivity predicates; this conjunction is the source's “finite projective”. -/

/-- A finite projective module. -/
def FiniteProjective
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  Module.Finite R M ∧ Module.Projective R M

private theorem finiteLocallyFree_of_finiteProjective
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (hM : FiniteProjective R M) : FiniteLocallyFree R M := by
  letI : Module.Finite R M := hM.1
  letI : Module.Projective R M := hM.2
  letI : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  let s : Set R :=
    {f | Module.Free (Localization.Away f) (LocalizedModule.Away f M)}
  have hs : Ideal.span s = ⊤ := by
    by_contra hst
    obtain ⟨I, hI, hIs⟩ := Ideal.ne_top_iff_exists_maximal.mp hst
    let p : PrimeSpectrum R := ⟨I, hI.isPrime⟩
    have hp : Module.Free (Localization.AtPrime I)
        (LocalizedModule I.primeCompl M) := by
      simpa only [p] using
        (Module.mem_freeLocus.mp
          (Module.freeLocus_eq_univ_iff.mpr hM.2 ▸ Set.mem_univ p))
    obtain ⟨f, hf, hfree, _⟩ :=
      Module.FinitePresentation.exists_free_localizedModule_powers
        I.primeCompl (LocalizedModule.mkLinearMap I.primeCompl M)
        (Localization.AtPrime I)
    exact hf (hIs (Ideal.subset_span hfree))
  refine ⟨s, hs, ?_⟩
  intro f hf
  exact ⟨by infer_instance, hf⟩

private theorem free_at_prime_of_locallyFree
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (hM : LocallyFree R M) (p : PrimeSpectrum R) :
    Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl M) := by
  rcases hM with ⟨s, hs, hfree⟩
  have pick : ∃ a ∈ s, a ∉ p.asIdeal := by
    by_contra h
    push_neg at h
    have hle : Ideal.span s ≤ p.asIdeal := Ideal.span_le.mpr h
    exact p.isPrime.ne_top (by
      apply top_unique
      rw [← hs]
      exact hle)
  obtain ⟨a, ha, hap⟩ := pick
  have hle : Submonoid.powers a ≤ p.asIdeal.primeCompl := by
    rintro _ ⟨k, rfl⟩
    exact p.asIdeal.primeCompl.pow_mem hap k
  let Rₚ := Localization.AtPrime p.asIdeal
  let Mₚ := LocalizedModule p.asIdeal.primeCompl M
  let p' := Algebra.algebraMapSubmonoid (Localization.Away a) p.asIdeal.primeCompl
  let : Algebra (Localization.Away a) Rₚ :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers a)
      p.asIdeal.primeCompl hle
  have : IsScalarTower R (Localization.Away a) Rₚ :=
    IsLocalization.localization_isScalarTower_of_submonoid_le ..
  let : Module (Localization.Away a) Mₚ := Module.compHom Mₚ (algebraMap _ Rₚ)
  have hRM : IsScalarTower R Rₚ Mₚ := by infer_instance
  have : IsScalarTower R (Localization.Away a) Mₚ :=
    ⟨fun r r' m ↦ by
      change algebraMap (Localization.Away a) Rₚ (r • r') • m =
        r • (algebraMap (Localization.Away a) Rₚ r' • m)
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, mul_smul]
      simpa only [Algebra.smul_def, mul_smul] using
        hRM.smul_assoc r (algebraMap (Localization.Away a) Rₚ r') m⟩
  have : IsScalarTower (Localization.Away a) Rₚ Mₚ :=
    ⟨fun r r' m ↦ show (r • r') • m =
        algebraMap (Localization.Away a) Rₚ r • r' • m by
      rw [← mul_smul, ← Algebra.smul_def]⟩
  let l :=
    (IsLocalizedModule.liftOfLE _ _ hle
      (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)).extendScalarsOfIsLocalization
      (Submonoid.powers a) (Localization.Away a)
  have : IsLocalization p' Rₚ :=
    IsLocalization.isLocalization_of_submonoid_le (Localization.Away a) Rₚ _ _ hle
  have : IsLocalizedModule p.asIdeal.primeCompl (l.restrictScalars R) :=
    inferInstanceAs (IsLocalizedModule p.asIdeal.primeCompl
      (IsLocalizedModule.liftOfLE _ _ hle
        (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)))
  have : IsLocalizedModule p' l :=
    IsLocalizedModule.of_restrictScalars p.asIdeal.primeCompl ..
  letI : Module.Free (Localization.Away a) (LocalizedModule.Away a M) :=
    hfree a ha
  exact Module.free_of_isLocalizedModule p' l

private theorem subsingleton_away_mul
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {a b : R} (h : Subsingleton (LocalizedModule.Away a M)) :
    Subsingleton (LocalizedModule.Away (a * b) M) := by
  rw [subsingleton_iff_forall_eq 0]
  intro x
  obtain ⟨⟨m, s⟩, rfl⟩ :=
    IsLocalizedModule.mk'_surjective (Submonoid.powers (a * b))
      (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) M) x
  have hzero : IsLocalizedModule.mk' (LocalizedModule.mkLinearMap
      (Submonoid.powers a) M) m (1 : Submonoid.powers a) = 0 :=
    Subsingleton.elim _ _
  obtain ⟨k, hk⟩ :=
    (IsLocalizedModule.mk'_eq_zero' (LocalizedModule.mkLinearMap
      (Submonoid.powers a) M) (1 : Submonoid.powers a)).mp hzero
  rcases k with ⟨k, ⟨n, rfl⟩⟩
  apply (IsLocalizedModule.mk'_eq_zero' (LocalizedModule.mkLinearMap
    (Submonoid.powers (a * b)) M) s).mpr
  let t : Submonoid.powers (a * b) := ⟨(a * b) ^ n, ⟨n, rfl⟩⟩
  refine ⟨t, ?_⟩
  change (a * b) ^ n • m = 0
  change a ^ n • m = 0 at hk
  rw [mul_pow, mul_comm (a ^ n) (b ^ n), mul_smul, hk, smul_zero]

private theorem reduced_bijective_of_surjective_of_minimal_rank
    {R F N : Type*} [CommRing R] [IsReduced R]
    [AddCommGroup F] [Module R F] [Module.Finite R F] [Module.Free R F]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    {r : ℕ} (φ : F →ₗ[R] N) (hφ : Function.Surjective φ)
    (hF : Module.finrank R F = r)
    (hrank : ∀ (p : Ideal R) (hp : p ∈ minimalPrimes R),
      Module.rankAtStalk N ⟨p, hp.1.1⟩ = r) :
    Function.Bijective φ := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · letI := hR
    have hFsub : Subsingleton F := Module.subsingleton R F
    exact ⟨by
      intro x y _
      exact Subsingleton.elim _ _, hφ⟩
  · letI := hR
    have hφ_inj : Function.Injective φ := by
      let b := Module.finBasis R F
      intro x y hxy
      apply b.repr.injective
      ext i
      have hφxy : φ (x - y) = 0 := by
        rw [map_sub, hxy, sub_self]
      have hmem (p : Ideal R) (hp : p ∈ minimalPrimes R) :
          b.repr (x - y) i ∈ p := by
        letI : p.IsPrime := hp.1.1
        letI : Ring.KrullDimLE 0 (Localization.AtPrime p) :=
          Ring.KrullDimLE.of_isLocalization p hp (Localization.AtPrime p)
        let hfield : IsField (Localization.AtPrime p) :=
          Ring.KrullDimLE.isField_of_isReduced
        letI : IsField (Localization.AtPrime p) := hfield
        letI : Field (Localization.AtPrime p) :=
          hfield.toField
        letI : Module.Free (Localization.AtPrime p)
            (LocalizedModule p.primeCompl F) :=
          Module.free_of_isLocalizedModule p.primeCompl
            (LocalizedModule.mkLinearMap p.primeCompl F)
        letI : Module.Free (Localization.AtPrime p)
            (LocalizedModule p.primeCompl N) :=
          Module.Free.of_equiv'
            (inferInstance : Module.Free (Localization.AtPrime p)
              (Fin (Module.finrank (Localization.AtPrime p)
                (LocalizedModule p.primeCompl N)) →₀ Localization.AtPrime p))
            (Module.finBasis (Localization.AtPrime p)
              (LocalizedModule p.primeCompl N)).repr.symm
        have hFloc : Module.finrank (Localization.AtPrime p)
            (LocalizedModule p.primeCompl F) = Module.finrank R F :=
          Module.finrank_of_isLocalizedModule_of_free
            (M := F) (Mₛ := LocalizedModule p.primeCompl F)
            (Localization.AtPrime p) p.primeCompl
            (LocalizedModule.mkLinearMap p.primeCompl F)
        have hbij : Function.Bijective (LocalizedModule.map p.primeCompl φ) := by
          apply OrzechProperty.bijective_of_surjective_of_finrank_le
            (LocalizedModule.map p.primeCompl φ)
            (LocalizedModule.map_surjective p.primeCompl φ hφ)
          rw [hFloc, hF, ← hrank p hp]
          rfl
        have hzero : LocalizedModule.mkLinearMap p.primeCompl F (x - y) = 0 := by
          apply hbij.1
          simpa [hφxy]
        obtain ⟨s, hs⟩ :=
          (IsLocalizedModule.eq_zero_iff p.primeCompl
            (LocalizedModule.mkLinearMap p.primeCompl F)).mp hzero
        have hsrepr : (s : R) • b.repr (x - y) = 0 := by
          have hs' := congrArg b.repr hs
          change b.repr ((s : R) • (x - y)) = b.repr 0 at hs'
          simpa using hs'
        have hmul : (s : R) * b.repr (x - y) i = 0 := by
          simpa [smul_eq_mul] using congrArg (fun z ↦ z i) hsrepr
        have hcases : (s : R) ∈ p ∨ b.repr (x - y) i ∈ p :=
          Ideal.IsPrime.mem_or_mem (I := p) (hI := inferInstance)
            (x := (s : R))
            (y := b.repr (x - y) i) (by rw [hmul]; exact p.zero_mem)
        rcases hcases with hs' | hi
        · exact (s.property hs').elim
        · exact hi
      have hrad : b.repr (x - y) i ∈ (⊥ : Ideal R).radical := by
        rw [← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
        intro p hp
        exact hmem p hp
      have hradbot : (⊥ : Ideal R).radical = ⊥ :=
        (Ideal.isRadical_bot (R := R)).radical
      exact sub_eq_zero.mp (by simpa [hradbot] using hrad)
    exact ⟨hφ_inj, hφ⟩

private theorem rankAtStalk_eq_fiber_finrank_of_minimal
    {R M : Type*} [CommRing R] [IsReduced R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ minimalPrimes R) :
    Module.rankAtStalk M p =
      Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M) := by
  letI : p.asIdeal.IsPrime := p.isPrime
  let S := Localization.AtPrime p.asIdeal
  let N := LocalizedModule.AtPrime p.asIdeal M
  letI : Ring.KrullDimLE 0 S :=
    Ring.KrullDimLE.of_isLocalization p.asIdeal hp S
  have hfield : IsField S := Ring.KrullDimLE.isField_of_isReduced
  letI : Field S := hfield.toField
  let K := p.asIdeal.ResidueField
  have hK : IsField K := Field.toIsField K
  letI : Field K := hK.toField
  have hdim : Module.finrank K (K ⊗[S] N) =
      Module.finrank K (K ⊗[R] M) := by
    let e₁ := (LinearEquiv.lTensor K
      (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl M)).extendScalarsOfSurjective
        IsLocalRing.residue_surjective
    let e₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange
      R S K K M
    exact (e₁.trans e₂).finrank_eq
  change Module.finrank S N = Module.finrank K (K ⊗[R] M)
  calc
    Module.finrank S N = Module.finrank K (K ⊗[S] N) :=
      Module.finrank_baseChange.symm
    _ = Module.finrank K (K ⊗[R] M) := hdim

/- A direct summand of a finite free module is represented using the canonical
finite free module `Fin n →₀ R` and a retraction. -/

/-- `M` is a direct summand of a finite free `R`-module. -/
def FiniteFreeSummand
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  ∃ n : ℕ, ∃ i : M →ₗ[R] (Fin n →₀ R),
    ∃ p : (Fin n →₀ R) →ₗ[R] M,
      p.comp i = LinearMap.id

/-- The source's fiber-dimension function `ρ_M`. -/
noncomputable def rankFunction
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] :
    PrimeSpectrum R → ℤ :=
  fun p => Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M)

/-- The rank function is the fiber dimension from the source. -/
theorem rankFunction_eq_fiber_finrank
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (p : PrimeSpectrum R) :
    rankFunction R M p =
      (Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M) : ℤ) := by
  rfl

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
  change List.TFAE [
    Module.FinitePresentation R M ∧ Module.Flat R M,
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
        IsLocallyConstant (rankFunction R M)]
  tfae_have 1 ↔ 2 := by
    constructor
    · rintro ⟨hfp, hflat⟩
      letI := hfp
      letI := hflat
      exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩
    · rintro ⟨hfin, hproj⟩
      letI := hfin
      letI := hproj
      exact ⟨Module.finitePresentation_of_projective R M, inferInstance⟩
  tfae_have 2 ↔ 3 := by
    constructor
    · rintro ⟨hfin, hproj⟩
      letI := hfin
      letI := hproj
      obtain ⟨n, f, g, hsurj, _, hfg⟩ :=
        Module.Finite.exists_comp_eq_id_of_projective R M
      let e := Finsupp.linearEquivFunOnFinite R R (Fin n)
      refine ⟨n, e.symm.toLinearMap.comp g, f.comp e.toLinearMap, ?_⟩
      apply LinearMap.ext
      intro x
      simpa [LinearMap.comp_apply] using LinearMap.congr_fun hfg x
    · rintro ⟨n, i, p, hpi⟩
      letI : Module.Finite R (Fin n →₀ R) := inferInstance
      have hpsurj : Function.Surjective p := by
        intro x
        refine ⟨i x, ?_⟩
        simpa [LinearMap.comp_apply] using LinearMap.congr_fun hpi x
      exact ⟨Module.Finite.of_surjective p hpsurj, Module.Projective.of_split i p hpi⟩
  tfae_have 2 ↔ 4 := by
    constructor
    · rintro ⟨hfin, hproj⟩
      letI := hfin
      letI := hproj
      letI : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
      refine ⟨inferInstance, ?_⟩
      rw [← Set.eq_univ_iff_forall]
      exact Module.freeLocus_eq_univ_iff.mpr hproj
    · rintro ⟨hfp, hall⟩
      letI := hfp
      have hproj : Module.Projective R M := by
        apply Module.freeLocus_eq_univ_iff.mp
        rw [Set.eq_univ_iff_forall]
        exact hall
      exact ⟨inferInstance, hproj⟩
  tfae_have 2 ↔ 5 := by
    constructor
    · rintro ⟨hfin, hproj⟩
      letI := hfin
      letI := hproj
      letI : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
      refine ⟨inferInstance, ?_⟩
      intro m
      exact Module.mem_freeLocus.mp <|
        (Module.freeLocus_eq_univ_iff.mpr hproj) ▸ Set.mem_univ
          (⟨m.asIdeal, m.isMaximal.isPrime⟩ : PrimeSpectrum R)
    · rintro ⟨hfp, hall⟩
      letI := hfp
      have hproj : Module.Projective R M :=
        Module.projective_of_localization_maximal (fun I hI ↦ by
          let m : MaximalSpectrum R := ⟨I, hI⟩
          letI := hall m
          exact Module.Projective.of_free)
      exact ⟨inferInstance, hproj⟩
  tfae_have 6 ↔ 7 := by
    constructor
    · rintro ⟨hfin, ⟨s, hs, hfree⟩⟩
      letI := hfin
      refine ⟨s, hs, ?_⟩
      intro f hf
      exact ⟨inferInstance, hfree f hf⟩
    · rintro ⟨s, hs, hfree⟩
      have hfin : Module.Finite R M :=
        Module.Finite.of_localizationSpan s hs (fun f ↦ (hfree f f.property).1)
      refine ⟨hfin, ⟨s, hs, ?_⟩⟩
      intro f hf
      exact (hfree f hf).2
  tfae_have 2 ↔ 7 := by
    constructor
    · exact finiteLocallyFree_of_finiteProjective
    · intro h
      have hfp := finitePresentation_of_finiteLocallyFree h
      letI := hfp
      obtain ⟨s, hs, hfree⟩ := h
      let hloc : LocallyFree R M := ⟨s, hs, fun f hf ↦ (hfree f hf).2⟩
      have hproj : Module.Projective R M :=
        Module.projective_of_localization_maximal (fun I hI ↦ by
          let p : PrimeSpectrum R := ⟨I, hI.isPrime⟩
          letI := free_at_prime_of_locallyFree hloc p
          exact Module.Projective.of_free)
      exact ⟨inferInstance, hproj⟩
  tfae_have 2 → 8 := by
    rintro ⟨hfin, hproj⟩
    letI := hfin
    letI := hproj
    letI : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
    obtain ⟨s, hs, hfree⟩ := finiteLocallyFree_of_finiteProjective ⟨hfin, hproj⟩
    let hloc : LocallyFree R M := ⟨s, hs, fun f hf ↦ (hfree f hf).2⟩
    have hfree : ∀ p : PrimeSpectrum R, p ∈ Module.freeLocus R M := by
      intro p
      exact Module.mem_freeLocus.mpr <| free_at_prime_of_locallyFree hloc p
    have hlocRank : IsLocallyConstant (rankFunction R M) := by
      have hstalk : IsLocallyConstant (fun p : PrimeSpectrum R =>
          (Module.rankAtStalk M p : ℤ)) := by
        simpa [Function.comp_def] using
          (Module.isLocallyConstant_rankAtStalk (R := R) (M := M)).comp
            (fun n : ℕ => (n : ℤ))
      have heq : rankFunction R M = fun p : PrimeSpectrum R =>
          (Module.rankAtStalk M p : ℤ) := by
        funext p
        simp [rankFunction, Ideal.finrank_fiber_eq_rankAtStalk]
      rw [heq]
      exact hstalk
    exact ⟨hfin, hfree, hlocRank⟩
  tfae_have 8 → 2 := by
    rintro ⟨hfin, hfree, hloc⟩
    letI := hfin
    have hflat : Module.Flat R M := Module.flat_of_localized_maximal M (fun I hI ↦ by
      let p : PrimeSpectrum R := ⟨I, hI.isPrime⟩
      letI := Module.mem_freeLocus.mp (hfree p)
      rw [← Module.flat_iff_of_isLocalization (Localization.AtPrime I) I.primeCompl]
      exact Module.Flat.of_free)
    letI := hflat
    have hflf : FiniteLocallyFree R M := by
      let s : Set R :=
        {f | Module.Free (Localization.Away f) (LocalizedModule.Away f M)}
      have hs : Ideal.span s = ⊤ := by
        by_contra hst
        obtain ⟨I, hI, hIs⟩ := Ideal.ne_top_iff_exists_maximal.mp hst
        let p : PrimeSpectrum R := ⟨I, hI.isPrime⟩
        obtain ⟨U, hU, hpU, hconst⟩ := IsLocallyConstant.exists_open hloc p
        obtain ⟨t, ⟨a, rfl⟩, hpa, hta⟩ :=
          PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp hU p hpU
        have haI : a ∉ I := hpa
        let n := Module.rankAtStalk M p
        let f : (Fin n →₀ R) →ₗ[R] Fin n →₀ Localization.AtPrime I :=
          Finsupp.mapRange.linearMap (Algebra.linearMap R (Localization.AtPrime I))
        let g : M →ₗ[R] LocalizedModule.AtPrime I M :=
          LocalizedModule.mkLinearMap I.primeCompl M
        letI : Module.Free (Localization.AtPrime I)
            (LocalizedModule.AtPrime I M) := Module.mem_freeLocus.mp (hfree p)
        obtain ⟨φ, -, -, hφps⟩ :=
          Module.exists_localizedMap_surjective_of_surjective I.primeCompl f g
            ((Module.finBasis (Localization.AtPrime I)
              (LocalizedModule.AtPrime I M)).repr.restrictScalars R).symm.surjective
        obtain ⟨b, hbI, hφbs⟩ :=
          Module.exists_localizedMap_away_surjective_of_localizedMap_atPrime_surjective
            I φ (by simpa [LocalizedModule.coe_map_eq f g])
        let c := a * b
        have hφcs : Function.Surjective (LocalizedModule.map
            (Submonoid.powers c) φ) := by
          apply (LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker
            (Submonoid.powers c) φ).mpr
          simpa [mul_comm] using subsingleton_away_mul (a := b) (b := a)
            ((LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker
              (Submonoid.powers b) φ).mp hφbs)
        have hcr : c ∉ I := by
          intro hc
          exact hI.isPrime.mul_notMem haI hbI hc
        have hrank : ∀ q : PrimeSpectrum R, q ∈ PrimeSpectrum.basicOpen c →
            Module.rankAtStalk M q = n := by
          intro q hq
          have hqa : q ∈ PrimeSpectrum.basicOpen a :=
            PrimeSpectrum.basicOpen_mul_le_left a b hq
          have heq : rankFunction R M q = rankFunction R M p :=
            hconst q (hta hqa)
          have heq' : (Module.rankAtStalk M q : ℤ) =
              (Module.rankAtStalk M p : ℤ) := by
            simpa [rankFunction, Ideal.finrank_fiber_eq_rankAtStalk] using heq
          exact_mod_cast heq'
        letI : Module.Flat (Localization.Away c)
            (LocalizedModule.Away c M) := inferInstance
        letI : Module.Free (Localization.Away c)
            (LocalizedModule.Away c (Fin n →₀ R)) :=
          Module.free_of_isLocalizedModule (R := R) (M := Fin n →₀ R)
            (Rₛ := Localization.Away c)
            (Mₛ := LocalizedModule.Away c (Fin n →₀ R))
            (Submonoid.powers c)
            (LocalizedModule.mkLinearMap (Submonoid.powers c) (Fin n →₀ R))
        let φc : LocalizedModule.Away c (Fin n →₀ R) →ₗ[Localization.Away c]
            LocalizedModule.Away c M := LocalizedModule.map (Submonoid.powers c) φ
        have hφcb : Function.Bijective φc := by
          apply Module.bijective_of_surjective_of_rankAtStalk_eq hφcs
          intro J hJ
          let S := Localization.Away c
          let q : PrimeSpectrum R :=
            PrimeSpectrum.comap (algebraMap R S) ⟨J, hJ.isPrime⟩
          have hqc : q ∈ PrimeSpectrum.basicOpen c := by
            rw [PrimeSpectrum.mem_basicOpen]
            intro hc
            apply hJ.ne_top
            change algebraMap R S c ∈ J at hc
            exact Ideal.eq_top_of_isUnit_mem J hc
              (IsLocalization.map_units S ⟨c, Submonoid.mem_powers c⟩)
          have hsource : Module.rankAtStalk
              (LocalizedModule.Away c (Fin n →₀ R))
              (⟨J, hJ.isPrime⟩ : PrimeSpectrum (Localization.Away c)) =
              n := by
            have hRnontrivial : Nontrivial R := by
              rw [← not_subsingleton_iff_nontrivial]
              intro hsub
              letI := hsub
              exact hI.ne_top (Subsingleton.elim I ⊤)
            letI := hRnontrivial
            have hnontrivial : Nontrivial (Localization.Away c) := by
              rw [← not_subsingleton_iff_nontrivial]
              intro hsub
              letI := hsub
              exact hJ.ne_top (Subsingleton.elim J ⊤)
            letI := hnontrivial
            calc
              Module.rankAtStalk (LocalizedModule.Away c (Fin n →₀ R))
                  (⟨J, hJ.isPrime⟩ : PrimeSpectrum (Localization.Away c)) =
                  Module.finrank (Localization.Away c)
                    (LocalizedModule.Away c (Fin n →₀ R)) := by
                exact congrFun (Module.rankAtStalk_eq_finrank_of_free
                  (R := Localization.Away c)
                  (M := LocalizedModule.Away c (Fin n →₀ R)))
                  (⟨J, hJ.isPrime⟩ : PrimeSpectrum (Localization.Away c))
              _ = Module.finrank R (Fin n →₀ R) :=
                Module.finrank_of_isLocalizedModule_of_free
                  (M := Fin n →₀ R) (Mₛ := LocalizedModule.Away c (Fin n →₀ R))
                  (Localization.Away c) (Submonoid.powers c)
                  (LocalizedModule.mkLinearMap (Submonoid.powers c) (Fin n →₀ R))
              _ = n := by
                rw [Module.finrank_finsupp_self, Fintype.card_fin]
          have htarget : Module.rankAtStalk
              (LocalizedModule.Away c M)
              (⟨J, hJ.isPrime⟩ : PrimeSpectrum (Localization.Away c)) =
              Module.rankAtStalk M q := by
            have h := Module.rankAtStalk_isBaseChange
              (R := R) (M := M) (S := Localization.Away c)
              (Mₛ := LocalizedModule.Away c M)
              (f := LocalizedModule.mkLinearMap (Submonoid.powers c) M)
              (LocalizedModule.isBaseChange (Submonoid.powers c) M)
              (⟨J, hJ.isPrime⟩ : PrimeSpectrum (Localization.Away c))
            simpa [q, S] using h
          calc
            Module.rankAtStalk (LocalizedModule.Away c (Fin n →₀ R))
                ⟨J, hJ.isPrime⟩ = n := hsource
            _ = Module.rankAtStalk M q := (hrank q hqc).symm
            _ = Module.rankAtStalk (LocalizedModule.Away c M)
                ⟨J, hJ.isPrime⟩ := htarget.symm
        have hfreec : Module.Free (Localization.Away c)
            (LocalizedModule.Away c M) := Module.Free.of_equiv
              (LinearEquiv.ofBijective φc hφcb)
        exact hcr (hIs (Ideal.subset_span hfreec))
      refine ⟨s, hs, ?_⟩
      intro f hf
      exact ⟨by infer_instance, hf⟩
    exact tfae_2_iff_7.mpr hflf
  tfae_finish

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
  change List.TFAE [
    Module.FinitePresentation R M ∧ Module.Flat R M,
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
        IsLocallyConstant (rankFunction R M),
    FiniteLocallyConstantRank R M]
  have hchar := finite_projective_characterization (R := R) (M := M)
  tfae_have 1 ↔ 2 := hchar.out 0 1
  tfae_have 2 ↔ 3 := hchar.out 1 2
  tfae_have 2 ↔ 4 := hchar.out 1 3
  tfae_have 2 ↔ 5 := hchar.out 1 4
  tfae_have 2 ↔ 6 := hchar.out 1 5
  tfae_have 2 ↔ 7 := hchar.out 1 6
  tfae_have 2 ↔ 8 := hchar.out 1 7
  tfae_have 2 ↔ 9 := by
    constructor
    · rintro ⟨hfin, hproj⟩
      letI := hfin
      letI := hproj
      letI : Module.FinitePresentation R M :=
        Module.finitePresentation_of_projective R M
      have hstalk : IsLocallyConstant (fun p : PrimeSpectrum R =>
          (Module.rankAtStalk M p : ℤ)) := by
        simpa [Function.comp_def] using
          (Module.isLocallyConstant_rankAtStalk (R := R) (M := M)).comp
            (fun n : ℕ => (n : ℤ))
      have heq : rankFunction R M = fun p : PrimeSpectrum R =>
          (Module.rankAtStalk M p : ℤ) := by
        funext p
        simp [rankFunction, Ideal.finrank_fiber_eq_rankAtStalk]
      exact ⟨hfin, by rw [heq]; exact hstalk⟩
    · rintro ⟨hfin, hloc⟩
      letI := hfin
      have hflf : FiniteLocallyFree R M := by
        let s : Set R :=
          {f | Module.Free (Localization.Away f)
            (LocalizedModule.Away f M)}
        have hs : Ideal.span s = ⊤ := by
          by_contra hst
          obtain ⟨I, hI, hIs⟩ := Ideal.ne_top_iff_exists_maximal.mp hst
          let p : PrimeSpectrum R := ⟨I, hI.isPrime⟩
          obtain ⟨U, hU, hpU, hconst⟩ := IsLocallyConstant.exists_open hloc p
          obtain ⟨t, ⟨a, rfl⟩, hpa, hta⟩ :=
            PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp hU p hpU
          have haI : a ∉ I := hpa
          let S := Localization.AtPrime I
          let N := LocalizedModule.AtPrime I M
          let K := IsLocalRing.ResidueField S
          have hK : IsField K := Field.toIsField K
          letI : Field K := hK.toField
          have hdim : Module.finrank K (K ⊗[S] N) =
              Module.finrank K (K ⊗[R] M) := by
            let e₁ := (LinearEquiv.lTensor K
              (LocalizedModule.equivTensorProduct I.primeCompl M)).extendScalarsOfSurjective
                IsLocalRing.residue_surjective
            let e₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange
              R S K K M
            exact (e₁.trans e₂).finrank_eq
          let r := Module.finrank K (K ⊗[S] N)
          let b := Module.finBasis K (K ⊗[S] N)
          have hmk : Function.Surjective (TensorProduct.mk S K N 1) :=
            TensorProduct.mk_surjective S N K IsLocalRing.residue_surjective
          choose v hv using fun i : Fin r => hmk (b i)
          have hspan : Submodule.span S (Set.range v) = ⊤ :=
            IsLocalRing.span_eq_top_of_tmul_eq_basis v b (by
              intro i
              simpa using hv i)
          let ψp : (Fin r →₀ S) →ₗ[S] N :=
            Finsupp.linearCombination S v
          have hψps : Function.Surjective ψp := by
            rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
            exact hspan
          let f : (Fin r →₀ R) →ₗ[R] Fin r →₀ S :=
            Finsupp.mapRange.linearMap (Algebra.linearMap R S)
          let g : M →ₗ[R] N := LocalizedModule.mkLinearMap I.primeCompl M
          have hψpsR : Function.Surjective (ψp.restrictScalars R) := hψps
          obtain ⟨φ, -, -, hφps⟩ :=
            Module.exists_localizedMap_surjective_of_surjective I.primeCompl f g hψpsR
          obtain ⟨b', hbI, hφbs⟩ :=
            Module.exists_localizedMap_away_surjective_of_localizedMap_atPrime_surjective
              I φ (by simpa [LocalizedModule.coe_map_eq f g])
          let c := a * b'
          have hφcs : Function.Surjective (LocalizedModule.map
              (Submonoid.powers c) φ) := by
            apply (LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker
              (Submonoid.powers c) φ).mpr
            simpa [mul_comm] using subsingleton_away_mul (a := b') (b := a)
              ((LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker
                (Submonoid.powers b') φ).mp hφbs)
          have hcr : c ∉ I := by
            intro hc
            exact hI.isPrime.mul_notMem haI hbI hc
          have hprank : rankFunction R M p = (r : ℤ) := by
            rw [rankFunction_eq_fiber_finrank p]
            have hnat : Module.finrank p.asIdeal.ResidueField
                (p.asIdeal.Fiber M) = r := by
              simpa [p, r, S, N, K] using hdim.symm
            rw [hnat]
          have hfiber : ∀ q : PrimeSpectrum R,
              q ∈ PrimeSpectrum.basicOpen c →
                (Module.finrank q.asIdeal.ResidueField
                  (q.asIdeal.Fiber M) : ℤ) = (r : ℤ) := by
            intro q hq
            have hqa : q ∈ PrimeSpectrum.basicOpen a :=
              PrimeSpectrum.basicOpen_mul_le_left a b' hq
            have heq : rankFunction R M q = rankFunction R M p :=
              hconst q (hta hqa)
            simpa [rankFunction, hprank] using heq.trans hprank
          letI : Module.Free (Localization.Away c)
              (LocalizedModule.Away c (Fin r →₀ R)) :=
            Module.free_of_isLocalizedModule (R := R) (M := Fin r →₀ R)
              (Rₛ := Localization.Away c)
              (Mₛ := LocalizedModule.Away c (Fin r →₀ R))
              (Submonoid.powers c)
              (LocalizedModule.mkLinearMap (Submonoid.powers c) (Fin r →₀ R))
          have hsource : Module.finrank (Localization.Away c)
              (LocalizedModule.Away c (Fin r →₀ R)) = r := by
            have hRnontrivial : Nontrivial R := by
              rw [← not_subsingleton_iff_nontrivial]
              intro hsub
              letI := hsub
              exact hI.ne_top (Subsingleton.elim I ⊤)
            letI := hRnontrivial
            letI : Nontrivial (Localization.Away c) :=
              (IsLocalization.toLocalizationMap (Submonoid.powers c)
                (Localization.Away c)).nontrivial (by
                rintro ⟨k, hk⟩
                exact (I.primeCompl.pow_mem hcr k) (by
                  change c ^ k = 0 at hk
                  rw [hk]
                  exact I.zero_mem))
            calc
              Module.finrank (Localization.Away c)
                  (LocalizedModule.Away c (Fin r →₀ R)) =
                  Module.finrank R (Fin r →₀ R) :=
                Module.finrank_of_isLocalizedModule_of_free
                  (M := Fin r →₀ R)
                  (Mₛ := LocalizedModule.Away c (Fin r →₀ R))
                  (Localization.Away c) (Submonoid.powers c)
                  (LocalizedModule.mkLinearMap (Submonoid.powers c)
                    (Fin r →₀ R))
              _ = r := by
                rw [Module.finrank_finsupp_self, Fintype.card_fin]
          have hrankmin : ∀ (J : Ideal (Localization.Away c))
              (hJ : J ∈ minimalPrimes (Localization.Away c)),
                Module.rankAtStalk (LocalizedModule.Away c M)
                  ⟨J, hJ.1.1⟩ = r := by
            intro J hJ
            let S' := Localization.Away c
            let q : PrimeSpectrum R :=
              PrimeSpectrum.comap (algebraMap R S') ⟨J, hJ.isPrime⟩
            have hqc : q ∈ PrimeSpectrum.basicOpen c := by
              rw [PrimeSpectrum.mem_basicOpen]
              intro hc
              apply hJ.1.1.ne_top
              change algebraMap R S' c ∈ J at hc
              exact Ideal.eq_top_of_isUnit_mem J hc
                (IsLocalization.map_units S' ⟨c, Submonoid.mem_powers c⟩)
            have hqmin : q.asIdeal ∈ minimalPrimes R := by
              have hm := IsLocalization.minimalPrimes_map
                (Submonoid.powers c) (Localization.Away c) (⊥ : Ideal R)
              change J ∈ Ideal.under R ⁻¹' minimalPrimes R
              rw [← hm]
              simpa using hJ
            have htarget : Module.rankAtStalk
                (LocalizedModule.Away c M)
                (⟨J, hJ.isPrime⟩ : PrimeSpectrum (Localization.Away c)) =
                Module.rankAtStalk M q := by
              letI : J.IsPrime := hJ.1.1
              have hb := LocalizedModule.isBaseChange (Submonoid.powers c) M
              let qk := q.asIdeal.ResidueField
              let Jk := J.ResidueField
              let e : qk →ₐ[R] Jk :=
                Ideal.ResidueField.mapₐ q.asIdeal J (Algebra.ofId R S') rfl
              letI : Algebra qk Jk := e.toRingHom.toAlgebra
              letI : IsScalarTower R qk Jk :=
                IsScalarTower.of_algebraMap_eq' e.comp_algebraMap.symm
              have hdim : Module.finrank Jk (Jk ⊗[qk] (qk ⊗[R] M)) =
                  Module.finrank qk (qk ⊗[R] M) := Module.finrank_baseChange
              let e₁₀ := LinearEquiv.lTensor Jk hb.equiv
              let e₁ : Jk ⊗[Localization (Submonoid.powers c)]
                    (Localization (Submonoid.powers c) ⊗[R] M) ≃ₗ[Jk]
                  Jk ⊗[Localization (Submonoid.powers c)]
                    (LocalizedModule (Submonoid.powers c) M) :=
                { e₁₀ with
                  map_smul' := by
                    intro s x
                    induction x using TensorProduct.induction_on with
                    | zero => simp
                    | tmul x y =>
                      change (s • x) ⊗ₜ[Localization (Submonoid.powers c)]
                          hb.equiv y = s • (x ⊗ₜ[Localization (Submonoid.powers c)] hb.equiv y)
                      rfl
                    | add x y hx hy =>
                      rw [smul_add]
                      change e₁₀ (s • x + s • y) = s • e₁₀ (x + y)
                      have hx' : e₁₀ (s • x) = s • e₁₀ x := by simpa using hx
                      have hy' : e₁₀ (s • y) = s • e₁₀ y := by simpa using hy
                      rw [map_add e₁₀, hx', hy', map_add e₁₀, smul_add] }
              let e₁' := e₁.symm.trans
                (TensorProduct.AlgebraTensorModule.cancelBaseChange
                  R S' Jk Jk M)
              let e₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange
                R qk Jk Jk M
              have hdim' : Module.finrank Jk (Jk ⊗[R] M) =
                  Module.finrank qk (qk ⊗[R] M) :=
                e₂.finrank_eq.symm.trans hdim
              rw [rankAtStalk_eq_fiber_finrank_of_minimal
                (M := LocalizedModule.Away c M)
                (⟨J, hJ.isPrime⟩ : PrimeSpectrum (Localization.Away c)) hJ,
                rankAtStalk_eq_fiber_finrank_of_minimal q hqmin]
              change Module.finrank Jk (Jk ⊗[S'] (LocalizedModule.Away c M)) =
                Module.finrank qk (qk ⊗[R] M)
              exact e₁'.finrank_eq.trans hdim'
            have hqrank : Module.rankAtStalk M q = r := by
              rw [rankAtStalk_eq_fiber_finrank_of_minimal q hqmin]
              exact_mod_cast hfiber q hqc
            exact htarget.symm ▸ hqrank
          let φc : LocalizedModule.Away c (Fin r →₀ R) →ₗ[Localization.Away c]
              LocalizedModule.Away c M :=
            LocalizedModule.map (Submonoid.powers c) φ
          have hφcb : Function.Bijective φc := by
            apply reduced_bijective_of_surjective_of_minimal_rank
              (R := Localization.Away c)
              (F := LocalizedModule.Away c (Fin r →₀ R))
              (N := LocalizedModule.Away c M) (r := r) φc hφcs hsource
            exact hrankmin
          have hfreec : Module.Free (Localization.Away c)
              (LocalizedModule.Away c M) := Module.Free.of_equiv
                (LinearEquiv.ofBijective φc hφcb)
          exact hcr (hIs (Ideal.subset_span hfreec))
        refine ⟨s, hs, ?_⟩
        intro f hf
        exact ⟨by infer_instance, hf⟩
      have hfp := finitePresentation_of_finiteLocallyFree hflf
      letI := hfp
      obtain ⟨s, hs, hfree⟩ := hflf
      let hloc : LocallyFree R M :=
        ⟨s, hs, fun f hf ↦ (hfree f hf).2⟩
      have hproj : Module.Projective R M :=
        Module.projective_of_localization_maximal (fun I hI ↦ by
          let p : PrimeSpectrum R := ⟨I, hI.isPrime⟩
          letI := free_at_prime_of_locallyFree hloc p
          exact Module.Projective.of_free)
      exact ⟨inferInstance, hproj⟩
  tfae_finish

/-- The property exhibited by the warning's finite flat non-projective example. -/
def IsFiniteFlatNotProjective
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  Module.Finite R M ∧ Module.Flat R M ∧ ¬ Module.Projective R M

private def finiteSupportIdeal78 : Ideal (ℕ → ZMod 2) where
  carrier := {x | (Function.support x).Finite}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    apply (hx.union hy).subset
    intro n hn
    by_contra hzero
    have hxzero : x n = 0 := by
      by_contra hxzero
      exact hzero (Or.inl hxzero)
    have hyzero : y n = 0 := by
      by_contra hyzero
      exact hzero (Or.inr hyzero)
    simp [hxzero, hyzero] at hn
  smul_mem' := by
    intro r x hx
    exact hx.subset (Function.support_smul_subset_right r x)

private lemma product_zmodTwo_idempotent78 (x : ℕ → ZMod 2) :
    IsIdempotentElem x := by
  funext n
  let i : Fin 2 := (ZMod.finEquiv 2).symm (x n)
  have hi : ZMod.finEquiv 2 i = x n :=
    (ZMod.finEquiv 2).apply_symm_apply _
  change x n * x n = x n
  rw [← hi]
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with h | h
  · rw [h]
    simp
  · rw [h]
    simp

private lemma finiteSupportIdeal78_pure :
    Ideal.Pure (finiteSupportIdeal78 : Ideal (ℕ → ZMod 2)) := by
  apply Ideal.Pure.of_inf_eq_mul
  intro J hJ
  have hJid : IsIdempotentElem J := by
    rw [IsIdempotentElem]
    apply le_antisymm
    · exact Ideal.mul_le.mpr fun x hx y hy => J.mul_mem_left x hy
    · intro x hx
      convert Ideal.mul_mem_mul hx hx using 1
      exact (product_zmodTwo_idempotent78 x).eq.symm
  obtain ⟨e, he, hJe⟩ := (J.isIdempotentElem_iff_of_fg hJ).mp hJid
  subst J
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hx.2
    have hxe : x * e = x := by
      rw [← ha, mul_assoc, he.eq]
    rw [← hxe]
    exact Ideal.mul_mem_mul hx.1 (Ideal.subset_span (by simp))
  · refine Ideal.mul_le.mpr ?_
    intro x hx y hy
    refine ⟨finiteSupportIdeal78.mul_mem_right y hx, ?_⟩
    obtain ⟨a, ha⟩ := (Submodule.mem_span_singleton).mp hy
    rw [← ha]
    simpa [smul_eq_mul, mul_assoc] using
      (Submodule.smul_mem (R := ℕ → ZMod 2) (M := ℕ → ZMod 2)
        ((ℕ → ZMod 2) ∙ e) (x * a)
        (Submodule.subset_span (show e ∈ ({e} : Set (ℕ → ZMod 2)) by simp)))

private lemma finiteSupportIdeal78_not_fg :
    ¬ (finiteSupportIdeal78 : Ideal (ℕ → ZMod 2)).FG := by
  intro hI
  obtain ⟨s, hs⟩ := hI
  have hsI : ∀ x ∈ s, x ∈ (finiteSupportIdeal78 : Ideal (ℕ → ZMod 2)) := by
    intro x hx
    rw [← hs]
    exact Ideal.subset_span hx
  let T : Set ℕ :=
    ⋃ x ∈ (s : Set (ℕ → ZMod 2)), Function.support x
  have hT : T.Finite := by
    dsimp [T]
    apply Set.Finite.biUnion s.finite_toSet
    intro x hx
    exact hsI x hx
  obtain ⟨m, hm⟩ := hT.exists_notMem
  let d : ℕ → ZMod 2 := fun i => if i = m then 1 else 0
  have hd : d ∈ (finiteSupportIdeal78 : Ideal (ℕ → ZMod 2)) := by
    apply Set.Finite.subset (Set.finite_singleton m)
    intro i hi
    have hi' : i = m := by
      simpa [d, Function.mem_support] using hi
    exact Set.mem_singleton_iff.mpr hi'
  have hds : d ∈ Ideal.span (s : Set (ℕ → ZMod 2)) := by
    rw [hs]
    exact hd
  have hs0 : ∀ x ∈ s, x m = 0 := by
    intro x hx
    by_contra hzero
    apply hm
    exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, hzero⟩⟩
  let ev : (ℕ → ZMod 2) →+* ZMod 2 :=
    Pi.evalRingHom (fun _ : ℕ => ZMod 2) m
  have hker : Ideal.span (s : Set (ℕ → ZMod 2)) ≤ RingHom.ker ev := by
    rw [Ideal.span_le]
    intro x hx
    exact RingHom.mem_ker.mpr (hs0 x hx)
  have hz : ev d = 0 := RingHom.mem_ker.mp (hker hds)
  have hone : ev d = 1 := by
    simp [ev, d]
  rw [hone] at hz
  exact one_ne_zero hz

private lemma finiteSupportQuotient78_not_projective :
    ¬ Module.Projective (ℕ → ZMod 2)
      ((ℕ → ZMod 2) ⧸ finiteSupportIdeal78) := by
  intro hprojective
  let R := ℕ → ZMod 2
  let I : Ideal R := finiteSupportIdeal78
  let q : R →ₗ[R] (R ⧸ I) := I.mkQ
  obtain ⟨sec, hsection⟩ :=
    (Module.Projective.iff_split_of_projective q Ideal.Quotient.mk_surjective).mp
      hprojective
  let retraction : R →ₗ[R] I :=
    { toFun := fun x => ⟨x - sec (q x), by
        apply (Ideal.Quotient.eq_zero_iff_mem).mp
        change q (x - sec (q x)) = 0
        rw [map_sub]
        have hqsec : q (sec (q x)) = q x := by
          have h := LinearMap.congr_fun hsection (q x)
          simpa [LinearMap.comp_apply] using h
        rw [hqsec, sub_self]
        ⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        dsimp
        rw [map_add, map_add]
        ring
      map_smul' := by
        intro r x
        apply Subtype.ext
        dsimp
        change r • x - sec (q (r • x)) = r • (x - sec (q x))
        rw [map_smul, map_smul]
        rw [smul_sub] }
  have hretraction_surjective : Function.Surjective retraction := by
    intro x
    refine ⟨(x : R), ?_⟩
    apply Subtype.ext
    dsimp [retraction]
    have hqx : q (x : R) = 0 := by
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr x.property
    rw [hqx, map_zero, sub_zero]
  have hfinite : Module.Finite R I :=
    Module.Finite.of_surjective retraction hretraction_surjective
  exact finiteSupportIdeal78_not_fg (Module.Finite.iff_fg.mp hfinite)

/- The source gives the concrete example `C^∞(ℝ)` and its local quotient.  The
abstract existence statement records the mathematical warning without adding a
non-canonical smooth-function-ring model to this algebra chapter. -/

/-- Finite flat modules need not be projective. -/
theorem exists_finite_flat_not_projective :
    ∃ (R : Type u) (_ : CommRing R) (M : Type v)
      (_ : AddCommGroup M) (_ : Module R M),
      IsFiniteFlatNotProjective R M := by
  let R₀ := ℕ → ZMod 2
  let I₀ : Ideal R₀ := finiteSupportIdeal78
  let M₀ := R₀ ⧸ I₀
  let R := ULift.{u} R₀
  let M := ULift.{v} M₀
  have hflat₀ : Module.Flat R₀ M₀ := finiteSupportIdeal78_pure
  have hflat₁ : Module.Flat R M₀ := by
    rw [Module.Flat.ulift_left_iff]
    exact hflat₀
  have hflat : Module.Flat R M := by
    rw [Module.Flat.ulift_right_iff]
    exact hflat₁
  have hfinite₁ : Module.Finite R M₀ :=
    Module.Finite.of_restrictScalars_finite R₀ R M₀
  letI : Module.Finite R M₀ := hfinite₁
  have hfinite : Module.Finite R M := inferInstance
  have hnot : ¬ Module.Projective R M := by
    intro hprojective
    letI : Module.Projective R M := hprojective
    letI : Module.Projective R M₀ :=
      Module.Projective.of_equiv' (ULift.moduleEquiv (R := R) (M := M₀))
    let σ : R →+* R₀ := ULift.ringEquiv
    let σ' : R₀ →+* R := ULift.ringEquiv.symm
    letI : RingHomInvPair σ σ' := RingHomInvPair.of_ringEquiv ULift.ringEquiv
    letI : RingHomInvPair σ' σ :=
      RingHomInvPair.symm σ σ'
    let e : M₀ ≃ₛₗ[σ] M₀ :=
      { Equiv.refl M₀ with
        map_add' := by intro x y; rfl
        map_smul' := by intro x y; rfl }
    have hprojective₀ : Module.Projective R₀ M₀ :=
      Module.Projective.of_equiv e
    exact finiteSupportQuotient78_not_projective hprojective₀
  refine ⟨R, inferInstance, M, inferInstance, inferInstance, ?_⟩
  exact ⟨hfinite, hflat, hnot⟩

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
  constructor
  · rintro ⟨hfin, hproj⟩
    letI := hfin
    letI := hproj
    letI : Module.Free S (S ⊗[R] M) := Module.free_of_flat_of_isLocalRing
    exact ⟨inferInstance, Module.Projective.of_free⟩
  · rintro ⟨hfin, hproj⟩
    letI := hfin
    letI := hproj
    letI : Module.FaithfullyFlat R S :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    have hflat : Module.Flat R M :=
      (Module.Flat.iff_flat_tensorProduct R M S).mp inferInstance
    letI := hflat
    letI : Module.Free R M := Module.free_of_flat_of_isLocalRing
    exact ⟨inferInstance, Module.Projective.of_free⟩

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
  classical
  rcases hr with ⟨r, hr⟩
  have hfp : FiniteProjective R M :=
    ((finite_projective_characterization (R := R) (M := M)).out 6 1).mp hM
  letI : Module.Finite R M := hfp.1
  letI : Module.Projective R M := hfp.2
  letI : Finite (MaximalSpectrum R) := hR
  have hfiber (P : MaximalSpectrum R) :
    Module.finrank (R ⧸ P.1) ((R ⧸ P.1) ⊗[R] M) = r := by
    letI : P.1.IsPrime := P.isMaximal.isPrime
    let p : PrimeSpectrum R := ⟨P.1, P.isMaximal.isPrime⟩
    letI : p.asIdeal.IsMaximal := P.isMaximal
    obtain ⟨s, hs, hsr⟩ := hr
    have pick (w : Set R) (hw : Ideal.span w = ⊤) : ∃ a ∈ w, a ∉ P.1 := by
      by_contra h
      push_neg at h
      have hle : Ideal.span w ≤ P.1 := Ideal.span_le.mpr h
      exact P.isMaximal.ne_top (by
        apply top_unique
        rw [← hw]
        exact hle)
    obtain ⟨a, ha, haP⟩ := pick s hs
    obtain ⟨q, hq⟩ : p ∈ Set.range (PrimeSpectrum.comap
        (algebraMap R (Localization.Away a))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away a) a]
      exact haP
    letI : Nontrivial (Localization.Away a) :=
      (IsLocalization.toLocalizationMap (Submonoid.powers a)
        (Localization.Away a)).nontrivial (by
          rintro ⟨k, hk⟩
          exact (p.asIdeal.primeCompl.pow_mem haP k) (by
            change a ^ k = 0 at hk
            rw [hk]
            exact p.asIdeal.zero_mem))
    obtain ⟨e⟩ := hsr a ha
    letI : Module.Free (Localization.Away a) (LocalizedModule.Away a M) :=
      Module.Free.of_equiv e.symm
    have hAway : Module.rankAtStalk (LocalizedModule.Away a M) q = r := by
      rw [Module.rankAtStalk_eq_finrank_of_free]
      calc
        Module.finrank (Localization.Away a) (LocalizedModule.Away a M) =
            Module.finrank (Localization.Away a)
              (Fin r →₀ Localization.Away a) := e.finrank_eq
        _ = Module.finrank (Localization.Away a)
            (Fin r → Localization.Away a) :=
          (Finsupp.linearEquivFunOnFinite (Localization.Away a)
            (Localization.Away a) (Fin r)).finrank_eq
        _ = Fintype.card (Fin r) :=
          Module.finrank_fintype_fun_eq_card (Localization.Away a)
        _ = r := Fintype.card_fin r
    have hP : Module.rankAtStalk M p = r := by
      calc
        Module.rankAtStalk M p = Module.rankAtStalk M
            (PrimeSpectrum.comap (algebraMap R (Localization.Away a)) q) := by
          rw [hq]
        _ = Module.rankAtStalk (LocalizedModule.Away a M) q := by
          symm
          exact Module.rankAtStalk_isBaseChange
            (LocalizedModule.isBaseChange (Submonoid.powers a) M) q
        _ = r := hAway
    have hres : Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M) = r :=
      (Ideal.finrank_fiber_eq_rankAtStalk (M := M) p.asIdeal).trans hP
    change Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M) = r at hres
    letI : Field (R ⧸ p.asIdeal) := Ideal.Quotient.field p.asIdeal
    let e₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange
      R (R ⧸ p.asIdeal) p.asIdeal.ResidueField p.asIdeal.ResidueField M
    calc
      Module.finrank (R ⧸ p.asIdeal) ((R ⧸ p.asIdeal) ⊗[R] M) =
          Module.finrank p.asIdeal.ResidueField
            (p.asIdeal.ResidueField ⊗[R ⧸ p.asIdeal]
              ((R ⧸ p.asIdeal) ⊗[R] M)) := by
        simpa only using
          (Module.finrank_baseChange
            (R := p.asIdeal.ResidueField) (S := R ⧸ p.asIdeal)
            (M' := (R ⧸ p.asIdeal) ⊗[R] M)).symm
      _ = Module.finrank p.asIdeal.ResidueField
          (p.asIdeal.ResidueField ⊗[R] M) := e₂.finrank_eq
      _ = r := hres
  exact Module.free_of_flat_of_finrank_eq R M r hfiber

/-- A finite locally free module over a semilocal ring with connected spectrum is free. -/
theorem free_of_finiteLocallyFree_of_connectedSpectrum
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [ConnectedSpace (PrimeSpectrum R)]
    (hR : Formalization.Books.Algebra.Unit03.IsSemilocalRing R)
    (hM : FiniteLocallyFree R M) :
    Module.Free R M := by
  classical
  have hfp : FiniteProjective R M :=
    ((finite_projective_characterization (R := R) (M := M)).out 6 1).mp hM
  letI : Module.Finite R M := hfp.1
  letI : Module.Projective R M := hfp.2
  letI : Finite (MaximalSpectrum R) := hR
  letI : Module.FinitePresentation R M :=
    Module.finitePresentation_of_projective R M
  rcases subsingleton_or_nontrivial R with hR0 | hR0
  · letI := hR0
    exact Module.Free.of_subsingleton' R M
  · letI := hR0
    obtain ⟨I, hI⟩ := Formalization.Books.Algebra.Unit03.exists_maximal_ideal R
    letI : I.IsPrime := hI.isPrime
    let p₀ : PrimeSpectrum R := ⟨I, hI.isPrime⟩
    have hloc : IsLocallyConstant (Module.rankAtStalk (R := R) M) :=
      Module.isLocallyConstant_rankAtStalk
    have hconst (p q : PrimeSpectrum R) :
        Module.rankAtStalk M p = Module.rankAtStalk M q :=
      hloc.apply_eq_of_preconnectedSpace p q
    let r := Module.rankAtStalk M p₀
    apply Module.free_of_flat_of_finrank_eq R M r
    intro P
    let p : PrimeSpectrum R := ⟨P.1, P.isMaximal.isPrime⟩
    letI : p.asIdeal.IsPrime := P.isMaximal.isPrime
    letI : p.asIdeal.IsMaximal := P.isMaximal
    have hp : Module.rankAtStalk M p = r := by
      exact hconst p p₀
    have hres : Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M) = r :=
      (Ideal.finrank_fiber_eq_rankAtStalk (M := M) p.asIdeal).trans hp
    change Module.finrank p.asIdeal.ResidueField
      (p.asIdeal.ResidueField ⊗[R] M) = r at hres
    letI : Field (R ⧸ p.asIdeal) := Ideal.Quotient.field p.asIdeal
    let e₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange
      R (R ⧸ p.asIdeal) p.asIdeal.ResidueField p.asIdeal.ResidueField M
    calc
      Module.finrank (R ⧸ p.asIdeal) ((R ⧸ p.asIdeal) ⊗[R] M) =
          Module.finrank p.asIdeal.ResidueField
            (p.asIdeal.ResidueField ⊗[R ⧸ p.asIdeal]
              ((R ⧸ p.asIdeal) ⊗[R] M)) := by
        simpa only using
          (Module.finrank_baseChange
            (R := p.asIdeal.ResidueField) (S := R ⧸ p.asIdeal)
            (M' := (R ⧸ p.asIdeal) ⊗[R] M)).symm
      _ = Module.finrank p.asIdeal.ResidueField
          (p.asIdeal.ResidueField ⊗[R] M) := e₂.finrank_eq
      _ = r := hres

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
