import Formalization.Books.Algebra.Unit78.FiniteProjectiveModules
import Formalization.Books.Algebra.Unit157.SerresCriterion
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# More on Algebra, Chapter 22: Torsion free modules

This file records the source's torsion notions and the consequences collected
in the chapter.  Torsion-free modules use Mathlib's canonical
`Module.IsTorsionFree` class, and torsion submodules use `Submodule.torsion`.
The source's support and associated-prime terminology is represented by the
interfaces established in the earlier Algebra chapters.
-/

namespace Formalization.Books.MoreAlgebra.Unit22

open Set
open Formalization.Books.Algebra.Unit63
open Formalization.Books.Algebra.Unit67
open Formalization.Books.Algebra.Unit157
open scoped TensorProduct

universe u v w

noncomputable section

/-! ## Definitions -/

/-- The source's torsion-free predicate, delegated to Mathlib's canonical
`Module.IsTorsionFree` class. -/
abbrev TorsionFree (R M : Type*) [CommRing R] [AddCommGroup M]
    [Module R M] : Prop :=
  Module.IsTorsionFree R M

/-- The source's torsion-module predicate, delegated to Mathlib's canonical
`Module.IsTorsion` abbreviation. -/
abbrev TorsionModule (R M : Type*) [CommRing R] [AddCommGroup M]
    [Module R M] : Prop :=
  Module.IsTorsion R M

/-- Over a domain, membership in the canonical torsion submodule is exactly
the elementwise definition in the source. -/
theorem mem_torsion_iff_exists_smul_eq_zero
    {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] (x : M) :
    x ∈ Submodule.torsion R M ↔
      ∃ r : R, r ≠ 0 ∧ r • x = 0 := by
  simp [Submodule.torsion]

/-- The usual elementwise characterization of the source's torsion-free
condition. -/
theorem torsionFree_iff_smul_eq_zero
    {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] :
    TorsionFree R M ↔
      ∀ (r : R) (x : M), r • x = 0 → r = 0 ∨ x = 0 :=
  Module.isTorsionFree_iff_smul_eq_zero

/-- Every element is torsion exactly when it belongs to the torsion
submodule. -/
theorem torsionModule_iff_forall_mem_torsion
    {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] :
    TorsionModule R M ↔ ∀ x : M, x ∈ Submodule.torsion R M := by
  simp [TorsionModule, Module.IsTorsion, Submodule.torsion]

/-! ## Localization and torsion quotients -/

/-- The canonical map into a fraction-field tensor product. -/
noncomputable def fractionFieldTensorMap
    {R M K : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Field K] [Algebra R K] :
    M →ₗ[R] M ⊗[R] K :=
  (TensorProduct.mk R M K).flip 1

/-- A domain module is torsion-free exactly when its localization at all
nonzero elements is injective. -/
theorem torsionFree_iff_nonZeroDivisorLocalization_injective
    {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] :
    TorsionFree R M ↔
      Function.Injective
        (LocalizedModule.mkLinearMap (nonZeroDivisors R) M) := by
  change Module.IsTorsionFree R M ↔
    Function.Injective (fun m : M => LocalizedModule.mk m 1)
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  constructor
  · intro h m₁ m₂ hm
    obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp hm
    have hu0 : (u : R) ≠ 0 := nonZeroDivisors.ne_zero u.property
    have hu' : (u : R) • m₁ = (u : R) • m₂ := by
      simpa [Submonoid.smul_def] using hu
    have hzero : (u : R) • (m₁ - m₂) = 0 := by
      rw [smul_sub, sub_eq_zero]
      exact hu'
    have hdiff : m₁ - m₂ = 0 :=
      (h (u : R) (m₁ - m₂) hzero).resolve_left hu0
    exact sub_eq_zero.mp hdiff
  · intro h r m hr
    by_cases hr0 : r = 0
    · exact Or.inl hr0
    · apply Or.inr
      apply h
      change LocalizedModule.mk m 1 = LocalizedModule.mk 0 1
      let s : nonZeroDivisors R := ⟨r, by simpa using hr0⟩
      rw [← LocalizedModule.mk_cancel s m]
      rw [Submonoid.smul_def, hr]
      simp

/-- For a fraction field, the localization criterion can be written using
the canonical map into the tensor product with that field. -/
theorem torsionFree_iff_fractionFieldTensorMap_injective
    {R M K : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Field K] [Algebra R K]
    [IsFractionRing R K] :
    TorsionFree R M ↔
      Function.Injective
        (fractionFieldTensorMap (R := R) (M := M) (K := K)) := by
  change Module.IsTorsionFree R M ↔ Function.Injective ⇑fractionFieldTensorMap
  let S := nonZeroDivisors R
  let g : M →ₗ[R] K ⊗[R] M := TensorProduct.mk R K M 1
  have hg : Function.Injective g ↔
      Function.Injective (LocalizedModule.mkLinearMap S M) := by
    let e := IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S M) g
    constructor
    · intro h x y hxy
      apply h
      have heq := congrArg e hxy
      simpa only [e, IsLocalizedModule.linearEquiv_apply] using heq
    · intro h x y hxy
      apply h
      apply e.injective
      simpa only [e, IsLocalizedModule.linearEquiv_apply] using hxy
  have hloc : Module.IsTorsionFree R M ↔ Function.Injective g := by
    rw [hg]
    exact torsionFree_iff_nonZeroDivisorLocalization_injective
  have hmap : fractionFieldTensorMap (R := R) (M := M) (K := K) =
      (TensorProduct.comm R K M).toLinearMap.comp g := by
    ext m
    rfl
  rw [hloc, hmap]
  constructor
  · intro h
    exact (TensorProduct.comm R K M).injective.comp h
  · intro h x y hxy
    apply h
    change (TensorProduct.comm R K M) (g x) = (TensorProduct.comm R K M) (g y)
    exact congrArg ((TensorProduct.comm R K M).toLinearMap) hxy

/-- The torsion submodule is the kernel of the fraction-field map. -/
theorem torsion_eq_ker_fractionFieldTensorMap
    {R M K : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Field K] [Algebra R K]
    [IsFractionRing R K] :
    Submodule.torsion R M =
      LinearMap.ker
        (fractionFieldTensorMap (R := R) (M := M) (K := K)) := by
  apply le_antisymm
  · intro x hx
    rw [mem_torsion_iff_exists_smul_eq_zero] at hx
    change fractionFieldTensorMap (R := R) (M := M) (K := K) x = 0
    obtain ⟨r, hr, hrx⟩ := hx
    let g : M →ₗ[R] K ⊗[R] M := TensorProduct.mk R K M 1
    have hmap : fractionFieldTensorMap (R := R) (M := M) (K := K) =
        (TensorProduct.comm R K M).toLinearMap.comp g := by
      ext m
      rfl
    have hsmul : algebraMap R K r • g x = 0 := by
      rw [algebraMap_smul K]
      rw [← g.map_smul]
      simpa [hrx]
    have hg : g x = 0 :=
      (smul_eq_zero.mp hsmul).resolve_left
        (fun h => hr (IsFractionRing.injective R K (by simpa using h)))
    rw [hmap]
    exact congrArg (TensorProduct.comm R K M) hg
  · intro x hx
    change fractionFieldTensorMap (R := R) (M := M) (K := K) x = 0 at hx
    rw [mem_torsion_iff_exists_smul_eq_zero]
    let S := nonZeroDivisors R
    let g : M →ₗ[R] K ⊗[R] M := TensorProduct.mk R K M 1
    let e : LocalizedModule S M ≃ₗ[R] K ⊗[R] M :=
      IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S M) g
    have hcomm : Function.Injective (TensorProduct.comm R K M) :=
      (TensorProduct.comm R K M).injective
    have hxg : g x = 0 := by
      apply hcomm
      simpa [fractionFieldTensorMap, g] using hx
    have hm : LocalizedModule.mk x (1 : S) = 0 := by
      have heq := congrArg e.symm hxg
      simpa [e] using heq
    have hm' : LocalizedModule.mk x (1 : S) = LocalizedModule.mk 0 (1 : S) := by
      simpa using hm
    obtain ⟨u, hu⟩ := (LocalizedModule.mk_eq (S := S)).mp hm'
    have hu0 : (u : R) ≠ 0 := nonZeroDivisors.ne_zero u.property
    refine ⟨(u : R), hu0, ?_⟩
    simpa [Submonoid.smul_def] using hu

/-- Quotienting by the torsion submodule produces a torsion-free module. -/
theorem quotient_by_torsion_isTorsionFree
    {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] :
    TorsionFree R (M ⧸ Submodule.torsion R M) := by
  infer_instance

/-- Localization preserves torsion-freeness over a domain. -/
theorem localizedModule_isTorsionFree
    {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] (S : Submonoid R)
    [Module.IsTorsionFree R M] :
    Module.IsTorsionFree (Localization S) (LocalizedModule S M) := by
  infer_instance

attribute [local instance] Algebra.TensorProduct.rightAlgebra Algebra.TensorProduct.leftAlgebra in
/-- Flat base change between domains preserves torsion-freeness. -/
theorem flat_baseChange_isTorsionFree
    {R R' M : Type*} [CommRing R] [CommRing R']
    [IsDomain R] [IsDomain R'] [Algebra R R']
    [AddCommGroup M] [Module R M] [Module.Flat R R']
    [Module.IsTorsionFree R M] :
    Module.IsTorsionFree R' (R' ⊗[R] M) := by
  let K := FractionRing R
  let V := K ⊗[R] M
  let A := R' ⊗[R] K
  have hA : Module.IsTorsionFree R' A := by
    infer_instance
  have hD_A : Module.IsTorsionFree A (A ⊗[K] V) := by
    infer_instance
  have hD : Module.IsTorsionFree R' (A ⊗[K] V) := by
    exact @Module.IsTorsionFree.trans A R' (A ⊗[K] V)
      _ _ _ _ _ hD_A _ hA _ _ _
  let e₁ : A ⊗[K] V ≃ₗ[R'] A ⊗[R] M :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R K A A M).restrictScalars R'
  let e₂ : A ⊗[R] M ≃ₗ[R'] R' ⊗[R] V :=
    TensorProduct.AlgebraTensorModule.assoc R R R' R' K M
  let e : A ⊗[K] V ≃ₗ[R'] R' ⊗[R] V := e₁.trans e₂
  have hC : Module.IsTorsionFree R' (R' ⊗[R] V) := by
    exact @Function.Injective.moduleIsTorsionFree R' (R' ⊗[R] V)
      (A ⊗[K] V) _ _ _ _ _ hD e.symm e.symm.injective
      (fun r x ↦ e.symm.map_smul r x)
  let g : M →ₗ[R] V := TensorProduct.mk R K M 1
  have hg : Function.Injective g := by
    have hf : Function.Injective
        (fractionFieldTensorMap (R := R) (M := M) (K := K)) :=
      (torsionFree_iff_fractionFieldTensorMap_injective (R := R) (M := M)
        (K := K)).mp inferInstance
    have hmap : fractionFieldTensorMap (R := R) (M := M) (K := K) =
        (TensorProduct.comm R K M).toLinearMap.comp g := by
      ext m
      rfl
    intro x y hxy
    apply hf
    rw [hmap]
    exact congrArg (TensorProduct.comm R K M) hxy
  let gb : R' ⊗[R] M →ₗ[R'] R' ⊗[R] V :=
    TensorProduct.AlgebraTensorModule.lTensor R' R' g
  have hbase : Function.Injective gb :=
    Module.Flat.lTensor_preserves_injective_linearMap g hg
  exact @Function.Injective.moduleIsTorsionFree R' (R' ⊗[R] M)
    (R' ⊗[R] V) _ _ _ _ _ hC gb hbase (fun r x ↦ gb.map_smul r x)

/-! ## Extensions, local tests, and finite modules -/

/-- In a short exact sequence, torsion-freeness is inherited by the middle
module from the two end modules. -/
theorem shortExact_middle_isTorsionFree
    {R M M' M'' : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup M''] [Module R M'']
    (f : M →ₗ[R] M') (g : M' →ₗ[R] M'')
    (hf : Function.Injective f)
    (h_exact : Function.Exact (f : M → M') (g : M' → M''))
    (hg : Function.Surjective g)
    [Module.IsTorsionFree R M] [Module.IsTorsionFree R M''] :
    Module.IsTorsionFree R M' := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro r x hrx
  by_cases hr : r = 0
  · exact Or.inl hr
  · right
    have hgx_smul : r • g x = 0 := by
      rw [← g.map_smul, hrx]
      simp
    have hgx : g x = 0 :=
      (Module.isTorsionFree_iff_smul_eq_zero.mp inferInstance r (g x) hgx_smul).resolve_left hr
    obtain ⟨y, hy⟩ := (h_exact x).mp hgx
    have hsy : r • f y = 0 := by
      rw [hy]
      exact hrx
    have hry : r • y = 0 := by
      apply hf
      simpa using hsy
    have hy0 : y = 0 :=
      (Module.isTorsionFree_iff_smul_eq_zero.mp inferInstance r y hry).resolve_left hr
    simpa [hy0] using hy.symm

/-- Torsion-freeness can be checked after localizing at every maximal ideal.
The points are represented by the canonical `MaximalSpectrum` type. -/
theorem torsionFree_iff_localized_at_maximal
    {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] :
    TorsionFree R M ↔
      ∀ m : MaximalSpectrum R,
        Module.IsTorsionFree (Localization.AtPrime m.asIdeal)
          (LocalizedModule.AtPrime m.asIdeal M) := by
  constructor
  · intro h m
    exact @localizedModule_isTorsionFree R M _ _ _ _ m.asIdeal.primeCompl h
  · intro h
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro r x hrx
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      by_contra hx
      let I : Ideal R :=
        { carrier := {a | a • x = 0}
          zero_mem' := by simp
          add_mem' := by
            intro a b ha hb
            change (a + b) • x = 0
            rw [add_smul, ha, hb, add_zero]
          smul_mem' := by
            intro a b hb
            change (a * b) • x = 0
            rw [mul_smul, hb, smul_zero] }
      have hI_top : I ≠ ⊤ := by
        intro htop
        have hone : (1 : R) ∈ I := htop ▸ (show (1 : R) ∈ (⊤ : Ideal R) from trivial)
        exact hx (by simpa [I] using hone)
      obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI_top
      let p : MaximalSpectrum R := ⟨m, hm⟩
      let S := p.asIdeal.primeCompl
      have hrp : algebraMap R (Localization S) r ≠ 0 := by
        intro hzero
        apply hr
        apply FaithfulSMul.algebraMap_injective R (Localization S)
        simpa using hzero
      have hsmul : algebraMap R (Localization S) r •
          (LocalizedModule.mk x (1 : S)) = 0 := by
        rw [algebraMap_smul (Localization S)]
        change r • (LocalizedModule.mkLinearMap S M x) = 0
        rw [← (LocalizedModule.mkLinearMap S M).map_smul]
        simpa [hrx]
      have hmk : LocalizedModule.mk x (1 : S) = 0 :=
        (Module.isTorsionFree_iff_smul_eq_zero.mp (h p)
          (algebraMap R (Localization S) r) (LocalizedModule.mk x (1 : S)) hsmul).resolve_left hrp
      have hmk' : LocalizedModule.mk x (1 : S) = LocalizedModule.mk 0 (1 : S) := by
        simpa using hmk
      obtain ⟨u, hu⟩ := (LocalizedModule.mk_eq (S := S)).mp hmk'
      have huI : (u : R) ∈ I := by
        simpa [I, Submonoid.smul_def] using hu
      exact u.property (hIm huI)

/-- A finite torsion-free module over a domain embeds in a finite free module.
The finite free module is represented canonically by a finite Finsupp type. -/
theorem finite_torsionFree_iff_embeds_finiteFree
    {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    TorsionFree R M ↔
      ∃ n : ℕ, ∃ f : M →ₗ[R] (Fin n →₀ R), Function.Injective f := by
  classical
  constructor
  · intro h
    let K := FractionRing R
    let V := K ⊗[R] M
    let g : M →ₗ[R] V := TensorProduct.mk R K M 1
    have hg : Function.Injective g := by
      have hf : Function.Injective
          (fractionFieldTensorMap (R := R) (M := M) (K := K)) :=
        (torsionFree_iff_fractionFieldTensorMap_injective (R := R) (M := M)
          (K := K)).mp h
      have hmap : fractionFieldTensorMap (R := R) (M := M) (K := K) =
          (TensorProduct.comm R K M).toLinearMap.comp g := by
        ext m
        rfl
      intro x y hxy
      apply hf
      rw [hmap]
      exact congrArg (TensorProduct.comm R K M) hxy
    obtain ⟨ι, b₀⟩ := Module.Free.exists_basis (R := K) (M := V)
    let : Finite ι := Module.Finite.finite_basis b₀
    obtain ⟨n, e₀⟩ := Finite.exists_equiv_fin ι
    obtain ⟨e⟩ := e₀
    let b : Module.Basis (Fin n) K V := b₀.reindex e
    let hK : M →ₗ[R] (Fin n →₀ K) :=
      b.repr.toLinearMap.restrictScalars R |>.comp g
    have hhK : Function.Injective hK := b.repr.injective.comp hg
    obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule R M).FG)
    let q : (Fin n →₀ R) →ₗ[R] (Fin n →₀ K) :=
      Finsupp.mapRange.linearMap (Algebra.linearMap R K)
    have hq : Function.Injective q := by
      intro x y hxy
      apply Finsupp.ext
      intro i
      apply IsFractionRing.injective R K
      simpa [q] using congrArg (fun z => z i) hxy
    obtain ⟨d, hd⟩ :=
      IsLocalization.exist_integer_multiples_of_finite
        (M := nonZeroDivisors R) (S := K)
        (fun z : s × Fin n => hK z.1 z.2)
    have hd' (x : s) (i : Fin n) :
        ∃ r : R, algebraMap R K r = (d : R) • hK x.1 i := by
      simpa [IsLocalization.IsInteger] using hd (x, i)
    let z : s → Fin n →₀ R := fun x =>
      Finsupp.equivFunOnFinite.symm (fun i => (hd' x i).choose)
    have hz (x : s) :
        q (z x) = (d : R) • hK x.1 := by
      ext i
      simpa [q, z, hd' x i] using (hd' x i).choose_spec
    let hD : M →ₗ[R] (Fin n →₀ K) := (d : R) • hK
    let L : Submodule R (Fin n →₀ K) := LinearMap.range q
    have hgen : ∀ x : s, hD x ∈ L := by
      intro x
      change (d : R) • hK x.1 ∈ L
      exact ⟨z x, hz x⟩
    have hDmem : ∀ x : M, hD x ∈ L := by
      intro x
      have hle : (⊤ : Submodule R M) ≤ L.comap hD := by
        rw [← hs]
        exact Submodule.span_le.2 (fun y hy => hgen ⟨y, hy⟩)
      exact hle (by trivial)
    let eL : (Fin n →₀ R) ≃ₗ[R] L := LinearEquiv.ofInjective q hq
    let f : M →ₗ[R] (Fin n →₀ R) :=
      eL.symm.toLinearMap.comp (hD.codRestrict L hDmem)
    refine ⟨n, f, ?_⟩
    intro x y hxy
    have hxy' : hD x = hD y := by
      change eL.symm (hD.codRestrict L hDmem x) =
        eL.symm (hD.codRestrict L hDmem y) at hxy
      exact congrArg Subtype.val (eL.symm.injective hxy)
    have hzero : (d : R) • (hK x - hK y) = 0 := by
      rw [smul_sub]
      change hD x - hD y = 0
      exact sub_eq_zero.mpr hxy'
    have hzero' :
        (algebraMap R K (d : R)) • (hK x - hK y) = 0 := by
      simpa [Algebra.smul_def] using hzero
    have hd0 : algebraMap R K (d : R) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.property
    apply hhK
    exact sub_eq_zero.mp ((smul_eq_zero.mp hzero').resolve_left hd0)
  · rintro ⟨n, f, hf⟩
    exact Function.Injective.moduleIsTorsionFree (f : M → (Fin n →₀ R)) hf
      (fun r x => f.map_smul r x)

/-! ## The noetherian-domain criteria -/

/-- The finite-module characterizations of torsion-freeness over a noetherian
domain.  The last two clauses use the earlier chapters' support, associated
prime, embedded-prime, and `(S_1)` interfaces. -/
theorem finite_noetherian_domain_torsionFree_criteria
    {R M : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] :
    List.TFAE
      [TorsionFree R M,
       ∃ n : ℕ, ∃ f : M →ₗ[R] (Fin n →₀ R), Function.Injective f,
       ∀ p : PrimeSpectrum R,
         p ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M ↔
           p.asIdeal = (⊥ : Ideal R),
       (∃ p : PrimeSpectrum R,
          p ∈ Module.support R M ∧ p.asIdeal = (⊥ : Ideal R)) ∧
         Formalization.Books.Algebra.Unit157.HasPropertySkModule R M 1,
       (∃ p : PrimeSpectrum R,
          p ∈ Module.support R M ∧ p.asIdeal = (⊥ : Ideal R)) ∧
         Formalization.Books.Algebra.Unit67.embeddedAssociatedPrimes
           (R := R) (M := M) = ∅] := by
  tfae_have 1 ↔ 2 := by
    exact finite_torsionFree_iff_embeds_finiteFree (R := R) (M := M)
  tfae_have 1 ↔ 3 := by
    constructor
    · intro h p
      constructor
      · intro hp
        change ∃ m : M, (⊥ : Submodule R M).colon ({m} : Set M) = p.asIdeal at hp
        obtain ⟨m, hm⟩ := hp
        have hm0 : m ≠ 0 := by
          intro hmzero
          apply p.isPrime.ne_top
          rw [← hm, Submodule.colon_eq_top_iff_subset]
          simp [hmzero]
        apply le_antisymm
        · intro r hr
          change r = 0
          have hsmul : r • m = 0 := by
            rw [← hm, Submodule.mem_colon_singleton] at hr
            simpa using hr
          exact ((torsionFree_iff_smul_eq_zero.mp h) r m hsmul).resolve_right hm0
        · exact bot_le
      · intro hp
        change ∃ m : M, (⊥ : Submodule R M).colon ({m} : Set M) = p.asIdeal
        obtain ⟨m, hm⟩ := @exists_ne M inferInstance (0 : M)
        refine ⟨m, ?_⟩
        rw [hp]
        apply le_antisymm
        · intro r hr
          change r = 0
          have hsmul : r • m = 0 := by
            rw [Submodule.mem_colon_singleton] at hr
            simpa using hr
          exact ((torsionFree_iff_smul_eq_zero.mp h) r m hsmul).resolve_right hm
        · exact bot_le
    · intro h3
      apply Module.IsTorsionFree.of_smul_eq_zero
      intro r x hrx
      by_cases hr : r = 0
      · exact Or.inl hr
      · right
        by_contra hx
        have hrzd : r ∈ {x : R | ∃ m : M, m ≠ 0 ∧ x • m = 0} :=
          ⟨x, hx, hrx⟩
        have hrunion :
            r ∈ ⋃ p : {p : PrimeSpectrum R // p ∈
              Formalization.Books.Algebra.Unit63.associatedPrimes R M},
                (p.1.asIdeal : Set R) := by
          rw [Formalization.Books.Algebra.Unit63.iUnion_associatedPrimes_eq_module_zeroDivisors]
          exact hrzd
        obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hrunion
        have hpbot := (h3 p.1).mp p.2
        have hr0 : r = 0 := by
          rw [hpbot] at hp
          exact hp
        exact hr hr0
  tfae_have 3 ↔ 5 := by
    constructor
    · intro h3
      have hass : (Formalization.Books.Algebra.Unit63.associatedPrimes R M).Nonempty := by
        by_contra hnonempty
        have hsub : Subsingleton M :=
          (Formalization.Books.Algebra.Unit63.ass_eq_empty_iff_subsingleton
            (R := R) (M := M)).mpr (Set.not_nonempty_iff_eq_empty.mp hnonempty)
        exact not_subsingleton_iff_nontrivial.mpr inferInstance hsub
      obtain ⟨p, hp⟩ := hass
      have hpbot : p.asIdeal = (⊥ : Ideal R) := (h3 p).mp hp
      refine ⟨⟨p, ⟨Formalization.Books.Algebra.Unit63.ass_subset_support hp, hpbot⟩⟩, ?_⟩
      rw [Set.eq_empty_iff_forall_notMem]
      intro q hq
      apply hq.2
      refine ⟨hq.1, ?_⟩
      intro r hr hrq
      have hqbot : q.asIdeal = (⊥ : Ideal R) := (h3 q).mp hq.1
      have hrbot : r.asIdeal = (⊥ : Ideal R) := (h3 r).mp hr
      change q.asIdeal ≤ r.asIdeal
      rw [hqbot, hrbot]
    · rintro ⟨hsupp, hemb⟩ p
      let p₀ : PrimeSpectrum R := ⟨(⊥ : Ideal R), Ideal.isPrime_bot⟩
      have hp₀supp : p₀ ∈ Module.support R M := by
        obtain ⟨q, hq, hqbot⟩ := hsupp
        have hqeq : q = p₀ := by
          apply PrimeSpectrum.ext
          simpa [p₀] using hqbot
        simpa [hqeq] using hq
      have hp₀min : Minimal
          (fun q : PrimeSpectrum R => q ∈ Module.support R M) p₀ := by
        refine ⟨hp₀supp, ?_⟩
        intro q hq hqle
        have hqeq : q = p₀ := by
          apply PrimeSpectrum.ext
          change q.asIdeal = (⊥ : Ideal R)
          exact le_antisymm hqle bot_le
        simp [hqeq]
      have hp₀ass :
          p₀ ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M :=
        Formalization.Books.Algebra.Unit63.ass_of_minimal_support p₀ hp₀supp hp₀min
      constructor
      · intro hp
        have hpmin :
            Minimal
              (fun q : PrimeSpectrum R =>
                q ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M) p := by
          by_contra hnot
          exact (Set.eq_empty_iff_forall_notMem.mp hemb p) ⟨hp, hnot⟩
        have hp_le : p ≤ p₀ := hpmin.2 hp₀ass (by
          change (⊥ : Ideal R) ≤ p.asIdeal
          exact bot_le)
        have hpbot : p.asIdeal = (⊥ : Ideal R) := by
          apply le_antisymm
          · change p.asIdeal ≤ (⊥ : Ideal R) at hp_le
            exact hp_le
          · exact bot_le
        exact hpbot
      · intro hpbot
        have hpeq : p = p₀ := by
          apply PrimeSpectrum.ext
          simpa [p₀] using hpbot
        simpa [hpeq] using hp₀ass
  tfae_have 4 ↔ 5 := by
    constructor
    · rintro ⟨hsupp, hS⟩
      exact ⟨hsupp, (Formalization.Books.Algebra.Unit157.criterion_no_embedded_primes
        (R := R) (M := M)).mpr hS⟩
    · rintro ⟨hsupp, hemb⟩
      exact ⟨hsupp, (Formalization.Books.Algebra.Unit157.criterion_no_embedded_primes
        (R := R) (M := M)).mp hemb⟩
  tfae_finish

/-! ## Flatness, valuation rings, and Dedekind domains -/

/-- Every flat module over a domain is torsion-free. -/
theorem flat_isTorsionFree
    {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.Flat R M] :
    TorsionFree R M := by
  infer_instance

/-- Over a valuation ring, flatness and torsion-freeness coincide. -/
theorem valuationRing_flat_iff_torsionFree
    {A M : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
    [AddCommGroup M] [Module A M] :
    Module.Flat A M ↔ Module.IsTorsionFree A M := by
  simpa only [← Submodule.isTorsionFree_iff_torsion_eq_bot] using
    (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout (R := A) (M := M))

/-- Over a Dedekind domain, flatness and torsion-freeness coincide. -/
theorem dedekindDomain_flat_iff_torsionFree
    {A M : Type*} [CommRing A] [IsDedekindDomain A]
    [AddCommGroup M] [Module A M] :
    Module.Flat A M ↔ Module.IsTorsionFree A M := by
  simpa only [← Submodule.isTorsionFree_iff_torsion_eq_bot] using
    (IsDedekindDomain.flat_iff_torsion_eq_bot (R := A) (M := M))

/-- A finite torsion-free module over a Dedekind domain is finite locally
free, using the earlier chapter's source-facing local-freeness predicate. -/
theorem finite_torsionFree_dedekindDomain_isFiniteLocallyFree
    {A M : Type*} [CommRing A] [IsDedekindDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.IsTorsionFree A M] :
    Formalization.Books.Algebra.Unit78.FiniteLocallyFree A M := by
  sorry

/-- A finite torsion-free module over a PID is finite free.  Mathlib's
`IsPrincipalIdealRing` is the canonical PID class; its domain instance also
supplies the Dedekind-domain structure used in the surrounding source. -/
theorem finite_torsionFree_pid_isFree
    {A M : Type*} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.IsTorsionFree A M] :
    Module.Free A M := by
  infer_instance

/-! The source's parenthetical DVR examples are covered by Mathlib's
canonical instances from discrete valuation rings to Dedekind domains. -/

/-! ## Hom modules -/

/-- If the target is torsion-free, the linear Hom module into it is
torsion-free. -/
theorem hom_into_torsionFree_isTorsionFree
    {R M N : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.IsTorsionFree R N] :
    Module.IsTorsionFree R (M →ₗ[R] N) := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit22
