/-
# More on Algebra, Chapter 128: Splitting off a free module
-/

import Formalization.Books.Topology.Unit11.CodimensionAndCatenary
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Spectrum.Maximal.Topology
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Topology.KrullDimension
import Mathlib.Topology.NoetherianSpace

namespace Formalization.Books.MoreAlgebra.Unit128

open Set
open scoped TensorProduct

noncomputable section

universe u v

/-! ## The source situation and its canonical fibre -/

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/- The source's closed-point space `Ω` is Mathlib's maximal spectrum, whose
   topology is the subspace topology induced from the prime spectrum. -/

abbrev fibre (x : MaximalSpectrum R) : Type u := x.asIdeal.Fiber M

abbrev residueField (x : MaximalSpectrum R) : Type u := x.asIdeal.ResidueField

/- `1 ⊗ s` is the canonical image of a section in its residue-field fibre. -/
def fibreClass (x : MaximalSpectrum R) (s : M) : fibre (M := M) x :=
  (1 : residueField x) ⊗ₜ[R] s

/- The dual map in the source is the base change of a functional, followed by
   the canonical right-unit equivalence for tensor products. -/
noncomputable def fibreDualMap (x : MaximalSpectrum R) (φ : M →ₗ[R] R) :
    fibre (M := M) x →ₗ[residueField x] residueField x :=
  (TensorProduct.AlgebraTensorModule.rid R (residueField x) (residueField x)).toLinearMap.comp
    (φ.baseChange (residueField x))

@[simp]
theorem fibreDualMap_fibreClass (x : MaximalSpectrum R) (φ : M →ₗ[R] R) (s : M) :
    fibreDualMap x φ (fibreClass x s) = algebraMap R (residueField x) (φ s) := by
  simp [fibreDualMap, fibreClass, Algebra.smul_def]

/- The perpendicular `B(x)` is equivalently the intersection of the kernels
   of all functionals induced on the fibre. -/
noncomputable def B (x : MaximalSpectrum R) :
    Submodule (residueField x) (fibre (M := M) x) :=
  ⨅ φ : M →ₗ[R] R, LinearMap.ker (fibreDualMap x φ)

abbrev V (x : MaximalSpectrum R) : Type u := fibre (M := M) x ⧸ B x

def fibreToV (x : MaximalSpectrum R) :
    fibre (M := M) x →ₗ[residueField x] V (M := M) x :=
  (B x).mkQ

/- The inclusion of `B(x)` and the quotient map to `V(x)` form the source's
   canonical short exact sequence. -/
theorem b_fibre_v_short_exact (x : MaximalSpectrum R) :
    Function.Injective (B (M := M) x).subtype ∧
      Function.Exact (B (M := M) x).subtype (B (M := M) x).mkQ ∧
        Function.Surjective (B (M := M) x).mkQ := by
  refine ⟨(B (M := M) x).subtype_injective,
    LinearMap.exact_subtype_mkQ (B (M := M) x), ?_⟩
  exact fun y => Quotient.mk_surjective y

/- The finite-presentation hypothesis in the situation implies that the
   source fibre, and hence its quotient `V(x)`, are finite-dimensional. -/
theorem finiteDimensional_fibre [Module.FinitePresentation R M]
    (x : MaximalSpectrum R) :
    FiniteDimensional (residueField x) (fibre (M := M) x) := by
  infer_instance

theorem finiteDimensional_V [Module.FinitePresentation R M]
    (x : MaximalSpectrum R) :
    FiniteDimensional (residueField x) (V (M := M) x) := by
  infer_instance

/-! ## The direct-summand criterion -/

/- The source's map after inverting `f` is represented by the canonical
   localized-module map from the localized finite free module. -/
noncomputable def localizedSectionMap {r : ℕ} (f : R) (s : Fin r → M) :
    LocalizedModule.Away f (Fin r →₀ R) →ₗ[Localization.Away f]
      LocalizedModule.Away f M :=
  LocalizedModule.map (Submonoid.powers f) (Finsupp.linearCombination R s)

def IsLocalizedDirectSummand {r : ℕ} (f : R) (s : Fin r → M) : Prop :=
  Function.Injective (localizedSectionMap f s) ∧
    IsComplemented (LinearMap.range (localizedSectionMap f s))

private theorem compactElement_of_fg {A N : Type u} [CommRing A] [AddCommGroup N]
    [Module A N] {P : Submodule A N} (hP : P.FG) : IsCompactElement P := by
  obtain ⟨n, g, hg⟩ := (Submodule.fg_iff_exists_fin_generating_family.mp hP)
  intro S U hS hdir hL hPU
  have hsup : (⨆ q : S, (q : Submodule A N)) = U := by
    apply le_antisymm
    · exact iSup_le fun q => hL.1 q.property
    · apply hL.2
      intro q hq
      exact le_iSup_of_le ⟨q, hq⟩ le_rfl
  have hgen : ∀ i, g i ∈ (⨆ q : S, (q : Submodule A N)) := by
    intro i
    rw [hsup]
    apply hPU
    rw [← hg]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hpick : ∀ i, ∃ t : Finset S, g i ∈ ⨆ q ∈ t, (q : Submodule A N) := by
    intro i
    exact Submodule.exists_finset_of_mem_iSup (fun q : S => (q : Submodule A N)) (hgen i)
  have hupper : ∀ t : Finset S, ∃ q : S, ∀ a ∈ t, (a : Submodule A N) ≤ q := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        obtain ⟨q, hq⟩ := hS
        exact ⟨⟨q, hq⟩, by simp⟩
    | @insert a t ha ih =>
        obtain ⟨q, hqt⟩ := ih
        obtain ⟨q', hq', haq, hqq'⟩ := hdir a a.property q q.property
        refine ⟨⟨q', hq'⟩, ?_⟩
        intro b hb
        simp only [Finset.mem_insert] at hb
        exact hb.elim (fun h => h ▸ haq) (fun h => le_trans (hqt b h) hqq')
  choose t ht using hpick
  let u : Finset S := (Finset.univ : Finset (Fin n)).biUnion t
  obtain ⟨q, hq⟩ := hupper u
  refine ⟨q, q.property, ?_⟩
  rw [← hg]
  apply Submodule.span_le.2
  rintro z ⟨i, rfl⟩
  have hiq : (⨆ a ∈ t i, (a : Submodule A N)) ≤ q := by
    refine iSup_le fun a => iSup_le fun ha => ?_
    exact hq a (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, ha⟩)
  exact hiq (ht i)

private theorem finsupp_linearCombination_eq_sum {A P : Type u} {ι : Type v} [CommRing A]
    [AddCommGroup P] [Module A P] [Fintype ι]
    (v : ι → P) (c : ι →₀ A) :
    Finsupp.linearCombination A v c = ∑ i, c i • v i := by
  classical
  let e := Finsupp.linearEquivFunOnFinite A A ι
  have hc : c = e.symm (e c) := by simp [e]
  rw [hc, Finsupp.linearCombination_eq_fintype_linearCombination_apply]
  simp [e, Fintype.linearCombination]

private theorem map_finsupp_linearCombination {A P Q : Type u} {ι : Type v} [CommRing A]
    [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q] [Finite ι]
    (q : P →ₗ[A] Q) (v : ι → P) (c : ι →₀ A) :
    q (Finsupp.linearCombination A v c) =
      Finsupp.linearCombination A (fun i => q (v i)) c := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  rw [finsupp_linearCombination_eq_sum, finsupp_linearCombination_eq_sum]
  simp [map_sum, map_smul]

private theorem left_inverse_of_complemented {A N F : Type u} [CommRing A]
    [AddCommGroup N] [Module A N] [AddCommGroup F] [Module A F]
    (l : F →ₗ[A] N) (hl : Function.Injective l) (hc : IsComplemented (LinearMap.range l)) :
    ∃ g : N →ₗ[A] F, g.comp l = LinearMap.id := by
  rcases hc with ⟨K, hK⟩
  let e : F ≃ₗ[A] LinearMap.range l := LinearEquiv.ofInjective l hl
  let g : N →ₗ[A] F :=
    LinearMap.ofIsCompl (F := F) (p := LinearMap.range l) (q := K)
      hK e.symm.toLinearMap (0 : K →ₗ[A] F)
  refine ⟨g, LinearMap.ext (fun z : F => ?_)⟩
  have he :
      (LinearMap.ofIsCompl hK e.symm.toLinearMap (0 : K →ₗ[A] F)) (e z) = e.symm (e z) :=
    LinearMap.ofIsCompl_apply_left hK (e z)
  simpa [g, e] using he

private theorem directSummand_of_smul_left_inverse {r : ℕ}
    (d : R) (s : Fin r → M)
    (g : M →ₗ[R] (Fin r →₀ R)) (hg : g.comp (Finsupp.linearCombination R s) = d • LinearMap.id)
    : IsLocalizedDirectSummand d s := by
  let S : Submonoid R := Submonoid.powers d
  let L : LocalizedModule S (Fin r →₀ R) →ₗ[Localization S] LocalizedModule S M :=
    localizedSectionMap d s
  let G : LocalizedModule S M →ₗ[Localization S] LocalizedModule S (Fin r →₀ R) :=
    (LocalizedModule.map S g).extendScalarsOfIsLocalization S (Localization S)
  let u : (Localization S)ˣ :=
    (IsLocalization.map_units (Localization S)
      ⟨d, by
        change d ∈ Submonoid.powers d
        rw [Submonoid.mem_powers_iff]
        exact ⟨1, by simp⟩⟩).unit
  let ui : Localization S := ↑(u⁻¹)
  let P := ui • G
  have hGL : G.comp L = (algebraMap R (Localization S) d) • LinearMap.id := by
    apply LinearMap.ext
    intro z
    obtain ⟨⟨z, a⟩, rfl⟩ := IsLocalizedModule.mk'_surjective
      S (LocalizedModule.mkLinearMap S (Fin r →₀ R)) z
    simp only [Function.uncurry_apply_pair]
    rw [← IsLocalizedModule.mk_eq_mk']
    simp only [L, G, LinearMap.comp_apply]
    rw [LinearMap.extendScalarsOfIsLocalization_apply']
    change (LocalizedModule.map S g)
      (localizedSectionMap d s (LocalizedModule.mk z a)) =
      (algebraMap R (Localization S) d) • LocalizedModule.mk z a
    rw [show localizedSectionMap d s (LocalizedModule.mk z a) =
        LocalizedModule.mk (Finsupp.linearCombination R s z) a by
          simp [localizedSectionMap]]
    rw [LocalizedModule.map_mk]
    have hz := congrArg (fun k => k z) hg
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at hz
    rw [hz]
    rw [← IsLocalization.mk'_one (M := S) (S := Localization S) d]
    rw [← Localization.mk_eq_mk'_apply]
    rw [LocalizedModule.mk_smul_mk]
    simp
  have hleft : P.comp L = LinearMap.id := by
    dsimp [P]
    rw [LinearMap.smul_comp, hGL]
    have hu' : (u : Localization S) = algebraMap R (Localization S) d :=
      (IsLocalization.map_units (Localization S)
        ⟨d, by
          change d ∈ Submonoid.powers d
          rw [Submonoid.mem_powers_iff]
          exact ⟨1, by simp⟩⟩).unit_spec
    rw [smul_smul]
    change ((↑(u⁻¹) : Localization S) * algebraMap R (Localization S) d) •
      LinearMap.id = LinearMap.id
    rw [← hu']
    simp
  have hleft' : Function.LeftInverse P L := by
    intro z
    exact LinearMap.congr_fun hleft z
  refine ⟨hleft'.injective, ?_⟩
  exact ⟨LinearMap.ker P, by
    constructor
    · rw [Submodule.disjoint_iff_add_eq_zero]
      intro z y hzL hzK hsum
      rcases hzL with ⟨w, hw⟩
      have hsum' : L w + y = 0 := by rw [hw]; exact hsum
      have hp := congrArg P hsum'
      have hw0 : w = 0 := by
        rw [map_add, LinearMap.mem_ker.mp hzK, add_zero] at hp
        simpa [hleft' w] using hp
      have hz0 : z = 0 := by rw [← hw, hw0]; simp
      have hy0 : y = 0 := by rw [hw0] at hsum'; simpa using hsum'
      exact ⟨hz0, hy0⟩
    · change Codisjoint (LinearMap.range (localizedSectionMap d s)) (LinearMap.ker P)
      rw [codisjoint_iff]
      apply le_antisymm le_top
      intro z hz
      have hzdecomp : z = localizedSectionMap d s (P z) +
          (z - localizedSectionMap d s (P z)) := by abel
      rw [hzdecomp]
      apply Submodule.add_mem_sup
      · exact ⟨P z, rfl⟩
      · simp only [LinearMap.mem_ker]
        have hz' := hleft' (P z)
        rw [map_sub, hz']
        simp
    ⟩

private theorem smul_left_inverse_of_directSummand [Module.FinitePresentation R M]
    (x : MaximalSpectrum R) {r : ℕ} (s : Fin r → M)
    (h : ∃ f : R, f ∉ x.asIdeal ∧ IsLocalizedDirectSummand f s) :
    ∃ d : R, d ∉ x.asIdeal ∧
      ∃ g : M →ₗ[R] (Fin r →₀ R),
        g.comp (Finsupp.linearCombination R s) = d • LinearMap.id := by
  rcases h with ⟨f, hf, hinj, hcomp⟩
  let S := Submonoid.powers f
  let L := localizedSectionMap f s
  obtain ⟨gl, hgl⟩ := left_inverse_of_complemented
    (A := Localization.Away f) (N := LocalizedModule.Away f M)
    (F := LocalizedModule.Away f (Fin r →₀ R)) L hinj hcomp
  let glR : LocalizedModule S M →ₗ[R] LocalizedModule S (Fin r →₀ R) :=
    gl.restrictScalars R
  let fM : M →ₗ[R] LocalizedModule S M := LocalizedModule.mkLinearMap S M
  let fF : (Fin r →₀ R) →ₗ[R] LocalizedModule S (Fin r →₀ R) :=
    LocalizedModule.mkLinearMap S (Fin r →₀ R)
  let LR : LocalizedModule S (Fin r →₀ R) →ₗ[R] LocalizedModule S M :=
    L.restrictScalars R
  obtain ⟨g, a, hga⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    (M := M) (N := Fin r →₀ R) (N' := LocalizedModule.Away f (Fin r →₀ R))
    S fF (glR.comp fM)
  have hmap : fM.comp (Finsupp.linearCombination R s) = LR.comp fF := by
    apply LinearMap.ext
    intro z
    simp [L, LR, fM, fF, localizedSectionMap, LocalizedModule.map_mk]
  have hglR : glR.comp LR = LinearMap.id := by
    apply LinearMap.ext
    intro z
    exact LinearMap.congr_fun hgl z
  have hcomp' : fF.comp (g.comp (Finsupp.linearCombination R s)) = a • fF := by
    calc
      fF.comp (g.comp (Finsupp.linearCombination R s)) =
          (fF.comp g).comp (Finsupp.linearCombination R s) := by
            rfl
      _ = (a • glR.comp fM).comp (Finsupp.linearCombination R s) := by rw [hga]
      _ = a • (glR.comp (fM.comp (Finsupp.linearCombination R s))) := by
            ext z
            rfl
      _ = a • (glR.comp (LR.comp fF)) := by rw [hmap]
      _ = a • fF := by
            rw [← LinearMap.comp_assoc, hglR]
            simp
  let g₁ : (Fin r →₀ R) →ₗ[R] (Fin r →₀ R) :=
    g.comp (Finsupp.linearCombination R s)
  let g₂ : (Fin r →₀ R) →ₗ[R] (Fin r →₀ R) := a • LinearMap.id
  have hcomp'' : fF.comp g₁ = fF.comp g₂ := by
    calc
      fF.comp g₁ = a • fF := by simpa [g₁] using hcomp'
      _ = fF.comp g₂ := by
        ext z
        dsimp [g₂]
        change (a : R) • fF (Finsupp.single z 1) =
          fF ((a : R) • Finsupp.single z 1)
        rw [map_smul]
  obtain ⟨b, hb⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule
    (M := Fin r →₀ R) (N := Fin r →₀ R)
      (N' := LocalizedModule.Away f (Fin r →₀ R))
    S fF g₁ g₂ hcomp''
  refine ⟨(b : R) * (a : R), ?_, b • g, ?_⟩
  · intro hba
    apply hf
    have hprime : x.asIdeal.IsPrime := x.isMaximal.isPrime
    have hpow : ∀ {q : R}, q ∈ Submonoid.powers f →
        q ∈ x.asIdeal → f ∈ x.asIdeal := by
      intro q hq hqI
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff q f).mp hq
      apply hprime.mem_of_pow_mem n
      rw [hn]
      exact hqI
    have hbpow : (b : R) ∈ Submonoid.powers f := by simp [S]
    have hapow : (a : R) ∈ Submonoid.powers f := by simp [S]
    rcases hprime.mem_or_mem hba with hbI | haI
    · exact hpow hbpow hbI
    · exact hpow hapow haI
  · calc
      (b • g).comp (Finsupp.linearCombination R s) =
          b • (g.comp (Finsupp.linearCombination R s)) := by
            rw [LinearMap.smul_comp]
      _ = b • g₁ := by rfl
      _ = b • g₂ := hb
      _ = ((b : R) * (a : R)) • LinearMap.id := by
        dsimp [g₂]
        rw [smul_smul]
        exact congrArg (fun c : R => c • LinearMap.id) (Submonoid.coe_mul S b a)

/- This is the source's assertion that the displayed map becomes the
   inclusion of a direct summand after inverting `f`. -/
theorem which_elements_split [Module.FinitePresentation R M]
    (x : MaximalSpectrum R) {r : ℕ} (s : Fin r → M) :
    (∃ f : R, f ∉ x.asIdeal ∧ IsLocalizedDirectSummand f s) ↔
      LinearIndependent (residueField x)
        (fun i => fibreToV x (fibreClass x (s i))) := by
  sorry
/-
  constructor
  · intro h
    obtain ⟨d, hd, g, hg⟩ := smul_left_inverse_of_directSummand x s h
    rw [linearIndependent_iff]
    intro c hc
    have hB : Finsupp.linearCombination (residueField x)
        (fun i => fibreToV x (fibreClass x (s i))) c = 0 := hc
    have hB' : Finsupp.linearCombination (residueField x)
        (fun i => fibreClass x (s i)) c ∈ B (M := M) x := by
      apply (Submodule.Quotient.mk_eq_zero (B (M := M) x)).mp
      have hmapq : (B (M := M) x).mkQ
          (Finsupp.linearCombination (residueField x)
            (fun i => fibreClass x (s i)) c) =
          Finsupp.linearCombination (residueField x)
            (fun i => fibreToV x (fibreClass x (s i))) c := by
        exact map_finsupp_linearCombination (B (M := M) x).mkQ
          (fun i => fibreClass x (s i)) c
      change (B (M := M) x).mkQ
        (Finsupp.linearCombination (residueField x)
          (fun i => fibreClass x (s i)) c) = 0
      rw [hmapq]
      exact hB
    rw [B, Submodule.mem_iInf] at hB'
    have hmat (i j : Fin r) :
        ((Finsupp.lapply i).comp g) (s j) = d * if i = j then 1 else 0 := by
      have h := congrArg (fun k => k (Finsupp.single j 1)) hg
      have h' := congrArg (fun z : Fin r →₀ R => z i) h
      simpa [LinearMap.comp_apply, Finsupp.single_apply, eq_comm] using h'
    apply Finsupp.ext
    intro i
    have hzero := hB' ((Finsupp.lapply i).comp g)
    have hzero' : ∑ j, c j * algebraMap R (residueField x)
        (((Finsupp.lapply i).comp g) (s j)) = 0 := by
      have hzero'' : Finsupp.linearCombination (residueField x)
          (fun j => fibreDualMap x ((Finsupp.lapply i).comp g)
            (fibreClass x (s j))) c = 0 := by
        rw [← map_finsupp_linearCombination
          (q := fibreDualMap x ((Finsupp.lapply i).comp g))
          (v := fun j => fibreClass x (s j)) (c := c)]
        exact hzero
      rw [finsupp_linearCombination_eq_sum] at hzero''
      simpa [fibreDualMap_fibreClass, smul_eq_mul, mul_comm] using hzero''
    have hdK : algebraMap R (residueField x) d ≠ 0 := by
      intro hzero
      exact hd (Ideal.algebraMap_residueField_eq_zero.mp hzero)
    have hsum_i :
        (∑ j, c j * algebraMap R (residueField x)
          (d * if i = j then 1 else 0)) =
          algebraMap R (residueField x) d * c i := by
      rw [Finset.sum_eq_single i]
      · simp [mul_comm]
      · intro j hj hji
        simp
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    have hci : algebraMap R (residueField x) d * c i = 0 := by
      rw [← hsum_i]
      simpa [hmat] using hzero'
    exact (mul_eq_zero.mp hci).resolve_left hdK
  · intro h
    classical
    let K := residueField x
    let a : Fin r → (M →ₗ[R] R) → K :=
      fun i φ => algebraMap R K (φ (s i))
    have hla : LinearIndependent K a := by
      rw [linearIndependent_iff]
      intro c hc
      have hmem : Finsupp.linearCombination K
          (fun i => fibreClass x (s i)) c ∈ B (M := M) x := by
        rw [B, Submodule.mem_iInf]
        intro φ
        have hφ := congrFun hc φ
        have hφ' : Finsupp.linearCombination K
            (fun i => fibreDualMap x φ (fibreClass x (s i))) c = 0 := by
          rw [finsupp_linearCombination_eq_sum] at hφ ⊢
          simpa [a, fibreDualMap_fibreClass] using hφ
        change fibreDualMap x φ
          (Finsupp.linearCombination K (fun i => fibreClass x (s i)) c) = 0
        rw [map_finsupp_linearCombination]
        exact hφ'
      apply h
      have hmapq : (B (M := M) x).mkQ
          (Finsupp.linearCombination K
            (fun i => fibreClass x (s i)) c) =
          Finsupp.linearCombination K
            (fun i => fibreToV x (fibreClass x (s i))) c := by
        exact map_finsupp_linearCombination (B (M := M) x).mkQ
          (fun i => fibreClass x (s i)) c
      rw [← hmapq]
      exact (Submodule.Quotient.mk_eq_zero (B (M := M) x)).2 hmem
    have hspan : Submodule.span K (Set.range (flip a)) = ⊤ :=
      span_flip_eq_top_iff_linearIndependent.mpr hla
    have htop : (⊤ : Submodule K (Fin r → K)) ≤
        ⨆ φ : M →ₗ[R] R, Submodule.span K {flip a φ} := by
      rw [← hspan]
      apply Submodule.span_le.2
      rintro z ⟨φ, rfl⟩
      exact (le_iSup (fun φ : M →ₗ[R] R => Submodule.span K {flip a φ}) φ)
        (Submodule.subset_span (Set.mem_singleton _))
    have hfin := CompleteLattice.IsCompactElement.exists_finset_of_le_iSup
      (Submodule K (Fin r → K))
      (compactElement_of_fg (Module.Finite.fg_top (R := K) (M := Fin r → K)))
      (fun φ : M →ₗ[R] R => Submodule.span K {flip a φ}) htop
    rcases hfin with ⟨T, hT⟩
    let T₀ := {φ : M →ₗ[R] R // φ ∈ T}
    letI : Fintype T₀ := Fintype.ofFinite T₀
    let mat : (T₀ → K) →ₗ[K] (Fin r → K) :=
      { toFun := fun c i => ∑ φ : T₀, c φ * a i φ
        map_add' := by
          intro c d
          ext i
          simp [add_mul, Finset.sum_add_distrib]
        map_smul' := by
          intro c d
          ext i
          simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
          rw [Finset.mul_sum]
          simp only [mul_assoc] }
    have hT' : (⊤ : Submodule K (Fin r → K)) ≤
        ⨆ φ : T₀, Submodule.span K {flip a (φ : M →ₗ[R] R)} := by
      apply le_trans hT
      refine iSup_le fun φ => iSup_le fun hφ => ?_
      exact le_iSup_of_le ⟨φ, hφ⟩ le_rfl
    have hrange : (⨆ φ : T₀,
        Submodule.span K {flip a (φ : M →ₗ[R] R)}) ≤ LinearMap.range mat := by
      refine iSup_le fun φ => ?_
      apply Submodule.span_le.2
      rintro z rfl
      refine ⟨fun ψ => if ψ = φ then 1 else 0, ?_⟩
      ext i
      simp only [mat, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Finset.sum_eq_single φ]
      · simp [flip]
      · intro ψ hψ hψφ
        simp
      · intro hnot
        exact (hnot (Finset.mem_univ φ)).elim
    have hsurj : Function.Surjective mat := by
      intro z
      have hz : z ∈ LinearMap.range mat := by
        apply hT'.trans hrange
        simp
      exact hz
    have hrange_top : LinearMap.range mat = ⊤ := by
      apply top_unique
      intro z hz
      exact hsurj z
    obtain ⟨q, hq⟩ := LinearMap.exists_rightInverse_of_surjective mat hrange_top
    let e : Fin r → Fin r → K := fun i => Pi.single i 1
    have hcoeff (i : Fin r) (φ : T₀) :
        ∃ c : R, algebraMap R K c = q (e i) φ :=
      x.asIdeal.algebraMap_residueField_surjective (q (e i) φ)
    choose c hc using hcoeff
    let ψ : Fin r → M →ₗ[R] R := fun i =>
      ∑ φ : T₀, c i φ • (φ : M →ₗ[R] R)
    let A : Matrix (Fin r) (Fin r) R := fun i j => ψ i (s j)
    have hA (i j : Fin r) : algebraMap R K (A i j) = if i = j then 1 else 0 := by
      have hq' := congrFun (congrArg (fun l => l (e i)) hq) j
      have hq'' :
          ∑ φ : T₀, (algebraMap R K) (c i φ) * a j (φ : M →ₗ[R] R) =
            e i j := by
        simpa [A, ψ, a, mat, e, hc, map_sum, map_smul, mul_comm] using hq'
      have hsingle : e i j = if i = j then 1 else 0 := by
        by_cases hij : i = j
        · subst j
          simp [e]
        · simp [e]
      calc
        algebraMap R K (A i j) =
            ∑ φ : T₀, (algebraMap R K) (c i φ) * a j (φ : M →ₗ[R] R) := by
              simp [A, ψ, a]
        _ = e i j := hq''
        _ = if i = j then 1 else 0 := hsingle
    have hdet : algebraMap R K A.det = 1 := by
      calc
        algebraMap R K A.det = Matrix.det (fun i j => algebraMap R K (A i j)) := by
          change algebraMap R K A.det = ((algebraMap R K).mapMatrix A).det
          exact RingHom.map_det (algebraMap R K) A
        _ = Matrix.det (1 : Matrix (Fin r) (Fin r) K) := by
          congr 1
          ext i j
          rw [hA]
          by_cases hij : i = j
          · subst j; simp
          · simp
        _ = 1 := Matrix.det_one
    have hdet_not_mem : A.det ∉ x.asIdeal := by
      intro hdet_mem
      have hz := (Ideal.algebraMap_residueField_eq_zero (I := x.asIdeal)).2 hdet_mem
      rw [hdet] at hz
      simp at hz
    let gFun : M →ₗ[R] (Fin r → R) :=
      { toFun := fun m i => ∑ k, A.adjugate i k * ψ k m
        map_add' := by
          intro m n
          ext i
          simp [mul_add, Finset.sum_add_distrib]
        map_smul' := by
          intro r₀ m
          ext i
          simp }
    let eF : (Fin r →₀ R) ≃ₗ[R] (Fin r → R) :=
      Finsupp.linearEquivFunOnFinite R R (Fin r)
    let g : M →ₗ[R] (Fin r →₀ R) := eF.symm.toLinearMap.comp gFun
    have hadj (i j : Fin r) :
        ∑ k, A.adjugate i k * A k j = A.det * if i = j then 1 else 0 := by
      have h := congrFun (congrFun (Matrix.adjugate_mul A) i) j
      have hone : (1 : Matrix (Fin r) (Fin r) R) i j =
          if i = j then 1 else 0 := by
          by_cases hij : i = j
          · subst j; simp
          · simp
      simpa [Matrix.mul_apply, smul_eq_mul, hone] using h
    have hg : g.comp (Finsupp.linearCombination R s) = A.det • LinearMap.id := by
      apply LinearMap.ext
      intro z
      apply eF.injective
      change eF (eF.symm (gFun (Finsupp.linearCombination R s z))) =
        eF (A.det • z)
      rw [eF.apply_symm_apply]
      ext i
      rw [finsupp_linearCombination_eq_sum]
      simp [gFun, eF, map_sum, map_smul, smul_eq_mul]
      have hψA (k j : Fin r) : ψ k (s j) = A k j := by rfl
      simp_rw [hψA]
      calc
        (∑ x, z x * ∑ k, A.adjugate i k * A k x) =
            ∑ x, z x * (A.det * if i = x then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hadj i j]
        _ = A.det * z i := by
          rw [Finset.sum_eq_single i]
          · simp [mul_comm]
          · intro j hj hji
            simp
          · intro hi
            exact (hi (Finset.mem_univ i)).elim
    exact ⟨A.det, hdet_not_mem, directSummand_of_smul_left_inverse A.det s g hg⟩ -/

/-! ## The dependence locus and prescribed values -/

def Z {r : ℕ} (s : Fin r → M) : Set (MaximalSpectrum R) :=
  {x | ¬ LinearIndependent (residueField x)
    (fun i => fibreToV x (fibreClass x (s i)))}

theorem isClosed_Z [Module.FinitePresentation R M]
    {r : ℕ} (s : Fin r → M) : IsClosed (Z (R := R) s) := by
  apply isClosed_compl_iff.mpr
  have hopen : IsOpen (⋃ f : R,
      {x : MaximalSpectrum R | f ∉ x.asIdeal ∧ IsLocalizedDirectSummand f s}) := by
    refine isOpen_iUnion fun f => ?_
    by_cases hf : IsLocalizedDirectSummand f s
    · have hbasic : IsOpen {x : MaximalSpectrum R | f ∉ x.asIdeal} := by
        have h : IsOpen ((fun x : MaximalSpectrum R => MaximalSpectrum.toPrimeSpectrum x) ⁻¹'
            PrimeSpectrum.basicOpen f) :=
          (PrimeSpectrum.isOpen_basicOpen (R := R) (a := f)).preimage
            MaximalSpectrum.toPrimeSpectrum_continuous
        convert h using 1
        ext x
        change MaximalSpectrum.toPrimeSpectrum x ∈ PrimeSpectrum.basicOpen f ↔
          f ∉ x.asIdeal
        rw [PrimeSpectrum.mem_basicOpen]
        rfl
      simpa [hf] using hbasic
    · have hempty : {x : MaximalSpectrum R |
          f ∉ x.asIdeal ∧ IsLocalizedDirectSummand f s} = ∅ := by
        ext y
        simp [hf]
      rw [hempty]
      exact isOpen_empty
  change IsOpen {y : MaximalSpectrum R |
      LinearIndependent (residueField y)
        (fun i => fibreToV y (fibreClass y (s i)))}
  rw [show {y : MaximalSpectrum R |
      LinearIndependent (residueField y)
        (fun i => fibreToV y (fibreClass y (s i)))} = ⋃ f : R,
      {x : MaximalSpectrum R | f ∉ x.asIdeal ∧ IsLocalizedDirectSummand f s} by
    ext y
    constructor
    · intro hy
      obtain ⟨f, hf, hsplit⟩ :=
        (which_elements_split (M := M) (R := R) y s).mpr hy
      exact mem_iUnion.2 ⟨f, hf, hsplit⟩
    · intro hy
      rcases mem_iUnion.1 hy with ⟨f, hf, hsplit⟩
      have hy' := (which_elements_split (M := M) (R := R) y s).mp ⟨f, hf, hsplit⟩
      exact hy']
  exact hopen

theorem choose_values {n : ℕ} (x : Fin n → MaximalSpectrum R)
    (hx : Pairwise (fun i j => x i ≠ x j))
    (v : ∀ i, V (M := M) (x i)) :
    ∃ s : M, ∀ i, fibreToV (x i) (fibreClass (x i) s) = v i := by
  classical
  have hsurj (y : MaximalSpectrum R) :
      Function.Surjective (fibreClass (M := M) y) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp [fibreClass]⟩
    | tmul a m =>
        obtain ⟨r, hr⟩ := y.asIdeal.algebraMap_residueField_surjective a
        refine ⟨r • m, ?_⟩
        rw [fibreClass, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
        rw [Algebra.smul_def, mul_one, hr]
    | add a b ha hb =>
        rcases ha with ⟨m, hm⟩
        rcases hb with ⟨n, hn⟩
        refine ⟨m + n, ?_⟩
        rw [fibreClass, TensorProduct.tmul_add]
        simpa [fibreClass] using congrArg₂ (· + ·) hm hn
  have hq (i : Fin n) : Function.Surjective (fibreToV (x i)) :=
    (b_fibre_v_short_exact (M := M) (R := R) (x i)).2.2
  choose z hz using fun i => hq i (v i)
  choose m hm using fun i => hsurj (x i) (z i)
  have hcop : Pairwise (fun i j => IsCoprime (x i).asIdeal (x j).asIdeal) := by
    intro i j hij
    apply Ideal.isCoprime_of_isMaximal
    exact fun heq => hx hij (MaximalSpectrum.ext heq)
  have hcrt (i : Fin n) : ∃ e : R, ∀ j,
      algebraMap R (residueField (x j)) e = if i = j then 1 else 0 := by
    obtain ⟨e, he⟩ := Ideal.exists_forall_sub_mem_ideal hcop
      (fun j => if i = j then 1 else 0)
    refine ⟨e, fun j => ?_⟩
    have hz' := (Ideal.algebraMap_residueField_eq_zero (I := (x j).asIdeal)).2 (he j)
    rw [map_sub] at hz'
    simpa using sub_eq_zero.mp hz'
  choose e he using hcrt
  refine ⟨∑ i, e i • m i, ?_⟩
  intro j
  have hsum : fibreClass (x j) (∑ i, e i • m i) =
      ∑ i, (algebraMap R (residueField (x j)) (e i)) • fibreClass (x j) (m i) := by
    simp [fibreClass, TensorProduct.tmul_sum, TensorProduct.tmul_smul]
  rw [hsum, Finset.sum_eq_single j]
  · rw [he j j]
    simp [hm j, hz j]
  · intro i hi hij
    rw [he i j]
    simp [hij]
  · intro hnot
    exact (hnot (Finset.mem_univ j)).elim

/-! ## Noetherian codimension bookkeeping -/

/- `irreducibleComponents F` is formed in the subspace `F`; this predicate is
   its ambient-space formulation, which is the form needed for codimension in
   `Ω`. -/
def IsAmbientIrreducibleComponent {X : Type u} [TopologicalSpace X]
    (F : Set X) (Y : TopologicalSpace.IrreducibleCloseds X) : Prop :=
  (Y : Set X) ⊆ F ∧
    ∀ Z : TopologicalSpace.IrreducibleCloseds X,
      (Z : Set X) ⊆ F → (Y : Set X) ⊆ Z → Z = Y

def ComponentsHaveCodimensionAtLeast {X : Type u} [TopologicalSpace X]
    (F : Set X) (k : ℕ) : Prop :=
  ∀ Y : TopologicalSpace.IrreducibleCloseds X,
    IsAmbientIrreducibleComponent F Y →
      (k : ℕ∞) ≤ Formalization.Books.Topology.Unit11.codimension Y

/- The proposition below is the source's Serre induction step.  The finite
   index types encode the displayed finite lists of sections and points. -/
theorem proposition_splitting
    [Module.FinitePresentation R M]
    [TopologicalSpace.NoetherianSpace (MaximalSpectrum R)]
    {h : ℕ} (s : Fin h → M) (F : Set (MaximalSpectrum R))
    (hF : IsClosed F) (hZF : Z (R := R) s ⊆ F)
    {n : ℕ} (x : Fin n → MaximalSpectrum R)
    (hxF : ∀ i, x i ∈ F)
    (hx : Pairwise (fun i j => x i ≠ x j))
    (v : ∀ i, V (M := M) (x i)) (k : ℕ)
    (hbound : ∀ y : MaximalSpectrum R,
      h + k ≤ Module.finrank (residueField y) (V (M := M) y)) :
    ∃ t : M, ∃ F' : Set (MaximalSpectrum R),
      IsClosed F' ∧
      (∀ i, fibreToV (x i) (fibreClass (x i) t) = v i) ∧
      Z (R := R) (Fin.snoc s t) ⊆ F ∪ F' ∧
      ComponentsHaveCodimensionAtLeast F' k := by
  sorry

/-! ## Splitting off a free summand -/

/- A free direct summand of a localized module is represented by a
   complemented submodule carrying the canonical `Module.Free` instance. -/
def HasFreeDirectSummandAbove (A N : Type u) [CommRing A]
    [AddCommGroup N] [Module A N] (d : ℕ) : Prop :=
  ∃ K : Submodule A N,
    IsComplemented K ∧ Module.Free A K ∧
      (d : Cardinal) < Module.rank A K

theorem splitting_off_free
    [Module.FinitePresentation R M]
    [TopologicalSpace.NoetherianSpace (MaximalSpectrum R)]
    (d : ℕ)
    (hdim : topologicalKrullDim (MaximalSpectrum R) = d)
    (hfree : ∀ m : MaximalSpectrum R,
      HasFreeDirectSummandAbove (Localization.AtPrime m.asIdeal)
        (LocalizedModule.AtPrime m.asIdeal M) d) :
    ∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module R M'),
      Nonempty (M ≃ₗ[R] R × M') := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit128
