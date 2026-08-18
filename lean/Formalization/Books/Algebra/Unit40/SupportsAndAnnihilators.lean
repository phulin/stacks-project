import Formalization.Books.Algebra.Unit03.BasicNotions
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Spectrum.Prime.Module
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Commutative Algebra, Chapter 40: supports and annihilators

The source's support and annihilator constructions are represented by Mathlib's canonical
`Module.support`, `Module.annihilator`, and the earlier chapter's `annihilatorOf`.  The
source-facing interfaces below record the statements that are not already available under a
chapter-specific name.
-/

namespace Formalization.Books.Algebra.Unit40

open Set
open scoped TensorProduct

universe u v

noncomputable section

/-! ## Support and annihilators -/

/- The definition in the source is Mathlib's `Module.support R M`: the primes at which
   `LocalizedModule p.asIdeal.primeCompl M` is nontrivial. -/

/- The source's zero module is represented by the canonical `Subsingleton M` proposition. -/
theorem support_eq_empty_iff {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    Module.support R M = ∅ ↔ Subsingleton M :=
  Module.support_eq_empty_iff

/- The proof notes the stronger maximal-ideal consequence; it is recorded explicitly here. -/
theorem exists_maximal_mem_support {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Nontrivial M] :
    ∃ p : PrimeSpectrum R, p.asIdeal.IsMaximal ∧ p ∈ Module.support R M := by
  obtain ⟨p, hp⟩ := Module.nonempty_support_of_nontrivial (R := R) (M := M)
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
  refine ⟨⟨m, hm.isPrime⟩, hm, ?_⟩
  exact Module.mem_support_mono hpm hp

/- The earlier chapter's `annihilatorOf` is definitionally this span-annihilator expression;
   the source-facing theorem is stated using Mathlib's universe-polymorphic form. -/
theorem annihilator_element_mem_iff {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (m : M) (r : R) :
    r ∈ Formalization.Books.Algebra.Unit03.annihilatorOf m ↔ r • m = 0 :=
  Formalization.Books.Algebra.Unit03.annihilatorOf_mem_iff m r

/- `Module.annihilator R M` is Mathlib's canonical ideal of scalars annihilating every
   element of `M`. -/
theorem annihilator_module_mem_iff {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (r : R) :
    r ∈ Module.annihilator R M ↔ ∀ m : M, r • m = 0 :=
  Module.mem_annihilator

/-! ### Flat base change of annihilators -/

theorem annihilator_element_flat_base_change
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module.Flat R S] (m : M) :
    (Formalization.Books.Algebra.Unit03.annihilatorOf m).map (algebraMap R S) =
      Formalization.Books.Algebra.Unit03.annihilatorOf ((1 : S) ⊗ₜ[R] m) := by
  change (Submodule.span R ({m} : Set M)).annihilator.map (algebraMap R S) =
    (Submodule.span S ({(1 : S) ⊗ₜ[R] m} : Set (S ⊗[R] M))).annihilator
  rw [Submodule.annihilator_span_singleton, Submodule.annihilator_span_singleton]
  let f : R →ₗ[R] M := LinearMap.toSpanSingleton R M m
  have h_exact : Function.Exact (LinearMap.ker f).subtype f := f.exact_subtype_ker_map
  have h_exact' := Module.Flat.lTensor_exact S h_exact
  have hker : LinearMap.ker (f.lTensor S) =
      LinearMap.range ((LinearMap.ker f).subtype.lTensor S) :=
    h_exact'.linearMap_ker_eq
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change (LinearMap.toSpanSingleton S (S ⊗[R] M) (1 ⊗ₜ[R] m))
      (algebraMap R S r) = 0
    rw [LinearMap.toSpanSingleton_apply]
    simpa [f] using congrArg (fun x => (1 : S) ⊗ₜ[R] x) (show f r = 0 from hr)
  · intro s hs
    have hs' : (s ⊗ₜ[R] (1 : R)) ∈ LinearMap.ker (f.lTensor S) := by
      change (f.lTensor S) (s ⊗ₜ[R] (1 : R)) = 0
      have hcalc : (f.lTensor S) (s ⊗ₜ[R] (1 : R)) = s ⊗ₜ[R] f 1 := by rfl
      rw [hcalc]
      rw [show f 1 = m by simp [f]]
      rw [TensorProduct.tmul_eq_smul_one_tmul]
      exact (LinearMap.toSpanSingleton_apply S (S ⊗[R] M) (1 ⊗ₜ[R] m) s).symm ▸ hs
    obtain ⟨y, hy⟩ := (LinearMap.mem_range.mp (hker ▸ hs'))
    have hmem : ∀ (y : S ⊗[R] LinearMap.ker f) (s : S),
        (LinearMap.lTensor S (LinearMap.ker f).subtype) y = s ⊗ₜ[R] (1 : R) →
          s ∈ Ideal.map (algebraMap R S) (LinearMap.ker (LinearMap.toSpanSingleton R M m)) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero =>
          intro s hs
          have hs0 := congrArg (TensorProduct.rid R S) hs
          simp at hs0
          simpa [hs0] using (Ideal.map (algebraMap R S)
            (LinearMap.ker (LinearMap.toSpanSingleton R M m))).zero_mem
      | add x y hx hy =>
          intro s hs
          have hs' := congrArg (TensorProduct.rid R S) hs
          have hxy : s = (TensorProduct.rid R S)
              ((LinearMap.lTensor S (LinearMap.ker f).subtype) x) +
              (TensorProduct.rid R S)
                ((LinearMap.lTensor S (LinearMap.ker f).subtype) y) := by
            simpa using hs'.symm
          subst s
          exact (Ideal.map (algebraMap R S)
            (LinearMap.ker (LinearMap.toSpanSingleton R M m))).add_mem
            (hx _ (by
              rw [← TensorProduct.rid_symm_apply]
              exact ((TensorProduct.rid R S).symm_apply_apply _).symm))
            (hy _ (by
              rw [← TensorProduct.rid_symm_apply]
              exact ((TensorProduct.rid R S).symm_apply_apply _).symm))
      | tmul s' i =>
          intro s hs
          have hs' := congrArg (TensorProduct.rid R S) hs
          have hi : algebraMap R S (i : R) ∈
              Ideal.map (algebraMap R S) (LinearMap.ker (LinearMap.toSpanSingleton R M m)) :=
            Ideal.mem_map_of_mem (algebraMap R S) i.property
          have hsi := (Ideal.map (algebraMap R S)
            (LinearMap.ker (LinearMap.toSpanSingleton R M m))).mul_mem_left s' hi
          have hs'' : (i : R) • s' = s := by simpa using hs'
          rw [← hs'']
          simpa [Algebra.smul_def, mul_comm] using hsi
    exact hmem y s hy

private lemma ideal_map_inf_of_flat
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (I J : Ideal R) :
    (I ⊓ J).map (algebraMap R S) =
      I.map (algebraMap R S) ⊓ J.map (algebraMap R S) := by
  let lmapS : ∀ K : Ideal R, S ⊗[R] K →ₗ[S] S :=
    fun K => (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap.comp
      (TensorProduct.AlgebraTensorModule.map (LinearMap.id : S →ₗ[S] S) K.subtype)
  let lmap : ∀ K : Ideal R, S ⊗[R] K →ₗ[R] S :=
    fun K => (lmapS K).restrictScalars R
  have hrangeS (K : Ideal R) :
      LinearMap.range (lmapS K) = K.map (algebraMap R S) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      induction x using TensorProduct.induction_on with
      | zero => exact (K.map (algebraMap R S)).zero_mem
      | add x y hx hy => simpa only [map_add] using (K.map (algebraMap R S)).add_mem hx hy
      | tmul s k =>
          simpa [lmapS, Algebra.smul_def, mul_comm] using
            (K.map (algebraMap R S)).mul_mem_left s
              (Ideal.mem_map_of_mem (algebraMap R S) k.property)
    · rw [Ideal.map, Submodule.span_le]
      rintro _ ⟨k, hk, rfl⟩
      exact LinearMap.mem_range.mpr ⟨(1 : S) ⊗ₜ[R] (⟨k, hk⟩ : K), by
        simp [lmapS, Algebra.smul_def]⟩
  have hrange (K : Ideal R) :
      LinearMap.range (lmap K) = (K.map (algebraMap R S)).restrictScalars R := by
    simp only [lmap, LinearMap.range_restrictScalars, hrangeS]
  let hR : (I × J) →ₗ[R] R :=
    { toFun := fun x => (x.1 : R) - (x.2 : R)
      map_add' := by intro x y; simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      map_smul' := by intro r x; simp [mul_sub] }
  let f : (I × J) →ₗ[R] ↥(I ⊔ J) :=
    hR.codRestrict (I ⊔ J) (by
      intro x
      exact sub_mem (Submodule.mem_sup_left x.1.property)
        (Submodule.mem_sup_right x.2.property))
  let d : ↥(I ⊓ J) →ₗ[R] (I × J) :=
    { toFun := fun x =>
        (⟨(x : R), x.property.1⟩, ⟨(x : R), x.property.2⟩)
      map_add' := by intro x y; rfl
      map_smul' := by intro r x; rfl }
  have h_exact : Function.Exact d f := by
    rw [LinearMap.exact_iff]
    apply le_antisymm
    · intro x hx
      have hx0 : hR x = 0 := by
        exact congrArg Subtype.val (LinearMap.mem_ker.mp hx)
      have hxval : (x.1 : R) = (x.2 : R) := sub_eq_zero.mp hx0
      let z : ↥(I ⊓ J) :=
        ⟨(x.1 : R), ⟨x.1.property, hxval ▸ x.2.property⟩⟩
      refine LinearMap.mem_range.mpr ⟨z, ?_⟩
      apply Prod.ext <;> apply Subtype.ext
      · rfl
      · have : (x.1 : R) = (x.2 : R) := sub_eq_zero.mp hx0
        exact this
    · rintro x ⟨z, rfl⟩
      exact LinearMap.mem_ker.mpr (Subtype.ext (sub_self (z : R)))
  have h_exact' := Module.Flat.lTensor_exact S h_exact
  let pI : I × J →ₗ[R] I :=
    { toFun := Prod.fst
      map_add' := by intro x y; rfl
      map_smul' := by intro r x; rfl }
  let pJ : I × J →ₗ[R] J :=
    { toFun := Prod.snd
      map_add' := by intro x y; rfl
      map_smul' := by intro r x; rfl }
  have hfcomp :
      ((I ⊔ J).subtype.lTensor S).comp (f.lTensor S) = hR.lTensor S := by
    rw [← LinearMap.lTensor_comp]
    rfl
  have hpair :
      (TensorProduct.rid R S).comp (hR.lTensor S) =
        (lmap I).comp (pI.lTensor S) - (lmap J).comp (pJ.lTensor S) := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
        simpa only [map_add, LinearMap.sub_apply] using congrArg₂ (fun u v => u + v) hx hy
    | tmul s x =>
        simp [hR, lmap, lmapS, pI, pJ, Algebra.smul_def, sub_eq_add_neg,
          mul_add, mul_comm]
  have hdi :
      ((lmap I).comp (pI.lTensor S)).comp (d.lTensor S) = lmap (I ⊓ J) := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
        simp only [map_add]
        rw [hx, hy]
    | tmul s z => simp [lmap, lmapS, pI, d, Algebra.smul_def]
  apply le_antisymm
  · exact le_inf (Ideal.map_mono inf_le_left) (Ideal.map_mono inf_le_right)
  · intro x hx
    have hxI : x ∈ (I.map (algebraMap R S)).restrictScalars R := hx.1
    have hxJ : x ∈ (J.map (algebraMap R S)).restrictScalars R := hx.2
    rw [← hrange I] at hxI
    rw [← hrange J] at hxJ
    rcases hxI with ⟨a, ha⟩
    rcases hxJ with ⟨b, hb⟩
    let e := TensorProduct.prodRight R S S I J
    let y := e.symm (a, b)
    have hpi' : (e y).1 = pI.lTensor S y := by
      induction y using TensorProduct.induction_on with
      | zero => simp [e, pI]
      | add u v hu hv => simp [e, pI, hu, hv]
      | tmul s z => rfl
    have hpj' : (e y).2 = pJ.lTensor S y := by
      induction y using TensorProduct.induction_on with
      | zero => simp [e, pJ]
      | add u v hu hv => simp [e, pJ, hu, hv]
      | tmul s z => rfl
    have hpi : pI.lTensor S y = a := by
      rw [← hpi']
      exact congrArg Prod.fst (e.apply_symm_apply (a, b))
    have hpj : pJ.lTensor S y = b := by
      rw [← hpj']
      exact congrArg Prod.snd (e.apply_symm_apply (a, b))
    have hzeroR : hR.lTensor S y = 0 := by
      apply (TensorProduct.rid R S).injective
      change ((TensorProduct.rid R S).comp (hR.lTensor S)) y = 0
      rw [hpair, LinearMap.sub_apply]
      simp only [LinearMap.comp_apply]
      rw [hpi, hpj, ha, hb, sub_self]
    have hzero : f.lTensor S y = 0 := by
      apply Module.Flat.lTensor_preserves_injective_linearMap
        (I ⊔ J).subtype Subtype.val_injective
      change (((I ⊔ J).subtype.lTensor S).comp (f.lTensor S)) y = 0
      rw [hfcomp]
      exact hzeroR
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp
      ((LinearMap.exact_iff.mp h_exact') ▸ LinearMap.mem_ker.mpr hzero)
    have hx' : lmap (I ⊓ J) z = x := by
      calc
        lmap (I ⊓ J) z = lmap I (pI.lTensor S (d.lTensor S z)) := by
          simpa only [LinearMap.comp_apply] using (congrArg (fun g => g z) hdi).symm
        _ = lmap I (pI.lTensor S y) := by rw [hz]
        _ = lmap I a := by rw [hpi]
        _ = x := ha
    have hxK : x ∈ ((I ⊓ J).map (algebraMap R S)).restrictScalars R := by
      rw [← hrange (I ⊓ J)]
      exact ⟨z, hx'⟩
    exact hxK

theorem annihilator_module_flat_base_change
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module.Flat R S] [Module.Finite R M] :
    (Module.annihilator R M).map (algebraMap R S) =
      Module.annihilator S (S ⊗[R] M) := by
  classical
  obtain ⟨s, hs⟩ := ‹Module.Finite R M›
  have hspan (t : Finset M) :
      (Submodule.span R (t : Set M)).annihilator.map (algebraMap R S) =
        (Submodule.span S
          (TensorProduct.mk R S M 1 '' (t : Set M))).annihilator := by
    induction t using Finset.induction_on with
    | empty =>
        simp only [Finset.coe_empty, Set.image_empty, Submodule.span_empty,
          Submodule.annihilator_bot, Ideal.map_top]
    | @insert m t hm ih =>
        simp only [Finset.coe_insert, Set.insert_eq, Set.image_union, Set.image_singleton]
        rw [Submodule.span_union, Submodule.span_union,
          Submodule.annihilator_sup, Submodule.annihilator_sup,
          ideal_map_inf_of_flat, ih]
        have he := annihilator_element_flat_base_change (R := R) (S := S) m
        change (Submodule.span R ({m} : Set M)).annihilator.map (algebraMap R S) =
          (Submodule.span S ({(1 : S) ⊗ₜ[R] m} : Set (S ⊗[R] M))).annihilator at he
        rw [he]
        rfl
  have htop :
      Submodule.span S
          (TensorProduct.mk R S M 1 '' (s : Set M)) = (⊤ : Submodule S (S ⊗[R] M)) := by
    rw [← Submodule.baseChange_span S (s : Set M), hs, Submodule.baseChange_top]
  calc
    (Module.annihilator R M).map (algebraMap R S) =
        (Submodule.span R (s : Set M)).annihilator.map (algebraMap R S) := by
      rw [← Submodule.annihilator_top, ← hs]
    _ = (Submodule.span S
          (TensorProduct.mk R S M 1 '' (s : Set M))).annihilator := hspan s
    _ = Module.annihilator S (S ⊗[R] M) := by
      rw [← Submodule.annihilator_top, htop]

/-! ### Support of finite modules -/

theorem support_closed_of_finite
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    IsClosed (Module.support R M) ∧
      PrimeSpectrum.zeroLocus (Module.annihilator R M : Set R) = Module.support R M := by
  exact ⟨Module.isClosed_support, Module.support_eq_zeroLocus.symm⟩

/- The source's base-change statement is formulated with the canonical algebra structure on the
   target ring; this is the Lean form of a commutative ring map. -/
theorem support_base_change
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.support S (S ⊗[R] M) =
      PrimeSpectrum.comap (algebraMap R S) ⁻¹' Module.support R M := by
  ext q
  let p := PrimeSpectrum.comap (algebraMap R S) q
  change q ∈ Module.support S (S ⊗[R] M) ↔ p ∈ Module.support R M
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    Module.mem_support_iff_nontrivial_residueField_tensorProduct]
  let f : p.asIdeal.ResidueField →ₐ[R] q.asIdeal.ResidueField :=
    Ideal.ResidueField.mapₐ p.asIdeal q.asIdeal (Algebra.ofId R S) (by rfl)
  let eS := TensorProduct.AlgebraTensorModule.cancelBaseChange R S
    q.asIdeal.ResidueField q.asIdeal.ResidueField M
  let eP :=
    letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField := f.toRingHom.toAlgebra
    letI : IsScalarTower R p.asIdeal.ResidueField q.asIdeal.ResidueField :=
      IsScalarTower.of_algebraMap_eq' (by
        ext r
        change algebraMap R q.asIdeal.ResidueField r = f
          (algebraMap R p.asIdeal.ResidueField r)
        exact (f.commutes r).symm)
    TensorProduct.AlgebraTensorModule.cancelBaseChange R p.asIdeal.ResidueField
      q.asIdeal.ResidueField q.asIdeal.ResidueField M
  rw [eS.nontrivial_congr, ← eP.nontrivial_congr]
  rw [Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right]

/- The source's element criterion uses the canonical localization map into
   `LocalizedModule p.asIdeal.primeCompl M`. -/
theorem support_element_iff
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (p : PrimeSpectrum R) (m : M) :
    p ∈ PrimeSpectrum.zeroLocus
      ((Formalization.Books.Algebra.Unit03.annihilatorOf m : Ideal R) : Set R) ↔
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) m ≠ 0 := by
  sorry

/-! ### Finitely presented modules -/

theorem support_finitePresentation_constructible
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] :
    IsClosed (Module.support R M) ∧ IsCompact (Module.support R M)ᶜ := by
  constructor
  · exact Module.isClosed_support
  · sorry

/-! ### Quotients, submodules, and exact sequences -/

theorem support_quotient_by_ideal
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) :
    Module.support R (M ⧸ (I • (⊤ : Submodule R M))) =
      Module.support R M ∩ PrimeSpectrum.zeroLocus (I : Set R) :=
  Module.support_quotient I

theorem support_submodule_subset
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) :
    Module.support R N ⊆ Module.support R M := by
  exact Module.support_subset_of_injective (Submodule.subtype N) Subtype.val_injective

/- A quotient module is represented by a surjective linear map. -/
theorem support_quotient_subset
    {R M Q : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup Q]
    [Module R M] [Module R Q] (q : M →ₗ[R] Q) (hq : Function.Surjective q) :
    Module.support R Q ⊆ Module.support R M :=
  Module.support_subset_of_surjective q hq

theorem support_short_exact
    {R N M Q : Type*} [CommRing R]
    [AddCommGroup N] [AddCommGroup M] [AddCommGroup Q]
    [Module R N] [Module R M] [Module R Q]
    (f : N →ₗ[R] M) (g : M →ₗ[R] Q)
    (hexact : Function.Exact f g) (hinjective : Function.Injective f)
    (hsurjective : Function.Surjective g) :
    Module.support R M = Module.support R Q ∪ Module.support R N := by
  simpa [Set.union_comm] using
    (Module.support_of_exact (f := f) (g := g) hexact hinjective hsurjective)

end
end Formalization.Books.Algebra.Unit40
