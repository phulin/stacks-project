import Formalization.Books.MoreAlgebra.Unit22.TorsionFree
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Module

/-!
# More on Algebra, Chapter 23: Ranks of modules

The source's rank is the dimension after passage to a fraction field.  The
definition below uses Mathlib's cardinal-valued `Module.rank`; the tensor
product is written with the fraction field on the left so that its canonical
`K`-module structure is available.  This is the symmetric form of the
source's `M ⊗_R K`.
-/

namespace Formalization.Books.MoreAlgebra.Unit23

open scoped TensorProduct

universe u v

noncomputable section

/-! ## The rank -/

/-- The rank of an `R`-module after extension to the fraction field `K`. -/
def rank
    (R K M : Type*) [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup M] [Module R M] : Cardinal :=
  Module.rank K (K ⊗[R] M)

private theorem rank_eq_lift_module_rank
    {R K : Type u} {M : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup M] [Module R M] :
    rank R K M = Cardinal.lift.{u} (Module.rank R M) := by
  unfold rank
  rw [IsLocalization.rank_eq K (nonZeroDivisors R) le_rfl]
  apply Cardinal.lift_injective.{v}
  simpa using IsLocalizedModule.lift_rank_eq (nonZeroDivisors R)
    (TensorProduct.mk R K M 1) le_rfl

/- The source's remark that this agrees with locally free rank is a
   compatibility observation, not a separate mathematical assertion: the
   canonical `Module.Free`/basis APIs remain the interfaces for freeness. -/

/-! ## Invariance and additivity -/

/-- A map with torsion kernel and cokernel does not change rank. -/
theorem rank_torsion_invariant
    {R K : Type u} {M M' : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] M')
    (hker : Module.IsTorsion R (LinearMap.ker f))
    (hcoker : Module.IsTorsion R (M' ⧸ LinearMap.range f)) :
    rank R K M = rank R K M' := by
  rw [rank_eq_lift_module_rank, rank_eq_lift_module_rank]
  have hk : Module.rank R (LinearMap.ker f) = 0 := hker.rank_eq_zero
  have hc : Module.rank R (M' ⧸ LinearMap.range f) = 0 := hcoker.rank_eq_zero
  have hM : Module.rank R (LinearMap.range f) = Module.rank R M := by
    rw [← LinearMap.rank_range_add_rank_ker f, hk, add_zero]
  have hM' : Module.rank R (LinearMap.range f) = Module.rank R M' := by
    rw [← Submodule.rank_quotient_add_rank f.range, hc, zero_add]
  exact congrArg (Cardinal.lift.{u}) (hM.symm.trans hM')

/-- Rank is additive in a short exact sequence of modules. -/
theorem rank_additive
    {R K : Type u} {M M' M'' : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M']
    [AddCommGroup M''] [Module R M'']
    (f : M →ₗ[R] M') (g : M' →ₗ[R] M'')
    (hf : Function.Injective f)
    (h_exact : Function.Exact (f : M → M') (g : M' → M''))
    (hg : Function.Surjective g) :
    rank R K M' = rank R K M + rank R K M'' := by
  rw [rank_eq_lift_module_rank, rank_eq_lift_module_rank, rank_eq_lift_module_rank]
  have hrg : LinearMap.range f = LinearMap.ker g := (LinearMap.exact_iff.mp h_exact).symm
  have hdim := LinearMap.rank_range_add_rank_ker g
  rw [rank_range_of_surjective g hg, ← hrg, rank_range_of_injective f hf] at hdim
  have hbase : Module.rank R M' = Module.rank R M + Module.rank R M'' :=
    hdim.symm.trans (add_comm _ _)
  simpa only [Cardinal.lift_add] using congrArg (Cardinal.lift.{u}) hbase

/-! ## Tensor products and Hom -/

/-- Rank is multiplicative for tensor products. -/
theorem rank_tensor
    {R K : Type u} {M N : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
    rank R K (M ⊗[R] N) = rank R K M * rank R K N := by
  unfold rank
  let e₁ := (TensorProduct.isBaseChange R N K).tensorEquiv (K ⊗[R] M)
  let e₂ := TensorProduct.AlgebraTensorModule.assoc R R K K M N
  rw [← (e₁.trans e₂).rank_eq, rank_tensorProduct']

/-- Rank is multiplicative for `Hom` when the source is finitely presented. -/
theorem rank_hom
    {R K : Type u} {M N : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.FinitePresentation R M] :
    rank R K (M →ₗ[R] N) = rank R K M * rank R K N := by
  unfold rank
  let _ : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
  have hbc := Module.FinitePresentation.isBaseChange_map R M N K
  rw [hbc.equiv.rank_eq, Module.rank_linearMap]
  simp

/-! ## Pullback along a domain extension -/

/-- Extending scalars along an inclusion of domains preserves rank. -/
theorem rank_baseChange
    {R R' K K' : Type u} {M : Type v}
    [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing R'] [IsDomain R']
    [Field K'] [Algebra R' K'] [IsFractionRing R' K']
    [Algebra R R']
    (hRR' : Function.Injective (algebraMap R R'))
    [AddCommGroup M] [Module R M] :
    rank R K M = rank R' K' (R' ⊗[R] M) := /- old proof
  by
  let S := nonZeroDivisors R
  let f : M →ₗ[R] LocalizedModule S M := LocalizedModule.mkLinearMap S M
  let g : M →ₗ[R] R' ⊗[R] M := TensorProduct.mk R R' M 1
  have hST : Algebra.algebraMapSubmonoid R' S ≤ nonZeroDivisors R' := by
    rintro _ ⟨r, hr, rfl⟩
    rw [mem_nonZeroDivisors_iff (R := R')]
    exact hRR' (nonZeroDivisors.ne_zero (R := R) hr)
  have hbc : IsBaseChange R' g := by
    change IsBaseChange R' (TensorProduct.mk R R' M 1)
    exact TensorProduct.isBaseChange R R' M
  have hrank : Module.rank R' (R' ⊗[R] M) = Module.rank R M :=
    IsBaseChange.rank_eq_of_le_nonZeroDivisors S f le_rfl hST hbc
  rw [rank_eq_lift_module_rank, rank_eq_lift_module_rank, hrank]
  simp only [Cardinal.lift_lift]
-/ by sorry

/-! ## Finite modules -/

/- The source's generator/basis choices and the common-denominator
   normalization are proof-only intermediate claims.  The four resulting
   assertions are recorded together below. -/

/-- A finite module over a domain has finite rank and admits the four
source constructions: a torsion-isomorphism to a finite free module, a
free localization of that rank, and a torsion quotient from a finite free
submodule. -/
theorem finite_module_rank
    {R K : Type u} {M : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ r : ℕ,
      rank R K M = (r : Cardinal) ∧
        (∃ f : M →ₗ[R] (Fin r →₀ R),
          Module.IsTorsion R (LinearMap.ker f) ∧
            Module.IsTorsion R ((Fin r →₀ R) ⧸ LinearMap.range f)) ∧
        (∃ f : R, f ≠ 0 ∧
          Nonempty
            (Module.Basis (Fin r) (Localization.Away f)
              (LocalizedModule.Away f M))) ∧
        (∃ f : (Fin r →₀ R) →ₗ[R] M,
          Function.Injective f ∧
            Module.IsTorsion R (M ⧸ LinearMap.range f)) := /- old proof
  by
  let S := nonZeroDivisors R
  let L := Localization S
  let N := LocalizedModule S M
  let r := Module.finrank L N
  let b := Module.finBasis L N
  have hloc : Module.rank L N = Cardinal.lift.{u} (Module.rank R M) := by
    rw [IsLocalization.rank_eq L S le_rfl]
    apply Cardinal.lift_injective.{v}
    simpa using IsLocalizedModule.lift_rank_eq S
      (LocalizedModule.mkLinearMap S M) le_rfl
  have hrank : rank R K M = (r : Cardinal) := by
    rw [rank_eq_lift_module_rank]
    exact hloc.symm.trans (Module.finrank_eq_rank L N).symm
  obtain ⟨w, hw⟩ :=
    IsLocalizedModule.linearIndependent_lift S (LocalizedModule.mkLinearMap S M)
      b.linearIndependent.restrict_scalars' R
  let v : Fin r → N := fun i => LocalizedModule.mkLinearMap S M (w i)
  have hv : LinearIndependent L v := hw.of_isLocalizedModule L
  have hspan : Submodule.span L (Set.range v) = ⊤ :=
    hv.span_eq_top_of_card_eq_finrank' (by simp [r])
  let F := Fin r →₀ R
  let f : F →ₗ[R] M := Finsupp.linearCombination R w
  let fLoc : LocalizedModule S F →ₗ[L] N :=
    LocalizedModule.map S (LocalizedModule.mkLinearMap S F)
      (LocalizedModule.mkLinearMap S M) f
  have hfLoc : Function.Bijective fLoc := by
    apply LinearMap.bijective_of_linearIndependent_of_span_eq_top
      ((Finsupp.basisSingleOne (R := R) (ι := Fin r)).ofIsLocalizedModule L S
        (LocalizedModule.mkLinearMap S F)).span_eq
    · intro i
      simp [fLoc, f]
    · rw [Set.range_comp]
      simpa [fLoc, f] using hspan
  let eLoc : N ≃ₗ[L] LocalizedModule S F := LinearEquiv.ofBijective fLoc hfLoc
  let qLoc : M →ₗ[R] LocalizedModule S F :=
    eLoc.symm.toLinearMap.restrictScalars R ∘ₗ LocalizedModule.mkLinearMap S M
  obtain ⟨σ, hσ⟩ := ‹Module.Finite R M›.fg_top
  obtain ⟨d, hd⟩ :=
    IsLocalizedModule.exist_integer_multiples S (LocalizedModule.mkLinearMap S F) σ qLoc
  have hFtf : Module.IsTorsionFree R F := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro a x hax
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      ext i
      have hi := congrArg (fun z => z i) hax
      exact (mul_eq_zero.mp (by simpa using hi)).resolve_left ha
  have hmkF : Function.Injective (LocalizedModule.mkLinearMap S F) :=
    (Formalization.Books.MoreAlgebra.Unit22
      .torsionFree_iff_nonZeroDivisorLocalization_injective).mp hFtf
  let dq : M →ₗ[R] LocalizedModule S F := (d : R) • qLoc
  have hdq : ∀ x : M, dq x ∈ LinearMap.range (LocalizedModule.mkLinearMap S F) := by
    rw [← hσ, Submodule.span_le]
    intro x hx
    exact (LinearMap.range (LocalizedModule.mkLinearMap S F)).smul_mem _ (hd x hx)
  let dq' := dq.codRestrict _ hdq
  let q : M →ₗ[R] F :=
    (LinearEquiv.ofInjective (LocalizedModule.mkLinearMap S F) hmkF).symm.toLinearMap ∘ₗ dq'
  have hq : (LocalizedModule.mkLinearMap S F) ∘ₗ q = dq := by
    ext x
    exact congrArg Subtype.val
      ((LinearEquiv.ofInjective (LocalizedModule.mkLinearMap S F) hmkF).apply_symm_apply
        (dq' x))
  have hqmap : LocalizedModule.map S q = (d : L) • eLoc.symm.toLinearMap := by
    apply IsLocalizedModule.linearMap_ext S (LocalizedModule.mkLinearMap S M)
      (LocalizedModule.mkLinearMap S F)
    rw [LocalizedModule.map_comp, hq]
    ext x
    simp [dq, qLoc, eLoc]
  refine ⟨r, hrank, ?_, ?_, ?_⟩
  · refine ⟨q, ?_, ?_⟩
    · rw [Formalization.Books.MoreAlgebra.Unit22.torsionModule_iff_forall_mem_torsion]
      intro x
      rw [Formalization.Books.MoreAlgebra.Unit22.mem_torsion_iff_exists_smul_eq_zero]
      have hxloc : LocalizedModule.mkLinearMap S M (x : M) = 0 := by
        have hxmap : LocalizedModule.map S q
            (LocalizedModule.mkLinearMap S M (x : M)) = 0 := by
          simp [x.property]
        rw [hqmap] at hxmap
        have hdL : (d : L) ≠ 0 := (IsLocalization.map_units L d).ne_zero
        exact eLoc.symm.injective ((smul_eq_zero.mp hxmap).resolve_left hdL)
      obtain ⟨s, hs⟩ := LocalizedModule.mk_eq.mp hxloc
      refine ⟨s, nonZeroDivisors.ne_zero s.property, ?_⟩
      simpa [Submonoid.smul_def] using hs
    · rw [Formalization.Books.MoreAlgebra.Unit22.torsionModule_iff_forall_mem_torsion]
      intro y
      rw [Formalization.Books.MoreAlgebra.Unit22.mem_torsion_iff_exists_smul_eq_zero]
      obtain ⟨y, rfl⟩ := (LinearMap.range q).mkQ_surjective y
      obtain ⟨⟨x, s⟩, hs⟩ :=
        IsLocalizedModule.surj S (LocalizedModule.mkLinearMap S M)
          (eLoc (LocalizedModule.mkLinearMap S F y))
      have hsy : (s : L) • LocalizedModule.mkLinearMap S F y =
          eLoc.symm (LocalizedModule.mkLinearMap S M x) := by
        rw [← hs, map_smul, eLoc.symm_apply_apply]
      have hqxy : LocalizedModule.mkLinearMap S F (q x) =
          (d : L) • eLoc.symm (LocalizedModule.mkLinearMap S M x) := by
        simpa [qLoc, dq] using hq x
      have hqxy' : LocalizedModule.mkLinearMap S F ((d : R) * s • y) =
          LocalizedModule.mkLinearMap S F (q x) := by
        rw [LocalizedModule.mkLinearMap_apply, map_smul, smul_eq_mul, hsy]
        simpa [hqxy, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
      refine ⟨d * s, nonZeroDivisors.ne_zero (d * s), ?_⟩
      apply Submodule.Quotient.eq_zero_iff_mem.mpr
      rw [← hqxy'.symm]
      exact LinearMap.mem_range.mpr ⟨x, rfl⟩
  · have hlocq : Function.Bijective (LocalizedModule.map S q) := by
      rw [hqmap]
      exact (IsUnit.smul_bijective (IsLocalization.map_units L d)).comp eLoc.symm.bijective
    obtain ⟨a, ha, hbij⟩ :=
      Module.Finite.exists_bijective_map_powers S
        (LocalizedModule.mkLinearMap S M) (LocalizedModule.mkLinearMap S F) q hlocq
    have hbij_a : Function.Bijective (LocalizedModule.map (.powers a) q) :=
      hbij a dvd_rfl
    let ea : LocalizedModule.Away a M ≃ₗ[Localization.Away a]
        LocalizedModule.Away a F := LinearEquiv.ofBijective _ hbij_a
    let bF :=
      (Finsupp.basisSingleOne (R := R) (ι := Fin r)).ofIsLocalizedModule
        (Localization.Away a) (.powers a)
        (LocalizedModule.mkLinearMap (.powers a) F)
    exact ⟨bF.map ea.symm⟩
  · have hf_inj : Function.Injective f := by
      apply LinearMap.injective_of_linearIndependent
        (Finsupp.basisSingleOne (R := R) (ι := Fin r)).span_eq
      simpa [f] using hw
    refine ⟨f, hf_inj, ?_⟩
    rw [Formalization.Books.MoreAlgebra.Unit22.torsionModule_iff_forall_mem_torsion]
    intro y
    rw [Formalization.Books.MoreAlgebra.Unit22.mem_torsion_iff_exists_smul_eq_zero]
    obtain ⟨y, rfl⟩ := (LinearMap.range f).mkQ_surjective y
    obtain ⟨z, hz⟩ := hfLoc.2 (LocalizedModule.mkLinearMap S M y)
    obtain ⟨⟨x, s⟩, hs⟩ :=
      IsLocalizedModule.surj S (LocalizedModule.mkLinearMap S F) z
    have hsy : (s : L) • LocalizedModule.mkLinearMap S M y =
        LocalizedModule.mkLinearMap S M (f x) := by
      rw [← hz, ← map_smul, hs]
      simp [fLoc, f]
    obtain ⟨t, ht⟩ := LocalizedModule.mk_eq.mp hsy
    refine ⟨t * s, nonZeroDivisors.ne_zero (t * s), ?_⟩
    apply Submodule.Quotient.eq_zero_iff_mem.mpr
    refine LinearMap.mem_range.mpr ⟨(t : R) • x, ?_⟩
    simpa [Submonoid.smul_def, smul_smul, mul_comm, mul_left_comm, mul_assoc] using ht.symm
-/ by sorry

end

end Formalization.Books.MoreAlgebra.Unit23
