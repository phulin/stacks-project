import Formalization.Books.MoreAlgebra.Unit22.TorsionFree
import Formalization.Books.Algebra.Unit157.SerresCriterion
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# More on Algebra, Chapter 24: Reflexive modules

The source's reflexive-module predicate is delegated to Mathlib's canonical
`Module.IsReflexive` class.  The fractional-module intersections below use
concrete tensor-product models for `M_K`; this makes the source's phrase
“taken in `M_K`” an explicit set or submodule equality.
-/

namespace Formalization.Books.MoreAlgebra.Unit24

open Set
open Module
open Formalization.Books.Algebra.Unit37
open Formalization.Books.Algebra.Unit63
open Formalization.Books.Algebra.Unit72
open Formalization.Books.Algebra.Unit157
open scoped TensorProduct

universe u v w

noncomputable section

/-! ## Reflexivity and the double dual -/

/-- The source's reflexive-module predicate, using Mathlib's canonical class. -/
abbrev Reflexive (R M : Type*) [CommRing R] [AddCommGroup M]
    [Module R M] : Prop :=
  Module.IsReflexive R M

/-! The source notes that this definition has wider variants, but recommends
the Noetherian, finite, torsion-free setting used by the results below. -/

/-- The natural map from a module to its double dual. -/
abbrev reflexivityMap
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    M →ₗ[R] Module.Dual R (Module.Dual R M) :=
  Module.Dual.eval R M

@[simp]
theorem reflexivityMap_apply
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (m : M) (φ : Module.Dual R M) :
    reflexivityMap (R := R) (M := M) m φ = φ m := by
  rfl

/-- Reflexivity is exactly bijectivity of the natural evaluation map. -/
theorem reflexive_iff_bijective_reflexivityMap
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    Reflexive R M ↔ Function.Bijective (reflexivityMap (R := R) (M := M)) := by
  exact ⟨fun h => h.bijective_dual_eval', fun h => ⟨h⟩⟩

/-- A reflexive module is torsion free. -/
theorem reflexive_torsionFree
    {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M]
    (hM : Reflexive R M) :
    Module.IsTorsionFree R M := by
  constructor
  intro r hr m₁ m₂ hm
  apply hM.bijective_dual_eval'.injective
  ext n
  simpa [hr.1.eq_iff] using congr(n $hm)

private theorem exists_smul_dualRestrict
    {R : Type*} [CommRing R] [IsDomain R]
    {F : Type*} [AddCommGroup F] [Module R F]
    {n : ℕ} (b : Basis (Fin n) R F) (N : Submodule R F)
    (φ : N →ₗ[R] R) :
    ∃ a : nonZeroDivisors R, ∃ ψ : F →ₗ[R] R,
      a • φ = N.dualRestrict ψ := by
  let S := nonZeroDivisors R
  let K := Localization S
  let qN := LocalizedModule.mkLinearMap S N
  let qF := LocalizedModule.mkLinearMap S F
  let i : LocalizedModule S N →ₗ[K] LocalizedModule S F :=
    LocalizedModule.map S N.subtype
  have hi : Function.Injective i := by
    exact LocalizedModule.map_injective S N.subtype N.injective_subtype
  let φR : N →ₗ[R] K := (Algebra.linearMap R K).comp φ
  have hK : ∀ x : S, IsUnit ((algebraMap R (Module.End R K)) x) := by
    intro x
    exact IsLocalizedModule.map_units (Algebra.linearMap R K) x
  let φK : LocalizedModule S N →ₗ[K] K :=
    (IsLocalizedModule.lift S qN φR hK).extendScalarsOfIsLocalization S K
  obtain ⟨gK, hgK⟩ := LinearMap.dualMap_surjective_of_injective hi φK
  let c' : Fin n → K := fun j => gK (qF (b j))
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples_of_finite S c'
  choose c hc using ha
  let ψ : F →ₗ[R] R := b.constr R c
  let ψR : F →ₗ[R] K := (Algebra.linearMap R K).comp ψ
  let ψK : LocalizedModule S F →ₗ[K] K :=
    (IsLocalizedModule.lift S qF ψR hK).extendScalarsOfIsLocalization S K
  let aK : K := algebraMap R K (a : R)
  have hR :
      ((aK • gK).restrictScalars R).comp qF =
        (ψK.restrictScalars R).comp qF := by
    apply b.ext
    intro j
    change aK • gK (qF (b j)) =
      (IsLocalizedModule.lift S qF ψR hK) (qF (b j))
    rw [IsLocalizedModule.lift_apply]
    simpa [aK, c', ψ, ψR, Algebra.smul_def] using (hc j).symm
  have hK' : (aK • gK).restrictScalars R = ψK.restrictScalars R := by
    apply IsLocalizedModule.ext S qF hK
    exact hR
  refine ⟨a, ψ, ?_⟩
  apply LinearMap.ext
  intro x
  apply (IsFractionRing.injective R K)
  have hx := congrArg (fun f : LocalizedModule S F →ₗ[R] K => f (qF x)) hK'
  have hxi := congrArg (fun f : Module.Dual K (LocalizedModule S N) => f (qN x)) hgK
  have hxi' : gK (qF x) = algebraMap R K (φ x) := by
    calc
      gK (qF x) = gK (i (qN x)) := by
        congr 1
        change LocalizedModule.mk (x : F) 1 =
          (LocalizedModule.map S N.subtype) (LocalizedModule.mk x 1)
        rw [LocalizedModule.map_mk]
        rfl
      _ = (i.dualMap gK) (qN x) := rfl
      _ = φK (qN x) := hxi
      _ = algebraMap R K (φ x) := by
        change (IsLocalizedModule.lift S qN φR hK) (qN x) = _
        rw [IsLocalizedModule.lift_apply]
        simp [φR, LinearMap.comp_apply]
  have hx' : aK • gK (qF x) = algebraMap R K (ψ x) := by
    calc
      aK • gK (qF x) = ((aK • gK).restrictScalars R) (qF x) := rfl
      _ = (ψK.restrictScalars R) (qF x) := hx
      _ = algebraMap R K (ψ x) := by
        change (IsLocalizedModule.lift S qF ψR hK) (qF x) = _
        rw [IsLocalizedModule.lift_apply]
        simp [ψR, LinearMap.comp_apply]
  calc
    algebraMap R K (a • φ x) = aK • algebraMap R K (φ x) := by
      change algebraMap R K ((a : R) * φ x) =
        algebraMap R K (a : R) • algebraMap R K (φ x)
      rw [map_mul]
      rfl
    _ = aK • gK (qF x) := by rw [hxi'.symm]
    _ = algebraMap R K (ψ x) := hx'
    _ = algebraMap R K (N.dualRestrict ψ x) := by
      rw [Submodule.dualRestrict_apply]

/-- For a finite module, the kernel and cokernel of the natural map are
torsion modules.  The cokernel is represented by the quotient by its range. -/
theorem dualEval_kernel_cokernel_isTorsion
    {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.IsTorsion R (LinearMap.ker (reflexivityMap (R := R) (M := M))) ∧
      Module.IsTorsion R
        (Module.Dual R (Module.Dual R M) ⧸
          LinearMap.range (reflexivityMap (R := R) (M := M))) := by
  constructor
  · intro x
    let T := Submodule.torsion R M
    let Q := M ⧸ T
    let q : M →ₗ[R] Q := T.mkQ
    obtain ⟨n, f, hf⟩ :=
      (Formalization.Books.MoreAlgebra.Unit22.finite_torsionFree_iff_embeds_finiteFree
        (R := R) (M := Q)).mp inferInstance
    have hfx : f (q x) = 0 := by
      ext i
      have hi := congrArg
        (fun g : Module.Dual R (Module.Dual R M) =>
          g ((Finsupp.lapply i).comp f |>.comp q)) x.property
      change (f (q (x : M))) i = (0 : Fin n →₀ R) i at hi
      exact hi
    have hqx : q x = 0 := hf (hfx.trans (f.map_zero).symm)
    have hxT : (x : M) ∈ T := by
      change T.mkQ (x : M) = 0 at hqx
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hqx
      exact hqx
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff (x := (x : M))).mp hxT
    refine ⟨a, ?_⟩
    apply Subtype.ext
    exact ha
  · intro z
    obtain ⟨φ, rfl⟩ :=
      (Submodule.Quotient.mk_surjective
        (p := LinearMap.range (reflexivityMap (R := R) (M := M)))) z
    obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
    let q := p.dualMap
    have hq : Function.Injective q :=
      LinearMap.dualMap_injective_of_surjective hp
    let W := LinearMap.range q
    let e : Module.Dual R M ≃ₗ[R] W :=
      LinearEquiv.ofBijective q.rangeRestrict
        ⟨(q.injective_rangeRestrict_iff).2 hq, q.surjective_rangeRestrict⟩
    let φW : W →ₗ[R] R := φ.comp e.symm.toLinearMap
    obtain ⟨a, ψ, hψ⟩ :=
      exists_smul_dualRestrict (b := (Pi.basisFun R (Fin n)).dualBasis) W φW
    have hqψ : a • φ = q.dualMap ψ := by
      ext f
      change a • φ f = ψ (q f)
      calc
        a • φ f = (a • φW) (e f) := by simp [φW]
        _ = (W.dualRestrict ψ) (e f) :=
          congrArg (fun l : W →ₗ[R] R => l (e f)) hψ
        _ = ψ (q f) := by
          change ψ (e f) = ψ (q f)
          congr 1
    obtain ⟨y, hy⟩ := (Module.bijective_dual_eval R (Fin n → R)).2 ψ
    have hq_eval : q.dualMap ψ =
        reflexivityMap (R := R) (M := M) (p y) := by
      ext f
      rw [← hy]
      simp [q, LinearMap.dualMap_apply]
    refine ⟨a, ?_⟩
    rw [← Submodule.Quotient.mk_smul]
    apply (Submodule.Quotient.mk_eq_zero _).2
    rw [hqψ, hq_eval]
    exact ⟨p y, rfl⟩

/-- For a finite module over a domain, the natural map is injective exactly
when the module is torsion free. -/
theorem dualEval_injective_iff_torsionFree
    {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Function.Injective (reflexivityMap (R := R) (M := M)) ↔
      Module.IsTorsionFree R M := by
  constructor
  · intro h
    exact h.moduleIsTorsionFree (reflexivityMap (R := R) (M := M)) (by
      intro r m
      exact (reflexivityMap (R := R) (M := M)).map_smul r m)
  · intro hM
    obtain ⟨n, f, hf⟩ :=
      (Formalization.Books.MoreAlgebra.Unit22.finite_torsionFree_iff_embeds_finiteFree
        (R := R) (M := M)).mp hM
    intro x y hxy
    apply hf
    ext i
    have hi := congrArg
      (fun g : Module.Dual R (Module.Dual R M) =>
        g (Finsupp.lapply i ∘ₗ f)) hxy
    simpa [LinearMap.comp_apply, reflexivityMap_apply, Finsupp.lapply_apply] using hi

private theorem exists_smul_dualMap_eq
    {R M M' : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    (f : M →ₗ[R] M') (hf : Function.Injective f)
    (hM' : Module.IsTorsionFree R M') (φ : Module.Dual R M) :
    ∃ a : nonZeroDivisors R, ∃ ψ : Module.Dual R M',
      a • φ = f.dualMap ψ := by
  obtain ⟨n, e, he⟩ :=
    (Formalization.Books.MoreAlgebra.Unit22.finite_torsionFree_iff_embeds_finiteFree
      (R := R) (M := M')).mp hM'
  let i := e.comp f
  have hi : Function.Injective i := he.comp hf
  let N := LinearMap.range i
  let eN : M ≃ₗ[R] N :=
    LinearEquiv.ofBijective i.rangeRestrict
      ⟨(i.injective_rangeRestrict_iff).2 hi, i.surjective_rangeRestrict⟩
  let φN : N →ₗ[R] R := φ.comp eN.symm.toLinearMap
  obtain ⟨a, ψ, hψ⟩ :=
    exists_smul_dualRestrict (b := Finsupp.basisSingleOne) N φN
  refine ⟨a, ψ.comp e, ?_⟩
  ext x
  have hx := congrArg (fun l : N →ₗ[R] R => l (eN x)) hψ
  have heNx : (eN x : Fin n →₀ R) = i x := by
    change ((i.rangeRestrict) x : Fin n →₀ R) = i x
    rfl
  change (a : R) • φ (eN.symm (eN x)) = ψ (eN x : Fin n →₀ R) at hx
  rw [eN.symm_apply_apply, heNx] at hx
  change (↑a : R) * φ x = ψ (e (f x))
  simpa [i, LinearMap.dualMap_apply, LinearMap.comp_apply] using hx

private theorem dualMap_dualMap_injective_of_injective_torsionFree
    {R M M' : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    (f : M →ₗ[R] M') (hf : Function.Injective f)
    (hM' : Module.IsTorsionFree R M') :
    Function.Injective f.dualMap.dualMap := by
  intro z₁ z₂ hz
  ext φ
  obtain ⟨a, ψ, hψ⟩ := exists_smul_dualMap_eq f hf hM' φ
  have hz' := congrArg (fun z : Module.Dual R (Module.Dual R M') => z ψ) hz
  change z₁ (f.dualMap ψ) = z₂ (f.dualMap ψ) at hz'
  have hz'' : z₁ (a • φ) = z₂ (a • φ) := by
    rw [hψ]
    exact hz'
  have hz''' : (↑a : R) • z₁ φ = (↑a : R) • z₂ φ := by
    calc
      (↑a : R) • z₁ φ = z₁ ((↑a : R) • φ) := (z₁.map_smul _ _).symm
      _ = z₁ (a • φ) := by rfl
      _ = z₂ (a • φ) := hz''
      _ = z₂ ((↑a : R) • φ) := by rfl
      _ = (↑a : R) • z₂ φ := z₂.map_smul _ _
  have hdiff : (↑a : R) • (z₁ φ - z₂ φ) = 0 := by
    rw [smul_sub]
    rw [sub_eq_zero]
    exact hz'''
  have hzero : z₁ φ - z₂ φ = 0 :=
    ((Module.isTorsionFree_iff_smul_eq_zero.mp inferInstance
      (↑a : R) (z₁ φ - z₂ φ) hdiff).resolve_left
      (nonZeroDivisors.ne_zero a.property))
  exact sub_eq_zero.mp hzero

private theorem dualMap_range_smul_mem_of_surjective
    {R M F : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup F] [Module R F]
    (p : F →ₗ[R] Module.Dual R M) (hp : Function.Surjective p)
    (r : R) (z : Module.Dual R F)
    (hrz : r • z ∈ LinearMap.range p.dualMap) :
    r = 0 ∨ z ∈ LinearMap.range p.dualMap := by
  by_cases hr : r = 0
  · exact Or.inl hr
  right
  let K := LinearMap.ker p
  obtain ⟨ψ, hψ⟩ := hrz
  have hK : K ≤ LinearMap.ker z := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    have hkill : r • z x = 0 := by
      change (r • z) x = 0
      rw [← hψ]
      change ψ (p x) = 0
      rw [LinearMap.mem_ker.mp hx]
      simp
    exact (Module.isTorsionFree_iff_smul_eq_zero.mp inferInstance r (z x)
      hkill).resolve_left hr
  let e := p.quotKerEquivOfSurjective hp
  let zbar : (F ⧸ K) →ₗ[R] R := K.liftQ z hK
  let ψ' : Module.Dual R (Module.Dual R M) := zbar.comp e.symm.toLinearMap
  have hψ'z : ψ'.comp p = z := by
    ext x
    simp [ψ', zbar, e]
  exact ⟨ψ', hψ'z⟩

private theorem dualMap_cokernel_isTorsionFree_of_surjective
    {R M F : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup F] [Module R F]
    (p : F →ₗ[R] Module.Dual R M) (hp : Function.Surjective p) :
    Module.IsTorsionFree R
      (Module.Dual R F ⧸ LinearMap.range p.dualMap) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro r z hrz
  let L := LinearMap.range p.dualMap
  obtain ⟨z, rfl⟩ := (Submodule.Quotient.mk_surjective (p := L)) z
  change L.mkQ (r • z) = 0 at hrz
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hrz
  obtain hzero | hz := dualMap_range_smul_mem_of_surjective p hp r z hrz
  · exact Or.inl hzero
  · exact Or.inr ((Submodule.Quotient.mk_eq_zero L).2 hz)

private theorem linearEquiv_comp_dualMap_cokernel_isTorsionFree_of_surjective
    {R M F G : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup F] [Module R F]
    [AddCommGroup G] [Module R G]
    (p : F →ₗ[R] Module.Dual R M) (hp : Function.Surjective p)
    (d : Module.Dual R F ≃ₗ[R] G) :
    Module.IsTorsionFree R
      (G ⧸ LinearMap.range (d.toLinearMap.comp p.dualMap)) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro r z hrz
  by_cases hr : r = 0
  · exact Or.inl hr
  right
  let L := LinearMap.range (d.toLinearMap.comp p.dualMap)
  obtain ⟨z, rfl⟩ := (Submodule.Quotient.mk_surjective (p := L)) z
  change L.mkQ (r • z) = 0 at hrz
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hrz
  obtain ⟨ψ, hψ⟩ := hrz
  have hmem : r • d.symm z ∈ LinearMap.range p.dualMap := by
    refine ⟨ψ, ?_⟩
    apply d.injective
    rw [map_smul, d.apply_symm_apply]
    exact hψ
  obtain hzero | hz := dualMap_range_smul_mem_of_surjective p hp r (d.symm z) hmem
  · exact (hr hzero).elim
  · apply (Submodule.Quotient.mk_eq_zero L).2
    obtain ⟨ψ, hψ⟩ := hz
    refine ⟨ψ, ?_⟩
    change d (p.dualMap ψ) = z
    rw [hψ]
    exact d.apply_symm_apply _

/-- Over a discrete valuation ring, the natural map is surjective for every
finite module, including modules with torsion. -/
theorem dualEval_surjective_of_discreteValuationRing
    {R M : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    Function.Surjective (reflexivityMap (R := R) (M := M)) := by
  let hpid :=
    (IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime R).mp
      (inferInstance : IsDiscreteValuationRing R)
  let _ : IsPrincipalIdealRing R := hpid.1
  let T := Submodule.torsion R M
  let Q := M ⧸ T
  let q : M →ₗ[R] Q := T.mkQ
  have hq : Function.Surjective q := T.mkQ_surjective
  have hQref : Reflexive R Q := inferInstance
  have hqdual : Function.Injective q.dualMap :=
    LinearMap.dualMap_injective_of_surjective hq
  have hqdual_surj : Function.Surjective q.dualMap := by
    intro φ
    let hT : T ≤ LinearMap.ker φ := by
      intro x hx
      obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff (x := (x : M))).mp hx
      apply LinearMap.mem_ker.mpr
      have hax : (a : R) • φ (x : M) = 0 := by
        calc
          (a : R) • φ (x : M) = φ ((a : R) • (x : M)) :=
            (φ.map_smul _ _).symm
          _ = 0 := (congrArg φ ha).trans (map_zero φ)
      exact ((Module.isTorsionFree_iff_smul_eq_zero.mp inferInstance
        (a : R) (φ (x : M)) hax).resolve_left
        (nonZeroDivisors.ne_zero a.property))
    refine ⟨T.liftQ φ hT, ?_⟩
    ext x
    change (T.liftQ φ hT) (T.mkQ x) = φ x
    exact congrArg (fun l : M →ₗ[R] R => l x) (T.liftQ_mkQ φ hT)
  let e : Module.Dual R Q ≃ₗ[R] Module.Dual R M :=
    LinearEquiv.ofBijective q.dualMap ⟨hqdual, hqdual_surj⟩
  intro z
  let zQ : Module.Dual R (Module.Dual R Q) := z.comp e.toLinearMap
  obtain ⟨y, hy⟩ := hQref.bijective_dual_eval'.surjective zQ
  obtain ⟨m, hm⟩ := hq y
  refine ⟨m, ?_⟩
  ext φ
  obtain ⟨ψ, hψ⟩ := e.surjective φ
  have hzQ := congrArg (fun z' : Module.Dual R (Module.Dual R Q) => z' ψ) hy
  have hzQ' : ψ y = z (e ψ) := by
    simpa [zQ] using hzQ
  have hz : z φ = ψ y := by
    rw [← hψ]
    exact hzQ'.symm
  calc
    φ m = (e ψ) m := by rw [hψ]
    _ = ψ (q m) := by rfl
    _ = ψ y := by rw [hm]
    _ = z φ := hz.symm

/-! ## Locality and exact sequences -/

private theorem localized_reflexivityMap_naturality
    {R M : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.FinitePresentation R M]
    [Module.FinitePresentation R (Module.Dual R M)] (S : Submonoid R) :
    let A := Localization S
    let L := LocalizedModule S M
    let lM := LocalizedModule.mkLinearMap S M
    let lDD := LocalizedModule.mkLinearMap S
      (Module.Dual R (Module.Dual R M))
    let eD : LocalizedModule S (Module.Dual R M) ≃ₗ[A]
        Module.Dual A L :=
      (Module.FinitePresentation.linearEquivMapExtendScalars
        (M := M) (N := R) S).extendScalarsOfIsLocalization S A
    let eDD : LocalizedModule S (Module.Dual R (Module.Dual R M)) ≃ₗ[A]
        Module.Dual A (LocalizedModule S (Module.Dual R M)) :=
      (Module.FinitePresentation.linearEquivMapExtendScalars
        (M := Module.Dual R M) (N := R) S).extendScalarsOfIsLocalization S A
    let e : LocalizedModule S (Module.Dual R (Module.Dual R M)) ≃ₗ[A]
        Module.Dual A (Module.Dual A L) :=
      eDD.trans eD.dualMap.symm
    e.toLinearMap.comp
          (IsLocalizedModule.mapExtendScalars S lM lDD A
            (reflexivityMap (R := R) (M := M))) =
      reflexivityMap (R := A) (M := L) := by
  let A := Localization S
  let L := LocalizedModule S M
  let lM := LocalizedModule.mkLinearMap S M
  let lDD := LocalizedModule.mkLinearMap S
    (Module.Dual R (Module.Dual R M))
  let eD : LocalizedModule S (Module.Dual R M) ≃ₗ[A]
      Module.Dual A L :=
    (Module.FinitePresentation.linearEquivMapExtendScalars
      (M := M) (N := R) S).extendScalarsOfIsLocalization S A
  let eDD : LocalizedModule S (Module.Dual R (Module.Dual R M)) ≃ₗ[A]
      Module.Dual A (LocalizedModule S (Module.Dual R M)) :=
    (Module.FinitePresentation.linearEquivMapExtendScalars
      (M := Module.Dual R M) (N := R) S).extendScalarsOfIsLocalization S A
  let e := eDD.trans eD.dualMap.symm
  change e.toLinearMap.comp
      (IsLocalizedModule.mapExtendScalars S lM lDD A
        (reflexivityMap (R := R) (M := M))) =
    reflexivityMap (R := A) (M := L)
  apply LinearMap.restrictScalars_injective R
  let eR := e.restrictScalars R
  apply IsLocalizedModule.linearMap_ext S
    (LocalizedModule.mkLinearMap S M)
    (f' := eR.toLinearMap.comp (LocalizedModule.mkLinearMap S
      (Module.Dual R (Module.Dual R M))))
  ext m φ
  let j := reflexivityMap (R := R) (M := M)
  let lD := LocalizedModule.mkLinearMap S (Module.Dual R M)
  let G : LocalizedModule S (Module.Dual R M) →ₗ[A] A :=
    (reflexivityMap (R := A) (M := L) (lM m)).comp eD.toLinearMap
  have hfun : eDD (lDD (j m)) = G := by
    apply LinearMap.restrictScalars_injective R
    apply IsLocalizedModule.linearMap_ext S lD
      (f' := Algebra.linearMap R A)
    ext ψ
    have heD :
        eD (lD ψ) =
          IsLocalizedModule.mapExtendScalars S lM
            (LocalizedModule.mkLinearMap S R) A ψ := by
      change
        (Module.FinitePresentation.linearEquivMapExtendScalars S)
            (LocalizedModule.mkLinearMap S
              (Module.Dual R M) ψ) =
          IsLocalizedModule.mapExtendScalars S lM
            (LocalizedModule.mkLinearMap S R) A ψ
      rw [Module.FinitePresentation.linearEquivMapExtendScalars_apply]
    have heDD :
        eDD (lDD (j m)) =
          IsLocalizedModule.mapExtendScalars S lD
            (LocalizedModule.mkLinearMap S R) A (j m) := by
      change
        (Module.FinitePresentation.linearEquivMapExtendScalars S)
            (LocalizedModule.mkLinearMap S
              (Module.Dual R (Module.Dual R M)) (j m)) =
          IsLocalizedModule.mapExtendScalars S lD
            (LocalizedModule.mkLinearMap S R) A (j m)
      rw [Module.FinitePresentation.linearEquivMapExtendScalars_apply]
    rw [heDD]
    change
      (IsLocalizedModule.mapExtendScalars S lD
        (LocalizedModule.mkLinearMap S R) A (j m)) (lD ψ) =
        (reflexivityMap (R := A) (M := L) (lM m)) (eD (lD ψ))
    rw [heD]
    change
      (IsLocalizedModule.map S lD (LocalizedModule.mkLinearMap S R) (j m))
          (lD ψ) =
        (IsLocalizedModule.map S lM (LocalizedModule.mkLinearMap S R) ψ)
          (lM m)
    rw [IsLocalizedModule.map_apply, IsLocalizedModule.map_apply]
    rfl
  simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars]
  rw [IsLocalizedModule.mapExtendScalars_apply_apply]
  rw [IsLocalizedModule.map_apply]
  change (eD.dualMap.symm (eDD (lDD (j m)))) φ = φ (lM m)
  rw [hfun]
  rw [LinearEquiv.dualMap_symm]
  simp [G]

private theorem reflexive_localized_iff_map_bijective
    {R M : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.FinitePresentation R M]
    [Module.FinitePresentation R (Module.Dual R M)] (S : Submonoid R) :
    Reflexive (Localization S) (LocalizedModule S M) ↔
      Function.Bijective
        (LocalizedModule.map S (reflexivityMap (R := R) (M := M))) := by
  let A := Localization S
  let L := LocalizedModule S M
  let lM := LocalizedModule.mkLinearMap S M
  let lDD := LocalizedModule.mkLinearMap S
    (Module.Dual R (Module.Dual R M))
  let eD : LocalizedModule S (Module.Dual R M) ≃ₗ[A]
      Module.Dual A L :=
    (Module.FinitePresentation.linearEquivMapExtendScalars
      (M := M) (N := R) S).extendScalarsOfIsLocalization S A
  let eDD : LocalizedModule S (Module.Dual R (Module.Dual R M)) ≃ₗ[A]
      Module.Dual A (LocalizedModule S (Module.Dual R M)) :=
    (Module.FinitePresentation.linearEquivMapExtendScalars
      (M := Module.Dual R M) (N := R) S).extendScalarsOfIsLocalization S A
  let e := eDD.trans eD.dualMap.symm
  have hnat :
      e.toLinearMap.comp
          (IsLocalizedModule.mapExtendScalars S lM lDD A
            (reflexivityMap (R := R) (M := M))) =
        reflexivityMap (R := A) (M := L) :=
    localized_reflexivityMap_naturality S
  rw [reflexive_iff_bijective_reflexivityMap]
  rw [← hnat]
  change Function.Bijective
      (e.toLinearMap.comp
        (IsLocalizedModule.mapExtendScalars S lM lDD A
          (reflexivityMap (R := R) (M := M)))) ↔
    Function.Bijective
      (IsLocalizedModule.mapExtendScalars S lM lDD A
        (reflexivityMap (R := R) (M := M)))
  exact Function.Bijective.of_comp_iff' e.bijective _

/-- Reflexivity of a finite module over a Noetherian domain can be checked at
all primes or at all maximal ideals. -/
theorem reflexive_localization_iff
    {R M : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    List.TFAE
      [Reflexive R M,
       ∀ p : PrimeSpectrum R,
         Reflexive (Localization.AtPrime p.asIdeal)
           (LocalizedModule.AtPrime p.asIdeal M),
       ∀ m : MaximalSpectrum R,
         Reflexive (Localization.AtPrime m.asIdeal)
           (LocalizedModule.AtPrime m.asIdeal M)] := by
  let _ : Module.FinitePresentation R M := finitePresentation_of_finite R M
  let _ : Module.FinitePresentation R (Module.Dual R M) :=
    finitePresentation_of_finite R (Module.Dual R M)
  apply List.tfae_of_forall (Reflexive R M)
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact Iff.rfl
  · constructor
    · intro hp
      apply (reflexive_iff_bijective_reflexivityMap (R := R) (M := M)).2
      apply bijective_of_localized_maximal
      intro J hJ
      apply (reflexive_localized_iff_map_bijective
        (R := R) (M := M) J.primeCompl).mp
      exact hp ⟨J, inferInstance⟩
    · intro hM p
      apply (reflexive_localized_iff_map_bijective
        (R := R) (M := M) p.asIdeal.primeCompl).mpr
      exact ⟨LocalizedModule.map_injective p.asIdeal.primeCompl
          (reflexivityMap (R := R) (M := M))
          hM.bijective_dual_eval'.injective,
        LocalizedModule.map_surjective p.asIdeal.primeCompl
          (reflexivityMap (R := R) (M := M))
          hM.bijective_dual_eval'.surjective⟩
  · constructor
    · intro hm
      apply (reflexive_iff_bijective_reflexivityMap (R := R) (M := M)).2
      apply bijective_of_localized_maximal
      intro J hJ
      apply (reflexive_localized_iff_map_bijective
        (R := R) (M := M) J.primeCompl).mp
      exact hm ⟨J, hJ⟩
    · intro hM m
      apply (reflexive_localized_iff_map_bijective
        (R := R) (M := M) m.asIdeal.primeCompl).mpr
      exact ⟨LocalizedModule.map_injective m.asIdeal.primeCompl
          (reflexivityMap (R := R) (M := M))
          hM.bijective_dual_eval'.injective,
        LocalizedModule.map_surjective m.asIdeal.primeCompl
          (reflexivityMap (R := R) (M := M))
          hM.bijective_dual_eval'.surjective⟩

/-- In an exact sequence `0 → M → M' → M''`, reflexivity descends from the
middle term when the right term is torsion free. -/
theorem reflexive_of_exact
    {R M M' M'' : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    [AddCommGroup M''] [Module R M''] [Module.Finite R M'']
    (f : M →ₗ[R] M') (g : M' →ₗ[R] M'')
    (hf : Function.Injective f)
    (hfg : Function.Exact (f : M → M') (g : M' → M''))
    (hM' : Reflexive R M')
    (hM'' : Module.IsTorsionFree R M'') :
    Reflexive R M := by
  let jM := reflexivityMap (R := R) (M := M)
  let jM' := reflexivityMap (R := R) (M := M')
  let jM'' := reflexivityMap (R := R) (M := M'')
  have hgf : g.comp f = 0 := by
    ext x
    exact (hfg (f x)).mpr ⟨x, rfl⟩
  have htop : Function.Injective f.dualMap.dualMap :=
    dualMap_dualMap_injective_of_injective_torsionFree f hf
      (reflexive_torsionFree hM')
  have hinj : Function.Injective jM := by
    intro x y hxy
    apply hf
    apply hM'.bijective_dual_eval'.injective
    ext φ
    have hφ := congrArg
      (fun z : Module.Dual R (Module.Dual R M) => z (f.dualMap φ)) hxy
    simpa [jM, jM', reflexivityMap_apply, LinearMap.dualMap_apply,
      LinearMap.comp_apply] using hφ
  have hsurj : Function.Surjective jM := by
    intro z
    obtain ⟨m', hm'⟩ := hM'.bijective_dual_eval'.surjective
      (f.dualMap.dualMap z)
    have hgzero : g m' = 0 := by
      apply (dualEval_injective_iff_torsionFree (R := R) (M := M'')).mpr hM''
      ext φ
      have hφ := congrArg
        (fun z' : Module.Dual R (Module.Dual R M') => z' (g.dualMap φ)) hm'
      have hleft : φ (g m') =
          (f.dualMap.dualMap z) (g.dualMap φ) := by
        simpa [jM', reflexivityMap_apply, LinearMap.dualMap_apply] using hφ
      have htarget : φ (g m') = 0 := by
        rw [hleft]
        change z (f.dualMap (g.dualMap φ)) = 0
        rw [show f.dualMap (g.dualMap φ) = 0 by
          ext x
          change φ (g (f x)) = 0
          rw [← LinearMap.comp_apply]
          simpa [LinearMap.comp_apply] using
            congrArg φ (congrArg (fun k : M →ₗ[R] M'' => k x) hgf)]
        simp
      simpa [jM'', reflexivityMap_apply] using htarget
    obtain ⟨m, hm⟩ := (hfg m').mp hgzero
    refine ⟨m, ?_⟩
    apply htop
    calc
      f.dualMap.dualMap (jM m) = jM' (f m) := by
        ext φ
        rfl
      _ = jM' m' := by rw [hm]
      _ = f.dualMap.dualMap z := hm'
  exact (reflexive_iff_bijective_reflexivityMap (R := R) (M := M)).2
    ⟨hinj, hsurj⟩

/-- Characterization of finite reflexive modules by a finite-free presentation
whose cokernel is torsion free. -/
theorem reflexive_iff_finiteFree_presentation
    {R M : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Reflexive R M ↔
      ∃ n : ℕ, ∃ f : M →ₗ[R] (Fin n →₀ R),
        Function.Injective f ∧
          Module.IsTorsionFree R
            ((Fin n →₀ R) ⧸ LinearMap.range f) := by
  constructor
  · intro hM
    obtain ⟨n, p₀, hp₀⟩ := Module.Finite.exists_fin' R (Module.Dual R M)
    let u := Finsupp.linearEquivFunOnFinite R R (Fin n)
    let p : (Fin n →₀ R) →ₗ[R] Module.Dual R M := p₀.comp u.toLinearMap
    have hp : Function.Surjective p := by
      intro φ
      obtain ⟨v, hv⟩ := hp₀ φ
      refine ⟨u.symm v, ?_⟩
      simpa [p, u] using hv
    let b := (Finsupp.basisSingleOne (R := R) (ι := Fin n)).dualBasis
    let d : Module.Dual R (Fin n →₀ R) ≃ₗ[R] (Fin n →₀ R) :=
      b.equivFun.trans u.symm
    let j := reflexivityMap (R := R) (M := M)
    let q := d.toLinearMap.comp p.dualMap
    let f := q.comp j
    have hf : Function.Injective f := by
      exact (d.injective.comp (LinearMap.dualMap_injective_of_surjective hp)).comp
        hM.bijective_dual_eval'.injective
    have hrange : LinearMap.range f = LinearMap.range q := by
      apply le_antisymm
      · rintro _ ⟨m, rfl⟩
        exact ⟨j m, rfl⟩
      · rintro _ ⟨z, rfl⟩
        obtain ⟨m, hm⟩ := hM.bijective_dual_eval'.surjective z
        refine ⟨m, ?_⟩
        rw [← hm]
        rfl
    refine ⟨n, f, hf, ?_⟩
    rw [hrange]
    exact linearEquiv_comp_dualMap_cokernel_isTorsionFree_of_surjective p hp d
  · rintro ⟨n, f, hf, hQ⟩
    apply reflexive_of_exact f (LinearMap.range f).mkQ hf
    · exact LinearMap.exact_iff.mpr (by
        rw [Submodule.ker_mkQ])
    · exact ⟨Module.bijective_dual_eval R (Fin n →₀ R)⟩
    · exact hQ

private theorem finiteFree_presentation_of_reflexive
    {R M : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Reflexive R M) :
    ∃ n : ℕ, ∃ f : M →ₗ[R] (Fin n →₀ R),
      Function.Injective f ∧
        Module.IsTorsionFree R
          ((Fin n →₀ R) ⧸ LinearMap.range f) := by
  obtain ⟨n, p₀, hp₀⟩ := Module.Finite.exists_fin' R (Module.Dual R M)
  let u := Finsupp.linearEquivFunOnFinite R R (Fin n)
  let p : (Fin n →₀ R) →ₗ[R] Module.Dual R M := p₀.comp u.toLinearMap
  have hp : Function.Surjective p := by
    intro φ
    obtain ⟨v, hv⟩ := hp₀ φ
    refine ⟨u.symm v, ?_⟩
    simpa [p, u] using hv
  let b := (Finsupp.basisSingleOne (R := R) (ι := Fin n)).dualBasis
  let d : Module.Dual R (Fin n →₀ R) ≃ₗ[R] (Fin n →₀ R) :=
    b.equivFun.trans u.symm
  let j := reflexivityMap (R := R) (M := M)
  let q := d.toLinearMap.comp p.dualMap
  let f := q.comp j
  have hf : Function.Injective f := by
    exact (d.injective.comp (LinearMap.dualMap_injective_of_surjective hp)).comp
      hM.bijective_dual_eval'.injective
  have hrange : LinearMap.range f = LinearMap.range q := by
    apply le_antisymm
    · rintro _ ⟨m, rfl⟩
      exact ⟨j m, rfl⟩
    · rintro _ ⟨z, rfl⟩
      obtain ⟨m, hm⟩ := hM.bijective_dual_eval'.surjective z
      refine ⟨m, ?_⟩
      rw [← hm]
      rfl
  refine ⟨n, f, hf, ?_⟩
  rw [hrange]
  exact linearEquiv_comp_dualMap_cokernel_isTorsionFree_of_surjective p hp d

/-- Flat base change of a finite reflexive module between Noetherian domains
is finite and reflexive. -/
theorem reflexive_flat_baseChange
    {R R' M : Type*} [CommRing R] [CommRing R']
    [IsDomain R] [IsDomain R'] [IsNoetherianRing R] [IsNoetherianRing R']
    [Algebra R R'] [Module.Flat R R']
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Reflexive R M) :
    Module.Finite R' (R' ⊗[R] M) ∧
      Reflexive R' (R' ⊗[R] M) := by
  obtain ⟨n, f, hf, hQ⟩ := finiteFree_presentation_of_reflexive hM
  let q := (LinearMap.range f).mkQ
  have hq : Function.Exact (f : M → (Fin n →₀ R)) (q : _ → _) :=
    LinearMap.exact_iff.mpr (by rw [Submodule.ker_mkQ])
  let f' : R' ⊗[R] M →ₗ[R'] R' ⊗[R] (Fin n →₀ R) :=
    TensorProduct.AlgebraTensorModule.lTensor (R := R) R' R' f
  let q' : R' ⊗[R] (Fin n →₀ R) →ₗ[R']
      R' ⊗[R] ((Fin n →₀ R) ⧸ LinearMap.range f) :=
    TensorProduct.AlgebraTensorModule.lTensor (R := R) R' R' q
  have hf' : Function.Injective f' := by
    intro x y hxy
    apply (Module.Flat.lTensor_preserves_injective_linearMap (M := R') f hf)
    change (f.lTensor R') x = (f.lTensor R') y
    exact hxy
  have hq' : Function.Exact (f' : R' ⊗[R] M → _)
      (q' : R' ⊗[R] (Fin n →₀ R) → _) := by
    change Function.Exact (f.lTensor R') (q.lTensor R')
    exact Module.Flat.lTensor_exact (M := R') hq
  have hmid : Reflexive R' (R' ⊗[R] (Fin n →₀ R)) := by
    let _ : Module.Free R' (R' ⊗[R] (Fin n →₀ R)) := by infer_instance
    exact Module.IsReflexive.of_finite_of_free R' (R' ⊗[R] (Fin n →₀ R))
  have hright : Module.IsTorsionFree R'
      (R' ⊗[R] ((Fin n →₀ R) ⧸ LinearMap.range f)) :=
    Formalization.Books.MoreAlgebra.Unit22.flat_baseChange_isTorsionFree
      (R := R) (R' := R')
      (M := (Fin n →₀ R) ⧸ LinearMap.range f)
  exact ⟨inferInstance,
    reflexive_of_exact
      (R := R') (M := R' ⊗[R] M)
      (M' := R' ⊗[R] (Fin n →₀ R))
      (M'' := R' ⊗[R] ((Fin n →₀ R) ⧸ LinearMap.range f))
      f' q' hf' hq' hmid hright⟩

private theorem finite_pi_reflexive
    {R X : Type*} [CommRing R] [AddCommGroup X] [Module R X]
    (hX : Reflexive R X) (n : ℕ) :
    Reflexive R (Fin n → X) := by
  refine Module.pi_induction' R
    (motive := fun Y _ _ => Reflexive R Y)
    (motive' := fun Y _ _ => Reflexive R Y)
    (equiv := ?_)
    (equiv' := ?_)
    (unit := by infer_instance)
    (prod := ?_) (fun _ : Fin n => X) ?_
  · intro Y Y' _ _ _ _ e h
    exact @Module.equiv R Y Y' _ _ _ _ _ h e
  · intro Y Y' _ _ _ _ e h
    exact @Module.equiv R Y Y' _ _ _ _ _ h e
  · intro Y Y' _ _ _ _ hY hY'
    exact @Prod.instModuleIsReflexive R Y Y' _ _ _ _ _ hY hY'
  · intro i
    exact hX

private theorem hom_from_fin_pi_reflexive
    {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    (hN : Reflexive R N) (n : ℕ) :
    Reflexive R ((Fin n → R) →ₗ[R] N) := by
  let eSum : (Fin n → (R →ₗ[R] N)) ≃ₗ[R] ((Fin n →₀ R) →ₗ[R] N) :=
    Finsupp.lsum R
  let eDom : (Fin n →₀ R) ≃ₗ[R] (Fin n → R) :=
    Finsupp.linearEquivFunOnFinite R R (Fin n)
  let eCoord : (Fin n → (R →ₗ[R] N)) ≃ₗ[R] (Fin n → N) :=
    LinearEquiv.piCongrRight (fun _ => LinearMap.ringLmapEquivSelf R R N)
  let e : ((Fin n → R) →ₗ[R] N) ≃ₗ[R] (Fin n → N) :=
    ((eDom.arrowCongr (LinearEquiv.refl R N)).symm.trans eSum.symm).trans eCoord
  exact @Module.equiv R (Fin n → N) ((Fin n → R) →ₗ[R] N)
    _ _ _ _ _ (finite_pi_reflexive hN n) e.symm

/-- The Hom module into a finite reflexive module is reflexive. -/
theorem hom_into_reflexive_isReflexive
    {R M N : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (hN : Reflexive R N) :
    Reflexive R (M →ₗ[R] N) := by
  let _ : Module.FinitePresentation R M := finitePresentation_of_finite R M
  obtain ⟨n, m, p, q, hp, hpq⟩ :=
    Module.FinitePresentation.exists_fin' R M
  let i : (M →ₗ[R] N) →ₗ[R] ((Fin n → R) →ₗ[R] N) :=
    { toFun := fun a => a.comp p
      map_add' := by intro a b; ext x; simp
      map_smul' := by intro r a; ext x; simp }
  let j : ((Fin n → R) →ₗ[R] N) →ₗ[R] ((Fin m → R) →ₗ[R] N) :=
    { toFun := fun b => b.comp q
      map_add' := by intro a b; ext x; simp
      map_smul' := by intro r a; ext x; simp }
  have hi : Function.Injective i := by
    intro a b hab
    apply LinearMap.ext
    intro x
    obtain ⟨y, hy⟩ := hp x
    have h := congrArg (fun k : (Fin n → R) →ₗ[R] N => k y) hab
    simpa [i, hy] using h
  have hqp : p.comp q = 0 := hpq.linearMap_comp_eq_zero
  have hij : Function.Exact (i : (M →ₗ[R] N) → ((Fin n → R) →ₗ[R] N))
      (j : ((Fin n → R) →ₗ[R] N) → ((Fin m → R) →ₗ[R] N)) := by
    apply LinearMap.exact_iff.mpr
    apply le_antisymm
    · intro b hb
      have hbq : b.comp q = 0 := by
        simpa [j] using hb
      have hker : LinearMap.ker p ≤ LinearMap.ker b := by
        intro x hx
        have hx' : x ∈ LinearMap.range q := by
          rw [← LinearMap.exact_iff.mp hpq]
          exact hx
        obtain ⟨y, hy⟩ := hx'
        rw [← hy]
        change b (q y) = 0
        rw [← LinearMap.comp_apply, hbq, LinearMap.zero_apply]
      let l := (LinearMap.ker p).liftQ b hker
      let e := p.quotKerEquivOfSurjective hp
      let a := l.comp e.symm.toLinearMap
      have hcomp : a.comp p = b := by
        apply LinearMap.ext
        intro x
        change l (e.symm (p x)) = b x
        rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
        exact congrArg (fun k : (Fin n → R) →ₗ[R] N => k x)
          ((LinearMap.ker p).liftQ_mkQ b hker)
      exact ⟨a, hcomp⟩
    · rintro _ ⟨a, rfl⟩
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext
      intro y
      change a (p (q y)) = 0
      have : p (q y) = 0 := by
        change (p.comp q) y = 0
        rw [hqp, LinearMap.zero_apply]
      rw [this, map_zero]
  exact reflexive_of_exact
    (R := R) (M := M →ₗ[R] N)
    (M' := (Fin n → R) →ₗ[R] N)
    (M'' := (Fin m → R) →ₗ[R] N)
    i j hi hij
    (hom_from_fin_pi_reflexive hN n)
    (reflexive_torsionFree (hom_from_fin_pi_reflexive hN m))

/-! ## Reflexive hull -/

/-- The double dual of a finite module, called its reflexive hull in the
source. -/
abbrev reflexiveHull
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] : Type _ :=
  Module.Dual R (Module.Dual R M)

/-- Under the finite Noetherian-domain hypotheses of the source, the double
dual is itself reflexive. -/
theorem reflexiveHull_isReflexive
    {R M : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Reflexive R (reflexiveHull (R := R) (M := M)) := by
  let _ : Module.FinitePresentation R (Module.Dual R M) :=
    finitePresentation_of_finite R (Module.Dual R M)
  exact hom_into_reflexive_isReflexive (R := R) (M := Module.Dual R M) (N := R)
    (by infer_instance)

/-- The map induced on reflexive hulls by a module map. -/
def reflexiveHullMap
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    reflexiveHull (R := R) (M := M) →ₗ[R]
      reflexiveHull (R := R) (M := N) :=
  f.dualMap.dualMap

@[simp]
theorem reflexiveHullMap_id
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    reflexiveHullMap (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  simp [reflexiveHullMap]

theorem reflexiveHullMap_comp
    {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    reflexiveHullMap (g.comp f) =
      (reflexiveHullMap g).comp (reflexiveHullMap f) := by
  simp [reflexiveHullMap, ← LinearMap.dualMap_comp_dualMap]

/-- The canonical factor through the reflexive hull of a map into a reflexive
module. -/
noncomputable def reflexiveHullFactor
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.IsReflexive R N] (f : M →ₗ[R] N) :
    reflexiveHull (R := R) (M := M) →ₗ[R] N :=
  (Module.evalEquiv R N).symm.toLinearMap.comp (reflexiveHullMap f)

/-- The canonical hull factor restricts to the original map. -/
theorem reflexiveHullFactor_comp_reflexivityMap
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.IsReflexive R N] (f : M →ₗ[R] N) :
    (reflexiveHullFactor f).comp (reflexivityMap (R := R) (M := M)) = f := by
  ext x
  change (Module.evalEquiv R N).symm
      (f.dualMap.dualMap ((Module.Dual.eval R M) x)) = f x
  have h := congrArg
    (fun k : M →ₗ[R] Module.Dual R (Module.Dual R N) => k x)
    (Module.Dual.eval_naturality f)
  simp only [LinearMap.comp_apply] at h
  rw [h, ← Module.evalEquiv_apply]
  exact (Module.evalEquiv R N).symm_apply_apply (f x)

/-- The hull factor is the unique factor through the natural evaluation map. -/
theorem reflexiveHullFactor_unique
    {R M N : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N]
    [Module.IsReflexive R N] (f : M →ₗ[R] N)
    (g : reflexiveHull (R := R) (M := M) →ₗ[R] N)
    (hg : g.comp (reflexivityMap (R := R) (M := M)) = f) :
    g = reflexiveHullFactor f := by
  let j := reflexivityMap (R := R) (M := M)
  let h := g - reflexiveHullFactor f
  have hj : h.comp j = 0 := by
    ext x
    change g (j x) - reflexiveHullFactor f (j x) = 0
    have hgx := congrArg (fun k : M →ₗ[R] N => k x) hg
    have hfx := congrArg (fun k : M →ₗ[R] N => k x)
      (reflexiveHullFactor_comp_reflexivityMap f)
    simpa [j, LinearMap.comp_apply] using sub_eq_zero.mpr (hgx.trans hfx.symm)
  have hQ : Module.IsTorsion R
      (Module.Dual R (Module.Dual R M) ⧸ LinearMap.range j) :=
    (dualEval_kernel_cokernel_isTorsion (R := R) (M := M)).2
  have hNtf : Module.IsTorsionFree R N :=
    reflexive_torsionFree (R := R) (M := N) (by infer_instance)
  apply LinearMap.ext
  intro z
  rcases hQ (x := (LinearMap.range j).mkQ z) with ⟨a, ha⟩
  have haz : (a : R) • z ∈ LinearMap.range j := by
    apply (Submodule.Quotient.mk_eq_zero (LinearMap.range j)).mp
    change (LinearMap.range j).mkQ ((a : R) • z) = 0
    rw [(LinearMap.range j).mkQ.map_smul]
    simpa [Submonoid.smul_def] using ha
  obtain ⟨y, hy⟩ := haz
  have hkill : (a : R) • h z = 0 := by
    calc
      (a : R) • h z = h ((a : R) • z) := (h.map_smul _ _).symm
      _ = h (j y) := by rw [hy]
      _ = 0 := by
        simpa [LinearMap.comp_apply] using congrArg (fun k : _ →ₗ[R] N => k y) hj
  have hz : h z = 0 :=
    ((Module.isTorsionFree_iff_smul_eq_zero.mp hNtf)
      (a : R) (h z) hkill).resolve_left (nonZeroDivisors.ne_zero a.property)
  exact sub_eq_zero.mp (by simpa [h] using hz)

/-! ## Hom modules, depth, and Serre conditions -/

/-- Hom into a module of depth at least one has depth at least one. -/
theorem hom_depth_ge_one
    {R M N : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (hN : 1 ≤ localDepth R N) :
    1 ≤ localDepth R (M →ₗ[R] N) := by
  let _ : Module.FinitePresentation R M := finitePresentation_of_finite R M
  have hNreg : ∃ r : R, r ∈ IsLocalRing.maximalIdeal R ∧ IsSMulRegular N r := by
    by_cases hNtr : Nontrivial N
    · by_contra hno
      have hzero : localDepth R N = 0 :=
        (depth_eq_zero_iff (IsLocalRing.maximalIdeal R) N).2 ⟨hNtr, hno⟩
      rw [hzero] at hN
      simp at hN
    · refine ⟨0, Ideal.zero_mem _, ?_⟩
      intro x y hxy
      exact (not_nontrivial_iff_subsingleton.mp hNtr).elim x y
  obtain ⟨r, hr, hregN⟩ := hNreg
  have hregHom : IsSMulRegular (M →ₗ[R] N) r := by
    intro a b hab
    apply LinearMap.ext
    intro x
    apply hregN
    simpa using congrArg (fun k : M →ₗ[R] N => k x) hab
  by_cases hHtr : Nontrivial (M →ₗ[R] N)
  · have hHne : localDepth R (M →ₗ[R] N) ≠ 0 := by
      intro hzero
      exact ((depth_eq_zero_iff (IsLocalRing.maximalIdeal R)
        (M →ₗ[R] N)).mp hzero).2 ⟨r, hr, hregHom⟩
    exact Order.one_le_iff_ne_zero.mpr hHne
  · have hsub : Subsingleton (M →ₗ[R] N) :=
      not_nontrivial_iff_subsingleton.mp hHtr
    have htop : localDepth R (M →ₗ[R] N) = ⊤ := by
      exact depth_eq_top_of_subsingleton (IsLocalRing.maximalIdeal R)
        (M →ₗ[R] N)
    rw [htop]
    exact le_top

/-- Hom into a module of depth at least two has depth at least two. -/
theorem hom_depth_ge_two
    {R M N : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (hN : 2 ≤ localDepth R N) :
    2 ≤ localDepth R (M →ₗ[R] N) := by
  sorry

/-- Hom preserves the module `(S_1)` and `(S_2)` conditions. -/
theorem hom_hasPropertySkModule
    {R M N : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] :
    (HasPropertySkModule R N 1 → HasPropertySkModule R (M →ₗ[R] N) 1) ∧
      (HasPropertySkModule R N 2 → HasPropertySkModule R (M →ₗ[R] N) 2) := by
  sorry

/-- Over a domain, Hom into a torsion-free `(S_2)` module is torsion-free and
`(S_2)`. -/
theorem hom_torsionFree_hasPropertySkModule
    {R M N : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (hN₁ : Module.IsTorsionFree R N)
    (hN₂ : HasPropertySkModule R N 2) :
    Module.IsTorsionFree R (M →ₗ[R] N) ∧
      HasPropertySkModule R (M →ₗ[R] N) 2 := by
  sorry

/-! ## Associated-prime tests for maps -/

/-- Injectivity can be checked after localization at associated primes. -/
theorem injective_of_localized_injective_or_not_associated
    {R M N : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N)
    (hφ : ∀ p : PrimeSpectrum R,
      Function.Injective
          (LocalizedModule.map p.asIdeal.primeCompl φ) ∨
        p ∉ Formalization.Books.Algebra.Unit63.associatedPrimes R M) :
    Function.Injective φ := by
  sorry

/-- A finite map is an isomorphism when it is locally an isomorphism or its
source has depth at least two away from the associated primes of the target. -/
theorem isomorphism_of_localized_isomorphism_or_depth_two
    {R M N : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N)
    (hφ : ∀ p : PrimeSpectrum R,
      Function.Bijective
          (LocalizedModule.map p.asIdeal.primeCompl φ) ∨
        (2 ≤ localDepth (Localization.AtPrime p.asIdeal)
              (LocalizedModule.AtPrime p.asIdeal M) ∧
          p ∉ Formalization.Books.Algebra.Unit63.associatedPrimes R N)) :
    Function.Bijective φ := by
  sorry

/-- The preceding isomorphism criterion specializes to a torsion-free target
over a Noetherian domain. -/
theorem isomorphism_of_depth_two_torsionFree_target
    {R M N : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) (hN : Module.IsTorsionFree R N)
    (hφ : ∀ p : PrimeSpectrum R,
      Function.Bijective
          (LocalizedModule.map p.asIdeal.primeCompl φ) ∨
        2 ≤ localDepth (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal M)) :
    Function.Bijective φ := by
  sorry

/-- Reflexivity is equivalent to local reflexivity or depth at least two at
every prime. -/
theorem reflexive_iff_local_reflexive_or_depth_two
    {R M : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Reflexive R M ↔
      ∀ p : PrimeSpectrum R,
        Reflexive (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal M) ∨
          2 ≤ localDepth (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal M) := by
  sorry

/-- A finite reflexive module has depth at least two wherever the ring has
depth at least two. -/
theorem reflexive_local_depth_ge_two
    {R M : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Reflexive R M) (p : PrimeSpectrum R)
    (hR : 2 ≤ localDepth (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal)) :
    2 ≤ localDepth (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal M) := by
  sorry

/-- If a Noetherian domain has property `(S_2)`, a finite reflexive module has
the module property `(S_2)`. -/
theorem reflexive_hasPropertySkModule_two
    {R M : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Reflexive R M) (hR : HasPropertySk R 2) :
    HasPropertySkModule R M 2 := by
  sorry

/-! ## The example separating reflexivity from `(S_2)` -/

/-- The subalgebra `k[y, x², xy, x³]` of `k[x, y]`, with the redundant
generator `1` retained to mirror the source. -/
def exampleRing (k : Type u) [Field k] :
    Subalgebra k (MvPolynomial (Fin 2) k) :=
  Algebra.adjoin k
    ({1, MvPolynomial.X (1 : Fin 2),
      (MvPolynomial.X (0 : Fin 2)) ^ 2,
      MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2),
      (MvPolynomial.X (0 : Fin 2)) ^ 3} : Set (MvPolynomial (Fin 2) k))

def exampleY (k : Type u) [Field k] : exampleRing k :=
  ⟨MvPolynomial.X (1 : Fin 2), by
    exact Algebra.subset_adjoin (by simp)⟩

def exampleXSquared (k : Type u) [Field k] : exampleRing k :=
  ⟨(MvPolynomial.X (0 : Fin 2)) ^ 2, by
    exact Algebra.subset_adjoin (by simp)⟩

def exampleXY (k : Type u) [Field k] : exampleRing k :=
  ⟨MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2), by
    exact Algebra.subset_adjoin (by simp)⟩

def exampleXCubed (k : Type u) [Field k] : exampleRing k :=
  ⟨(MvPolynomial.X (0 : Fin 2)) ^ 3, by
    exact Algebra.subset_adjoin (by simp)⟩

/-- The ideal `(y, x², xy, x³)` in the example ring. -/
def exampleMaximalIdeal (k : Type u) [Field k] : Ideal (exampleRing k) :=
  Ideal.span ({exampleY k, exampleXSquared k, exampleXY k, exampleXCubed k} :
    Set (exampleRing k))

/-- The example ring is a Noetherian domain, as asserted at the end of the
source example. -/
theorem exampleRing_isNoetherianDomain
    (k : Type u) [Field k] :
    IsNoetherianRing (exampleRing k) ∧ IsDomain (exampleRing k) := by
  sorry

/-- The example ring is not `(S_2)`. -/
theorem exampleRing_not_hasPropertySk_two
    (k : Type u) [Field k] :
    ¬ HasPropertySk (exampleRing k) 2 := by
  sorry

/-- The example ring is reflexive over itself. -/
theorem exampleRing_reflexive_as_module
    (k : Type u) [Field k] :
    Reflexive (exampleRing k) (exampleRing k) := by
  sorry

/-- The ambient polynomial module in the example is reflexive and `(S_2)`;
the existential records the finite-module instance required by the canonical
module-form Serre predicate. -/
theorem exampleModule_reflexive_and_hasPropertySk_two
    (k : Type u) [Field k] :
    ∃ hM : Module.Finite (exampleRing k) (MvPolynomial (Fin 2) k),
      Reflexive (exampleRing k) (MvPolynomial (Fin 2) k) ∧
        @HasPropertySkModule (exampleRing k) (MvPolynomial (Fin 2) k)
          _ _ _ hM 2 := by
  sorry

/-- The two Hom identities in the example, represented as linear
equivalences. -/
theorem example_hom_identities
    (k : Type u) [Field k] :
    Nonempty
        ((MvPolynomial (Fin 2) k →ₗ[exampleRing k] exampleRing k) ≃ₗ[
          exampleRing k] exampleMaximalIdeal k) ∧
      Nonempty
        ((exampleMaximalIdeal k →ₗ[exampleRing k] exampleRing k) ≃ₗ[
          exampleRing k] MvPolynomial (Fin 2) k) := by
  sorry

/-! ## Normal domains and height-one intersections -/

/-- The fraction-field map with the field in the left tensor factor.  This is
the tensor-product commutation of the map used in Unit 22, and gives the
target its natural `K`-module structure. -/
def fractionFieldTensorMapLeft
    (R M K : Type*) [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Field K] [Algebra R K]
    [IsFractionRing R K] :
    M →ₗ[R] K ⊗[R] M :=
  (TensorProduct.comm R M K).toLinearMap.comp
    (Formalization.Books.MoreAlgebra.Unit22.fractionFieldTensorMap
      (R := R) (M := M) (K := K))

/-- The image in `K ⊗[R] M` of the localization of `M` at a height-one
prime, after its local torsion is killed by the fraction-field map. -/
def heightOneModuleLocalizationImage
    (R M K : Type*) [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Field K] [Algebra R K]
    [IsFractionRing R K]
    (p : {p : PrimeSpectrum R // p.asIdeal.height = 1}) :
    Submodule R (K ⊗[R] M) :=
  Submodule.span R {z | ∃ m : M, ∃ s : R,
    s ∉ p.1.asIdeal ∧
      z = (algebraMap R K s)⁻¹ •
        fractionFieldTensorMapLeft (R := R) (M := M) (K := K) m}

/-- The intersection of all height-one localized module images. -/
def heightOneModuleLocalizationIntersection
    (R M K : Type*) [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Field K] [Algebra R K]
    [IsFractionRing R K] :
    Submodule R (K ⊗[R] M) :=
  ⨅ p : {p : PrimeSpectrum R // p.asIdeal.height = 1},
    heightOneModuleLocalizationImage R M K p

/-- The fraction-field map after quotienting by the torsion submodule. -/
noncomputable def fractionFieldTensorMapQuotient
    (R M K : Type*) [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Field K] [Algebra R K]
    [IsFractionRing R K] :
    (M ⧸ Submodule.torsion R M) →ₗ[R] K ⊗[R] M :=
  (TensorProduct.comm R M K).toLinearMap.comp
    ((Submodule.torsion R M).liftQ
      (Formalization.Books.MoreAlgebra.Unit22.fractionFieldTensorMap
        (R := R) (M := M) (K := K))
      (by
        rw [Formalization.Books.MoreAlgebra.Unit22.torsion_eq_ker_fractionFieldTensorMap
          (R := R) (M := M) (K := K)]))

/-- The height-one intersection written using the torsion-free quotient. -/
def heightOneTorsionQuotientIntersection
    (R M K : Type*) [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Field K] [Algebra R K]
    [IsFractionRing R K] :
    Submodule R (K ⊗[R] M) :=
  ⨅ p : {p : PrimeSpectrum R // p.asIdeal.height = 1},
    Submodule.span R {z | ∃ m : M ⧸ Submodule.torsion R M, ∃ s : R,
      s ∉ p.1.asIdeal ∧
        z = (algebraMap R K s)⁻¹ •
          fractionFieldTensorMapQuotient R M K m}

/-- The three equivalent characterizations of a finite module over a
Noetherian normal domain: reflexivity, torsion-free `(S_2)`, and the
height-one intersection criterion. -/
theorem reflexive_normal_iff_torsionFree_S2_heightOne
    {R M K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    List.TFAE
      [Reflexive R M,
       Module.IsTorsionFree R M ∧ HasPropertySkModule R M 2,
       Module.IsTorsionFree R M ∧
         Set.range (fractionFieldTensorMapLeft (R := R) (M := M) (K := K)) =
           (heightOneModuleLocalizationIntersection R M K : Set (K ⊗[R] M))] := by
  sorry

/-- The reflexive hull is modeled by the height-one intersection; the two
displayed source intersections agree after using the torsion-free quotient. -/
theorem reflexiveHull_heightOne_intersection
    {R M K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    Nonempty
        (reflexiveHull (R := R) (M := M) ≃ₗ[R]
          heightOneModuleLocalizationIntersection R M K) ∧
      heightOneModuleLocalizationIntersection R M K =
        heightOneTorsionQuotientIntersection R M K := by
  sorry

/-! ## Integral closures -/

/-- A finite integral closure in a finite field extension of a fraction field
is reflexive over a Noetherian normal domain. -/
theorem integralClosure_reflexive
    {A K L : Type*} [CommRing A] [IsNoetherianRing A]
    [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Module.Finite K L]
    [Module.Finite A (integralClosure A L)] :
    Reflexive A (integralClosure A L) := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit24
