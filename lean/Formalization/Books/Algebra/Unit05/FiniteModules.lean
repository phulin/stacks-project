import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.RingHom
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Commutative Algebra, Chapter 5: Finite modules and finitely presented modules

The source's finite and finitely presented module notions are Mathlib's
`Module.Finite` and `Module.FinitePresentation`.  The source-facing results
below use finite free modules `(Fin n → R)` and Mathlib's canonical short exact
complexes of modules.
-/

namespace Formalization.Books.Algebra.Unit05

open CategoryTheory

universe u v

/-! ## Definitions and finite free presentations -/

-- “Finite module” and “finitely presented module” are respectively
-- `Module.Finite` and `Module.FinitePresentation`.

/-- The finite-module definition is equivalent to a finite free surjection. -/
theorem finite_iff_exists_fin_surjective
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    Module.Finite R M ↔
      ∃ (n : ℕ) (f : (Fin n → R) →ₗ[R] M), Function.Surjective f := by
  constructor
  · exact fun h =>
      letI : Module.Finite R M := h
      Module.Finite.exists_fin' R M
  · rintro ⟨n, f, hf⟩
    exact Module.Finite.of_surjective f hf

/-- A finite presentation is exactly a right-exact sequence of finite free
modules ending in the given module. -/
theorem finitePresentation_iff_exists_fin_presentation
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    Module.FinitePresentation R M ↔
      ∃ (n m : ℕ)
        (f : (Fin n → R) →ₗ[R] M)
        (g : (Fin m → R) →ₗ[R] (Fin n → R)),
        Function.Surjective f ∧ Function.Exact g f := by
  constructor
  · exact fun h =>
      letI : Module.FinitePresentation R M := h
      Module.FinitePresentation.exists_fin' R M
  · rintro ⟨n, m, f, g, hf, hgf⟩
    apply Module.finitePresentation_of_surjective f hf
    rw [LinearMap.exact_iff.mp hgf]
    exact Submodule.fg_range g

/-! ## Lifting maps -/

/-- A map out of a finite free module lifts through any map containing its
image. -/
theorem linearMap_exists_factorization_of_range_le
    {R : Type u} {M N : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    {n : ℕ} (α : (Fin n → R) →ₗ[R] M) (β : N →ₗ[R] M)
    (hαβ : LinearMap.range α ≤ LinearMap.range β) :
    ∃ γ : (Fin n → R) →ₗ[R] N, α = β.comp γ := by
  classical
  choose x hx using fun i : Fin n =>
    hαβ (LinearMap.mem_range_self α (Pi.single i 1))
  refine ⟨Fintype.linearCombination R x, ?_⟩
  apply LinearMap.pi_ext
  intro i r
  simp only [LinearMap.comp_apply, Fintype.linearCombination_apply_single, map_smul]
  rw [show Pi.single i r = r • Pi.single i 1 by
    ext j
    by_cases h : i = j <;> simp [h]]
  simp [hx i]

/-! ## Extensions -/

/- The source's sequence

    0 → M₁ → M₂ → M₃ → 0

  is represented by `S : ShortComplex (ModuleCat R)` together with
  `hS : S.ShortExact`. -/

/-- Finite modules are closed under extensions. -/
theorem finite_middle_of_shortExact
    {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact)
    (h₁ : Module.Finite R S.X₁) (h₃ : Module.Finite R S.X₃) :
    Module.Finite R S.X₂ := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R S.X₃
  have hf_top : LinearMap.range f = (⊤ : Submodule R S.X₃) :=
    LinearMap.range_eq_top.mpr hf
  have hg_top : LinearMap.range S.g.hom = (⊤ : Submodule R S.X₃) :=
    LinearMap.range_eq_top.mpr hS.moduleCat_surjective_g
  obtain ⟨γ, hγ⟩ := linearMap_exists_factorization_of_range_le f S.g.hom (by
    rw [hf_top, hg_top])
  let F : S.X₁ × (Fin n → R) →ₗ[R] S.X₂ :=
    S.f.hom.comp (LinearMap.fst R S.X₁ (Fin n → R)) +
      γ.comp (LinearMap.snd R S.X₁ (Fin n → R))
  refine Module.Finite.of_surjective F ?_
  intro x₂
  obtain ⟨a, ha⟩ := hf (S.g.hom x₂)
  have hx : S.g.hom (x₂ - γ a) = 0 := by
    rw [map_sub, ← ha, hγ, LinearMap.comp_apply, sub_self]
  obtain ⟨x₁, hx₁⟩ := S.moduleCat_exact_iff.mp hS.exact (x₂ - γ a) hx
  refine ⟨(x₁, a), ?_⟩
  simp [F, hx₁]

/-- An extension of two finitely presented modules is finitely presented. -/
theorem finitePresentation_middle_of_shortExact
    {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact)
    (h₁ : Module.FinitePresentation R S.X₁)
    (h₃ : Module.FinitePresentation R S.X₃) :
    Module.FinitePresentation R S.X₂ := by
  let e : S.X₁ ≃ₗ[R] LinearMap.ker S.g.hom :=
    LinearEquiv.ofBijective S.moduleCatToCycles (by
      constructor
      · intro x y h
        exact hS.moduleCat_injective_f (congrArg Subtype.val h)
      · rintro ⟨x, hx⟩
        obtain ⟨x₁, hx₁⟩ := S.moduleCat_exact_iff.mp hS.exact x hx
        exact ⟨x₁, Subtype.ext hx₁⟩)
  have hker : Module.FinitePresentation R (LinearMap.ker S.g.hom) :=
    Module.FinitePresentation.of_equiv e
  exact @Module.finitePresentation_of_ker R S.X₂ S.X₃ _ _ _ _ _ h₃ S.g.hom
    hS.moduleCat_surjective_g hker

/-- A quotient of a finite module is finite. -/
theorem finite_right_of_shortExact
    {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact)
    (h₂ : Module.Finite R S.X₂) :
    Module.Finite R S.X₃ := by
  exact Module.Finite.of_surjective S.g.hom hS.moduleCat_surjective_g

/-- If the middle module is finitely presented and the left module is finite,
then the quotient is finitely presented. -/
theorem finitePresentation_right_of_shortExact
    {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact)
    (h₂ : Module.FinitePresentation R S.X₂)
    (h₁ : Module.Finite R S.X₁) :
    Module.FinitePresentation R S.X₃ := by
  apply Module.finitePresentation_of_surjective S.g.hom hS.moduleCat_surjective_g
  simpa only [← hS.exact.moduleCat_range_eq_ker] using (Submodule.fg_range S.f.hom)

/-- If the quotient is finitely presented and the middle module is finite,
then the left module is finite. -/
theorem finite_left_of_shortExact
    {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact)
    (h₃ : Module.FinitePresentation R S.X₃)
    (h₂ : Module.Finite R S.X₂) :
    Module.Finite R S.X₁ := by
  refine ⟨?_⟩
  rw [← Submodule.fg_map_iff S.f.hom hS.moduleCat_injective_f]
  rw [Submodule.map_top, hS.exact.moduleCat_range_eq_ker]
  exact Module.FinitePresentation.fg_ker S.g.hom hS.moduleCat_surjective_g

/-! ## Filtrations by cyclic modules -/

/-- A finite filtration whose successive factors are cyclic modules. -/
structure FiniteCyclicFiltration
    (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] where
  length : ℕ
  stage : Fin (length + 1) → Submodule R M
  ideal : Fin length → Ideal R
  zero : stage 0 = ⊥
  top : stage (Fin.last length) = ⊤
  step : ∀ i : Fin length,
    stage (Fin.castSucc i) ≤ stage (Fin.succ i)
  finite : ∀ i, Module.Finite R (stage i)
  quotient : ∀ i : Fin length,
    Nonempty
      (((stage (Fin.succ i)) ⧸
        (stage (Fin.castSucc i)).comap (stage (Fin.succ i)).subtype)
        ≃ₗ[R] (R ⧸ ideal i))

/-- Every finite module has a finite filtration with cyclic successive
quotients. -/
theorem exists_finiteCyclicFiltration
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (hM : Module.Finite R M) :
    Nonempty (FiniteCyclicFiltration R M) := by
  obtain ⟨n, s, hs⟩ : ∃ (n : ℕ) (s : Fin n → M), Submodule.span R (Set.range s) = ⊤ :=
    @Module.Finite.exists_fin R M _ _ _ hM
  let stage : Fin (n + 1) → Submodule R M :=
    fun i => Submodule.span R (s '' {j : Fin n | (j : ℕ) < i.val})
  have hzero : stage 0 = ⊥ := by simp [stage]
  have htop : stage (Fin.last n) = ⊤ := by
    change Submodule.span R (s '' {j : Fin n | (j : ℕ) < n}) = ⊤
    rw [← hs]
    congr 1
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      refine ⟨j, ?_, rfl⟩
      simp
  have hstep : ∀ i : Fin n, stage (Fin.castSucc i) ≤ stage (Fin.succ i) := by
    intro i
    apply Submodule.span_mono
    rintro y ⟨j, hj, rfl⟩
    refine ⟨j, ?_, rfl⟩
    change (j : ℕ) < i.val + 1
    exact Nat.lt_succ_of_lt (show (j : ℕ) < i.val from hj)
  have hfinite : ∀ i, Module.Finite R (stage i) := by
    intro i
    apply Module.Finite.of_fg
    apply Submodule.fg_span
    exact (Set.toFinite {j : Fin n | (j : ℕ) < i.val}).image s
  have hsup : ∀ i : Fin n,
      stage (Fin.succ i) = stage (Fin.castSucc i) ⊔ R ∙ s i := by
    intro i
    simp only [stage, Fin.val_succ, Fin.val_castSucc]
    rw [← Submodule.span_union]
    apply congrArg (Submodule.span R)
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      by_cases hji : j = i
      · subst j
        exact Or.inr rfl
      · left
        refine ⟨j, ?_, rfl⟩
        change (j : ℕ) < i.val
        have hne : (j : ℕ) ≠ i.val := by
          intro h
          apply hji
          exact Fin.ext h
        have hjle : (j : ℕ) ≤ i.val := by
          apply Nat.le_of_lt_succ
          exact (show (j : ℕ) < i.val + 1 from by simpa using hj)
        exact lt_of_le_of_ne hjle hne
    · intro hx
      rcases hx with hx | hx
      · rcases hx with ⟨j, hj, rfl⟩
        refine ⟨j, ?_, rfl⟩
        change (j : ℕ) < i.val + 1
        exact Nat.lt_succ_of_lt (show (j : ℕ) < i.val from hj)
      · rw [Set.mem_singleton_iff] at hx
        subst x
        exact ⟨i, by simp, rfl⟩
  have hquot : ∀ i : Fin n,
      ∃ (I : Ideal R),
        Nonempty (((stage (Fin.succ i)) ⧸
          (stage (Fin.castSucc i)).comap (stage (Fin.succ i)).subtype) ≃ₗ[R] (R ⧸ I)) := by
    intro i
    let A := stage (Fin.castSucc i)
    let B := stage (Fin.succ i)
    have hAB : B = A ⊔ R ∙ s i := by simpa [A, B] using hsup i
    have hxi : s i ∈ B := by
      rw [hAB]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    let xi : B := ⟨s i, hxi⟩
    let q : B →ₗ[R] (B ⧸ A.comap B.subtype) :=
      (A.comap B.subtype).mkQ
    let φ : R →ₗ[R] (B ⧸ A.comap B.subtype) :=
      q.comp (LinearMap.toSpanSingleton R B xi)
    have hφ : Function.Surjective φ := by
      intro y
      obtain ⟨b, rfl⟩ := (A.comap B.subtype).mkQ_surjective y
      have hb : b.val ∈ A ⊔ R ∙ s i := by
        rw [← hAB]
        exact b.property
      obtain ⟨a, ha, z, hz, hsum⟩ := Submodule.mem_sup.mp hb
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hz
      refine ⟨r, ?_⟩
      apply (Submodule.Quotient.eq _).2
      change r • s i - b.val ∈ A
      rw [← hsum, hr]
      simpa [sub_eq_add_neg, add_assoc] using A.neg_mem ha
    let I : Ideal R := LinearMap.ker φ
    exact ⟨I, ⟨(LinearMap.quotKerEquivOfSurjective φ hφ).symm⟩⟩
  choose ideal hideal using hquot
  refine ⟨{
    length := n
    stage := stage
    ideal := ideal
    zero := hzero
    top := htop
    step := hstep
    finite := hfinite
    quotient := hideal
  }⟩

/-! ## Finite modules over a larger ring -/

/-- A module finite over a ring is finite over any larger ring acting on it;
the smaller action is the one induced by the ring map. -/
theorem finite_over_ringHom
    {R S M : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) [AddCommGroup M] [Module S M]
    (hM : letI : Module R M := Module.compHom M f; Module.Finite R M) :
    Module.Finite S M := by
  exact
    letI : Module R S := Module.compHom S f
    letI : Module R M := Module.compHom M f
    letI : IsScalarTower R S M := SMul.comp.isScalarTower f
    letI : Module.Finite R M := hM
    Module.Finite.of_restrictScalars_finite R S M

end Formalization.Books.Algebra.Unit05
