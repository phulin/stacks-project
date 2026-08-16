import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Examples, Chapter 10: the category of complete modules is not abelian

This file records the constructions and statements in the chapter.  The
universal-property and counterexample proofs are intentionally deferred to the
proof stage.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum
open IsLocalRing

namespace Examples.Unit10

variable {R : Type u} [CommRing R]

/-! ## The category of complete modules -/

/-- The object property defining the full subcategory of `I`-adically complete modules. -/
abbrev CompleteModuleProperty (R : Type u) [CommRing R] (I : Ideal R) :
    ObjectProperty (ModuleCat.{u} R) :=
  fun M => IsAdicComplete I M

/-- The category of `I`-adically complete `R`-modules. -/
abbrev CompleteModuleCat (R : Type u) [CommRing R] (I : Ideal R) :=
  (CompleteModuleProperty R I).FullSubcategory

/-! ## The complete cokernel and complete kernel -/

/-- The `I`-adic neighbourhood of a submodule at level `n`. -/
def adicNeighbourhood (I : Ideal R) {M : Type u} [AddCommGroup M] [Module R M]
    (N : Submodule R M) (n : ℕ) : Submodule R M :=
  N ⊔ (I ^ n • (⊤ : Submodule R M))

/-- Algebraic form of being closed for the `I`-adic topology. -/
def IsAdicClosed (I : Ideal R) {M : Type u} [AddCommGroup M] [Module R M]
    (N : Submodule R M) : Prop :=
  N = ⨅ n : {n : ℕ // 1 ≤ n}, adicNeighbourhood I N n.1

/-- Algebraic continuity for a linear map in the `I`-adic filtrations. -/
def IsAdicContinuous (I : Ideal R) {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) : Prop :=
  ∀ n : ℕ, I ^ n • (⊤ : Submodule R M) ≤
    (I ^ n • (⊤ : Submodule R N)).comap f

/-- The source's closed-submodule equality is the definition of `IsAdicClosed`. -/
theorem isAdicClosed_iff_iInf (I : Ideal R) {M : Type u} [AddCommGroup M] [Module R M]
    (N : Submodule R M) :
    IsAdicClosed I N ↔ N = ⨅ n : {n : ℕ // 1 ≤ n}, adicNeighbourhood I N n.1 :=
  Iff.rfl

/-- Linear maps preserve the `I`-adic filtration in the sense needed here. -/
theorem linearMap_isAdicContinuous (I : Ideal R) {M N : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) : IsAdicContinuous I f := by
  sorry

/-- The kernel of a continuous map out of a complete module is `I`-adically closed. -/
theorem kernel_isAdicClosed (I : Ideal R) {M N : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (hM : IsAdicComplete I M) (hN : IsAdicComplete I N)
    (f : M →ₗ[R] N) (hf : IsAdicContinuous I f) :
    IsAdicClosed I f.ker := by
  sorry

/-- Closedness is equivalent to completeness of the quotient. -/
theorem isAdicClosed_iff_quotient_complete (I : Ideal R) {M : Type u}
    [AddCommGroup M] [Module R M] (hM : IsAdicComplete I M) (N : Submodule R M) :
    IsAdicClosed I N ↔ IsAdicComplete I (M ⧸ N) := by
  sorry

/-- For a finitely generated ideal, a closed submodule is complete in its own right. -/
theorem isAdicComplete_submodule_of_fg (I : Ideal R) (hI : I.FG) {M : Type u}
    [AddCommGroup M] [Module R M] (hM : IsAdicComplete I M) (N : Submodule R M)
    (hN : IsAdicClosed I N) : IsAdicComplete I N := by
  sorry

/-- The complete kernel is the ordinary module kernel, equipped with completeness. -/
noncomputable def completeModuleKernel (R : Type u) [CommRing R] (I : Ideal R)
    (hI : I.FG) {X Y : CompleteModuleCat R I} (f : X ⟶ Y) : CompleteModuleCat R I :=
  ⟨ModuleCat.of R f.hom.hom.ker,
    isAdicComplete_submodule_of_fg I hI X.property f.hom.hom.ker
      (kernel_isAdicClosed I X.property Y.property f.hom.hom
        (linearMap_isAdicContinuous I f.hom.hom))⟩

/-- The canonical inclusion of the complete kernel into the source. -/
noncomputable def completeModuleKernelι (R : Type u) [CommRing R] (I : Ideal R)
    (hI : I.FG) {X Y : CompleteModuleCat R I} (f : X ⟶ Y) :
    completeModuleKernel R I hI f ⟶ X :=
  ObjectProperty.homMk (ModuleCat.ofHom f.hom.hom.ker.subtype)

/-- The complete cokernel is the adic completion of the ordinary module cokernel. -/
noncomputable def completeModuleCokernel (R : Type u) [CommRing R] (I : Ideal R)
    (hI : I.FG) {X Y : CompleteModuleCat R I} (f : X ⟶ Y) : CompleteModuleCat R I :=
  ⟨ModuleCat.of R (AdicCompletion I (Y.obj ⧸ f.hom.hom.range)),
    AdicCompletion.isAdicComplete hI⟩

/-- The canonical projection onto the complete cokernel. -/
noncomputable def completeModuleCokernelπ (R : Type u) [CommRing R] (I : Ideal R)
    (hI : I.FG) {X Y : CompleteModuleCat R I} (f : X ⟶ Y) :
    Y ⟶ completeModuleCokernel R I hI f :=
  ObjectProperty.homMk <|
    ModuleCat.ofHom <|
      (AdicCompletion.of I (Y.obj ⧸ f.hom.hom.range)).comp
        (LinearMap.range f.hom.hom).mkQ

/-! The following interfaces package the source's assertions that these maps
are categorical kernels and cokernels. -/

noncomputable def completeModuleKernel_isKernel (R : Type u) [CommRing R] (I : Ideal R)
    (hI : I.FG) {X Y : CompleteModuleCat R I} (f : X ⟶ Y) :
    IsLimit (KernelFork.ofι (f := f) (completeModuleKernelι R I hI f) (by
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      ext x
      exact LinearMap.mem_ker.mp x.property)) := by
  sorry

noncomputable def completeModuleCokernel_isCokernel (R : Type u) [CommRing R] (I : Ideal R)
    (hI : I.FG) {X Y : CompleteModuleCat R I} (f : X ⟶ Y) :
    IsColimit (CokernelCofork.ofπ (f := f) (completeModuleCokernelπ R I hI f) (by
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      change (AdicCompletion.of I (Y.obj ⧸ f.hom.hom.range)).comp
          ((LinearMap.range f.hom.hom).mkQ.comp f.hom.hom) = 0
      rw [LinearMap.range_mkQ_comp, LinearMap.comp_zero])) := by
  sorry

/-! ## The closed-submodule lemma -/

/-- The three algebraic forms of the closed-submodule lemma. -/
theorem isAdicClosed_iff_iInf_quotient_complete (I : Ideal R) {M : Type u}
    [AddCommGroup M] [Module R M] (hM : IsAdicComplete I M) (N : Submodule R M) :
    IsAdicClosed I N ↔
      N = ⨅ n : {n : ℕ // 1 ≤ n}, adicNeighbourhood I N n.1 ∧
        IsAdicComplete I (M ⧸ N) := by
  sorry

/-! ## The `p`-adic example -/

/-- The principal ideal used for the `p`-adic filtration. -/
noncomputable def padicIdeal (p : ℕ) [Fact p.Prime] : Ideal ℤ_[p] :=
  Ideal.span {(p : ℤ_[p])}

theorem padicIdeal_eq_maximalIdeal (p : ℕ) [Fact p.Prime] :
    padicIdeal p = maximalIdeal ℤ_[p] := by
  exact PadicInt.maximalIdeal_eq_span_p.symm

theorem padicIdeal_fg (p : ℕ) [Fact p.Prime] : (padicIdeal p).FG := by
  refine ⟨{(p : ℤ_[p])}, ?_⟩
  simp [padicIdeal]

theorem padicIdeal_isAdicComplete (p : ℕ) [Fact p.Prime] :
    IsAdicComplete (padicIdeal p) ℤ_[p] := by
  rw [padicIdeal_eq_maximalIdeal]
  infer_instance

/-- A product of complete modules is complete for a finitely generated ideal. -/
theorem isAdicComplete_pi_of_fg (R : Type u) [CommRing R] (I : Ideal R) (hI : I.FG)
    {ι : Type u} (M : ι → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (hM : ∀ i, IsAdicComplete I (M i)) :
    IsAdicComplete I (∀ i, M i) := by
  sorry

theorem padicProduct_isAdicComplete (p : ℕ) [Fact p.Prime] :
    IsAdicComplete (padicIdeal p) (∀ _ : ℕ, ℤ_[p]) := by
  exact isAdicComplete_pi_of_fg (ℤ_[p]) (padicIdeal p) (padicIdeal_fg p)
    (fun _ : ℕ => ℤ_[p]) (fun _ => padicIdeal_isAdicComplete p)

/-- The finite-support diagonal map into the full product.

We index by `ℕ`, so index `n` corresponds to the source's positive index `n + 1`; this
keeps the displayed weights `1, p, p^2, ...` literal. -/
noncomputable def padicDiagonalBaseMap (p : ℕ) [Fact p.Prime] :
    (⨁ _ : ℕ, ℤ_[p]) →ₗ[ℤ_[p]] (∀ _ : ℕ, ℤ_[p]) :=
  DirectSum.toModule (ℤ_[p]) ℕ (∀ _ : ℕ, ℤ_[p])
    (fun n => (p : ℤ_[p]) ^ n •
      LinearMap.single (ℤ_[p]) (fun _ : ℕ => ℤ_[p]) n)

theorem padicDiagonalBaseMap_lof (p : ℕ) [Fact p.Prime] (n : ℕ) (x : ℤ_[p]) :
    padicDiagonalBaseMap p (DirectSum.lof (ℤ_[p]) ℕ (fun _ : ℕ => ℤ_[p]) n x) =
      Pi.single n ((p : ℤ_[p]) ^ n * x) := by
  sorry

/-- The completed diagonal map from the completion of the direct sum to the product. -/
noncomputable def padicDiagonalMap (p : ℕ) [Fact p.Prime] :
    AdicCompletion (padicIdeal p) (⨁ _ : ℕ, ℤ_[p]) →ₗ[ℤ_[p]] (∀ _ : ℕ, ℤ_[p]) :=
  letI : IsAdicComplete (padicIdeal p) (∀ _ : ℕ, ℤ_[p]) :=
    padicProduct_isAdicComplete p
  (AdicCompletion.ofLinearEquiv (padicIdeal p) (∀ _ : ℕ, ℤ_[p])).symm ∘ₗ
    (AdicCompletion.map (padicIdeal p) (padicDiagonalBaseMap p)).restrictScalars ℤ_[p]

/-- Power-filtration formulation of the assertion that coordinates tend to zero `p`-adically. -/
def PAdicDecay (p : ℕ) [Fact p.Prime] (x : ℕ → ℤ_[p]) : Prop :=
  ∀ n : ℕ, ∃ N : ℕ, ∀ i ≥ N, x i ∈ (padicIdeal p) ^ n

/-- The type of product vectors whose coordinates tend to zero `p`-adically. -/
def PAdicDecaySequence (p : ℕ) [Fact p.Prime] :=
  {x : (ℕ → ℤ_[p]) // PAdicDecay p x}

theorem padicCompletion_directSum_description (p : ℕ) [Fact p.Prime] :
    Nonempty
      (AdicCompletion (padicIdeal p) (⨁ n : ℕ, ℤ_[p]) ≃
        PAdicDecaySequence p) := by
  sorry

/-- Algebraic `I`-adic closure of a subset of a module. -/
def InAdicClosure (I : Ideal R) {M : Type u} [AddCommGroup M] [Module R M]
    (x : M) (s : Set M) : Prop :=
  ∀ n : ℕ, ∃ y, y ∈ s ∧ x - y ∈ I ^ n • (⊤ : Submodule R M)

/-- The product vector used to witness failure of surjectivity. -/
noncomputable def padicGeometricPoint (p : ℕ) [Fact p.Prime] : ℕ → ℤ_[p] :=
  fun n => (p : ℤ_[p]) ^ n

theorem padicGeometricPoint_mem_adicClosure_range (p : ℕ) [Fact p.Prime] :
    InAdicClosure (padicIdeal p) (padicGeometricPoint p)
      (Set.range (padicDiagonalMap p)) := by
  sorry

theorem padicGeometricPoint_not_mem_range (p : ℕ) [Fact p.Prime] :
    padicGeometricPoint p ∉ Set.range (padicDiagonalMap p) := by
  sorry

/-! ## Categorical conclusion -/

noncomputable def padicDiagonalDomain (p : ℕ) [Fact p.Prime] :
    CompleteModuleCat (ℤ_[p]) (padicIdeal p) :=
  ⟨ModuleCat.of (ℤ_[p])
      (AdicCompletion (padicIdeal p) (⨁ _ : ℕ, ℤ_[p])),
    AdicCompletion.isAdicComplete (padicIdeal_fg p)⟩

noncomputable def padicDiagonalTarget (p : ℕ) [Fact p.Prime] :
    CompleteModuleCat (ℤ_[p]) (padicIdeal p) :=
  ⟨ModuleCat.of (ℤ_[p]) (∀ _ : ℕ, ℤ_[p]), padicProduct_isAdicComplete p⟩

noncomputable def padicDiagonalCategoryHom (p : ℕ) [Fact p.Prime] :
    padicDiagonalDomain p ⟶ padicDiagonalTarget p :=
  ObjectProperty.homMk (ModuleCat.ofHom (padicDiagonalMap p))

noncomputable def completeModuleCoimage (R : Type u) [CommRing R] (I : Ideal R)
    (hI : I.FG) {X Y : CompleteModuleCat R I} (f : X ⟶ Y) :=
  completeModuleCokernel R I hI (completeModuleKernelι R I hI f)

noncomputable def completeModuleImage (R : Type u) [CommRing R] (I : Ideal R)
    (hI : I.FG) {X Y : CompleteModuleCat R I} (f : X ⟶ Y) :=
  completeModuleKernel R I hI (completeModuleCokernelπ R I hI f)

/-- The canonical coimage-to-image comparison supplied by the two universal properties. -/
theorem completeModuleCoimageImageComparison_exists (R : Type u) [CommRing R] (I : Ideal R)
    (hI : I.FG) {X Y : CompleteModuleCat R I} (f : X ⟶ Y) :
    ∃ c : completeModuleCoimage R I hI f ⟶ completeModuleImage R I hI f,
      (completeModuleCokernelπ R I hI (completeModuleKernelι R I hI f) ≫ c) ≫
          completeModuleKernelι R I hI (completeModuleCokernelπ R I hI f) = f := by
  sorry

noncomputable def completeModuleCoimageImageComparison (R : Type u) [CommRing R]
    (I : Ideal R) (hI : I.FG) {X Y : CompleteModuleCat R I} (f : X ⟶ Y) :
    completeModuleCoimage R I hI f ⟶ completeModuleImage R I hI f :=
  Classical.choose (completeModuleCoimageImageComparison_exists R I hI f)

theorem completeModuleCoimageImageComparison_fac (R : Type u) [CommRing R] (I : Ideal R)
    (hI : I.FG) {X Y : CompleteModuleCat R I} (f : X ⟶ Y) :
    (completeModuleCokernelπ R I hI (completeModuleKernelι R I hI f) ≫
        completeModuleCoimageImageComparison R I hI f) ≫
        completeModuleKernelι R I hI (completeModuleCokernelπ R I hI f) = f :=
  Classical.choose_spec (completeModuleCoimageImageComparison_exists R I hI f)

theorem padicDiagonal_coimageImageComparison_not_isIso (p : ℕ) [Fact p.Prime] :
    ¬ IsIso (completeModuleCoimageImageComparison (ℤ_[p]) (padicIdeal p)
      (padicIdeal_fg p) (padicDiagonalCategoryHom p)) := by
  sorry

/-- Complete modules have kernels and cokernels, with the constructions above. -/
theorem completeModuleCat_has_kernels_and_cokernels (R : Type u) [CommRing R] (I : Ideal R)
    (hI : I.FG) :
    HasKernels (CompleteModuleCat R I) ∧ HasCokernels (CompleteModuleCat R I) := by
  sorry

/-- The chosen `p`-adic coefficient ring is Noetherian. -/
theorem padicIntegers_isNoetherianRing (p : ℕ) [Fact p.Prime] :
    IsNoetherianRing ℤ_[p] := by
  infer_instance

/-- The complete-module category is therefore a kernels-and-cokernels category which is not
abelian in general, even for a Noetherian coefficient ring. -/
theorem padicCompleteModuleCat_has_kernels_cokernels_not_abelian (p : ℕ) [Fact p.Prime] :
    HasKernels (CompleteModuleCat (ℤ_[p]) (padicIdeal p)) ∧
      HasCokernels (CompleteModuleCat (ℤ_[p]) (padicIdeal p)) ∧
      ¬ Nonempty (Abelian (CompleteModuleCat (ℤ_[p]) (padicIdeal p))) := by
  sorry

end Examples.Unit10
