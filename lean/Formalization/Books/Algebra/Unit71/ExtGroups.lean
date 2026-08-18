import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.Algebra.Category.ModuleCat.LeftResolution
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Commutative Algebra, Chapter 71: Ext groups

The chapter's resolutions are represented by Mathlib's projective-resolution
interface.  The source asks for free resolutions, so the source-facing
structures below retain the same canonical resolution together with the
degreewise freeness (and finite generation) hypotheses.
-/

namespace Formalization.Books.Algebra.Unit71

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

universe u

/-! ## Resolutions -/

/-- Chain complexes of `R`-modules indexed by the nonnegative integers. -/
abbrev ModuleChainComplex (R : Type u) [Ring R] :=
  ChainComplex (ModuleCat.{u} R) ℕ

/-- Cochain complexes of `R`-modules indexed by the nonnegative integers. -/
abbrev ModuleCochainComplex (R : Type u) [Ring R] :=
  CochainComplex (ModuleCat.{u} R) ℕ

/-- A resolution is an exact nonnegative chain complex together with an
epimorphic augmentation to the module in degree zero. -/
structure Resolution (R : Type u) [Ring R] (M : ModuleCat.{u} R) where
  complex : ModuleChainComplex R
  augmentation : complex.X 0 ⟶ M
  augmentation_condition : complex.d 1 0 ≫ augmentation = 0
  exact_zero :
    (ShortComplex.mk (complex.d 1 0) augmentation augmentation_condition).Exact
  exact_succ : ∀ n,
    (ShortComplex.mk (complex.d (n + 2) (n + 1))
      (complex.d (n + 1) n) (complex.d_comp_d (n + 2) (n + 1) n)).Exact
  augmentation_epi : Epi augmentation

/-- A resolution whose terms are free modules. -/
structure FreeResolution (R : Type u) [Ring R] (M : ModuleCat.{u} R) where
  resolution : Resolution R M
  free : ∀ n, Module.Free R (resolution.complex.X n)

/-- A resolution whose terms are finite free modules. -/
structure FiniteFreeResolution (R : Type u) [Ring R] (M : ModuleCat.{u} R) where
  resolution : FreeResolution R M
  finite : ∀ n, Module.Finite R (resolution.resolution.complex.X n)

/-- A complex of free modules augmented to a module.

This is the source-facing hypothesis in the comparison lemma: unlike a
`FreeResolution`, the complex itself is not required to be exact. -/
structure FreeAugmentedComplex (R : Type u) [Ring R] (M : ModuleCat.{u} R) where
  complex : ModuleChainComplex R
  augmentation : complex.X 0 ⟶ M
  augmentation_condition : complex.d 1 0 ≫ augmentation = 0
  free : ∀ n, Module.Free R (complex.X n)

/-- A projective resolution supplies the preceding source-facing resolution
data. -/
noncomputable def projectiveResolutionToResolution {R : Type u} [Ring R]
    {M : ModuleCat.{u} R} (P : CategoryTheory.ProjectiveResolution M) :
    Resolution R M where
  complex := P.complex
  augmentation := P.π.f 0
  augmentation_condition := P.complex_d_comp_π_f_zero
  exact_zero := by simpa using P.exact₀
  exact_succ := fun n => by simpa using P.exact_succ n
  augmentation_epi := by
    exact Limits.epi_of_isColimit_cofork P.isColimitCokernelCofork

/-- The complex underlying a free resolution. -/
abbrev FreeResolution.complex {R : Type u} [Ring R] {M : ModuleCat.{u} R}
    (F : FreeResolution R M) : ModuleChainComplex R :=
  F.resolution.complex

/-- The complex underlying a finite-free resolution. -/
abbrev FiniteFreeResolution.complex {R : Type u} [Ring R] {M : ModuleCat.{u} R}
    (F : FiniteFreeResolution R M) : ModuleChainComplex R :=
  F.resolution.resolution.complex

/-- Exactness at the augmentation term of a resolution. -/
theorem resolution_exact_zero {R : Type u} [Ring R] {M : ModuleCat.{u} R}
    (F : Resolution R M) :
    (ShortComplex.mk (F.complex.d 1 0) F.augmentation
      F.augmentation_condition).Exact :=
  F.exact_zero

/-- Exactness at every positive term of a resolution. -/
theorem resolution_exact_succ {R : Type u} [Ring R] {M : ModuleCat.{u} R}
    (F : Resolution R M) (n : ℕ) :
    (ShortComplex.mk (F.complex.d (n + 2) (n + 1))
      (F.complex.d (n + 1) n) (F.complex.d_comp_d (n + 2) (n + 1) n)).Exact :=
  F.exact_succ n

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Every module admits a free resolution. -/
theorem exists_free_resolution {R : Type u} [Ring R] (M : ModuleCat.{u} R) :
    Nonempty (FreeResolution R M) := by
  let ι := ObjectProperty.ι (isProjective (ModuleCat.{u} R))
  let Λ := ModuleCat.projectiveResolution R
  let C := Λ.chainComplexFunctor.obj M
  let K := (ι.mapHomologicalComplex (ComplexShape.down ℕ)).obj C
  let e0 : C.X 0 ≅ Λ.F.obj M := by
    simpa [C, CategoryTheory.Abelian.LeftResolution.chainComplexFunctor] using
      Λ.chainComplexXZeroIso M
  let e1 : C.X 1 ≅ Λ.F.obj (kernel (Λ.π.app M)) := by
    simpa [C, CategoryTheory.Abelian.LeftResolution.chainComplexFunctor] using
      Λ.chainComplexXOneIso M
  let e1' : K.X 1 ≅ (Λ.F ⋙ ι).obj (kernel (Λ.π.app M)) := by
    simpa only [K, Functor.mapHomologicalComplex_obj_X, Functor.comp_obj] using ι.mapIso e1
  let e0' : K.X 0 ≅ (Λ.F ⋙ ι).obj M := by
    simpa only [K, Functor.mapHomologicalComplex_obj_X, Functor.comp_obj] using ι.mapIso e0
  let aug := e0'.hom ≫ Λ.π.app M
  have exact_of_epi_kernel {X Y P : ModuleCat.{u} R} (f : X ⟶ Y)
      (p : P ⟶ kernel f) [Epi p] :
      (ShortComplex.mk (p ≫ kernel.ι f) f (by simp)).Exact := by
    let α : ShortComplex.mk (p ≫ kernel.ι f) f (by simp) ⟶
        ShortComplex.mk (kernel.ι f) f (by simp) :=
      { τ₁ := p, τ₂ := 𝟙 _, τ₃ := 𝟙 _ }
    rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono α]
    apply ShortComplex.exact_of_f_is_kernel
    apply kernelIsKernel
  have hdK : K.d 1 0 =
      e1'.hom ≫ Λ.π.app (kernel (Λ.π.app M)) ≫ kernel.ι (Λ.π.app M) ≫ e0'.inv := by
    change ι.map (C.d 1 0) =
      ι.map e1.hom ≫ Λ.π.app (kernel (Λ.π.app M)) ≫ kernel.ι (Λ.π.app M) ≫ ι.map e0.inv
    change ι.map ((Λ.chainComplex M).d 1 0) =
      ι.map (Λ.chainComplexXOneIso M).hom ≫
        Λ.π.app (kernel (Λ.π.app M)) ≫ kernel.ι (Λ.π.app M) ≫
          ι.map (Λ.chainComplexXZeroIso M).inv
    exact Λ.map_chainComplex_d_1_0 M
  have hzero : K.d 1 0 ≫ aug = 0 := by
    rw [hdK]
    simp [aug, Category.assoc]
  refine ⟨⟨⟨K, aug, ?_, ?_, ?_, ?_⟩, ?_⟩⟩
  · change K.d 1 0 ≫ aug = 0
    exact hzero
  · let f := Λ.π.app M
    let p := Λ.π.app (kernel f)
    have hS₂ :
        (ShortComplex.mk (p ≫ kernel.ι f) f (by simp)).Exact :=
      exact_of_epi_kernel f p
    let S₁ := ShortComplex.mk (K.d 1 0) aug hzero
    let S₂ := ShortComplex.mk (p ≫ kernel.ι f) f (by simp)
    let i : S₁ ≅ S₂ := ShortComplex.isoMk e1' e0' (Iso.refl _)
      (by
        have hh := congrArg (fun q : K.X 1 ⟶ K.X 0 => q ≫ e0'.hom) hdK.symm
        simpa [S₁, S₂, aug, f, p, Category.assoc] using hh)
      (by simp [S₁, S₂, aug, f])
    exact (ShortComplex.exact_iff_of_iso i).2 hS₂
  · intro n
    apply (HomologicalComplex.exactAt_iff' (K := K) (j := n + 1)
      (i := n + 2) (k := n) (by simp) (by simp)).mp
    simpa [K, C, CategoryTheory.Abelian.LeftResolution.chainComplexFunctor] using
      Λ.exactAt_map_chainComplex_succ M n
  · infer_instance
  · intro n
    have free_F : ∀ X : ModuleCat.{u} R,
        Module.Free R (ι.obj (Λ.F.obj X)) := by
      intro X
      dsimp [Λ, ModuleCat.projectiveResolution]
      change Module.Free R ((X : Type u) →₀ R)
      infer_instance
    obtain _ | _ | n := n
    · exact Module.Free.of_equiv' (free_F M)
        ((ι.mapIso (Λ.chainComplexXZeroIso M)).symm.toLinearEquiv)
    · exact Module.Free.of_equiv' (free_F _)
        ((ι.mapIso (Λ.chainComplexXOneIso M)).symm.toLinearEquiv)
    · exact Module.Free.of_equiv' (free_F _)
        ((ι.mapIso (Λ.chainComplexXIso M n)).symm.toLinearEquiv)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Noetherian finite modules admit finite-free resolutions. -/
theorem exists_finite_free_resolution {R : Type u} [Ring R]
    [IsNoetherianRing R] (M : ModuleCat.{u} R) [Module.Finite R M] :
    Nonempty (FiniteFreeResolution R M) := by
  classical
  let globalEnough : EnoughProjectives (ModuleCat.{u} R) := inferInstance
  let finitePresentation : ∀ (X : ModuleCat.{u} R), Module.Finite R X →
      ProjectivePresentation X := fun X hX => by
    letI := hX
    let h := Module.Finite.exists_fin' R X
    let n := h.choose
    let f := h.choose_spec.choose
    have hf : Function.Surjective f := h.choose_spec.choose_spec
    let P := ModuleCat.of R (Fin n → R)
    let p : P ⟶ X := ModuleCat.ofHom f
    letI : Projective P := ModuleCat.projective_of_free (Module.Free.chooseBasis R _)
    letI : Epi p := (ModuleCat.epi_iff_surjective p).mpr hf
    exact ⟨P, p⟩
  let presentation : ∀ X : ModuleCat.{u} R, ProjectivePresentation X := fun X =>
    if hX : Module.Finite R X then finitePresentation X hX else
      (globalEnough.presentation X).some
  let over : ModuleCat.{u} R → ModuleCat.{u} R := fun X => (presentation X).p
  let pi : ∀ X : ModuleCat.{u} R, over X ⟶ X :=
    fun X => (presentation X).f
  have finite_over : ∀ X : ModuleCat.{u} R, Module.Finite R X →
      Module.Finite R ↑(over X) := by
    intro X hX
    have heq : over X = (finitePresentation X hX).p := by
      dsimp [over, presentation]
      rw [dif_pos hX]
    let e : over X ≅ (finitePresentation X hX).p := eqToIso heq
    let _ : IsNoetherian R ((finitePresentation X hX).p : Type u) :=
      isNoetherian_of_isNoetherianRing_of_finite R _
    apply Module.Finite.of_injective (R := R) (S := R)
      (M := (over X : Type u)) (N := ((finitePresentation X hX).p : Type u))
      e.toLinearEquiv.toLinearMap
    exact e.toLinearEquiv.injective
  have free_over : ∀ X : ModuleCat.{u} R, Module.Finite R X →
      Module.Free R ↑(over X) := by
    intro X hX
    have heq : over X = (finitePresentation X hX).p := by
      dsimp [over, presentation]
      rw [dif_pos hX]
    let e : over X ≅ (finitePresentation X hX).p := eqToIso heq
    have hfree : Module.Free R ((finitePresentation X hX).p : Type u) := by
      dsimp [finitePresentation]
      infer_instance
    exact Module.Free.of_equiv' hfree e.symm.toLinearEquiv
  have epi_pi (X : ModuleCat.{u} R) : Epi (pi X) :=
    (presentation X).epi
  have kernel_finite {X Y : ModuleCat.{u} R} (f : X ⟶ Y)
      [Module.Finite R X] : Module.Finite R ↑(kernel f) := by
    let _ : IsNoetherian R (X : Type u) :=
      isNoetherian_of_isNoetherianRing_of_finite R (X : Type u)
    apply Module.Finite.of_injective (R := R) (S := R)
      (M := ((kernel f : ModuleCat.{u} R) : Type u)) (N := (X : Type u))
      (kernel.ι f).hom
    exact (ModuleCat.mono_iff_injective _).mp inferInstance
  have exact_d_f' {X Y : ModuleCat.{u} R} (f : X ⟶ Y) :
      (ShortComplex.mk (pi (kernel f) ≫ kernel.ι f) f (by simp)).Exact := by
    let _ : Epi (pi (kernel f)) := epi_pi (kernel f)
    let α : ShortComplex.mk (pi (kernel f) ≫ kernel.ι f) f (by simp) ⟶
        ShortComplex.mk (kernel.ι f) f (by simp) :=
      { τ₁ := pi (kernel f), τ₂ := 𝟙 _, τ₃ := 𝟙 _ }
    rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono α]
    apply ShortComplex.exact_of_f_is_kernel
    apply kernelIsKernel
  let C : ModuleChainComplex R :=
    ChainComplex.mk' (over M) (over (kernel (pi M)))
      (pi (kernel (pi M)) ≫ kernel.ι (pi M))
      (fun {X₀ X₁} f => ⟨over (kernel f), pi (kernel f) ≫ kernel.ι f, by simp⟩)
  have finite_C : ∀ n : ℕ, Module.Finite R (C.X n) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      obtain _ | _ | n := n
      · change Module.Finite R ↑(over M)
        exact finite_over M inferInstance
      · change Module.Finite R ↑(over (kernel (pi M)))
        apply finite_over
        let _ : Module.Finite R ↑(over M) := finite_over M inferInstance
        exact kernel_finite (pi M)
      · let f := C.d (n + 1) n
        let _ : Module.Finite R (C.X (n + 1)) :=
          ih (n + 1) (Nat.lt_succ_self (n + 1))
        let _ : Module.Finite R ↑(over (kernel f)) :=
          finite_over _ (kernel_finite f)
        let e : C.X (n + 2) ≅ over (kernel f) := by
          simpa [C, f] using
            (ChainComplex.mk'XIso (over M) (over (kernel (pi M)))
              (pi (kernel (pi M)) ≫ kernel.ι (pi M))
              (fun {X₀ X₁} g =>
                ⟨over (kernel g), pi (kernel g) ≫ kernel.ι g, by simp⟩) n)
        let _ : IsNoetherian R (over (kernel f) : Type u) :=
          isNoetherian_of_isNoetherianRing_of_finite R _
        apply Module.Finite.of_injective (R := R) (S := R)
          (M := (C.X (n + 2) : Type u)) (N := (over (kernel f) : Type u))
          e.toLinearEquiv.toLinearMap
        exact e.toLinearEquiv.injective
  have free_C : ∀ n : ℕ, Module.Free R (C.X n) := by
    intro n
    obtain _ | _ | n := n
    · change Module.Free R ↑(over M)
      exact free_over M inferInstance
    · change Module.Free R ↑(over (kernel (pi M)))
      apply free_over
      let _ : Module.Finite R ↑(over M) := finite_over M inferInstance
      exact kernel_finite (pi M)
    · let f := C.d (n + 1) n
      let _ : Module.Finite R (C.X (n + 1)) := finite_C (n + 1)
      have hfree : Module.Free R ↑(over (kernel f)) :=
        free_over _ (kernel_finite f)
      let e : C.X (n + 2) ≅ over (kernel f) := by
        simpa [C, f] using
          (ChainComplex.mk'XIso (over M) (over (kernel (pi M)))
            (pi (kernel (pi M)) ≫ kernel.ι (pi M))
            (fun {X₀ X₁} g =>
              ⟨over (kernel g), pi (kernel g) ≫ kernel.ι g, by simp⟩) n)
      exact Module.Free.of_equiv' hfree e.symm.toLinearEquiv
  have hzero : C.d 1 0 ≫ pi M = 0 := by
    change (pi (kernel (pi M)) ≫ kernel.ι (pi M)) ≫ pi M = 0
    simp
  have hexact_zero :
      (ShortComplex.mk (C.d 1 0) (pi M) hzero).Exact := by
    simpa [C] using exact_d_f' (pi M)
  have hexact_succ : ∀ n : ℕ,
      (ShortComplex.mk (C.d (n + 2) (n + 1)) (C.d (n + 1) n)
        (C.d_comp_d (n + 2) (n + 1) n)).Exact := by
    intro n
    let f := C.d (n + 1) n
    let e : C.X (n + 2) ≅ over (kernel f) := by
      simpa [C, f] using
        (ChainComplex.mk'XIso (over M) (over (kernel (pi M)))
          (pi (kernel (pi M)) ≫ kernel.ι (pi M))
          (fun {X₀ X₁} g =>
            ⟨over (kernel g), pi (kernel g) ≫ kernel.ι g, by simp⟩) n)
    let S₁ := ShortComplex.mk (C.d (n + 2) (n + 1)) f
      (C.d_comp_d (n + 2) (n + 1) n)
    let S₂ := ShortComplex.mk (pi (kernel f) ≫ kernel.ι f) f (by simp)
    have hS₂ : S₂.Exact := exact_d_f' f
    let i : S₁ ≅ S₂ := ShortComplex.isoMk e (Iso.refl _) (Iso.refl _)
      (by simpa [S₁, S₂, e, C, f] using
        (ChainComplex.mk'_d (over M) (over (kernel (pi M)))
          (pi (kernel (pi M)) ≫ kernel.ι (pi M))
          (fun {X₀ X₁} g =>
            ⟨over (kernel g), pi (kernel g) ≫ kernel.ι g, by simp⟩) n).symm)
      (by simp [S₁, S₂, f])
    exact (ShortComplex.exact_iff_of_iso i).2 hS₂
  let H : Resolution R M :=
    { complex := C, augmentation := pi M, augmentation_condition := hzero,
      exact_zero := hexact_zero, exact_succ := hexact_succ,
      augmentation_epi := epi_pi M }
  let FF : FreeResolution R M := { resolution := H, free := free_C }
  exact ⟨{ resolution := FF, finite := finite_C }⟩

/-- A comparison map from a free augmented complex to a resolution. -/
structure FreeAugmentedComplexMap {R : Type u} [Ring R]
    {M N : ModuleCat.{u} R} (F : FreeAugmentedComplex R M) (G : Resolution R N)
    (φ : M ⟶ N) where
  hom : F.complex ⟶ G.complex
  hom_f_zero_comp_augmentation : hom.f 0 ≫ G.augmentation = F.augmentation ≫ φ

/-- An augmented complex of free modules admits a comparison map to any
resolution. -/
theorem free_augmented_complex_map_exists {R : Type u} [Ring R]
    {M N : ModuleCat.{u} R} (F : FreeAugmentedComplex R M) (G : Resolution R N)
    (φ : M ⟶ N) :
    Nonempty (FreeAugmentedComplexMap F G φ) := by
  classical
  let : Epi G.augmentation := G.augmentation_epi
  let : Module.Free R (F.complex.X 0 : Type u) := F.free 0
  let : Projective (F.complex.X 0) :=
    ModuleCat.projective_of_free (Module.Free.chooseBasis R (F.complex.X 0 : Type u))
  let lift_zero : F.complex.X 0 ⟶ G.complex.X 0 :=
    Projective.factorThru (F.augmentation ≫ φ) G.augmentation
  have lift_zero_comm :
      lift_zero ≫ G.augmentation = F.augmentation ≫ φ := by
    dsimp [lift_zero]
    exact Projective.factorThru_comp _ _
  let : Module.Free R (F.complex.X 1 : Type u) := F.free 1
  let : Projective (F.complex.X 1) :=
    ModuleCat.projective_of_free (Module.Free.chooseBasis R (F.complex.X 1 : Type u))
  let lift_one : F.complex.X 1 ⟶ G.complex.X 1 :=
    G.exact_zero.liftFromProjective (F.complex.d 1 0 ≫ lift_zero) (by
      rw [Category.assoc, lift_zero_comm, ← Category.assoc,
        F.augmentation_condition, zero_comp])
  have lift_one_comm :
      lift_one ≫ G.complex.d 1 0 = F.complex.d 1 0 ≫ lift_zero := by
    exact G.exact_zero.liftFromProjective_comp _ _
  let lift_succ (n : ℕ)
      (g : F.complex.X n ⟶ G.complex.X n)
      (g' : F.complex.X (n + 1) ⟶ G.complex.X (n + 1))
      (w : g' ≫ G.complex.d (n + 1) n =
        F.complex.d (n + 1) n ≫ g) :
      Σ' g'' : F.complex.X (n + 2) ⟶ G.complex.X (n + 2),
        g'' ≫ G.complex.d (n + 2) (n + 1) =
          F.complex.d (n + 2) (n + 1) ≫ g' := by
    letI : Module.Free R (F.complex.X (n + 2) : Type u) := F.free (n + 2)
    letI : Projective (F.complex.X (n + 2)) :=
      ModuleCat.projective_of_free
        (Module.Free.chooseBasis R (F.complex.X (n + 2) : Type u))
    refine ⟨G.exact_succ n |>.liftFromProjective
      (F.complex.d (n + 2) (n + 1) ≫ g') ?_, ?_⟩
    · rw [Category.assoc, w]
      simp
    · exact G.exact_succ n |>.liftFromProjective_comp _ _
  let hom : F.complex ⟶ G.complex :=
    ChainComplex.mkHom F.complex G.complex lift_zero lift_one lift_one_comm
      (fun n p => lift_succ n p.1 p.2.1 p.2.2)
  have hcompat : hom.f 0 ≫ G.augmentation = F.augmentation ≫ φ := by
    rw [show hom.f 0 = lift_zero by rfl]
    exact lift_zero_comm
  exact ⟨FreeAugmentedComplexMap.mk hom hcompat⟩

/- A map of resolutions is a map of complexes compatible with the augmentation. -/
structure ResolutionMap {R : Type u} [Ring R] {M N : ModuleCat.{u} R}
    (F : Resolution R M) (G : Resolution R N) (φ : M ⟶ N) where
  hom : F.complex ⟶ G.complex
  hom_f_zero_comp_augmentation : hom.f 0 ≫ G.augmentation = F.augmentation ≫ φ

/-- The comparison map interface is also compatible with Mathlib's canonical
projective-resolution lift. -/
noncomputable def canonicalResolutionMap {R : Type u} [Ring R]
    {M N : ModuleCat.{u} R} (P : CategoryTheory.ProjectiveResolution M)
    (Q : CategoryTheory.ProjectiveResolution N) (φ : M ⟶ N) :
    ResolutionMap (projectiveResolutionToResolution P)
      (projectiveResolutionToResolution Q) φ where
  hom := CategoryTheory.ProjectiveResolution.lift φ P Q
  hom_f_zero_comp_augmentation := by
    simpa [projectiveResolutionToResolution] using
      CategoryTheory.ProjectiveResolution.lift_commutes_zero φ P Q

/-- A free resolution admits a comparison map to any resolution. -/
theorem resolution_map_exists {R : Type u} [Ring R] {M N : ModuleCat.{u} R}
    (F : FreeResolution R M) (G : Resolution R N) (φ : M ⟶ N) :
    Nonempty (ResolutionMap F.resolution G φ) := by
  let FF : FreeAugmentedComplex R M :=
    { complex := F.complex, augmentation := F.resolution.augmentation,
      augmentation_condition := F.resolution.augmentation_condition, free := F.free }
  rcases free_augmented_complex_map_exists FF G φ with ⟨h⟩
  exact ⟨⟨h.hom, h.hom_f_zero_comp_augmentation⟩⟩

/-! ## Homology, cohomology, maps, and homotopies -/

/-- The differential `F_{i+1} → F_i` of a chain complex. -/
abbrev chainDifferential {R : Type u} [Ring R] (F : ModuleChainComplex R) (i : ℕ) :
    F.X (i + 1) ⟶ F.X i :=
  F.d (i + 1) i

/-- The differential `F^i → F^{i+1}` of a cochain complex. -/
abbrev cochainDifferential {R : Type u} [Ring R] (F : ModuleCochainComplex R) (i : ℕ) :
    F.X i ⟶ F.X (i + 1) :=
  F.d i (i + 1)

/-- Homology of a chain complex, using the canonical kernel/cokernel homology API. -/
noncomputable def chainHomology {R : Type u} [Ring R] (F : ModuleChainComplex R) (i : ℕ) :
    ModuleCat.{u} R :=
  HomologicalComplex.homology F i

/-- Cohomology of a cochain complex, using the canonical kernel/cokernel homology API. -/
noncomputable def cochainCohomology {R : Type u} [Ring R] (F : ModuleCochainComplex R) (i : ℕ) :
    ModuleCat.{u} R :=
  HomologicalComplex.homology F i

/-- The explicit kernel/image quotient presentation of chain homology. -/
noncomputable def chainHomologyQuotientIso {R : Type u} [Ring R]
    (F : ModuleChainComplex R) (i : ℕ) :
    chainHomology F i ≅ (F.sc i).moduleCatLeftHomologyData.H :=
  (F.sc i).moduleCatHomologyIso

/-- The explicit kernel/image quotient presentation of cohomology. -/
noncomputable def cochainCohomologyQuotientIso {R : Type u} [Ring R]
    (F : ModuleCochainComplex R) (i : ℕ) :
    cochainCohomology F i ≅ (F.sc i).moduleCatLeftHomologyData.H :=
  (F.sc i).moduleCatHomologyIso

/-- The map induced on chain homology by a map of complexes. -/
noncomputable def chainHomologyMap {R : Type u} [Ring R]
    {F G : ModuleChainComplex R} (α : F ⟶ G) (i : ℕ) :
    chainHomology F i ⟶ chainHomology G i :=
  HomologicalComplex.homologyMap α i

/-- The map induced on cohomology by a map of cochain complexes. -/
noncomputable def cochainCohomologyMap {R : Type u} [Ring R]
    {F G : ModuleCochainComplex R} (α : F ⟶ G) (i : ℕ) :
    cochainCohomology F i ⟶ cochainCohomology G i :=
  HomologicalComplex.homologyMap α i

/-- Homotopy of chain maps, in Mathlib's shape-aware formulation. -/
def ChainHomotopic {R : Type u} [Ring R] {F G : ModuleChainComplex R}
    (α β : F ⟶ G) : Prop :=
  Nonempty (Homotopy α β)

/-- Homotopy of cochain maps, in Mathlib's shape-aware formulation. -/
def CochainHomotopic {R : Type u} [Ring R] {F G : ModuleCochainComplex R}
    (α β : F ⟶ G) : Prop :=
  Nonempty (Homotopy α β)

/-- Homotopy of additive-group-valued cochain maps. -/
def AdditiveCochainHomotopic
    {F G : CochainComplex (AddCommGrpCat.{u}) ℕ} (α β : F ⟶ G) : Prop :=
  Nonempty (Homotopy α β)

/-- Any two comparison maps from an augmented free complex to a resolution
are homotopic. -/
theorem free_augmented_complex_maps_homotopic {R : Type u} [Ring R]
    {M N : ModuleCat.{u} R} (F : FreeAugmentedComplex R M) (G : Resolution R N)
    (φ : M ⟶ N) (α β : FreeAugmentedComplexMap F G φ) :
    ChainHomotopic α.hom β.hom := by
  have lift_of_exact {A B C X : ModuleCat.{u} R} (f : A ⟶ B) (g : B ⟶ C)
      (hfg : f ≫ g = 0)
      (hex : (ShortComplex.mk f g hfg).Exact) (u : X ⟶ B) (hu : u ≫ g = 0)
      (hfree : Module.Free R X) : ∃ v : X ⟶ A, v ≫ f = u := by
    let _ : Projective X :=
      ModuleCat.projective_of_free (Module.Free.chooseBasis R (X : Type u))
    let _ : Epi (kernel.lift g f hfg) :=
      (ShortComplex.exact_iff_epi_kernel_lift (ShortComplex.mk f g hfg)).mp hex
    let v := Projective.factorThru (kernel.lift g u hu) (kernel.lift g f hfg)
    refine ⟨v, ?_⟩
    calc
      v ≫ f = (v ≫ kernel.lift g f hfg) ≫ kernel.ι g := by
        simp [Category.assoc]
      _ = kernel.lift g u hu ≫ kernel.ι g := by
        rw [Projective.factorThru_comp]
      _ = u := by simp
  classical
  let e : F.complex ⟶ G.complex := α.hom - β.hom
  have he0 : e.f 0 ≫ G.augmentation = 0 := by
    dsimp [e]
    rw [Preadditive.sub_comp, α.hom_f_zero_comp_augmentation,
      β.hom_f_zero_comp_augmentation, sub_self]
  have h0_exists := lift_of_exact (G.complex.d 1 0) G.augmentation
    G.augmentation_condition G.exact_zero (e.f 0) he0 (F.free 0)
  let h0 := Classical.choose h0_exists
  have h0_spec := Classical.choose_spec h0_exists
  have h1_zero :
      (e.f 1 - F.complex.d 1 0 ≫ h0) ≫ G.complex.d 1 0 = 0 := by
    rw [Preadditive.sub_comp, e.comm' 1 0 (by simp), Category.assoc, h0_spec]
    simp
  have h1_exists := lift_of_exact (G.complex.d 2 1) (G.complex.d 1 0)
    (G.complex.d_comp_d 2 1 0) (G.exact_succ 0)
    (e.f 1 - F.complex.d 1 0 ≫ h0) h1_zero (F.free 1)
  let h1 := Classical.choose h1_exists
  have h1_spec := Classical.choose_spec h1_exists
  have h1_comm :
      e.f 1 = F.complex.d 1 0 ≫ h0 + h1 ≫ G.complex.d 2 1 := by
    rw [h1_spec]
    abel
  have hs : ∀ (n : ℕ)
      (p : Σ' (f : F.complex.X n ⟶ G.complex.X (n + 1))
        (f' : F.complex.X (n + 1) ⟶ G.complex.X (n + 2)),
        e.f (n + 1) = F.complex.d (n + 1) n ≫ f + f' ≫ G.complex.d (n + 2) (n + 1)),
      Σ' f'' : F.complex.X (n + 2) ⟶ G.complex.X (n + 3),
        e.f (n + 2) = F.complex.d (n + 2) (n + 1) ≫ p.2.1 +
          f'' ≫ G.complex.d (n + 3) (n + 2) := by
    intro n p
    rcases p with ⟨p0, p1, hp⟩
    have hu :
        (e.f (n + 2) - F.complex.d (n + 2) (n + 1) ≫ p1) ≫
            G.complex.d (n + 2) (n + 1) = 0 := by
      rw [Preadditive.sub_comp, e.comm' (n + 2) (n + 1) (by simp), Category.assoc,
        hp]
      simp
    have h_exists := lift_of_exact (G.complex.d (n + 3) (n + 2))
      (G.complex.d (n + 2) (n + 1))
      (G.complex.d_comp_d (n + 3) (n + 2) (n + 1)) (G.exact_succ (n + 1))
      (e.f (n + 2) - F.complex.d (n + 2) (n + 1) ≫ p1) hu (F.free (n + 2))
    let h := Classical.choose h_exists
    have h_spec := Classical.choose_spec h_exists
    refine ⟨h, ?_⟩
    rw [h_spec]
    abel
  have h := Homotopy.mkInductive e h0 h0_spec.symm h1 h1_comm hs
  exact ⟨(Homotopy.equivSubZero (f := α.hom) (g := β.hom)).symm h⟩

theorem chain_homotopic_maps_equal_on_homology {R : Type u} [Ring R]
    {F G : ModuleChainComplex R} {α β : F ⟶ G} (h : ChainHomotopic α β) (i : ℕ) :
    chainHomologyMap α i = chainHomologyMap β i := by
  rcases h with ⟨h⟩
  exact h.homologyMap_eq i

theorem cochain_homotopic_maps_equal_on_cohomology {R : Type u} [Ring R]
    {F G : ModuleCochainComplex R} {α β : F ⟶ G} (h : CochainHomotopic α β) (i : ℕ) :
    cochainCohomologyMap α i = cochainCohomologyMap β i := by
  rcases h with ⟨h⟩
  exact h.homologyMap_eq i

/-! ## The Hom complex attached to a resolution -/

/-- Precomposition on the additive groups of module homomorphisms. -/
def homPrecompAddMonoidHom {R : Type u} [Ring R]
    {A B N : ModuleCat.{u} R} (f : B ⟶ A) :
    (A ⟶ N) →+ (B ⟶ N) where
  toFun g := f ≫ g
  map_zero' := by simp
  map_add' g h := by simp

/-- The differential in `Hom_R(F_•,N)`, with the source's cohomological indexing. -/
noncomputable def resolutionHomDifferential {R : Type u} [Ring R]
    (F : ModuleChainComplex R) (N : ModuleCat.{u} R) (i j : ℕ) :
    AddCommGrpCat.of (F.X i ⟶ N) ⟶ AddCommGrpCat.of (F.X j ⟶ N) :=
  if i + 1 = j then
    AddCommGrpCat.ofHom (homPrecompAddMonoidHom (F.d j i))
  else 0

/-- The cochain complex `Hom_R(F_•,N)`. -/
noncomputable def resolutionHomComplex {R : Type u} [Ring R]
    (F : ModuleChainComplex R) (N : ModuleCat.{u} R) :
    CochainComplex (AddCommGrpCat.{u}) ℕ where
  X i := AddCommGrpCat.of (F.X i ⟶ N)
  d i j := resolutionHomDifferential F N i j
  shape i j hij := by
    classical
    dsimp [resolutionHomDifferential]
    split_ifs with h
    · exact (hij h).elim
    · rfl
  d_comp_d' i j k hij hjk := by
    classical
    have hij' : i + 1 = j := by
      simpa only [ComplexShape.up_Rel] using hij
    have hjk' : j + 1 = k := by
      simpa only [ComplexShape.up_Rel] using hjk
    dsimp [resolutionHomDifferential]
    rw [if_pos hij', if_pos hjk']
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro g
    change F.d k j ≫ (F.d j i ≫ g) = 0
    simp

/-- A map of resolutions induces the contravariant map of Hom complexes. -/
noncomputable def resolutionHomMap {R : Type u} [Ring R]
    {F G : ModuleChainComplex R} (α : F ⟶ G) (N : ModuleCat.{u} R) :
    resolutionHomComplex G N ⟶ resolutionHomComplex F N where
  f i := AddCommGrpCat.ofHom (homPrecompAddMonoidHom (α.f i))
  comm' i j hij := by
    classical
    have hij' : i + 1 = j := by
      simpa only [ComplexShape.up_Rel] using hij
    dsimp [resolutionHomComplex, resolutionHomDifferential]
    rw [if_pos hij']
    rw [if_pos hij']
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro g
    change F.d j i ≫ (α.f i ≫ g) = α.f j ≫ (G.d j i ≫ g)
    rw [← Category.assoc, ← Category.assoc, ← α.comm j i]

/-- Cohomology of an additive-group-valued cochain complex. -/
noncomputable def additiveCochainCohomology
    (F : CochainComplex (AddCommGrpCat.{u}) ℕ) (i : ℕ) : AddCommGrpCat.{u} :=
  HomologicalComplex.homology F i

/-- The map induced on additive cohomology by a map of cochain complexes. -/
noncomputable def additiveCochainCohomologyMap
    {F G : CochainComplex (AddCommGrpCat.{u}) ℕ} (α : F ⟶ G) (i : ℕ) :
    additiveCochainCohomology F i ⟶ additiveCochainCohomology G i :=
  HomologicalComplex.homologyMap α i

theorem additive_cochain_homotopic_maps_equal_on_cohomology
    {F G : CochainComplex (AddCommGrpCat.{u}) ℕ} {α β : F ⟶ G}
    (h : AdditiveCochainHomotopic α β) (i : ℕ) :
    additiveCochainCohomologyMap α i = additiveCochainCohomologyMap β i := by
  rcases h with ⟨h⟩
  exact h.homologyMap_eq i

/-- The induced map on the cohomology of the Hom complex. -/
noncomputable def resolutionHomCohomologyMap {R : Type u} [Ring R]
    {F G : ModuleChainComplex R} (α : F ⟶ G) (N : ModuleCat.{u} R) (i : ℕ) :
    additiveCochainCohomology (resolutionHomComplex G N) i ⟶
      additiveCochainCohomology (resolutionHomComplex F N) i :=
  additiveCochainCohomologyMap (resolutionHomMap α N) i

/-! ## Resolution Ext and its independence of choices -/

/-- The `i`th cohomology group of `Hom_R(F_•,N)`. -/
noncomputable def ResolutionExt {R : Type u} [Ring R]
    {M : ModuleCat.{u} R} (F : FreeResolution R M) (N : ModuleCat.{u} R) (i : ℕ) :
    AddCommGrpCat.{u} :=
  additiveCochainCohomology (resolutionHomComplex F.complex N) i

/-- The resolution-based Ext group, extended by zero to negative degrees. -/
noncomputable def ResolutionExtZ {R : Type u} [Ring R]
    {M : ModuleCat.{u} R} (F : FreeResolution R M) (N : ModuleCat.{u} R) (i : ℤ) :
    AddCommGrpCat.{u} :=
  if 0 ≤ i then AddCommGrpCat.of (ResolutionExt F N i.toNat) else 0

/-- The canonical Ext group in the module category. -/
abbrev ExtGroup {R : Type u} [Ring R]
    (M N : ModuleCat.{u} R) (i : ℕ) : Type u :=
  CategoryTheory.Abelian.Ext M N i

/-- The canonical Ext module over a commutative ring. -/
noncomputable def ExtModule {R : Type u} [CommRing R]
    (M N : ModuleCat.{u} R) (i : ℕ) : ModuleCat.{u} R :=
  ModuleCat.of R (ExtGroup M N i)

/-- The canonical Ext value, extended by zero to negative degrees. -/
noncomputable def ExtModuleZ {R : Type u} [CommRing R]
    (M N : ModuleCat.{u} R) (i : ℤ) : ModuleCat.{u} R :=
  if 0 ≤ i then ExtModule M N i.toNat else 0

theorem resolution_ext_negative {R : Type u} [Ring R]
    {M : ModuleCat.{u} R} (F : FreeResolution R M) (N : ModuleCat.{u} R)
    {i : ℤ} (hi : i < 0) : ResolutionExtZ F N i = 0 := by
  simp [ResolutionExtZ, not_le_of_gt hi]

theorem ext_module_negative {R : Type u} [CommRing R]
    (M N : ModuleCat.{u} R) {i : ℤ} (hi : i < 0) : ExtModuleZ M N i = 0 := by
  simp [ExtModuleZ, not_le_of_gt hi]

/-- A chosen free-resolution computation is additively equivalent to the
derived-category Ext group. The `Nonempty` wrapper records existence without
choosing a comparison equivalence. -/
theorem resolution_ext_represents_ext {R : Type u} [Ring R]
    {M N : ModuleCat.{u} R} (F : FreeResolution R M) (i : ℕ) :
    Nonempty (ResolutionExt F N i ≃+ ExtGroup M N i) := by
  sorry

/-- Degree zero Ext is the module-hom group. -/
noncomputable def extZeroLinearEquiv {R : Type u} [CommRing R]
    (M N : ModuleCat.{u} R) : ExtGroup M N 0 ≃ₗ[R] (M ⟶ N) :=
  CategoryTheory.Abelian.Ext.linearEquiv₀

/-- The degree-zero group computed from a free resolution is the Hom group. -/
theorem resolution_ext_zero_equiv_hom {R : Type u} [CommRing R]
    {M : ModuleCat.{u} R} (F : FreeResolution R M) (N : ModuleCat.{u} R) :
    Nonempty (ResolutionExt F N 0 ≃+ (M ⟶ N)) := by
  rcases resolution_ext_represents_ext F 0 with ⟨e⟩
  exact ⟨e.trans (extZeroLinearEquiv M N).toAddEquiv⟩

/-- Two comparison maps induce homotopic maps on the Hom complexes. -/
theorem resolution_maps_homotopic {R : Type u} [Ring R]
    {M₁ M₂ : ModuleCat.{u} R} (F : FreeResolution R M₁)
    (G : Resolution R M₂) (φ : M₁ ⟶ M₂) (α β : ResolutionMap F.resolution G φ) :
    ChainHomotopic α.hom β.hom := by
  exact free_augmented_complex_maps_homotopic
    { complex := F.complex, augmentation := F.resolution.augmentation,
      augmentation_condition := F.resolution.augmentation_condition, free := F.free }
    G φ ⟨α.hom, α.hom_f_zero_comp_augmentation⟩
      ⟨β.hom, β.hom_f_zero_comp_augmentation⟩

/-- Two comparison maps induce homotopic maps on the Hom complexes. -/
theorem resolution_hom_maps_homotopic {R : Type u} [Ring R]
    {M₁ M₂ : ModuleCat.{u} R} (F : FreeResolution R M₁)
    (G : Resolution R M₂) (φ : M₁ ⟶ M₂) (α β : ResolutionMap F.resolution G φ)
    (N : ModuleCat.{u} R) :
    AdditiveCochainHomotopic (resolutionHomMap α.hom N) (resolutionHomMap β.hom N) := by
  rcases resolution_maps_homotopic F G φ α β with ⟨h⟩
  exact ⟨
    { hom := fun i j =>
        if j + 1 = i then
          (show (resolutionHomComplex G.complex N).X i ⟶
              (resolutionHomComplex F.resolution.complex N).X j from by
            change AddCommGrpCat.of (G.complex.X i ⟶ N) ⟶
              AddCommGrpCat.of (F.resolution.complex.X j ⟶ N)
            exact AddCommGrpCat.ofHom (homPrecompAddMonoidHom (h.hom j i)))
        else 0
      zero := by
        intro i j hij
        dsimp
        split_ifs with hji
        · exact (hij (by simpa [ComplexShape.up_Rel] using hji)).elim
        · rfl
      comm := by
        intro i
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro g
        change G.complex.X i ⟶ N at g
        cases i with
        | zero =>
          rw [Homotopy.dNext_cochainComplex]
          rw [Homotopy.prevD_zero_cochainComplex]
          dsimp [resolutionHomMap, resolutionHomComplex, resolutionHomDifferential,
            homPrecompAddMonoidHom]
          change α.hom.f 0 ≫ g =
            h.hom 0 1 ≫ G.complex.d 1 0 ≫ g + 0 + β.hom.f 0 ≫ g
          have hcomm := h.comm 0
          rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex] at hcomm
          have hcomm' : α.hom.f 0 = h.hom 0 1 ≫ G.complex.d 1 0 + β.hom.f 0 := by
            simpa using hcomm
          have hc := congrArg (fun q : F.complex.X 0 ⟶ G.complex.X 0 => q ≫ g) hcomm'
          have hadd := Preadditive.add_comp (F.complex.X 0) (G.complex.X 0) N
            (h.hom 0 1 ≫ G.complex.d 1 0) (β.hom.f 0) g
          rw [hadd] at hc
          rw [Category.assoc] at hc
          simpa using hc
        | succ i =>
          rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_succ_cochainComplex]
          dsimp [resolutionHomMap, resolutionHomComplex, resolutionHomDifferential,
            homPrecompAddMonoidHom]
          simp only [if_pos rfl]
          change α.hom.f (i + 1) ≫ g =
            h.hom (i + 1) (i + 2) ≫ G.complex.d (i + 2) (i + 1) ≫ g +
              F.resolution.complex.d (i + 1) i ≫ h.hom i (i + 1) ≫ g +
              β.hom.f (i + 1) ≫ g
          have hcomm := h.comm (i + 1)
          rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at hcomm
          have hcomm' : α.hom.f (i + 1) =
              h.hom (i + 1) (i + 2) ≫ G.complex.d (i + 2) (i + 1) +
                F.complex.d (i + 1) i ≫ h.hom i (i + 1) + β.hom.f (i + 1) := by
            simpa [Nat.add_assoc, add_comm, add_left_comm, add_assoc] using hcomm
          have hc := congrArg
            (fun q : F.complex.X (i + 1) ⟶ G.complex.X (i + 1) => q ≫ g)
            hcomm'
          have hadd₁ := Preadditive.add_comp (F.complex.X (i + 1))
            (G.complex.X (i + 1)) N
            (h.hom (i + 1) (i + 2) ≫ G.complex.d (i + 2) (i + 1))
            (F.complex.d (i + 1) i ≫ h.hom i (i + 1)) g
          have hadd₂ := Preadditive.add_comp (F.complex.X (i + 1))
            (G.complex.X (i + 1)) N
            (h.hom (i + 1) (i + 2) ≫ G.complex.d (i + 2) (i + 1) +
              F.complex.d (i + 1) i ≫ h.hom i (i + 1))
            (β.hom.f (i + 1)) g
          rw [hadd₂, hadd₁] at hc
          simpa [Category.assoc] using hc }⟩

/-- The induced map on `H^i(Hom_R(-,N))` is independent of the comparison map.

The direction is contravariant: a comparison `F_• ⟶ G_•` induces a map from
`H^i(Hom_R(G_•,N))` to `H^i(Hom_R(F_•,N))`. -/
theorem resolution_ext_map_independent {R : Type u} [Ring R]
    {M₁ M₂ : ModuleCat.{u} R} (F : FreeResolution R M₁)
    (G : FreeResolution R M₂) (φ : M₁ ⟶ M₂)
    (α β : ResolutionMap F.resolution G.resolution φ) (N : ModuleCat.{u} R) (i : ℕ) :
    resolutionHomCohomologyMap α.hom N i = resolutionHomCohomologyMap β.hom N i := by
  exact additive_cochain_homotopic_maps_equal_on_cohomology
    (resolution_hom_maps_homotopic F G.resolution φ α β N) i

/-- An isomorphism of modules induces an isomorphism on the resolution Ext groups. -/
theorem isIso_resolution_ext_map_of_isIso {R : Type u} [Ring R]
    {M₁ M₂ : ModuleCat.{u} R} (F : FreeResolution R M₁)
    (G : FreeResolution R M₂) (φ : M₁ ⟶ M₂) [IsIso φ]
    (α : ResolutionMap F.resolution G.resolution φ) (N : ModuleCat.{u} R) (i : ℕ) :
    IsIso (resolutionHomCohomologyMap α.hom N i) := by
  let γ : ResolutionMap G.resolution F.resolution (inv φ) :=
    Classical.choice (resolution_map_exists G F.resolution (inv φ))
  let δ₁ : ResolutionMap F.resolution F.resolution (𝟙 M₁) :=
    { hom := α.hom ≫ γ.hom
      hom_f_zero_comp_augmentation := by
        change (α.hom.f 0 ≫ γ.hom.f 0) ≫ F.resolution.augmentation = _
        rw [Category.assoc, γ.hom_f_zero_comp_augmentation,
          ← Category.assoc, α.hom_f_zero_comp_augmentation]
        simp }
  let δ₂ : ResolutionMap G.resolution G.resolution (𝟙 M₂) :=
    { hom := γ.hom ≫ α.hom
      hom_f_zero_comp_augmentation := by
        change (γ.hom.f 0 ≫ α.hom.f 0) ≫ G.resolution.augmentation = _
        rw [Category.assoc, α.hom_f_zero_comp_augmentation,
          ← Category.assoc, γ.hom_f_zero_comp_augmentation]
        simp }
  let ε₁ : ResolutionMap F.resolution F.resolution (𝟙 M₁) :=
    { hom := 𝟙 F.complex
      hom_f_zero_comp_augmentation := by simp }
  let ε₂ : ResolutionMap G.resolution G.resolution (𝟙 M₂) :=
    { hom := 𝟙 G.complex
      hom_f_zero_comp_augmentation := by simp }
  have hmap_id (K : ModuleChainComplex R) :
      resolutionHomMap (𝟙 K) N = 𝟙 (resolutionHomComplex K N) := by
    apply HomologicalComplex.hom_ext
    intro p
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro g
    change K.X p ⟶ N at g
    change (𝟙 K : K ⟶ K).f p ≫ g = g
    rw [HomologicalComplex.id_f]
    simp
  have hδ₁ : resolutionHomCohomologyMap δ₁.hom N i =
      𝟙 (ResolutionExt F N i) := by
    rw [resolution_ext_map_independent F F (𝟙 M₁) δ₁ ε₁ N i]
    change HomologicalComplex.homologyMap (resolutionHomMap ε₁.hom N) i = _
    rw [show ε₁.hom = 𝟙 F.complex by rfl, hmap_id F.complex]
    exact HomologicalComplex.homologyMap_id _ _
  have hδ₂ : resolutionHomCohomologyMap δ₂.hom N i =
      𝟙 (ResolutionExt G N i) := by
    rw [resolution_ext_map_independent G G (𝟙 M₂) δ₂ ε₂ N i]
    change HomologicalComplex.homologyMap (resolutionHomMap ε₂.hom N) i = _
    rw [show ε₂.hom = 𝟙 G.complex by rfl, hmap_id G.complex]
    exact HomologicalComplex.homologyMap_id _ _
  have hcomp₁ : resolutionHomMap α.hom N ≫ resolutionHomMap γ.hom N =
      resolutionHomMap δ₂.hom N := by
    apply HomologicalComplex.hom_ext
    intro p
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro g
    change G.complex.X p ⟶ N at g
    change γ.hom.f p ≫ (α.hom.f p ≫ g) =
      (γ.hom.f p ≫ α.hom.f p) ≫ g
    simp only [Category.assoc]
  have hcomp₂ : resolutionHomMap γ.hom N ≫ resolutionHomMap α.hom N =
      resolutionHomMap δ₁.hom N := by
    apply HomologicalComplex.hom_ext
    intro p
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro g
    change F.complex.X p ⟶ N at g
    change α.hom.f p ≫ (γ.hom.f p ≫ g) =
      (α.hom.f p ≫ γ.hom.f p) ≫ g
    simp only [Category.assoc]
  have hleft : resolutionHomCohomologyMap α.hom N i ≫
      resolutionHomCohomologyMap γ.hom N i =
        𝟙 (ResolutionExt G N i) := by
    change HomologicalComplex.homologyMap (resolutionHomMap α.hom N) i ≫
        HomologicalComplex.homologyMap (resolutionHomMap γ.hom N) i =
      𝟙 (HomologicalComplex.homology (resolutionHomComplex G.complex N) i)
    rw [← HomologicalComplex.homologyMap_comp (resolutionHomMap α.hom N)
      (resolutionHomMap γ.hom N) i, hcomp₁]
    change resolutionHomCohomologyMap δ₂.hom N i = 𝟙 (ResolutionExt G N i)
    exact hδ₂
  have hright : resolutionHomCohomologyMap γ.hom N i ≫
      resolutionHomCohomologyMap α.hom N i =
        𝟙 (ResolutionExt F N i) := by
    change HomologicalComplex.homologyMap (resolutionHomMap γ.hom N) i ≫
        HomologicalComplex.homologyMap (resolutionHomMap α.hom N) i =
      𝟙 (HomologicalComplex.homology (resolutionHomComplex F.complex N) i)
    rw [← HomologicalComplex.homologyMap_comp (resolutionHomMap γ.hom N)
      (resolutionHomMap α.hom N) i, hcomp₂]
    change resolutionHomCohomologyMap δ₁.hom N i = 𝟙 (ResolutionExt F N i)
    exact hδ₁
  exact ⟨⟨resolutionHomCohomologyMap γ.hom N i, hleft, hright⟩⟩

/-- A comparison map lifting the identity between one resolution and itself
induces an isomorphism on the computed Ext groups. -/
theorem isIso_resolution_ext_identity_map {R : Type u} [Ring R]
    {M : ModuleCat.{u} R} (F : FreeResolution R M)
    (α : ResolutionMap F.resolution F.resolution (𝟙 M))
    (N : ModuleCat.{u} R) (i : ℕ) :
    IsIso (resolutionHomCohomologyMap α.hom N i) := by
  exact isIso_resolution_ext_map_of_isIso F F (𝟙 M) α N i

/-! ## Long exact sequences -/

/-- The five-arrow segment of the covariant long exact Ext sequence. -/
noncomputable def extCovariantSequence {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (M : ModuleCat.{u} R) (i : ℕ) :
    ComposableArrows (AddCommGrpCat.{u}) 5 :=
  CategoryTheory.Abelian.Ext.covariantSequence M hS i (i + 1) rfl

/-- Exactness of every five-arrow segment in the covariant long exact sequence. -/
theorem extCovariantSequence_exact {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (M : ModuleCat.{u} R) (i : ℕ) :
    (extCovariantSequence S hS M i).Exact := by
  simpa [extCovariantSequence] using
    (CategoryTheory.Abelian.Ext.covariantSequence_exact M hS i (i + 1) rfl)

/-- The initial map into `Ext⁰` is injective when the first map is mono. -/
theorem ext_covariant_initial_injective {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (M : ModuleCat.{u} R) :
    Function.Injective
      ((CategoryTheory.Abelian.Ext.mk₀ S.f).postcomp M (Nat.add_zero 0)) := by
  exact CategoryTheory.Abelian.Ext.postcomp_mk₀_injective_of_mono
    (hf := hS.mono_f) M S.f

/-- The five-arrow segment of the contravariant long exact Ext sequence. -/
noncomputable def extContravariantSequence {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (N : ModuleCat.{u} R) (i : ℕ) :
    ComposableArrows (AddCommGrpCat.{u}) 5 :=
  CategoryTheory.Abelian.Ext.contravariantSequence hS N i (i + 1)
    (by simp [Nat.add_comm])

/-- Exactness of every five-arrow segment in the contravariant long exact sequence. -/
theorem extContravariantSequence_exact {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (N : ModuleCat.{u} R) (i : ℕ) :
    (extContravariantSequence S hS N i).Exact := by
  simpa [extContravariantSequence] using
    (CategoryTheory.Abelian.Ext.contravariantSequence_exact hS N i (i + 1)
      (by simp [Nat.add_comm]))

/-- The initial map into the contravariant `Ext⁰` sequence is injective when
the second map of the short exact sequence is epi. -/
theorem ext_contravariant_initial_injective {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (N : ModuleCat.{u} R) :
    Function.Injective
      ((CategoryTheory.Abelian.Ext.mk₀ S.g).precomp N (Nat.zero_add 0)) := by
  exact CategoryTheory.Abelian.Ext.precomp_mk₀_injective_of_epi
    (hg := hS.epi_g) N S.g

/-! ## Annihilation and Noetherian finiteness -/

/-- If `r` belongs to the annihilator of `N`, scalar multiplication by `r`
vanishes on every Ext group. -/
theorem ext_smul_eq_zero_of_annihilates_right {R : Type u} [CommRing R]
    (r : R) (M N : ModuleCat.{u} R) (hN : r ∈ Module.annihilator R N) (i : ℕ) :
    ∀ e : ExtGroup M N i, r • e = 0 := by
  intro e
  have hzero : r • (𝟙 N) = 0 := by
    simp [← ModuleCat.lsmul_eq_smul_id,
      Module.mem_annihilator_iff_lsmul_eq_zero.mp hN]
  rw [CategoryTheory.Abelian.Ext.smul_eq_comp_mk₀, hzero,
    CategoryTheory.Abelian.Ext.mk₀_zero]
  exact CategoryTheory.Abelian.Ext.comp_zero e N 0 i (add_zero i)

/-- If `r` belongs to the annihilator of `M`, scalar multiplication by `r`
vanishes on every Ext group. -/
theorem ext_smul_eq_zero_of_annihilates_left {R : Type u} [CommRing R]
    (r : R) (M N : ModuleCat.{u} R) (hM : r ∈ Module.annihilator R M) (i : ℕ) :
    ∀ e : ExtGroup M N i, r • e = 0 := by
  intro e
  have hz := CategoryTheory.Abelian.Ext.postcomp_smul_id_eq_zero_of_mem_annihilator
    (R := R) (M := N) (N := M) (r := r) (mem_ann := hM) i
  have hz' := congrArg (fun f => f e) hz
  rw [CategoryTheory.Abelian.Ext.mk₀_smul (C := ModuleCat R) (X := N) (Y := N) r (𝟙 N)] at hz'
  simpa [CategoryTheory.Abelian.Ext.postcomp, CategoryTheory.Abelian.Ext.comp_smul] using hz'

/-- Ext between finite modules over a Noetherian ring is finite. -/
theorem ext_finite_of_noetherian {R : Type u} [CommRing R]
    [IsNoetherianRing R] (M N : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Finite R N] (i : ℕ) :
    Module.Finite R (ExtGroup M N i) := by
  infer_instance

end Formalization.Books.Algebra.Unit71
