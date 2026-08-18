import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Formalization.Books.Algebra.Unit39.FlatModules
import Formalization.Books.Algebra.Unit71.ExtGroups

/-!
# Commutative Algebra, Chapter 75: Tor groups and flatness

This file records the Tor construction, the double-complex comparison used for
symmetry, and the flatness criteria in the source section.  The underlying
resolutions, homology objects, tensor products, and flatness predicates are
Mathlib's canonical constructions (with the resolution interfaces from the
preceding formalization chapter).
-/

namespace Formalization.Books.Algebra.Unit75

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit71
open scoped TensorProduct BigOperators

noncomputable section

universe u v w

/-! ## Tensoring a resolution -/

/-- The chain complex obtained by tensoring a module chain complex on the right. -/
noncomputable def tensorComplex {R : Type u} [CommRing R]
    (F : ModuleChainComplex R) (N : ModuleCat.{u} R) : ModuleChainComplex R where
  X i := ModuleCat.of R (TensorProduct R (F.X i) N)
  d i j := if h : j + 1 = i then
    ModuleCat.ofHom (LinearMap.rTensor N (F.d i j).hom)
  else 0
  shape i j hij := by
    classical
    split_ifs with h
    · exact (hij h).elim
    · rfl
  d_comp_d' i j k hij hjk := by
    classical
    have hij' : j + 1 = i := by
      simpa only [ComplexShape.down_Rel] using hij
    have hjk' : k + 1 = j := by
      simpa only [ComplexShape.down_Rel] using hjk
    dsimp
    rw [if_pos hij', if_pos hjk']
    apply ModuleCat.hom_ext
    change (LinearMap.rTensor N (F.d j k).hom).comp
        (LinearMap.rTensor N (F.d i j).hom) = 0
    rw [← LinearMap.rTensor_comp]
    have hcomp : (F.d j k).hom.comp (F.d i j).hom = 0 := by
      exact congrArg (fun f => f.hom) (F.d_comp_d i j k)
    rw [hcomp]
    simp

/-- The Tor group computed from a chosen free resolution. -/
noncomputable def resolutionTor {R : Type u} [CommRing R]
    {M : ModuleCat.{u} R} (F : FreeResolution R M) (N : ModuleCat.{u} R) (i : ℕ) :
    ModuleCat.{u} R :=
  chainHomology (tensorComplex F.complex N) i

/-- A canonical Tor group, obtained from a fixed choice of free resolution. -/
noncomputable def Tor {R : Type u} [CommRing R]
    (M N : ModuleCat.{u} R) (i : ℕ) : ModuleCat.{u} R :=
  resolutionTor (Classical.choice (exists_free_resolution M)) N i

/-- Tensoring a chain map on the first variable. -/
noncomputable def tensorComplexMap {R : Type u} [CommRing R]
    {F G : ModuleChainComplex R} (α : F ⟶ G) (N : ModuleCat.{u} R) :
    tensorComplex F N ⟶ tensorComplex G N where
  f i := ModuleCat.ofHom (LinearMap.rTensor N (α.f i).hom)
  comm' i j hij := by
    classical
    have hij' : j + 1 = i := by
      simpa only [ComplexShape.down_Rel] using hij
    dsimp [tensorComplex]
    rw [if_pos hij', if_pos hij']
    apply ModuleCat.hom_ext
    change (LinearMap.rTensor N (G.d i j).hom).comp
        (LinearMap.rTensor N (α.f i).hom) =
      (LinearMap.rTensor N (α.f j).hom).comp
        (LinearMap.rTensor N (F.d i j).hom)
    rw [← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp]
    exact congrArg (fun f => LinearMap.rTensor N f)
      (congrArg (fun q => q.hom) (α.comm i j))

/-- Tensoring a chain map on the second variable. -/
noncomputable def tensorComplexMapRight {R : Type u} [CommRing R]
    (F : ModuleChainComplex R) {N P : ModuleCat.{u} R} (β : N ⟶ P) :
    tensorComplex F N ⟶ tensorComplex F P where
  f i := ModuleCat.ofHom ((β.hom).lTensor (F.X i))
  comm' i j hij := by
    classical
    have hij' : j + 1 = i := by
      simpa only [ComplexShape.down_Rel] using hij
    dsimp [tensorComplex]
    rw [if_pos hij', if_pos hij']
    apply ModuleCat.hom_ext
    change (LinearMap.rTensor P (F.d i j).hom).comp
        ((β.hom).lTensor (F.X i)) =
      ((β.hom).lTensor (F.X j)).comp
        (LinearMap.rTensor N (F.d i j).hom)
    ext x y
    rfl

private theorem tensorComplexMap_id {R : Type u} [CommRing R]
    (F : ModuleChainComplex R) (N : ModuleCat.{u} R) :
    tensorComplexMap (𝟙 F) N = 𝟙 (tensorComplex F N) := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  simp [tensorComplexMap]
  rfl

/-- The map induced on a chosen resolution computation of Tor. -/
noncomputable def resolutionTorMap {R : Type u} [CommRing R]
    {M₁ M₂ : ModuleCat.{u} R} (F : FreeResolution R M₁)
    (G : FreeResolution R M₂) (φ : M₁ ⟶ M₂)
    (α : ResolutionMap F.resolution G.resolution φ)
    (N : ModuleCat.{u} R) (i : ℕ) :
    resolutionTor F N i ⟶ resolutionTor G N i :=
  chainHomologyMap (tensorComplexMap α.hom N) i

/-- Comparison maps induce the same map on the Tor computation. -/
theorem resolutionTorMap_independent {R : Type u} [CommRing R]
    {M₁ M₂ : ModuleCat.{u} R} (F : FreeResolution R M₁)
    (G : FreeResolution R M₂) (φ : M₁ ⟶ M₂)
    (α β : ResolutionMap F.resolution G.resolution φ)
    (N : ModuleCat.{u} R) (i : ℕ) :
    resolutionTorMap F G φ α N i = resolutionTorMap F G φ β N i := by
  unfold resolutionTorMap
  apply chain_homotopic_maps_equal_on_homology
  rcases resolution_maps_homotopic F G.resolution φ α β with ⟨h⟩
  refine ⟨(fun p q => ModuleCat.ofHom (LinearMap.rTensor N (h.hom p q).hom)), ?_, ?_⟩
  · intro p q hpq
    rw [h.zero p q hpq]
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_ofHom, LinearMap.rTensor_zero, ModuleCat.hom_zero]
    change (0 : _ ) = 0
    rfl
  · intro p
    have hp := congrArg (fun q => ModuleCat.ofHom (LinearMap.rTensor N q.hom))
      (h.comm p)
    dsimp [tensorComplexMap]
    rw [hp]
    simp only [ModuleCat.hom_add, LinearMap.rTensor_add]
    have hd : ModuleCat.ofHom
          (LinearMap.rTensor N ((dNext (C := F.complex) (D := G.complex) p h.hom).hom)) =
        dNext (C := tensorComplex F.complex N) (D := tensorComplex G.complex N) p
          (fun p q => ModuleCat.ofHom (LinearMap.rTensor N (h.hom p q).hom)) := by
      rw [dNext_nat F.complex G.complex p h.hom,
        dNext_nat (tensorComplex F.complex N) (tensorComplex G.complex N) p
          (fun p q => ModuleCat.ofHom (LinearMap.rTensor N (h.hom p q).hom))]
      apply ModuleCat.hom_ext
      cases p <;> simp [tensorComplex, ModuleCat.hom_comp, LinearMap.rTensor_comp]
    have hv : ModuleCat.ofHom
          (LinearMap.rTensor N ((prevD (C := F.complex) (D := G.complex) p h.hom).hom)) =
        prevD (C := tensorComplex F.complex N) (D := tensorComplex G.complex N) p
          (fun p q => ModuleCat.ofHom (LinearMap.rTensor N (h.hom p q).hom)) := by
      have hp : (ComplexShape.down ℕ).Rel (p + 1) p := by simp
      rw [prevD_eq h.hom hp,
        prevD_eq (C := tensorComplex F.complex N) (D := tensorComplex G.complex N)
          (fun p q => ModuleCat.ofHom (LinearMap.rTensor N (h.hom p q).hom)) hp]
      apply ModuleCat.hom_ext
      simp [tensorComplex, ModuleCat.hom_comp, LinearMap.rTensor_comp]
    change (ModuleCat.ofHom
          (LinearMap.rTensor N ((dNext (C := F.complex) (D := G.complex) p h.hom).hom)) +
        ModuleCat.ofHom
          (LinearMap.rTensor N ((prevD (C := F.complex) (D := G.complex) p h.hom).hom)) +
        ModuleCat.ofHom (LinearMap.rTensor N (β.hom.f p).hom)) = _
    rw [← hd, ← hv]
    rfl

/-- An isomorphism of modules induces an isomorphism on the computed Tor groups. -/
theorem isIso_resolutionTorMap_of_isIso {R : Type u} [CommRing R]
    {M₁ M₂ : ModuleCat.{u} R} (F : FreeResolution R M₁)
    (G : FreeResolution R M₂) (φ : M₁ ⟶ M₂) [IsIso φ]
    (α : ResolutionMap F.resolution G.resolution φ)
    (N : ModuleCat.{u} R) (i : ℕ) :
    IsIso (resolutionTorMap F G φ α N i) := by
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
  have hδ₁ : resolutionTorMap F F (𝟙 M₁) δ₁ N i = 𝟙 (resolutionTor F N i) := by
    rw [resolutionTorMap_independent F F (𝟙 M₁) δ₁ ε₁ N i]
    change chainHomologyMap (tensorComplexMap ε₁.hom N) i = _
    rw [show ε₁.hom = 𝟙 F.complex by rfl, tensorComplexMap_id F.complex N]
    exact HomologicalComplex.homologyMap_id _ _
  have hδ₂ : resolutionTorMap G G (𝟙 M₂) δ₂ N i = 𝟙 (resolutionTor G N i) := by
    rw [resolutionTorMap_independent G G (𝟙 M₂) δ₂ ε₂ N i]
    change chainHomologyMap (tensorComplexMap ε₂.hom N) i = _
    rw [show ε₂.hom = 𝟙 G.complex by rfl, tensorComplexMap_id G.complex N]
    exact HomologicalComplex.homologyMap_id _ _
  have hcomp₁ : tensorComplexMap α.hom N ≫ tensorComplexMap γ.hom N =
      tensorComplexMap δ₁.hom N := by
    apply HomologicalComplex.hom_ext
    intro p
    apply ModuleCat.hom_ext
    simp [tensorComplexMap, δ₁, ModuleCat.hom_comp, LinearMap.rTensor_comp]
    rfl
  have hcomp₂ : tensorComplexMap γ.hom N ≫ tensorComplexMap α.hom N =
      tensorComplexMap δ₂.hom N := by
    apply HomologicalComplex.hom_ext
    intro p
    apply ModuleCat.hom_ext
    simp [tensorComplexMap, δ₂, ModuleCat.hom_comp, LinearMap.rTensor_comp]
    rfl
  have hleft : resolutionTorMap F G φ α N i ≫
      resolutionTorMap G F (inv φ) γ N i = 𝟙 (resolutionTor F N i) := by
    change HomologicalComplex.homologyMap (tensorComplexMap α.hom N) i ≫
        HomologicalComplex.homologyMap (tensorComplexMap γ.hom N) i =
      𝟙 (HomologicalComplex.homology (tensorComplex F.complex N) i)
    rw [← HomologicalComplex.homologyMap_comp (tensorComplexMap α.hom N)
      (tensorComplexMap γ.hom N) i, hcomp₁]
    change resolutionTorMap F F (𝟙 M₁) δ₁ N i = 𝟙 (resolutionTor F N i)
    exact hδ₁
  have hright : resolutionTorMap G F (inv φ) γ N i ≫
      resolutionTorMap F G φ α N i = 𝟙 (resolutionTor G N i) := by
    change HomologicalComplex.homologyMap (tensorComplexMap γ.hom N) i ≫
        HomologicalComplex.homologyMap (tensorComplexMap α.hom N) i =
      𝟙 (HomologicalComplex.homology (tensorComplex G.complex N) i)
    rw [← HomologicalComplex.homologyMap_comp (tensorComplexMap γ.hom N)
      (tensorComplexMap α.hom N) i, hcomp₂]
    change resolutionTorMap G G (𝟙 M₂) δ₂ N i = 𝟙 (resolutionTor G N i)
    exact hδ₂
  exact ⟨⟨resolutionTorMap G F (inv φ) γ N i, hleft, hright⟩⟩

/-- A comparison map lifting an identity induces an isomorphism on Tor. -/
theorem isIso_resolutionTorMap_identity {R : Type u} [CommRing R]
    {M : ModuleCat.{u} R} (F : FreeResolution R M)
    (α : ResolutionMap F.resolution F.resolution (𝟙 M))
    (N : ModuleCat.{u} R) (i : ℕ) :
    IsIso (resolutionTorMap F F (𝟙 M) α N i) := by
  let ε : ResolutionMap F.resolution F.resolution (𝟙 M) :=
    { hom := 𝟙 F.complex
      hom_f_zero_comp_augmentation := by simp }
  have hα : resolutionTorMap F F (𝟙 M) α N i = 𝟙 (resolutionTor F N i) := by
    rw [resolutionTorMap_independent F F (𝟙 M) α ε N i]
    change chainHomologyMap (tensorComplexMap ε.hom N) i = _
    rw [show ε.hom = 𝟙 F.complex by rfl, tensorComplexMap_id F.complex N]
    exact HomologicalComplex.homologyMap_id _ _
  rw [hα]
  infer_instance

/-- The first-variable map on the chosen canonical Tor groups. -/
noncomputable def torMapFirst {R : Type u} [CommRing R]
    {M₁ M₂ N : ModuleCat.{u} R} (φ : M₁ ⟶ M₂) (i : ℕ) :
    Tor M₁ N i ⟶ Tor M₂ N i := by
  let F : FreeResolution R M₁ := Classical.choice (exists_free_resolution M₁)
  let G : FreeResolution R M₂ := Classical.choice (exists_free_resolution M₂)
  let α : ResolutionMap F.resolution G.resolution φ :=
    Classical.choice (resolution_map_exists F G.resolution φ)
  exact resolutionTorMap F G φ α N i

/-- The second-variable map on the chosen canonical Tor groups. -/
noncomputable def torMapSecond {R : Type u} [CommRing R]
    (M N P : ModuleCat.{u} R) (ψ : N ⟶ P) (i : ℕ) :
    Tor M N i ⟶ Tor M P i := by
  let F : FreeResolution R M := Classical.choice (exists_free_resolution M)
  exact chainHomologyMap (tensorComplexMapRight F.complex ψ) i

/-- The first Tor construction is functorial. -/
theorem torMapFirst_id {R : Type u} [CommRing R]
    {M N : ModuleCat.{u} R} (i : ℕ) :
    torMapFirst (𝟙 M) i = 𝟙 (Tor M N i) := by
  unfold torMapFirst
  dsimp
  let F : FreeResolution R M := Classical.choice (exists_free_resolution M)
  let G : FreeResolution R M := Classical.choice (exists_free_resolution M)
  let α : ResolutionMap F.resolution G.resolution (𝟙 M) :=
    Classical.choice (resolution_map_exists F G.resolution (𝟙 M))
  change resolutionTorMap F G (𝟙 M) α N i = 𝟙 (resolutionTor F N i)
  change resolutionTorMap F F (𝟙 M) α N i = 𝟙 (resolutionTor F N i)
  let ε : ResolutionMap F.resolution F.resolution (𝟙 M) :=
    { hom := 𝟙 F.complex
      hom_f_zero_comp_augmentation := by simp }
  rw [resolutionTorMap_independent F F (𝟙 M) α ε N i]
  change chainHomologyMap (tensorComplexMap ε.hom N) i = _
  rw [show ε.hom = 𝟙 F.complex by rfl, tensorComplexMap_id F.complex N]
  exact HomologicalComplex.homologyMap_id _ _

theorem torMapFirst_comp {R : Type u} [CommRing R]
    {M₁ M₂ M₃ N : ModuleCat.{u} R}
    (φ : M₁ ⟶ M₂) (ψ : M₂ ⟶ M₃) (i : ℕ) :
    torMapFirst (N := N) (φ ≫ ψ) i =
      torMapFirst (N := N) φ i ≫ torMapFirst (N := N) ψ i := by
  unfold torMapFirst
  dsimp
  let F₁ : FreeResolution R M₁ := Classical.choice (exists_free_resolution M₁)
  let F₂ : FreeResolution R M₂ := Classical.choice (exists_free_resolution M₂)
  let F₃ : FreeResolution R M₃ := Classical.choice (exists_free_resolution M₃)
  let α : ResolutionMap F₁.resolution F₂.resolution φ :=
    Classical.choice (resolution_map_exists F₁ F₂.resolution φ)
  let β : ResolutionMap F₂.resolution F₃.resolution ψ :=
    Classical.choice (resolution_map_exists F₂ F₃.resolution ψ)
  let γ : ResolutionMap F₁.resolution F₃.resolution (φ ≫ ψ) :=
    Classical.choice (resolution_map_exists F₁ F₃.resolution (φ ≫ ψ))
  change resolutionTorMap F₁ F₃ (φ ≫ ψ) γ N i =
    resolutionTorMap F₁ F₂ φ α N i ≫ resolutionTorMap F₂ F₃ ψ β N i
  let δ : ResolutionMap F₁.resolution F₃.resolution (φ ≫ ψ) :=
    { hom := α.hom ≫ β.hom
      hom_f_zero_comp_augmentation := by
        change (α.hom.f 0 ≫ β.hom.f 0) ≫ F₃.resolution.augmentation = _
        rw [Category.assoc, β.hom_f_zero_comp_augmentation,
          ← Category.assoc, α.hom_f_zero_comp_augmentation]
        simp }
  rw [resolutionTorMap_independent F₁ F₃ (φ ≫ ψ) γ δ]
  have hmap : tensorComplexMap δ.hom N =
      tensorComplexMap α.hom N ≫ tensorComplexMap β.hom N := by
    apply HomologicalComplex.hom_ext
    intro p
    apply ModuleCat.hom_ext
    simp [tensorComplexMap, δ, ModuleCat.hom_comp, LinearMap.rTensor_comp]
    rfl
  unfold resolutionTorMap
  change HomologicalComplex.homologyMap (tensorComplexMap δ.hom N) i =
    HomologicalComplex.homologyMap (tensorComplexMap α.hom N) i ≫
      HomologicalComplex.homologyMap (tensorComplexMap β.hom N) i
  rw [hmap, HomologicalComplex.homologyMap_comp]

/-- The second Tor construction is functorial. -/
theorem torMapSecond_id {R : Type u} [CommRing R]
    {M N : ModuleCat.{u} R} (i : ℕ) :
    torMapSecond M N N (𝟙 N) i = 𝟙 (Tor M N i) := by
  unfold torMapSecond
  dsimp
  rw [show tensorComplexMapRight (Classical.choice (exists_free_resolution M)).complex (𝟙 N) =
      𝟙 (tensorComplex (Classical.choice (exists_free_resolution M)).complex N) by
    apply HomologicalComplex.hom_ext
    intro p
    apply ModuleCat.hom_ext
    simp [tensorComplexMapRight, LinearMap.lTensor_id]
    rfl]
  exact HomologicalComplex.homologyMap_id _ _

theorem torMapSecond_comp {R : Type u} [CommRing R]
    {M N₁ N₂ N₃ : ModuleCat.{u} R}
    (φ : N₁ ⟶ N₂) (ψ : N₂ ⟶ N₃) (i : ℕ) :
    torMapSecond M N₁ N₃ (φ ≫ ψ) i =
      torMapSecond M N₁ N₂ φ i ≫ torMapSecond M N₂ N₃ ψ i := by
  unfold torMapSecond
  dsimp
  change HomologicalComplex.homologyMap
      (tensorComplexMapRight (Classical.choice (exists_free_resolution M)).complex (φ ≫ ψ)) i =
    HomologicalComplex.homologyMap
        (tensorComplexMapRight (Classical.choice (exists_free_resolution M)).complex φ) i ≫
      HomologicalComplex.homologyMap
        (tensorComplexMapRight (Classical.choice (exists_free_resolution M)).complex ψ) i
  have hmap : tensorComplexMapRight (Classical.choice (exists_free_resolution M)).complex (φ ≫ ψ) =
      tensorComplexMapRight (Classical.choice (exists_free_resolution M)).complex φ ≫
        tensorComplexMapRight (Classical.choice (exists_free_resolution M)).complex ψ := by
    apply HomologicalComplex.hom_ext
    intro p
    apply ModuleCat.hom_ext
    simp [tensorComplexMapRight, ModuleCat.hom_comp, LinearMap.lTensor_comp]
    rfl
  rw [hmap, HomologicalComplex.homologyMap_comp]

/-- The two Tor-variable maps form the commutative square from the source. -/
theorem torMap_commute {R : Type u} [CommRing R]
    {M₁ M₂ N₁ N₂ : ModuleCat.{u} R}
    (φ : M₁ ⟶ M₂) (ψ : N₁ ⟶ N₂) (i : ℕ) :
    torMapFirst (N := N₁) φ i ≫ torMapSecond M₂ N₁ N₂ ψ i =
      torMapSecond M₁ N₁ N₂ ψ i ≫ torMapFirst (N := N₂) φ i := by
  unfold torMapFirst torMapSecond
  dsimp
  let F₁ : FreeResolution R M₁ := Classical.choice (exists_free_resolution M₁)
  let F₂ : FreeResolution R M₂ := Classical.choice (exists_free_resolution M₂)
  let α : ResolutionMap F₁.resolution F₂.resolution φ :=
    Classical.choice (resolution_map_exists F₁ F₂.resolution φ)
  change resolutionTorMap F₁ F₂ φ α N₁ i ≫
      chainHomologyMap (tensorComplexMapRight F₂.complex ψ) i =
    chainHomologyMap (tensorComplexMapRight F₁.complex ψ) i ≫
      resolutionTorMap F₁ F₂ φ α N₂ i
  have hmap :
      tensorComplexMap α.hom N₁ ≫ tensorComplexMapRight F₂.complex ψ =
        tensorComplexMapRight F₁.complex ψ ≫ tensorComplexMap α.hom N₂ := by
    apply HomologicalComplex.hom_ext
    intro p
    apply ModuleCat.hom_ext
    simp [tensorComplexMap, tensorComplexMapRight]
    apply TensorProduct.ext'
    intro x y
    rfl
  unfold resolutionTorMap
  change HomologicalComplex.homologyMap (tensorComplexMap α.hom N₁) i ≫
      HomologicalComplex.homologyMap (tensorComplexMapRight F₂.complex ψ) i =
    HomologicalComplex.homologyMap (tensorComplexMapRight F₁.complex ψ) i ≫
      HomologicalComplex.homologyMap (tensorComplexMap α.hom N₂) i
  rw [← HomologicalComplex.homologyMap_comp
        (tensorComplexMap α.hom N₁) (tensorComplexMapRight F₂.complex ψ) i,
      ← HomologicalComplex.homologyMap_comp
        (tensorComplexMapRight F₁.complex ψ) (tensorComplexMap α.hom N₂) i,
      hmap]

/-! ## The Tor long exact sequence -/

/-- Tensoring a module map on the right by a fixed module. -/
def tensorByMap {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) {N P : ModuleCat.{u} R} (f : N ⟶ P) :
    TensorProduct R M N →ₗ[R] TensorProduct R M P :=
  f.hom.lTensor M

/-- The six-term exact segment in the long exact sequence of Tor, including
the terminal surjection onto the zero module. -/
structure TorLongExactSequence {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) (S : ShortComplex (ModuleCat.{u} R)) where
  map₁ : Tor M S.X₁ 1 →ₗ[R] Tor M S.X₂ 1
  map₂ : Tor M S.X₂ 1 →ₗ[R] Tor M S.X₃ 1
  connecting : Tor M S.X₃ 1 →ₗ[R] TensorProduct R M S.X₁
  map₁_eq : map₁ = (torMapSecond M S.X₁ S.X₂ S.f 1).hom
  map₂_eq : map₂ = (torMapSecond M S.X₂ S.X₃ S.g 1).hom
  exact₁ : Function.Exact map₁ map₂
  exact₂ : Function.Exact map₂ connecting
  exact₃ : Function.Exact connecting (tensorByMap M S.f)
  exact₄ : Function.Exact (tensorByMap M S.f) (tensorByMap M S.g)
  terminal_surjective : Function.Surjective (tensorByMap M S.g)

/-- A short exact sequence of modules admits the source's long exact Tor
segment. -/
theorem exists_tor_long_exact_sequence {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) : Nonempty (TorLongExactSequence M S) := by
  classical
  let F : FreeResolution R M := Classical.choice (exists_free_resolution M)
  let T : ShortComplex (HomologicalComplex (ModuleCat.{u} R) (ComplexShape.down ℕ)) :=
    ShortComplex.mk (tensorComplexMapRight F.complex S.f) (tensorComplexMapRight F.complex S.g) (by
      apply HomologicalComplex.hom_ext
      intro i
      apply ModuleCat.hom_ext
      change ((S.g.hom).lTensor (F.complex.X i)).comp
          ((S.f.hom).lTensor (F.complex.X i)) = 0
      rw [← LinearMap.lTensor_comp]
      rw [show (S.g.hom.comp S.f.hom) = 0 by
        exact congrArg (fun q => q.hom) S.zero]
      simp)
  have hT : T.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro i
    dsimp [T, tensorComplexMapRight]
    apply ModuleCat.shortComplex_shortExact
    · rw [← ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      let _ : Module.Free R (F.complex.X i) := F.free i
      exact Module.Flat.lTensor_shortComplex_exact (F.complex.X i) S hS.exact
    · let _ : Module.Free R (F.complex.X i) := F.free i
      exact Module.Flat.lTensor_preserves_injective_linearMap S.f.hom
        hS.moduleCat_injective_f
    · exact LinearMap.lTensor_surjective _ hS.moduleCat_surjective_g
  let e₀ : (tensorComplex F.complex S.X₁).X 0 ≅
      ModuleCat.of R (TensorProduct R (F.complex.X 0) S.X₁) :=
    eqToIso (by dsimp [tensorComplex])
  let e₁ : (tensorComplex F.complex S.X₁).X 1 ≅
      ModuleCat.of R (TensorProduct R (F.complex.X 1) S.X₁) :=
    eqToIso (by dsimp [tensorComplex])
  let b₁ : ModuleCat.of R (TensorProduct R (F.complex.X 0) S.X₁) ⟶
      ModuleCat.of R (TensorProduct R M S.X₁) := by
    exact ModuleCat.ofHom (LinearMap.rTensor S.X₁ F.resolution.augmentation.hom)
  let a₁ : (tensorComplex F.complex S.X₁).cycles 0 ⟶
      ModuleCat.of R (TensorProduct R M S.X₁) :=
    (tensorComplex F.complex S.X₁).iCycles 0 ≫ e₀.hom ≫ b₁
  have ha₁ : (tensorComplex F.complex S.X₁).toCycles 1 0 ≫ a₁ = 0 := by
    change (tensorComplex F.complex S.X₁).toCycles 1 0 ≫
      (tensorComplex F.complex S.X₁).iCycles 0 ≫ e₀.hom ≫ b₁ = 0
    rw [← Category.assoc, HomologicalComplex.toCycles_i]
    dsimp [e₀, b₁, tensorComplex]
    apply ModuleCat.hom_ext
    change (LinearMap.rTensor S.X₁ F.resolution.augmentation.hom).comp
        (LinearMap.rTensor S.X₁ (F.complex.d 1 0).hom) = 0
    rw [← LinearMap.rTensor_comp]
    rw [show F.resolution.augmentation.hom.comp (F.complex.d 1 0).hom = 0 by
      exact congrArg (fun q => q.hom) F.resolution.augmentation_condition]
    rw [LinearMap.rTensor_zero]
  let q₁' : cokernel ((tensorComplex F.complex S.X₁).toCycles 1 0) ⟶
      ModuleCat.of R (TensorProduct R M S.X₁) :=
    cokernel.desc ((tensorComplex F.complex S.X₁).toCycles 1 0) a₁ ha₁
  have hq₁' : IsIso q₁' := by
    have hex : Function.Exact (LinearMap.rTensor S.X₁ (F.complex.d 1 0).hom)
        (LinearMap.rTensor S.X₁ F.resolution.augmentation.hom) := by
      apply rTensor_exact (S.X₁ : Type u)
      · exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
          (ShortComplex.mk (F.complex.d 1 0) F.resolution.augmentation
            F.resolution.augmentation_condition)).mp F.resolution.exact_zero
      · exact (ModuleCat.epi_iff_surjective F.resolution.augmentation).mp
          F.resolution.augmentation_epi
    let C₁ : ShortComplex (ModuleCat R) :=
      ShortComplex.mk ((tensorComplex F.complex S.X₁).toCycles 1 0) a₁ ha₁
    let D₁ : ShortComplex (ModuleCat R) :=
      ShortComplex.mk
        (ModuleCat.ofHom (LinearMap.rTensor S.X₁ (F.complex.d 1 0).hom))
        b₁ (by
          apply ModuleCat.hom_ext
          change (LinearMap.rTensor S.X₁ F.resolution.augmentation.hom).comp
              (LinearMap.rTensor S.X₁ (F.complex.d 1 0).hom) = 0
          rw [← LinearMap.rTensor_comp]
          rw [show F.resolution.augmentation.hom.comp (F.complex.d 1 0).hom = 0 by
            exact congrArg (fun q => q.hom) F.resolution.augmentation_condition]
          rw [LinearMap.rTensor_zero])
    have hD₁ : D₁.Exact := ModuleCat.shortComplex_exact D₁ hex
    let i₁ : C₁ ≅ D₁ := ShortComplex.isoMk e₁
      ((tensorComplex F.complex S.X₁).iCyclesIso 0 0 (by simp) (by simp) ≪≫ e₀)
      (Iso.refl _)
      (by
        dsimp [C₁, D₁]
        change e₁.hom ≫
            ModuleCat.ofHom (LinearMap.rTensor S.X₁ (F.complex.d 1 0).hom) =
          ((tensorComplex F.complex S.X₁).toCycles 1 0 ≫
            (tensorComplex F.complex S.X₁).iCycles 0) ≫ e₀.hom
        rw [HomologicalComplex.toCycles_i]
        simp [e₀, e₁, tensorComplex])
      (by
        dsimp [C₁, D₁, a₁]
        change ((tensorComplex F.complex S.X₁).iCycles 0 ≫ e₀.hom) ≫ b₁ =
          ((tensorComplex F.complex S.X₁).iCycles 0 ≫ e₀.hom ≫ b₁) ≫ 𝟙 _
        simp [Category.assoc])
    have hC₁ : C₁.Exact := (ShortComplex.exact_iff_of_iso i₁).2 hD₁
    have hmono : Mono q₁' := by
      exact (ShortComplex.exact_iff_mono_cokernel_desc C₁).mp hC₁
    let _ : Mono q₁' := hmono
    let _ : Epi b₁ := (ModuleCat.epi_iff_surjective b₁).2 (by
      change Function.Surjective (LinearMap.rTensor S.X₁ F.resolution.augmentation.hom)
      exact LinearMap.rTensor_surjective _
        ((ModuleCat.epi_iff_surjective F.resolution.augmentation).mp
          F.resolution.augmentation_epi))
    let _ : IsIso ((tensorComplex F.complex S.X₁).iCycles 0) :=
      (tensorComplex F.complex S.X₁).isIso_iCycles 0 0 (by simp) (by simp)
    have : Epi a₁ := by
      dsimp [a₁]
      infer_instance
    let _ : Epi (cokernel.π ((tensorComplex F.complex S.X₁).toCycles 1 0) ≫ q₁') := by
      rw [cokernel.π_desc]
      infer_instance
    have : Epi q₁' := epi_of_epi_fac
      (f := cokernel.π ((tensorComplex F.complex S.X₁).toCycles 1 0))
      (g := q₁') (h := a₁) (by simp [q₁'])
    exact isIso_of_mono_of_epi q₁'
  let hcol₁ := HomologicalComplex.homologyIsCokernel
    (tensorComplex F.complex S.X₁) 1 0 (by simp)
  let ccol₁ := cokernelIsCokernel ((tensorComplex F.complex S.X₁).toCycles 1 0)
  let hcan₁ := colimit.isColimit (parallelPair
    ((tensorComplex F.complex S.X₁).toCycles 1 0) 0)
  let eHom₁ : (tensorComplex F.complex S.X₁).homology 0 ≅
      cokernel ((tensorComplex F.complex S.X₁).toCycles 1 0) :=
    hcol₁.coconePointUniqueUpToIso hcan₁ ≪≫
      (ccol₁.coconePointUniqueUpToIso hcan₁).symm
  let q₁Iso : (tensorComplex F.complex S.X₁).homology 0 ≅
      ModuleCat.of R (TensorProduct R M S.X₁) := by
    letI : IsIso q₁' := hq₁'
    exact eHom₁ ≪≫ asIso q₁'
  let q₁ := q₁Iso.hom
  let tensorAug (N : ModuleCat R) :
      (tensorComplex F.complex N).cycles 0 ⟶
        ModuleCat.of R (TensorProduct R M N) :=
    (tensorComplex F.complex N).iCycles 0 ≫
      (eqToIso (by dsimp [tensorComplex])).hom ≫
      ModuleCat.ofHom (LinearMap.rTensor N F.resolution.augmentation.hom)
  let makeQ (N : ModuleCat R) :
      { q : (tensorComplex F.complex N).homology 0 ≅
          ModuleCat.of R (TensorProduct R M N) //
        (tensorComplex F.complex N).homologyπ 0 ≫ q.hom = tensorAug N } := by
    let e₀ : (tensorComplex F.complex N).X 0 ≅
        ModuleCat.of R (TensorProduct R (F.complex.X 0) N) :=
      eqToIso (by dsimp [tensorComplex])
    let e₁ : (tensorComplex F.complex N).X 1 ≅
        ModuleCat.of R (TensorProduct R (F.complex.X 1) N) :=
      eqToIso (by dsimp [tensorComplex])
    let b₁ : ModuleCat.of R (TensorProduct R (F.complex.X 0) N) ⟶
        ModuleCat.of R (TensorProduct R M N) := by
      exact ModuleCat.ofHom (LinearMap.rTensor N F.resolution.augmentation.hom)
    let a₁ : (tensorComplex F.complex N).cycles 0 ⟶
        ModuleCat.of R (TensorProduct R M N) :=
      (tensorComplex F.complex N).iCycles 0 ≫ e₀.hom ≫ b₁
    have ha₁ : (tensorComplex F.complex N).toCycles 1 0 ≫ a₁ = 0 := by
      change (tensorComplex F.complex N).toCycles 1 0 ≫
        (tensorComplex F.complex N).iCycles 0 ≫ e₀.hom ≫ b₁ = 0
      rw [← Category.assoc, HomologicalComplex.toCycles_i]
      dsimp [e₀, b₁, tensorComplex]
      apply ModuleCat.hom_ext
      change (LinearMap.rTensor N F.resolution.augmentation.hom).comp
          (LinearMap.rTensor N (F.complex.d 1 0).hom) = 0
      rw [← LinearMap.rTensor_comp]
      rw [show F.resolution.augmentation.hom.comp (F.complex.d 1 0).hom = 0 by
        exact congrArg (fun q => q.hom) F.resolution.augmentation_condition]
      rw [LinearMap.rTensor_zero]
    let q' : cokernel ((tensorComplex F.complex N).toCycles 1 0) ⟶
        ModuleCat.of R (TensorProduct R M N) :=
      cokernel.desc ((tensorComplex F.complex N).toCycles 1 0) a₁ ha₁
    have hq' : IsIso q' := by
      have hex : Function.Exact (LinearMap.rTensor N (F.complex.d 1 0).hom)
          (LinearMap.rTensor N F.resolution.augmentation.hom) := by
        apply rTensor_exact (N : Type u)
        · exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
            (ShortComplex.mk (F.complex.d 1 0) F.resolution.augmentation
              F.resolution.augmentation_condition)).mp F.resolution.exact_zero
        · exact (ModuleCat.epi_iff_surjective F.resolution.augmentation).mp
            F.resolution.augmentation_epi
      let C : ShortComplex (ModuleCat R) :=
        ShortComplex.mk ((tensorComplex F.complex N).toCycles 1 0) a₁ ha₁
      let D : ShortComplex (ModuleCat R) :=
        ShortComplex.mk
          (ModuleCat.ofHom (LinearMap.rTensor N (F.complex.d 1 0).hom))
          b₁ (by
            apply ModuleCat.hom_ext
            change (LinearMap.rTensor N F.resolution.augmentation.hom).comp
                (LinearMap.rTensor N (F.complex.d 1 0).hom) = 0
            rw [← LinearMap.rTensor_comp]
            rw [show F.resolution.augmentation.hom.comp (F.complex.d 1 0).hom = 0 by
              exact congrArg (fun q => q.hom) F.resolution.augmentation_condition]
            rw [LinearMap.rTensor_zero])
      have hD : D.Exact := ModuleCat.shortComplex_exact D hex
      let i : C ≅ D := ShortComplex.isoMk e₁
        ((tensorComplex F.complex N).iCyclesIso 0 0 (by simp) (by simp) ≪≫ e₀)
        (Iso.refl _)
        (by
          dsimp [C, D]
          change e₁.hom ≫
              ModuleCat.ofHom (LinearMap.rTensor N (F.complex.d 1 0).hom) =
            ((tensorComplex F.complex N).toCycles 1 0 ≫
              (tensorComplex F.complex N).iCycles 0) ≫ e₀.hom
          rw [HomologicalComplex.toCycles_i]
          simp [e₀, e₁, tensorComplex])
        (by
          dsimp [C, D, a₁]
          change ((tensorComplex F.complex N).iCycles 0 ≫ e₀.hom) ≫ b₁ =
            ((tensorComplex F.complex N).iCycles 0 ≫ e₀.hom ≫ b₁) ≫ 𝟙 _
          simp [Category.assoc])
      have hC : C.Exact := (ShortComplex.exact_iff_of_iso i).2 hD
      have hmono : Mono q' :=
        (ShortComplex.exact_iff_mono_cokernel_desc C).mp hC
      let _ : Mono q' := hmono
      let _ : Epi b₁ := (ModuleCat.epi_iff_surjective b₁).2 (by
        change Function.Surjective (LinearMap.rTensor N F.resolution.augmentation.hom)
        exact LinearMap.rTensor_surjective _
          ((ModuleCat.epi_iff_surjective F.resolution.augmentation).mp
            F.resolution.augmentation_epi))
      let _ : IsIso ((tensorComplex F.complex N).iCycles 0) :=
        (tensorComplex F.complex N).isIso_iCycles 0 0 (by simp) (by simp)
      have : Epi a₁ := by
        dsimp [a₁]
        infer_instance
      let _ : Epi (cokernel.π ((tensorComplex F.complex N).toCycles 1 0) ≫ q') := by
        rw [cokernel.π_desc]
        infer_instance
      have : Epi q' := epi_of_epi_fac
        (f := cokernel.π ((tensorComplex F.complex N).toCycles 1 0))
        (g := q') (h := a₁) (by simp [q'])
      exact isIso_of_mono_of_epi q'
    let hcol := HomologicalComplex.homologyIsCokernel
      (tensorComplex F.complex N) 1 0 (by simp)
    let ccol := cokernelIsCokernel ((tensorComplex F.complex N).toCycles 1 0)
    let hcan := colimit.isColimit (parallelPair
      ((tensorComplex F.complex N).toCycles 1 0) 0)
    let eHom : (tensorComplex F.complex N).homology 0 ≅
        cokernel ((tensorComplex F.complex N).toCycles 1 0) :=
      hcol.coconePointUniqueUpToIso hcan ≪≫
        (ccol.coconePointUniqueUpToIso hcan).symm
    letI : IsIso q' := hq'
    refine ⟨eHom ≪≫ asIso q', ?_⟩
    let s := CokernelCofork.ofπ a₁ ha₁
    have hdesc :
        (hcol.coconePointUniqueUpToIso hcan).hom ≫ hcan.desc s =
          hcol.desc s := by
      apply hcol.uniq
      intro j
      rw [← Category.assoc, hcol.comp_coconePointUniqueUpToIso_hom hcan j]
      exact hcan.fac s j
    have hdesc₂ :
        (ccol.coconePointUniqueUpToIso hcan).inv ≫
            cokernel.desc ((tensorComplex F.complex N).toCycles 1 0) a₁ ha₁ =
          hcan.desc s := by
      refine hcan.uniq s _ ?_
      intro j
      simp [hcan, ccol]
      cases j <;> simp [s, ha₁]
    have hq : (eHom ≪≫ asIso q').hom =
        (hcol.coconePointUniqueUpToIso hcan).hom ≫ hcan.desc s := by
      change
        ((hcol.coconePointUniqueUpToIso hcan).hom ≫
            (ccol.coconePointUniqueUpToIso hcan).inv) ≫
          cokernel.desc ((tensorComplex F.complex N).toCycles 1 0) a₁ ha₁ =
        (hcol.coconePointUniqueUpToIso hcan).hom ≫ hcan.desc s
      rw [Category.assoc, hdesc₂, hdesc]
    have hfac : (tensorComplex F.complex N).homologyπ 0 ≫
        (hcol.coconePointUniqueUpToIso hcan).hom ≫ hcan.desc s = a₁ := by
      calc
        (tensorComplex F.complex N).homologyπ 0 ≫
              (hcol.coconePointUniqueUpToIso hcan).hom ≫ hcan.desc s =
            (tensorComplex F.complex N).homologyπ 0 ≫ hcol.desc s := by
              exact congrArg (fun k => (tensorComplex F.complex N).homologyπ 0 ≫ k) hdesc
        _ = a₁ := by
          simpa [s, Cofork.app_one_eq_π, CokernelCofork.π_ofπ] using
            hcol.fac s WalkingParallelPair.one
    change (tensorComplex F.complex N).homologyπ 0 ≫
        (eHom ≪≫ asIso q').hom = a₁
    rw [hq, hfac]
  let q₂Data := makeQ S.X₂
  let q₂Iso := q₂Data.1
  let q₂ := q₂Iso.hom
  let e₂ : (tensorComplex F.complex S.X₂).X 0 ≅
      ModuleCat.of R (TensorProduct R (F.complex.X 0) S.X₂) :=
    eqToIso (by dsimp [tensorComplex])
  let b₂ : ModuleCat.of R (TensorProduct R (F.complex.X 0) S.X₂) ⟶
      ModuleCat.of R (TensorProduct R M S.X₂) :=
    ModuleCat.ofHom (LinearMap.rTensor S.X₂ F.resolution.augmentation.hom)
  let a₂ : (tensorComplex F.complex S.X₂).cycles 0 ⟶
      ModuleCat.of R (TensorProduct R M S.X₂) :=
    (tensorComplex F.complex S.X₂).iCycles 0 ≫ e₂.hom ≫ b₂
  have hπq₁ : (tensorComplex F.complex S.X₁).homologyπ 0 ≫ q₁ = a₁ := by
    let s₁ := CokernelCofork.ofπ a₁ ha₁
    have hdesc :
        (hcol₁.coconePointUniqueUpToIso hcan₁).hom ≫ hcan₁.desc s₁ =
          hcol₁.desc s₁ := by
      apply hcol₁.uniq
      intro j
      rw [← Category.assoc, hcol₁.comp_coconePointUniqueUpToIso_hom hcan₁ j]
      exact hcan₁.fac s₁ j
    have hdesc₂ :
        (ccol₁.coconePointUniqueUpToIso hcan₁).inv ≫
          cokernel.desc ((tensorComplex F.complex S.X₁).toCycles 1 0) a₁ ha₁ =
            hcan₁.desc s₁ := by
      refine hcan₁.uniq s₁ _ ?_
      intro j
      simp [hcan₁, ccol₁]
      cases j <;> simp [s₁, ha₁]
    have hq₁ : (eHom₁ ≪≫ asIso q₁').hom =
        (hcol₁.coconePointUniqueUpToIso hcan₁).hom ≫ hcan₁.desc s₁ := by
      change
        ((hcol₁.coconePointUniqueUpToIso hcan₁).hom ≫
            (ccol₁.coconePointUniqueUpToIso hcan₁).inv) ≫
          cokernel.desc ((tensorComplex F.complex S.X₁).toCycles 1 0) a₁ ha₁ =
        (hcol₁.coconePointUniqueUpToIso hcan₁).hom ≫ hcan₁.desc s₁
      rw [Category.assoc, hdesc₂, hdesc]
    have hfac₁ : (tensorComplex F.complex S.X₁).homologyπ 0 ≫
        (hcol₁.coconePointUniqueUpToIso hcan₁).hom ≫ hcan₁.desc s₁ = a₁ := by
      calc
        (tensorComplex F.complex S.X₁).homologyπ 0 ≫
              (hcol₁.coconePointUniqueUpToIso hcan₁).hom ≫ hcan₁.desc s₁ =
            (tensorComplex F.complex S.X₁).homologyπ 0 ≫ hcol₁.desc s₁ := by
              exact congrArg (fun k => (tensorComplex F.complex S.X₁).homologyπ 0 ≫ k) hdesc
        _ = a₁ := by
          simpa [s₁, Cofork.app_one_eq_π, CokernelCofork.π_ofπ] using
            hcol₁.fac s₁ WalkingParallelPair.one
    change (tensorComplex F.complex S.X₁).homologyπ 0 ≫
        (eHom₁ ≪≫ asIso q₁').hom = a₁
    rw [hq₁, hfac₁]
  have hπq₂ : (tensorComplex F.complex S.X₂).homologyπ 0 ≫ q₂ = a₂ := by
    change (tensorComplex F.complex S.X₂).homologyπ 0 ≫ q₂Data.1.hom =
      tensorAug S.X₂
    exact q₂Data.2
  have hq12 :
      HomologicalComplex.homologyMap (tensorComplexMapRight F.complex S.f) 0 ≫ q₂ =
        q₁ ≫ ModuleCat.ofHom (tensorByMap M S.f) := by
    apply (cancel_epi ((tensorComplex F.complex S.X₁).homologyπ 0)).1
    rw [← Category.assoc, HomologicalComplex.homologyπ_naturality]
    simp only [Category.assoc]
    rw [hπq₂]
    conv_rhs => rw [← Category.assoc]
    rw [hπq₁]
    dsimp [a₁, a₂]
    rw [← Category.assoc, HomologicalComplex.cyclesMap_i]
    simp only [Category.assoc]
    apply (cancel_epi ((tensorComplex F.complex S.X₁).iCycles 0)).2
    simp [e₀, e₂, b₁, b₂, tensorComplexMapRight, tensorByMap, tensorComplex]
    apply ModuleCat.hom_ext
    change
      (LinearMap.rTensor (S.X₂ : Type u) F.resolution.augmentation.hom).comp
          (LinearMap.lTensor (F.complex.X 0) S.f.hom) =
        (LinearMap.lTensor M S.f.hom).comp
          (LinearMap.rTensor (S.X₁ : Type u) F.resolution.augmentation.hom)
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  let H := HomologicalComplex.HomologySequence.snakeInput hT 1 0 (by simp)
  refine ⟨
    { map₁ := H.L₀.f.hom
      map₂ := H.L₀.g.hom
      connecting := (H.δ ≫ q₁).hom
      map₁_eq := by rfl
      map₂_eq := by rfl
      exact₁ := by
        exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact H.L₀).mp H.L₀_exact
      exact₂ := by
        let q₁HIso : H.L₃.X₁ ≅ ModuleCat.of R (TensorProduct R M S.X₁) := by
          change (tensorComplex F.complex S.X₁).homology 0 ≅
            ModuleCat.of R (TensorProduct R M S.X₁)
          exact q₁Iso
        let E₂ : ShortComplex (ModuleCat R) :=
          ShortComplex.mk H.L₀.g (H.δ ≫ q₁HIso.hom) (by
            rw [← Category.assoc, H.L₀_g_δ, zero_comp])
        let i₂ : H.L₁' ≅ E₂ :=
          ShortComplex.isoMk (Iso.refl _) (Iso.refl _) q₁HIso
            (by
              dsimp [E₂, ShortComplex.SnakeInput.L₁']
              simp)
            (by
              dsimp [E₂, ShortComplex.SnakeInput.L₁']
              simp)
        have hE₂ : E₂.Exact :=
          (ShortComplex.exact_iff_of_iso i₂).1 H.L₁'_exact
        change Function.Exact E₂.f E₂.g
        exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact E₂).mp hE₂
      exact₃ := by
        let q₁HIso : H.L₃.X₁ ≅ ModuleCat.of R (TensorProduct R M S.X₁) := by
          change (tensorComplex F.complex S.X₁).homology 0 ≅
            ModuleCat.of R (TensorProduct R M S.X₁)
          exact q₁Iso
        let q₂HIso : H.L₃.X₂ ≅ ModuleCat.of R (TensorProduct R M S.X₂) := by
          change (tensorComplex F.complex S.X₂).homology 0 ≅
            ModuleCat.of R (TensorProduct R M S.X₂)
          exact q₂Iso
        have hcomm : q₁HIso.hom ≫ ModuleCat.ofHom (tensorByMap M S.f) =
            H.L₃.f ≫ q₂HIso.hom := by
          symm
          dsimp [H, q₁HIso, q₂Iso, q₂]
          exact hq12
        let E₃ : ShortComplex (ModuleCat R) :=
          ShortComplex.mk (H.δ ≫ q₁HIso.hom)
            (ModuleCat.ofHom (tensorByMap M S.f)) (by
              rw [Category.assoc]
              rw [hcomm, ← Category.assoc, H.δ_L₃_f, zero_comp])
        let i₃ : H.L₂' ≅ E₃ :=
          ShortComplex.isoMk (Iso.refl _) q₁HIso q₂HIso
            (by
              dsimp [E₃, ShortComplex.SnakeInput.L₂']
              simp)
            (by
              dsimp [E₃, ShortComplex.SnakeInput.L₂']
              exact hcomm)
        have hE₃ : E₃.Exact :=
          (ShortComplex.exact_iff_of_iso i₃).1 H.L₂'_exact
        change Function.Exact E₃.f E₃.g
        exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact E₃).mp hE₃
      exact₄ := by
        change Function.Exact (LinearMap.lTensor (M : Type u) S.f.hom)
          (LinearMap.lTensor (M : Type u) S.g.hom)
        apply lTensor_exact (M : Type u)
        · exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
        · exact hS.moduleCat_surjective_g
      terminal_surjective := by
        change Function.Surjective (LinearMap.lTensor (M : Type u) S.g.hom)
        exact LinearMap.lTensor_surjective _ hS.moduleCat_surjective_g }⟩

/-! ## Double complexes and the two quotient complexes -/

/-- A homological double complex of modules in the first quadrant. -/
structure DoubleComplex (R : Type u) [CommRing R] where
  obj : ℕ → ℕ → ModuleCat.{u} R
  d : ∀ i j, obj (i + 1) j ⟶ obj i j
  delta : ∀ i j, obj i (j + 1) ⟶ obj i j
  d_sq : ∀ i j, d (i + 1) j ≫ d i j = 0
  delta_sq : ∀ i j, delta i (j + 1) ≫ delta i j = 0
  comm : ∀ i j, d i (j + 1) ≫ delta i j = delta (i + 1) j ≫ d i j

/-- A morphism of double complexes. -/
structure DoubleComplexMap {R : Type u} [CommRing R]
    (A B : DoubleComplex R) where
  f : ∀ i j, A.obj i j ⟶ B.obj i j
  d_comm : ∀ i j, A.d i j ≫ f i j = f (i + 1) j ≫ B.d i j
  delta_comm : ∀ i j, A.delta i j ≫ f i j = f i (j + 1) ≫ B.delta i j

/-- The right quotient terms `R(A)_j = coker(A_{1,j} → A_{0,j})`. -/
noncomputable def rightTerm {R : Type u} [CommRing R]
    (A : DoubleComplex R) (j : ℕ) : ModuleCat.{u} R :=
  cokernel (A.d 0 j)

/-- The up quotient terms `U(A)_i = coker(A_{i,1} → A_{i,0})`. -/
noncomputable def upTerm {R : Type u} [CommRing R]
    (A : DoubleComplex R) (i : ℕ) : ModuleCat.{u} R :=
  cokernel (A.delta i 0)

/-- The differential induced by `delta` on the right quotient terms. -/
  noncomputable def rightDifferential {R : Type u} [CommRing R]
    (A : DoubleComplex R) (j : ℕ) :
    rightTerm A (j + 1) ⟶ rightTerm A j :=
  cokernel.map (A.d 0 (j + 1)) (A.d 0 j) (A.delta 1 j) (A.delta 0 j)
    (A.comm 0 j)

/-- The differential induced by `d` on the up quotient terms. -/
noncomputable def upDifferential {R : Type u} [CommRing R]
    (A : DoubleComplex R) (i : ℕ) :
    upTerm A (i + 1) ⟶ upTerm A i :=
  cokernel.map (A.delta (i + 1) 0) (A.delta i 0) (A.d i 1) (A.d i 0)
    (A.comm i 0).symm

/-- Consecutive induced right differentials compose to zero. -/
theorem rightDifferential_comp_zero {R : Type u} [CommRing R]
    (A : DoubleComplex R) (j : ℕ) :
    rightDifferential A (j + 1) ≫ rightDifferential A j = 0 := by
  change
    (cokernel.map (A.d 0 (j + 1 + 1)) (A.d 0 (j + 1))
        (A.delta 1 (j + 1)) (A.delta 0 (j + 1)) (A.comm 0 (j + 1)) ≫
      cokernel.map (A.d 0 (j + 1)) (A.d 0 j)
        (A.delta 1 j) (A.delta 0 j) (A.comm 0 j)) = 0
  apply (cancel_epi (cokernel.π (A.d 0 (j + 1 + 1)))).1
  rw [← Category.assoc, cokernel.π_desc, Category.assoc, cokernel.π_desc]
  rw [← Category.assoc]
  rw [A.delta_sq]
  simp only [zero_comp, comp_zero]

/-- Consecutive induced up differentials compose to zero. -/
theorem upDifferential_comp_zero {R : Type u} [CommRing R]
    (A : DoubleComplex R) (i : ℕ) :
    upDifferential A (i + 1) ≫ upDifferential A i = 0 := by
  change
    (cokernel.map (A.delta (i + 1 + 1) 0) (A.delta (i + 1) 0)
        (A.d (i + 1) 1) (A.d (i + 1) 0) (A.comm (i + 1) 0).symm ≫
      cokernel.map (A.delta (i + 1) 0) (A.delta i 0)
        (A.d i 1) (A.d i 0) (A.comm i 0).symm) = 0
  apply (cancel_epi (cokernel.π (A.delta (i + 1 + 1) 0))).1
  rw [← Category.assoc, cokernel.π_desc, Category.assoc, cokernel.π_desc]
  rw [← Category.assoc]
  rw [A.d_sq]
  simp only [zero_comp, comp_zero]

/-- The right quotient complex `R(A)_•`. -/
noncomputable def rightComplex {R : Type u} [CommRing R]
    (A : DoubleComplex R) : ModuleChainComplex R where
  X i := rightTerm A i
  d i j := if h : j + 1 = i then h ▸ rightDifferential A j else 0
  shape i j hij := by
    classical
    split_ifs with h
    · exact (hij h).elim
    · rfl
  d_comp_d' i j k hij hjk := by
    classical
    have hij' : j + 1 = i := by
      simpa only [ComplexShape.down_Rel] using hij
    have hjk' : k + 1 = j := by
      simpa only [ComplexShape.down_Rel] using hjk
    rw [dif_pos hij', dif_pos hjk']
    subst i
    subst j
    exact rightDifferential_comp_zero A k

/-- The up quotient complex `U(A)_•`. -/
noncomputable def upComplex {R : Type u} [CommRing R]
    (A : DoubleComplex R) : ModuleChainComplex R where
  X i := upTerm A i
  d i j := if h : j + 1 = i then h ▸ upDifferential A j else 0
  shape i j hij := by
    classical
    split_ifs with h
    · exact (hij h).elim
    · rfl
  d_comp_d' i j k hij hjk := by
    classical
    have hij' : j + 1 = i := by
      simpa only [ComplexShape.down_Rel] using hij
    have hjk' : k + 1 = j := by
      simpa only [ComplexShape.down_Rel] using hjk
    rw [dif_pos hij', dif_pos hjk']
    subst i
    subst j
    exact upDifferential_comp_zero A k

/-- The row complex of a double complex. -/
noncomputable def rowComplex {R : Type u} [CommRing R]
    (A : DoubleComplex R) (j : ℕ) : ModuleChainComplex R where
  X i := A.obj i j
  d i k := if h : k + 1 = i then h ▸ A.d k j else 0
  shape i k hik := by
    classical
    split_ifs with h
    · exact (hik h).elim
    · rfl
  d_comp_d' i k l hik hkl := by
    classical
    have hik' : k + 1 = i := by
      simpa only [ComplexShape.down_Rel] using hik
    have hkl' : l + 1 = k := by
      simpa only [ComplexShape.down_Rel] using hkl
    rw [dif_pos hik', dif_pos hkl']
    subst i
    subst k
    exact A.d_sq l j

/-- The column complex of a double complex. -/
noncomputable def columnComplex {R : Type u} [CommRing R]
    (A : DoubleComplex R) (i : ℕ) : ModuleChainComplex R where
  X j := A.obj i j
  d j k := if h : k + 1 = j then h ▸ A.delta i k else 0
  shape j k hjk := by
    classical
    split_ifs with h
    · exact (hjk h).elim
    · rfl
  d_comp_d' j k l hjk hkl := by
    classical
    have hjk' : k + 1 = j := by
      simpa only [ComplexShape.down_Rel] using hjk
    have hkl' : l + 1 = k := by
      simpa only [ComplexShape.down_Rel] using hkl
    rw [dif_pos hjk', dif_pos hkl']
    subst j
    subst k
    exact A.delta_sq i l

/-- A fixed chain complex and augmentation are a resolution in the sense of
the preceding chapter's `Resolution` interface. -/
def IsResolution {R : Type u} [CommRing R]
    (F : ModuleChainComplex R) (M : ModuleCat.{u} R)
    (augmentation : F.X 0 ⟶ M) : Prop :=
  ∃ (Q : Resolution R M) (hQ : Q.complex = F),
    hQ ▸ Q.augmentation = augmentation

/-- The row-resolution hypothesis in the double-complex lemma. -/
def RowsAreResolutions {R : Type u} [CommRing R]
    (A : DoubleComplex R) : Prop :=
  ∀ j, IsResolution (rowComplex A j) (rightTerm A j)
    (cokernel.π (A.d 0 j))

/-- The column-resolution hypothesis in the double-complex lemma. -/
def ColumnsAreResolutions {R : Type u} [CommRing R]
    (A : DoubleComplex R) : Prop :=
  ∀ i, IsResolution (columnComplex A i) (upTerm A i)
    (cokernel.π (A.delta i 0))

/-- The map induced on the right quotient terms by a double-complex map. -/
noncomputable def rightTermMap {R : Type u} [CommRing R]
    {A B : DoubleComplex R} (Φ : DoubleComplexMap A B) (j : ℕ) :
    rightTerm A j ⟶ rightTerm B j :=
  cokernel.map (A.d 0 j) (B.d 0 j) (Φ.f 1 j) (Φ.f 0 j) (Φ.d_comm 0 j)

/-- The map induced on the up quotient terms by a double-complex map. -/
noncomputable def upTermMap {R : Type u} [CommRing R]
    {A B : DoubleComplex R} (Φ : DoubleComplexMap A B) (i : ℕ) :
    upTerm A i ⟶ upTerm B i :=
  cokernel.map (A.delta i 0) (B.delta i 0) (Φ.f i 1) (Φ.f i 0)
    (Φ.delta_comm i 0)

/-- Naturality of the induced right differentials. -/
theorem rightTermMap_comm {R : Type u} [CommRing R]
    {A B : DoubleComplex R} (Φ : DoubleComplexMap A B) (j : ℕ) :
    rightDifferential A j ≫ rightTermMap Φ j =
      rightTermMap Φ (j + 1) ≫ rightDifferential B j := by
  change
    (cokernel.map (A.d 0 (j + 1)) (A.d 0 j)
        (A.delta 1 j) (A.delta 0 j) (A.comm 0 j) ≫
      cokernel.map (A.d 0 j) (B.d 0 j)
        (Φ.f 1 j) (Φ.f 0 j) (Φ.d_comm 0 j)) =
    (cokernel.map (A.d 0 (j + 1)) (B.d 0 (j + 1))
        (Φ.f 1 (j + 1)) (Φ.f 0 (j + 1)) (Φ.d_comm 0 (j + 1)) ≫
      cokernel.map (B.d 0 (j + 1)) (B.d 0 j)
        (B.delta 1 j) (B.delta 0 j) (B.comm 0 j))
  apply (cancel_epi (cokernel.π (A.d 0 (j + 1)))).1
  rw [← Category.assoc, cokernel.π_desc, Category.assoc, cokernel.π_desc]
  conv_rhs => rw [← Category.assoc]
  rw [cokernel.π_desc]
  conv_rhs => rw [Category.assoc, cokernel.π_desc]
  exact congrArg (fun q => q ≫ cokernel.π (B.d 0 j)) (Φ.delta_comm 0 j)

/-- Naturality of the induced up differentials. -/
theorem upTermMap_comm {R : Type u} [CommRing R]
    {A B : DoubleComplex R} (Φ : DoubleComplexMap A B) (i : ℕ) :
    upDifferential A i ≫ upTermMap Φ i =
      upTermMap Φ (i + 1) ≫ upDifferential B i := by
  change
    (cokernel.map (A.delta (i + 1) 0) (A.delta i 0)
        (A.d i 1) (A.d i 0) (A.comm i 0).symm ≫
      cokernel.map (A.delta i 0) (B.delta i 0)
        (Φ.f i 1) (Φ.f i 0) (Φ.delta_comm i 0)) =
    (cokernel.map (A.delta (i + 1) 0) (B.delta (i + 1) 0)
        (Φ.f (i + 1) 1) (Φ.f (i + 1) 0) (Φ.delta_comm (i + 1) 0) ≫
      cokernel.map (B.delta (i + 1) 0) (B.delta i 0)
        (B.d i 1) (B.d i 0) (B.comm i 0).symm)
  apply (cancel_epi (cokernel.π (A.delta (i + 1) 0))).1
  rw [← Category.assoc, cokernel.π_desc, Category.assoc, cokernel.π_desc]
  conv_rhs => rw [← Category.assoc]
  rw [cokernel.π_desc]
  conv_rhs => rw [Category.assoc, cokernel.π_desc]
  exact congrArg (fun q => q ≫ cokernel.π (B.delta i 0)) (Φ.d_comm i 0)

/-- The induced map on the right quotient complexes. -/
noncomputable def rightComplexMap {R : Type u} [CommRing R]
    {A B : DoubleComplex R} (Φ : DoubleComplexMap A B) :
    rightComplex A ⟶ rightComplex B where
  f i := rightTermMap Φ i
  comm' i j hij := by
    classical
    have hij' : j + 1 = i := by
      simpa only [ComplexShape.down_Rel] using hij
    dsimp [rightComplex]
    simp only [dif_pos hij']
    subst i
    exact (rightTermMap_comm Φ j).symm

/-- The induced map on the up quotient complexes. -/
noncomputable def upComplexMap {R : Type u} [CommRing R]
    {A B : DoubleComplex R} (Φ : DoubleComplexMap A B) :
    upComplex A ⟶ upComplex B where
  f i := upTermMap Φ i
  comm' i j hij := by
    classical
    have hij' : j + 1 = i := by
      simpa only [ComplexShape.down_Rel] using hij
    dsimp [upComplex]
    simp only [dif_pos hij']
    subst i
    exact (upTermMap_comm Φ j).symm

/-! The source calls the comparison canonical and requires functoriality.  A
chosen isomorphism for each double complex would not provide that property,
so the two requirements are bundled in one family before making a choice. -/
structure DoubleComplexHomologyIsoFamily (R : Type u) [CommRing R] where
  iso : ∀ (A : DoubleComplex R) (_hrow : RowsAreResolutions A)
    (_hcol : ColumnsAreResolutions A) (i : ℕ),
    chainHomology (rightComplex A) i ≅ chainHomology (upComplex A) i
  natural : ∀ {A B : DoubleComplex R} (Φ : DoubleComplexMap A B)
    (hrowA : RowsAreResolutions A) (hcolA : ColumnsAreResolutions A)
    (hrowB : RowsAreResolutions B) (hcolB : ColumnsAreResolutions B)
    (i : ℕ),
    chainHomologyMap (rightComplexMap Φ) i ≫
        (iso B hrowB hcolB i).hom =
      (iso A hrowA hcolA i).hom ≫
        chainHomologyMap (upComplexMap Φ) i

/-- The source's canonical, functorial double-complex comparison. -/
theorem exists_doubleComplex_homology_iso_family {R : Type u} [CommRing R] :
    Nonempty (DoubleComplexHomologyIsoFamily R) := by
  sorry

/-- A chosen family of the canonical double-complex comparisons. -/
noncomputable def doubleComplexHomologyIsoFamily {R : Type u} [CommRing R] :
    DoubleComplexHomologyIsoFamily R :=
  Classical.choice (exists_doubleComplex_homology_iso_family (R := R))

/-- The double-complex lemma produces the canonical homology isomorphism. -/
theorem doubleComplex_homology_iso_exists {R : Type u} [CommRing R]
    (A : DoubleComplex R) (hrow : RowsAreResolutions A)
    (hcol : ColumnsAreResolutions A) (i : ℕ) :
    Nonempty (chainHomology (rightComplex A) i ≅ chainHomology (upComplex A) i) :=
  ⟨(doubleComplexHomologyIsoFamily (R := R)).iso A hrow hcol i⟩

/-- The chosen representative of the canonical double-complex comparison. -/
noncomputable def doubleComplexHomologyIso {R : Type u} [CommRing R]
    (A : DoubleComplex R) (hrow : RowsAreResolutions A)
    (hcol : ColumnsAreResolutions A) (i : ℕ) :
    chainHomology (rightComplex A) i ≅ chainHomology (upComplex A) i :=
  (doubleComplexHomologyIsoFamily (R := R)).iso A hrow hcol i

/-- The double-complex homology isomorphism is functorial. -/
theorem doubleComplex_homology_iso_natural {R : Type u} [CommRing R]
    {A B : DoubleComplex R} (Φ : DoubleComplexMap A B)
    (hrowA : RowsAreResolutions A) (hcolA : ColumnsAreResolutions A)
    (hrowB : RowsAreResolutions B) (hcolB : ColumnsAreResolutions B)
    (i : ℕ) :
    chainHomologyMap (rightComplexMap Φ) i ≫
        (doubleComplexHomologyIso B hrowB hcolB i).hom =
      (doubleComplexHomologyIso A hrowA hcolA i).hom ≫
        chainHomologyMap (upComplexMap Φ) i :=
  (doubleComplexHomologyIsoFamily (R := R)).natural Φ
    hrowA hcolA hrowB hcolB i

/-! ## Symmetry and finiteness -/

/-! As with the double-complex comparison, naturality belongs to the family
of symmetry isomorphisms, not to unrelated choices made object by object. -/
structure TorSymmetryIsoFamily (R : Type u) [CommRing R] where
  iso : ∀ (M N : ModuleCat.{u} R) (i : ℕ), Tor M N i ≅ Tor N M i
  natural : ∀ {M₁ M₂ N₁ N₂ : ModuleCat.{u} R}
    (φ : M₁ ⟶ M₂) (ψ : N₁ ⟶ N₂) (i : ℕ),
    (iso M₁ N₁ i).hom ≫
        torMapFirst (N := M₁) ψ i ≫ torMapSecond N₂ M₁ M₂ φ i =
      torMapFirst (N := N₁) φ i ≫ torMapSecond M₂ N₁ N₂ ψ i ≫
        (iso M₂ N₂ i).hom

/-- The source's canonical symmetry isomorphisms, natural in both variables. -/
theorem exists_tor_symmetry_iso_family {R : Type u} [CommRing R] :
    Nonempty (TorSymmetryIsoFamily R) := by
  sorry

/-- A chosen family of the canonical Tor symmetry isomorphisms. -/
noncomputable def torSymmetryIsoFamily {R : Type u} [CommRing R] :
    TorSymmetryIsoFamily R :=
  Classical.choice (exists_tor_symmetry_iso_family (R := R))

/-- Tor is canonically symmetric in its two module variables. -/
theorem tor_left_right {R : Type u} [CommRing R]
    (M N : ModuleCat.{u} R) (i : ℕ) :
    Nonempty (Tor M N i ≅ Tor N M i) :=
  ⟨(torSymmetryIsoFamily (R := R)).iso M N i⟩

/-- A chosen representative of the canonical symmetry isomorphism for Tor. -/
noncomputable def torLeftRightIso {R : Type u} [CommRing R]
    (M N : ModuleCat.{u} R) (i : ℕ) : Tor M N i ≅ Tor N M i :=
  (torSymmetryIsoFamily (R := R)).iso M N i

/-- The Tor symmetry is natural in both variables. -/
theorem torLeftRightIso_natural {R : Type u} [CommRing R]
    {M₁ M₂ N₁ N₂ : ModuleCat.{u} R}
    (φ : M₁ ⟶ M₂) (ψ : N₁ ⟶ N₂) (i : ℕ) :
    (torLeftRightIso M₁ N₁ i).hom ≫
        torMapFirst (N := M₁) ψ i ≫ torMapSecond N₂ M₁ M₂ φ i =
      torMapFirst (N := N₁) φ i ≫ torMapSecond M₂ N₁ N₂ ψ i ≫
        (torLeftRightIso M₂ N₂ i).hom :=
  (torSymmetryIsoFamily (R := R)).natural φ ψ i

/-- Tor of finite modules over a Noetherian ring is finite. -/
theorem tor_finite_of_noetherian {R : Type u} [CommRing R]
    [IsNoetherianRing R] (M N : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Finite R N] (p : ℕ) :
    Module.Finite R (Tor M N p) := by
  let Ff : FiniteFreeResolution R M :=
    Classical.choice (exists_finite_free_resolution M)
  let C : ModuleChainComplex R :=
    tensorComplex Ff.resolution.resolution.complex N
  have hF (n : ℕ) : Module.Finite R
      (Ff.resolution.resolution.complex.X n : Type u) := Ff.finite n
  have hT (n : ℕ) : Module.Finite R
      (TensorProduct R (Ff.resolution.resolution.complex.X n : Type u) (N : Type u)) := by
    apply Module.Finite.tensorProduct
  have hX (n : ℕ) : Module.Finite R (C.X n : Type u) := by
    change Module.Finite R
      (TensorProduct R (Ff.resolution.resolution.complex.X n : Type u) (N : Type u))
    exact hT n
  have hcycles (n : ℕ) : IsNoetherian R (C.cycles n : Type u) := by
    let _ : IsNoetherian R (C.X n : Type u) :=
      isNoetherian_of_isNoetherianRing_of_finite R _
    apply isNoetherian_of_injective (R := R) (S := R) (C.iCycles n).hom
    exact (ModuleCat.mono_iff_injective _).mp inferInstance
  have hhomology (n : ℕ) : IsNoetherian R (C.homology n : Type u) := by
    let _ : IsNoetherian R (C.cycles n : Type u) := hcycles n
    apply isNoetherian_of_surjective (R := R) (S := R) (C.homologyπ n).hom
    apply LinearMap.range_eq_top.mpr
    exact (ModuleCat.epi_iff_surjective _).mp inferInstance
  let F : FreeResolution R M := Classical.choice (exists_free_resolution M)
  let α : ResolutionMap F.resolution Ff.resolution.resolution (𝟙 M) :=
    Classical.choice (resolution_map_exists F Ff.resolution.resolution (𝟙 M))
  let _ : IsIso (resolutionTorMap F Ff.resolution (𝟙 M) α N p) :=
    isIso_resolutionTorMap_of_isIso F Ff.resolution (𝟙 M) α N p
  have hsource : Module.Finite R (resolutionTor F N p : Type u) := by
    let _ : IsNoetherian R (resolutionTor Ff.resolution N p : Type u) := by
      change IsNoetherian R (C.homology p : Type u)
      exact hhomology p
    apply Module.Finite.of_injective (R := R) (S := R)
      (asIso (resolutionTorMap F Ff.resolution (𝟙 M) α N p)).hom.hom
    exact (ModuleCat.mono_iff_injective _).mp inferInstance
  unfold Tor
  change Module.Finite R (resolutionTor F N p : Type u)
  exact hsource

/-! ## Flatness and Tor -/

/-- The `i`th Tor functor in the second variable is zero on every module. -/
def TorFunctorZero {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) (i : ℕ) : Prop :=
  ∀ N : ModuleCat.{u} R, IsZero (Tor M N i)

/-- Vanishing of `Tor₁(M,R/I)` for all ideals. -/
def TorOneVanishingOnIdeals {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) : Prop :=
  ∀ I : Ideal R, IsZero (Tor M (ModuleCat.of R (R ⧸ I)) 1)

/-- Vanishing of `Tor₁(M,R/I)` for finitely generated ideals. -/
def TorOneVanishingOnFinitelyGeneratedIdeals {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) : Prop :=
  ∀ I : Ideal R, I.FG → IsZero (Tor M (ModuleCat.of R (R ⧸ I)) 1)

/-- The five equivalent flatness criteria stated in the source. -/
theorem flat_iff_tor_criteria {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) :
    List.TFAE [
      Module.Flat R M,
      ∀ i : ℕ, 0 < i → TorFunctorZero M i,
      TorFunctorZero M 1,
      TorOneVanishingOnIdeals M,
      TorOneVanishingOnFinitelyGeneratedIdeals M] := by
  have hflat_to_all :
      Module.Flat R M →
        ∀ i : ℕ, 0 < i → TorFunctorZero M i := by
    intro hflat i hi N
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    let G : FreeResolution R N :=
      Classical.choice (exists_free_resolution N)
    let K := tensorComplex G.complex M
    have hK : K.ExactAt (n + 1) := by
      apply (HomologicalComplex.exactAt_iff' (K := K) (j := n + 1)
        (i := n + 2) (k := n) (by simp) (by simp)).2
      dsimp [HomologicalComplex.sc', K, tensorComplex,
        HomologicalComplex.shortComplexFunctor']
      simp only [Nat.add_assoc]
      apply ModuleCat.shortComplex_exact
      have hex :
          Function.Exact (G.complex.d (n + 2) (n + 1)).hom
            (G.complex.d (n + 1) n).hom :=
        (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
          (ShortComplex.mk (G.complex.d (n + 2) (n + 1))
            (G.complex.d (n + 1) n) (G.complex.d_comp_d' (n + 2) (n + 1) n
              (by simp) (by simp)))).mp (G.resolution.exact_succ n)
      exact Module.Flat.rTensor_exact M hex
    have hz : IsZero (chainHomology K (n + 1)) := by
      exact hK.isZero_homology
    have hz' : IsZero (Tor N M (n + 1)) := by
      simpa [Tor, resolutionTor, K, G] using hz
    exact IsZero.of_iso hz' (torLeftRightIso M N (n + 1))
  have hflat_crit :
      Module.Flat R (M : Type u) ↔
        ∀ (I : Ideal R), I.FG →
          Function.Injective (I.subtype.rTensor (M : Type u)) :=
    (Formalization.Books.Algebra.Unit39.flat_criteria
      (R := R) (M := (M : Type u))).out 0 3
  have hfg_to_flat :
      TorOneVanishingOnFinitelyGeneratedIdeals M → Module.Flat R M := by
    intro hzero
    apply hflat_crit.mpr
    intro I hIFG
    let S : ShortComplex (ModuleCat.{u} R) :=
      ShortComplex.mk (ModuleCat.ofHom I.subtype)
        (ModuleCat.ofHom (Submodule.mkQ I)) (by
          apply ModuleCat.hom_ext
          ext x
          exact Ideal.Quotient.eq_zero_iff_mem.mpr x.property)
    have hS : S.ShortExact := by
      apply ModuleCat.shortComplex_shortExact
      · simpa [S] using (LinearMap.exact_subtype_mkQ I)
      · exact Subtype.val_injective
      · exact Submodule.mkQ_surjective I
    let hseq := Classical.choice (exists_tor_long_exact_sequence M S hS)
    have hzeroS : IsZero (Tor M S.X₃ 1) := by
      simpa [S] using hzero I hIFG
    have hconn : hseq.connecting = 0 := by
      have hc : ModuleCat.ofHom hseq.connecting = 0 :=
        hzeroS.eq_of_src _ _
      exact congrArg (fun f => f.hom) hc
    have hinj : Function.Injective (tensorByMap M S.f) :=
      (LinearMap.injective_iff_eq_zero_of_exact hseq.exact₃).2 hconn
    rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
    simpa [S, tensorByMap] using hinj
  have hone_to_flat :
      TorFunctorZero M 1 → Module.Flat R M := by
    intro h
    apply hfg_to_flat
    intro I hIFG
    change ∀ N : ModuleCat.{u} R, IsZero (Tor M N 1) at h
    exact h (ModuleCat.of R (R ⧸ I))
  have hideals_of_flat :
      Module.Flat R M → TorOneVanishingOnIdeals M := by
    intro h I
    have h' := hflat_to_all h 1 (by simp)
    change ∀ N : ModuleCat.{u} R, IsZero (Tor M N 1) at h'
    exact h' (ModuleCat.of R (R ⧸ I))
  have hfg_of_flat :
      Module.Flat R M → TorOneVanishingOnFinitelyGeneratedIdeals M := by
    intro h I hIFG
    exact hideals_of_flat h I
  tfae_have 1 ↔ 2 := by
    constructor
    · exact hflat_to_all
    · intro h
      apply hfg_to_flat
      intro I hIFG
      exact (h 1 (by simp)) (ModuleCat.of R (R ⧸ I))
  tfae_have 1 ↔ 3 := by
    constructor
    · intro h
      have h' := hflat_to_all h 1 (by simp)
      exact h'
    · exact hone_to_flat
  tfae_have 1 ↔ 4 := by
    constructor
    · exact hideals_of_flat
    · intro h
      apply hfg_to_flat
      intro I hIFG
      exact h I
  tfae_have 1 ↔ 5 := by
    constructor
    · exact hfg_of_flat
    · exact hfg_to_flat
  tfae_finish

/-- The canonical multiplication/action map `I ⊗ M → M`. -/
def idealTensorActionMap {R : Type u} [CommRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) :
    TensorProduct R I M →ₗ[R] M :=
  TensorProduct.lift
    { toFun := fun a =>
        { toFun := fun m => (a : R) • m
          map_add' := by intro m n; simp [smul_add]
          map_smul' := by intro r m; simp [smul_smul, mul_comm] }
      map_add' := by intro a b; ext m; simp [add_smul]
      map_smul' := by intro r a; ext m; simp [smul_smul] }

/-- The kernel module of `I ⊗ M → M`. -/
noncomputable def idealTensorActionKernel {R : Type u} [CommRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) : ModuleCat.{u} R :=
  ModuleCat.of R (LinearMap.ker (idealTensorActionMap I M))

/-- The ideal-quotient Tor group is the kernel of the action map. -/
theorem tor_one_ideal_quotient_kernel {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) (I : Ideal R) :
    Nonempty (Tor M (ModuleCat.of R (R ⧸ I)) 1 ≅
      idealTensorActionKernel I M) := by
  sorry

/- The switch map in the proof of symmetry can genuinely be nontrivial. -/
def tensorSwitch {k V : Type u} [CommRing k]
    [AddCommGroup V] [Module k V] :
    TensorProduct k V V ≃ₗ[k] TensorProduct k V V :=
  TensorProduct.comm k V V

theorem tensorSwitch_two_dimensional_not_identity {k : Type u} [Field k] :
    (tensorSwitch (k := k) (V := Fin 2 → k)).toLinearMap ≠ LinearMap.id := by
  intro h
  let x : Fin 2 → k := Pi.single 0 1
  let y : Fin 2 → k := Pi.single 1 1
  have h' := congrArg (fun f => f (x ⊗ₜ[k] y)) h
  have hne : x ⊗ₜ[k] y ≠ y ⊗ₜ[k] x := by
    intro hx
    let p0 : (Fin 2 → k) →ₗ[k] k := LinearMap.proj 0
    let p1 : (Fin 2 → k) →ₗ[k] k := LinearMap.proj 1
    let q := (TensorProduct.lid k k).toLinearMap.comp
      (TensorProduct.map p0 p1)
    have hq := congrArg q hx
    have h00 : p0 x = 1 := by simp [p0, x]
    have h11 : p1 y = 1 := by simp [p1, y]
    have h01 : p0 y = 0 := by simp [p0, y]
    have h10 : p1 x = 0 := by simp [p1, x]
    simp [q, h00, h11, h01, h10] at hq
  apply hne
  simpa [tensorSwitch, x, y] using h'.symm

private abbrev pairIndex (n : ℕ) := Fin n × Fin n
private abbrev upperIndex (n : ℕ) := {p : pairIndex n // p.1 ≤ p.2}
private abbrev strictIndex (n : ℕ) := {p : pairIndex n // p.1 < p.2}

private def pairSwapFun {k : Type u} [Semiring k] (n : ℕ)
    (x : pairIndex n → k) : pairIndex n → k :=
  fun p => x (p.2, p.1)

private def pairSwapMap {k : Type u} [Semiring k] (n : ℕ) :
    (pairIndex n → k) →ₗ[k] (pairIndex n → k) :=
  { toFun := pairSwapFun n
    map_add' := by
      intro x y
      funext p
      change (x + y) (p.2, p.1) = x (p.2, p.1) + y (p.2, p.1)
      rfl
    map_smul' := by
      intro r x
      funext p
      change (r • x) (p.2, p.1) = r • x (p.2, p.1)
      rfl }

private def symFun {k : Type u} [Semiring k] (n : ℕ) (a : upperIndex n → k)
    (p : pairIndex n) : k :=
  if h : p.1 ≤ p.2 then a ⟨p, h⟩ else a ⟨(p.2, p.1), le_of_not_ge h⟩

private def symMap {k : Type u} [Semiring k] (n : ℕ) :
    (upperIndex n → k) →ₗ[k] (pairIndex n → k) :=
  { toFun := symFun n
    map_add' := by
      intro a b
      funext p
      change symFun n (a + b) p = symFun n a p + symFun n b p
      by_cases h : p.1 ≤ p.2 <;> simp [symFun, h, Pi.add_apply]
    map_smul' := by
      intro r a
      funext p
      change symFun n (r • a) p = r • symFun n a p
      by_cases h : p.1 ≤ p.2 <;> simp [symFun, h, Pi.smul_apply] }

private def symPart {k : Type u} [Semiring k] (n : ℕ) :
    (pairIndex n → k) →ₗ[k] (upperIndex n → k) :=
  { toFun := fun x p => x p.1 + x (p.1.2, p.1.1)
    map_add' := by
      intro x y
      funext p
      change (x + y) p.1 + (x + y) (p.1.2, p.1.1) =
        (x p.1 + x (p.1.2, p.1.1)) + (y p.1 + y (p.1.2, p.1.1))
      simp [add_assoc, add_left_comm, add_comm]
    map_smul' := by
      intro r x
      funext p
      change (r • x) p.1 + (r • x) (p.1.2, p.1.1) =
        r • (x p.1 + x (p.1.2, p.1.1))
      simp [mul_add] }

private def symLiftFun {k : Type u} [Field k] (n : ℕ) (_hchar : (2 : k) ≠ 0)
    (a : upperIndex n → k) (p : pairIndex n) : k :=
  if h : p.1 ≤ p.2 then
    if p.1 < p.2 then a ⟨p, h⟩ else (2 : k)⁻¹ • a ⟨p, h⟩
  else 0

private def symLift {k : Type u} [Field k] (n : ℕ) (hchar : (2 : k) ≠ 0) :
    (upperIndex n → k) →ₗ[k] (pairIndex n → k) :=
  { toFun := symLiftFun n hchar
    map_add' := by
      intro a b
      funext p
      change symLiftFun n hchar (a + b) p =
        symLiftFun n hchar a p + symLiftFun n hchar b p
      by_cases h : p.1 ≤ p.2
      · by_cases hlt : p.1 < p.2
        · simp [symLiftFun, h, hlt, Pi.add_apply]
        · simp [symLiftFun, h, hlt, Pi.add_apply]
          ring
      · simp [symLiftFun, h]
    map_smul' := by
      intro r a
      funext p
      change symLiftFun n hchar (r • a) p = r • symLiftFun n hchar a p
      by_cases h : p.1 ≤ p.2
      · by_cases hlt : p.1 < p.2
        · simp [symLiftFun, h, hlt, Pi.smul_apply]
        · simp [symLiftFun, h, hlt, Pi.smul_apply]
          ring
      · simp [symLiftFun, h] }

private def antiFun {k : Type u} [Ring k] (n : ℕ) (a : strictIndex n → k)
    (p : pairIndex n) : k :=
  if h : p.1 < p.2 then a ⟨p, h⟩ else
    if h' : p.2 < p.1 then -a ⟨(p.2, p.1), h'⟩ else 0

private def antiMap {k : Type u} [Ring k] (n : ℕ) :
    (strictIndex n → k) →ₗ[k] (pairIndex n → k) :=
  { toFun := antiFun n
    map_add' := by
      intro a b
      funext p
      change antiFun n (a + b) p = antiFun n a p + antiFun n b p
      by_cases h : p.1 < p.2
      · simp [antiFun, h, Pi.add_apply]
      · by_cases h' : p.2 < p.1
        · simp [antiFun, h, h', Pi.add_apply]
          ac_rfl
        · simp [antiFun, h, h']
    map_smul' := by
      intro r a
      funext p
      change antiFun n (r • a) p = r • antiFun n a p
      by_cases h : p.1 < p.2
      · simp [antiFun, h, Pi.smul_apply]
      · by_cases h' : p.2 < p.1
        · simp [antiFun, h, h', Pi.smul_apply]
        · simp [antiFun, h, h'] }

private def antiPart {k : Type u} [Ring k] (n : ℕ) :
    (pairIndex n → k) →ₗ[k] (strictIndex n → k) :=
  { toFun := fun x p => x p.1 - x (p.1.2, p.1.1)
    map_add' := by
      intro x y
      funext p
      change (x + y) p.1 - (x + y) (p.1.2, p.1.1) =
        (x p.1 - x (p.1.2, p.1.1)) + (y p.1 - y (p.1.2, p.1.1))
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    map_smul' := by
      intro r x
      funext p
      change (r • x) p.1 - (r • x) (p.1.2, p.1.1) =
        r • (x p.1 - x (p.1.2, p.1.1))
      simp [sub_eq_add_neg, mul_add] }

private def antiLiftFun {k : Type u} [Field k] (n : ℕ) (_hchar : (2 : k) ≠ 0)
    (a : strictIndex n → k) (p : pairIndex n) : k :=
  if h : p.1 < p.2 then (2 : k)⁻¹ • a ⟨p, h⟩ else
    if h' : p.2 < p.1 then -(2 : k)⁻¹ • a ⟨(p.2, p.1), h'⟩ else 0

private def antiLift {k : Type u} [Field k] (n : ℕ) (hchar : (2 : k) ≠ 0) :
    (strictIndex n → k) →ₗ[k] (pairIndex n → k) :=
  { toFun := antiLiftFun n hchar
    map_add' := by
      intro a b
      funext p
      change antiLiftFun n hchar (a + b) p =
        antiLiftFun n hchar a p + antiLiftFun n hchar b p
      by_cases h : p.1 < p.2
      · simp [antiLiftFun, h, Pi.add_apply]
        ring
      · by_cases h' : p.2 < p.1
        · simp [antiLiftFun, h, h', Pi.add_apply]
          ring
        · simp [antiLiftFun, h, h']
    map_smul' := by
      intro r a
      funext p
      change antiLiftFun n hchar (r • a) p = r • antiLiftFun n hchar a p
      by_cases h : p.1 < p.2
      · simp [antiLiftFun, h, Pi.smul_apply]
        ring
      · by_cases h' : p.2 < p.1
        · simp [antiLiftFun, h, h', Pi.smul_apply]
          ring
        · simp [antiLiftFun, h, h'] }

private lemma sum_fin_sub (n : ℕ) :
    (∑ i : Fin n, (n - (i : ℕ))) = n * (n + 1) / 2 := by
  have hsum : (∑ i : Fin n, (n - (i : ℕ))) =
      Finset.sum (Finset.range n) (fun i => n - i) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    have hil : i < n := Finset.mem_range.mp hi
    simp [hil]
  rw [hsum]
  calc
    Finset.sum (Finset.range n) (fun i => n - i) =
        Finset.sum (Finset.range n) (fun i => 1 + (n - 1 - i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hil : i < n := Finset.mem_range.mp hi
      omega
    _ = n + Finset.sum (Finset.range n) (fun i => n - 1 - i) := by
      rw [Finset.sum_add_distrib]
      simp
    _ = n + Finset.sum (Finset.range n) (fun i => i) := by
      exact congrArg (fun x => n + x) (Finset.sum_range_reflect (fun i => i) n)
    _ = n * (n + 1) / 2 := by
      rw [Finset.sum_range_id]
      have hdiv : 2 ∣ n * (n - 1) := (Nat.even_mul_pred_self n).two_dvd
      have hdiv' : 2 ∣ n * (n + 1) := (Nat.even_mul_succ_self n).two_dvd
      symm
      rw [Nat.div_eq_iff_eq_mul_left (by decide) hdiv']
      have hmul := Nat.mul_div_cancel' hdiv
      have hiden : n * (n + 1) = n * (n - 1) + 2 * n := by
        cases n with
        | zero => simp
        | succ n => simp; ring
      calc
        n * (n + 1) = n * (n - 1) + 2 * n := hiden
        _ = 2 * n + n * (n - 1) := by ac_rfl
        _ = 2 * n + 2 * (n * (n - 1) / 2) := by rw [hmul]
        _ = (n + n * (n - 1) / 2) * 2 := by
          rw [Nat.add_mul, Nat.mul_comm n 2]
          simp [mul_comm]

private theorem pair_plus_finrank {k : Type u} [Field k] (n : ℕ) (hchar : (2 : k) ≠ 0) :
    Module.finrank k
        (Module.End.eigenspace (pairSwapMap (k := k) n) (1 : k)) =
      n * (n + 1) / 2 := by
  let s := LinearMap.id + pairSwapMap (k := k) n
  let e := symMap (k := k) n
  have hsr : LinearMap.range s = LinearMap.range e := by
    let q := symPart (k := k) n
    let r := symLift (k := k) n hchar
    have hse : s = e.comp q := by
      ext x p
      by_cases h : p.1 ≤ p.2
      · simp [s, e, q, pairSwapMap, pairSwapFun, symMap, symFun, symPart, h]
      · have h' : p.2 ≤ p.1 := le_of_not_ge h
        simp [s, e, q, pairSwapMap, pairSwapFun, symMap, symFun, symPart, h, add_comm]
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact ⟨q x, by
        have hx := congrArg (fun f => f x) hse
        simpa [s, e, q] using hx.symm⟩
    · rintro _ ⟨a, rfl⟩
      refine ⟨r a, ?_⟩
      ext p
      rcases p with ⟨i, j⟩
      by_cases h : i ≤ j
      · by_cases hlt : i < j
        · have h' : ¬j ≤ i := not_le_of_gt hlt
          simp [s, r, e, pairSwapMap, pairSwapFun, symMap, symFun, symLift,
            symLiftFun, h, hlt, h']
        · have heq : i = j := le_antisymm h (le_of_not_gt hlt)
          subst j
          simp [s, r, e, pairSwapMap, pairSwapFun, symMap, symFun, symLift,
            symLiftFun]
          field_simp
          ring
      · have h' : j ≤ i := le_of_not_ge h
        simp [s, r, e, pairSwapMap, pairSwapFun, symMap, symFun, symLift,
          symLiftFun, h, h']
  have heinj : Function.Injective e := by
    intro a b hab
    funext p
    have hp := congrArg (fun x => x p) hab
    simpa [e, symMap, symFun, p.property] using hp
  have hseig : LinearMap.range s =
      Module.End.eigenspace (pairSwapMap (k := k) n) (1 : k) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      apply Module.End.mem_eigenspace_iff.mpr
      simp [s, pairSwapMap, add_comm]
      funext p
      simp [pairSwapFun, add_comm]
    · intro x hx
      refine ⟨(2 : k)⁻¹ • x, ?_⟩
      have hx' := Module.End.mem_eigenspace_iff.mp hx
      have hx'' : pairSwapFun n x = x := by
        simpa [pairSwapMap] using hx'
      simp [s, pairSwapMap, hx'', smul_add]
      ext p
      simp [smul_eq_mul]
      field_simp [hchar]
      ring
  rw [← hseig, hsr, LinearMap.finrank_range_of_inj heinj, Module.finrank_pi]
  rw [Fintype.card_congr (by
    let ec : upperIndex n ≃ Σ i : Fin n, {j : Fin n // i ≤ j} :=
      { toFun := fun p => ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
        invFun := fun q => ⟨(q.1, q.2.1), q.2.2⟩
        left_inv := by intro p; rfl
        right_inv := by intro q; rfl }
    exact ec), Fintype.card_sigma]
  have hci (i : Fin n) : Fintype.card {j : Fin n // i ≤ j} = n - (i : ℕ) := by
    rw [Fintype.card_subtype]
    have heq : (Finset.filter (fun x : Fin n => i ≤ x) Finset.univ) =
        Finset.Ici i := by
      ext x
      simp
    rw [heq]
    exact Fin.card_Ici i
  simp_rw [hci]
  exact sum_fin_sub n

private theorem pair_minus_finrank {k : Type u} [Field k] (n : ℕ) (hchar : (2 : k) ≠ 0) :
    Module.finrank k
        (Module.End.eigenspace (pairSwapMap (k := k) n) (-1 : k)) =
      n * (n - 1) / 2 := by
  let e := antiMap (k := k) n
  have heinj : Function.Injective e := by
    intro a b hab
    funext p
    have hp := congrArg (fun x => x p.1) hab
    simpa [e, antiMap, antiFun, p.property] using hp
  have hde : LinearMap.range (LinearMap.id - pairSwapMap (k := k) n) =
      LinearMap.range e := by
    exact (show LinearMap.range (LinearMap.id - pairSwapMap (k := k) n) =
        LinearMap.range (antiMap (k := k) n) from by
      let d := LinearMap.id - pairSwapMap (k := k) n
      let q := antiPart (k := k) n
      let r := antiLift (k := k) n hchar
      have hde' : d = e.comp q := by
        ext x p
        rcases p with ⟨i, j⟩
        by_cases h : i < j
        · simp [d, e, q, pairSwapMap, pairSwapFun, antiMap, antiFun, antiPart, h]
        · by_cases h' : j < i
          · simp [d, e, q, pairSwapMap, pairSwapFun, antiMap, antiFun, antiPart, h, h',
              sub_eq_add_neg]
          · have heq : i = j := le_antisymm (le_of_not_gt h') (le_of_not_gt h)
            subst j
            simp [d, e, q, pairSwapMap, pairSwapFun, antiMap, antiFun, antiPart]
      apply le_antisymm
      · rintro _ ⟨x, rfl⟩
        exact ⟨q x, by
          have hx := congrArg (fun f => f x) hde'
          simpa [d, e, q] using hx.symm⟩
      · rintro _ ⟨a, rfl⟩
        refine ⟨r a, ?_⟩
        ext p
        rcases p with ⟨i, j⟩
        by_cases h : i < j
        · have h' : ¬j < i := not_lt_of_ge (le_of_lt h)
          simp [r, pairSwapMap, pairSwapFun, antiMap, antiFun, antiLift,
            antiLiftFun, h, h']
          field_simp [hchar]
          ring
        · by_cases h' : j < i
          · simp [r, pairSwapMap, pairSwapFun, antiMap, antiFun, antiLift,
              antiLiftFun, h, h']
            field_simp [hchar]
            ring
          · have heq : i = j := le_antisymm (le_of_not_gt h') (le_of_not_gt h)
            subst j
            simp [r, pairSwapMap, pairSwapFun, antiMap, antiFun, antiLift, antiLiftFun]
      )
  have hseig : LinearMap.range (LinearMap.id - pairSwapMap (k := k) n) =
      Module.End.eigenspace (pairSwapMap (k := k) n) (-1 : k) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      apply Module.End.mem_eigenspace_iff.mpr
      simp [LinearMap.id, pairSwapMap]
      funext p
      simp [pairSwapFun]
    · intro x hx
      refine ⟨(2 : k)⁻¹ • x, ?_⟩
      have hx' := Module.End.mem_eigenspace_iff.mp hx
      have hx'' : pairSwapFun n x = -x := by
        simpa [pairSwapMap] using hx'
      simp [LinearMap.id, pairSwapMap, hx'']
      ext p
      simp [smul_eq_mul]
      field_simp [hchar]
      ring
  rw [← hseig, hde, LinearMap.finrank_range_of_inj heinj, Module.finrank_pi]
  rw [Fintype.card_congr (by
    let ec : strictIndex n ≃ Σ i : Fin n, {j : Fin n // i < j} :=
      { toFun := fun p => ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
        invFun := fun q => ⟨(q.1, q.2.1), q.2.2⟩
        left_inv := by intro p; rfl
        right_inv := by intro q; rfl }
    exact ec), Fintype.card_sigma]
  have hci (i : Fin n) : Fintype.card {j : Fin n // i < j} = n - (i : ℕ) - 1 := by
    rw [Fintype.card_subtype]
    have heq : (Finset.filter (fun x : Fin n => i < x) Finset.univ) =
        Finset.Ioi i := by
      ext x
      simp
    rw [heq]
    calc
      (Finset.Ioi i).card = n - 1 - (i : ℕ) := Fin.card_Ioi i
      _ = n - (i : ℕ) - 1 := by omega
  simp_rw [hci]
  have hsum : (∑ i : Fin n, (n - (i : ℕ) - 1)) =
      n * (n - 1) / 2 := by
    have hsum' : (∑ i : Fin n, (n - (i : ℕ) - 1)) =
        Finset.sum (Finset.range n) (fun i => n - i - 1) := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      have hil : i < n := Finset.mem_range.mp hi
      simp [hil]
    rw [hsum']
    calc
      Finset.sum (Finset.range n) (fun i => n - i - 1) =
          Finset.sum (Finset.range n) (fun i => n - 1 - i) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hil : i < n := Finset.mem_range.mp hi
        omega
      _ = Finset.sum (Finset.range n) (fun i => i) :=
        Finset.sum_range_reflect (fun i => i) n
      _ = n * (n - 1) / 2 := Finset.sum_range_id n
  exact hsum

/- The source's eigenvalue count is recorded as eigenspace dimensions when
the two eigenvalues are distinct. -/
theorem tensorSwitch_eigenspace_finrank {k : Type u} [Field k]
    (hchar : (2 : k) ≠ 0) (n : ℕ) :
    Module.finrank k
          (Module.End.eigenspace
            (tensorSwitch (k := k) (V := Fin n → k)).toLinearMap (1 : k)) =
        n * (n + 1) / 2 ∧
      Module.finrank k
          (Module.End.eigenspace
            (tensorSwitch (k := k) (V := Fin n → k)).toLinearMap (-1 : k)) =
        n * (n - 1) / 2 := by
  change Module.finrank k
          (Module.End.eigenspace
            (TensorProduct.comm k (Fin n → k) (Fin n → k)).toLinearMap (1 : k)) =
        n * (n + 1) / 2 ∧
      Module.finrank k
          (Module.End.eigenspace
            (TensorProduct.comm k (Fin n → k) (Fin n → k)).toLinearMap (-1 : k)) =
        n * (n - 1) / 2
  let b := Pi.basisFun k (Fin n)
  let bt := b.tensorProduct b
  let e := bt.equivFun
  have hcoord (x : TensorProduct k (Fin n → k) (Fin n → k)) :
      e ((TensorProduct.comm k (Fin n → k) (Fin n → k)) x) =
        pairSwapFun n (e x) := by
    have hm := TensorProduct.toMatrix_comm b b
    ext p
    change bt.repr ((TensorProduct.comm k (Fin n → k) (Fin n → k)) x) p =
      bt.repr x (p.2, p.1)
    have hv := LinearMap.toMatrix_mulVec_repr bt bt
      ((TensorProduct.comm k (Fin n → k) (Fin n → k)).toLinearMap) x
    have hp := congrArg (fun f => f p) hv
    calc
      bt.repr ((TensorProduct.comm k (Fin n → k) (Fin n → k)) x) p =
          ((LinearMap.toMatrix bt bt)
            (TensorProduct.comm k (Fin n → k) (Fin n → k)).toLinearMap).mulVec
              (bt.repr x) p := hp.symm
      _ = (bt.repr x) (p.2, p.1) := by
        rw [hm]
        simp [Matrix.mulVec, dotProduct, Matrix.submatrix, Matrix.one_apply, Prod.swap]
  let Eplus := Module.End.eigenspace
    (TensorProduct.comm k (Fin n → k) (Fin n → k)).toLinearMap (1 : k)
  let Pplus := Module.End.eigenspace (pairSwapMap (k := k) n) (1 : k)
  let eeplus : Eplus ≃ₗ[k] Pplus :=
    { toFun := fun x =>
        ⟨e x, by
          apply Module.End.mem_eigenspace_iff.mpr
          have hx := Module.End.mem_eigenspace_iff.mp x.property
          have hs : pairSwapFun n (e x) = e x := by
            calc
              pairSwapFun n (e x) = e ((TensorProduct.comm k (Fin n → k) (Fin n → k)) x) :=
                hcoord x |>.symm
              _ = e ((1 : k) • x) := by
                exact congrArg e hx
              _ = e x := by simp
          simp [pairSwapMap, hs]⟩
      invFun := fun y =>
        ⟨e.symm y, by
          apply Module.End.mem_eigenspace_iff.mpr
          apply e.injective
          have hy := Module.End.mem_eigenspace_iff.mp y.property
          have hc := hcoord (e.symm y)
          calc
            e ((TensorProduct.comm k (Fin n → k) (Fin n → k)) (e.symm y)) =
                pairSwapFun n y := by simpa using hc
            _ = (1 : k) • y := by simpa [pairSwapMap] using hy
            _ = e ((1 : k) • e.symm y) := by simp⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact e.symm_apply_apply x
      right_inv := by
        intro y
        apply Subtype.ext
        exact e.apply_symm_apply y
      map_add' := by
        intro x y
        apply Subtype.ext
        simp
      map_smul' := by
        intro r x
        apply Subtype.ext
        simp }
  let Eminus := Module.End.eigenspace
    (TensorProduct.comm k (Fin n → k) (Fin n → k)).toLinearMap (-1 : k)
  let Pminus := Module.End.eigenspace (pairSwapMap (k := k) n) (-1 : k)
  let eeminus : Eminus ≃ₗ[k] Pminus :=
    { toFun := fun x =>
        ⟨e x, by
          apply Module.End.mem_eigenspace_iff.mpr
          have hx := Module.End.mem_eigenspace_iff.mp x.property
          have hs : pairSwapFun n (e x) = -e x := by
            calc
              pairSwapFun n (e x) = e ((TensorProduct.comm k (Fin n → k) (Fin n → k)) x) :=
                hcoord x |>.symm
              _ = e ((-1 : k) • x) := by
                congr 1
              _ = -e x := by simp
          simp [pairSwapMap, hs]⟩
      invFun := fun y =>
        ⟨e.symm y, by
          apply Module.End.mem_eigenspace_iff.mpr
          apply e.injective
          have hy := Module.End.mem_eigenspace_iff.mp y.property
          have hc := hcoord (e.symm y)
          calc
            e ((TensorProduct.comm k (Fin n → k) (Fin n → k)) (e.symm y)) =
                pairSwapFun n y := by simpa using hc
            _ = (-1 : k) • y := by simpa [pairSwapMap] using hy
            _ = e ((-1 : k) • e.symm y) := by simp⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact e.symm_apply_apply x
      right_inv := by
        intro y
        apply Subtype.ext
        exact e.apply_symm_apply y
      map_add' := by
        intro x y
        apply Subtype.ext
        simp
      map_smul' := by
        intro r x
        apply Subtype.ext
        simp }
  constructor
  · change Module.finrank k Eplus = n * (n + 1) / 2
    rw [eeplus.finrank_eq]
    simpa [Pplus] using pair_plus_finrank n hchar
  · change Module.finrank k Eminus = n * (n - 1) / 2
    rw [eeminus.finrank_eq]
    simpa [Pminus] using pair_minus_finrank n hchar

/- In characteristic two, the switch is not diagonalizable; semisimplicity is
the canonical Mathlib interface for this finite-dimensional assertion. -/
theorem tensorSwitch_two_dimensional_charTwo_not_semisimple
    {k : Type u} [Field k] [CharP k 2] :
    ¬ Module.End.IsSemisimple
        (tensorSwitch (k := k) (V := Fin 2 → k)).toLinearMap := by
  intro hs
  let T := TensorProduct k (Fin 2 → k) (Fin 2 → k)
  let f : Module.End k T :=
    (tensorSwitch (k := k) (V := Fin 2 → k)).toLinearMap
  have hone : algebraMap k (Module.End k T) 1 = LinearMap.id := by
    ext z
    simp [Module.End.one_eq_id]
  have hf2 : f.comp f = LinearMap.id := by
    ext z
    simp [f, tensorSwitch, T, LinearMap.comp_apply]
  have hnil : IsNilpotent (f - algebraMap k (Module.End k T) 1) := by
    rw [hone]
    refine ⟨2, ?_⟩
    change (f - LinearMap.id).comp (f - LinearMap.id) = 0
    have hexpand :
        (f - LinearMap.id).comp (f - LinearMap.id) =
          (LinearMap.id : Module.End k T) + LinearMap.id - (f + f) := by
      rw [LinearMap.comp_sub, LinearMap.sub_comp, LinearMap.comp_id,
        LinearMap.id_comp, hf2]
      abel
    rw [hexpand]
    have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
    have hff : f + f = (0 : Module.End k T) := by
      calc
        f + f = (2 : k) • f := (two_smul k f).symm
        _ = 0 := by rw [htwo, zero_smul]
    have hid : (LinearMap.id : Module.End k T) + LinearMap.id = 0 := by
      calc
        (LinearMap.id : Module.End k T) + LinearMap.id =
            (2 : k) • LinearMap.id := (two_smul k _).symm
        _ = 0 := by rw [htwo, zero_smul]
    rw [hff, hid]
    exact sub_self (0 : Module.End k T)
  have hsub : (f - algebraMap k (Module.End k T) 1).IsSemisimple :=
    (Module.End.isSemisimple_sub_algebraMap_iff (f := f) (μ := (1 : k))).mpr hs
  have hzero := Module.End.eq_zero_of_isNilpotent_isSemisimple hnil hsub
  rw [hone] at hzero
  apply (tensorSwitch_two_dimensional_not_identity (k := k))
  simpa [f, T] using sub_eq_zero.mp hzero

theorem neg_tensorSwitch_two_dimensional_not_identity
    {k : Type u} [Field k] :
    -(tensorSwitch (k := k) (V := Fin 2 → k)).toLinearMap ≠ LinearMap.id := by
  intro h
  let x : Fin 2 → k := Pi.single 0 1
  let y : Fin 2 → k := Pi.single 1 1
  have h' := congrArg (fun f => f (x ⊗ₜ[k] y)) h
  let p0 : (Fin 2 → k) →ₗ[k] k := LinearMap.proj 0
  let p1 : (Fin 2 → k) →ₗ[k] k := LinearMap.proj 1
  let q := (TensorProduct.lid k k).toLinearMap.comp
    (TensorProduct.map p0 p1)
  have hq := congrArg q h'
  simp [tensorSwitch, q, p0, p1, x, y] at hq

end

end Formalization.Books.Algebra.Unit75
