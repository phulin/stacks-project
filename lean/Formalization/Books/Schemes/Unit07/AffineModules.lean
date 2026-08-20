import Formalization.Books.Schemes.Unit05
import Formalization.Books.Schemes.Unit06
import Formalization.Books.Modules.Unit16.TensorProduct
import Formalization.Books.Modules.Unit21.SymmetricExterior
import Formalization.Books.Modules.Unit22.InternalHom
import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
import Mathlib.Algebra.Module.FinitePresentation

/-!
# Schemes, Chapter 7: Quasi-coherent sheaves on affines

This file records the source-ordered interfaces for the eight numbered results in the
chapter.  The affine module sheaf and global-sections constructions are Mathlib's `tilde`
adjunction; tensor products, powers, and internal Homs reuse the earlier Modules chapters.
The theorem proofs are intentionally deferred to the proof stage.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry TensorProduct

namespace Formalization.Books.Schemes.Unit07

universe u

/-! ## 7.1. Comparing the two constructions of an associated module sheaf -/

/-- The affine scheme used throughout this chapter for a commutative ring `R`. -/
abbrev affineScheme (R : Type u) [CommRing R] : Scheme.{u} :=
  AlgebraicGeometry.Spec (CommRingCat.of R)

/-- The canonical `R`-module sheaf associated to a bundled `R`-module. -/
noncomputable def affineTilde {R : Type u} [CommRing R]
    (M : ModuleCat (CommRingCat.of R)) : (affineScheme R).Modules :=
  AlgebraicGeometry.tilde M

/-- The source-facing associated module sheaf for an unbundled module. -/
noncomputable def affineModuleSheaf (R M : Type u) [CommRing R]
    [AddCommGroup M] [Module R M] : (affineScheme R).Modules :=
  affineTilde (ModuleCat.of (CommRingCat.of R) M)

/-- The global-sections module of a sheaf on an affine scheme. -/
noncomputable def affineGlobalSections {R : Type u} [CommRing R]
    (F : (affineScheme R).Modules) : ModuleCat (CommRingCat.of R) :=
  (AlgebraicGeometry.moduleSpecΓFunctor (R := CommRingCat.of R)).obj F

/-- The associated-sheaf functor `M ↦ M̃`. -/
abbrev affineModuleSheafFunctor (R : Type u) [CommRing R] :
    ModuleCat (CommRingCat.of R) ⥤ (affineScheme R).Modules :=
  Formalization.Books.Schemes.Unit05.associatedModuleFunctor R

/-- The chapter's `𝓕_M` is the canonical Mathlib `M̃` construction. -/
abbrev affineAssociatedModuleSheaf {R : Type u} [CommRing R]
    (M : ModuleCat (CommRingCat.of R)) : (affineScheme R).Modules :=
  affineTilde M

/-- The comparison isomorphism between the two associated-module-sheaf constructions. -/
noncomputable def affineModuleSheafComparison {R : Type u} [CommRing R]
    (M : ModuleCat (CommRingCat.of R)) :
    affineTilde M ≅ affineAssociatedModuleSheaf M :=
  Iso.refl _

theorem affineTilde_isQuasicoherent {R : Type u} [CommRing R]
    (M : ModuleCat (CommRingCat.of R)) :
    (affineTilde M).IsQuasicoherent := by
  change (AlgebraicGeometry.tilde M).IsQuasicoherent
  infer_instance

noncomputable def affineTilde_hom_equiv {R : Type u} [CommRing R]
    (M : ModuleCat (CommRingCat.of R)) (F : (affineScheme R).Modules) :
    (affineTilde M ⟶ F) ≃ (M ⟶ affineGlobalSections F) := by
  exact (AlgebraicGeometry.tilde.adjunction (R := CommRingCat.of R)).homEquiv _ _

theorem affineModuleSheafFunctor_map {R : Type u} [CommRing R]
    {M N : ModuleCat (CommRingCat.of R)} (f : M ⟶ N) :
    (affineModuleSheafFunctor R).map f = AlgebraicGeometry.tilde.map f := rfl

/-! ## 7.2. Tensor constructions, powers, and internal Hom -/

private abbrev affineStructureSheaf (R : Type u) [CommRing R] :
    Formalization.Books.Sheaves.Unit17.CommRingSheaf (PrimeSpectrum.Top R) :=
  AlgebraicGeometry.Spec.structureSheaf (CommRingCat.of R)

/-- The tensor product of two affine module sheaves, using the earlier Modules construction. -/
noncomputable def affineTensorProductSheaf {R : Type u} [CommRing R]
    (M N : ModuleCat (CommRingCat.of R)) : (affineScheme R).Modules :=
  Formalization.Books.Modules.Unit16.tensorProductSheaf (affineStructureSheaf R)
    (affineTilde M) (affineTilde N)

theorem affineTilde_tensor_iso_exists {R : Type u} [CommRing R]
    (M N : ModuleCat (CommRingCat.of R)) :
    Nonempty (affineTilde (M ⊗ N) ≅
      affineTensorProductSheaf M N) := by
  sorry

noncomputable def affineTilde_tensor_iso {R : Type u} [CommRing R]
    (M N : ModuleCat (CommRingCat.of R)) :
    affineTilde (M ⊗ N) ≅
      affineTensorProductSheaf M N :=
  Classical.choice (affineTilde_tensor_iso_exists M N)

/-- The degree-`n` tensor power of an affine module sheaf. -/
noncomputable def affineTensorPowerSheaf {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (n : ℕ) : (affineScheme R).Modules :=
  affineModuleSheaf R (Formalization.Books.Algebra.Unit13.tensorPower R M n)

/-- The degree-`n` symmetric power of an affine module sheaf. -/
noncomputable def affineSymmetricPowerSheaf {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (n : ℕ) : (affineScheme R).Modules :=
  affineModuleSheaf R (Formalization.Books.Algebra.Unit13.symmetricPower R M n)

/-- The degree-`n` exterior power of an affine module sheaf. -/
noncomputable def affineExteriorPowerSheaf {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (n : ℕ) : (affineScheme R).Modules :=
  affineModuleSheaf R (Formalization.Books.Algebra.Unit13.exteriorPower R M n)

theorem affineTilde_tensorPower_iso_exists {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (n : ℕ) :
    Nonempty (affineTensorPowerSheaf (R := R) (M := M) n ≅
      Formalization.Books.Modules.Unit21.tensorPowerSheaf (affineStructureSheaf R)
      (affineTilde (ModuleCat.of (CommRingCat.of R) M)) n) := by
  sorry

noncomputable def affineTilde_tensorPower_iso {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (n : ℕ) :
    affineTensorPowerSheaf (R := R) (M := M) n ≅
      Formalization.Books.Modules.Unit21.tensorPowerSheaf (affineStructureSheaf R)
        (affineTilde (ModuleCat.of (CommRingCat.of R) M)) n :=
  Classical.choice (affineTilde_tensorPower_iso_exists n)

theorem affineTilde_symmetricPower_iso_exists {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (n : ℕ) :
    Nonempty (affineSymmetricPowerSheaf (R := R) (M := M) n ≅
      Formalization.Books.Modules.Unit21.symmetricPowerSheaf (affineStructureSheaf R)
        (affineTilde (ModuleCat.of (CommRingCat.of R) M)) n) := by
  sorry

noncomputable def affineTilde_symmetricPower_iso {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (n : ℕ) :
    affineSymmetricPowerSheaf (R := R) (M := M) n ≅
      Formalization.Books.Modules.Unit21.symmetricPowerSheaf (affineStructureSheaf R)
        (affineTilde (ModuleCat.of (CommRingCat.of R) M)) n :=
  Classical.choice (affineTilde_symmetricPower_iso_exists n)

theorem affineTilde_exteriorPower_iso_exists {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (n : ℕ) :
    Nonempty (affineExteriorPowerSheaf (R := R) (M := M) n ≅
      Formalization.Books.Modules.Unit21.exteriorPowerSheaf (affineStructureSheaf R)
        (affineTilde (ModuleCat.of (CommRingCat.of R) M)) n) := by
  sorry

noncomputable def affineTilde_exteriorPower_iso {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (n : ℕ) :
    affineExteriorPowerSheaf (R := R) (M := M) n ≅
      Formalization.Books.Modules.Unit21.exteriorPowerSheaf (affineStructureSheaf R)
        (affineTilde (ModuleCat.of (CommRingCat.of R) M)) n :=
  Classical.choice (affineTilde_exteriorPower_iso_exists n)

theorem affineTilde_internalHom_iso_exists {R : Type u} [CommRing R]
    (M N : ModuleCat (CommRingCat.of R))
    (hM : Module.FinitePresentation R (M : Type u)) :
    Nonempty (affineTilde (ModuleCat.of (CommRingCat.of R) (M ⟶ N)) ≅
      Formalization.Books.Modules.Unit22.internalHom (affineStructureSheaf R)
        (affineTilde M) (affineTilde N)) := by
  sorry

noncomputable def affineTilde_internalHom_iso {R : Type u} [CommRing R]
    (M N : ModuleCat (CommRingCat.of R))
    (hM : Module.FinitePresentation R (M : Type u)) :
    affineTilde (ModuleCat.of (CommRingCat.of R) (M ⟶ N)) ≅
      Formalization.Books.Modules.Unit22.internalHom (affineStructureSheaf R)
        (affineTilde M) (affineTilde N) :=
  Classical.choice (affineTilde_internalHom_iso_exists M N hM)

/-! ## 7.3. Pullback and pushforward for affine morphisms -/

/-- The affine scheme morphism induced by an `R`-algebra structure on `S`. -/
noncomputable def affineSchemeMapOfAlgebra (R S : Type u)
    [CommRing R] [CommRing S] [Algebra R S] :
    affineScheme S ⟶ affineScheme R :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R S))

/-- Pullback of module sheaves along the affine morphism `Spec S → Spec R`. -/
noncomputable def affinePullbackFunctor (R S : Type u)
    [CommRing R] [CommRing S] [Algebra R S] :
    (affineScheme R).Modules ⥤ (affineScheme S).Modules :=
  AlgebraicGeometry.Scheme.Modules.pullback (affineSchemeMapOfAlgebra R S)

/-- Pushforward of module sheaves along the affine morphism `Spec S → Spec R`. -/
noncomputable def affinePushforwardFunctor (R S : Type u)
    [CommRing R] [CommRing S] [Algebra R S] :
    (affineScheme S).Modules ⥤ (affineScheme R).Modules :=
  AlgebraicGeometry.Scheme.Modules.pushforward (affineSchemeMapOfAlgebra R S)

/-- Restriction of scalars along `R → S`, bundled as an `R`-module. -/
noncomputable def restrictScalarsModule (R S : Type u)
    [CommRing R] [CommRing S] [Algebra R S]
    (N : ModuleCat (CommRingCat.of S)) : ModuleCat (CommRingCat.of R) :=
  (ModuleCat.restrictScalars (algebraMap R S)).obj N

/-- The module on the source side of affine pullback. -/
noncomputable def affineBaseChangeModule (R S : Type u)
    [CommRing R] [CommRing S] [Algebra R S]
    (M : ModuleCat (CommRingCat.of R)) : ModuleCat (CommRingCat.of S) :=
  ModuleCat.of (CommRingCat.of S) (S ⊗[R] (M : Type u))

theorem affine_pullback_tilde_iso_exists (R S : Type u)
    [CommRing R] [CommRing S] [Algebra R S]
    (M : ModuleCat (CommRingCat.of R)) :
    Nonempty ((affinePullbackFunctor R S).obj (affineTilde M) ≅
      affineTilde (affineBaseChangeModule R S M)) := by
  sorry

theorem affine_pushforward_tilde_iso_exists (R S : Type u)
    [CommRing R] [CommRing S] [Algebra R S]
    (N : ModuleCat (CommRingCat.of S)) :
    Nonempty ((affinePushforwardFunctor R S).obj (affineTilde N) ≅
      affineTilde (restrictScalarsModule R S N)) := by
  sorry

/- The standard-open restriction is the localization statement used repeatedly after this
lemma.  The target is expressed by Mathlib's `IsLocalizedModule` interface rather than by
duplicating a second sheaf construction for `D(f)`. -/
theorem affineTilde_basicOpen_isLocalized {R : Type u} [CommRing R]
    (M : ModuleCat (CommRingCat.of R)) (f : R) :
    IsLocalizedModule.Away f
      (AlgebraicGeometry.tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom := by
  sorry

/-! ## 7.4. Every quasi-coherent sheaf on an affine is associated to global sections -/

theorem affine_quasiCoherent_iff_tilde_globalSections {R : Type u} [CommRing R]
    (F : (affineScheme R).Modules) :
    F.IsQuasicoherent ↔
    IsIso (AlgebraicGeometry.Scheme.Modules.fromTildeΓ (R := CommRingCat.of R) F) := by
  exact AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ F

theorem affine_quasiCoherent_is_associated_to_globalSections {R : Type u} [CommRing R]
    (F : (affineScheme R).Modules) [F.IsQuasicoherent] :
    Nonempty (affineTilde (affineGlobalSections F) ≅ F) := by
  sorry

/-! ## 7.5. The equivalence between modules and quasi-coherent sheaves -/

noncomputable def affineQuasiCoherentEquivalence (R : Type u) [CommRing R] :
  ModuleCat (CommRingCat.of R) ≌
      (SheafOfModules.isQuasicoherent (affineScheme R).ringCatSheaf).FullSubcategory :=
  AlgebraicGeometry.tildeEquiv (R := CommRingCat.of R)

/-! ## 7.6. Kernels and cokernels -/

theorem affine_tilde_preserves_exact {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat (CommRingCat.of R))) (hS : S.Exact) :
    (S.map (affineModuleSheafFunctor R)).Exact := by
  exact Formalization.Books.Schemes.Unit05.associatedModuleFunctor_exact S hS

theorem affine_kernel_isQuasicoherent {R : Type u} [CommRing R]
    {F G : (affineScheme R).Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (f : F ⟶ G) : (kernel f).IsQuasicoherent := by
  sorry

theorem affine_cokernel_isQuasicoherent {R : Type u} [CommRing R]
    {F G : (affineScheme R).Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (f : F ⟶ G) : (cokernel f).IsQuasicoherent := by
  sorry

/-! ## 7.7. Direct sums and colimits -/

noncomputable def affineColimit {R : Type u} [CommRing R]
    {J : Type u} [Category.{u} J] (D : J ⥤ (affineScheme R).Modules) :
    (affineScheme R).Modules :=
  colimit D

noncomputable def affineDirectSum {R : Type u} [CommRing R]
    {ι : Type u} (F : ι → (affineScheme R).Modules) :
    (affineScheme R).Modules :=
  colimit (Discrete.functor F)

theorem affine_directSum_isQuasicoherent {R : Type u} [CommRing R]
    {ι : Type u} (F : ι → (affineScheme R).Modules)
    (hF : ∀ i, (F i).IsQuasicoherent) :
    (affineDirectSum F).IsQuasicoherent := by
  sorry

theorem affine_colimit_isQuasicoherent {R : Type u} [CommRing R]
    {J : Type u} [Category.{u} J] (D : J ⥤ (affineScheme R).Modules)
    (hD : ∀ j, (D.obj j).IsQuasicoherent) :
    (affineColimit D).IsQuasicoherent := by
  sorry

/-! ## 7.8. Extensions -/

instance affineGlobalSections_preservesZeroMorphisms {R : Type u} [CommRing R] :
    (AlgebraicGeometry.moduleSpecΓFunctor (R := CommRingCat.of R)).PreservesZeroMorphisms where
  map_zero X Y := by
    rfl

theorem affine_globalSections_exact_of_outer_quasiCoherent
    {R : Type u} [CommRing R]
    {F₁ F₂ F₃ : (affineScheme R).Modules}
    (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).ShortExact)
    [F₁.IsQuasicoherent] [F₃.IsQuasicoherent] :
    ((ShortComplex.mk f g hfg).map
      (AlgebraicGeometry.moduleSpecΓFunctor (R := CommRingCat.of R))).Exact := by
  sorry

theorem affine_extension_isQuasicoherent
    {R : Type u} [CommRing R]
    {F₁ F₂ F₃ : (affineScheme R).Modules}
    (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).ShortExact)
    (hQC : (F₁.IsQuasicoherent ∧ F₂.IsQuasicoherent) ∨
      (F₁.IsQuasicoherent ∧ F₃.IsQuasicoherent) ∨
      (F₂.IsQuasicoherent ∧ F₃.IsQuasicoherent)) :
    F₁.IsQuasicoherent ∧ F₂.IsQuasicoherent ∧ F₃.IsQuasicoherent := by
  sorry

end Formalization.Books.Schemes.Unit07
