import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Localization
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.CategoryTheory.Abelian.SerreClass.Bousfield
import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Examples, Chapter 79: The category of modules modulo torsion modules

The source identifies Serre quotients of module categories with module
categories over localizations.  Mathlib's `ObjectProperty.IsSerreClass` and
`MorphismProperty.Localization` provide the quotient-category interface, while
`ModuleCat.localizedModuleFunctor` provides the canonical localization functor.
The declarations below keep the source-facing properties and categories
explicit and use those existing constructions.
-/

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct nonZeroDivisors

namespace Formalization.Books.Examples.Unit79

/-! ## The generic localization statement -/

/- The source uses `Mod_A` for the category of modules over a commutative ring.
   `ModuleCat` is Mathlib's canonical bundled version of this category. -/
abbrev moduleCategory (A : Type u) [CommRing A] := ModuleCat.{u} A

/- A `ModuleCat` over a field is the category of vector spaces over that
   field. -/
abbrev vectorSpaceCategory (K : Type u) [Field K] := ModuleCat.{u} K

/-! The source's multiplicative subset is represented by a `Submonoid`. -/

/-- The property of modules whose elements are killed by elements of `S`. -/
def sTorsionModuleProperty (A : Type u) [CommRing A] (S : Submonoid A) :
    ObjectProperty (moduleCategory A) :=
  fun M => Module.IsTorsion' (M : Type u) S

@[simp]
theorem sTorsionModuleProperty_iff (A : Type u) [CommRing A] (S : Submonoid A)
    (M : moduleCategory A) :
    sTorsionModuleProperty A S M ↔ Module.IsTorsion' (M : Type u) S :=
  Iff.rfl

/-- Torsion modules form a Serre class in the category of all modules. -/
instance sTorsionModuleProperty_isSerreClass (A : Type u) [CommRing A]
    (S : Submonoid A) :
    (sTorsionModuleProperty A S).IsSerreClass := by
  have hzero (M : moduleCategory A) :
      IsZero ((ModuleCat.localizedModuleFunctor S).obj M) ↔
        Module.IsTorsion' (M : Type u) S := by
    change IsZero (M.localizedModule S) ↔ Module.IsTorsion' (M : Type u) S
    rw [ModuleCat.isZero_iff_subsingleton]
    change Subsingleton (Shrink.{u} (LocalizedModule S (M : Type u))) ↔ _
    exact (Equiv.subsingleton_congr (equivShrink (LocalizedModule S (M : Type u)))).symm.trans
      (by simpa [Module.IsTorsion'] using
        (LocalizedModule.subsingleton_iff (S := S) (M := (M : Type u))))
  have hP : sTorsionModuleProperty A S =
      ObjectProperty.inverseImage (IsZero (C := ModuleCat (Localization S)))
        (ModuleCat.localizedModuleFunctor S) := by
    ext M
    exact (hzero M).symm
  rw [hP]
  infer_instance

/-- The category obtained by inverting the isomorphisms modulo `S`-torsion. -/
abbrev sTorsionSerreQuotient (A : Type u) [CommRing A] (S : Submonoid A) :=
  (sTorsionModuleProperty A S).isoModSerre.Localization

/-- The canonical localization functor on module categories. -/
noncomputable def moduleLocalizationFunctor (A : Type u) [CommRing A]
    (S : Submonoid A) :
    moduleCategory A ⥤ ModuleCat.{u} (Localization S) :=
  ModuleCat.localizedModuleFunctor S

/- The exactness assertion in the source is already supplied by the canonical
   Mathlib localization functor. -/
theorem moduleLocalizationFunctor_isExact (A : Type u) [CommRing A]
    (S : Submonoid A) :
    Limits.PreservesFiniteLimits (moduleLocalizationFunctor A S) ∧
      Limits.PreservesFiniteColimits (moduleLocalizationFunctor A S) := by
  change
    Limits.PreservesFiniteLimits (ModuleCat.localizedModuleFunctor S) ∧
      Limits.PreservesFiniteColimits (ModuleCat.localizedModuleFunctor S)
  exact ⟨inferInstance, inferInstance⟩

/- The source identifies the localized module with the tensor-product model.
   Mathlib's `LocalizedModule.equivTensorProduct` supplies the canonical
   equivalence; the first factor only transports across `ModuleCat`'s
   universe-small `Shrink` model. -/
noncomputable def localizedModuleTensorProductEquiv (A : Type u) [CommRing A]
    (S : Submonoid A) (M : moduleCategory A) :
    (M.localizedModule S : Type u) ≃ₗ[Localization S]
      (Localization S ⊗[A] (M : Type u)) :=
  (Shrink.linearEquiv (Localization S) (LocalizedModule S (M : Type u))) ≪≫ₗ
    LocalizedModule.equivTensorProduct S (M : Type u)

theorem localizedModule_tensorProduct_model (A : Type u) [CommRing A]
    (S : Submonoid A) (M : moduleCategory A) :
    Nonempty ((M.localizedModule S : Type u) ≃ₗ[Localization S]
      (Localization S ⊗[A] (M : Type u))) :=
  ⟨localizedModuleTensorProductEquiv A S M⟩

/- This is the source's kernel calculation: the localized module vanishes
   exactly for modules in the torsion class. -/
theorem moduleLocalizationFunctor_obj_isZero_iff (A : Type u) [CommRing A]
    (S : Submonoid A) (M : moduleCategory A) :
    IsZero ((moduleLocalizationFunctor A S).obj M) ↔
      sTorsionModuleProperty A S M := by
  change IsZero (M.localizedModule S) ↔ Module.IsTorsion' (M : Type u) S
  rw [ModuleCat.isZero_iff_subsingleton]
  change Subsingleton (Shrink.{u} (LocalizedModule S (M : Type u))) ↔ _
  exact (Equiv.subsingleton_congr (equivShrink (LocalizedModule S (M : Type u)))).symm.trans
    (by simpa [Module.IsTorsion'] using
      (LocalizedModule.subsingleton_iff (S := S) (M := (M : Type u))))

/- The proposition-level interface records that the canonical functor is a
   localization for the Serre quotient. -/
theorem moduleLocalizationFunctor_isLocalization (A : Type u) [CommRing A]
    (S : Submonoid A) :
    (moduleLocalizationFunctor A S).IsLocalization
      (sTorsionModuleProperty A S).isoModSerre := by
  let adj : moduleLocalizationFunctor A S ⊣
      ModuleCat.restrictScalars (algebraMap A (Localization S)) :=
    Adjunction.mkOfHomEquiv {
      homEquiv := fun X Y => by
        change (X.localizedModule S ⟶ Y) ≃
          (X ⟶ (ModuleCat.restrictScalars (algebraMap A (Localization S))).obj Y)
        letI : IsScalarTower A (Localization S) (X.localizedModule S) := by
          infer_instance
        letI : Module A (Y : Type u) :=
          Module.compHom (Y : Type u) (algebraMap A (Localization S))
        letI : IsScalarTower A (Localization S) (Y : Type u) :=
          IsScalarTower.of_compHom A (Localization S) (Y : Type u)
        letI : IsLocalizedModule S
            (LinearMap.id : (Y : Type u) →ₗ[A] (Y : Type u)) :=
          isLocalizedModule_id S (Y : Type u) (Localization S)
        refine Equiv.mk
          (fun f => ModuleCat.ofHom
            ((f.hom.restrictScalars A).comp (X.localizedModuleMkLinearMap S)))
          (fun g => by
            exact ModuleCat.ofHom
              (IsLocalizedModule.mapExtendScalars S
                (X.localizedModuleMkLinearMap S)
                (LinearMap.id : (Y : Type u) →ₗ[A] (Y : Type u))
                (Localization S) g.hom))
          (by
            intro f
            apply ModuleCat.hom_ext
            let L : (X.localizedModule S : Type u) →ₗ[Localization S] (Y : Type u) :=
              IsLocalizedModule.mapExtendScalars S
                (X.localizedModuleMkLinearMap S)
                (LinearMap.id : (Y : Type u) →ₗ[A] (Y : Type u))
                (Localization S)
                ((f.hom.restrictScalars A).comp (X.localizedModuleMkLinearMap S))
            change L = f.hom
            have h : L.restrictScalars A = f.hom.restrictScalars A := by
              apply IsLocalizedModule.linearMap_ext S (X.localizedModuleMkLinearMap S)
                (LinearMap.id : (Y : Type u) →ₗ[A] (Y : Type u))
                (g := L.restrictScalars A) (g' := f.hom.restrictScalars A)
              ext x
              change
                (IsLocalizedModule.map S (X.localizedModuleMkLinearMap S)
                    (LinearMap.id : (Y : Type u) →ₗ[A] (Y : Type u))
                    ((f.hom.restrictScalars A).comp (X.localizedModuleMkLinearMap S)))
                  ((X.localizedModuleMkLinearMap S) x) =
                  ((f.hom.restrictScalars A).comp (X.localizedModuleMkLinearMap S)) x
              rw [IsLocalizedModule.map_apply]
              rfl
            apply LinearMap.ext
            intro x
            exact LinearMap.congr_fun h x)
          (by
            intro g
            apply ModuleCat.hom_ext
            ext x
            let g' : (X : Type u) →ₗ[A] (Y : Type u) :=
              { toFun := g.hom
                map_add' := by intro x y; exact g.hom.map_add x y
                map_smul' := by
                  intro c x
                  exact g.hom.map_smul c x }
            change
              (IsLocalizedModule.map S (X.localizedModuleMkLinearMap S)
                  (LinearMap.id : (Y : Type u) →ₗ[A] (Y : Type u)) g')
                ((X.localizedModuleMkLinearMap S) x) = g.hom x
            rw [IsLocalizedModule.map_apply]
            rfl)
      homEquiv_naturality_left_symm := by
        intros X' X Y f g
        let : Module A (X'.localizedModule S : Type u) :=
          by infer_instance
        let : Module A (Y : Type u) :=
          Module.compHom _ (algebraMap A (Localization S))
        let : IsScalarTower A (Localization S) (X'.localizedModule S : Type u) :=
          by infer_instance
        let : IsScalarTower A (Localization S) (Y : Type u) :=
          IsScalarTower.of_compHom A (Localization S) _
        let : IsLocalizedModule S (LinearMap.id : (Y : Type u) →ₗ[A] (Y : Type u)) :=
          isLocalizedModule_id S (Y : Type u) (Localization S)
        let : Module A ((ModuleCat.restrictScalars (algebraMap A (Localization S))).obj Y : Type u) :=
          ((ModuleCat.restrictScalars (algebraMap A (Localization S))).obj Y).isModule
        let : IsScalarTower A (Localization S)
            ((ModuleCat.restrictScalars (algebraMap A (Localization S))).obj Y : Type u) :=
          IsScalarTower.of_compHom A (Localization S) _
        let : IsLocalizedModule S
            (LinearMap.id :
              ((ModuleCat.restrictScalars (algebraMap A (Localization S))).obj Y : Type u) →ₗ[A]
                ((ModuleCat.restrictScalars (algebraMap A (Localization S))).obj Y : Type u)) :=
          isLocalizedModule_id S (Y : Type u) (Localization S)
        dsimp only [Equiv.symm, Equiv.mk, id]
        dsimp [moduleLocalizationFunctor, ModuleCat.localizedModuleFunctor]
        apply ModuleCat.hom_ext
        ext x
        change
          (IsLocalizedModule.mapExtendScalars S (X'.localizedModuleMkLinearMap S)
              LinearMap.id (Localization S) (ModuleCat.Hom.hom (f ≫ g))) x =
            (ModuleCat.Hom.hom
              (ModuleCat.localizedModuleMap S f ≫
                ModuleCat.ofHom
                  (IsLocalizedModule.mapExtendScalars S (X.localizedModuleMkLinearMap S)
                    LinearMap.id (Localization S) (ModuleCat.Hom.hom g)))) x
        simp [ModuleCat.localizedModuleMap, IsLocalizedModule.mapExtendScalars,
          LinearMap.extendScalarsOfIsLocalizationEquiv]
        rw [IsLocalizedModule.map_comp' S (X'.localizedModuleMkLinearMap S)
          (X.localizedModuleMkLinearMap S)
          (LinearMap.id :
            ((ModuleCat.restrictScalars (algebraMap A (Localization S))).obj Y : Type u) →ₗ[A]
              ((ModuleCat.restrictScalars (algebraMap A (Localization S))).obj Y : Type u))
          (ModuleCat.Hom.hom f) (ModuleCat.Hom.hom g)]
        change
          _ = (LinearMap.extendScalarsOfIsLocalization S (Localization S) _)
            ((LinearMap.extendScalarsOfIsLocalization S (Localization S) _) x)
        rfl
      homEquiv_naturality_right := by
        intros X Y Y' f g
        let : Module A ((moduleLocalizationFunctor A S).obj X : Type u) :=
          Module.compHom _ (algebraMap A (Localization S))
        let : IsScalarTower A (Localization S)
            ((moduleLocalizationFunctor A S).obj X : Type u) :=
          IsScalarTower.of_compHom A (Localization S) _
        let : Module A ((ModuleCat.localizedModuleFunctor S).obj X : Type u) :=
          Module.compHom _ (algebraMap A (Localization S))
        let : Module A (Y : Type u) :=
          Module.compHom _ (algebraMap A (Localization S))
        let : Module A (Y' : Type u) :=
          Module.compHom _ (algebraMap A (Localization S))
        let : IsScalarTower A (Localization S)
            ((ModuleCat.localizedModuleFunctor S).obj X : Type u) :=
          IsScalarTower.of_compHom A (Localization S) _
        let : IsScalarTower A (Localization S) (Y : Type u) :=
          IsScalarTower.of_compHom A (Localization S) _
        let : IsScalarTower A (Localization S) (Y' : Type u) :=
          IsScalarTower.of_compHom A (Localization S) _
        dsimp only [Equiv.symm, Equiv.mk, id]
        dsimp [moduleLocalizationFunctor, ModuleCat.localizedModuleFunctor]
        apply ModuleCat.hom_ext
        ext x
        change
          (ModuleCat.Hom.hom (f ≫ g)).restrictScalars A
              ((X.localizedModuleMkLinearMap S) x) =
            (ModuleCat.Hom.hom g)
              ((ModuleCat.Hom.hom f).restrictScalars A
                ((X.localizedModuleMkLinearMap S) x))
        rfl
    }
  let _ : (ModuleCat.restrictScalars (algebraMap A (Localization S))).Full := ⟨by
    intro X Y f
    let : Module A ((ModuleCat.restrictScalars (algebraMap A (Localization S))).obj X : Type u) :=
      ((ModuleCat.restrictScalars (algebraMap A (Localization S))).obj X).isModule
    let : Module A ((ModuleCat.restrictScalars (algebraMap A (Localization S))).obj Y : Type u) :=
      ((ModuleCat.restrictScalars (algebraMap A (Localization S))).obj Y).isModule
    let : IsScalarTower A (Localization S)
        ((ModuleCat.restrictScalars (algebraMap A (Localization S))).obj X : Type u) :=
      IsScalarTower.of_compHom A (Localization S) _
    let : IsScalarTower A (Localization S)
        ((ModuleCat.restrictScalars (algebraMap A (Localization S))).obj Y : Type u) :=
      IsScalarTower.of_compHom A (Localization S) _
    refine ⟨ModuleCat.ofHom
      (LinearMap.extendScalarsOfIsLocalization
        (M := ((ModuleCat.restrictScalars (algebraMap A (Localization S))).obj X : Type u))
        (N := ((ModuleCat.restrictScalars (algebraMap A (Localization S))).obj Y : Type u))
        S (Localization S) f.hom), ?_⟩
    ext x
    rfl⟩
  let _ : PreservesFiniteLimits (moduleLocalizationFunctor A S) :=
    (moduleLocalizationFunctor_isExact A S).1
  let _ : PreservesFiniteColimits (moduleLocalizationFunctor A S) :=
    (moduleLocalizationFunctor_isExact A S).2
  have hL := Abelian.isLocalization_isoModSerre_kernel_of_leftAdjoint adj
  have hP : (moduleLocalizationFunctor A S).kernel = sTorsionModuleProperty A S := by
    ext M
    change IsZero ((moduleLocalizationFunctor A S).obj M) ↔ _
    exact moduleLocalizationFunctor_obj_isZero_iff A S M
  have hW : (moduleLocalizationFunctor A S).kernel.isoModSerre =
      (sTorsionModuleProperty A S).isoModSerre := by
    ext X Y f
    change
      ((moduleLocalizationFunctor A S).kernel (kernel f) ∧
        (moduleLocalizationFunctor A S).kernel (cokernel f)) ↔
      ((sTorsionModuleProperty A S) (kernel f) ∧
        (sTorsionModuleProperty A S) (cokernel f))
    rw [hP]
  rw [hW] at hL
  exact hL

/-- The canonical equivalence `Mod_A / T ≌ Mod_{S⁻¹A}`. -/
noncomputable def moduleLocalizationSerreQuotientEquivalence
    (A : Type u) [CommRing A] (S : Submonoid A) :
    sTorsionSerreQuotient A S ≌ ModuleCat.{u} (Localization S) := by
  letI := moduleLocalizationFunctor_isLocalization A S
  exact CategoryTheory.Localization.uniq
    (sTorsionModuleProperty A S).isoModSerre.Q
    (moduleLocalizationFunctor A S)
    (sTorsionModuleProperty A S).isoModSerre

/-- The generic localization/Serre-quotient equivalence. -/
theorem localization_and_serre_quotients
    (A : Type u) [CommRing A] (S : Submonoid A) :
    Nonempty (sTorsionSerreQuotient A S ≌ ModuleCat.{u} (Localization S)) :=
  ⟨moduleLocalizationSerreQuotientEquivalence A S⟩

/-! ## The total quotient ring -/

/- Mathlib's `FractionRing` is the total quotient ring in the general
   commutative-ring case, not only in the domain case. -/
abbrev totalQuotientRing (A : Type u) [CommRing A] := FractionRing A

abbrev torsionModuleProperty (A : Type u) [CommRing A] :
    ObjectProperty (moduleCategory A) :=
  sTorsionModuleProperty A (nonZeroDivisors A)

@[simp]
theorem torsionModuleProperty_iff (A : Type u) [CommRing A]
    (M : moduleCategory A) :
    torsionModuleProperty A M ↔ Module.IsTorsion A (M : Type u) :=
  Iff.rfl

/-- Torsion `A`-modules form a Serre class in `Mod_A`. -/
theorem torsionModuleProperty_isSerreClass (A : Type u) [CommRing A] :
    (torsionModuleProperty A).IsSerreClass :=
  inferInstance

/-- The total-quotient specialization of the generic kernel criterion. -/
theorem totalQuotientModule_isZero_iff_torsion (A : Type u) [CommRing A]
    (M : moduleCategory A) :
    IsZero ((moduleLocalizationFunctor A (nonZeroDivisors A)).obj M) ↔
      torsionModuleProperty A M := by
  exact moduleLocalizationFunctor_obj_isZero_iff A (nonZeroDivisors A) M

/-- The quotient of `Mod_A` by torsion modules is `Mod_{Q(A)}`. -/
theorem quotientByTorsionModules_equiv_totalQuotientRing
    (A : Type u) [CommRing A] :
    Nonempty
      ((torsionModuleProperty A).isoModSerre.Localization ≌
        ModuleCat.{u} (totalQuotientRing A)) := by
  exact ⟨moduleLocalizationSerreQuotientEquivalence A (nonZeroDivisors A)⟩

/- When `A` is a domain, the total quotient ring is the fraction field, so
   the target category is a category of vector spaces. -/
theorem quotientByTorsionModules_equiv_fractionField
    (A : Type u) [CommRing A] [IsDomain A] :
    Nonempty
      ((torsionModuleProperty A).isoModSerre.Localization ≌
        vectorSpaceCategory (FractionRing A)) :=
  quotientByTorsionModules_equiv_totalQuotientRing A

/-! ## Finitely generated modules over a Noetherian domain -/

/-- Mathlib's `FGModuleCat` is the canonical full subcategory for the source's
category `Mod_A^fg`. -/
abbrev finitelyGeneratedModuleProperty (A : Type u) [CommRing A] :
    ObjectProperty (moduleCategory A) :=
  ModuleCat.isFG.{u} A

abbrev finitelyGeneratedModuleCategory (A : Type u) [CommRing A] :=
  FGModuleCat.{u} A

/- The Noetherian hypothesis is exactly the source's hypothesis ensuring that
   the finitely generated module category is abelian; this is Mathlib's
   canonical instance for `FGModuleCat`. -/
instance finitelyGeneratedModuleCategory_abelian
    (A : Type u) [CommRing A] [IsNoetherianRing A] :
    Abelian (finitelyGeneratedModuleCategory A) := inferInstance

/-- The canonical inclusion `Mod_A^fg ↪ Mod_A`. -/
def finitelyGeneratedModuleInclusion (A : Type u) [CommRing A] :
    finitelyGeneratedModuleCategory A ⥤ moduleCategory A :=
  (finitelyGeneratedModuleProperty A).ι

/-- The finitely generated torsion modules inside `Mod_A^fg`. -/
def finitelyGeneratedTorsionModuleProperty (A : Type u) [CommRing A] :
    ObjectProperty (finitelyGeneratedModuleCategory A) :=
  fun M => Module.IsTorsion A (M.obj : Type u)

/- Finitely generated torsion modules form a Serre class once the ambient
   finitely generated category is known to be abelian. -/
instance finitelyGeneratedTorsionModuleProperty_isSerreClass
    (A : Type u) [CommRing A] [IsNoetherianRing A] :
    (finitelyGeneratedTorsionModuleProperty A).IsSerreClass := by
  change (ObjectProperty.inverseImage
      (torsionModuleProperty A) (finitelyGeneratedModuleInclusion A)).IsSerreClass
  let _ : (torsionModuleProperty A).IsSerreClass := torsionModuleProperty_isSerreClass A
  let _ : PreservesFiniteLimits (finitelyGeneratedModuleInclusion A) := by
    change PreservesFiniteLimits (forget₂ (FGModuleCat A) (ModuleCat A))
    infer_instance
  let _ : PreservesFiniteColimits (finitelyGeneratedModuleInclusion A) := by
    change PreservesFiniteColimits (forget₂ (FGModuleCat A) (ModuleCat A))
    infer_instance
  infer_instance

abbrev finitelyGeneratedTorsionSerreQuotient
    (A : Type u) [CommRing A] [IsNoetherianRing A] :=
  (finitelyGeneratedTorsionModuleProperty A).isoModSerre.Localization

/- Mathlib's `FGModuleCat K` is the canonical category of finite-dimensional
   vector spaces when `K` is a field. -/
abbrev finiteDimensionalVectorSpaceCategory (K : Type u) [Field K] :=
  FGModuleCat.{u} K

theorem finitelyGeneratedQuotientFunctor_isInvertedBy
    (A : Type u) [CommRing A] [IsNoetherianRing A] :
    (finitelyGeneratedTorsionModuleProperty A).isoModSerre.IsInvertedBy
      (finitelyGeneratedModuleInclusion A ⋙
        (torsionModuleProperty A).isoModSerre.Q) := by
  let _ : Abelian (torsionModuleProperty A).isoModSerre.Localization :=
    ObjectProperty.SerreClassLocalization.abelian
      (torsionModuleProperty A).isoModSerre.Q (torsionModuleProperty A)
  let _ : PreservesFiniteLimits ((torsionModuleProperty A).isoModSerre.Q) :=
    ObjectProperty.SerreClassLocalization.preservesFiniteLimits
      (torsionModuleProperty A).isoModSerre.Q (torsionModuleProperty A)
  let _ : PreservesFiniteColimits ((torsionModuleProperty A).isoModSerre.Q) :=
    ObjectProperty.SerreClassLocalization.preservesFiniteColimits
      (torsionModuleProperty A).isoModSerre.Q (torsionModuleProperty A)
  let _ : PreservesFiniteLimits (finitelyGeneratedModuleInclusion A) := by
    change PreservesFiniteLimits (forget₂ (FGModuleCat A) (ModuleCat A))
    infer_instance
  let _ : PreservesFiniteColimits (finitelyGeneratedModuleInclusion A) := by
    change PreservesFiniteColimits (forget₂ (FGModuleCat A) (ModuleCat A))
    infer_instance
  let _ : PreservesFiniteLimits
      (finitelyGeneratedModuleInclusion A ⋙
        (torsionModuleProperty A).isoModSerre.Q) :=
    comp_preservesFiniteLimits _ _
  let _ : PreservesFiniteColimits
      (finitelyGeneratedModuleInclusion A ⋙
        (torsionModuleProperty A).isoModSerre.Q) :=
    comp_preservesFiniteColimits _ _
  apply (ObjectProperty.isoModSerre_isInvertedBy_iff
    (finitelyGeneratedTorsionModuleProperty A)
    (finitelyGeneratedModuleInclusion A ⋙
      (torsionModuleProperty A).isoModSerre.Q)).2
  intro M hM
  exact (ObjectProperty.SerreClassLocalization.isZero_obj_iff
    (torsionModuleProperty A).isoModSerre.Q (torsionModuleProperty A)
    ((finitelyGeneratedModuleInclusion A).obj M)).2 hM

/- The inclusion of finitely generated modules induces the canonical functor
   between the two Serre quotient categories. -/
noncomputable def finitelyGeneratedQuotientToModuleQuotient
    (A : Type u) [CommRing A] [IsNoetherianRing A] :
    finitelyGeneratedTorsionSerreQuotient A ⥤
      (torsionModuleProperty A).isoModSerre.Localization := by
  let F :=
    finitelyGeneratedModuleInclusion A ⋙
      (torsionModuleProperty A).isoModSerre.Q
  exact CategoryTheory.Localization.lift F
    (finitelyGeneratedQuotientFunctor_isInvertedBy A)
    (finitelyGeneratedTorsionModuleProperty A).isoModSerre.Q

/- This is the source's assertion that the canonical functor from the
   finitely generated quotient to the unrestricted quotient is full. -/
theorem finitelyGeneratedQuotientToModuleQuotient_full
    (A : Type u) [CommRing A] [IsNoetherianRing A] :
    (finitelyGeneratedQuotientToModuleQuotient A).Full := by
  sorry
  /- Original proof attempt:
  let L := (finitelyGeneratedTorsionModuleProperty A).isoModSerre.Q
  have : L.EssSurj := Localization.essSurj L
    (finitelyGeneratedTorsionModuleProperty A).isoModSerre
  let F := finitelyGeneratedModuleInclusion A ⋙
    (torsionModuleProperty A).isoModSerre.Q
  let e : F ≅ L ⋙ finitelyGeneratedQuotientToModuleQuotient A :=
    (Localization.fac F (finitelyGeneratedQuotientFunctor_isInvertedBy A) L).symm
  refine (finitelyGeneratedQuotientToModuleQuotient A).full_of_comp_essSurj L
    (fun X₁ X₂ φ ↦ ?_)
  obtain ⟨φ', hφ'⟩ : ∃ φ', φ = e.inv.app X₁ ≫ φ' ≫ e.hom.app X₂ :=
    ⟨e.hom.app X₁ ≫ φ ≫ e.inv.app X₂, by
      simp [dsimp% e.inv_hom_id_app_assoc, dsimp% e.inv_hom_id_app]⟩
  obtain ⟨f, hf⟩ := Localization.exists_leftFraction
    (torsionModuleProperty A).isoModSerre.Q
    (torsionModuleProperty A).isoModSerre φ'
  let B : moduleCategory A :=
    (finitelyGeneratedModuleInclusion A).obj X₁ ⊞
      (finitelyGeneratedModuleInclusion A).obj X₂
  let h : B ⟶ f.Y' := biprod.desc f.f f.s
  let _ : Module.Finite A ((finitelyGeneratedModuleInclusion A).obj X₁ : Type u) := by
    exact X₁.property
  let _ : Module.Finite A ((finitelyGeneratedModuleInclusion A).obj X₂ : Type u) := by
    exact X₂.property
  let _ : Module.Finite A
      (B : Type u) := by
    apply (Module.Finite.equiv_iff
      (ModuleCat.biprodIsoProd
        ((finitelyGeneratedModuleInclusion A).obj X₁)
        ((finitelyGeneratedModuleInclusion A).obj X₂)).toLinearEquiv).2
    exact Module.Finite.prod
  let Z : finitelyGeneratedModuleCategory A :=
    ⟨(Abelian.image (C := moduleCategory A) h : moduleCategory A), by
      change ModuleCat.isFG A (Abelian.image (C := moduleCategory A) h)
      simpa only [ModuleCat.isFG] using
        (Module.Finite.of_surjective
          (Abelian.factorThruImage h).hom
          ((ModuleCat.epi_iff_surjective _).1 inferInstance))⟩
  let f' : (finitelyGeneratedModuleInclusion A).obj X₁ ⟶
      (finitelyGeneratedModuleInclusion A).obj Z :=
    by
      dsimp [Z]
      change _ ⟶ (Abelian.image (C := moduleCategory A) h : moduleCategory A)
      exact biprod.inl ≫ Abelian.factorThruImage h
  let s' : (finitelyGeneratedModuleInclusion A).obj X₂ ⟶
      (finitelyGeneratedModuleInclusion A).obj Z :=
    by
      dsimp [Z]
      change _ ⟶ (Abelian.image (C := moduleCategory A) h : moduleCategory A)
      exact biprod.inr ≫ Abelian.factorThruImage h
  let ffg : X₁ ⟶ Z :=
    ObjectProperty.homMk (P := finitelyGeneratedModuleProperty A)
      (X := X₁) (Y := Z) f'
  let sfg : X₂ ⟶ Z :=
    ObjectProperty.homMk (P := finitelyGeneratedModuleProperty A)
      (X := X₂) (Y := Z) s'
  dsimp [Z] at f' s'
  let _ : PreservesFiniteLimits (finitelyGeneratedModuleInclusion A) := by
    change PreservesFiniteLimits (forget₂ (FGModuleCat A) (ModuleCat A))
    infer_instance
  let _ : PreservesFiniteColimits (finitelyGeneratedModuleInclusion A) := by
    change PreservesFiniteColimits (forget₂ (FGModuleCat A) (ModuleCat A))
    infer_instance
  have hf' : f.f = f' ≫ Abelian.image.ι (C := moduleCategory A) h := by
    change f.f = (biprod.inl ≫ Abelian.factorThruImage h) ≫
      Abelian.image.ι (C := moduleCategory A) h
    rw [Category.assoc, Abelian.image.fac, biprod.inl_desc]
  have hs' : f.s = s' ≫ Abelian.image.ι (C := moduleCategory A) h := by
    change f.s = (biprod.inr ≫ Abelian.factorThruImage h) ≫
      Abelian.image.ι (C := moduleCategory A) h
    rw [Category.assoc, Abelian.image.fac, biprod.inr_desc]
  let i : (finitelyGeneratedModuleInclusion A).obj Z ⟶ f.Y' := by
    dsimp [Z]
    exact Abelian.image.ι (C := moduleCategory A) h
  have hfi : f.f = f' ≫ i := by
    change f.f = f' ≫ Abelian.image.ι (C := moduleCategory A) h
    exact hf'
  have hsi : f.s = s' ≫ i := by
    change f.s = s' ≫ Abelian.image.ι (C := moduleCategory A) h
    exact hs'
  let q := cokernel.map f.s (Abelian.image.ι (C := moduleCategory A) h) s' (𝟙 _)
    (by rw [hs']; rfl)
  have _ : Epi q := by
    have hfac : cokernel.π f.s ≫ q =
        cokernel.π (Abelian.image.ι (C := moduleCategory A) h) := by
      dsimp [q]
      simp
    exact epi_of_epi_fac hfac
  have hfs : (torsionModuleProperty A) (cokernel f.s) :=
    ((torsionModuleProperty A).isoModSerre_iff f.s).mp f.hs |>.2
  have hq : (torsionModuleProperty A)
      (cokernel (Abelian.image.ι (C := moduleCategory A) h)) := by
    exact (torsionModuleProperty A).prop_of_epi q hfs
  have hi : (torsionModuleProperty A).isoModSerre
      (Abelian.image.ι (C := moduleCategory A) h) := by
    rw [(torsionModuleProperty A).isoModSerre_iff_of_mono]
    exact hq
  have hi' : (torsionModuleProperty A).isoModSerre i := by
    change (torsionModuleProperty A).isoModSerre
      (Abelian.image.ι (C := moduleCategory A) h)
    exact hi
  have hs'_all : (torsionModuleProperty A).isoModSerre s' := by
    apply MorphismProperty.of_postcomp
      (W := (torsionModuleProperty A).isoModSerre)
      (W' := (torsionModuleProperty A).isoModSerre) s'
      (Abelian.image.ι (C := moduleCategory A) h) hi
    rw [← hs']
    exact f.hs
  have hs'_map : (torsionModuleProperty A).isoModSerre
      ((finitelyGeneratedModuleInclusion A).map sfg) := by
    change (torsionModuleProperty A).isoModSerre s'
    exact hs'_all
  have hs'_fg : (finitelyGeneratedTorsionModuleProperty A).isoModSerre sfg := by
    rw [ObjectProperty.isoModSerre_iff]
    constructor
    · change (torsionModuleProperty A)
        ((finitelyGeneratedModuleInclusion A).obj (kernel sfg))
      exact (torsionModuleProperty A).prop_of_iso
        (PreservesKernel.iso (finitelyGeneratedModuleInclusion A) sfg).symm
        ((hs'_map.1))
    · change (torsionModuleProperty A)
        ((finitelyGeneratedModuleInclusion A).obj (cokernel sfg))
      exact (torsionModuleProperty A).prop_of_iso
        (PreservesCokernel.iso (finitelyGeneratedModuleInclusion A) sfg).symm
        ((hs'_map.2))
  let g : (finitelyGeneratedTorsionModuleProperty A).isoModSerre.LeftFraction X₁ X₂ :=
    { Y' := Z
      f := ffg
      s := sfg
      hs := hs'_fg }
  have := Localization.inverts L _ _ g.hs
  refine ⟨g.map L (Localization.inverts _ _), ?_⟩
  rw [← cancel_mono ((finitelyGeneratedQuotientToModuleQuotient A).map
      (L.map g.s)), ← Functor.map_comp,
    MorphismProperty.LeftFraction.map_comp_map_s]
  let _ : IsIso ((torsionModuleProperty A).isoModSerre.Q.map s') :=
    Localization.inverts (torsionModuleProperty A).isoModSerre.Q
      (torsionModuleProperty A).isoModSerre s' hs'_all
  let _ : IsIso ((torsionModuleProperty A).isoModSerre.Q.map
      (Abelian.image.ι (C := moduleCategory A) h)) :=
    Localization.inverts (torsionModuleProperty A).isoModSerre.Q
      (torsionModuleProperty A).isoModSerre _ hi
  let _ : IsIso ((torsionModuleProperty A).isoModSerre.Q.map i) :=
    Localization.inverts (torsionModuleProperty A).isoModSerre.Q
      (torsionModuleProperty A).isoModSerre i hi'
  let _ : IsIso ((torsionModuleProperty A).isoModSerre.Q.map f.s) :=
    Localization.inverts (torsionModuleProperty A).isoModSerre.Q
      (torsionModuleProperty A).isoModSerre _ f.hs
  have hfmap : f.map (torsionModuleProperty A).isoModSerre.Q
      (Localization.inverts _ _) =
      (torsionModuleProperty A).isoModSerre.Q.map f' ≫
        inv ((torsionModuleProperty A).isoModSerre.Q.map s') := by
    rw [← cancel_mono ((torsionModuleProperty A).isoModSerre.Q.map f.s)]
    rw [MorphismProperty.LeftFraction.map_comp_map_s, hfi, hsi]
    simp only [Functor.map_comp]
    simp
  rw [hφ', hf, hfmap]
  dsimp [g]
  have hffg : F.map ffg = (torsionModuleProperty A).isoModSerre.Q.map f' := by
    change (torsionModuleProperty A).isoModSerre.Q.map f' =
      (torsionModuleProperty A).isoModSerre.Q.map f'
    rfl
  have hsfg_map : F.map sfg = (torsionModuleProperty A).isoModSerre.Q.map s' := by
    change (torsionModuleProperty A).isoModSerre.Q.map s' =
      (torsionModuleProperty A).isoModSerre.Q.map s'
    rfl
  have hnatf : F.map ffg ≫ e.hom.app Z =
      e.hom.app X₁ ≫ (finitelyGeneratedQuotientToModuleQuotient A).map
        (L.map ffg) := by
    simpa only [Functor.comp_map] using e.hom.naturality ffg
  have hnats : F.map sfg ≫ e.hom.app Z =
      e.hom.app X₂ ≫ (finitelyGeneratedQuotientToModuleQuotient A).map
        (L.map sfg) := by
    simpa only [Functor.comp_map] using e.hom.naturality sfg
  calc
    (finitelyGeneratedQuotientToModuleQuotient A).map (L.map ffg) =
        e.inv.app X₁ ≫ e.hom.app X₁ ≫
          (finitelyGeneratedQuotientToModuleQuotient A).map (L.map ffg) := by
      simp
    _ = e.inv.app X₁ ≫ F.map ffg ≫ e.hom.app Z := by
      rw [← hnatf]
    _ = e.inv.app X₁ ≫
        (torsionModuleProperty A).isoModSerre.Q.map f' ≫ e.hom.app Z := by
      rw [hffg]
    _ = (e.inv.app X₁ ≫
        ((torsionModuleProperty A).isoModSerre.Q.map f' ≫
          inv ((torsionModuleProperty A).isoModSerre.Q.map s')) ≫
        e.hom.app X₂ ≫
      (finitelyGeneratedQuotientToModuleQuotient A).map (L.map sfg)) := by
      simp only [Category.assoc, ← hnats, hsfg_map, IsIso.inv_hom_id_assoc] <;>
        rw [Category.assoc]
  -/

/- The main finite-dimensionality statement records the source's restriction
   of the total-quotient equivalence to finitely generated modules. -/
theorem quotientByFinitelyGeneratedTorsionModules_equiv_finiteDimensional
    (A K : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] :
    Nonempty
      (finitelyGeneratedTorsionSerreQuotient A ≌
        finiteDimensionalVectorSpaceCategory K) := by
  sorry
  /- Original proof attempt:
  let r : FractionRing A ≃+* K := (FractionRing.algEquiv A K).toRingEquiv
  let r' : Localization (nonZeroDivisors A) ≃+* K :=
    (FractionRing.algEquiv A K).toRingEquiv
  let R : ModuleCat.{u} (FractionRing A) ≌ ModuleCat.{u} K :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv r).symm
  let e := moduleLocalizationSerreQuotientEquivalence A (nonZeroDivisors A)
  let _ : (moduleLocalizationFunctor A (nonZeroDivisors A)).IsLocalization
      ((torsionModuleProperty A).isoModSerre) :=
    moduleLocalizationFunctor_isLocalization A (nonZeroDivisors A)
  let H : finitelyGeneratedTorsionSerreQuotient A ⥤ ModuleCat.{u} K :=
    finitelyGeneratedQuotientToModuleQuotient A ⋙ e.functor ⋙ R.functor
  have hfinite (X : finitelyGeneratedTorsionSerreQuotient A) :
      ModuleCat.isFG K (H.obj X) := by
    let Lfg := (finitelyGeneratedTorsionModuleProperty A).isoModSerre.Q
    let _ : Lfg.EssSurj := Localization.essSurj Lfg
      (finitelyGeneratedTorsionModuleProperty A).isoModSerre
    obtain ⟨M, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage Lfg X
    let _ : Module.Finite A ((finitelyGeneratedModuleInclusion A).obj M : Type u) :=
      M.property
    let F' := finitelyGeneratedModuleInclusion A ⋙
      (torsionModuleProperty A).isoModSerre.Q
    let η : F' ≅ Lfg ⋙ finitelyGeneratedQuotientToModuleQuotient A :=
      (Localization.fac F' (finitelyGeneratedQuotientFunctor_isInvertedBy A) Lfg).symm
    let ε : (torsionModuleProperty A).isoModSerre.Q ⋙ e.functor ≅
        moduleLocalizationFunctor A (nonZeroDivisors A) :=
      Localization.compUniqFunctor
        (torsionModuleProperty A).isoModSerre.Q
        (moduleLocalizationFunctor A (nonZeroDivisors A))
        (torsionModuleProperty A).isoModSerre
    let k : e.functor.obj ((torsionModuleProperty A).isoModSerre.Q.obj
        ((finitelyGeneratedModuleInclusion A).obj M)) ≅
        e.functor.obj ((finitelyGeneratedQuotientToModuleQuotient A).obj
          (Lfg.obj M)) :=
      e.functor.mapIso (η.app M)
    let _ : Module.Finite (FractionRing A)
        ((moduleLocalizationFunctor A (nonZeroDivisors A)).obj
          ((finitelyGeneratedModuleInclusion A).obj M) : Type u) := by
      change Module.Finite (FractionRing A)
        (Shrink.{u} (LocalizedModule (nonZeroDivisors A)
          ((finitelyGeneratedModuleInclusion A).obj M : Type u)))
      exact Module.Finite.equiv
        (Shrink.linearEquiv (FractionRing A)
          (LocalizedModule (nonZeroDivisors A)
            ((finitelyGeneratedModuleInclusion A).obj M : Type u))).symm
    let _ : Module.Finite (FractionRing A)
        (e.functor.obj ((torsionModuleProperty A).isoModSerre.Q.obj
          ((finitelyGeneratedModuleInclusion A).obj M)) : Type u) := by
      apply Module.Finite.of_surjective (ε.app ((finitelyGeneratedModuleInclusion A).obj M)).inv.hom
      exact (ModuleCat.epi_iff_surjective _).1 inferInstance
    let _ : Module.Finite (FractionRing A)
        (e.functor.obj ((finitelyGeneratedQuotientToModuleQuotient A).obj
          (Lfg.obj M)) : Type u) := by
      apply Module.Finite.of_surjective k.hom.hom
      exact (ModuleCat.epi_iff_surjective _).1 inferInstance
    let _ : Algebra (FractionRing A) K := r.toRingHom.toAlgebra
    let _ : Module (FractionRing A) (H.obj (Lfg.obj M) : Type u) :=
      Module.compHom _ r.toRingHom
    let _ : IsScalarTower (FractionRing A) K (H.obj (Lfg.obj M) : Type u) :=
      ⟨fun x y z => by
        change (r x * y) • z = r x • y • z
        exact (smul_smul (r x) y z).symm⟩
    let _ : Module.Finite (FractionRing A) (H.obj (Lfg.obj M) : Type u) := by
      let eV :
          ((e.functor.obj ((finitelyGeneratedQuotientToModuleQuotient A).obj
            (Lfg.obj M)) : ModuleCat (FractionRing A)) : Type u) ≃ₗ[FractionRing A]
          (H.obj (Lfg.obj M) : Type u) :=
        { toFun := fun x => x
          invFun := fun x => x
          left_inv := by intro x; rfl
          right_inv := by intro x; rfl
          map_add' := by intro x y; rfl
          map_smul' := by
            intro c x
            change @Eq
                ((ModuleCat.restrictScalars r'.symm.toRingHom).obj
                  (e.functor.obj ((finitelyGeneratedQuotientToModuleQuotient A).obj
                    (Lfg.obj M))) : Type u)
                (AddCommGrpCat.Hom.hom
                  ((e.functor.obj ((finitelyGeneratedQuotientToModuleQuotient A).obj
                    (Lfg.obj M))).smul c) x)
                (AddCommGrpCat.Hom.hom (((ModuleCat.restrictScalars r'.symm.toRingHom).obj
                  (e.functor.obj ((finitelyGeneratedQuotientToModuleQuotient A).obj
                    (Lfg.obj M)))).smul (r c)) x)
            have hrr : r c = r' c := rfl
            have hrc : r'.symm.toRingHom (r' c) = c :=
              r'.symm_apply_apply c
            convert (congrArg (fun h => AddCommGrpCat.Hom.hom h x)
              (ModuleCat.smul_restrictScalars r'.symm.toRingHom (r' c)
                (e.functor.obj ((finitelyGeneratedQuotientToModuleQuotient A).obj
                  (Lfg.obj M))))).symm using 1 <;>
              simp only [hrr, hrc] <;>
              rfl }
      exact Module.Finite.equiv eV
    let _ : Module.Finite K (H.obj (Lfg.obj M) : Type u) :=
      Module.Finite.of_restrictScalars_finite (FractionRing A) K
        (H.obj (Lfg.obj M) : Type u)
    apply Module.Finite.of_surjective (H.map i.hom).hom
    exact (ModuleCat.epi_iff_surjective _).1 inferInstance
  let F : finitelyGeneratedTorsionSerreQuotient A ⥤
      finiteDimensionalVectorSpaceCategory K :=
    (ModuleCat.isFG K).lift H hfinite
  let _ : PreservesFiniteLimits (finitelyGeneratedModuleInclusion A) := by
    change PreservesFiniteLimits (forget₂ (FGModuleCat A) (ModuleCat A))
    infer_instance
  let _ : PreservesFiniteColimits (finitelyGeneratedModuleInclusion A) := by
    change PreservesFiniteColimits (forget₂ (FGModuleCat A) (ModuleCat A))
    infer_instance
  have hfaith :
      (finitelyGeneratedQuotientToModuleQuotient A).Faithful := by
    let L' := (finitelyGeneratedTorsionModuleProperty A).isoModSerre.Q
    refine Functor.faithful_of_comp_of_hasLeftCalculusOfFractions
      (L := L') (W := (finitelyGeneratedTorsionModuleProperty A).isoModSerre)
      (finitelyGeneratedQuotientToModuleQuotient A) (fun X Y f g hfg ↦ ?_)
    let F' := finitelyGeneratedModuleInclusion A ⋙
      (torsionModuleProperty A).isoModSerre.Q
    let _ : PreservesFiniteLimits ((torsionModuleProperty A).isoModSerre.Q) :=
      ObjectProperty.SerreClassLocalization.preservesFiniteLimits
        ((torsionModuleProperty A).isoModSerre.Q) (torsionModuleProperty A)
    let _ : PreservesFiniteColimits ((torsionModuleProperty A).isoModSerre.Q) :=
      ObjectProperty.SerreClassLocalization.preservesFiniteColimits
        ((torsionModuleProperty A).isoModSerre.Q) (torsionModuleProperty A)
    let _ : PreservesFiniteLimits F' := comp_preservesFiniteLimits _ _
    let _ : PreservesFiniteColimits F' := comp_preservesFiniteColimits _ _
    let _ : PreservesBiproductsOfShape WalkingPair F' := by
      constructor
      intro f
      apply preservesBiproduct_of_preservesProduct
    let _ : PreservesBinaryBiproducts F' := by
      apply preservesBinaryBiproducts_of_preservesBiproducts
    let η : F' ≅ L' ⋙ finitelyGeneratedQuotientToModuleQuotient A :=
      (Localization.fac F' (finitelyGeneratedQuotientFunctor_isInvertedBy A) L').symm
    have hF'eq : F'.map f = F'.map g := by
      apply (cancel_mono (η.hom.app Y)).1
      rw [η.hom.naturality, η.hom.naturality]
      simpa only [Functor.comp_map] using
        congrArg (fun k => η.hom.app X ≫ k) hfg
    let _ : F'.Additive := by
      apply Functor.additive_of_preservesBinaryBiproducts
    have hFdiff : F'.map (f - g) = 0 := by
      rw [Functor.map_sub, hF'eq, sub_self]
    have hq :
        (finitelyGeneratedQuotientToModuleQuotient A).map (L'.map (f - g)) = 0 := by
      have hzero : η.hom.app X ≫
              (finitelyGeneratedQuotientToModuleQuotient A).map (L'.map (f - g)) = 0 := by
        calc
          η.hom.app X ≫
                (finitelyGeneratedQuotientToModuleQuotient A).map (L'.map (f - g)) =
              F'.map (f - g) ≫ η.hom.app Y := by
            simpa only [Functor.comp_map] using (η.hom.naturality (f - g)).symm
          _ = 0 := by simp only [hFdiff, zero_comp]
      apply (cancel_epi (η.hom.app X)).1
      simpa only [comp_zero] using hzero
    have hF' : F'.map (f - g) = 0 := by
      apply (cancel_mono (η.hom.app Y)).1
      rw [η.hom.naturality]
      simp only [Functor.comp_map, hq, comp_zero, zero_comp]
    have hQ : (torsionModuleProperty A).isoModSerre.Q.map
        ((finitelyGeneratedModuleInclusion A).map (f - g)) = 0 := by
      simpa [F'] using hF'
    have ht : (torsionModuleProperty A)
        (Abelian.image ((finitelyGeneratedModuleInclusion A).map (f - g))) :=
      (ObjectProperty.SerreClassLocalization.map_eq_zero_iff
        (torsionModuleProperty A).isoModSerre.Q (torsionModuleProperty A) _).1 hQ
    have ht' : finitelyGeneratedTorsionModuleProperty A
        (Abelian.image (f - g)) := by
      change (torsionModuleProperty A)
        ((finitelyGeneratedModuleInclusion A).obj (Abelian.image (f - g)))
      exact (torsionModuleProperty A).prop_of_iso
        (Abelian.PreservesImage.iso (finitelyGeneratedModuleInclusion A) (f - g)).symm ht
    rw [← sub_eq_zero, ← L'.map_sub]
    exact (ObjectProperty.SerreClassLocalization.map_eq_zero_iff L'
      (finitelyGeneratedTorsionModuleProperty A) _).2 ht'
  haveI : (finitelyGeneratedQuotientToModuleQuotient A).Faithful := hfaith
  haveI : (finitelyGeneratedQuotientToModuleQuotient A).Full :=
    finitelyGeneratedQuotientToModuleQuotient_full A
  let _ : (finitelyGeneratedQuotientToModuleQuotient A).FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful _
  let _ : H.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful H
  haveI : F.EssSurj := by
    refine ⟨fun Y ↦ ?_⟩
    letI : Module A (Y : Type u) := Module.compHom _ (algebraMap A K)
    letI : IsScalarTower A K (Y : Type u) :=
      ⟨fun a k y => by
        change (algebraMap A K a * k) • y = _
        rw [smul_smul]⟩
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' K (Y : Type u)
    let P : Submodule A (Y : Type u) :=
      Submodule.span A (Set.range f)
    letI : Module.Finite A P :=
      Module.Finite.span_of_finite A (Set.finite_range f)
    let M : finitelyGeneratedModuleCategory A :=
      ⟨ModuleCat.of A P, by change Module.Finite A P; infer_instance⟩
    let inclP : P →ₗ[A] (Y : Type u) := P.subtype
    letI : IsLocalizedModule (nonZeroDivisors A) inclP := by
      let hspan : Submodule.span K (Set.range f) = ⊤ := by
        rw [← LinearMap.range_eq_top]
        exact hf
      constructor
      · exact (isLocalizedModule_id (nonZeroDivisors A) (Y : Type u) K).map_units
      · intro y
        obtain ⟨t, ht⟩ :=
          multiple_mem_span_of_mem_localization_span
            (M := nonZeroDivisors A) (R := A) (R' := K)
            (Set.range f) y (by rw [hspan]; trivial)
        exact ⟨⟨t • y, ht⟩, t, rfl⟩
      · intro x₁ x₂ h
        refine ⟨1, ?_⟩
        apply Subtype.ext
        exact h
    let eP : (LocalizedModule (nonZeroDivisors A) (P : Type u)) ≃ₗ[
        FractionRing A] (Y : Type u) :=
      LinearEquiv.extendScalarsOfIsLocalization (nonZeroDivisors A) (FractionRing A)
        (IsLocalizedModule.iso (nonZeroDivisors A) inclP)
    let W : ModuleCat (FractionRing A) :=
      ModuleCat.of (FractionRing A) (LocalizedModule (nonZeroDivisors A) (P : Type u))
    let eW : e.functor.obj (L.obj M) ≅ W := by
      apply LinearEquiv.toModuleIso
      exact
        (Shrink.linearEquiv (FractionRing A)
          (LocalizedModule (nonZeroDivisors A) (P : Type u))).trans eP
    let J : R.functor.obj W ≅ Y.obj := by
      apply LinearEquiv.toModuleIso
      let j : (R.functor.obj W : Type u) ≃ₗ[K] (Y : Type u) :=
        { toFun := id
          invFun := id
          left_inv := by intro x; rfl
          right_inv := by intro x; rfl
          map_add' := by intro x y; rfl
          map_smul' := by
            intro k x
            change (r.symm k : FractionRing A) • x = k • x
            rw [Algebra.smul_def, Algebra.smul_def]
            simp }
      exact j
    let iY : H.obj (L.obj M) ≅ Y.obj :=
      R.mapIso eW ≪≫ J
    refine ⟨L.obj M, ⟨?__⟩⟩
    exact (ModuleCat.isFG K).isoMk iY (by infer_instance)
  let _ : F.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful F
  letI : F.IsEquivalence := by infer_instance
  exact ⟨F.asEquivalence⟩
  -/

/- The source's canonical choice of the field of fractions is Mathlib's
   `FractionRing`; the preceding theorem also permits any equivalent model. -/
theorem quotientByFinitelyGeneratedTorsionModules_equiv_fractionField
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] :
    Nonempty
      (finitelyGeneratedTorsionSerreQuotient A ≌
        finiteDimensionalVectorSpaceCategory (FractionRing A)) := by
  exact quotientByFinitelyGeneratedTorsionModules_equiv_finiteDimensional
    A (FractionRing A)

/-! ## Abelian groups modulo torsion groups -/

/-- Torsion abelian groups, viewed as `\mathbb{Z}`-modules. -/
def abelianGroupTorsionProperty :
    ObjectProperty (AddCommGrpCat.{u}) :=
  fun G => Module.IsTorsion ℤ (G : Type u)

@[simp]
theorem abelianGroupTorsionProperty_iff (G : AddCommGrpCat.{u}) :
    abelianGroupTorsionProperty G ↔ Module.IsTorsion ℤ (G : Type u) :=
  Iff.rfl

/-- Torsion abelian groups form a Serre class in `Ab`. -/
instance abelianGroupTorsionProperty_isSerreClass :
    abelianGroupTorsionProperty.{u}.IsSerreClass := by
  let e := (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence
  let L := e.inverse ⋙ ModuleCat.localizedModuleFunctor.{u} (nonZeroDivisors ℤ)
  have hzero (G : AddCommGrpCat.{u}) :
      IsZero (L.obj G) ↔ Module.IsTorsion ℤ (G : Type u) := by
    change IsZero ((ModuleCat.localizedModuleFunctor.{u} (nonZeroDivisors ℤ)).obj
      ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence.inverse.obj G)) ↔
      Module.IsTorsion ℤ (G : Type u)
    change IsZero (ModuleCat.localizedModule
      ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence.inverse.obj G)
      (nonZeroDivisors ℤ)) ↔
      Module.IsTorsion ℤ (G : Type u)
    rw [ModuleCat.isZero_iff_subsingleton]
    change Subsingleton (Shrink.{u}
      (LocalizedModule (nonZeroDivisors ℤ) (e.inverse.obj G : Type u))) ↔ _
    have hlocal : Subsingleton (LocalizedModule (nonZeroDivisors ℤ)
        (e.inverse.obj G : Type u)) ↔
        Module.IsTorsion ℤ (e.inverse.obj G : Type u) := by
      rw [LocalizedModule.subsingleton_iff]
      constructor
      · intro h x
        obtain ⟨r, hr, hx⟩ := @h x
        refine ⟨⟨r, hr⟩, ?_⟩
        simpa only [Submonoid.smul_def] using hx
      · intro h x
        obtain ⟨a, ha⟩ := @h x
        exact ⟨a, a.property, by simpa only [Submonoid.smul_def] using ha⟩
    let E : (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).obj
        (e.inverse.obj G) ≅ G := e.counitIso.app G
    let N : ModuleCat.{u} ℤ := ModuleCat.of ℤ (G : Type u)
    let j : (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).obj N ≅ G :=
      Iso.refl _
    obtain ⟨u, hu⟩ :=
      (ModuleCat.forget₂_addCommGroup_full.map_surjective (E.hom ≫ j.inv))
    obtain ⟨v, hv⟩ :=
      (ModuleCat.forget₂_addCommGroup_full.map_surjective (j.hom ≫ E.inv))
    have huv : u ≫ v = 𝟙 _ := by
      apply (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).map_injective
      rw [Functor.map_comp, hu, hv]
      simp
      ext x
      rfl
    have hvu : v ≫ u = 𝟙 _ := by
      apply (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).map_injective
      rw [Functor.map_comp, hv, hu]
      simp
      ext x
      rfl
    have huv_apply (x : e.inverse.obj G) : v.hom (u.hom x) = x := by
      have h := congrArg (fun f : (e.inverse.obj G) ⟶ e.inverse.obj G => f.hom x) huv
      simpa using h
    have hvu_apply (x : N) : u.hom (v.hom x) = x := by
      have h := congrArg (fun f : N ⟶ N => f.hom x) hvu
      simpa using h
    have htorsion : Module.IsTorsion ℤ (e.inverse.obj G : Type u) ↔
        Module.IsTorsion ℤ (N : Type u) := by
      constructor
      · intro h x
        obtain ⟨a, ha⟩ := @h (v.hom x)
        refine ⟨a, ?_⟩
        have ha' : AddCommGrpCat.Hom.hom ((e.inverse.obj G).smul (a : ℤ)) (v.hom x) = 0 := by
          exact ha
        have hu_smul : AddCommGrpCat.Hom.hom (N.smul (a : ℤ)) x =
            u.hom (AddCommGrpCat.Hom.hom ((e.inverse.obj G).smul (a : ℤ)) (v.hom x)) := by
          have h1 : AddCommGrpCat.Hom.hom (N.smul (a : ℤ)) (u.hom (v.hom x)) =
              u.hom (AddCommGrpCat.Hom.hom
                ((e.inverse.obj G).smul (a : ℤ)) (v.hom x)) := by
            have hnat := congrArg (fun f => f (v.hom x))
              (ModuleCat.smul_naturality u (a : ℤ))
            change AddCommGrpCat.Hom.hom (N.smul (a : ℤ)) (u.hom (v.hom x)) =
              u.hom (AddCommGrpCat.Hom.hom
                ((e.inverse.obj G).smul (a : ℤ)) (v.hom x)) at hnat
            exact hnat
          exact (congrArg (fun y => AddCommGrpCat.Hom.hom (N.smul (a : ℤ)) y)
            (hvu_apply x).symm).trans h1
        change AddCommGrpCat.Hom.hom (N.smul (a : ℤ)) x = 0
        rw [hu_smul, ha', u.hom.map_zero]
      · intro h x
        obtain ⟨a, ha⟩ := @h (u.hom x)
        refine ⟨a, ?_⟩
        have ha' : AddCommGrpCat.Hom.hom (N.smul (a : ℤ)) (u.hom x) = 0 := by
          exact ha
        have hv_smul : AddCommGrpCat.Hom.hom ((e.inverse.obj G).smul (a : ℤ)) x =
            v.hom (AddCommGrpCat.Hom.hom (N.smul (a : ℤ)) (u.hom x)) := by
          have h1 : AddCommGrpCat.Hom.hom ((e.inverse.obj G).smul (a : ℤ))
                (v.hom (u.hom x)) =
              v.hom (AddCommGrpCat.Hom.hom (N.smul (a : ℤ)) (u.hom x)) := by
            have hnat := congrArg (fun f => f (u.hom x))
              (ModuleCat.smul_naturality v (a : ℤ))
            change AddCommGrpCat.Hom.hom ((e.inverse.obj G).smul (a : ℤ))
                (v.hom (u.hom x)) =
              v.hom (AddCommGrpCat.Hom.hom (N.smul (a : ℤ)) (u.hom x)) at hnat
            exact hnat
          exact (congrArg (fun y => AddCommGrpCat.Hom.hom
            ((e.inverse.obj G).smul (a : ℤ)) y) (huv_apply x).symm).trans h1
        change AddCommGrpCat.Hom.hom ((e.inverse.obj G).smul (a : ℤ)) x = 0
        rw [hv_smul, ha', v.hom.map_zero]
    exact (Equiv.subsingleton_congr
      (equivShrink (LocalizedModule (nonZeroDivisors ℤ)
        (e.inverse.obj G : Type u)))).symm.trans
      (hlocal.trans htorsion)
  have hP : abelianGroupTorsionProperty.{u} =
      ObjectProperty.inverseImage (IsZero (C := ModuleCat (Localization (nonZeroDivisors ℤ)))) L := by
    ext G
    exact (hzero G).symm
  rw [hP]
  let _ : PreservesFiniteLimits L := comp_preservesFiniteLimits _ _
  let _ : PreservesFiniteColimits L := comp_preservesFiniteColimits _ _
  infer_instance

abbrev abelianGroupTorsionSerreQuotient :=
  abelianGroupTorsionProperty.{u}.isoModSerre.Localization

/-- The canonical equivalence between `\mathbb{Z}`-modules and abelian groups. -/
noncomputable def zModuleToAbelianGroupEquivalence :
    ModuleCat.{u} ℤ ≌ AddCommGrpCat.{u} :=
  (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence

/-- The fraction ring of `\mathbb{Z}` is canonically the field of rationals. -/
noncomputable def integerFractionRingEquivRationals :
    FractionRing ℤ ≃+* ℚ :=
  (FractionRing.algEquiv ℤ ℚ).toRingEquiv

/-- The localization functor sends an abelian group to its rationalization. -/
noncomputable def abelianGroupToRationalVectorSpace :
    AddCommGrpCat.{u} ⥤ ModuleCat.{u} ℚ :=
  zModuleToAbelianGroupEquivalence.{u}.inverse ⋙
    ModuleCat.localizedModuleFunctor.{u} (nonZeroDivisors ℤ) ⋙
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (integerFractionRingEquivRationals)).symm.functor

theorem abelianGroupToRationalVectorSpace_isLocalization :
    abelianGroupToRationalVectorSpace.{u}.IsLocalization
      abelianGroupTorsionProperty.{u}.isoModSerre := by
  sorry

/-- The Serre quotient of abelian groups by torsion groups is rational vector spaces. -/
noncomputable def quotientAbelianGroupsByTorsionGroupsEquivalence :
    abelianGroupTorsionSerreQuotient.{u} ≌ ModuleCat.{u} ℚ := by
  letI := abelianGroupToRationalVectorSpace_isLocalization.{u}
  exact CategoryTheory.Localization.uniq
    abelianGroupTorsionProperty.{u}.isoModSerre.Q
    abelianGroupToRationalVectorSpace.{u}
    abelianGroupTorsionProperty.{u}.isoModSerre

theorem quotientAbelianGroupsByTorsionGroups_equiv_rationalVectorSpaces :
    Nonempty (abelianGroupTorsionSerreQuotient.{u} ≌ ModuleCat.{u} ℚ) :=
  ⟨quotientAbelianGroupsByTorsionGroupsEquivalence.{u}⟩

end Formalization.Books.Examples.Unit79
