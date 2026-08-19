import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Localization
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.CategoryTheory.Abelian.SerreClass.Bousfield
import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
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
        letI : Module A (X'.localizedModule S : Type u) :=
          by infer_instance
        letI : Module A (Y : Type u) :=
          Module.compHom _ (algebraMap A (Localization S))
        letI : IsScalarTower A (Localization S) (X'.localizedModule S : Type u) :=
          by infer_instance
        letI : IsScalarTower A (Localization S) (Y : Type u) :=
          IsScalarTower.of_compHom A (Localization S) _
        letI : IsLocalizedModule S (LinearMap.id : (Y : Type u) →ₗ[A] (Y : Type u)) :=
          isLocalizedModule_id S (Y : Type u) (Localization S)
        letI : Module A ((ModuleCat.restrictScalars (algebraMap A (Localization S))).obj Y : Type u) :=
          ((ModuleCat.restrictScalars (algebraMap A (Localization S))).obj Y).isModule
        letI : IsScalarTower A (Localization S)
            ((ModuleCat.restrictScalars (algebraMap A (Localization S))).obj Y : Type u) :=
          IsScalarTower.of_compHom A (Localization S) _
        letI : IsLocalizedModule S
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
          LinearMap.extendScalarsOfIsLocalizationEquiv, IsLocalizedModule.map_comp',
          ModuleCat.localizedModuleFunctor]
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
        letI : Module A ((moduleLocalizationFunctor A S).obj X : Type u) :=
          Module.compHom _ (algebraMap A (Localization S))
        letI : IsScalarTower A (Localization S)
            ((moduleLocalizationFunctor A S).obj X : Type u) :=
          IsScalarTower.of_compHom A (Localization S) _
        letI : Module A ((ModuleCat.localizedModuleFunctor S).obj X : Type u) :=
          Module.compHom _ (algebraMap A (Localization S))
        letI : Module A (Y : Type u) :=
          Module.compHom _ (algebraMap A (Localization S))
        letI : Module A (Y' : Type u) :=
          Module.compHom _ (algebraMap A (Localization S))
        letI : IsScalarTower A (Localization S)
            ((ModuleCat.localizedModuleFunctor S).obj X : Type u) :=
          IsScalarTower.of_compHom A (Localization S) _
        letI : IsScalarTower A (Localization S) (Y : Type u) :=
          IsScalarTower.of_compHom A (Localization S) _
        letI : IsScalarTower A (Localization S) (Y' : Type u) :=
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
    letI : Module A ((ModuleCat.restrictScalars (algebraMap A (Localization S))).obj X : Type u) :=
      ((ModuleCat.restrictScalars (algebraMap A (Localization S))).obj X).isModule
    letI : Module A ((ModuleCat.restrictScalars (algebraMap A (Localization S))).obj Y : Type u) :=
      ((ModuleCat.restrictScalars (algebraMap A (Localization S))).obj Y).isModule
    letI : IsScalarTower A (Localization S)
        ((ModuleCat.restrictScalars (algebraMap A (Localization S))).obj X : Type u) :=
      IsScalarTower.of_compHom A (Localization S) _
    letI : IsScalarTower A (Localization S)
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
  sorry

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

/- The main finite-dimensionality statement records the source's restriction
   of the total-quotient equivalence to finitely generated modules. -/
theorem quotientByFinitelyGeneratedTorsionModules_equiv_finiteDimensional
    (A K : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] :
    Nonempty
      (finitelyGeneratedTorsionSerreQuotient A ≌
        finiteDimensionalVectorSpaceCategory K) := by
  sorry

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
  sorry

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
