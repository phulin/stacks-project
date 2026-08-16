import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Localization
import Mathlib.Algebra.Module.Torsion.Basic
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
  sorry

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
  sorry

/- The proposition-level interface records that the canonical functor is a
   localization for the Serre quotient. -/
theorem moduleLocalizationFunctor_isLocalization (A : Type u) [CommRing A]
    (S : Submonoid A) :
    (moduleLocalizationFunctor A S).IsLocalization
      (sTorsionModuleProperty A S).isoModSerre := by
  sorry

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
  sorry

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
