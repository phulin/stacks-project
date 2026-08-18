import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Formalization.Books.Derived.Unit30.DerivingAdjoints
import Formalization.Books.MoreAlgebra.Unit87

/-!
# More on Algebra, Chapter 88: Rlim of modules

This file records the definitions and theorem interfaces in the section on
derived inverse limits of modules.  The module systems themselves use
Mathlib's canonical `PresheafOfModules` construction, so that the scalar
restriction in each transition map is part of the object rather than an
extra convention.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Formalization.Books.MoreAlgebra.Unit87
open Formalization.Books.Derived.Unit30
open scoped BigOperators CategoryTheory.Pretriangulated.Opposite ZeroObject

universe u v w z

namespace Formalization.Books.MoreAlgebra.Unit88

/-! ## 88.1. The category of modules over an inverse system of rings -/

/-- An inverse system of rings indexed by the opposite of `ℕ`. -/
abbrev RingInverseSystem := ℕᵒᵖ ⥤ RingCat.{u}

/-- The source's category `Mod(ℕ, (Aₙ))`.

`PresheafOfModules` is Mathlib's canonical category of modules over a
presheaf of rings.  Its restriction maps are precisely semilinear maps along
the transition ring homomorphisms `Aₙ₊₁ → Aₙ`.
-/
abbrev ModuleInverseSystem (A : RingInverseSystem.{u}) :=
  PresheafOfModules.{v} A

/-- The inverse limit ring of a system of rings. -/
abbrev inverseLimitRing (A : RingInverseSystem.{u}) : RingCat.{u} :=
  limit A

/-- Data for the inverse-limit functor on module systems.  Its object part is
the compatible-family module, with scalar action induced by the projections
`lim Aₙ → Aₙ`; the categorical construction is recorded as an existence
interface because Mathlib does not yet bundle presheaves of modules over a
varying ring as a complete category. -/
structure ModuleLimitFunctorData (A : RingInverseSystem.{u}) where
  functor : ModuleInverseSystem.{u, v} A ⥤ ModuleCat.{v} (inverseLimitRing A)

/-- The inverse-limit module functor exists. -/
theorem exists_inverseLimitModuleFunctor (A : RingInverseSystem.{u}) :
    Nonempty (ModuleLimitFunctorData A) := by
  sorry

/-- The inverse limit module attached to a module system. -/
noncomputable def moduleLimit
    (A : RingInverseSystem.{u}) (M : ModuleInverseSystem.{u, v} A) :
    ModuleCat (inverseLimitRing A) :=
  (Classical.choice (exists_inverseLimitModuleFunctor A)).functor.obj M

/-- The chosen inverse-limit functor on module systems. -/
noncomputable def inverseLimitModuleFunctor
    (A : RingInverseSystem.{u}) :
    ModuleInverseSystem.{u, v} A ⥤ ModuleCat.{v} (inverseLimitRing A) :=
  (Classical.choice (exists_inverseLimitModuleFunctor A)).functor

/-- The chosen limit module has the compatible-family description from the
source. -/
theorem moduleLimit_is_compatibleFamilyModule
    (A : RingInverseSystem.{u}) (M : ModuleInverseSystem.{u, v} A) :
    Nonempty ((moduleLimit A M : Type v) ≃ M.sections) := by
  sorry

/-! The source states that this category is abelian and has the usual derived
category.  Mathlib supplies the category and preadditive structure of
`PresheafOfModules`; the remaining existence interfaces are recorded here so
the later declarations can use the source's derived-category notation. -/

noncomputable instance moduleInverseSystemAbelian
    (A : RingInverseSystem.{u}) : Abelian (ModuleInverseSystem.{u, v} A) := by
  sorry

noncomputable instance moduleInverseSystemHasDerivedCategory
    (A : RingInverseSystem.{u}) :
    HasDerivedCategory (ModuleInverseSystem.{u, v} A) := by
  exact HasDerivedCategory.standard _

noncomputable instance moduleCatHasDerivedCategory
    (R : Type u) [Ring R] : HasDerivedCategory (ModuleCat.{v} R) := by
  exact HasDerivedCategory.standard _

noncomputable instance moduleInverseSystemHasInjectiveResolutions
    (A : RingInverseSystem.{u}) :
    HasInjectiveResolutions (ModuleInverseSystem.{u, v} A) := by
  sorry

noncomputable instance inverseLimitModuleFunctorAdditive
    (A : RingInverseSystem.{u}) :
    (inverseLimitModuleFunctor (A := A)).Additive := by
  sorry

/-- The derived category of module systems over `A`. -/
abbrev DerivedModuleInverseSystem (A : RingInverseSystem.{u}) :=
  DerivedCategory (ModuleInverseSystem.{u, v} A)

/-! ## 88.2. Computing `Rlim` -/

/-- The right-derived inverse-limit functor on module systems. -/
noncomputable abbrev derivedLimitFunctorModules
    (A : RingInverseSystem.{u}) (p : ℕ) :
    ModuleInverseSystem.{u, v} A ⥤ ModuleCat.{v} (inverseLimitRing A) :=
  letI := inverseLimitModuleFunctorAdditive (A := A)
  (inverseLimitModuleFunctor (A := A)).rightDerived p

/-- The `p`-th derived inverse limit of a module system. -/
noncomputable abbrev derivedLimitModule
    (A : RingInverseSystem.{u}) (M : ModuleInverseSystem.{u, v} A) (p : ℕ) :
    ModuleCat.{v} (inverseLimitRing A) :=
  (derivedLimitFunctorModules A p).obj M

/-- The first derived inverse limit of a module system. -/
noncomputable abbrev firstDerivedLimitModule
    (A : RingInverseSystem.{u}) (M : ModuleInverseSystem.{u, v} A) :
    ModuleCat.{v} (inverseLimitRing A) :=
  derivedLimitModule A M 1

/-- Right acyclicity for inverse limit means vanishing of all positive derived
limits. -/
def IsRightAcyclicForModuleLimit
    (A : RingInverseSystem.{u}) (M : ModuleInverseSystem.{u, v} A) : Prop :=
  ∀ p : ℕ, 0 < p → IsZero (derivedLimitModule A M p)

/-- The source's first-derived-limit vanishing condition. -/
abbrev FirstDerivedLimitModuleVanishing
    (A : RingInverseSystem.{u}) (M : ModuleInverseSystem.{u, v} A) : Prop :=
  IsZero (firstDerivedLimitModule A M)

/-- The Mittag--Leffler condition on the underlying inverse system of modules. -/
abbrev IsMittagLefflerModuleSystem
    (M : ModuleInverseSystem.{u, v} A) : Prop :=
  (M.presheaf ⋙ forget Ab).IsMittagLeffler

/-- The map `1 - f` on the product of the terms of a module system. -/
noncomputable def moduleInverseLimitDifferenceMap
    (A : RingInverseSystem.{u}) (M : ModuleInverseSystem.{u, v} A)
    [HasProduct (fun n : ℕ =>
      (ModuleCat.restrictScalars (limit.π A (Opposite.op n)).hom).obj
        (M.obj (Opposite.op n)))] :
    (∏ᶜ fun n : ℕ =>
      (ModuleCat.restrictScalars (limit.π A (Opposite.op n)).hom).obj
        (M.obj (Opposite.op n))) ⟶
      (∏ᶜ fun n : ℕ =>
        (ModuleCat.restrictScalars (limit.π A (Opposite.op n)).hom).obj
          (M.obj (Opposite.op n))) := by
  sorry

/-- A complex is a two-term presentation of the standard module `Rlim`
complex when its differential is `1 - f`. -/
def IsTwoTermModuleRlimRepresentation
    (A : RingInverseSystem.{u}) (M : ModuleInverseSystem.{u, v} A)
    (K : CochainComplex (ModuleCat (inverseLimitRing A)) ℤ)
    [HasProduct (fun n : ℕ =>
      (ModuleCat.restrictScalars (limit.π A (Opposite.op n)).hom).obj
        (M.obj (Opposite.op n)))] : Prop :=
  (∀ p : ℤ, p ≠ 0 → p ≠ 1 → IsZero (K.X p)) ∧
    ∃ (e₀ : K.X 0 ≅ ∏ᶜ fun n : ℕ =>
        (ModuleCat.restrictScalars (limit.π A (Opposite.op n)).hom).obj
          (M.obj (Opposite.op n)))
      (e₁ : K.X 1 ≅ ∏ᶜ fun n : ℕ =>
        (ModuleCat.restrictScalars (limit.π A (Opposite.op n)).hom).obj
          (M.obj (Opposite.op n))),
      K.d 0 1 ≫ e₁.hom = e₀.hom ≫ moduleInverseLimitDifferenceMap A M

/-- A chosen unbounded right-derived functor of inverse limit on the derived
category of module systems. -/
theorem exists_moduleLimit_rightDerivedFunctor
    (A : RingInverseSystem.{u}) :
    ∃ RF : DerivedModuleInverseSystem.{u, v} A ⥤
        DerivedCategory (ModuleCat (inverseLimitRing A)),
      IsUnboundedRightDerivedFunctor (inverseLimitModuleFunctor (A := A)) RF := by
  sorry

/-- The cohomology object of a chosen derived inverse-limit functor. -/
noncomputable abbrev moduleRlimCohomology
    (A : RingInverseSystem.{u})
    (RF : DerivedModuleInverseSystem.{u, v} A ⥤
      DerivedCategory (ModuleCat (inverseLimitRing A)))
    (K : DerivedModuleInverseSystem.{u, v} A) (p : ℤ) :
    ModuleCat (inverseLimitRing A) :=
  (DerivedCategory.homologyFunctor (ModuleCat (inverseLimitRing A)) p).obj (RF.obj K)

/-- Higher derived inverse limits of module systems vanish above degree one. -/
theorem moduleRlim_higher_vanishes
    (A : RingInverseSystem.{u}) (M : ModuleInverseSystem.{u, v} A) (p : ℕ)
    (hp : 1 < p) : IsZero (derivedLimitModule A M p) := by
  sorry

/-- A Mittag--Leffler module system is right acyclic for inverse limit. -/
theorem moduleRlim_MittagLeffler_is_rightAcyclic
    (A : RingInverseSystem.{u}) (M : ModuleInverseSystem.{u, v} A)
    (hM : IsMittagLefflerModuleSystem M) :
    IsRightAcyclicForModuleLimit A M := by
  sorry

/-- The standard two-term complex represents the derived inverse limit of a
module system. -/
theorem moduleRlim_two_term_representation
    (A : RingInverseSystem.{u}) (M : ModuleInverseSystem.{u, v} A)
    [HasProduct (fun n : ℕ =>
      (ModuleCat.restrictScalars (limit.π A (Opposite.op n)).hom).obj
        (M.obj (Opposite.op n)))] :
    ∃ K : CochainComplex (ModuleCat (inverseLimitRing A)) ℤ,
      IsTwoTermModuleRlimRepresentation A M K := by
  sorry

/-- Every derived module-system object has a representative with
right-acyclic terms. -/
theorem exists_rightAcyclic_moduleRepresentative
    (A : RingInverseSystem.{u}) (K : DerivedModuleInverseSystem.{u, v} A) :
    ∃ L : CochainComplex (ModuleInverseSystem.{u, v} A) ℤ,
      Nonempty
        (K ≅
          (DerivedCategory.Q : CochainComplex (ModuleInverseSystem.{u, v} A) ℤ ⥤
            DerivedModuleInverseSystem.{u, v} A).obj L) ∧
        ∀ p : ℤ, IsRightAcyclicForModuleLimit A (L.X p) := by
  sorry

/-- If every term is right acyclic, the termwise inverse-limit complex
computes the derived inverse limit. -/
theorem moduleRlim_of_rightAcyclic_terms
    (A : RingInverseSystem.{u}) (K : CochainComplex (ModuleInverseSystem.{u, v} A) ℤ)
    (hK : ∀ p : ℤ, IsRightAcyclicForModuleLimit A (K.X p)) :
    Nonempty
      ((DerivedCategory.Q : CochainComplex (ModuleCat (inverseLimitRing A)) ℤ ⥤
          DerivedCategory (ModuleCat (inverseLimitRing A))).obj
        (by sorry) ≅
        (by sorry)) := by
  sorry
