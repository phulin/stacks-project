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
    (inverseLimitModuleFunctor.{u, v} A).Additive := by
  sorry

noncomputable instance moduleInverseSystemHasInjectiveResolutionsExplicit
    (A : RingInverseSystem.{u}) :
    HasInjectiveResolutions (ModuleInverseSystem.{u, v} A) :=
  moduleInverseSystemHasInjectiveResolutions (A := A)

/-- The derived category of module systems over `A`. -/
abbrev DerivedModuleInverseSystem (A : RingInverseSystem.{u}) :=
  DerivedCategory (ModuleInverseSystem.{u, v} A)

/-- A chosen localization functor from complexes of module systems to their
derived category.  This is the source-facing quotient functor; packaging it
separately keeps the chosen abelian-category instance explicit. -/
structure ModuleSystemDerivedQuotientData (A : RingInverseSystem.{u}) where
  Q : CochainComplex (ModuleInverseSystem.{u, v} A) ℤ ⥤
    DerivedModuleInverseSystem.{u, v} A

theorem exists_moduleSystemDerivedQuotientData (A : RingInverseSystem.{u}) :
    Nonempty (ModuleSystemDerivedQuotientData.{u, v} A) := by
  sorry

noncomputable def moduleSystemDerivedQuotient (A : RingInverseSystem.{u}) :
    CochainComplex (ModuleInverseSystem.{u, v} A) ℤ ⥤
      DerivedModuleInverseSystem.{u, v} A :=
  (Classical.choice (exists_moduleSystemDerivedQuotientData A)).Q

/-- A chosen localization functor for complexes of modules over the limit
ring. -/
structure ModuleDerivedQuotientData (A : RingInverseSystem.{u}) where
  Q : CochainComplex (ModuleCat.{v} (inverseLimitRing A)) ℤ ⥤
    DerivedCategory (ModuleCat.{v} (inverseLimitRing A))

theorem exists_moduleDerivedQuotientData (A : RingInverseSystem.{u}) :
    Nonempty (ModuleDerivedQuotientData.{u, v} A) := by
  sorry

noncomputable def moduleDerivedQuotient (A : RingInverseSystem.{u}) :
    CochainComplex (ModuleCat.{v} (inverseLimitRing A)) ℤ ⥤
      DerivedCategory (ModuleCat.{v} (inverseLimitRing A)) :=
  (Classical.choice (exists_moduleDerivedQuotientData A)).Q

/-! ## 88.2. Computing `Rlim` -/

/-- The right-derived inverse-limit functor on module systems. -/
noncomputable abbrev derivedLimitFunctorModules
    (A : RingInverseSystem.{u}) (p : ℕ) :
    ModuleInverseSystem.{u, v} A ⥤ ModuleCat.{v} (inverseLimitRing A) :=
  by
    sorry
/-
  letI := moduleInverseSystemHasInjectiveResolutionsExplicit (A := A)
  letI := inverseLimitModuleFunctorAdditive (A := A)
  (inverseLimitModuleFunctor.{u, v} A).rightDerived p
-/

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
structure ModuleInverseLimitRestrictedSystemData
    (A : RingInverseSystem.{u}) (M : ModuleInverseSystem.{u, v} A)
    where
  map {X Y : ℕᵒᵖ} (f : X ⟶ Y) :
    (ModuleCat.restrictScalars (limit.π A X).hom).obj (M.obj X) ⟶
      (ModuleCat.restrictScalars (limit.π A Y).hom).obj (M.obj Y)
  map_id (X : ℕᵒᵖ) : map (𝟙 X) = 𝟙 _
  map_comp {X Y Z : ℕᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) = map f ≫ map g

theorem exists_moduleInverseLimitRestrictedSystemData
    (A : RingInverseSystem.{u}) (M : ModuleInverseSystem.{u, v} A)
    : Nonempty (ModuleInverseLimitRestrictedSystemData A M) := by
  sorry

noncomputable def restrictedModuleSystem
    (A : RingInverseSystem.{u}) (M : ModuleInverseSystem.{u, v} A) :
    ℕᵒᵖ ⥤ ModuleCat (inverseLimitRing A) :=
  let D := Classical.choice (exists_moduleInverseLimitRestrictedSystemData A M)
  { obj := fun X =>
      (ModuleCat.restrictScalars (limit.π A X).hom).obj (M.obj X)
    map := D.map
    map_id := D.map_id
    map_comp := D.map_comp }

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
          (M.obj (Opposite.op n))) :=
  by
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

/-
theorem exists_moduleLimit_rightDerivedFunctor
    (A : RingInverseSystem.{u}) :
    letI : (inverseLimitModuleFunctor.{u, v} A).Additive :=
      inverseLimitModuleFunctorAdditive (A := A)
    ∃ RF : DerivedModuleInverseSystem.{u, v} A ⥤
        DerivedCategory (ModuleCat (inverseLimitRing A)),
      IsUnboundedRightDerivedFunctor (inverseLimitModuleFunctor.{u, v} A) RF := by
  dsimp
  sorry
-/

/-- A chosen derived inverse-limit functor. -/
noncomputable def moduleRlimFunctor (A : RingInverseSystem.{u}) :
    DerivedModuleInverseSystem.{u, v} A ⥤
      DerivedCategory (ModuleCat.{v} (inverseLimitRing A)) :=
  by
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

/-
theorem moduleRlim_two_term_representation
    (A : RingInverseSystem.{u}) (M : ModuleInverseSystem.{u, v} A)
    [HasProduct (fun n : ℕ =>
      (ModuleCat.restrictScalars (limit.π A (Opposite.op n)).hom).obj
        (M.obj (Opposite.op n)))] :
    ∃ K : CochainComplex (ModuleCat (inverseLimitRing A)) ℤ,
      IsTwoTermModuleRlimRepresentation A M K ∧
        Nonempty
          ((moduleDerivedQuotient A).obj K ≅
            moduleRlimFunctor A
              ((DerivedCategory.singleFunctor (ModuleInverseSystem A) 0).obj M)) := by
  sorry

/-- Every derived module-system object has a representative with
right-acyclic terms. -/
theorem exists_rightAcyclic_moduleRepresentative
    (A : RingInverseSystem.{u}) (K : DerivedModuleInverseSystem.{u, v} A) :
    ∃ L : CochainComplex (ModuleInverseSystem.{u, v} A) ℤ,
      Nonempty
        (K ≅
          (moduleSystemDerivedQuotient A).obj L) ∧
        ∀ p : ℤ, IsRightAcyclicForModuleLimit A (L.X p) := by
  sorry

/-- If every term is right acyclic, the termwise inverse-limit complex
computes the derived inverse limit. -/
theorem moduleRlim_of_rightAcyclic_terms
    (A : RingInverseSystem.{u}) (K : CochainComplex (ModuleInverseSystem.{u, v} A) ℤ)
    (hK : ∀ p : ℤ, IsRightAcyclicForModuleLimit A (K.X p)) :
    Nonempty
      ((moduleDerivedQuotient A).obj
        ((inverseLimitModuleFunctor.{u, v} A).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K ≅
        moduleRlimFunctor A ((moduleSystemDerivedQuotient A).obj K)) := by
  sorry

/-- The global-sections description of the module limit in the source's
chaotic-site interpretation. -/
abbrev moduleSystemGlobalSections
    (M : ModuleInverseSystem.{u, v} A) := M.sections

theorem moduleSystemGlobalSections_is_moduleLimit
    (A : RingInverseSystem.{u}) (M : ModuleInverseSystem.{u, v} A) :
    Nonempty ((moduleLimit A M : Type v) ≃ moduleSystemGlobalSections M) := by
  exact moduleLimit_is_compatibleFamilyModule A M

/-- A module system is the same object as a module sheaf on the natural
number line with its chaotic topology; its global sections are inverse limit. -/
theorem moduleSystem_chaoticSite_identification
    (A : RingInverseSystem.{u}) (M : ModuleInverseSystem.{u, v} A) :
    Nonempty ((moduleLimit A M : Type v) ≃ M.sections) := by
  exact moduleLimit_is_compatibleFamilyModule A M

/-! ## 88.3. Cohomology and derived-system presentations -/

/-- The inverse system of cohomology modules in a fixed degree. -/
noncomputable def moduleCohomologySystem
    (A : RingInverseSystem.{u})
    (K : CochainComplex (ModuleInverseSystem.{u, v} A) ℤ) (p : ℤ) :
    ModuleInverseSystem.{u, v} A :=
  (HomologicalComplex.homologyFunctor (ModuleInverseSystem.{u, v} A)
      (ComplexShape.up ℤ) p).obj K

/-- The short exact cohomology window for the derived inverse limit of a
complex of module systems. -/
def ModuleRlimCohomologyExactSequence
    (A : RingInverseSystem.{u})
    (K : CochainComplex (ModuleInverseSystem.{u, v} A) ℤ)
    (L : DerivedCategory (ModuleCat (inverseLimitRing A))) (p : ℤ)
    (_hL : Nonempty
      (L ≅ moduleRlimFunctor A ((moduleSystemDerivedQuotient A).obj K))) : Prop :=
  ∃ α : firstDerivedLimitModule A (moduleCohomologySystem A K (p - 1)) ⟶
      (DerivedCategory.homologyFunctor (ModuleCat (inverseLimitRing A)) p).obj L,
    ∃ β : (DerivedCategory.homologyFunctor (ModuleCat (inverseLimitRing A)) p).obj L ⟶
      moduleLimit A (moduleCohomologySystem A K p),
    (ComposableArrows.mk₄
        (0 : (0 : ModuleCat (inverseLimitRing A)) ⟶
          firstDerivedLimitModule A (moduleCohomologySystem A K (p - 1)))
        α β
        (0 : moduleLimit A (moduleCohomologySystem A K p) ⟶
          (0 : ModuleCat (inverseLimitRing A)))).Exact

/-- The cohomology long exact sequence breaks into the source's short exact
sequences. -/
theorem moduleRlim_break_long_exact_sequence
    (A : RingInverseSystem.{u})
    (K : CochainComplex (ModuleInverseSystem.{u, v} A) ℤ)
    (L : DerivedCategory (ModuleCat (inverseLimitRing A)))
    (hL : Nonempty
      (L ≅ moduleRlimFunctor A ((moduleSystemDerivedQuotient A).obj K)))
    (p : ℤ) : ModuleRlimCohomologyExactSequence A K L p hL := by
  sorry

/-- Derived restriction of scalars along the transition
`A_(n+1) → A_n`. -/
structure DerivedModuleStageRestrictionData
    (A : RingInverseSystem.{u}) (n : ℕ) where
  functor : DerivedCategory (ModuleCat (A.obj (Opposite.op n))) ⥤
    DerivedCategory (ModuleCat (A.obj (Opposite.op (n + 1))))

theorem exists_derivedModuleStageRestrictionData
    (A : RingInverseSystem.{u}) (n : ℕ) :
    Nonempty (DerivedModuleStageRestrictionData A n) := by
  sorry

noncomputable def derivedModuleStageRestriction
    (A : RingInverseSystem.{u}) (n : ℕ) :
    DerivedCategory (ModuleCat (A.obj (Opposite.op n))) ⥤
      DerivedCategory (ModuleCat (A.obj (Opposite.op (n + 1)))) :=
  (Classical.choice (exists_derivedModuleStageRestrictionData A n)).functor

/-- An inverse system of derived objects over the varying rings `A_n`, with
the transition map viewed over `A_(n+1)`. -/
structure DerivedModuleStageSystem (A : RingInverseSystem.{u}) where
  stage : ∀ n : ℕ, DerivedCategory (ModuleCat (A.obj (Opposite.op n)))
  transition : ∀ n : ℕ,
    stage (n + 1) ⟶ (derivedModuleStageRestriction A n).obj (stage n)

/- The pointwise evaluation of a derived module-system object, together with
its transition morphisms, is an interface because the exact derived
evaluation functor is not bundled by Mathlib for `PresheafOfModules`. -/
structure DerivedModuleStageEvaluationData
    (A : RingInverseSystem.{u}) where
  functor : ∀ n : ℕ,
    DerivedModuleInverseSystem.{u, v} A ⥤
      DerivedCategory (ModuleCat (A.obj (Opposite.op n)))
  transition : ∀ (n : ℕ) (K : DerivedModuleInverseSystem.{u, v} A),
    (functor (n + 1)).obj K ⟶
      (derivedModuleStageRestriction A n).obj ((functor n).obj K)

theorem exists_derivedModuleStageEvaluationData
    (A : RingInverseSystem.{u}) :
    Nonempty (DerivedModuleStageEvaluationData A) := by
  sorry

noncomputable def derivedModuleStageEvaluationData
    (A : RingInverseSystem.{u}) : DerivedModuleStageEvaluationData A :=
  Classical.choice (exists_derivedModuleStageEvaluationData A)

noncomputable def derivedModuleStageEvaluation
    (A : RingInverseSystem.{u}) (n : ℕ) :
    DerivedModuleInverseSystem.{u, v} A ⥤
      DerivedCategory (ModuleCat (A.obj (Opposite.op n))) :=
  (derivedModuleStageEvaluationData A).functor n

noncomputable def derivedModuleStageTransition
    (A : RingInverseSystem.{u}) (n : ℕ)
    (K : DerivedModuleInverseSystem.{u, v} A) :
    (derivedModuleStageEvaluation A (n + 1)).obj K ⟶
      (derivedModuleStageRestriction A n).obj
        ((derivedModuleStageEvaluation A n).obj K) :=
  (derivedModuleStageEvaluationData A).transition n K

/-- A compatible lift of a varying-ring system of derived objects to an
object of the derived category of module systems. -/
structure DerivedModuleStageSystemLift
    (A : RingInverseSystem.{u}) (S : DerivedModuleStageSystem A) where
  object : DerivedModuleInverseSystem.{u, v} A
  complex : CochainComplex (ModuleInverseSystem.{u, v} A) ℤ
  objectIso : Nonempty (object ≅ (moduleSystemDerivedQuotient A).obj complex)
  stageIso : ∀ n : ℕ,
    (derivedModuleStageEvaluation A n).obj object ≅ S.stage n
  compatible : ∀ n : ℕ,
    derivedModuleStageTransition A n object ≫
        (derivedModuleStageRestriction A n).map (stageIso n).hom =
      (stageIso (n + 1)).hom ≫ S.transition n

/-- Every compatible varying-ring derived system admits a lift to a derived
object represented by a system of complexes. -/
theorem exists_derivedModuleStageSystemLift
    (A : RingInverseSystem.{u}) (S : DerivedModuleStageSystem A) :
    Nonempty (DerivedModuleStageSystemLift A S) := by
  sorry

/-- A complex representative and its derived object, packaged as a lift. -/
structure DerivedModuleSystemComplexLift
    (A : RingInverseSystem.{u})
    (F : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat (inverseLimitRing A))) where
  complex : ℕᵒᵖ ⥤ CochainComplex (ModuleCat (inverseLimitRing A)) ℤ
  stageIso : ∀ n : ℕ,
    (moduleDerivedQuotient A).obj (complex.obj (Opposite.op n)) ≅
      F.obj (Opposite.op n)
  compatible : ∀ n : ℕ,
    (moduleDerivedQuotient A).map
        (complex.map (opHomOfLE (Nat.le_succ n))) ≫
        (stageIso n).hom =
      (stageIso (n + 1)).hom ≫ F.map (opHomOfLE (Nat.le_succ n))

/-- Every derived object of the module-system category admits a complex lift. -/
theorem exists_derivedModuleSystemComplexLift
    (A : RingInverseSystem.{u})
    (F : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat (inverseLimitRing A))) :
    Nonempty (DerivedModuleSystemComplexLift A F) := by
  sorry

/-- The chosen derived limit is independent of the chosen complex lift. -/
theorem derived_limit_of_moduleSystem_complex_lift
    (A : RingInverseSystem.{u})
    {F : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat (inverseLimitRing A))}
    {L : DerivedCategory (ModuleCat (inverseLimitRing A))}
    (hL : IsDerivedLimit F L) (M : DerivedModuleSystemComplexLift A F)
    [HasProduct (fun n : ℕ =>
      (moduleDerivedQuotient A).obj (M.complex.obj (Opposite.op n)))] :
    Nonempty
      (L ≅ derivedLimit
        (M.complex ⋙ moduleDerivedQuotient A)
        (exists_isDerivedLimit (M.complex ⋙ moduleDerivedQuotient A))) := by
  sorry

/-! ## 88.4. Surjective and K-flat representatives -/

/-- All transition maps of a module system are surjective. -/
def HasSurjectiveModuleTransitions
    (M : ModuleInverseSystem.{u, v} A) : Prop :=
  ∀ ⦃i j : ℕᵒᵖ⦄ (f : i ⟶ j), Function.Surjective (M.map f)

/-- Every derived module-system object has a representative with surjective
transition maps. -/
theorem exists_surjective_moduleSystem_representative
    (A : RingInverseSystem.{u}) (K : DerivedModuleInverseSystem.{u, v} A) :
    ∃ L : CochainComplex (ModuleInverseSystem.{u, v} A) ℤ,
      Nonempty (K ≅ (moduleSystemDerivedQuotient A).obj L) ∧
        ∀ p : ℤ, HasSurjectiveModuleTransitions (L.X p) := by
  sorry

/-! The varying-ring category has no bundled tensor-product-of-complexes API in
Mathlib.  The following small interface records exactly the operation used by
the source's K-flatness definition and keeps the missing construction visible. -/

structure ModuleSystemTensorComplexData (A : RingInverseSystem.{u}) where
  tensor : CochainComplex (ModuleInverseSystem.{u, v} A) ℤ →
    CochainComplex (ModuleInverseSystem.{u, v} A) ℤ →
      CochainComplex (ModuleInverseSystem.{u, v} A) ℤ

theorem exists_moduleSystemTensorComplexData (A : RingInverseSystem.{u}) :
    Nonempty (ModuleSystemTensorComplexData A) := by
  sorry

noncomputable def moduleSystemTensorComplex
    (A : RingInverseSystem.{u})
    (K L : CochainComplex (ModuleInverseSystem.{u, v} A) ℤ) :
    CochainComplex (ModuleInverseSystem.{u, v} A) ℤ :=
  (Classical.choice (exists_moduleSystemTensorComplexData A)).tensor K L

abbrev IsAcyclicModuleSystemComplex
    (K : CochainComplex (ModuleInverseSystem.{u, v} A) ℤ) : Prop :=
  K.Acyclic

/-- A complex is K-flat when tensoring it with every acyclic complex is
acyclic, as in the source's definition. -/
def IsKFlatModuleSystemComplex
    (A : RingInverseSystem.{u})
    (K : CochainComplex (ModuleInverseSystem.{u, v} A) ℤ) : Prop :=
  ∀ L : CochainComplex (ModuleInverseSystem.{u, v} A) ℤ,
    IsAcyclicModuleSystemComplex L →
      IsAcyclicModuleSystemComplex (moduleSystemTensorComplex A K L)

/-- Every derived module-system object admits a representative with K-flat
terms. -/
theorem exists_KFlat_moduleSystem_representative
    (A : RingInverseSystem.{u}) (K : DerivedModuleInverseSystem.{u, v} A) :
    ∃ L : CochainComplex (ModuleInverseSystem.{u, v} A) ℤ,
      Nonempty (K ≅ (moduleSystemDerivedQuotient A).obj L) ∧
        IsKFlatModuleSystemComplex A L := by
  sorry

/-! ## 88.5. Derived limits of inverse systems in the derived category -/

/-- An inverse system of derived modules over the inverse-limit ring. -/
abbrev ModuleDerivedInverseSystem (A : RingInverseSystem.{u}) :=
  ℕᵒᵖ ⥤ DerivedCategory (ModuleCat (inverseLimitRing A))

/-- The derived limit of an inverse system of derived modules. -/
noncomputable def moduleDerivedLimit
    (A : RingInverseSystem.{u}) (F : ModuleDerivedInverseSystem.{u, v} A)
    [HasProduct (fun n : ℕ => F.obj (Opposite.op n))] :
    DerivedCategory (ModuleCat (inverseLimitRing A)) :=
  derivedLimit F (exists_isDerivedLimit F)

theorem moduleDerivedLimit_isDerivedLimit
    (A : RingInverseSystem.{u}) (F : ModuleDerivedInverseSystem.{u, v} A)
    [HasProduct (fun n : ℕ => F.obj (Opposite.op n))] :
    IsDerivedLimit F (moduleDerivedLimit A F) := by
  exact derivedLimit_isDerivedLimit F (exists_isDerivedLimit F)

/-- The defining derived-limit presentation. -/
noncomputable def moduleDerivedLimitPresentation
    (A : RingInverseSystem.{u}) (F : ModuleDerivedInverseSystem.{u, v} A)
    [HasProduct (fun n : ℕ => F.obj (Opposite.op n))] :
    DerivedLimitPresentation F (moduleDerivedLimit A F) :=
  Classical.choice (moduleDerivedLimit_isDerivedLimit A F)

/-- The canonical distinguished triangle for a derived limit. -/
theorem moduleDerivedLimit_distinguished_triangle
    (A : RingInverseSystem.{u}) (F : ModuleDerivedInverseSystem.{u, v} A)
    [HasProduct (fun n : ℕ => F.obj (Opposite.op n))] :
    Triangle.mk (moduleDerivedLimitPresentation A F).inclusion
        (inverseSystemDifferenceMap F (moduleDerivedLimitPresentation A F).product)
        (moduleDerivedLimitPresentation A F).connecting ∈
      distTriang (DerivedCategory (ModuleCat (inverseLimitRing A))) := by
  exact (moduleDerivedLimitPresentation A F).distinguished

/-- A presentation of the derived inverse-limit output by an inverse system
of derived modules over the limit ring. -/
structure ModuleRlimPresentationData
    (A : RingInverseSystem.{u})
    (K : DerivedModuleInverseSystem.{u, v} A) where
  stages : ModuleDerivedInverseSystem.{u, v} A
  hasProduct : HasProduct (fun n : ℕ => stages.obj (Opposite.op n))

theorem exists_moduleRlimPresentationData
    (A : RingInverseSystem.{u}) (K : DerivedModuleInverseSystem.{u, v} A) :
    Nonempty (ModuleRlimPresentationData A K) := by
  sorry

noncomputable def moduleRlimPresentation
    (A : RingInverseSystem.{u}) (K : DerivedModuleInverseSystem.{u, v} A) :
    ModuleRlimPresentationData A K :=
  Classical.choice (exists_moduleRlimPresentationData A K)

noncomputable def moduleRlimPresentedDerivedLimit
    (A : RingInverseSystem.{u}) (K : DerivedModuleInverseSystem.{u, v} A) :
    DerivedCategory (ModuleCat (inverseLimitRing A)) :=
  let P := moduleRlimPresentation A K
  letI := P.hasProduct
  moduleDerivedLimit A P.stages

theorem moduleRlim_is_presented_as_derived_limit
    (A : RingInverseSystem.{u}) (K : DerivedModuleInverseSystem.{u, v} A) :
    Nonempty
      (moduleRlimFunctor A K ≅ moduleRlimPresentedDerivedLimit A K) := by
  sorry

/-- The canonical triangle `Rlim → ∏ Kₙ → ∏ Kₙ → Rlim[1]` for the chosen
derived-limit presentation of a module-system object. -/
theorem moduleRlim_distinguished_triangle
    (A : RingInverseSystem.{u}) (K : DerivedModuleInverseSystem.{u, v} A) :
    let P := moduleRlimPresentation A K
    letI := P.hasProduct
    Triangle.mk (moduleDerivedLimitPresentation A P.stages).inclusion
        (inverseSystemDifferenceMap P.stages
          (moduleDerivedLimitPresentation A P.stages).product)
        (moduleDerivedLimitPresentation A P.stages).connecting ∈
      distTriang (DerivedCategory (ModuleCat (inverseLimitRing A))) := by
  dsimp
  exact moduleDerivedLimit_distinguished_triangle A
    (moduleRlimPresentation A K).stages

/-- The first right-derived functor of the ordinary limit on systems of
modules over the fixed ring `inverseLimitRing A`.  This is separated from the
varying-ring inverse-limit functor above because the source uses both
categories. -/
structure FixedModuleInverseLimitDerivedData (A : RingInverseSystem.{u}) where
  firstDerived :
    (ℕᵒᵖ ⥤ ModuleCat (inverseLimitRing A)) ⥤
      ModuleCat (inverseLimitRing A)

theorem exists_fixedModuleInverseLimitDerivedData
    (A : RingInverseSystem.{u}) :
    Nonempty (FixedModuleInverseLimitDerivedData A) := by
  sorry

noncomputable def firstDerivedLimitOfModuleDerivedSystem
    (A : RingInverseSystem.{u})
    (F : ℕᵒᵖ ⥤ ModuleCat (inverseLimitRing A)) :
    ModuleCat (inverseLimitRing A) :=
  (Classical.choice (exists_fixedModuleInverseLimitDerivedData A)).firstDerived.obj F

/-- The cohomology system of an inverse system of derived modules. -/
noncomputable def moduleDerivedObjectCohomologySystem
    (A : RingInverseSystem.{u})
    (F : ModuleDerivedInverseSystem.{u, v} A) (p : ℤ) :
    ℕᵒᵖ ⥤ ModuleCat (inverseLimitRing A) :=
  F ⋙ DerivedCategory.homologyFunctor (ModuleCat (inverseLimitRing A)) p

/-- A system of derived modules admits the source's short exact cohomology
window after choosing representatives. -/
def ModuleDerivedLimitCohomologyExactSequence
    (A : RingInverseSystem.{u}) (F : ModuleDerivedInverseSystem.{u, v} A)
    (L : DerivedCategory (ModuleCat (inverseLimitRing A)))
    (_hL : IsDerivedLimit F L) (p : ℤ) : Prop :=
  ∃ α : firstDerivedLimitOfModuleDerivedSystem A
      (moduleDerivedObjectCohomologySystem A F (p - 1)) ⟶
      (DerivedCategory.homologyFunctor
      (ModuleCat (inverseLimitRing A)) p).obj L,
    ∃ β : (DerivedCategory.homologyFunctor
      (ModuleCat (inverseLimitRing A)) p).obj L ⟶
      limit (moduleDerivedObjectCohomologySystem A F p),
    (ComposableArrows.mk₄
      (0 : (0 : ModuleCat (inverseLimitRing A)) ⟶
        firstDerivedLimitOfModuleDerivedSystem A
          (moduleDerivedObjectCohomologySystem A F (p - 1)))
      α β
      (0 : limit (moduleDerivedObjectCohomologySystem A F p) ⟶
        (0 : ModuleCat (inverseLimitRing A)))).Exact

theorem moduleDerivedLimit_cohomology_exact_sequence
    (A : RingInverseSystem.{u}) (F : ModuleDerivedInverseSystem.{u, v} A)
    (L : DerivedCategory (ModuleCat (inverseLimitRing A)))
    (hL : IsDerivedLimit F L) (p : ℤ) :
    ModuleDerivedLimitCohomologyExactSequence A F L hL p := by
  sorry

/-! ## 88.6. Derived tensor products and functorial consequences -/

/-- Symmetry of the derived tensor product. -/
def IsSymmetricDerivedTensorProduct
    (A : RingInverseSystem.{u})
    (T : (DerivedModuleInverseSystem.{u, v} A ×
      DerivedModuleInverseSystem.{u, v} A) ⥤ DerivedModuleInverseSystem.{u, v} A) : Prop :=
  ∀ K L, Nonempty (T.obj (K, L) ≅ T.obj (L, K))

/-- The derived tensor product with a fixed first variable. -/
def derivedTensorLeft
    (A : RingInverseSystem.{u})
    (T : (DerivedModuleInverseSystem.{u, v} A ×
      DerivedModuleInverseSystem.{u, v} A) ⥤ DerivedModuleInverseSystem.{u, v} A)
    (K : DerivedModuleInverseSystem.{u, v} A) :
    DerivedModuleInverseSystem.{u, v} A ⥤ DerivedModuleInverseSystem.{u, v} A where
  obj L := T.obj (K, L)
  map f := T.map (𝟙 K, f)
  map_id := by intro L; simp
  map_comp := by intro L M N f g; simp

/-- The derived tensor product with a fixed second variable. -/
def derivedTensorRight
    (A : RingInverseSystem.{u})
    (T : (DerivedModuleInverseSystem.{u, v} A ×
      DerivedModuleInverseSystem.{u, v} A) ⥤ DerivedModuleInverseSystem.{u, v} A)
    (L : DerivedModuleInverseSystem.{u, v} A) :
    DerivedModuleInverseSystem.{u, v} A ⥤ DerivedModuleInverseSystem.{u, v} A where
  obj K := T.obj (K, L)
  map f := T.map (f, 𝟙 L)
  map_id := by intro K; simp
  map_comp := by intro K M N f g; simp

/-- Exactness in each variable of a derived tensor product. -/
def IsExactDerivedTensorProduct
    (A : RingInverseSystem.{u})
    (T : (DerivedModuleInverseSystem.{u, v} A ×
      DerivedModuleInverseSystem.{u, v} A) ⥤ DerivedModuleInverseSystem.{u, v} A) : Prop :=
  (∀ K, ∃ hF : (derivedTensorLeft A T K).CommShift ℤ,
    ∀ X : Triangle (DerivedModuleInverseSystem.{u, v} A),
      X ∈ distTriang (DerivedModuleInverseSystem.{u, v} A) →
        (letI := hF
        (derivedTensorLeft A T K).mapTriangle.obj X ∈
          distTriang (DerivedModuleInverseSystem.{u, v} A))) ∧
    (∀ L, ∃ hF : (derivedTensorRight A T L).CommShift ℤ,
    ∀ X : Triangle (DerivedModuleInverseSystem.{u, v} A),
      X ∈ distTriang (DerivedModuleInverseSystem.{u, v} A) →
        (letI := hF
        (derivedTensorRight A T L).mapTriangle.obj X ∈
          distTriang (DerivedModuleInverseSystem.{u, v} A)))

/-- The derived tensor product of two module-system complexes exists and is
canonical up to the usual derived equivalence. -/
theorem exists_derivedTensorProductSystem
    (A : RingInverseSystem.{u}) :
    ∃ T : (DerivedModuleInverseSystem.{u, v} A ×
      DerivedModuleInverseSystem.{u, v} A) ⥤ DerivedModuleInverseSystem.{u, v} A,
      IsSymmetricDerivedTensorProduct A T ∧ IsExactDerivedTensorProduct A T := by
  sorry

/-- The chosen bifunctor underlying the derived tensor product. -/
noncomputable def derivedTensorProductSystemFunctor
    (A : RingInverseSystem.{u}) :
    (DerivedModuleInverseSystem.{u, v} A ×
      DerivedModuleInverseSystem.{u, v} A) ⥤ DerivedModuleInverseSystem.{u, v} A :=
  Classical.choose (exists_derivedTensorProductSystem A)

/-- The chosen derived tensor product of two derived module systems. -/
noncomputable def derivedTensorProductSystem
    (A : RingInverseSystem.{u})
    (K L : DerivedModuleInverseSystem.{u, v} A) :
    DerivedModuleInverseSystem.{u, v} A :=
  (derivedTensorProductSystemFunctor A).obj (K, L)

theorem derivedTensorProductSystem_is_symmetric
    (A : RingInverseSystem.{u}) :
    IsSymmetricDerivedTensorProduct A (derivedTensorProductSystemFunctor A) := by
  exact (Classical.choose_spec (exists_derivedTensorProductSystem A)).1

theorem derivedTensorProductSystem_is_exact
    (A : RingInverseSystem.{u}) :
    IsExactDerivedTensorProduct A (derivedTensorProductSystemFunctor A) := by
  exact (Classical.choose_spec (exists_derivedTensorProductSystem A)).2

/-- The diagonal, or constant-system, functor. -/
noncomputable def diagonalDerivedFunctor
    (A : RingInverseSystem.{u}) :
    DerivedModuleInverseSystem.{u, v} A ⥤ ModuleDerivedInverseSystem.{u, v} A where
  obj K := Functor.const (ℕᵒᵖ) K
  map f :=
    { app := fun _ => f
      naturality := by intros; simp }
  map_id := by intro K; rfl
  map_comp := by intro K L M f g; rfl

/-- Data for the exact functor `Rlim(- ⊗ᴸ Eₙ)` attached to a chosen lift of
an inverse system of derived modules. -/
structure DerivedLimitTensorFunctorData
    (A : RingInverseSystem.{u}) (E : ModuleDerivedInverseSystem.{u, v} A) where
  functor : DerivedCategory (ModuleCat (inverseLimitRing A)) ⥤
    DerivedCategory (ModuleCat (inverseLimitRing A))
  commShift : functor.CommShift ℤ
  exact : ∀ T : Triangle (DerivedCategory (ModuleCat (inverseLimitRing A))),
    T ∈ distTriang (DerivedCategory (ModuleCat (inverseLimitRing A))) →
      (letI := commShift
      functor.mapTriangle.obj T ∈
        distTriang (DerivedCategory (ModuleCat (inverseLimitRing A))))

theorem exists_derivedLimitTensorFunctor
    (A : RingInverseSystem.{u}) (E : ModuleDerivedInverseSystem.{u, v} A) :
    Nonempty (DerivedLimitTensorFunctorData A E) := by
  sorry

noncomputable def derivedLimitTensorFunctor
    (A : RingInverseSystem.{u}) (E : ModuleDerivedInverseSystem.{u, v} A) :
    DerivedCategory (ModuleCat (inverseLimitRing A)) ⥤
      DerivedCategory (ModuleCat (inverseLimitRing A)) :=
  (Classical.choice (exists_derivedLimitTensorFunctor A E)).functor

/-- Tensoring a distinguished triangle and then taking `Rlim` is exact. -/
theorem tensor_Rlim_exact
    (A : RingInverseSystem.{u}) (E : ModuleDerivedInverseSystem.{u, v} A)
    (T : Triangle (DerivedCategory (ModuleCat (inverseLimitRing A))))
    (hT : T ∈ distTriang (DerivedCategory (ModuleCat (inverseLimitRing A)))) :
    ∃ hF : (derivedLimitTensorFunctor A E).CommShift ℤ,
      (letI := hF
      (derivedLimitTensorFunctor A E).mapTriangle.obj T ∈
        distTriang (DerivedCategory (ModuleCat (inverseLimitRing A)))) := by
  sorry

/-- Pro-isomorphic inverse systems have isomorphic derived limits. -/
theorem moduleDerivedLimit_pro_equal
    (A : RingInverseSystem.{u})
    (E D : ModuleDerivedInverseSystem.{u, v} A)
    [HasProduct (fun n : ℕ => E.obj (Opposite.op n))]
    [HasProduct (fun n : ℕ => D.obj (Opposite.op n))]
    (hED : Formalization.Books.MoreAlgebra.Unit87.IsProIsomorphism E D) :
    Nonempty (moduleDerivedLimit A E ≅ moduleDerivedLimit A D) := by
  sorry

/-- The system obtained by tensoring a constant derived object with an
inverse system of derived modules. -/
noncomputable def tensorDerivedInverseSystem
    (A : RingInverseSystem.{u})
    (K : DerivedCategory (ModuleCat (inverseLimitRing A)))
    (E : ModuleDerivedInverseSystem.{u, v} A) :
    ModuleDerivedInverseSystem.{u, v} A :=
  (derivedTensorProductSystemFunctor A).obj
    ((diagonalDerivedFunctor A).obj K, E)

/-- The tensor version of pro-isomorphism invariance of `Rlim`. -/
theorem tensor_Rlim_pro_equal
    (A : RingInverseSystem.{u})
    (K : DerivedCategory (ModuleCat (inverseLimitRing A)))
    (E D : ModuleDerivedInverseSystem.{u, v} A)
    [HasProduct (fun n : ℕ =>
      (tensorDerivedInverseSystem A K E).obj (Opposite.op n))]
    [HasProduct (fun n : ℕ =>
      (tensorDerivedInverseSystem A K D).obj (Opposite.op n))]
    (f : E ⟶ D)
    (hED : Formalization.Books.MoreAlgebra.Unit87.IsProIsomorphism E D) :
    Nonempty
      (moduleDerivedLimit A (tensorDerivedInverseSystem A K E) ≅
        moduleDerivedLimit A (tensorDerivedInverseSystem A K D)) := by
  sorry

-/
end Formalization.Books.MoreAlgebra.Unit88
