import Formalization.Books.Homology.Unit03.PreadditiveAndAdditiveCategories
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.Torsion.Prod
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.LinearAlgebra.Prod
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Exercises, Chapter 3: finitely generated torsion-free modules

The category in this exercise is represented as the full subcategory of
`ModuleCat` cut out by `Module.Finite` and `Module.IsTorsionFree`.  Its
cokernel is not the ordinary module cokernel: it is the ordinary cokernel
modulo its torsion submodule.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace Formalization.Books.Exercises.Unit03

/-! ## The category and its direct sums -/

/-- The objects used in the torsion-free exercise. -/
def FinitelyGeneratedTorsionFree
    (R : Type u) [CommRing R] :
    ObjectProperty (ModuleCat.{u} R) :=
  fun M => Module.Finite R M ∧ Module.IsTorsionFree R M

/-- The category of finitely generated torsion-free `R`-modules. -/
abbrev FinitelyGeneratedTorsionFreeModuleCat
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsDomain R] :=
  (FinitelyGeneratedTorsionFree R).FullSubcategory

abbrev torsionFreeUnderlyingLinearMap
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    {X Y : FinitelyGeneratedTorsionFreeModuleCat R} (f : X ⟶ Y) :
    X.obj →ₗ[R] Y.obj :=
  f.hom.hom

def torsionFreeModuleDirectSum
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    (X Y : FinitelyGeneratedTorsionFreeModuleCat R) :
    FinitelyGeneratedTorsionFreeModuleCat R := by
  letI : Module.Finite R X.obj := X.property.1
  letI : Module.IsTorsionFree R X.obj := X.property.2
  letI : Module.Finite R Y.obj := Y.property.1
  letI : Module.IsTorsionFree R Y.obj := Y.property.2
  exact ⟨ModuleCat.of R (X.obj × Y.obj), ⟨inferInstance, inferInstance⟩⟩

/-- The category of finitely generated torsion-free modules is additive. -/
theorem finitelyGeneratedTorsionFree_additive
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsDomain R] :
    Nonempty
      (Formalization.Books.Homology.Unit03.AdditiveCategory
        (FinitelyGeneratedTorsionFreeModuleCat R)) := by
  sorry

/-! ## Kernels -/

/-- The ordinary module kernel, with its inherited finite and torsion-free
properties. -/
def torsionFreeKernel
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    {X Y : FinitelyGeneratedTorsionFreeModuleCat R} (f : X ⟶ Y) :
    FinitelyGeneratedTorsionFreeModuleCat R := by
  letI : Module.Finite R X.obj := X.property.1
  letI : Module.IsTorsionFree R X.obj := X.property.2
  exact
    ⟨ModuleCat.of R (LinearMap.ker (torsionFreeUnderlyingLinearMap f)),
      ⟨inferInstance, inferInstance⟩⟩

/-- The kernel inclusion in the torsion-free category. -/
def torsionFreeKernelι
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    {X Y : FinitelyGeneratedTorsionFreeModuleCat R} (f : X ⟶ Y) :
    torsionFreeKernel f ⟶ X :=
  ObjectProperty.homMk
    (ModuleCat.ofHom (LinearMap.ker (torsionFreeUnderlyingLinearMap f)).subtype)

theorem torsionFreeKernelι_comp
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    {X Y : FinitelyGeneratedTorsionFreeModuleCat R} (f : X ⟶ Y) :
    torsionFreeKernelι f ≫ f = 0 := by
  sorry

def torsionFreeKernelFork
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    {X Y : FinitelyGeneratedTorsionFreeModuleCat R} (f : X ⟶ Y) :
    KernelFork f :=
  KernelFork.ofι (torsionFreeKernelι f) (torsionFreeKernelι_comp f)

theorem torsionFreeKernelFork_isLimit_exists
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    {X Y : FinitelyGeneratedTorsionFreeModuleCat R} (f : X ⟶ Y) :
    Nonempty (IsLimit (torsionFreeKernelFork f)) := by
  sorry

noncomputable def torsionFreeKernelFork_isLimit
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    {X Y : FinitelyGeneratedTorsionFreeModuleCat R} (f : X ⟶ Y) :
    IsLimit (torsionFreeKernelFork f) :=
  Classical.choice (torsionFreeKernelFork_isLimit_exists f)

/-! ## Cokernels -/

/-- The module underlying the torsion-free cokernel. -/
abbrev torsionFreeCokernelModule
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    {X Y : FinitelyGeneratedTorsionFreeModuleCat R} (f : X ⟶ Y) : Type u :=
  (Y.obj ⧸ LinearMap.range (torsionFreeUnderlyingLinearMap f)) ⧸
    Submodule.torsion R (Y.obj ⧸ LinearMap.range (torsionFreeUnderlyingLinearMap f))

theorem torsionFreeCokernelModule_finite
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    {X Y : FinitelyGeneratedTorsionFreeModuleCat R} (f : X ⟶ Y) :
    Module.Finite R (torsionFreeCokernelModule f) := by
  let _i : Module.Finite R Y.obj := Y.property.1
  let _i : Module.Finite R
      (Y.obj ⧸ LinearMap.range (torsionFreeUnderlyingLinearMap f)) := inferInstance
  infer_instance

theorem torsionFreeCokernelModule_torsionFree
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    {X Y : FinitelyGeneratedTorsionFreeModuleCat R} (f : X ⟶ Y) :
    Module.IsTorsionFree R (torsionFreeCokernelModule f) := by
  infer_instance

/-- The ordinary cokernel followed by quotienting out all torsion. -/
def torsionFreeCokernel
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    {X Y : FinitelyGeneratedTorsionFreeModuleCat R} (f : X ⟶ Y) :
    FinitelyGeneratedTorsionFreeModuleCat R :=
  ⟨ModuleCat.of R (torsionFreeCokernelModule f),
    ⟨torsionFreeCokernelModule_finite f,
      torsionFreeCokernelModule_torsionFree f⟩⟩

/-- The map from the target to the torsion-free cokernel. -/
def torsionFreeCokernelπ
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    {X Y : FinitelyGeneratedTorsionFreeModuleCat R} (f : X ⟶ Y) :
    Y ⟶ torsionFreeCokernel f :=
  ObjectProperty.homMk <|
    ModuleCat.ofHom <|
      (Submodule.torsion R
          (Y.obj ⧸ LinearMap.range (torsionFreeUnderlyingLinearMap f))).mkQ.comp
        (LinearMap.range (torsionFreeUnderlyingLinearMap f)).mkQ

theorem torsionFreeCokernel_comp
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    {X Y : FinitelyGeneratedTorsionFreeModuleCat R} (f : X ⟶ Y) :
    f ≫ torsionFreeCokernelπ f = 0 := by
  sorry

def torsionFreeCokernelCofork
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    {X Y : FinitelyGeneratedTorsionFreeModuleCat R} (f : X ⟶ Y) :
    CokernelCofork f :=
  CokernelCofork.ofπ (torsionFreeCokernelπ f) (torsionFreeCokernel_comp f)

theorem torsionFreeCokernelCofork_isColimit_exists
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    {X Y : FinitelyGeneratedTorsionFreeModuleCat R} (f : X ⟶ Y) :
    Nonempty (IsColimit (torsionFreeCokernelCofork f)) := by
  sorry

noncomputable def torsionFreeCokernelCofork_isColimit
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    {X Y : FinitelyGeneratedTorsionFreeModuleCat R} (f : X ⟶ Y) :
    IsColimit (torsionFreeCokernelCofork f) :=
  Classical.choice (torsionFreeCokernelCofork_isColimit_exists f)

noncomputable instance torsionFreeModuleCat_hasKernels
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsDomain R] :
    HasKernels (FinitelyGeneratedTorsionFreeModuleCat R) where
  has_limit f :=
    ⟨⟨torsionFreeKernelFork f, torsionFreeKernelFork_isLimit f⟩⟩

noncomputable instance torsionFreeModuleCat_hasCokernels
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsDomain R] :
    HasCokernels (FinitelyGeneratedTorsionFreeModuleCat R) where
  has_colimit f :=
    ⟨⟨torsionFreeCokernelCofork f, torsionFreeCokernelCofork_isColimit f⟩⟩

/-! ## The coimage/image counterexample -/

def integerModule : FinitelyGeneratedTorsionFreeModuleCat ℤ :=
  ⟨ModuleCat.of ℤ ℤ, ⟨inferInstance, inferInstance⟩⟩

def integerDoubling : ℤ →ₗ[ℤ] ℤ :=
  (LinearMap.id : ℤ →ₗ[ℤ] ℤ).smulRight 2

def integerDoublingMap : integerModule ⟶ integerModule :=
  ObjectProperty.homMk (ModuleCat.ofHom integerDoubling)

/-- In the torsion-free category, multiplication by `2` has zero categorical
cokernel, so its coimage-to-image comparison is not an isomorphism. -/
theorem integerDoubling_coimage_image_not_isIso :
    ¬ IsIso (Abelian.coimageImageComparison integerDoublingMap) := by
  sorry

end Formalization.Books.Exercises.Unit03
