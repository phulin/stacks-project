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
  let zero : FinitelyGeneratedTorsionFreeModuleCat R :=
    { obj := ModuleCat.of R PUnit
      property := ⟨inferInstance, inferInstance⟩ }
  let terminal : IsTerminal zero :=
    IsTerminal.ofUniqueHom (fun X => ObjectProperty.homMk 0) (by
      intro X m
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact Subsingleton.elim _ _)
  let : HasTerminal (FinitelyGeneratedTorsionFreeModuleCat R) :=
    terminal.hasTerminal
  let : ∀ {X Y : FinitelyGeneratedTorsionFreeModuleCat R},
      HasLimit (pair X Y) := by
    intro X Y
    let P := torsionFreeModuleDirectSum X Y
    let fst : P ⟶ X :=
      ObjectProperty.homMk
        (ModuleCat.ofHom (LinearMap.fst R X.obj Y.obj))
    let snd : P ⟶ Y :=
      ObjectProperty.homMk
        (ModuleCat.ofHom (LinearMap.snd R X.obj Y.obj))
    refine ⟨⟨BinaryFan.mk fst snd, ?_⟩⟩
    exact BinaryFan.IsLimit.mk (BinaryFan.mk fst snd)
      (fun {Z} a b =>
        ObjectProperty.homMk
          (ModuleCat.ofHom (LinearMap.prod a.hom.hom b.hom.hom)))
      (fun {Z} a b => by
        apply ObjectProperty.hom_ext
        apply ModuleCat.hom_ext
        change (LinearMap.fst R X.obj Y.obj).comp
            (LinearMap.prod a.hom.hom b.hom.hom) = a.hom.hom
        exact LinearMap.fst_prod a.hom.hom b.hom.hom)
      (fun {Z} a b => by
        apply ObjectProperty.hom_ext
        apply ModuleCat.hom_ext
        change (LinearMap.snd R X.obj Y.obj).comp
            (LinearMap.prod a.hom.hom b.hom.hom) = b.hom.hom
        exact LinearMap.snd_prod a.hom.hom b.hom.hom)
      (fun {Z} a b m h₁ h₂ => by
        apply ObjectProperty.hom_ext
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        have h₁' : m.hom ≫ fst.hom = a.hom := by
          exact congrArg (fun q : Z ⟶ X => q.hom) h₁
        have h₂' : m.hom ≫ snd.hom = b.hom := by
          exact congrArg (fun q : Z ⟶ Y => q.hom) h₂
        have h₁'' : (LinearMap.fst R X.obj Y.obj).comp m.hom.hom =
            a.hom.hom := by
          have h := congrArg
            (fun q : Z.obj ⟶ X.obj => q.hom) h₁'
          change (LinearMap.fst R X.obj Y.obj).comp m.hom.hom = a.hom.hom at h
          exact h
        have h₂'' : (LinearMap.snd R X.obj Y.obj).comp m.hom.hom =
            b.hom.hom := by
          have h := congrArg
            (fun q : Z.obj ⟶ Y.obj => q.hom) h₂'
          change (LinearMap.snd R X.obj Y.obj).comp m.hom.hom = b.hom.hom at h
          exact h
        change m.hom.hom z = (a.hom.hom z, b.hom.hom z)
        exact Prod.ext
          (by
            change (LinearMap.fst R X.obj Y.obj).comp m.hom.hom z = a.hom.hom z
            simpa only [LinearMap.comp_apply] using
              congrArg (fun q : Z.obj →ₗ[R] X.obj => q z) h₁'')
          (by
            change (LinearMap.snd R X.obj Y.obj).comp m.hom.hom z = b.hom.hom z
            simpa only [LinearMap.comp_apply] using
              congrArg (fun q : Z.obj →ₗ[R] Y.obj => q z) h₂''))
  let hproducts : HasBinaryProducts (FinitelyGeneratedTorsionFreeModuleCat R) :=
    @hasBinaryProducts_of_hasLimit_pair
      (FinitelyGeneratedTorsionFreeModuleCat R) _ this
  let hfinite : HasFiniteProducts (FinitelyGeneratedTorsionFreeModuleCat R) :=
    @hasFiniteProducts_of_has_binary_and_terminal
      (FinitelyGeneratedTorsionFreeModuleCat R) _ hproducts terminal.hasTerminal
  exact ⟨{ toPreadditive := inferInstance, toHasFiniteProducts := hfinite }⟩

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
  apply ObjectProperty.hom_ext
  dsimp [torsionFreeKernel, torsionFreeKernelι, torsionFreeUnderlyingLinearMap]
  apply ModuleCat.hom_ext
  change f.hom.hom.comp (LinearMap.ker f.hom.hom).subtype = 0
  exact LinearMap.comp_ker_subtype f.hom.hom

def torsionFreeKernelFork
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    {X Y : FinitelyGeneratedTorsionFreeModuleCat R} (f : X ⟶ Y) :
    KernelFork f :=
  KernelFork.ofι (torsionFreeKernelι f) (torsionFreeKernelι_comp f)

theorem torsionFreeKernelFork_isLimit_exists
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    {X Y : FinitelyGeneratedTorsionFreeModuleCat R} (f : X ⟶ Y) :
    Nonempty (IsLimit (torsionFreeKernelFork f)) := by
  let kernelLift {Z : FinitelyGeneratedTorsionFreeModuleCat R}
      (a : Z ⟶ X) (ha : a ≫ f = 0) :
      Z ⟶ torsionFreeKernel f := by
    apply ObjectProperty.homMk
    apply ModuleCat.ofHom
    exact LinearMap.codRestrict (LinearMap.ker f.hom.hom) a.hom.hom (by
      intro z
      rw [LinearMap.mem_ker]
      have ha' : f.hom.hom.comp a.hom.hom = 0 := by
        have h := congrArg (fun g : Z ⟶ Y => g.hom.hom) ha
        change f.hom.hom.comp a.hom.hom = 0 at h
        exact h
      have hz := congrArg (fun g : Z.obj →ₗ[R] Y.obj => g z) ha'
      simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using hz)
  refine ⟨KernelFork.IsLimit.ofι (torsionFreeKernelι f)
    (torsionFreeKernelι_comp f)
    (fun {Z} a ha => by
      exact kernelLift a ha)
    (fun {Z} a ha => by
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      change (LinearMap.ker f.hom.hom).subtype.comp
          (kernelLift a ha).hom.hom = a.hom.hom
      dsimp [kernelLift]
      rfl)
    (fun {Z} a ha m hm => by
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      have hm' : m.hom ≫ (torsionFreeKernelι f).hom = a.hom := by
        exact congrArg (fun g : Z ⟶ X => g.hom) hm
      have hm'' : (LinearMap.ker f.hom.hom).subtype.comp m.hom.hom =
          a.hom.hom := by
        have h := congrArg
          (fun g : Z.obj ⟶ X.obj => g.hom) hm'
        change (LinearMap.ker f.hom.hom).subtype.comp m.hom.hom =
            a.hom.hom at h
        exact h
      change (LinearMap.ker f.hom.hom).subtype (m.hom.hom z) =
          a.hom.hom z
      have h := congrArg
        (fun g : Z.obj →ₗ[R] X.obj => g z) hm''
      change (LinearMap.ker f.hom.hom).subtype (m.hom.hom z) =
          a.hom.hom z at h
      exact h)⟩

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
  apply ObjectProperty.hom_ext
  dsimp [torsionFreeCokernelπ, torsionFreeUnderlyingLinearMap]
  apply ModuleCat.hom_ext
  change ((Submodule.torsion R (Y.obj ⧸ LinearMap.range f.hom.hom)).mkQ.comp
      (LinearMap.range f.hom.hom).mkQ).comp f.hom.hom = 0
  rw [LinearMap.comp_assoc]
  rw [LinearMap.range_mkQ_comp]
  simp

def torsionFreeCokernelCofork
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    {X Y : FinitelyGeneratedTorsionFreeModuleCat R} (f : X ⟶ Y) :
    CokernelCofork f :=
  CokernelCofork.ofπ (torsionFreeCokernelπ f) (torsionFreeCokernel_comp f)

theorem torsionFreeCokernelCofork_isColimit_exists
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    {X Y : FinitelyGeneratedTorsionFreeModuleCat R} (f : X ⟶ Y) :
    Nonempty (IsColimit (torsionFreeCokernelCofork f)) := by
  let range_le_ker {Z : FinitelyGeneratedTorsionFreeModuleCat R}
      (a : Y ⟶ Z) (ha : f ≫ a = 0) :
      LinearMap.range f.hom.hom ≤ LinearMap.ker a.hom.hom := by
    have ha' : f.hom ≫ a.hom = 0 := congrArg (fun g : X ⟶ Z => g.hom) ha
    have ha'' := congrArg (fun g : X.obj ⟶ Z.obj => g.hom) ha'
    change a.hom.hom.comp f.hom.hom = 0 at ha''
    intro y hy
    rcases hy with ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    have hx := congrArg (fun g : X.obj →ₗ[R] Z.obj => g x) ha''
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using hx
  let rangeLift {Z : FinitelyGeneratedTorsionFreeModuleCat R}
      (a : Y ⟶ Z) (ha : f ≫ a = 0) :
      (Y.obj ⧸ LinearMap.range f.hom.hom) →ₗ[R] Z.obj :=
    (LinearMap.range f.hom.hom).liftQ a.hom.hom (range_le_ker a ha)
  let torsion_le_ker {Z : FinitelyGeneratedTorsionFreeModuleCat R}
      (a : Y ⟶ Z) (ha : f ≫ a = 0) :
      Submodule.torsion R (Y.obj ⧸ LinearMap.range f.hom.hom) ≤
        LinearMap.ker (rangeLift a ha) := by
    intro x hx
    rw [LinearMap.mem_ker]
    obtain ⟨r, hr⟩ := (Submodule.mem_torsion_iff x).mp hx
    change (r : R) • x = 0 at hr
    have h := congrArg (fun z : Y.obj ⧸ LinearMap.range f.hom.hom =>
      rangeLift a ha z) hr
    have h' : (r : R) • rangeLift a ha x = 0 := by
      simpa only [map_smul, map_zero] using h
    exact (Module.isTorsionFree_iff_smul_eq_zero.mp Z.property.2
      (r : R) (rangeLift a ha x) h').resolve_left
        (nonZeroDivisors.ne_zero r.prop)
  let quotientLift {Z : FinitelyGeneratedTorsionFreeModuleCat R}
      (a : Y ⟶ Z) (ha : f ≫ a = 0) :
      torsionFreeCokernel f ⟶ Z := by
    apply ObjectProperty.homMk
    change ModuleCat.of R (torsionFreeCokernelModule f) ⟶ Z.obj
    let g : (Y.obj ⧸ LinearMap.range f.hom.hom) ⧸
        Submodule.torsion R (Y.obj ⧸ LinearMap.range f.hom.hom) →ₗ[R] Z.obj :=
      (Submodule.torsion R (Y.obj ⧸ LinearMap.range f.hom.hom)).liftQ
        (rangeLift a ha) (torsion_le_ker a ha)
    exact ModuleCat.ofHom g
  refine ⟨CokernelCofork.IsColimit.ofπ (torsionFreeCokernelπ f)
    (torsionFreeCokernel_comp f)
    (fun {Z} a ha => quotientLift a ha)
    (fun {Z} a ha => by
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      change ((Submodule.torsion R (Y.obj ⧸ LinearMap.range f.hom.hom)).liftQ
        (rangeLift a ha) (torsion_le_ker a ha)).comp
        ((Submodule.torsion R (Y.obj ⧸ LinearMap.range f.hom.hom)).mkQ.comp
          (LinearMap.range f.hom.hom).mkQ) = a.hom.hom
      rw [← LinearMap.comp_assoc, Submodule.liftQ_mkQ]
      dsimp [rangeLift]
      rw [Submodule.liftQ_mkQ])
    (fun {Z} a ha m hm => by
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      refine Quotient.inductionOn' x ?_
      intro y
      refine Quotient.inductionOn' y ?_
      intro z
      have hm' := congrArg (fun g : Y ⟶ Z => g.hom.hom) hm
      change m.hom.hom.comp
          ((Submodule.torsion R (Y.obj ⧸ LinearMap.range f.hom.hom)).mkQ.comp
            (LinearMap.range f.hom.hom).mkQ) = a.hom.hom at hm'
      have h₁ := congrArg
        (fun g : Y.obj →ₗ[R] Z.obj => g z) hm'
      change m.hom.hom
          ((Submodule.torsion R (Y.obj ⧸ LinearMap.range f.hom.hom)).mkQ
            ((LinearMap.range f.hom.hom).mkQ z)) = a.hom.hom z at h₁
      have h₂ :
          (quotientLift a ha).hom.hom
              ((Submodule.torsion R (Y.obj ⧸ LinearMap.range f.hom.hom)).mkQ
                ((LinearMap.range f.hom.hom).mkQ z)) =
            a.hom.hom z := by
        change ((Submodule.torsion R (Y.obj ⧸ LinearMap.range f.hom.hom)).liftQ
            (rangeLift a ha) (torsion_le_ker a ha))
            ((Submodule.torsion R (Y.obj ⧸ LinearMap.range f.hom.hom)).mkQ
              ((LinearMap.range f.hom.hom).mkQ z)) = a.hom.hom z
        calc
          _ = (rangeLift a ha) ((LinearMap.range f.hom.hom).mkQ z) := by
            have hq := congrArg
              (fun g : (Y.obj ⧸ LinearMap.range f.hom.hom) →ₗ[R] Z.obj =>
                g ((LinearMap.range f.hom.hom).mkQ z))
              ((Submodule.torsion R (Y.obj ⧸ LinearMap.range f.hom.hom)).liftQ_mkQ
                (rangeLift a ha) (torsion_le_ker a ha))
            simpa only [LinearMap.comp_apply] using hq
          _ = a.hom.hom z := by
            dsimp [rangeLift]
      change m.hom.hom
          ((Submodule.torsion R (Y.obj ⧸ LinearMap.range f.hom.hom)).mkQ
            ((LinearMap.range f.hom.hom).mkQ z)) =
        (quotientLift a ha).hom.hom
          ((Submodule.torsion R (Y.obj ⧸ LinearMap.range f.hom.hom)).mkQ
            ((LinearMap.range f.hom.hom).mkQ z))
      exact h₁.trans h₂.symm)⟩

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
  have hmono : Mono integerDoublingMap := by
    constructor
    intro Z g h eq
    dsimp [integerModule] at g h
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have eq' := congrArg
      (fun t : Z ⟶ integerModule => t.hom.hom) eq
    change (integerDoubling.comp g.hom.hom) =
        (integerDoubling.comp h.hom.hom) at eq'
    have hx := congrArg (fun t : Z.obj →ₗ[ℤ] ℤ => t x) eq'
    dsimp [integerModule] at hx
    have hz := (Module.isTorsionFree_iff_smul_eq_zero.mp
      (by infer_instance : Module.IsTorsionFree ℤ (ModuleCat.of ℤ ℤ))
      (2 : ℤ) (g.hom.hom x - h.hom.hom x) (by
        change (LinearMap.lsmul ℤ ℤ 2)
            (g.hom.hom x - h.hom.hom x) = 0
        have hxy : (LinearMap.lsmul ℤ ℤ 2) (g.hom.hom x) =
            (LinearMap.lsmul ℤ ℤ 2) (h.hom.hom x) := by
          simpa [LinearMap.lsmul_apply, integerDoubling,
            LinearMap.smulRight_apply, LinearMap.id_apply, smul_eq_mul,
            mul_comm, LinearMap.comp_apply] using hx
        calc
          (LinearMap.lsmul ℤ ℤ 2) (g.hom.hom x - h.hom.hom x) =
              (LinearMap.lsmul ℤ ℤ 2) (g.hom.hom x) -
                (LinearMap.lsmul ℤ ℤ 2) (h.hom.hom x) := by
            exact (LinearMap.lsmul ℤ ℤ 2).map_sub _ _
          _ = 0 := sub_eq_zero.mpr hxy))
    exact sub_eq_zero.mp (hz.resolve_left (by norm_num))
  have hepi : Epi integerDoublingMap := by
    constructor
    intro Z g h eq
    dsimp [integerModule] at g h
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ℤ at x
    have eq' := congrArg
      (fun t : integerModule ⟶ Z => t.hom.hom) eq
    change (g.hom.hom.comp integerDoubling) =
        (h.hom.hom.comp integerDoubling) at eq'
    have hx := congrArg (fun t : ℤ →ₗ[ℤ] Z.obj => t x) eq'
    dsimp [integerModule] at hx
    have hx' : g.hom.hom (integerDoubling x) = h.hom.hom (integerDoubling x) := by
      change g.hom.hom (integerDoubling x) = h.hom.hom (integerDoubling x) at hx
      exact hx
    have hmapg := g.hom.hom.map_smul (2 : ℤ) x
    have hmaph := h.hom.hom.map_smul (2 : ℤ) x
    have hz := (Module.isTorsionFree_iff_smul_eq_zero.mp Z.property.2
      (2 : ℤ) (g.hom.hom x - h.hom.hom x) (by
        change (LinearMap.lsmul ℤ Z.obj 2)
            (g.hom.hom x - h.hom.hom x) = 0
        have hxy : (LinearMap.lsmul ℤ Z.obj 2) (g.hom.hom x) =
            (LinearMap.lsmul ℤ Z.obj 2) (h.hom.hom x) := by
          rw [LinearMap.lsmul_apply, LinearMap.lsmul_apply]
          calc
            _ = g.hom.hom ((2 : ℤ) • x) := hmapg.symm
            _ = g.hom.hom (integerDoubling x) := by
              congr 1
              simp [integerDoubling, LinearMap.smulRight_apply,
                LinearMap.id_apply, smul_eq_mul, mul_comm]
            _ = h.hom.hom (integerDoubling x) := hx'
            _ = h.hom.hom ((2 : ℤ) • x) := by
              congr 1
              simp [integerDoubling, LinearMap.smulRight_apply,
                LinearMap.id_apply, smul_eq_mul, mul_comm]
            _ = _ := hmaph
        calc
          (LinearMap.lsmul ℤ Z.obj 2) (g.hom.hom x - h.hom.hom x) =
              (LinearMap.lsmul ℤ Z.obj 2) (g.hom.hom x) -
                (LinearMap.lsmul ℤ Z.obj 2) (h.hom.hom x) := by
            exact (LinearMap.lsmul ℤ Z.obj 2).map_sub _ _
          _ = 0 := sub_eq_zero.mpr hxy))
    exact sub_eq_zero.mp (hz.resolve_left (by norm_num))
  have hkzero : IsZero (kernel integerDoublingMap) :=
    isZero_kernel_of_mono integerDoublingMap
  have hczero : IsZero (cokernel integerDoublingMap) :=
    isZero_cokernel_of_epi integerDoublingMap
  have hkι : kernel.ι integerDoublingMap = 0 :=
    hkzero.eq_of_src _ _
  have hcoiπ : IsIso (Abelian.coimage.π integerDoublingMap) := by
    change IsIso (cokernel.π (kernel.ι integerDoublingMap))
    let g : Abelian.coimage integerDoublingMap ⟶ integerModule :=
      cokernel.desc (kernel.ι integerDoublingMap) (𝟙 _)
        (by rw [hkι, zero_comp])
    refine ⟨⟨g, ?_⟩⟩
    refine ⟨cokernel.π_desc (kernel.ι integerDoublingMap) (𝟙 _) _, ?_⟩
    apply (cancel_epi (cokernel.π (kernel.ι integerDoublingMap))).1
    simp [g]
  have hπ : cokernel.π integerDoublingMap = 0 :=
    hczero.eq_of_tgt _ _
  have himι : IsIso (Abelian.image.ι integerDoublingMap) := by
    change IsIso (kernel.ι (cokernel.π integerDoublingMap))
    let g : integerModule ⟶ Abelian.image integerDoublingMap :=
      kernel.lift (cokernel.π integerDoublingMap) (𝟙 _)
        (by rw [hπ, comp_zero])
    refine ⟨⟨g, ?_⟩⟩
    refine ⟨?_, kernel.lift_ι (cokernel.π integerDoublingMap) (𝟙 _)
      (by rw [hπ, comp_zero])⟩
    apply (cancel_mono (kernel.ι (cokernel.π integerDoublingMap))).1
    simp [g, Category.assoc]
  have hnotiso : ¬ IsIso integerDoublingMap := by
    intro hIso
    let : IsIso integerDoublingMap := hIso
    let invF : integerModule ⟶ integerModule := inv integerDoublingMap
    have hinv : invF.hom.hom.comp integerDoubling = LinearMap.id := by
      have h' : integerDoublingMap ≫ invF = 𝟙 integerModule := by
        dsimp [invF]
        exact IsIso.hom_inv_id integerDoublingMap
      have h'' : integerDoublingMap.hom ≫ invF.hom =
          𝟙 (ModuleCat.of ℤ ℤ) := by
        exact congrArg
          (fun q : integerModule ⟶ integerModule => q.hom) h'
      have h''' := congrArg
        (fun q : integerModule.obj ⟶ integerModule.obj => q.hom) h''
      exact h'''
    let one : integerModule.obj := by
      change ℤ
      exact 1
    have h1 : invF.hom.hom (integerDoubling one) = one := by
      have h1' := congrArg
        (fun q : integerModule.obj →ₗ[ℤ] integerModule.obj => q one) hinv
      exact h1'
    have htwo : (2 : ℤ) • one = integerDoubling one := by
      change (2 : ℤ) • (1 : ℤ) = integerDoubling (1 : ℤ)
      simp [integerDoubling, LinearMap.smulRight_apply, LinearMap.id_apply,
        smul_eq_mul, mul_comm]
    have hlin := invF.hom.hom.map_smul (2 : ℤ) one
    have hlin' : (2 : ℤ) • invF.hom.hom one = one := by
      calc
        (2 : ℤ) • invF.hom.hom one = invF.hom.hom ((2 : ℤ) • one) :=
          (map_smul invF.hom.hom (2 : ℤ) one).symm
        _ = invF.hom.hom (integerDoubling one) := by rw [htwo]
        _ = one := h1
    let invOne : ℤ := by
      change ℤ
      exact invF.hom.hom one
    have hcontra : (2 : ℤ) * invOne = 1 := by
      change (2 : ℤ) * invOne = 1
      exact hlin'
    omega
  intro hcomp
  let : IsIso (Abelian.coimageImageComparison integerDoublingMap) := hcomp
  have hmapiso : IsIso integerDoublingMap := by
    rw [← Formalization.Books.Homology.Unit03.coimage_image_factorization
      integerDoublingMap]
    infer_instance
  exact hnotiso hmapiso

end Formalization.Books.Exercises.Unit03
