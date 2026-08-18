import Formalization.Books.Algebra.Unit71.ExtGroups
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.RingTheory.RingHom.Flat

/-!
# Commutative Algebra, Chapter 73: Functorialities for Ext

This file records the change-of-rings functorialities for the Ext groups
introduced in Chapter 71.  Restriction and extension of scalars are kept in
Mathlib's canonical `ModuleCat` form.  The target-scalar action in the first
change-of-rings statement is recorded by its postcomposition formula.
-/

namespace Formalization.Books.Algebra.Unit73

open CategoryTheory

universe u

/-! ## Change of rings -/

/-- The `R`-module obtained by restricting an `R'`-module along `f`. -/
noncomputable abbrev restrictedModule {R R' : Type u} [Ring R] [Ring R'] (f : R →+* R')
    (N' : ModuleCat.{u} R') : ModuleCat.{u} R :=
  (ModuleCat.restrictScalars f).obj N'

/-- The extension-of-scalars module attached to `f` and an `R`-module. -/
noncomputable abbrev extendedModule {R R' : Type u} [CommRing R] [CommRing R'] (f : R →+* R')
    (M : ModuleCat.{u} R) : ModuleCat.{u} R' :=
  (ModuleCat.extendScalars f).obj M

/-- The target of the second change-of-rings map, viewed as an `R`-module. -/
noncomputable abbrev restrictedExtendedModule {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') (N : ModuleCat.{u} R) : ModuleCat.{u} R :=
  (ModuleCat.extendScalars f ⋙ ModuleCat.restrictScalars f).obj N

/-- The scalar endomorphism of a restricted `R'`-module, regarded as an
`R`-linear map. -/
noncomputable def targetScalarMap {R R' : Type u} [CommRing R] [CommRing R'] (f : R →+* R')
    (N' : ModuleCat.{u} R') (s : R') : restrictedModule f N' ⟶ restrictedModule f N' := by
  exact (ModuleCat.restrictScalars f).map
    (ModuleCat.ofHom (LinearMap.lsmul R' N' s))

/-- The Ext group in the first change-of-rings statement, with its source
module regarded as an `R`-module. -/
abbrev restrictedExt {R R' : Type u} [Ring R] [Ring R'] (f : R →+* R')
    (M : ModuleCat.{u} R) (N' : ModuleCat.{u} R') (i : ℕ) : Type u :=
  Formalization.Books.Algebra.Unit71.ExtGroup M (restrictedModule f N') i

/-- The Ext group over `R'` occurring on the source side of the canonical
change-of-rings map. -/
abbrev extendedExt {R R' : Type u} [CommRing R] [CommRing R'] (f : R →+* R')
    (M : ModuleCat.{u} R) (N' : ModuleCat.{u} R') (i : ℕ) : Type u :=
  Formalization.Books.Algebra.Unit71.ExtGroup (extendedModule f M) N' i

/-- A natural `R'`-module structure on `Ext_R(M, N')`, expressed by the
postcomposition action of scalar endomorphisms of `N'`. -/
structure TargetExtModule {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') (M : ModuleCat.{u} R) (N' : ModuleCat.{u} R') (i : ℕ) where
  module : Module R' (restrictedExt f M N' i)
  smul_restricts : ∀ (r : R) (x : restrictedExt f M N' i),
    letI : Module R' (restrictedExt f M N' i) := module
    f r • x = r • x
  smul_eq_postcomp : ∀ (s : R') (x : restrictedExt f M N' i),
    letI : Module R' (restrictedExt f M N' i) := module
    s • x =
      ((CategoryTheory.Abelian.Ext.mk₀ (targetScalarMap f N' s)).postcomp M
        (Nat.add_zero i)) x

/-- The source section's natural `R'`-module structure on the restricted Ext
group. -/
theorem exists_target_ext_module {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') (M : ModuleCat.{u} R) (N' : ModuleCat.{u} R') (i : ℕ) :
    Nonempty (TargetExtModule f M N' i) := by
  have h_one : targetScalarMap f N' 1 = 𝟙 _ := by
    ext x
    change (1 : R') • x = x
    exact one_smul R' x
  have h_zero : targetScalarMap f N' 0 = 0 := by
    ext x
    change (0 : R') • x = 0
    exact zero_smul R' x
  have h_add (a b : R') : targetScalarMap f N' (a + b) =
      targetScalarMap f N' a + targetScalarMap f N' b := by
    ext x
    change (a + b) • x = a • x + b • x
    exact add_smul a b x
  have h_mul (a b : R') : targetScalarMap f N' (a * b) =
      targetScalarMap f N' a ≫ targetScalarMap f N' b := by
    ext x
    change (a * b) • x = b • (a • x)
    simpa [mul_comm] using (mul_smul b a x)
  let E := restrictedExt f M N' i
  let scalar : R' → E → E := fun s x =>
    ((CategoryTheory.Abelian.Ext.mk₀ (targetScalarMap f N' s)).postcomp M
      (Nat.add_zero i)) x
  have h_one_action (x : E) : scalar 1 x = x := by
    unfold scalar
    rw [h_one]
    change x.comp (CategoryTheory.Abelian.Ext.mk₀
      (𝟙 (restrictedModule f N'))) (Nat.add_zero i) = x
    exact CategoryTheory.Abelian.Ext.comp_mk₀_id x
  have h_zero_action (x : E) : scalar 0 x = 0 := by
    unfold scalar
    change x.comp (CategoryTheory.Abelian.Ext.mk₀
      (targetScalarMap f N' 0)) (Nat.add_zero i) = 0
    rw [h_zero, CategoryTheory.Abelian.Ext.mk₀_zero,
      CategoryTheory.Abelian.Ext.comp_zero]
  have h_add_action (a b : R') (x : E) :
      scalar (a + b) x = scalar a x + scalar b x := by
    unfold scalar
    rw [h_add, CategoryTheory.Abelian.Ext.mk₀_add]
    change x.comp (CategoryTheory.Abelian.Ext.mk₀
      (targetScalarMap f N' a) +
        CategoryTheory.Abelian.Ext.mk₀ (targetScalarMap f N' b))
        (Nat.add_zero i) =
      x.comp (CategoryTheory.Abelian.Ext.mk₀ (targetScalarMap f N' a))
        (Nat.add_zero i) +
        x.comp (CategoryTheory.Abelian.Ext.mk₀ (targetScalarMap f N' b))
          (Nat.add_zero i)
    rw [CategoryTheory.Abelian.Ext.comp_add]
  have h_mul_action (a b : R') (x : E) :
      scalar (a * b) x = scalar a (scalar b x) := by
    unfold scalar
    rw [show a * b = b * a by rw [mul_comm], h_mul b a]
    change x.comp (CategoryTheory.Abelian.Ext.mk₀
      (targetScalarMap f N' b ≫ targetScalarMap f N' a)) (Nat.add_zero i) =
      (x.comp (CategoryTheory.Abelian.Ext.mk₀ (targetScalarMap f N' b))
        (Nat.add_zero i)).comp
        (CategoryTheory.Abelian.Ext.mk₀ (targetScalarMap f N' a))
          (Nat.add_zero i)
    rw [CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero,
      CategoryTheory.Abelian.Ext.mk₀_comp_mk₀]
  let module : Module R' E :=
    { toDistribMulAction :=
        { toMulAction :=
            { smul := scalar
              one_smul := h_one_action
              mul_smul := h_mul_action }
          smul_zero := by
            intro a
            change ((CategoryTheory.Abelian.Ext.mk₀
              (targetScalarMap f N' a)).postcomp M (Nat.add_zero i)) 0 = 0
            simp
          smul_add := by
            intro a x y
            change ((CategoryTheory.Abelian.Ext.mk₀
              (targetScalarMap f N' a)).postcomp M (Nat.add_zero i)) (x + y) =
              ((CategoryTheory.Abelian.Ext.mk₀
                (targetScalarMap f N' a)).postcomp M (Nat.add_zero i)) x +
                ((CategoryTheory.Abelian.Ext.mk₀
                  (targetScalarMap f N' a)).postcomp M (Nat.add_zero i)) y
            simp }
      add_smul := h_add_action
      zero_smul := h_zero_action }
  refine ⟨{ module := module, smul_restricts := ?_, smul_eq_postcomp := ?_ }⟩
  · intro r x
    change ((CategoryTheory.Abelian.Ext.mk₀
      (targetScalarMap f N' (f r))).postcomp M (Nat.add_zero i)) x = r • x
    have h_restrict : targetScalarMap f N' (f r) =
        r • (𝟙 (restrictedModule f N') : restrictedModule f N' ⟶
          restrictedModule f N') := by
      ext y
      change f r • y = r • y
      rfl
    rw [h_restrict]
    simpa [CategoryTheory.Abelian.Ext.postcomp] using
      (CategoryTheory.Abelian.Ext.smul_eq_comp_mk₀ x r).symm
  · intro s x
    rfl

/-- The change-of-rings map on Ext, obtained by first applying restriction of
scalars and then precomposing with the unit of the extension/restriction
adjunction. -/
noncomputable def changeOfRingsExtMap {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') (M : ModuleCat.{u} R) (N' : ModuleCat.{u} R') (i : ℕ) :
    extendedExt f M N' i → restrictedExt f M N' i :=
  fun x =>
    (CategoryTheory.Abelian.Ext.mk₀
      (ModuleCat.ExtendRestrictScalarsAdj.Unit.map f)).comp
      (x.mapExactFunctor (ModuleCat.restrictScalars f)) (Nat.zero_add i)

/-- A natural family of target-scalar structures and canonical
`R'`-linear change-of-rings maps.  The two naturality fields make explicit the
contravariance in `M` and covariance in `N'`. -/
structure ExtChangeOfRingsData {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') where
  target : ∀ (M : ModuleCat.{u} R) (N' : ModuleCat.{u} R') (i : ℕ),
    TargetExtModule f M N' i
  map : ∀ (M : ModuleCat.{u} R) (N' : ModuleCat.{u} R') (i : ℕ),
    let T := target M N' i
    letI : Module R' (restrictedExt f M N' i) := T.module
    ModuleCat.of R' (extendedExt f M N' i) ⟶
      ModuleCat.of R' (restrictedExt f M N' i)
  map_eq :
    ∀ (M : ModuleCat.{u} R) (N' : ModuleCat.{u} R') (i : ℕ),
      let T := target M N' i
      letI : Module R' (restrictedExt f M N' i) := T.module
      ∀ x : extendedExt f M N' i,
        (map M N' i) x = changeOfRingsExtMap f M N' i x
  natural_in_first :
    ∀ {M₁ M₂ : ModuleCat.{u} R} (φ : M₁ ⟶ M₂)
      (N' : ModuleCat.{u} R') (i : ℕ),
      let T₁ := target M₁ N' i
      let T₂ := target M₂ N' i
      letI : Module R' (restrictedExt f M₁ N' i) := T₁.module
      letI : Module R' (restrictedExt f M₂ N' i) := T₂.module
      ∀ x : extendedExt f M₂ N' i,
        (map M₁ N' i)
            ((CategoryTheory.Abelian.Ext.precompOfLinear
              (CategoryTheory.Abelian.Ext.mk₀ ((ModuleCat.extendScalars f).map φ))
              R' N' (Nat.zero_add i)) x) =
          (CategoryTheory.Abelian.Ext.precompOfLinear
            (CategoryTheory.Abelian.Ext.mk₀ φ) R (restrictedModule f N')
            (Nat.zero_add i)) ((map M₂ N' i) x)
  natural_in_second :
    ∀ (M : ModuleCat.{u} R) {N'₁ N'₂ : ModuleCat.{u} R'} (ψ : N'₁ ⟶ N'₂)
      (i : ℕ),
      let T₁ := target M N'₁ i
      let T₂ := target M N'₂ i
      letI : Module R' (restrictedExt f M N'₁ i) := T₁.module
      letI : Module R' (restrictedExt f M N'₂ i) := T₂.module
      ∀ x : extendedExt f M N'₁ i,
        (map M N'₂ i)
            ((CategoryTheory.Abelian.Ext.postcompOfLinear
              (CategoryTheory.Abelian.Ext.mk₀ ψ) R' (extendedModule f M)
              (Nat.add_zero i)) x) =
          (CategoryTheory.Abelian.Ext.postcompOfLinear
            (CategoryTheory.Abelian.Ext.mk₀ ((ModuleCat.restrictScalars f).map ψ))
            R M (Nat.add_zero i)) ((map M N'₁ i) x)

/-- Existence of the natural canonical change-of-rings family in the first
source item. -/
theorem exists_ext_change_of_rings_data {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') : Nonempty (ExtChangeOfRingsData f) := by
  let target : ∀ (M : ModuleCat R) (N' : ModuleCat R') (i : ℕ),
      TargetExtModule f M N' i :=
    fun M N' i => Classical.choice (exists_target_ext_module f M N' i)
  refine ⟨{
    target := target
    map := fun M N' i => by
      let T := target M N' i
      letI : Module R' (restrictedExt f M N' i) := T.module
      exact ModuleCat.ofHom {
        toFun := changeOfRingsExtMap f M N' i
        map_add' := by
          intro x y
          simp [changeOfRingsExtMap, CategoryTheory.Abelian.Ext.comp_add]
        map_smul' := by
          intro s x
          change
            (CategoryTheory.Abelian.Ext.mk₀
              (ModuleCat.ExtendRestrictScalarsAdj.Unit.map f)).comp
                ((s • x).mapExactFunctor (ModuleCat.restrictScalars f))
              (Nat.zero_add i) = _
          rw [CategoryTheory.Abelian.Ext.smul_eq_comp_mk₀]
          rw [CategoryTheory.Abelian.Ext.mapExactFunctor_comp]
          rw [← CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero]
          rw [CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀]
          exact (T.smul_eq_postcomp s _).symm }
    map_eq := by
      intro M N' i
      dsimp
      intro x
      change changeOfRingsExtMap f M N' i x = _
      rfl
    natural_in_first := by
      intro M₁ M₂ φ N' i
      dsimp
      intro x
      have hunit := (ModuleCat.ExtendRestrictScalarsAdj.unit f).naturality φ
      change φ ≫ (ModuleCat.ExtendRestrictScalarsAdj.unit f).app M₂ =
        (ModuleCat.ExtendRestrictScalarsAdj.unit f).app M₁ ≫
          (ModuleCat.restrictScalars f).map ((ModuleCat.extendScalars f).map φ) at hunit
      change
        (CategoryTheory.Abelian.Ext.mk₀
          (ModuleCat.ExtendRestrictScalarsAdj.Unit.map f)).comp
            (((CategoryTheory.Abelian.Ext.mk₀
              ((ModuleCat.extendScalars f).map φ)).comp x
                (Nat.zero_add i)).mapExactFunctor
              (ModuleCat.restrictScalars f)) (Nat.zero_add i) =
          (CategoryTheory.Abelian.Ext.mk₀ φ).comp
            ((CategoryTheory.Abelian.Ext.mk₀
              (ModuleCat.ExtendRestrictScalarsAdj.Unit.map f)).comp
                (x.mapExactFunctor (ModuleCat.restrictScalars f))
                (Nat.zero_add i)) (Nat.zero_add i)
      rw [CategoryTheory.Abelian.Ext.mapExactFunctor_comp,
        CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀]
      rw [← CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero]
      rw [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀]
      change φ ≫ ModuleCat.ExtendRestrictScalarsAdj.Unit.map f =
        ModuleCat.ExtendRestrictScalarsAdj.Unit.map f ≫
          (ModuleCat.restrictScalars f).map ((ModuleCat.extendScalars f).map φ) at hunit
      rw [← hunit]
      rw [← CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero]
      rw [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀]
    natural_in_second := by
      intro M N'₁ N'₂ ψ i
      dsimp
      intro x
      change
        (CategoryTheory.Abelian.Ext.mk₀
          (ModuleCat.ExtendRestrictScalarsAdj.Unit.map f)).comp
            ((x.comp (CategoryTheory.Abelian.Ext.mk₀ ψ)
              (Nat.add_zero i)).mapExactFunctor
              (ModuleCat.restrictScalars f)) (Nat.zero_add i) =
          ((CategoryTheory.Abelian.Ext.mk₀
              (ModuleCat.ExtendRestrictScalarsAdj.Unit.map f)).comp
                (x.mapExactFunctor (ModuleCat.restrictScalars f))
                (Nat.zero_add i)).comp
            (CategoryTheory.Abelian.Ext.mk₀
              ((ModuleCat.restrictScalars f).map ψ)) (Nat.add_zero i)
      rw [CategoryTheory.Abelian.Ext.mapExactFunctor_comp,
        CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀]
      rw [← CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero] }⟩

/-- The chosen canonical change-of-rings family for the first source item. -/
noncomputable def canonicalExtChangeOfRingsData {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') : ExtChangeOfRingsData f :=
  Classical.choice (exists_ext_change_of_rings_data f)

/-- The canonical `R'`-linear map
`Ext_{R'}(M ⊗_R R', N') → Ext_R(M, N')`. -/
noncomputable def canonicalExtChangeOfRingsMap {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') (M : ModuleCat.{u} R) (N' : ModuleCat.{u} R') (i : ℕ) :
    let D := canonicalExtChangeOfRingsData f
    let T := D.target M N' i
    letI : Module R' (restrictedExt f M N' i) := T.module
    ModuleCat.of R' (extendedExt f M N' i) ⟶
      ModuleCat.of R' (restrictedExt f M N' i) :=
  let D := canonicalExtChangeOfRingsData f
  let T := D.target M N' i
  letI : Module R' (restrictedExt f M N' i) := T.module
  D.map M N' i

/-- In degree zero, the canonical change-of-rings map is the map on Hom induced
by the extension/restriction adjunction. -/
theorem canonicalExtChangeOfRingsMap_zero {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') (M : ModuleCat.{u} R) (N' : ModuleCat.{u} R')
    (x : extendedExt f M N' 0) :
    let D := canonicalExtChangeOfRingsData f
    let T := D.target M N' 0
    letI : Module R' (restrictedExt f M N' 0) := T.module
    Formalization.Books.Algebra.Unit71.extZeroLinearEquiv M (restrictedModule f N')
        (canonicalExtChangeOfRingsMap f M N' 0 x) =
      (ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _
          (Formalization.Books.Algebra.Unit71.extZeroLinearEquiv
          (extendedModule f M) N' x) := by
  dsimp [canonicalExtChangeOfRingsMap]
  let D := canonicalExtChangeOfRingsData f
  let T := D.target M N' 0
  let _ : Module R' (restrictedExt f M N' 0) := T.module
  change Formalization.Books.Algebra.Unit71.extZeroLinearEquiv M
      (restrictedModule f N') ((D.map M N' 0) x) = _
  rw [D.map_eq M N' 0 x]
  have hmap : x.mapExactFunctor (ModuleCat.restrictScalars f) =
      CategoryTheory.Abelian.Ext.mk₀
        ((ModuleCat.restrictScalars f).map
          (Formalization.Books.Algebra.Unit71.extZeroLinearEquiv
            (extendedModule f M) N' x)) := by
    rw [← CategoryTheory.Abelian.Ext.mk₀_linearEquiv₀_apply (R := R') x]
    rw [CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀]
    simp [Formalization.Books.Algebra.Unit71.extZeroLinearEquiv]
  simp [changeOfRingsExtMap, Formalization.Books.Algebra.Unit71.extZeroLinearEquiv,
    hmap]
  change CategoryTheory.Abelian.Ext.homEquiv₀
      (CategoryTheory.Abelian.Ext.mk₀ _) = _
  change (CategoryTheory.Abelian.Ext.homEquiv₀
      (X := M) (Y := restrictedModule f N')).toFun
        ((CategoryTheory.Abelian.Ext.homEquiv₀
          (X := M) (Y := restrictedModule f N')).invFun _) = _
  exact (CategoryTheory.Abelian.Ext.homEquiv₀
    (X := M) (Y := restrictedModule f N')).right_inv _

/-! ## The map obtained from the unit of extension and restriction of scalars -/

/-- The unit map `N → N ⊗_R R'`, viewed as an `R`-linear map. -/
noncomputable def tensorUnitMap {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') (N : ModuleCat.{u} R) :
    N ⟶ (ModuleCat.extendScalars f ⋙ ModuleCat.restrictScalars f).obj N :=
  ModuleCat.ExtendRestrictScalarsAdj.Unit.map f

/-- The natural `R`-linear map
`Ext_R(M, N) → Ext_R(M, N ⊗_R R')`. -/
noncomputable def extTensorMap {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') (M N : ModuleCat.{u} R) (i : ℕ) :
    Formalization.Books.Algebra.Unit71.ExtGroup M N i →ₗ[R]
      Formalization.Books.Algebra.Unit71.ExtGroup M
        ((ModuleCat.extendScalars f ⋙ ModuleCat.restrictScalars f).obj N) i :=
  CategoryTheory.Abelian.Ext.postcompOfLinear
    (CategoryTheory.Abelian.Ext.mk₀ (tensorUnitMap f N)) R M (Nat.add_zero i)

/-- Naturality of the tensor-induced map in the first Ext argument. -/
theorem extTensorMap_natural_in_first {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') {M₁ M₂ : ModuleCat.{u} R} (φ : M₁ ⟶ M₂)
    (N : ModuleCat.{u} R) (i : ℕ) :
    (extTensorMap f M₁ N i).comp
        (CategoryTheory.Abelian.Ext.precompOfLinear
          (CategoryTheory.Abelian.Ext.mk₀ φ) R N (Nat.zero_add i)) =
      (CategoryTheory.Abelian.Ext.precompOfLinear
        (CategoryTheory.Abelian.Ext.mk₀ φ) R
        ((ModuleCat.extendScalars f ⋙ ModuleCat.restrictScalars f).obj N)
        (Nat.zero_add i)).comp (extTensorMap f M₂ N i) := by
  ext x
  simp [extTensorMap, CategoryTheory.Abelian.Ext.precompOfLinear,
    CategoryTheory.Abelian.Ext.postcompOfLinear]

/-- Naturality of the tensor-induced map in the second Ext argument. -/
theorem extTensorMap_natural_in_second {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') (M : ModuleCat.{u} R) {N₁ N₂ : ModuleCat.{u} R}
    (ψ : N₁ ⟶ N₂) (i : ℕ) :
    (extTensorMap f M N₂ i).comp
        (CategoryTheory.Abelian.Ext.postcompOfLinear
          (CategoryTheory.Abelian.Ext.mk₀ ψ) R M (Nat.add_zero i)) =
      (CategoryTheory.Abelian.Ext.postcompOfLinear
        (CategoryTheory.Abelian.Ext.mk₀
          ((ModuleCat.extendScalars f ⋙ ModuleCat.restrictScalars f).map ψ))
        R M (Nat.add_zero i)).comp (extTensorMap f M N₁ i) := by
  have hunit := (ModuleCat.ExtendRestrictScalarsAdj.unit f).naturality ψ
  change ψ ≫ tensorUnitMap f N₂ =
      tensorUnitMap f N₁ ≫ (ModuleCat.restrictScalars f).map
        ((ModuleCat.extendScalars f).map ψ) at hunit
  ext x
  simp [extTensorMap, CategoryTheory.Abelian.Ext.postcompOfLinear, hunit]

/-! ## Flat base change -/

set_option backward.isDefEq.respectTransparency false in
private noncomputable def extendRestrictScalarsCochainAdj
    {R R' : Type u} [CommRing R] [CommRing R'] (f : R →+* R') :
    (ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ) ⊣
      (ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun X Y =>
      { toFun := fun φ =>
          { f := fun i => by
              exact (ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _ (φ.f i)
            comm' := by
              intro i j hij
              change
                (ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _ (φ.f i) ≫
                    (ModuleCat.restrictScalars f).map (Y.d i j) =
                  X.d i j ≫
                    (ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _ (φ.f j)
              rw [← (ModuleCat.extendRestrictScalarsAdj f).homEquiv_naturality_right,
                ← (ModuleCat.extendRestrictScalarsAdj f).homEquiv_naturality_left,
                φ.comm i j]
              simp only [Functor.mapHomologicalComplex_obj_d] }
        invFun := fun ψ =>
          { f := fun i => by
              exact ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm (ψ.f i)
            comm' := by
              intro i j hij
              change
                ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm (ψ.f i) ≫ Y.d i j =
                  (ModuleCat.extendScalars f).map (X.d i j) ≫
                    ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm (ψ.f j)
              have hψ := ψ.comm i j
              change ψ.f i ≫ (ModuleCat.restrictScalars f).map (Y.d i j) =
                  X.d i j ≫ ψ.f j at hψ
              rw [← (ModuleCat.extendRestrictScalarsAdj f).homEquiv_naturality_right_symm,
                ← (ModuleCat.extendRestrictScalarsAdj f).homEquiv_naturality_left_symm,
                hψ] }
        left_inv := by
          intro φ
          apply HomologicalComplex.hom_ext
          intro i
          simp only [Equiv.symm_apply_apply]
        right_inv := by
          intro ψ
          apply HomologicalComplex.hom_ext
          intro i
          simp }
    homEquiv_naturality_left_symm := by
      intro X X' Y f' g
      apply HomologicalComplex.hom_ext
      intro i
      change
        ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm (f'.f i ≫ g.f i) =
          (ModuleCat.extendScalars f).map (f'.f i) ≫
            ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm (g.f i)
      rw [(ModuleCat.extendRestrictScalarsAdj f).homEquiv_naturality_left_symm]
    homEquiv_naturality_right := by
      intro X Y Y' f' g
      apply HomologicalComplex.hom_ext
      intro i
      change
        (ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _ (f'.f i ≫ g.f i) =
          (ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _ (f'.f i) ≫
            (ModuleCat.restrictScalars f).map (g.f i)
      rw [(ModuleCat.extendRestrictScalarsAdj f).homEquiv_naturality_right] }

/-- Flat base change identifies the first change-of-rings Ext map with an
isomorphism.  Mathlib indexes Ext by `ℕ`, so the source condition `i ≥ 0` is
built into the index here. -/
theorem flat_base_change_ext {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') (hf : RingHom.Flat f) (M : ModuleCat.{u} R)
    (N' : ModuleCat.{u} R') (i : ℕ) :
    let D := canonicalExtChangeOfRingsData f
    let T := D.target M N' i
    letI : Module R' (restrictedExt f M N' i) := T.module
    IsIso (D.map M N' i) := by
  dsimp
  let D := canonicalExtChangeOfRingsData f
  let T := D.target M N' i
  let _ : Module R' (restrictedExt f M N' i) := T.module
  change IsIso (D.map M N' i)
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (fun x => D.map M N' i x)
  let : Algebra R R' := f.toAlgebra
  let : (ModuleCat.extendScalars f).Additive := by
    constructor
    intro X Y g h
    change
      ModuleCat.ofHom (LinearMap.baseChange R' (g.hom + h.hom)) =
        ModuleCat.ofHom (LinearMap.baseChange R' g.hom) +
          ModuleCat.ofHom (LinearMap.baseChange R' h.hom)
    rw [LinearMap.baseChange_add]
    rfl
  let : Limits.PreservesFiniteLimits (ModuleCat.extendScalars f) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  let inv : restrictedExt f M N' i → extendedExt f M N' i := fun x =>
    (x.mapExactFunctor (ModuleCat.extendScalars f)).comp
      (CategoryTheory.Abelian.Ext.mk₀
        (ModuleCat.ExtendRestrictScalarsAdj.Counit.map f)) (Nat.add_zero i)
  have hleft (x : extendedExt f M N' i) :
      inv ((ConcreteCategory.hom (D.map M N' i)) x) = x := by
    rw [D.map_eq M N' i x]
    dsimp [inv, changeOfRingsExtMap]
    rw [CategoryTheory.Abelian.Ext.mapExactFunctor_comp,
      CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀]
    let : HasDerivedCategory (ModuleCat.{u} R) := HasDerivedCategory.standard _
    let : HasDerivedCategory (ModuleCat.{u} R') := HasDerivedCategory.standard _
    let W₁ := HomologicalComplex.quasiIso (ModuleCat R) (ComplexShape.up ℤ)
    let W₂ := HomologicalComplex.quasiIso (ModuleCat R') (ComplexShape.up ℤ)
    let : CatCommSq ((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ))
        DerivedCategory.Q DerivedCategory.Q (ModuleCat.extendScalars f).mapDerivedCategory :=
      { iso := (ModuleCat.extendScalars f).mapDerivedCategoryFactors.symm }
    let : CatCommSq ((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℤ))
        DerivedCategory.Q DerivedCategory.Q (ModuleCat.restrictScalars f).mapDerivedCategory :=
      { iso := (ModuleCat.restrictScalars f).mapDerivedCategoryFactors.symm }
    let adjD := (extendRestrictScalarsCochainAdj f).localization
      DerivedCategory.Q W₁ DerivedCategory.Q W₂
      (ModuleCat.extendScalars f).mapDerivedCategory
      (ModuleCat.restrictScalars f).mapDerivedCategory
    let F := (ModuleCat.extendScalars f).mapDerivedCategory
    let G := (ModuleCat.restrictScalars f).mapDerivedCategory
    have h_adj {X : DerivedCategory (ModuleCat R)}
        {Y : DerivedCategory (ModuleCat R')}
        (h : F.obj X ⟶ Y) :
        F.map (adjD.unit.app X) ≫ F.map (G.map h) ≫ adjD.counit.app Y = h := by
      change F.map (adjD.unit.app X) ≫ (G ⋙ F).map h ≫ adjD.counit.app Y = h
      rw [adjD.counit.naturality h]
      have ht : F.map (adjD.unit.app X) ≫ adjD.counit.app (F.obj X) = 𝟙 _ :=
        adjD.left_triangle_components X
      rw [← Category.assoc, ht]
      simp
    apply (CategoryTheory.Abelian.Ext.homEquiv
      (X := extendedModule f M) (Y := N') (n := i)).injective
    simp only [CategoryTheory.Abelian.Ext.comp_hom]
    rw [CategoryTheory.Abelian.Ext.mapExactFunctor_hom]
    rw [CategoryTheory.Abelian.Ext.mapExactFunctor_hom]
    simp only [CategoryTheory.Abelian.Ext.mk₀_hom,
      CategoryTheory.ShiftedHom.mk₀_comp, CategoryTheory.ShiftedHom.comp_mk₀,
      CategoryTheory.ShiftedHom.map, Functor.map_comp, Category.assoc]
    let eF := (ModuleCat.extendScalars f).mapDerivedCategorySingleFunctor 0
    let eG := (ModuleCat.restrictScalars f).mapDerivedCategorySingleFunctor 0
    let X₀ := (DerivedCategory.singleFunctor (ModuleCat R) 0).obj M
    let Y₀ := (shiftFunctor (DerivedCategory (ModuleCat R')) (i : ℤ)).obj
      ((DerivedCategory.singleFunctor (ModuleCat R') 0).obj N')
    have hh := h_adj (X := X₀) (Y := Y₀)
      (eF.hom.app M ≫ CategoryTheory.Abelian.Ext.hom x)
    have hh' :
        eF.inv.app M ≫
            (F.map (adjD.unit.app X₀) ≫
              F.map (G.map (eF.hom.app M ≫ CategoryTheory.Abelian.Ext.hom x)) ≫
                adjD.counit.app Y₀) =
          CategoryTheory.Abelian.Ext.hom x := by
      rw [hh, ← Category.assoc, eF.inv_hom_id_app, Category.id_comp]
    have hunit0 :
        ((extendRestrictScalarsCochainAdj f).unit.app
          (((HomotopyCategory.singleFunctors (ModuleCat R)).functor 0).obj M).as).f 0 =
          ModuleCat.ExtendRestrictScalarsAdj.Unit.map f := by
      ext m
      rfl
    have hcu :
        (CochainComplex.singleFunctor (ModuleCat R) 0).map
            (ModuleCat.ExtendRestrictScalarsAdj.Unit.map f) ≫
          (HomologicalComplex.singleMapHomologicalComplex
            (ModuleCat.restrictScalars f) (ComplexShape.up ℤ) 0).inv.app
              (extendedModule f M) =
        ((extendRestrictScalarsCochainAdj f).unit.app
          (((HomotopyCategory.singleFunctors (ModuleCat R)).functor 0).obj M).as) ≫
          ((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((HomologicalComplex.singleMapHomologicalComplex
              (ModuleCat.extendScalars f) (ComplexShape.up ℤ) 0).hom.app M) := by
      apply HomologicalComplex.hom_ext
      intro j
      by_cases hj : j = 0
      · subst j
        simpa [hunit0, HomologicalComplex.singleMapHomologicalComplex]
      · apply (HomologicalComplex.isZero_single_obj_X
          (ComplexShape.up ℤ) 0 M j hj).eq_of_src
    have heF_unit :
        (DerivedCategory.singleFunctor (ModuleCat R') 0).map
            ((ModuleCat.extendScalars f).map (ModuleCat.ExtendRestrictScalarsAdj.Unit.map f)) ≫
          ((ModuleCat.extendScalars f).mapDerivedCategorySingleFunctor 0).inv.app
            ((ModuleCat.restrictScalars f).obj ((ModuleCat.extendScalars f).obj M)) =
        ((ModuleCat.extendScalars f).mapDerivedCategorySingleFunctor 0).inv.app M ≫
          F.map ((DerivedCategory.singleFunctor (ModuleCat R) 0).map
            (ModuleCat.ExtendRestrictScalarsAdj.Unit.map f)) := by
      exact ((ModuleCat.extendScalars f).mapDerivedCategorySingleFunctor 0).inv.naturality
        (ModuleCat.ExtendRestrictScalarsAdj.Unit.map f)
    have heG_factor :
        eG.inv.app (extendedModule f M) ≫
            (ModuleCat.restrictScalars f).mapDerivedCategoryFactors.hom.app
              ((HomologicalComplex.single (ModuleCat R') (ComplexShape.up ℤ) 0).obj
                (extendedModule f M)) =
          DerivedCategory.Q.map
            ((Functor.mapCochainComplexSingleFunctor
              (ModuleCat.restrictScalars f) 0).inv.app (extendedModule f M)) := by
      simpa [eG, Functor.mapCochainComplexSingleFunctor] using
        (Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app
          (F := ModuleCat.restrictScalars f) (X := extendedModule f M))
    have heG_inv :
        eG.inv.app (extendedModule f M) =
          DerivedCategory.Q.map
              ((Functor.mapCochainComplexSingleFunctor
                (ModuleCat.restrictScalars f) 0).inv.app (extendedModule f M)) ≫
            (CatCommSq.iso ((ModuleCat.restrictScalars f).mapHomologicalComplex
                (ComplexShape.up ℤ)) DerivedCategory.Q DerivedCategory.Q
                (ModuleCat.restrictScalars f).mapDerivedCategory).hom.app
              ((HomologicalComplex.single (ModuleCat R') (ComplexShape.up ℤ) 0).obj
                (extendedModule f M)) := by
      sorry
    dsimp [X₀, Y₀, adjD] at hh'
    erw [CategoryTheory.Adjunction.localization_unit_app,
      CategoryTheory.Adjunction.localization_counit_app] at hh'
    dsimp [F, G] at hh'
    set_option backward.isDefEq.respectTransparency false in
      rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp] at hh'
    simp at hh'
    calc
      _ = _ := by
        sorry
      _ = _ := hh'
  have hright (x : restrictedExt f M N' i) :
      (ConcreteCategory.hom (D.map M N' i)) (inv x) = x := by
    rw [D.map_eq M N' i]
    dsimp [inv, changeOfRingsExtMap]
    let : HasDerivedCategory (ModuleCat.{u} R) := HasDerivedCategory.standard _
    let : HasDerivedCategory (ModuleCat.{u} R') := HasDerivedCategory.standard _
    apply (CategoryTheory.Abelian.Ext.homEquiv
      (X := M) (Y := restrictedModule f N') (n := i)).injective
    simp only [CategoryTheory.Abelian.Ext.comp_hom]
    rw [CategoryTheory.Abelian.Ext.mapExactFunctor_hom]
    let W₁ := HomologicalComplex.quasiIso (ModuleCat R) (ComplexShape.up ℤ)
    let W₂ := HomologicalComplex.quasiIso (ModuleCat R') (ComplexShape.up ℤ)
    let : CatCommSq ((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ))
        DerivedCategory.Q DerivedCategory.Q (ModuleCat.extendScalars f).mapDerivedCategory :=
      { iso := (ModuleCat.extendScalars f).mapDerivedCategoryFactors.symm }
    let : CatCommSq ((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℤ))
        DerivedCategory.Q DerivedCategory.Q (ModuleCat.restrictScalars f).mapDerivedCategory :=
      { iso := (ModuleCat.restrictScalars f).mapDerivedCategoryFactors.symm }
    let adjD := (extendRestrictScalarsCochainAdj f).localization
      DerivedCategory.Q W₁ DerivedCategory.Q W₂
      (ModuleCat.extendScalars f).mapDerivedCategory
      (ModuleCat.restrictScalars f).mapDerivedCategory
    let F := (ModuleCat.extendScalars f).mapDerivedCategory
    let G := (ModuleCat.restrictScalars f).mapDerivedCategory
    have h_adj_right {X : DerivedCategory (ModuleCat R)}
        {Y : DerivedCategory (ModuleCat R')}
        (h : X ⟶ G.obj Y) :
        adjD.unit.app X ≫ G.map (F.map h) ≫ G.map (adjD.counit.app Y) = h := by
      change adjD.unit.app X ≫ (F ⋙ G).map h ≫ G.map (adjD.counit.app Y) = h
      have hn := adjD.unit.naturality h
      change h ≫ adjD.unit.app (G.obj Y) =
        adjD.unit.app X ≫ (F ⋙ G).map h at hn
      have ht : adjD.unit.app (G.obj Y) ≫ G.map (adjD.counit.app Y) = 𝟙 _ :=
        adjD.right_triangle_components Y
      rw [← Category.assoc, ← hn, Category.assoc, ht]
      simp
    simp only [CategoryTheory.Abelian.Ext.mk₀_hom,
      CategoryTheory.ShiftedHom.mk₀_comp,
      CategoryTheory.ShiftedHom.map, Category.assoc]
    let eG := (ModuleCat.restrictScalars f).mapDerivedCategorySingleFunctor 0
    let X₀ := (DerivedCategory.singleFunctor (ModuleCat R) 0).obj M
    let Y₀ := (shiftFunctor (DerivedCategory (ModuleCat R')) (i : ℤ)).obj
      ((DerivedCategory.singleFunctor (ModuleCat R') 0).obj N')
    let h₀ := CategoryTheory.Abelian.Ext.hom x ≫
      (shiftFunctor (DerivedCategory (ModuleCat R)) (i : ℤ)).map
        (eG.inv.app N') ≫
      (Functor.commShiftIso G (i : ℤ)).inv.app
        ((DerivedCategory.singleFunctor (ModuleCat R') 0).obj N')
    have hh := h_adj_right (X := X₀) (Y := Y₀)
      h₀
    have hh' :
        h₀ =
          adjD.unit.app X₀ ≫
            G.map (F.map h₀) ≫
              G.map (adjD.counit.app Y₀) := by
      exact hh.symm
    dsimp [X₀, Y₀, adjD] at hh'
    erw [CategoryTheory.Adjunction.localization_unit_app,
      CategoryTheory.Adjunction.localization_counit_app] at hh'
    dsimp [F, G] at hh'
    set_option backward.isDefEq.respectTransparency false in
      rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp] at hh'
    sorry
  constructor
  · intro x y h
    have := congrArg inv h
    rw [hleft x, hleft y] at this
    exact this
  · intro x
    exact ⟨inv x, hright x⟩

end Formalization.Books.Algebra.Unit73
