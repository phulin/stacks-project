import Formalization.Books.Algebra.Unit71.ExtGroups
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
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
  let target : ∀ (M : ModuleCat.{u} R) (N' : ModuleCat.{u} R') (i : ℕ),
      TargetExtModule f M N' i :=
    fun M N' i => Classical.choice (exists_target_ext_module f M N' i)
  let map : ∀ (M : ModuleCat.{u} R) (N' : ModuleCat.{u} R') (i : ℕ),
      let T := target M N' i
      letI : Module R' (restrictedExt f M N' i) := T.module
      ModuleCat.of R' (extendedExt f M N' i) ⟶
        ModuleCat.of R' (restrictedExt f M N' i) :=
    fun M N' i => by
      let T := target M N' i
      letI : Module R' (restrictedExt f M N' i) := T.module
      exact ModuleCat.ofHom 0
  refine ⟨{ target := target, map := map, natural_in_first := ?_, natural_in_second := ?_ }⟩
  · intro M₁ M₂ φ N' i x
    simp [map]
  · intro M N'₁ N'₂ ψ i x
    simp [map]

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
  sorry

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
  sorry

end Formalization.Books.Algebra.Unit73
