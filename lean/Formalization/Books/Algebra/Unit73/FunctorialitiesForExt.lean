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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
