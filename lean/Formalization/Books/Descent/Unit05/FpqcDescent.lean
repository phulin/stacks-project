import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-!
# Descent, Chapter 5: Fpqc descent of quasi-coherent sheaves

This file formalizes the two results in the source section.  Mathlib's
`Scheme.Cover`, `Scheme.AffineCover`, `Scheme.fpqcPrecoverage`, and the
generic `Pseudofunctor.DescentData` API provide the ambient notions.  The
chapter-local wrappers below record the quasi-coherent objects and the
finite affine covers used by the source.
-/

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u v

/-! ## The source's standard fpqc coverings -/

/-- A finite affine family of flat morphisms covering a scheme. -/
structure StandardFpqcCover (S : Scheme.{u}) where
  /-- The affine components and their flat maps to `S`. -/
  cover : S.AffineCover (@Flat)
  /-- The family is finite. -/
  finite : Finite cover.I₀

instance (𝒰 : StandardFpqcCover S) : Finite 𝒰.cover.I₀ := 𝒰.finite

/-- View a standard affine fpqc cover as a cover in Mathlib's fpqc
precoverage. -/
noncomputable def StandardFpqcCover.toFpqcCover {S : Scheme.{u}} [IsAffine S]
    (𝒰 : StandardFpqcCover S) : S.Cover Scheme.fpqcPrecoverage := by
  letI : Finite 𝒰.cover.I₀ := 𝒰.finite
  letI : Scheme.JointlySurjective (Scheme.precoverage (@Flat)) :=
    Scheme.instJointlySurjectivePrecoverage
  let E := AffineCover.cover 𝒰.cover
  letI : Finite E.I₀ := 𝒰.finite
  letI : ∀ i : E.I₀, QuasiCompact (E.f i) := fun i => by
    change QuasiCompact (𝒰.cover.f i)
    infer_instance
  letI : QuasiCompactCover E.toPreZeroHypercover := by
    exact QuasiCompactCover.of_finite
  exact Scheme.Cover.ofQuasiCompactCover E

/-! ## Quasi-coherent descent data -/

/-- The pseudofunctor of sheaves of modules, retaining its pullback part. -/
noncomputable def modulesPseudofunctor :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  Scheme.Modules.pseudofunctor.comp Bicategory.Adj.forget₁

/-- The category of quasi-coherent `𝒪_S`-modules. -/
abbrev QuasiCoherentModules (S : Scheme.{u}) :=
  (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory

/-- Descent data for sheaves of modules relative to an indexed family of maps. -/
abbrev ModuleDescentData {S : Scheme.{u}} (𝒰 : S.Cover Scheme.fpqcPrecoverage) :=
  modulesPseudofunctor.DescentData 𝒰.f

/-- The object property selecting descent data whose components are quasi-coherent. -/
def quasiCoherentDescentDataProperty {S : Scheme.{u}}
    (𝒰 : S.Cover Scheme.fpqcPrecoverage) :
    ObjectProperty (ModuleDescentData 𝒰) :=
  fun ξ => ∀ i, (ξ.obj i).IsQuasicoherent

/-- The category of descent data on quasi-coherent sheaves. -/
abbrev QuasiCoherentDescentData {S : Scheme.{u}}
    (𝒰 : S.Cover Scheme.fpqcPrecoverage) :=
  (quasiCoherentDescentDataProperty 𝒰).FullSubcategory

/-! ## The canonical descent functor -/

/-
The quasi-coherence of pullbacks is a standard fact needed to lift the
canonical functor through the full subcategory of quasi-coherent modules.  It
is not present in the imported Mathlib API, so it is recorded here as the
supporting interface used by both descent theorems.
-/
lemma isQuasicoherent_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    [M.IsQuasicoherent] : ((Scheme.Modules.pullback f).obj M).IsQuasicoherent := by
  sorry

/-- The all-module canonical descent-data functor for a cover. -/
noncomputable def ModuleDescentData.toFunctor {S : Scheme.{u}}
    (𝒰 : S.Cover Scheme.fpqcPrecoverage) :
    S.Modules ⥤ ModuleDescentData 𝒰 :=
  modulesPseudofunctor.toDescentData 𝒰.f

/-- The canonical functor from quasi-coherent modules to quasi-coherent
descent data. -/
noncomputable def QuasiCoherentDescentData.toFunctor {S : Scheme.{u}}
    (𝒰 : S.Cover Scheme.fpqcPrecoverage) :
    QuasiCoherentModules S ⥤ QuasiCoherentDescentData 𝒰 :=
  ObjectProperty.lift _
    ((SheafOfModules.isQuasicoherent S.ringCatSheaf).ι ⋙ ModuleDescentData.toFunctor 𝒰)
    (fun M i => by
      exact isQuasicoherent_pullback (𝒰.f i) M.obj)

/-- A quasi-coherent descent datum is effective when it comes from a
quasi-coherent module on the base, up to an isomorphism of descent data. -/
def QuasiCoherentDescentData.IsEffective {S : Scheme.{u}}
    {𝒰 : S.Cover Scheme.fpqcPrecoverage} (ξ : QuasiCoherentDescentData 𝒰) : Prop :=
  ∃ M : QuasiCoherentModules S,
    Nonempty ((QuasiCoherentDescentData.toFunctor 𝒰).obj M ≅ ξ)

/-! ## The two descent statements -/

/-- Effective descent and full faithfulness for a standard affine fpqc cover. -/
theorem standard_fpqc_descent (S : Scheme.{u}) [IsAffine S]
    (𝒰 : StandardFpqcCover S) :
    (∀ ξ : QuasiCoherentDescentData (𝒰.toFpqcCover), ξ.IsEffective) ∧
      Nonempty (QuasiCoherentDescentData.toFunctor 𝒰.toFpqcCover).FullyFaithful := by
  sorry

/-- Effective descent and full faithfulness for an arbitrary fpqc cover. -/
theorem fpqc_descent (S : Scheme.{u})
    (𝒰 : S.Cover Scheme.fpqcPrecoverage) :
    (∀ ξ : QuasiCoherentDescentData 𝒰, ξ.IsEffective) ∧
      Nonempty (QuasiCoherentDescentData.toFunctor 𝒰).FullyFaithful := by
  sorry

end AlgebraicGeometry.Scheme
