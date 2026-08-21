import Formalization.Books.Constructions.Unit02.RelativeGlueing
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Constructions of Schemes, §3 “Relative spectrum via glueing”

This file records the situation and the three precise lemmas in the source section.
The relative spectrum is built from Chapter 2's relative-glueing realization; the
proposition proofs are deferred to the proof stage.
-/

noncomputable section

open CategoryTheory
open TopologicalSpace
open AlgebraicGeometry
open Formalization.Books.Constructions.Unit02

namespace Formalization.Books.Constructions.Unit03

universe u

/-! ## The relative-spectrum situation -/

variable {S : Scheme.{u}}

/-- The underlying sheaf of rings of a sheaf of commutative rings. -/
noncomputable abbrev commRingSheafToRingSheaf
    {X : TopCat.{u}} (A : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) :
    Sheaf (Opens.grothendieckTopology X) RingCat.{u} :=
  (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat RingCat)).obj A

/-- The `𝒪_S`-module underlying a sheaf of commutative `𝒪_S`-algebras. -/
noncomputable def relativeSpectrumUnderlyingModule
    {S : Scheme.{u}}
    (A : Sheaf (Opens.grothendieckTopology S) CommRingCat.{u})
    (algebraMap : S.sheaf ⟶ A) : S.Modules :=
  (SheafOfModules.restrictScalars
    ((sheafCompose (Opens.grothendieckTopology S)
      (forget₂ CommRingCat RingCat)).map algebraMap)).obj
    (SheafOfModules.unit (commRingSheafToRingSheaf A))

/-- A quasi-coherent sheaf of `𝒪_S`-algebras. -/
structure RelativeSpectrumSituation where
  /-- The base scheme. -/
  S : Scheme.{u}
  /-- The sheaf of commutative rings playing the role of `𝒜`. -/
  algebra : Sheaf (Opens.grothendieckTopology S) CommRingCat.{u}
  /-- The structure map `𝒪_S → 𝒜`. -/
  algebraMap : S.sheaf ⟶ algebra
  /-- The underlying `𝒪_S`-module is quasi-coherent. -/
  isQuasiCoherent : (relativeSpectrumUnderlyingModule algebra algebraMap).IsQuasicoherent

namespace RelativeSpectrumSituation

variable (C : RelativeSpectrumSituation)

/-- The value `𝒜(U)` on an open subset. -/
abbrev sections (U : C.S.Opens) : CommRingCat := C.algebra.1.obj (.op U)

/-- The restriction map `𝒜(U) → 𝒜(V)` for `V ⊆ U`. -/
def restriction {U V : C.S.Opens} (hVU : V ≤ U) : sections C U ⟶ sections C V :=
  C.algebra.1.map (homOfLE hVU).op

/-- The ring map `𝒪_S(U) → 𝒜(U)` induced by the algebra structure. -/
abbrev algebraMapOn (U : C.S.Opens) :
    C.S.sheaf.1.obj (.op U) ⟶ sections C U :=
  C.algebraMap.hom.app (.op U)

/-- The morphism `Spec(𝒜(U)) → U` for an affine open `U`. -/
def structureMap (U : C.S.Opens) (hU : IsAffineOpen U) :
    AlgebraicGeometry.Spec (sections C U) ⟶ U.toScheme :=
  AlgebraicGeometry.Spec.map (algebraMapOn C U) ≫ hU.isoSpec.inv

/-- The morphism `Spec(𝒜(V)) → Spec(𝒜(U))` induced by `V ⊆ U`. -/
def inclusion {U V : C.S.Opens} (hVU : V ≤ U) :
    AlgebraicGeometry.Spec (sections C V) ⟶ AlgebraicGeometry.Spec (sections C U) :=
  AlgebraicGeometry.Spec.map (restriction C hVU)

/-- The affine-open transition diagram for the relative spectrum is cartesian. -/
theorem inclusion_isPullback {U V : C.S.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ U) :
    IsPullback (structureMap C V hV) (inclusion C hVU)
      (C.S.homOfLE hVU) (structureMap C U hU) := by
  sorry

/-- The transition map between affine relative spectra is an open immersion. -/
theorem inclusion_isOpenImmersion {U V : C.S.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ U) :
    IsOpenImmersion (inclusion C hVU) := by
  sorry

/-- The affine relative-spectrum transition maps are transitive. -/
theorem inclusion_transitive {U V W : C.S.Opens}
    (_hU : IsAffineOpen U) (_hV : IsAffineOpen V) (_hW : IsAffineOpen W)
    (hVU : V ≤ U) (hWV : W ≤ V) :
    inclusion C hWV ≫ inclusion C hVU = inclusion C (hWV.trans hVU) := by
  change AlgebraicGeometry.Spec.map (C.algebra.1.map (homOfLE hWV).op) ≫
      AlgebraicGeometry.Spec.map (C.algebra.1.map (homOfLE hVU).op) = _
  rw [← AlgebraicGeometry.Spec.map_comp, ← C.algebra.1.map_comp]
  rfl

/-! ## The relative spectrum obtained by glueing -/

/-- The affine-open relative-glueing datum whose local schemes are `Spec(𝒜(U))`. -/
def glueingData : RelativeGlueingData C.S C.S.affineOpens where
  basis := C.S.isBasis_affineOpens
  X := fun U _hU => AlgebraicGeometry.Spec (sections C U)
  f := fun U hU => structureMap C U hU
  rho := fun U V hU hV hVU => inclusion C hVU
  rho_over := by
    intro U V hU hV hVU
    rw [← Category.assoc, ← (inclusion_isPullback C hU hV hVU).w,
      Category.assoc, C.S.homOfLE_ι]
  rho_isPreimage := by
    intro U V hU hV hVU
    sorry
  rho_comp := by
    intro U V W hU hV hW hVU hWV
    exact (inclusion_transitive C hU hV hW hVU hWV).symm

abbrev Realization (C : RelativeSpectrumSituation) :=
  RelativeGlueingRealization (glueingData C)

/-- Existence of the glued relative spectrum and its affine-open charts. -/
theorem relativeSpectrum_exists (C : RelativeSpectrumSituation) :
    Nonempty (Realization C) := by
  exact relative_glueing (glueingData C)

/-- A chosen glued relative spectrum. -/
noncomputable def realization : Realization C :=
  Classical.choice (relativeSpectrum_exists C)

/-- The scheme `\underline{Spec}_S(𝒜)`. -/
noncomputable abbrev relativeSpectrum (C : RelativeSpectrumSituation) : Scheme :=
  (realization C).X

/-- The canonical morphism `\underline{Spec}_S(𝒜) → S`. -/
noncomputable abbrev relativeSpectrumToBase : relativeSpectrum C ⟶ C.S :=
  (realization C).f

/-- The local chart `π⁻¹(U) ≅ Spec(𝒜(U))`. -/
noncomputable abbrev chart (U : C.S.Opens) (hU : IsAffineOpen U) :
    ((relativeSpectrumToBase C) ⁻¹ᵁ U).toScheme ≅ AlgebraicGeometry.Spec (sections C U) :=
  (realization C).i U hU

/-- The local charts are morphisms over the corresponding affine opens. -/
theorem chart_over (U : C.S.Opens) (hU : IsAffineOpen U) :
    (chart C U hU).hom ≫ structureMap C U hU ≫ U.ι =
      ((relativeSpectrumToBase C) ⁻¹ᵁ U).ι ≫ relativeSpectrumToBase C := by
  exact (realization C).i_over U hU

/-- The local charts recover the affine transition maps. -/
theorem chart_transition {U V : C.S.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ U) :
    (chart C V hV).inv ≫ preimageOpenHom (relativeSpectrumToBase C) hVU ≫
        (chart C U hU).hom = inclusion C hVU := by
  exact (realization C).i_rho U V hU hV hVU

/-- Any two charted relative spectra are uniquely isomorphic over `S`. -/
theorem unique (R₁ R₂ : Realization C) :
    ∃! e : R₁.X ≅ R₂.X,
      RelativeGlueingRealizationIsoCondition R₁ R₂ e := by
  exact relative_glueing_unique (glueingData C) R₁ R₂

end RelativeSpectrumSituation

end Formalization.Books.Constructions.Unit03
