import Formalization.Books.Sheaves.Unit04.AbelianPresheaves
import Formalization.Books.Sheaves.Unit07.Sheaves
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Topology.Sheaves.Forget
import Mathlib.Topology.Sheaves.SheafCondition.EqualizerProducts

/-!
# Sheaves on Spaces, Chapter 8: Abelian sheaves

The source section is formalized with the canonical `AddCommGrpCat`-valued
presheaves and sheaves.  The abelian sheaf predicate is the source's
underlying-set sheaf condition, while `TopCat.Sheaf AddCommGrpCat X` is the
canonical category of such sheaves.  The exact sequence over an open cover is
presented with Mathlib's equalizer-products maps and `ShortComplex.Exact`.
-/

namespace Formalization.Books.Sheaves.Unit08

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit03
open Formalization.Books.Sheaves.Unit04
open Formalization.Books.Sheaves.Unit07

universe w v

/-! ## Abelian sheaves and their category -/

/-- An abelian sheaf on `X`, namely an abelian presheaf whose underlying
presheaf of sets is a sheaf. -/
abbrev AbelianSheaf {X : TopCat.{v}} (F : AbelianPresheaf.{w, v} X) : Prop :=
  SetSheaf (underlyingPresheaf F)

/-- The category `Ab(X)` of sheaves of abelian groups on `X`. -/
abbrev Ab (X : TopCat.{v}) := TopCat.Sheaf AddCommGrpCat.{w} X

/-- The source's underlying-set definition agrees with the canonical
`AddCommGrpCat`-valued sheaf condition. -/
theorem abelianSheaf_iff_categoryValuedSheaf
    {X : TopCat.{w}} (F : AbelianPresheaf.{w, w} X) :
    AbelianSheaf F ↔ TopCat.Presheaf.IsSheaf F := by
  change TopCat.Presheaf.IsSheaf
      (F ⋙ (CategoryTheory.forget AddCommGrpCat.{w})) ↔
    TopCat.Presheaf.IsSheaf F
  exact (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
    (CategoryTheory.forget AddCommGrpCat.{w}) F).symm

/-- The presheaf underlying an object of `Ab(X)` satisfies the source's
abelian-sheaf predicate. -/
theorem abelianSheaf_of_categoryValuedSheaf
    {X : TopCat.{w}} (F : Ab.{w, w} X) :
    AbelianSheaf F.presheaf := by
  exact (abelianSheaf_iff_categoryValuedSheaf F.presheaf).2 F.property

/-! ## The exact sequence attached to an open cover -/

universe u

/-- The product of sections over the members of an open cover. -/
noncomputable abbrev abelianSheafCoverSectionsProduct
    {X : TopCat.{u}} {ι : Type u} (F : AbelianPresheaf.{u, u} X)
    (U : ι → Opens X) :=
  TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens F U

/-- The product of sections over all pairwise intersections in an open cover. -/
noncomputable abbrev abelianSheafCoverIntersectionProduct
    {X : TopCat.{u}} {ι : Type u} (F : AbelianPresheaf.{u, u} X)
    (U : ι → Opens X) :=
  TopCat.Presheaf.SheafConditionEqualizerProducts.piInters F U

/-- The restriction map from sections over the union to the product of
sections over the members of the cover. -/
noncomputable abbrev abelianSheafCoverRestriction
    {X : TopCat.{u}} {ι : Type u} (F : AbelianPresheaf.{u, u} X)
    (U : ι → Opens X) :
    F.obj (op (iSup U)) ⟶ abelianSheafCoverSectionsProduct F U :=
  TopCat.Presheaf.SheafConditionEqualizerProducts.res F U

/-- Restriction of the first member of each pair to its intersection. -/
noncomputable abbrev abelianSheafCoverLeftRestriction
    {X : TopCat.{u}} {ι : Type u} (F : AbelianPresheaf.{u, u} X)
    (U : ι → Opens X) :
    abelianSheafCoverSectionsProduct F U ⟶
      abelianSheafCoverIntersectionProduct F U :=
  TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes F U

/-- Restriction of the second member of each pair to its intersection. -/
noncomputable abbrev abelianSheafCoverRightRestriction
    {X : TopCat.{u}} {ι : Type u} (F : AbelianPresheaf.{u, u} X)
    (U : ι → Opens X) :
    abelianSheafCoverSectionsProduct F U ⟶
      abelianSheafCoverIntersectionProduct F U :=
  TopCat.Presheaf.SheafConditionEqualizerProducts.rightRes F U

/-- The map sending a family `(s_i)` to the family of differences
`s_{i₀}|_{U_{i₀} ∩ U_{i₁}} - s_{i₁}|_{U_{i₀} ∩ U_{i₁}}`. -/
noncomputable abbrev abelianSheafCoverDifference
    {X : TopCat.{u}} {ι : Type u} (F : AbelianPresheaf.{u, u} X)
    (U : ι → Opens X) :
    abelianSheafCoverSectionsProduct F U ⟶
      abelianSheafCoverIntersectionProduct F U :=
  abelianSheafCoverLeftRestriction F U - abelianSheafCoverRightRestriction F U

/-- The short complex at the product of sections in the source's exact
sequence. -/
noncomputable def abelianSheafCoverShortComplex
    {X : TopCat.{u}} {ι : Type u} (F : AbelianPresheaf.{u, u} X)
    (U : ι → Opens X) : ShortComplex AddCommGrpCat.{u} where
  f := abelianSheafCoverRestriction F U
  g := abelianSheafCoverDifference F U
  zero := by
    rw [Preadditive.comp_sub]
    rw [TopCat.Presheaf.SheafConditionEqualizerProducts.w]
    exact sub_self _

/-- Exactness of the displayed complex
`0 → F(⋃ U_i) → ∏_i F(U_i) → ∏_(i₀,i₁) F(U_{i₀} ∩ U_{i₁})`. -/
abbrev AbelianSheafCoverExact
    {X : TopCat.{u}} {ι : Type u} (F : AbelianPresheaf.{u, u} X)
    (U : ι → Opens X) : Prop :=
  Mono (abelianSheafCoverRestriction F U) ∧
    (abelianSheafCoverShortComplex F U).Exact

/-- For an abelian presheaf, the sheaf condition is equivalent to exactness
of the source's cover complex for every open cover. -/
theorem abelianSheaf_iff_cover_exact
    {X : TopCat.{u}} (F : AbelianPresheaf.{u, u} X) :
    AbelianSheaf F ↔
      ∀ ⦃ι : Type u⦄ (U : ι → Opens X), AbelianSheafCoverExact F U := by
  sorry

end Formalization.Books.Sheaves.Unit08
