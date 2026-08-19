import Formalization.Books.Sheaves.Unit04.AbelianPresheaves
import Formalization.Books.Sheaves.Unit07.Sheaves
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Topology.Sheaves.Forget
import Mathlib.Topology.Sheaves.SheafCondition.EqualizerProducts
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.RealVectorSpace

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
    AbelianSheaf F ↔ TopCat.Presheaf.IsSheaf F := by sorry
theorem abelianSheaf_of_categoryValuedSheaf
    {X : TopCat.{w}} (F : Ab.{w, w} X) :
    AbelianSheaf F.presheaf := by sorry
abbrev AbelianSheafSurjective {X : TopCat.{v}} {F G : Ab.{w, v} X} (φ : F ⟶ G) : Prop :=
  sorry

/-- In `Ab(X)`, categorical epimorphisms are exactly locally surjective maps. -/
theorem abelianSheaf_epi_iff_surjective
    {X : TopCat.{v}} {F G : Ab.{w, v} X} (φ : F ⟶ G) :
    Epi φ ↔ AbelianSheafSurjective φ := by sorry
noncomputable def countableProductMap {C : Type u} [Category.{v} C]
    [HasCountableProducts C] (A B : ℕ → C) (φ : ∀ n, A n ⟶ B n) :
    limit (Discrete.functor A) ⟶ limit (Discrete.functor B) :=
    by sorry

@[reassoc (attr := simp)] theorem countableProductMap_π
    {C : Type u} [Category.{v} C] [HasCountableProducts C]
    (A B : ℕ → C) (φ : ∀ n, A n ⟶ B n) (n : ℕ) :
    countableProductMap A B φ ≫ limit.π (Discrete.functor B) (Discrete.mk n) =
      limit.π (Discrete.functor A) (Discrete.mk n) ≫ φ n := by sorry
structure CountableShortExactFamily (C : Type u) [Category.{v} C]
    [HasCountableProducts C] [HasZeroMorphisms C] where
  complex : ℕ → ShortComplex C
  shortExact : ∀ n, (complex n).ShortExact
  productMap_not_epi :
    ¬ Epi (countableProductMap (fun n => (complex n).X₂)
      (fun n => (complex n).X₃) (fun n => (complex n).g))

/-- Countable products are exact when they preserve the epimorphism in every
short exact family.  Products already preserve the finite-limit part in an
abelian category, so this is the right obstruction for the source's warning. -/
def CountableProductsExact (C : Type u) [Category.{v} C]
    [Abelian C] [HasCountableProducts C] [HasZeroMorphisms C] : Prop :=
  by sorry

/-- The category of abelian sheaves on the real line, at an arbitrary size. -/
abbrev RealAbelianSheaves.{u} := Ab.{u, 0} (TopCat.of ℝ)

instance realAbelianSheaves_abelian : Abelian (RealAbelianSheaves.{u}) := by sorry
instance realAbelianSheaves_hasCountableProducts :
    HasCountableProducts (RealAbelianSheaves.{u}) := by sorry
noncomputable def realLineShortExactFamily :
    CountableShortExactFamily (RealAbelianSheaves.{u}) := by sorry
theorem realLineShortExactFamily_shortExact (n : ℕ) :
    (realLineShortExactFamily.complex n).ShortExact :=
  realLineShortExactFamily.shortExact n

/-- The product morphism of the real-line family is not an epimorphism. -/
theorem realLineShortExactFamily_product_not_epi :
    ¬ Epi (countableProductMap
      (fun n => (realLineShortExactFamily.complex n).X₂)
      (fun n => (realLineShortExactFamily.complex n).X₃)
      (fun n => (realLineShortExactFamily.complex n).g)) :=
  realLineShortExactFamily.productMap_not_epi

/-- Equivalently, the real-line product morphism is not locally surjective. -/
theorem realLineShortExactFamily_product_not_surjective :
    ¬ AbelianSheafSurjective
      (countableProductMap
        (fun n => (realLineShortExactFamily.complex n).X₂)
        (fun n => (realLineShortExactFamily.complex n).X₃)
        (fun n => (realLineShortExactFamily.complex n).g)) := by sorry
theorem realAbelianSheaves_not_countableProductsExact :
    ¬ CountableProductsExact (RealAbelianSheaves.{u}) := by sorry
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
  zero := by sorry
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
      ∀ ⦃ι : Type u⦄ (U : ι → Opens X), AbelianSheafCoverExact F U := by sorry
