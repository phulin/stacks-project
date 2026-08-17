import Formalization.Books.Sheaves.Unit05.PresheavesOfAlgebraicStructures
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-!
# Sheaves on Spaces, Chapter 13: Stalks of presheaves of algebraic structures

The source span `books/sheaves.tex:1089-1136` is the section
`Stalks of presheaves of algebraic structures`.  A stalk in a category of
algebraic structures is the filtered colimit over the open neighborhoods of a
point.  The fixed-shape functor below uses Mathlib's canonical `colim`
functor, while the underlying-set comparison uses the preservation of this
filtered colimit by the forgetful functor.

The value categories listed in the source reuse the presheaf aliases from
Chapter 5.  Their forgetful functors and the filtered-colimit infrastructure
are recorded at the end of the file.
-/

namespace Formalization.Books.Sheaves.Unit13

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open Formalization.Books.Sheaves.Unit05

universe u w c

noncomputable section

/-! ## Stalks in a category with directed colimits -/

/-- The diagram of sections over the open neighborhoods of a point. -/
abbrev algebraicStalkDiagram
    {X : TopCat.{w}} {C : Type u} [Category.{c} C]
    (𝒜 : PresheafWithValues X C) (x : X) : (OpenNhds x)ᵒᵖ ⥤ C :=
  (OpenNhds.inclusion x).op ⋙ 𝒜

/-- The stalk functor at `x` for `C`-valued presheaves.

The source only assumes directed colimits.  Mathlib's public stalk functor
is packaged under an all-colimits assumption, so this fixed-shape version
uses the same `colim` construction with the weaker filtered-colimit class.
-/
noncomputable def algebraicStalkFunctor
    {X : TopCat.{w}} {C : Type u} [Category.{c} C]
    (x : X) [HasFilteredColimitsOfSize.{w, w} C] :
    PresheafWithValues X C ⥤ C :=
  ((Functor.whiskeringLeft _ _ C).obj (OpenNhds.inclusion x).op) ⋙ colim

/-- The categorical stalk of a `C`-valued presheaf at `x`. -/
abbrev algebraicStalk
    {X : TopCat.{w}} {C : Type u} [Category.{c} C]
    (𝒜 : PresheafWithValues X C) (x : X)
    [HasFilteredColimitsOfSize.{w, w} C] : C :=
  colimit (algebraicStalkDiagram 𝒜 x)

@[simp]
theorem algebraicStalkFunctor_obj
    {X : TopCat.{w}} {C : Type u} [Category.{c} C]
    (x : X) [HasFilteredColimitsOfSize.{w, w} C]
    (𝒜 : PresheafWithValues X C) :
    (algebraicStalkFunctor x).obj 𝒜 = algebraicStalk 𝒜 x :=
  rfl

/-- The canonical cocone defining a categorical stalk. -/
noncomputable def algebraicStalkCocone
    {X : TopCat.{w}} {C : Type u} [Category.{c} C]
    (𝒜 : PresheafWithValues X C) (x : X)
    [HasFilteredColimitsOfSize.{w, w} C] :
    Cocone (algebraicStalkDiagram 𝒜 x) :=
  colimit.cocone _

/-- The neighborhood cocone is a colimit in `C`. -/
noncomputable def algebraicStalkCocone_isColimit
    {X : TopCat.{w}} {C : Type u} [Category.{c} C]
    (𝒜 : PresheafWithValues X C) (x : X)
    [HasFilteredColimitsOfSize.{w, w} C] :
    IsColimit (algebraicStalkCocone 𝒜 x) :=
  colimit.isColimit _

/-- The canonical morphism from sections on `U` to the categorical stalk. -/
noncomputable def algebraicStalkGerm
    {X : TopCat.{w}} {C : Type u} [Category.{c} C]
    (𝒜 : PresheafWithValues X C) (U : Opens X) (x : X) (hx : x ∈ U)
    [HasFilteredColimitsOfSize.{w, w} C] :
    𝒜.obj (op U) ⟶ algebraicStalk 𝒜 x :=
  colimit.ι (algebraicStalkDiagram 𝒜 x) (op ⟨U, hx⟩)

/-! ## The underlying set of the categorical stalk -/

/-- The canonical comparison isomorphism from the underlying set of the
categorical stalk to the stalk of the underlying presheaf of sets. -/
noncomputable def algebraicStalkUnderlyingIso
    {X : TopCat.{w}} {C : Type u} [Category.{c} C]
    (F : C ⥤ Type w) (𝒜 : PresheafWithValues X C) (x : X)
    [HasFilteredColimitsOfSize.{w, w} C]
    [PreservesFilteredColimitsOfSize.{w, w} F] :
    F.obj (algebraicStalk 𝒜 x) ≅
      TopCat.Presheaf.stalk (underlyingPresheaf F 𝒜) x :=
  preservesColimitIso F (algebraicStalkDiagram 𝒜 x)

/-- The underlying-set equivalence identifying the categorical stalk with the
set-valued stalk. -/
def algebraicStalkUnderlyingEquiv
    {X : TopCat.{w}} {C : Type u} [Category.{c} C]
    (F : C ⥤ Type w) (𝒜 : PresheafWithValues X C) (x : X)
    [HasFilteredColimitsOfSize.{w, w} C]
    [PreservesFilteredColimitsOfSize.{w, w} F] :
    F.obj (algebraicStalk 𝒜 x) ≃
      TopCat.Presheaf.stalk (underlyingPresheaf F 𝒜) x :=
  (algebraicStalkUnderlyingIso F 𝒜 x).toEquiv

/-- The source lemma: under faithfulness and preservation of directed
colimits, the categorical stalk exists and has the underlying set-valued
stalk as its canonical underlying-set model. -/
noncomputable def algebraicStalk_underlying_stalk
    {X : TopCat.{w}} {C : Type u} [Category.{c} C]
    (F : C ⥤ Type w) [F.Faithful]
    [HasFilteredColimitsOfSize.{w, w} C]
    [PreservesFilteredColimitsOfSize.{w, w} F]
    (𝒜 : PresheafWithValues X C) (x : X) :
    F.obj (algebraicStalk 𝒜 x) ≃
      TopCat.Presheaf.stalk (underlyingPresheaf F 𝒜) x :=
  algebraicStalkUnderlyingEquiv F 𝒜 x

/-- After applying the faithful forgetful functor, a categorical germ is the
corresponding germ in the underlying presheaf of sets. -/
theorem algebraicStalkGerm_underlying
    {X : TopCat.{w}} {C : Type u} [Category.{c} C]
    (F : C ⥤ Type w) [F.Faithful]
    [HasFilteredColimitsOfSize.{w, w} C]
    [PreservesFilteredColimitsOfSize.{w, w} F]
    (𝒜 : PresheafWithValues X C) (U : Opens X) (x : X) (hx : x ∈ U) :
      F.map (algebraicStalkGerm 𝒜 U x hx) ≫
        (algebraicStalkUnderlyingIso F 𝒜 x).hom =
      (underlyingPresheaf F 𝒜).germ U x hx := by
  unfold algebraicStalkGerm algebraicStalkUnderlyingIso TopCat.Presheaf.germ
  exact ι_preservesColimitIso_hom F (algebraicStalkDiagram 𝒜 x) (op ⟨U, hx⟩)

/-- Faithfulness makes the categorical germ the unique morphism inducing the
specified underlying germ map. -/
theorem algebraicStalkGerm_unique
    {X : TopCat.{w}} {C : Type u} [Category.{c} C]
    (F : C ⥤ Type w) [F.Faithful]
    [HasFilteredColimitsOfSize.{w, w} C]
    [PreservesFilteredColimitsOfSize.{w, w} F]
    (𝒜 : PresheafWithValues X C) (U : Opens X) (x : X) (hx : x ∈ U)
    (φ : 𝒜.obj (op U) ⟶ algebraicStalk 𝒜 x)
    (hφ : F.map φ ≫ (algebraicStalkUnderlyingIso F 𝒜 x).hom =
      (underlyingPresheaf F 𝒜).germ U x hx) :
    φ = algebraicStalkGerm 𝒜 U x hx := by
  apply F.map_injective
  rw [← cancel_mono (algebraicStalkUnderlyingIso F 𝒜 x).hom]
  rw [hφ, algebraicStalkGerm_underlying]

/-! ## The standard algebraic-structure cases -/

/-!
The filtered-colimit presentation for arbitrary groups is available in
Mathlib as `GrpCat.FilteredColimits.colimitCocone`.  Registering the resulting
class here lets the generic stalk construction use exactly the same interface
as the ring and module cases.
-/
noncomputable instance grpCat_hasFilteredColimits :
    HasFilteredColimits (GrpCat.{u}) where
  HasColimitsOfShape := fun _J _ _ =>
    ⟨fun 𝒟 => ⟨GrpCat.FilteredColimits.colimitCocone 𝒟,
      GrpCat.FilteredColimits.colimitCoconeIsColimit 𝒟⟩⟩

/-- The forgetful functor from groups satisfies the hypotheses used for
underlying stalks. -/
theorem groups_stalk_hypotheses :
    HasFilteredColimits (GrpCat.{u}) ∧
      (forget GrpCat.{u}).Faithful ∧
        PreservesFilteredColimits (forget GrpCat.{u}) := by
  exact ⟨inferInstance, groups_forget_faithful, inferInstance⟩

/-- The forgetful functor from rings satisfies the hypotheses used for
underlying stalks. -/
theorem rings_stalk_hypotheses :
    HasFilteredColimits (RingCat.{u}) ∧
      (forget RingCat.{u}).Faithful ∧
        PreservesFilteredColimits (forget RingCat.{u}) := by
  exact ⟨inferInstance, rings_forget_faithful, inferInstance⟩

/-- The forgetful functor from modules over a fixed ring satisfies the
hypotheses used for underlying stalks. -/
theorem modules_stalk_hypotheses (R : Type u) [Ring R] :
    HasFilteredColimits (ModuleCat.{u} R) ∧
      (forget (ModuleCat.{u} R)).Faithful ∧
        PreservesFilteredColimits (forget (ModuleCat.{u} R)) := by
  exact ⟨inferInstance, modules_forget_faithful R, inferInstance⟩

/-- The preceding module statement specializes to vector spaces over a field. -/
theorem vectorSpaces_stalk_hypotheses (K : Type u) [Field K] :
    HasFilteredColimits (ModuleCat.{u} K) ∧
      (forget (ModuleCat.{u} K)).Faithful ∧
        PreservesFilteredColimits (forget (ModuleCat.{u} K)) := by
  exact modules_stalk_hypotheses K

end

end Formalization.Books.Sheaves.Unit13
