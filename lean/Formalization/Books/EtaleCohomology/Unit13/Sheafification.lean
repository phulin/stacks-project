import Formalization.Books.EtaleCohomology.Unit11.Sheaves
import Mathlib.CategoryTheory.Sites.ConcreteSheafification

/-!
# Étale Cohomology, Chapter 13: Sheafification

This file formalizes the source section `Sheafification` in
`books/etale-cohomology.tex`, lines 724--834.  The source's indexed covering
families are represented by Mathlib's canonical covering sieves.  Thus
`Meq` is the compatible-family form of zeroth Čech cohomology, and the
canonical plus/double-plus constructions provide the source's `F⁺` and `F#`.
-/

namespace Formalization.Books.EtaleCohomology.Unit13

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

variable {C : Type u} [Category.{v} C]

/-! ## Čech zero-cohomology -/

/-- A set-valued presheaf on `C`, using Chapter 9's canonical interface. -/
abbrev SetPresheaf (C : Type u) [Category.{v} C] :=
  Formalization.Books.EtaleCohomology.Unit09.Presheaf C

/-- The category of covering sieves over an object. -/
abbrev CoveringCategory (J : GrothendieckTopology C) (U : C) := J.Cover U

/-- The source's zeroth Čech cohomology of a presheaf on a covering.

`Meq` consists of sections on all arrows of the covering sieve satisfying the
pairwise compatibility relations.  It is a set for a set-valued presheaf. -/
abbrev CechH0 (J : GrothendieckTopology C) (F : SetPresheaf C)
    {U : C} (S : CoveringCategory J U) :=
  CategoryTheory.Meq F S

/-- The canonical restriction map from sections over the target to Čech
zero-cocycles on a covering. -/
def cechRestrictionMap (J : GrothendieckTopology C) (F : SetPresheaf C)
    {U : C} (S : CoveringCategory J U) :
    F.obj (op U) → CechH0 J F S :=
  fun s => CategoryTheory.Meq.mk S s

@[simp]
theorem cechRestrictionMap_apply (J : GrothendieckTopology C)
    (F : SetPresheaf C) {U : C} (S : CoveringCategory J U)
    (s : F.obj (op U)) (I : S.Arrow) :
    cechRestrictionMap J F S s I = F.map I.f.op s :=
  rfl

/-! ## Morphisms of coverings -/

/-- A canonical representative of a morphism of coverings.

The field `base` is the source's morphism `χ : V ⟶ U`; `refinement` records
the map from the covering over `V` to the pullback of the covering over `U`.
This is the sieve-level form of the source's choice of `α` and `χ_j`. -/
structure CoveringMorphism (J : GrothendieckTopology C)
    {U V : C} (S : CoveringCategory J V) (T : CoveringCategory J U) where
  base : V ⟶ U
  refinement : S ⟶ T.pullback base

/-- Pull a Čech zero-cocycle back along a morphism of the underlying site. -/
def cechPullback (J : GrothendieckTopology C) (F : SetPresheaf C)
    {U V : C} (f : V ⟶ U) {S : CoveringCategory J U} :
    CechH0 J F S → CechH0 J F (S.pullback f) :=
  fun x => CategoryTheory.Meq.pullback x f

/-- Restrict a compatible family along a refinement of coverings. -/
def cechRefinementMap (J : GrothendieckTopology C) (F : SetPresheaf C)
    {U : C} {S T : CoveringCategory J U} (e : S ⟶ T) :
    CechH0 J F T → CechH0 J F S :=
  fun x => CategoryTheory.Meq.refine x e

/-- The map on Čech zero-cohomology induced by a morphism of coverings. -/
def cechMapOfCoveringMorphism (J : GrothendieckTopology C)
    (F : SetPresheaf C) {U V : C}
    {S : CoveringCategory J V} {T : CoveringCategory J U}
    (m : CoveringMorphism J S T) :
    CechH0 J F T → CechH0 J F S :=
  fun x => cechRefinementMap J F m.refinement (cechPullback J F m.base x)

/- The codomain of `cechMapOfCoveringMorphism` is `CechH0` by construction,
so the source's well-definedness assertion is enforced by the definition.
The following theorem records its independence from the auxiliary choices. -/
theorem cechMapOfCoveringMorphism_independent
    (J : GrothendieckTopology C) (F : SetPresheaf C) {U V : C}
    {S : CoveringCategory J V} {T : CoveringCategory J U}
    {m₁ m₂ : CoveringMorphism J S T} (h : m₁.base = m₂.base) :
    cechMapOfCoveringMorphism J F m₁ =
      cechMapOfCoveringMorphism J F m₂ := by
  sorry

/-! ## The directed covering index and the plus construction -/

/-- The directedness condition for the covering index over one object. -/
def CoveringIndexIsDirected (J : GrothendieckTopology C) (U : C) : Prop :=
  ∀ S T : CoveringCategory J U,
    ∃ W : CoveringCategory J U, W ≤ S ∧ W ≤ T

/-- Two coverings have the common refinement given by their infimum. -/
def commonCoveringRefinement (J : GrothendieckTopology C) {U : C}
    (S T : CoveringCategory J U) : CoveringCategory J U :=
  S ⊓ T

theorem coveringIndex_isDirected (J : GrothendieckTopology C) (U : C) :
    CoveringIndexIsDirected J U := by
  intro S T
  exact ⟨commonCoveringRefinement J S T, inf_le_left, inf_le_right⟩

theorem coveringIndex_nonempty (J : GrothendieckTopology C) (U : C) :
    Nonempty (CoveringCategory J U) :=
  ⟨⊤⟩

section CanonicalPlus

variable (J : GrothendieckTopology C)
variable [instMultiequalizer : ∀ (P : Cᵒᵖ ⥤ Type v) (X : C) (S : J.Cover X),
  HasMultiequalizer (S.index P)]
variable [instCoverColimits : ∀ X : C,
    HasColimitsOfShape (J.Cover X)ᵒᵖ (Type v)]

include instMultiequalizer instCoverColimits

/-- The canonical compatible-family type is equivalent to the
multiequalizer used by Mathlib's plus construction. -/
noncomputable def cechH0CanonicalEquiv (F : SetPresheaf C)
    {U : C} (S : CoveringCategory J U) :
    (J.diagram F U).obj (op S) ≃ CechH0 J F S :=
  CategoryTheory.Meq.equiv F S

/-- The value of the plus construction on sections over `U`. -/
noncomputable def plusValue (F : SetPresheaf C) (U : C) : Type v :=
  colimit (J.diagram F U)

/-- The presheaf `F⁺`, whose value is the directed colimit of Čech data. -/
noncomputable def plusPresheaf (F : SetPresheaf C) : SetPresheaf C :=
  J.plusObj F

theorem plusPresheaf_obj (F : SetPresheaf C) (U : C) :
    (plusPresheaf J F).obj (op U) = plusValue J F U :=
  by
    change colimit (J.diagram F U) = colimit (J.diagram F U)
    rfl

/-- The canonical map of presheaves `F ⟶ F⁺`. -/
noncomputable def plusUnit (F : SetPresheaf C) : F ⟶ plusPresheaf J F :=
  J.toPlus F

/-- The map `F⁺ ⟶ G⁺` induced by a map of presheaves. -/
noncomputable def plusMap {F G : SetPresheaf C} (η : F ⟶ G) :
    plusPresheaf J F ⟶ plusPresheaf J G :=
  J.plusMap η

theorem plusMap_id (F : SetPresheaf C) :
    plusMap J (𝟙 F) = 𝟙 (plusPresheaf J F) := by
  sorry

theorem plusMap_comp {F G H : SetPresheaf C} (η : F ⟶ G) (θ : G ⟶ H) :
    plusMap J (η ≫ θ) = plusMap J η ≫ plusMap J θ := by
  sorry

/-- The plus construction is functorial in the presheaf. -/
noncomputable def plusFunctor : SetPresheaf C ⥤ SetPresheaf C :=
  J.plusFunctor (Type v)

/-- The source's separatedness condition for the plus construction. -/
theorem plus_isSeparated (F : SetPresheaf C) :
    Formalization.Books.EtaleCohomology.Unit11.SeparatedPresheaf J
      (plusPresheaf J F) := by
  sorry

/-- If `F` is separated, `F⁺` is a sheaf. -/
theorem plus_isSheaf_of_isSeparated (F : SetPresheaf C)
    (hF : Formalization.Books.EtaleCohomology.Unit11.SeparatedPresheaf J F) :
    Formalization.Books.EtaleCohomology.Unit11.IsSheaf J
      (plusPresheaf J F) := by
  sorry

/-- If `F` is separated, the canonical map `F ⟶ F⁺` is pointwise injective. -/
theorem plusUnit_pointwise_injective_of_isSeparated
    (F : SetPresheaf C)
    (hF : Formalization.Books.EtaleCohomology.Unit11.SeparatedPresheaf J F) :
    ∀ U : C, Function.Injective ((plusUnit J F).app (op U)) := by
  sorry

/-! ## Double plus and the universal property -/

/-- The canonical double-plus presheaf `F# = (F⁺)⁺`. -/
noncomputable def associatedSheafPresheaf (F : SetPresheaf C) : SetPresheaf C :=
  J.sheafify F

/-- The canonical map `F ⟶ F#`. -/
noncomputable def associatedSheafUnit (F : SetPresheaf C) :
    F ⟶ associatedSheafPresheaf J F :=
  J.toSheafify F

/-- The map on double-plus presheaves induced by a presheaf map. -/
noncomputable def associatedSheafMap {F G : SetPresheaf C} (η : F ⟶ G) :
    associatedSheafPresheaf J F ⟶ associatedSheafPresheaf J G :=
  J.sheafifyMap η

theorem associatedSheaf_isSheaf (F : SetPresheaf C) :
    Formalization.Books.EtaleCohomology.Unit11.IsSheaf J
      (associatedSheafPresheaf J F) := by
  exact J.sheafify_isSheaf F

theorem associatedSheafMap_id (F : SetPresheaf C) :
    associatedSheafMap J (𝟙 F) = 𝟙 (associatedSheafPresheaf J F) := by
  sorry

theorem associatedSheafMap_comp {F G H : SetPresheaf C}
    (η : F ⟶ G) (θ : G ⟶ H) :
    associatedSheafMap J (η ≫ θ) =
      associatedSheafMap J η ≫ associatedSheafMap J θ := by
  sorry

/-- The sheaf-valued sheafification functor `F ↦ F#`. -/
noncomputable def associatedSheafFunctor :
    SetPresheaf C ⥤ CategoryTheory.Sheaf J (Type v) :=
  CategoryTheory.plusPlusSheaf J (Type v)

/-- The double-plus presheaf is the underlying presheaf of the associated
sheaf returned by the canonical sheafification functor. -/
theorem associatedSheafFunctor_obj (F : SetPresheaf C) :
    ((associatedSheafFunctor J).obj F).1 = associatedSheafPresheaf J F := by
  change J.sheafify F = J.sheafify F
  rfl

/-- The adjunction expressing that sheafification is left adjoint to the
forgetful functor from sheaves to presheaves. -/
noncomputable def associatedSheafAdjunction
    :
    associatedSheafFunctor J ⊣
      CategoryTheory.sheafToPresheaf J (Type v) :=
  CategoryTheory.plusPlusAdjunction J (Type v)

/-- The functorial hom-set equivalence induced by the canonical map
`F ⟶ F#`, in the source's direction. -/
noncomputable def sheafificationHomEquiv
    (F : SetPresheaf C) (G : CategoryTheory.Sheaf J (Type v)) :
    (F ⟶ G.1) ≃ ((associatedSheafFunctor J).obj F ⟶ G) :=
  (associatedSheafAdjunction J).homEquiv F G |>.symm

end CanonicalPlus

end Formalization.Books.EtaleCohomology.Unit13
