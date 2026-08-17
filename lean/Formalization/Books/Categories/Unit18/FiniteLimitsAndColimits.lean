import Formalization.Books.Categories.Unit10.Equalizers
import Mathlib.CategoryTheory.Comma.CardinalArrow
import Mathlib.CategoryTheory.Limits.Constructions.Equalizers
import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.Pullbacks
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.IsConnected
import Mathlib.CategoryTheory.PathCategory.MorphismProperty

/-!
# Categories, Chapter 18: Finite limits and colimits

The source's adjectives “finite”, “nonempty”, and “connected” refer to the
index category.  We use Mathlib's canonical `FinCategory`, `Nonempty`, and
`IsConnected` interfaces directly; no parallel predicates for those index
properties are introduced.  The existence statements below package the
corresponding quantification over finite index categories.
-/

namespace Formalization.Books.Categories.Unit18

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty

universe u v u' v'

noncomputable section

section FiniteDiagramReduction

variable {I : Type u} [Category.{v} I]

/- A finite family of arrows is represented by a finite set in the arrow
   category.  `MorphismProperty.paths` then records exactly the source's
   assertion that every arrow is a composition of members of that family. -/
def HasFiniteGeneratingMorphisms : Prop :=
  ∃ S : Set (Arrow I), S.Finite ∧
    ∀ {X Y : I} (f : X ⟶ Y),
      ∃ p : Quiver.Path X Y,
        (let W : MorphismProperty I := fun _ _ g => Arrow.mk g ∈ S
         W.paths p) ∧ CategoryTheory.composePath p = f

/- Mathlib's `Arrow.finite_iff` is the canonical equivalence between the
   source's “finitely many objects and morphisms” wording and `FinCategory`. -/
theorem finite_index_category_iff {J : Type u} [SmallCategory J] :
    Finite (Arrow J) ↔ Nonempty (FinCategory J) :=
  Arrow.finite_iff J

/- The source's finite replacement is packaged as data so that its finiteness,
   preservation, and connectedness/nonemptiness comparisons remain usable by
   later users.  `Initial` and `Final` are Mathlib's canonical interfaces for
   the limit and colimit preservation asserted by the source. -/
structure FiniteDiagramReplacement (I : Type u) [Category.{v} I] where
  J : Type
  category : SmallCategory J
  finite : @FinCategory J category
  F : @CategoryTheory.Functor J category I (inferInstance : Category.{v} I)
  initial : @Functor.Initial J category I (inferInstance : Category.{v} I) F
  final : @Functor.Final J category I (inferInstance : Category.{v} I) F
  connected_iff : @IsConnected J category ↔ IsConnected I
  nonempty_iff : Nonempty J ↔ Nonempty I

attribute [instance] FiniteDiagramReplacement.category
attribute [instance] FiniteDiagramReplacement.finite
attribute [instance] FiniteDiagramReplacement.initial
attribute [instance] FiniteDiagramReplacement.final

/- The first source lemma: a finite object set together with finitely many
   generating arrows admits a finite replacement with the same (co)limits. -/
theorem finite_diagram_category [Finite I] (hI : HasFiniteGeneratingMorphisms (I := I)) :
    Nonempty (FiniteDiagramReplacement I) := by
  sorry

theorem finite_diagram_replacement_has_limit_iff
    (R : FiniteDiagramReplacement I) {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) :
    HasLimit M ↔ HasLimit (R.F ⋙ M) := by
  sorry

theorem finite_diagram_replacement_has_colimit_iff
    (R : FiniteDiagramReplacement I) {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) :
    HasColimit M ↔ HasColimit (R.F ⋙ M) := by
  sorry

theorem finite_diagram_replacement_limit_iso_unique
    (R : FiniteDiagramReplacement I) {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) [HasLimit M] [HasLimit (R.F ⋙ M)] :
    ∃! e : limit M ≅ limit (R.F ⋙ M),
      ∀ j : R.J, e.hom ≫ limit.π (R.F ⋙ M) j = limit.π M (R.F.obj j) := by
  sorry

noncomputable def finite_diagram_replacement_limit_iso
    (R : FiniteDiagramReplacement I) {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) [HasLimit M] [HasLimit (R.F ⋙ M)] :
    limit M ≅ limit (R.F ⋙ M) :=
  Classical.choose (ExistsUnique.exists (finite_diagram_replacement_limit_iso_unique R M))

theorem finite_diagram_replacement_limit_iso_hom_comp
    (R : FiniteDiagramReplacement I) {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) [HasLimit M] [HasLimit (R.F ⋙ M)] (j : R.J) :
    (finite_diagram_replacement_limit_iso R M).hom ≫ limit.π (R.F ⋙ M) j =
      limit.π M (R.F.obj j) := by
  simpa [finite_diagram_replacement_limit_iso] using
    (Classical.choose_spec
      (ExistsUnique.exists (finite_diagram_replacement_limit_iso_unique R M))) j

theorem finite_diagram_replacement_colimit_iso_unique
    (R : FiniteDiagramReplacement I) {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) [HasColimit M] [HasColimit (R.F ⋙ M)] :
    ∃! e : colimit M ≅ colimit (R.F ⋙ M),
      ∀ j : R.J, colimit.ι M (R.F.obj j) ≫ e.hom =
        colimit.ι (R.F ⋙ M) j := by
  sorry

noncomputable def finite_diagram_replacement_colimit_iso
    (R : FiniteDiagramReplacement I) {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) [HasColimit M] [HasColimit (R.F ⋙ M)] :
    colimit M ≅ colimit (R.F ⋙ M) :=
  Classical.choose (ExistsUnique.exists (finite_diagram_replacement_colimit_iso_unique R M))

theorem finite_diagram_replacement_colimit_iso_hom_comp
    (R : FiniteDiagramReplacement I) {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) [HasColimit M] [HasColimit (R.F ⋙ M)] (j : R.J) :
    colimit.ι M (R.F.obj j) ≫
        (finite_diagram_replacement_colimit_iso R M).hom =
      colimit.ι (R.F ⋙ M) j := by
  simpa [finite_diagram_replacement_colimit_iso] using
    (Classical.choose_spec
      (ExistsUnique.exists (finite_diagram_replacement_colimit_iso_unique R M))) j

end FiniteDiagramReduction

section FiniteExistencePredicates

variable {C : Type u} [Category.{v} C]

/- These four predicates are the chapter-facing quantifiers over the canonical
   Mathlib index-category interfaces.  In particular, `IsConnected` already
   includes nonemptiness. -/
def HasNonemptyFiniteLimits : Prop :=
  ∀ {J : Type*} [SmallCategory J] [FinCategory J] [Nonempty J]
    (F : J ⥤ C), HasLimit F

def HasNonemptyFiniteColimits : Prop :=
  ∀ {J : Type*} [SmallCategory J] [FinCategory J] [Nonempty J]
    (F : J ⥤ C), HasColimit F

def HasConnectedFiniteLimits : Prop :=
  ∀ {J : Type*} [SmallCategory J] [FinCategory J] [IsConnected J]
    (F : J ⥤ C), HasLimit F

def HasConnectedFiniteColimits : Prop :=
  ∀ {J : Type*} [SmallCategory J] [FinCategory J] [IsConnected J]
    (F : J ⥤ C), HasColimit F

/- Connected finite limits are exactly the limits generated by equalizers and
   fibre products. -/
theorem has_connected_finite_limits_iff :
    HasConnectedFiniteLimits (C := C) ↔ HasEqualizers C ∧ HasPullbacks C := by
  sorry

/- The dual connected-colimit statement. -/
theorem has_connected_finite_colimits_iff :
    HasConnectedFiniteColimits (C := C) ↔ HasCoequalizers C ∧ HasPushouts C := by
  sorry

/- The first presentation of nonempty finite limits from the source. -/
theorem has_nonempty_finite_limits_iff :
    HasNonemptyFiniteLimits (C := C) ↔
      HasBinaryProducts C ∧ HasEqualizers C := by
  sorry

section EqualizerFromFibreProducts

variable {C : Type u} [Category.{v} C]

/- This is the displayed construction in the proof of the source's
   `almost-finite-limits` and `finite-limits` lemmas.  The first pullback is
   `A ×_{a,B,b} A`; the second pulls it back along the diagonal of `A × A`. -/
noncomputable def equalizerViaPullbacks [HasBinaryProducts C] [HasPullbacks C]
    {A B : C} (a b : A ⟶ B) : C :=
  pullback
    (prod.lift (pullback.fst a b) (pullback.snd a b))
    (prod.lift (𝟙 A) (𝟙 A))

noncomputable def equalizerViaPullbacksMorphism [HasBinaryProducts C] [HasPullbacks C]
    {A B : C} (a b : A ⟶ B) : equalizerViaPullbacks a b ⟶ A :=
  pullback.snd
    (prod.lift (pullback.fst a b) (pullback.snd a b))
    (prod.lift (𝟙 A) (𝟙 A))

theorem equalizerViaPullbacks_isEqualizer [HasBinaryProducts C] [HasPullbacks C]
    {A B : C} (a b : A ⟶ B) :
    Formalization.Books.Categories.Unit10.IsEqualizer
      (equalizerViaPullbacksMorphism a b) a b := by
  sorry

end EqualizerFromFibreProducts

/- The second presentation of nonempty finite limits from the source. -/
theorem has_nonempty_finite_limits_iff_of_pullbacks :
    HasNonemptyFiniteLimits (C := C) ↔
      HasBinaryProducts C ∧ HasPullbacks C := by
  sorry

/- The first presentation of nonempty finite colimits from the source. -/
theorem has_nonempty_finite_colimits_iff :
    HasNonemptyFiniteColimits (C := C) ↔
      HasBinaryCoproducts C ∧ HasCoequalizers C := by
  sorry

/- The second presentation of nonempty finite colimits from the source. -/
theorem has_nonempty_finite_colimits_iff_of_pushouts :
    HasNonemptyFiniteColimits (C := C) ↔
      HasBinaryCoproducts C ∧ HasPushouts C := by
  sorry

/- The first presentation of finite limits from the source. -/
theorem has_finite_limits_iff :
    HasFiniteLimits C ↔
      HasFiniteProducts C ∧ HasEqualizers C := by
  sorry

/- The second presentation of finite limits from the source. -/
theorem has_finite_limits_iff_of_terminal_and_pullbacks :
    HasFiniteLimits C ↔ HasTerminal C ∧ HasPullbacks C := by
  sorry

/- The first presentation of finite colimits from the source. -/
theorem has_finite_colimits_iff :
    HasFiniteColimits C ↔
      HasFiniteCoproducts C ∧ HasCoequalizers C := by
  sorry

/- The second presentation of finite colimits from the source. -/
theorem has_finite_colimits_iff_of_initial_and_pushouts :
    HasFiniteColimits C ↔ HasInitial C ∧ HasPushouts C := by
  sorry

end FiniteExistencePredicates

end

end Formalization.Books.Categories.Unit18
