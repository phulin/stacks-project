import Formalization.Books.Categories.Unit10.Equalizers
import Mathlib.CategoryTheory.Comma.CardinalArrow
import Mathlib.CategoryTheory.Limits.Constructions.Equalizers
import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
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
   connectedness/nonemptiness comparison, existence equivalences, and the
   canonical universal-property isomorphisms remain usable by later users. -/
structure FiniteDiagramReplacement (I : Type u) [Category.{v} I] where
  J : Type
  category : SmallCategory J
  finite : @FinCategory J category
  F : @CategoryTheory.Functor J category I (inferInstance : Category.{v} I)
  connected_iff : @IsConnected J category ↔ IsConnected I
  nonempty_iff : Nonempty J ↔ Nonempty I
  preserves_limits :
    ∀ {C : Type u'} [Category.{v'} C] (M : I ⥤ C),
      HasLimit M ↔ HasLimit (F ⋙ M)
  preserves_colimits :
    ∀ {C : Type u'} [Category.{v'} C] (M : I ⥤ C),
      HasColimit M ↔ HasColimit (F ⋙ M)
  canonical_limit_iso :
    ∀ {C : Type u'} [Category.{v'} C] (M : I ⥤ C)
      [HasLimit M] [HasLimit (F ⋙ M)],
      Nonempty (limit M ≅ limit (F ⋙ M))
  canonical_colimit_iso :
    ∀ {C : Type u'} [Category.{v'} C] (M : I ⥤ C)
      [HasColimit M] [HasColimit (F ⋙ M)],
      Nonempty (colimit M ≅ colimit (F ⋙ M))

attribute [instance] FiniteDiagramReplacement.category

/- The first source lemma: a finite object set together with finitely many
   generating arrows admits a finite replacement with the same (co)limits. -/
theorem finite_diagram_category [Finite I] (hI : HasFiniteGeneratingMorphisms (I := I)) :
    Nonempty (FiniteDiagramReplacement.{u, v, u', v'} I) := by
  sorry

theorem finite_diagram_replacement_has_limit_iff
    (R : FiniteDiagramReplacement.{u, v, u', v'} I) {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) :
    HasLimit M ↔ HasLimit (R.F ⋙ M) := by
  exact R.preserves_limits M

theorem finite_diagram_replacement_has_colimit_iff
    (R : FiniteDiagramReplacement.{u, v, u', v'} I) {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) :
    HasColimit M ↔ HasColimit (R.F ⋙ M) := by
  exact R.preserves_colimits M

theorem finite_diagram_replacement_limit_iso
    (R : FiniteDiagramReplacement.{u, v, u', v'} I) {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) [HasLimit M] [HasLimit (R.F ⋙ M)] :
    Nonempty (limit M ≅ limit (R.F ⋙ M)) := by
  exact R.canonical_limit_iso M

theorem finite_diagram_replacement_colimit_iso
    (R : FiniteDiagramReplacement.{u, v, u', v'} I) {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) [HasColimit M] [HasColimit (R.F ⋙ M)] :
    Nonempty (colimit M ≅ colimit (R.F ⋙ M)) := by
  exact R.canonical_colimit_iso M

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

/- Nonempty finite limits admit the two equivalent presentations from the
   source: binary products plus equalizers, or binary products plus pullbacks. -/
theorem has_nonempty_finite_limits_iff :
    HasNonemptyFiniteLimits (C := C) ↔
      (HasBinaryProducts C ∧ HasEqualizers C) ∧
        (HasBinaryProducts C ∧ HasPullbacks C) := by
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

/- The dual nonempty finite-colimit presentation. -/
theorem has_nonempty_finite_colimits_iff :
    HasNonemptyFiniteColimits (C := C) ↔
      (HasBinaryCoproducts C ∧ HasCoequalizers C) ∧
        (HasBinaryCoproducts C ∧ HasPushouts C) := by
  sorry

/- Finite limits are equivalent to either finite products plus equalizers, or
   a terminal object plus fibre products. -/
theorem has_finite_limits_iff :
    HasFiniteLimits C ↔
      (HasFiniteProducts C ∧ HasEqualizers C) ∧
        (HasTerminal C ∧ HasPullbacks C) := by
  sorry

/- The product-over-the-final-object assertion used in the proof of the
   finite-limit equivalence is Mathlib's canonical comparison isomorphism. -/
noncomputable def binaryProductLimitConeFromTerminalAndPullbacks
    [HasTerminal C] [HasPullbacks C] (A B : C) : LimitCone (pair A B) :=
  limitConeOfTerminalAndPullbacks (pair A B)

noncomputable def binaryProductIsoPullbackOverTerminal [HasTerminal C] [HasPullbacks C]
    {A B : C} [HasBinaryProduct A B] :
    A ⨯ B ≅ pullback (terminal.from A) (terminal.from B) :=
  prodIsoPullback A B

/- The dual finite-colimit equivalence. -/
theorem has_finite_colimits_iff :
    HasFiniteColimits C ↔
      (HasFiniteCoproducts C ∧ HasCoequalizers C) ∧
        (HasInitial C ∧ HasPushouts C) := by
  sorry

end FiniteExistencePredicates

end

end Formalization.Books.Categories.Unit18
