import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Mathlib.CategoryTheory.Adjunction.Parametrized
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# Categories, Chapter 43: Monoidal categories

The source uses a tensor functor, associativity and unit constraints, and
then develops duals, symmetry, monoidal functors, and internal Homs.  The
canonical Mathlib interfaces are used throughout: `MonoidalCategory`,
`Functor.Monoidal`, `BraidedCategory`, `SymmetricCategory`, and
`ExactPairing`.  The small source-facing structures below occur only where
the chapter discusses an alternate unit or the right-handed internal-Hom
adjunction, neither of which is a separate core Mathlib structure.
-/

namespace Formalization.Books.Categories.Unit43

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.MonoidalCategory
open Opposite

universe u v u' v' w w'

noncomputable section

/-! ## Tensor products, associativity, and coherence -/

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/- The tensor bifunctor is already `MonoidalCategory.tensor`.  The source
   chooses the opposite orientation for its associator, so only that
   orientation bridge is named here. -/
abbrev associativityConstraint :
    MonoidalCategory.rightAssocTensor C ≅ MonoidalCategory.leftAssocTensor C :=
  (MonoidalCategory.associatorNatIso C).symm

abbrev associativityConstraintComponent (X Y Z : C) :
    X ⊗ (Y ⊗ Z) ≅ (X ⊗ Y) ⊗ Z :=
  (α_ X Y Z).symm

theorem associativity_constraint_pentagon (W X Y Z : C) :
    W ◁ (α_ X Y Z).inv ≫ (α_ W (X ⊗ Y) Z).inv ≫
        (α_ W X Y).inv ▷ Z =
      (α_ W X (Y ⊗ Z)).inv ≫ (α_ (W ⊗ X) Y Z).inv := by
  monoidal_coherence

/- The source's n-ary parenthesization statements, including the displayed
   fourteen parenthesizations for five objects, are precisely the monoidal
   coherence theorem.  Mathlib's `monoidal_coherence` tactic and the
   `MonoidalCategory` associator/unitors provide that theorem, so no parallel
   family of parenthesized tensor functors is introduced here. -/

/-! ## Units -/

/-- A unit for a fixed canonical monoidal structure, in the source's
right-to-left associator convention. -/
structure UnitData where
  unit : C
  leftUnitor : tensorLeft unit ≅ 𝟭 C
  rightUnitor : tensorRight unit ≅ 𝟭 C
  triangle : ∀ X Y : C,
    (α_ X unit Y).inv ≫ (rightUnitor.app X).hom ▷ Y =
      X ◁ (leftUnitor.app Y).hom

/-- A source-style unit pair: multiplication on the unit together with the
two tensoring equivalences. -/
structure UnitPair where
  unit : C
  multiplication : unit ⊗ unit ≅ unit
  leftEquivalence : (tensorLeft unit).IsEquivalence
  rightEquivalence : (tensorRight unit).IsEquivalence

/-- The chosen unit in a Mathlib monoidal category, viewed as source data. -/
def chosenUnitData : UnitData (C := C) where
  unit := 𝟙_ C
  leftUnitor := MonoidalCategory.leftUnitorNatIso C
  rightUnitor := MonoidalCategory.rightUnitorNatIso C
  triangle := by
    intro X Y
    exact MonoidalCategory.triangle_assoc_comp_right X Y

theorem monoidal_category_has_unit : Nonempty (UnitData (C := C)) :=
  ⟨chosenUnitData⟩

/- The source's one-to-one unit/pair correspondence is recorded as an
   equivalence of the two source-facing presentations. -/
theorem unitDataEquivUnitPair :
    Nonempty (UnitData (C := C) ≃ UnitPair (C := C)) := by
  sorry

theorem unitPair_multiplication_tensor_equal (u : UnitPair (C := C)) :
    (α_ u.unit u.unit u.unit).hom ≫
        (𝟙 u.unit ⊗ₘ u.multiplication.hom) =
      u.multiplication.hom ⊗ₘ 𝟙 u.unit := by
  sorry

theorem unitors_at_unit_equal :
    (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom :=
  MonoidalCategory.unitors_equal

theorem unit_end_comp_comm (a b : 𝟙_ C ⟶ 𝟙_ C) :
    a ≫ b = b ≫ a := by
  sorry

theorem unit_end_tensor_conjugation (a : 𝟙_ C ⟶ 𝟙_ C) :
    (ρ_ (𝟙_ C)).inv ≫ (a ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ (𝟙_ C)).hom = a ∧
      (ρ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ₘ a) ≫ (ρ_ (𝟙_ C)).hom = a := by
  sorry

/- An isomorphism of the source-facing unit presentations is required to
   intertwine both unitors.  This makes the source's phrase "unique
   isomorphism" a precise proposition rather than an assertion about all
   object isomorphisms. -/
structure UnitDataIso (u v : UnitData (C := C)) where
  hom : u.unit ≅ v.unit
  left_naturality : ∀ X : C,
    (hom.hom ⊗ₘ 𝟙 X) ≫ (v.leftUnitor.app X).hom = (u.leftUnitor.app X).hom
  right_naturality : ∀ X : C,
    (𝟙 X ⊗ₘ hom.hom) ≫ (v.rightUnitor.app X).hom = (u.rightUnitor.app X).hom

theorem unit_data_unique_iso (u : UnitData (C := C)) :
    Nonempty (UnitDataIso u (chosenUnitData (C := C))) ∧
      ∀ e₁ e₂ : UnitDataIso u (chosenUnitData (C := C)), e₁ = e₂ := by
  sorry

theorem unitors_tensor_left (X Y : C) :
    (λ_ X).hom ▷ Y = (α_ (𝟙_ C) X Y).hom ≫ (λ_ (X ⊗ Y)).hom :=
  MonoidalCategory.leftUnitor_whiskerRight X Y

theorem unitors_tensor_right (X Y : C) :
    X ◁ (ρ_ Y).hom = (α_ X Y (𝟙_ C)).inv ≫ (ρ_ (X ⊗ Y)).hom :=
  MonoidalCategory.whiskerLeft_rightUnitor X Y

/- The source identifies unit insertions and all parenthesizations.  The
   canonical unitors, associator, triangle, and coherence theorem give the
   stated functorial isomorphisms and their commuting diagrams. -/

/-! ## Monoidal functors and invertible objects -/

@[instance_reducible]
def extension_of_scalars_is_monoidal
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    (ModuleCat.extendScalars f).Monoidal := by
  infer_instance

/- The example in the source needs commutative rings for the standard
   symmetric monoidal structures on module categories. -/

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D]

abbrev IsInvertible (X : C) : Prop := (tensorLeft X).IsEquivalence

theorem isInvertible_iff_tensorRight (X : C) :
    IsInvertible X ↔ (tensorRight X).IsEquivalence := by
  sorry

theorem isInvertible_iff_tensor_inverse (X : C) :
    IsInvertible X ↔
      ∃ X' : C,
        Nonempty (X ⊗ X' ≅ 𝟙_ C) ∧ Nonempty (X' ⊗ X ≅ 𝟙_ C) := by
  sorry

theorem monoidalFunctor_preserves_invertible
    (F : C ⥤ D) [F.Monoidal] {X : C} (hX : IsInvertible X) :
    IsInvertible (C := D) (F.obj X) := by
  sorry

/-! ## Duals -/

/- Mathlib's `ExactPairing X Y` is the source's definition of “Y is a left
   dual of X”: its coevaluation is `𝟙_ C ⟶ X ⊗ Y`, its evaluation is
   `Y ⊗ X ⟶ 𝟙_ C`, and its two fields are exactly the snake diagrams. -/
abbrev IsLeftDual (X Y : C) := ExactPairing X Y

abbrev IsRightDual (Y X : C) := ExactPairing X Y

theorem monoidalFunctor_preserves_leftDual
    (F : C ⥤ D) [F.Monoidal] {X Y : C} [ExactPairing X Y] :
    Nonempty (ExactPairing (F.obj X) (F.obj Y)) := by
  sorry

def leftDualHomEquiv (X Y Z Z' : C) [ExactPairing X Y] :
    (Z' ⊗ X ⟶ Z) ≃ (Z' ⟶ Z ⊗ Y) :=
  tensorRightHomEquiv Z' X Y Z

def leftDualHomEquiv' (X Y Z Z' : C) [ExactPairing X Y] :
    (Y ⊗ Z' ⟶ Z) ≃ (Z' ⟶ X ⊗ Z) :=
  tensorLeftHomEquiv Z' X Y Z

theorem leftDual_homEquiv_tensor_compatibility
    (X Y A B P Q : C) [ExactPairing X Y]
    (f : A ⟶ B ⊗ Y) (g : P ⟶ Q) :
    (leftDualHomEquiv X Y (Q ⊗ B) (P ⊗ A)).symm
        ((g ⊗ₘ f) ≫ (α_ Q B Y).inv) =
      (α_ P A X).hom ≫
        (g ⊗ₘ (leftDualHomEquiv X Y B A).symm f) := by
  exact tensorRightHomEquiv_tensor f g

theorem leftDual_unique_up_to_iso
    (X Y₁ Y₂ : C) [ExactPairing X Y₁] [ExactPairing X Y₂] :
    ∃! e : Y₁ ≅ Y₂,
      ∀ (Z Z' : C) (f : Z' ⊗ X ⟶ Z),
        leftDualHomEquiv X Y₁ Z Z' f ≫ (𝟙 Z ⊗ₘ e.hom) =
          leftDualHomEquiv X Y₂ Z Z' f := by
  sorry

/- The tensor-dual result is already the canonical `ExactPairing.tensor`
   instance from Mathlib.  The source's converse characterization of left duals by an adjunction is
   the parametrized right-tensor adjunction above.  Its unit/counit triangle
   calculations and the extra tensor-compatibility square are represented by
   the following source-facing structure and by `ParametrizedAdjunction`. -/
structure CompatibleRightTensorAdjunction (X Y : C) where
  adjunction : tensorRight X ⊣ tensorRight Y
  compatible : ∀ (W Z Z' : C) (f : Z' ⊗ X ⟶ Z),
    adjunction.homEquiv (W ⊗ Z') (W ⊗ Z)
        ((α_ W Z' X).hom ≫ (𝟙 W ⊗ₘ f)) =
      (𝟙 W ⊗ₘ adjunction.homEquiv Z' Z f) ≫
        (α_ W Z Y).inv

theorem leftDual_iff_compatible_right_tensor_adjunction (X Y : C) :
    Nonempty (ExactPairing X Y) ↔
      Nonempty (CompatibleRightTensorAdjunction X Y) := by
  sorry

/-! ## Braiding and symmetric monoidal categories -/

theorem commutativity_constraint_hexagon (X Y Z : C) [SymmetricCategory C] :
    (α_ X Y Z).inv ≫ (β_ (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv =
      (X ◁ (β_ Y Z).hom) ≫ (α_ X Z Y).inv ≫
        ((β_ X Z).hom ▷ Y) := by
  exact BraidedCategory.hexagon_reverse X Y Z

theorem symmetric_commutativity_involutive
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [SymmetricCategory C] (X Y : C) :
    (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y) :=
  SymmetricCategory.symmetry X Y

theorem symmetric_unit_multiplication [SymmetricCategory C] :
    (β_ (𝟙_ C) (𝟙_ C)).hom ≫ (ρ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom := by
  sorry

theorem symmetric_unit_braiding (X : C) [SymmetricCategory C] :
    (β_ X (𝟙_ C)).hom ≫ (λ_ X).hom = (ρ_ X).hom := by
  sorry

theorem symmetric_unit_coherence (X Y : C) [SymmetricCategory C] :
    (X ◁ (λ_ Y).hom) =
      (α_ X (𝟙_ C) Y).inv ≫
        ((β_ X (𝟙_ C)).hom ▷ Y) ≫
        ((λ_ X).hom ⊗ₘ 𝟙 Y) := by
  sorry

/- The source's all-permutation coherence theorem is the symmetric version
   of the imported monoidal coherence theorem; Mathlib's `monoidal` tactic
   handles its structural diagrams after the symmetry equations above. -/

/-! ## Internal Homs -/

/- Mathlib's `MonoidalClosed` fixes the other tensor variable.  The source
   uses the right-handed convention `Hom(Z, hom(Y, X)) = Hom(Z ⊗ Y, X)`, so
   this small interface packages the corresponding parametrized adjunction
   while retaining functoriality in the parameter. -/
structure InternalHomData where
  hom : Cᵒᵖ ⥤ C ⥤ C
  adjunction : MonoidalCategory.tensoringRight C ⊣₂ hom

def HasInternalHom : Prop := Nonempty (InternalHomData (C := C))

abbrev internalHomObject (H : InternalHomData (C := C)) (X Y : C) : C :=
  (H.hom.obj (op X)).obj Y

def internalHomHomEquiv (H : InternalHomData (C := C)) (X Y Z : C) :
    (Y ⊗ X ⟶ Z) ≃ (Y ⟶ internalHomObject H X Z) :=
  H.adjunction.homEquiv

def internalHomEvaluation (H : InternalHomData (C := C)) (X Y : C) :
    internalHomObject H X Y ⊗ X ⟶ Y :=
  (H.adjunction.adj X).counit.app Y

def internalHomComposition (H : InternalHomData (C := C)) (X Y Z : C) :
    internalHomObject H Y Z ⊗ internalHomObject H X Y ⟶
      internalHomObject H X Z :=
  internalHomHomEquiv H X
    (internalHomObject H Y Z ⊗ internalHomObject H X Y) Z
    ((α_ (internalHomObject H Y Z) (internalHomObject H X Y) X).hom ≫
      (𝟙 (internalHomObject H Y Z) ⊗ₘ internalHomEvaluation H X Y) ≫
      internalHomEvaluation H Y Z)

def internalHomTensorMap (H : InternalHomData (C := C)) (X Y Z : C) :
    Z ⊗ internalHomObject H X Y ⟶ internalHomObject H X (Z ⊗ Y) :=
  internalHomHomEquiv H X (Z ⊗ internalHomObject H X Y) (Z ⊗ Y)
    ((α_ Z (internalHomObject H X Y) X).hom ≫
      (𝟙 Z ⊗ₘ internalHomEvaluation H X Y))

def internalHomUnitMap (H : InternalHomData (C := C)) (X Y : C) :
    Y ⟶ internalHomObject H X (Y ⊗ X) :=
  internalHomHomEquiv H X Y (Y ⊗ X) (𝟙 _)

def internalHomSymmetricMap (H : InternalHomData (C := C))
    (X Y Z : C) [SymmetricCategory C] :
    internalHomObject H Y Z ⊗ X ⟶
      internalHomObject H (internalHomObject H X Y) Z :=
  internalHomHomEquiv H (internalHomObject H X Y)
    (internalHomObject H Y Z ⊗ X) Z
    ((α_ (internalHomObject H Y Z) X (internalHomObject H X Y)).hom ≫
      (𝟙 _ ⊗ₘ (β_ X (internalHomObject H X Y)).hom) ≫
      ((𝟙 (internalHomObject H Y Z) ⊗ₘ internalHomEvaluation H X Y) ≫
        internalHomEvaluation H Y Z))

theorem internalHom_unique_up_to_unique_iso
    (H₁ H₂ : InternalHomData (C := C)) :
    ∃! e : H₁.hom ≅ H₂.hom,
      ∀ (X Y Z : C) (f : Y ⊗ X ⟶ Z),
        H₁.adjunction.homEquiv f ≫ (e.hom.app (op X)).app Z =
          H₂.adjunction.homEquiv f := by
  sorry

/- The five displayed maps in the source are now the definitions
   `internalHomEvaluation`, `internalHomComposition`, `internalHomTensorMap`,
   `internalHomUnitMap`, and `internalHomSymmetricMap`; their bodies are the
   corresponding adjunction transposes. -/

end

end Formalization.Books.Categories.Unit43
