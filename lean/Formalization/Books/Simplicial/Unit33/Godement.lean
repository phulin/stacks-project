import Formalization.Books.Simplicial.Unit20.Augmentations
import Formalization.Books.Simplicial.Unit26.Homotopies
import Mathlib.CategoryTheory.Whiskering

/-!
# Simplicial Methods, Chapter 33: Preparation for standard resolutions

The constructions in this file are expressed in the category of endofunctors.
The source's degreewise maps are kept explicit, while the existence statements
use Mathlib's `SimplicialObject` interface.
-/

noncomputable section

namespace Formalization.Books.Simplicial.Unit33

open CategoryTheory
open CategoryTheory.SimplicialObject
open Opposite

universe v u v' u'

/-! ## Iterated endofunctors and the Godement maps -/

/-- The composite of `n` copies of an endofunctor, with the empty composite
equal to the identity functor. -/
def iteratedEndofunctor {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) : ℕ → C ⥤ C
  | 0 => 𝟭 C
  | n + 1 => Y ⋙ iteratedEndofunctor Y n

/-- The degree `n` endofunctor in Example 33.1 is the composite of `n + 1`
copies of `Y`. -/
def godementDegree {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (n : ℕ) : C ⥤ C :=
  iteratedEndofunctor Y (n + 1)

theorem godementDegree_add {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (n m : ℕ) :
    godementDegree Y (n + m + 1) =
      godementDegree Y n ⋙ godementDegree Y m := by
  sorry

theorem iteratedEndofunctor_add {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (a b : ℕ) :
    iteratedEndofunctor Y (a + b) =
      iteratedEndofunctor Y a ⋙ iteratedEndofunctor Y b := by
  sorry

theorem godementFace_domain_decomposition
    {C : Type u} [Category.{v} C] (Y : C ⥤ C)
    (n : ℕ) (j : Fin (n + 1)) :
    iteratedEndofunctor Y (n + 1) =
      iteratedEndofunctor Y j ⋙ Y ⋙ iteratedEndofunctor Y (n - j) := by
  sorry

theorem godementFace_codomain_decomposition
    {C : Type u} [Category.{v} C] (Y : C ⥤ C)
    (n : ℕ) (j : Fin (n + 1)) :
    iteratedEndofunctor Y n =
      iteratedEndofunctor Y j ⋙ 𝟭 C ⋙ iteratedEndofunctor Y (n - j) := by
  sorry

theorem godementDegeneracy_domain_decomposition
    {C : Type u} [Category.{v} C] (Y : C ⥤ C)
    (n : ℕ) (j : Fin (n + 1)) :
    iteratedEndofunctor Y (n + 1) =
      iteratedEndofunctor Y j ⋙ Y ⋙ iteratedEndofunctor Y (n - j) := by
  exact godementFace_domain_decomposition Y n j

theorem godementDegeneracy_codomain_decomposition
    {C : Type u} [Category.{v} C] (Y : C ⥤ C)
    (n : ℕ) (j : Fin (n + 1)) :
    iteratedEndofunctor Y (n + 2) =
      iteratedEndofunctor Y j ⋙ (Y ⋙ Y) ⋙ iteratedEndofunctor Y (n - j) := by
  sorry

/-- The source's `d^n_j`, expressed as a natural transformation in the
category of endofunctors. -/
def godementFace {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) {n : ℕ} (j : Fin (n + 1)) :
    godementDegree Y n ⟶ iteratedEndofunctor Y n := by
  let raw :
      (iteratedEndofunctor Y j ⋙ Y ⋙ iteratedEndofunctor Y (n - j)) ⟶
        (iteratedEndofunctor Y j ⋙ 𝟭 C ⋙ iteratedEndofunctor Y (n - j)) :=
    Functor.whiskerLeft (iteratedEndofunctor Y j)
      (Functor.whiskerRight d (iteratedEndofunctor Y (n - j)))
  exact eqToHom (godementFace_domain_decomposition Y n j) ≫ raw ≫
    eqToHom (godementFace_codomain_decomposition Y n j).symm

/-- The source's `s^n_j`, expressed as a natural transformation in the
category of endofunctors. -/
def godementDegeneracy {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (s : Y ⟶ Y ⋙ Y) {n : ℕ} (j : Fin (n + 1)) :
    godementDegree Y n ⟶ godementDegree Y (n + 1) := by
  let raw :
      (iteratedEndofunctor Y j ⋙ Y ⋙ iteratedEndofunctor Y (n - j)) ⟶
        (iteratedEndofunctor Y j ⋙ (Y ⋙ Y) ⋙
          iteratedEndofunctor Y (n - j)) :=
    Functor.whiskerLeft (iteratedEndofunctor Y j)
      (Functor.whiskerRight s (iteratedEndofunctor Y (n - j)))
  exact eqToHom (godementDegeneracy_domain_decomposition Y n j) ≫ raw ≫
    eqToHom (godementDegeneracy_codomain_decomposition Y n j).symm

/-! ## The hypotheses and the canonical simplicial-object interface -/

/-- The two unit equations and the coassociativity equation in Lemma 33.2. -/
structure GodementEquations {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) : Prop where
  left_unit : s ≫ Functor.whiskerRight d Y = 𝟙 Y
  right_unit : s ≫ Functor.whiskerLeft Y d = 𝟙 Y
  coassoc : s ≫ Functor.whiskerRight s Y = s ≫ Functor.whiskerLeft Y s

def godementSimplicialFace {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) (n : ℕ) (j : Fin (n + 2)) :
    godementDegree Y (n + 1) ⟶ godementDegree Y n :=
  godementFace Y d j

def godementSimplicialDegeneracy {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (s : Y ⟶ Y ⋙ Y) (n : ℕ) (j : Fin (n + 1)) :
    godementDegree Y n ⟶ godementDegree Y (n + 1) :=
  godementDegeneracy Y s j

structure GodementSimplicialData {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) where
  object : SimplicialObject (C ⥤ C)
  object_obj : ∀ n,
    object.obj (op (SimplexCategory.mk n)) = godementDegree Y n
  face_def : ∀ n (j : Fin (n + 2)),
    eqToHom (object_obj (n + 1)).symm ≫ object.δ j ≫
        eqToHom (object_obj n) = godementSimplicialFace Y d n j
  degeneracy_def : ∀ n (j : Fin (n + 1)),
    eqToHom (object_obj n).symm ≫ object.σ j ≫
        eqToHom (object_obj (n + 1)) =
      godementSimplicialDegeneracy Y s n j

theorem godement_simplicial_data
    {C : Type u} [Category.{v} C] (Y : C ⥤ C)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) (h : GodementEquations Y d s) :
    Nonempty (GodementSimplicialData Y d s) := by
  sorry

theorem godement_simplicial_object
    {C : Type u} [Category.{v} C] (Y : C ⥤ C)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) (h : GodementEquations Y d s) :
    Nonempty (SimplicialObject (C ⥤ C)) := by
  rcases godement_simplicial_data Y d s h with ⟨data⟩
  exact ⟨data.object⟩

/-- The degree-zero transformation used as the augmentation datum in Lemma 33.2.
The resulting simplicial augmentation is stored in `GodementAugmentationData`. -/
def godementAugmentation {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) : Y ⟶ 𝟭 C := d

/-- The canonical component of the augmentation in every degree. -/
def godementAugmentationComponent {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) : (n : ℕ) →
      godementDegree Y n ⟶ 𝟭 C
  | 0 => (Functor.rightUnitor Y).hom ≫ d
  | n + 1 =>
      Functor.whiskerLeft Y (godementAugmentationComponent Y d n) ≫
        Functor.whiskerRight d (𝟭 C) ≫ (Functor.leftUnitor (𝟭 C)).hom

structure GodementAugmentationData {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) where
  /-- The simplicial object whose degrees are the iterated endofunctors. -/
  simplicial : GodementSimplicialData Y d s
  /-- The augmentation as an actual morphism of simplicial objects. -/
  augmentation :
    Formalization.Books.Simplicial.Unit20.Augmentation
      simplicial.object (𝟭 C)
  component : ∀ n, godementDegree Y n ⟶ 𝟭 C
  component_zero : component 0 = godementAugmentationComponent Y d 0
  component_formula : ∀ n,
    eqToHom (simplicial.object_obj n).symm ≫
        augmentation.app (op (SimplexCategory.mk n)) = component n
  face_naturality : ∀ {n} (i : Fin (n + 2)),
    godementFace Y d (n := n + 1) i ≫ component n = component (n + 1)
  degeneracy_naturality : ∀ {n} (i : Fin (n + 1)),
    godementDegeneracy Y s (n := n) i ≫ component (n + 1) = component n

theorem godement_augmentation_condition
    {C : Type u} [Category.{v} C] (Y : C ⥤ C)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) (h : GodementEquations Y d s) :
    Nonempty (GodementAugmentationData Y d s) := by
  sorry

/-! ## Functoriality and sections -/

/-- Whiskering a Godement degree by `F` and `G`. -/
def godementWhiskeredDegree {A : Type u} {B : Type u'} {C : Type v}
    [Category.{v'} A] [Category.{u} B] [Category.{v} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B) (n : ℕ) : A ⥤ B :=
  F ⋙ godementDegree Y n ⋙ G

def godementWhiskeredFace {A : Type u} {B : Type u'} {C : Type v}
    [Category.{v'} A] [Category.{u} B] [Category.{v} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B) (d : Y ⟶ 𝟭 C)
    {n : ℕ} (j : Fin (n + 1)) :
    godementWhiskeredDegree F Y G n ⟶ F ⋙ iteratedEndofunctor Y n ⋙ G :=
  Functor.whiskerRight (Functor.whiskerLeft F (godementFace Y d j)) G

def godementWhiskeredDegeneracy {A : Type u} {B : Type u'} {C : Type v}
    [Category.{v'} A] [Category.{u} B] [Category.{v} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B) (s : Y ⟶ Y ⋙ Y)
    {n : ℕ} (j : Fin (n + 1)) :
    godementWhiskeredDegree F Y G n ⟶
      godementWhiskeredDegree F Y G (n + 1) :=
  Functor.whiskerRight (Functor.whiskerLeft F (godementDegeneracy Y s j)) G

def godementWhiskeredSimplicialFace {A : Type u} {B : Type u'} {C : Type v}
    [Category.{v'} A] [Category.{u} B] [Category.{v} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B) (d : Y ⟶ 𝟭 C)
    (n : ℕ) (j : Fin (n + 2)) :
    godementWhiskeredDegree F Y G (n + 1) ⟶
      godementWhiskeredDegree F Y G n :=
  godementWhiskeredFace F Y G d j

def godementWhiskeredSimplicialDegeneracy
    {A : Type u} {B : Type u'} {C : Type v}
    [Category.{v'} A] [Category.{u} B] [Category.{v} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B) (s : Y ⟶ Y ⋙ Y)
    (n : ℕ) (j : Fin (n + 1)) :
    godementWhiskeredDegree F Y G n ⟶
      godementWhiskeredDegree F Y G (n + 1) :=
  godementWhiskeredDegeneracy F Y G s j

def godementWhiskeredAugmentationComponent
    {A : Type u} {B : Type u'} {C : Type v}
    [Category.{v'} A] [Category.{u} B] [Category.{v} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B) (d : Y ⟶ 𝟭 C) (n : ℕ) :
    godementWhiskeredDegree F Y G n ⟶ F ⋙ G := by
  exact
    Functor.whiskerRight
      (Functor.whiskerLeft F (godementAugmentationComponent Y d n)) G ≫
      (Functor.associator F (𝟭 C) G).hom ≫
      Functor.whiskerLeft F (Functor.rightUnitor G).hom

structure GodementWhiskeredSimplicialData
    {A : Type u} {B : Type u'} {C : Type v}
    [Category.{v'} A] [Category.{u} B] [Category.{v} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) where
  object : SimplicialObject (A ⥤ B)
  object_obj : ∀ n,
    object.obj (op (SimplexCategory.mk n)) = godementWhiskeredDegree F Y G n
  face_def : ∀ n (j : Fin (n + 2)),
    eqToHom (object_obj (n + 1)).symm ≫ object.δ j ≫
        eqToHom (object_obj n) =
      godementWhiskeredSimplicialFace F Y G d n j
  degeneracy_def : ∀ n (j : Fin (n + 1)),
    eqToHom (object_obj n).symm ≫ object.σ j ≫
        eqToHom (object_obj (n + 1)) =
      godementWhiskeredSimplicialDegeneracy F Y G s n j

/-! The functorial example carries the canonical degreewise maps above as an
augmentation of the whiskered simplicial object. -/

structure GodementWhiskeredAugmentationData
    {A : Type u} {B : Type u'} {C : Type v}
    [Category.{v'} A] [Category.{u} B] [Category.{v} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) where
  /-- The simplicial object receiving the augmentation. -/
  simplicial : GodementWhiskeredSimplicialData F Y G d s
  /-- The augmentation of the whiskered simplicial object. -/
  augmentation :
    Formalization.Books.Simplicial.Unit20.Augmentation
      simplicial.object (F ⋙ G)
  component : ∀ n, godementWhiskeredDegree F Y G n ⟶ F ⋙ G
  component_def : ∀ n,
    component n = godementWhiskeredAugmentationComponent F Y G d n
  component_formula : ∀ n,
    eqToHom (simplicial.object_obj n).symm ≫
        augmentation.app (op (SimplexCategory.mk n)) = component n
  face_naturality : ∀ {n} (i : Fin (n + 2)),
    godementWhiskeredSimplicialFace F Y G d n i ≫ component n =
      component (n + 1)
  degeneracy_naturality : ∀ {n} (i : Fin (n + 1)),
    godementWhiskeredSimplicialDegeneracy F Y G s n i ≫ component (n + 1) =
      component n

theorem godement_functorial
    {A : Type u} {B : Type u'} {C : Type v}
    [Category.{v'} A] [Category.{u} B] [Category.{v} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) (h : GodementEquations Y d s) :
    Nonempty (GodementWhiskeredSimplicialData F Y G d s) ∧
      Nonempty (SimplicialObject (A ⥤ B)) := by
  sorry

theorem godement_whiskered_augmentation_condition
    {A : Type u} {B : Type u'} {C : Type v}
    [Category.{v'} A] [Category.{u} B] [Category.{v} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) (h : GodementEquations Y d s) :
    Nonempty (GodementWhiskeredAugmentationData F Y G d s) := by
  sorry

theorem godement_functorial_with_augmentation
    {A : Type u} {B : Type u'} {C : Type v}
    [Category.{v'} A] [Category.{u} B] [Category.{v} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) (h : GodementEquations Y d s) :
    Nonempty (GodementWhiskeredSimplicialData F Y G d s) ∧
      Nonempty (GodementWhiskeredAugmentationData F Y G d s) := by
  exact ⟨(godement_functorial F Y G d s h).1,
    godement_whiskered_augmentation_condition F Y G d s h⟩

def godementZeroMap {A : Type u} {B : Type u'} {C : Type v}
    [Category.{v'} A] [Category.{u} B] [Category.{v} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B) :
    F ⋙ Y ⋙ G ⟶ godementWhiskeredDegree F Y G 0 :=
  Functor.whiskerRight
    (Functor.whiskerLeft F (Functor.rightUnitor Y).inv) G

structure GodementSection {A : Type u} {B : Type u'} {C : Type v}
    [Category.{v'} A] [Category.{u} B] [Category.{v} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (h₀ : F ⋙ G ⟶ F ⋙ Y ⋙ G) where
  component : ∀ n, F ⋙ G ⟶ godementWhiskeredDegree F Y G n
  component_zero : component 0 =
    h₀ ≫ godementZeroMap F Y G
  face_naturality : ∀ {n} (i : Fin (n + 2)),
    component (n + 1) ≫ godementWhiskeredSimplicialFace F Y G d n i =
      component n
  degeneracy_naturality : ∀ {n} (i : Fin (n + 1)),
    component n ≫ godementWhiskeredSimplicialDegeneracy F Y G s n i =
      component (n + 1)
  augmentation : ∀ n,
    component n ≫ godementWhiskeredAugmentationComponent F Y G d n = 𝟙 (F ⋙ G)

theorem godement_section_components
    {A : Type u} {B : Type u'} {C : Type v}
    [Category.{v'} A] [Category.{u} B] [Category.{v} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (h₀ : F ⋙ G ⟶ F ⋙ Y ⋙ G)
    (h₀_condition :
      h₀ ≫ godementZeroMap F Y G ≫
        godementWhiskeredAugmentationComponent F Y G d 0 = 𝟙 (F ⋙ G))
    (h : GodementEquations Y d s) :
    Nonempty (GodementSection F Y G d s h₀) := by
  sorry

/-! ## The two-map homotopy and the before/after maps -/

def godementOuterAugmentationComponent {B : Type u'} {C : Type v}
    [Category.{u} B] [Category.{v} C]
    (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) (G : C ⥤ B) (n : ℕ) :
    godementDegree Y n ⋙ G ⟶ G :=
  Functor.whiskerRight (godementAugmentationComponent Y d n) G ≫
    (Functor.leftUnitor G).hom

def godementInnerAugmentationComponent {A : Type u} {C : Type v}
    [Category.{v'} A] [Category.{v} C]
    (F : A ⥤ C) (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) (n : ℕ) :
    F ⋙ godementDegree Y n ⟶ F :=
  Functor.whiskerLeft F (godementAugmentationComponent Y d n) ≫
    (Functor.rightUnitor F).hom

structure GodementOuterMorphism {B : Type u'} {C : Type v}
    [Category.{u} B] [Category.{v} C]
    (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (G G' : C ⥤ B) (a : G ⟶ G')
    (aₙ : ∀ n, godementDegree Y n ⋙ G ⟶ godementDegree Y n ⋙ G') where
  face : ∀ {n} (j : Fin (n + 2)),
    aₙ (n + 1) ≫ Functor.whiskerRight
        (godementFace Y d (n := n + 1) j) G' =
      Functor.whiskerRight (godementFace Y d (n := n + 1) j) G ≫ aₙ n
  degeneracy : ∀ {n} (j : Fin (n + 1)),
    aₙ n ≫ Functor.whiskerRight (godementDegeneracy Y s j) G' =
      Functor.whiskerRight (godementDegeneracy Y s j) G ≫ aₙ (n + 1)
  augmentation : ∀ n,
    aₙ n ≫ godementOuterAugmentationComponent Y d G' n =
      godementOuterAugmentationComponent Y d G n ≫ a

structure GodementInnerMorphism {A : Type u} {C : Type v}
    [Category.{v'} A] [Category.{v} C]
    (F F' : A ⥤ C) (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (b : F ⟶ F')
    (bₙ : ∀ n, F ⋙ godementDegree Y n ⟶ F' ⋙ godementDegree Y n) where
  face : ∀ {n} (j : Fin (n + 2)),
    bₙ (n + 1) ≫ Functor.whiskerLeft F'
        (godementFace Y d (n := n + 1) j) =
      Functor.whiskerLeft F (godementFace Y d (n := n + 1) j) ≫ bₙ n
  degeneracy : ∀ {n} (j : Fin (n + 1)),
    bₙ n ≫ Functor.whiskerLeft F'
        (godementDegeneracy Y s j) =
      Functor.whiskerLeft F (godementDegeneracy Y s j) ≫ bₙ (n + 1)
  augmentation : ∀ n,
    bₙ n ≫ godementInnerAugmentationComponent F' Y d n =
      godementInnerAugmentationComponent F Y d n ≫ b

/-- The five degreewise conditions for the source's simplicial homotopy. -/
structure GodementDegreewiseHomotopy {D : Type u} [Category.{v} D]
    {X Y : ℕ → D}
    (faceX : ∀ n, Fin (n + 2) → (X (n + 1) ⟶ X n))
    (degenX : ∀ n, Fin (n + 1) → (X n ⟶ X (n + 1)))
    (faceY : ∀ n, Fin (n + 2) → (Y (n + 1) ⟶ Y n))
    (degenY : ∀ n, Fin (n + 1) → (Y n ⟶ Y (n + 1)))
    (left right : ∀ n, (X n ⟶ Y n)) where
  h : ∀ n, Fin (n + 2) → (X n ⟶ Y n)
  endpoint_zero : ∀ n, h n 0 = left n
  endpoint_last : ∀ n, h n (Fin.last (n + 1)) = right n
  face_of_gt {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2))
      (hji : j.castSucc < i) :
    h (n + 1) i ≫ faceY n j =
      faceX n j ≫ h n (i.pred hji.ne_zero)
  face_of_le {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2))
      (hij : i ≤ j.castSucc) :
    h (n + 1) i ≫ faceY n j =
      faceX n j ≫ h n
        (i.castPred (Fin.ne_last_of_lt
          (lt_of_le_of_lt hij j.castSucc_lt_succ)))
  degeneracy_of_gt {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
      (hji : j.castSucc < i) :
    h n i ≫ degenY n j = degenX n j ≫ h (n + 1) i.succ
  degeneracy_of_le {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
      (hij : i ≤ j.castSucc) :
    h n i ≫ degenY n j = degenX n j ≫ h (n + 1) i.castSucc

abbrev GodementWhiskeredHomotopy {A : Type u} {B : Type u'} {C : Type v}
    [Category.{v'} A] [Category.{u} B] [Category.{v} C]
    (F F' : A ⥤ C) (Y : C ⥤ C) (G G' : C ⥤ B)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (left right : ∀ n,
      godementWhiskeredDegree F Y G n ⟶
        godementWhiskeredDegree F' Y G' n) :=
  GodementDegreewiseHomotopy
    (godementWhiskeredSimplicialFace F Y G d)
    (godementWhiskeredSimplicialDegeneracy F Y G s)
    (godementWhiskeredSimplicialFace F' Y G' d)
    (godementWhiskeredSimplicialDegeneracy F' Y G' s) left right

abbrev GodementSelfHomotopy {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (left right : ∀ n, godementDegree Y n ⟶ godementDegree Y n) :=
  GodementDegreewiseHomotopy
    (fun n j => godementFace Y d (n := n + 1) j)
    (fun n j => godementDegeneracy Y s (n := n) j)
    (fun n j => godementFace Y d (n := n + 1) j)
    (fun n j => godementDegeneracy Y s (n := n) j) left right

theorem godement_two_maps_homotopic
    {A : Type u} {B : Type u'} {C : Type v}
    [Category.{v'} A] [Category.{u} B] [Category.{v} C]
    (F F' : A ⥤ C) (Y : C ⥤ C) (G G' : C ⥤ B)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) (h : GodementEquations Y d s)
    (a : G ⟶ G')
    (aₙ : ∀ n, godementDegree Y n ⋙ G ⟶ godementDegree Y n ⋙ G')
    (ha : GodementOuterMorphism Y d s G G' a aₙ)
    (b : F ⟶ F')
    (bₙ : ∀ n, F ⋙ godementDegree Y n ⟶ F' ⋙ godementDegree Y n)
    (hb : GodementInnerMorphism F F' Y d s b bₙ) :
    Nonempty (GodementWhiskeredHomotopy F F' Y G G' d s
      (fun n =>
        Functor.whiskerRight (bₙ n) G ≫
          Functor.whiskerLeft (F' ⋙ godementDegree Y n) a)
      (fun n =>
        Functor.whiskerLeft F (aₙ n) ≫
          Functor.whiskerRight b (godementDegree Y n ⋙ G'))) := by
  sorry

def godementBeforeMap {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (f : 𝟭 C ⟶ 𝟭 C) (n : ℕ) :
    godementDegree Y n ⟶ godementDegree Y n :=
  (Functor.leftUnitor (godementDegree Y n)).inv ≫
    Functor.whiskerRight f (godementDegree Y n) ≫
    (Functor.leftUnitor (godementDegree Y n)).hom

def godementAfterMap {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (f : 𝟭 C ⟶ 𝟭 C) (n : ℕ) :
    godementDegree Y n ⟶ godementDegree Y n :=
  (Functor.rightUnitor (godementDegree Y n)).inv ≫
    Functor.whiskerLeft (godementDegree Y n) f ≫
    (Functor.rightUnitor (godementDegree Y n)).hom

/-! After transporting across the unitors, the two maps in the final source
lemma are endomorphisms of each explicit degree. -/

structure GodementSelfMorphism {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (f : 𝟭 C ⟶ 𝟭 C) (maps : ∀ n, godementDegree Y n ⟶ godementDegree Y n) where
  face : ∀ {n} (j : Fin (n + 2)),
    maps (n + 1) ≫ godementFace Y d (n := n + 1) j =
      godementFace Y d (n := n + 1) j ≫ maps n
  degeneracy : ∀ {n} (j : Fin (n + 1)),
    maps n ≫ godementDegeneracy Y s (n := n) j =
      godementDegeneracy Y s (n := n) j ≫ maps (n + 1)
  augmentation : ∀ n,
    maps n ≫ godementAugmentationComponent Y d n =
      godementAugmentationComponent Y d n ≫ f

theorem godement_before_after_maps
    {C : Type u} [Category.{v} C] (Y : C ⥤ C)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) (h : GodementEquations Y d s)
    (f : 𝟭 C ⟶ 𝟭 C) :
    Nonempty (GodementSelfMorphism Y d s f
      (fun n => godementBeforeMap Y f n)) ∧
    Nonempty (GodementSelfMorphism Y d s f
      (fun n => godementAfterMap Y f n)) := by
  sorry

theorem godement_before_after_augmentation
    {C : Type u} [Category.{v} C] (Y : C ⥤ C)
    (d : Y ⟶ 𝟭 C) (f : 𝟭 C ⟶ 𝟭 C) :
    (∀ n, godementBeforeMap Y f n ≫ godementAugmentationComponent Y d n =
      godementAugmentationComponent Y d n ≫ f) ∧
    (∀ n, godementAfterMap Y f n ≫ godementAugmentationComponent Y d n =
      godementAugmentationComponent Y d n ≫ f) := by
  sorry

theorem godement_before_after_homotopic
    {C : Type u} [Category.{v} C] (Y : C ⥤ C)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) (h : GodementEquations Y d s)
    (f : 𝟭 C ⟶ 𝟭 C) :
    Nonempty (GodementSelfHomotopy Y d s
      (fun n => godementBeforeMap Y f n)
      (fun n => godementAfterMap Y f n)) := by
  sorry

end Formalization.Books.Simplicial.Unit33
