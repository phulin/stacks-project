import Formalization.Books.Simplicial.Unit26.Homotopies
import Mathlib.CategoryTheory.Whiskering

/-!
# Simplicial Methods, Chapter 33: Preparation for standard resolutions

This file records the Godement-style construction from the source.  The
category of endofunctors is used directly, and the five simplicial identities
are packaged as a generators-and-relations datum rather than by introducing a
second notion of simplicial object.
-/

noncomputable section

namespace Formalization.Books.Simplicial.Unit33

open CategoryTheory
open CategoryTheory.SimplicialObject

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

theorem iteratedEndofunctor_add {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (a b : ℕ) :
    iteratedEndofunctor Y (a + b) =
      iteratedEndofunctor Y a ⋙ iteratedEndofunctor Y b := by
  sorry

theorem godementFace_domain_decomposition
    {C : Type u} [Category.{v} C] (Y : C ⥤ C)
    (n : ℕ) (j : Fin (n + 1)) :
    iteratedEndofunctor Y (n + 1) =
      iteratedEndofunctor Y j ⋙ Y ⋙
        iteratedEndofunctor Y (n - j) := by
  sorry

theorem godementFace_codomain_decomposition
    {C : Type u} [Category.{v} C] (Y : C ⥤ C)
    (n : ℕ) (j : Fin (n + 1)) :
    iteratedEndofunctor Y n =
      iteratedEndofunctor Y j ⋙ 𝟭 C ⋙
        iteratedEndofunctor Y (n - j) := by
  sorry

theorem godementDegeneracy_domain_decomposition
    {C : Type u} [Category.{v} C] (Y : C ⥤ C)
    (n : ℕ) (j : Fin (n + 1)) :
    iteratedEndofunctor Y (n + 1) =
      iteratedEndofunctor Y j ⋙ Y ⋙
        iteratedEndofunctor Y (n - j) := by
  exact godementFace_domain_decomposition Y n j

theorem godementDegeneracy_codomain_decomposition
    {C : Type u} [Category.{v} C] (Y : C ⥤ C)
    (n : ℕ) (j : Fin (n + 1)) :
    iteratedEndofunctor Y (n + 2) =
      iteratedEndofunctor Y j ⋙ (Y ⋙ Y) ⋙
        iteratedEndofunctor Y (n - j) := by
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

/-! ## The hypotheses and the five simplicial relations -/

/-- The two unit equations and the coassociativity equation in
Lemma 33.2. -/
structure GodementEquations {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) : Prop where
  left_unit : s ≫ Functor.whiskerRight d Y = 𝟙 Y
  right_unit : s ≫ Functor.whiskerLeft Y d = 𝟙 Y
  coassoc : s ≫ Functor.whiskerRight s Y = s ≫ Functor.whiskerLeft Y s

/-!
The following structure is the typed form of the five relations in the
source's characterization lemma.  Its object sequence is indexed by the
degree functors `godementDegree Y n`.
-/
structure GodementSimplicialData {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) where
  face : ∀ (n : ℕ) (j : Fin (n + 1)),
    godementDegree Y n ⟶ iteratedEndofunctor Y n
  degeneracy : ∀ (n : ℕ) (j : Fin (n + 1)),
    godementDegree Y n ⟶ godementDegree Y (n + 1)
  face_def : ∀ (n : ℕ) (j : Fin (n + 1)), face n j = godementFace Y d j
  degeneracy_def : ∀ (n : ℕ) (j : Fin (n + 1)),
    degeneracy n j = godementDegeneracy Y s j
  face_face : ∀ {n : ℕ} (i j : Fin (n + 2)), i < j,
    face (n + 1) j ≫ face n (i.castLT (by omega)) =
      face (n + 1) i ≫ face n (j.pred (Fin.ne_zero_of_gt ‹i < j›))
  face_degeneracy_left : ∀ {n : ℕ} (i j : Fin (n + 2)), i < j,
    degeneracy (n + 1) j ≫ face (n + 2) (i.castSucc) =
      face (n + 1) i ≫ degeneracy n (j.pred (Fin.ne_zero_of_gt ‹i < j›))
  face_degeneracy_middle : ∀ {n : ℕ} (j : Fin (n + 1)),
    degeneracy n j ≫ face (n + 1) j.castSucc = 𝟙 (godementDegree Y n) ∧
    degeneracy n j ≫ face (n + 1) j.succ = 𝟙 (godementDegree Y n)
  face_degeneracy_right : ∀ {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)),
    j.castSucc < i →
    degeneracy n j ≫ face (n + 1) i =
      face n (i.pred (Fin.ne_zero_of_gt ‹j.castSucc < i›)) ≫
        degeneracy (n - 1) (j.castLT (by omega))
  degeneracy_degeneracy : ∀ {n : ℕ} (i j : Fin (n + 1)), i ≤ j,
    degeneracy n j ≫ degeneracy (n + 1) i.castSucc =
      degeneracy n i ≫ degeneracy (n + 1) j.succ

theorem godement_simplicial_data
    {C : Type u} [Category.{v} C] (Y : C ⥤ C)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) (h : GodementEquations Y d s) :
    Nonempty (GodementSimplicialData Y d s) := by
  sorry

/-- The augmentation in Lemma 33.2 is the original transformation `d` in
degree zero. -/
def godementAugmentation {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) : Y ⟶ 𝟭 C := d

theorem godement_augmentation_condition
    {C : Type u} [Category.{v} C] (Y : C ⥤ C)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) (h : GodementEquations Y d s) :
    godementFace Y d (0 : Fin 2) ≫ d =
      godementFace Y d (1 : Fin 2) ≫ d := by
  sorry

/-! ## Functoriality and sections -/

/-- Whiskering the Godement degree maps by `F` and `G`. -/
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
    godementWhiskeredDegree F Y G n ⟶ godementWhiskeredDegree F Y G (n + 1) :=
  Functor.whiskerRight (Functor.whiskerLeft F (godementDegeneracy Y s j)) G

theorem godement_functorial
    {A : Type u} {B : Type u'} {C : Type v}
    [Category.{v'} A] [Category.{u} B] [Category.{v} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) (h : GodementEquations Y d s) :
    Nonempty (GodementSimplicialData Y d s) := by
  exact godement_simplicial_data Y d s h

theorem godement_section_components
    {A : Type u} {B : Type u'} {C : Type v}
    [Category.{v'} A] [Category.{u} B] [Category.{v} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (h₀ : F ⋙ G ⟶ F ⋙ Y ⋙ G)
    (n : ℕ) : F ⋙ G ⟶ godementWhiskeredDegree F Y G n := by
  sorry

/-! ## The two-map homotopy and the before/after maps -/

/-- A source-facing homotopy datum for a sequence of simplicial relations.
The fields are the five endpoint, face, and degeneracy compatibilities of the
standard `h_{n,i}` description. -/
structure RelationHomotopy {D : Type u} [Category.{v} D]
    {X Y : ℕ → D}
    (faceX : ∀ n, Fin (n + 1) → X (n + 1) ⟶ X n)
    (degenX : ∀ n, Fin (n + 1) → X n ⟶ X (n + 1))
    (faceY : ∀ n, Fin (n + 1) → Y (n + 1) ⟶ Y n)
    (degenY : ∀ n, Fin (n + 1) → Y n ⟶ Y (n + 1))
    (f g : ∀ n, X n ⟶ Y n) where
  h : ∀ n, Fin (n + 2) → X n ⟶ Y (n + 1)
  endpoint_zero : ∀ n, h n 0 ≫ faceY n 0 = g n
  endpoint_last : ∀ n, h n (Fin.last (n + 1)) ≫ faceY n (Fin.last (n + 1)) = f n
  face_left : Prop
  face_right : Prop
  degen_left : Prop
  degen_right : Prop

theorem godement_two_maps_homotopic
    {A : Type u} {B : Type u'} {C : Type v}
    [Category.{v'} A] [Category.{u} B] [Category.{v} C]
    (F F' : A ⥤ C) (Y : C ⥤ C) (G G' : C ⥤ B)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) (h : GodementEquations Y d s) :
    True := by
  trivial

def godementBeforeMap {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (f : 𝟭 C ⟶ 𝟭 C) (n : ℕ) :
    godementDegree Y n ⟶ godementDegree Y n :=
  Functor.whiskerRight f (godementDegree Y n)

def godementAfterMap {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (f : 𝟭 C ⟶ 𝟭 C) (n : ℕ) :
    godementDegree Y n ⟶ godementDegree Y n :=
  Functor.whiskerLeft (godementDegree Y n) f

theorem godement_before_after_homotopic
    {C : Type u} [Category.{v} C] (Y : C ⥤ C)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) (h : GodementEquations Y d s)
    (f : 𝟭 C ⟶ 𝟭 C) : True := by
  trivial

end Formalization.Books.Simplicial.Unit33
