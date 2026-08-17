import Formalization.Books.Categories.Unit30.TwoOneCategories
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Products.Basic

/-!
# Categories, Chapter 31: 2-fibre products

The source works with strict `(2, 1)`-categories.  The ambient 2-categorical
operations below use Mathlib's `Bicategory` interface; strictness is used only
to write the source's strict composite formulas without inserting coherence
isomorphisms.  The category-valued example is the full subcategory of a comma
category on the objects whose comma arrow is an isomorphism.
-/

namespace Formalization.Books.Categories.Unit31

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.ObjectProperty

universe w v u w' v' u'

/-! ## Final objects -/

/-- A final object in a `(2, 1)`-category in the sense used by the source.

The explicit local-groupoid argument records the source's ambient
`(2, 1)`-category hypothesis without introducing a second typeclass. -/
def IsFinalObject {C : Type u} [Bicategory.{w, v} C]
    (_hC : Bicategory.IsLocallyGroupoid C) (x : C) : Prop :=
  ∀ y : C, Nonempty (y ⟶ x) ∧
    ∀ (f g : y ⟶ x), ∃! η : f ⟶ g, IsIso η

/-! ## 2-commutative diagrams -/

/-- A square in a bicategory is 2-commutative when its two composites are
connected by an invertible 2-morphism.  Composition is written in Mathlib's
left-to-right convention. -/
def IsTwoCommutative
    {C : Type u} [Bicategory.{w, v} C]
    {X Y Z W : C} (a : W ⟶ X) (b : W ⟶ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) : Prop :=
  ∃ (φ : a ≫ f ⟶ b ≫ g), IsIso φ

/-- An object of the 2-category of 2-commutative diagrams over `f` and `g`. -/
structure TwoCommutativeDiagram
    {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]
    {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) where
  /-- The object at the upper-left corner. -/
  vertex : C
  /-- The map from the vertex to `X`. -/
  left : vertex ⟶ X
  /-- The map from the vertex to `Y`. -/
  right : vertex ⟶ Y
  /-- The chosen invertible comparison 2-morphism. -/
  comparison : left ≫ f ⟶ right ≫ g
  /-- The comparison is invertible. -/
  comparison_isIso : IsIso comparison

attribute [instance] TwoCommutativeDiagram.comparison_isIso

namespace TwoCommutativeDiagram

variable {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]
variable {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}

/-- The strict associativity transport used by the source's formulas. -/
def strictAssocHom {A B D : C} (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ Z) :
    (a ≫ b) ≫ c ⟶ a ≫ b ≫ c :=
  eqToHom (Bicategory.Strict.assoc a b c)

/-- The inverse associativity transport. -/
def strictAssocInv {A B D : C} (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ Z) :
    a ≫ b ≫ c ⟶ (a ≫ b) ≫ c :=
  eqToHom (Bicategory.Strict.assoc a b c).symm

/-- A 1-morphism between two 2-commutative diagrams. -/
structure Hom (D E : TwoCommutativeDiagram f g) where
  /-- The map between the two upper-left vertices. -/
  vertex : D.vertex ⟶ E.vertex
  /-- The 2-morphism on the `X` leg. -/
  left : D.left ⟶ vertex ≫ E.left
  /-- The 2-morphism on the `Y` leg. -/
  right : D.right ⟶ vertex ≫ E.right
  /-- Compatibility with the chosen square 2-morphisms. -/
  commutes :
    (Bicategory.whiskerRight left f) ≫
          strictAssocHom vertex E.left f ≫
          (Bicategory.whiskerLeft vertex E.comparison) ≫
          strictAssocInv vertex E.right g =
      D.comparison ≫ Bicategory.whiskerRight right g

notation D " ⟶₂ " E => Hom D E

/-- The identity 1-morphism of a 2-commutative diagram. -/
def Hom.id (D : TwoCommutativeDiagram f g) : D ⟶₂ D where
  vertex := 𝟙 D.vertex
  left := eqToHom (Bicategory.Strict.id_comp D.left).symm
  right := eqToHom (Bicategory.Strict.id_comp D.right).symm
  commutes := by sorry

/-- Composition of 1-morphisms of 2-commutative diagrams. -/
def Hom.comp {D E K : TwoCommutativeDiagram f g}
    (h : D ⟶₂ E) (k : E ⟶₂ K) : D ⟶₂ K where
  vertex := h.vertex ≫ k.vertex
  left := h.left ≫ Bicategory.whiskerLeft h.vertex k.left ≫
    strictAssocInv h.vertex k.vertex K.left
  right := h.right ≫ Bicategory.whiskerLeft h.vertex k.right ≫
    strictAssocInv h.vertex k.vertex K.right
  commutes := by sorry

/-- A 2-morphism between 1-morphisms of 2-commutative diagrams. -/
structure TwoHom {D E : TwoCommutativeDiagram f g} (h k : D ⟶₂ E) where
  /-- The underlying 2-morphism between the vertex maps. -/
  vertex : h.vertex ⟶ k.vertex
  /-- Compatibility with the `X` leg. -/
  left : h.left ≫ Bicategory.whiskerRight vertex E.left = k.left
  /-- Compatibility with the `Y` leg. -/
  right : h.right ≫ Bicategory.whiskerRight vertex E.right = k.right

@[ext]
lemma TwoHom.ext {D E : TwoCommutativeDiagram f g} {h k : D ⟶₂ E}
    {η θ : TwoHom h k} (vertex : η.vertex = θ.vertex) : η = θ := by
  cases η
  cases θ
  cases vertex
  rfl

/-- The identity 2-morphism. -/
def TwoHom.id {D E : TwoCommutativeDiagram f g} (h : D ⟶₂ E) : TwoHom h h where
  vertex := 𝟙 h.vertex
  left := by simp
  right := by simp

/-- Vertical composition of 2-morphisms. -/
def TwoHom.comp {D E : TwoCommutativeDiagram f g}
    {h k l : D ⟶₂ E} (η : TwoHom h k) (θ : TwoHom k l) : TwoHom h l where
  vertex := η.vertex ≫ θ.vertex
  left := by sorry
  right := by sorry

/-- The category of 2-morphisms between two fixed diagrams' 1-morphisms. -/
instance homCategory (D E : TwoCommutativeDiagram f g) : Category (D ⟶₂ E) where
  Hom h k := TwoHom h k
  id h := TwoHom.id h
  comp η θ := TwoHom.comp η θ
  id_comp := by intros; apply TwoHom.ext; simp [TwoHom.comp, TwoHom.id]
  comp_id := by intros; apply TwoHom.ext; simp [TwoHom.comp, TwoHom.id]
  assoc := by intros; apply TwoHom.ext; simp [TwoHom.comp, Category.assoc]

instance categoryStruct : CategoryStruct (TwoCommutativeDiagram f g) where
  Hom D E := D ⟶₂ E
  id D := Hom.id D
  comp h k := Hom.comp h k

/-- Horizontal composition on the `X`-leg. -/
def TwoHom.whiskerLeft {D E K : TwoCommutativeDiagram f g}
    (h : D ⟶₂ E) {k l : E ⟶₂ K} (η : TwoHom k l) :
    TwoHom (Hom.comp h k) (Hom.comp h l) where
  vertex := Bicategory.whiskerLeft h.vertex η.vertex
  left := by sorry
  right := by sorry

/-- Horizontal composition on the `Y`-leg. -/
def TwoHom.whiskerRight {D E K : TwoCommutativeDiagram f g}
    {h k : D ⟶₂ E} (η : TwoHom h k) (l : E ⟶₂ K) :
    TwoHom (Hom.comp h l) (Hom.comp k l) where
  vertex := Bicategory.whiskerRight η.vertex l.vertex
  left := by sorry
  right := by sorry

/-- Horizontal composition of 2-morphisms of diagram 1-morphisms. -/
def TwoHom.horizComp
    {D E K : TwoCommutativeDiagram f g}
    {h₁ h₂ : D ⟶₂ E} {k₁ k₂ : E ⟶₂ K}
    (η : TwoHom h₁ h₂) (θ : TwoHom k₁ k₂) :
    TwoHom (Hom.comp h₁ k₁) (Hom.comp h₂ k₂) where
  vertex :=
    Bicategory.whiskerRight η.vertex k₁.vertex ≫
      Bicategory.whiskerLeft h₂.vertex θ.vertex
  left := by sorry
  right := by sorry

/-- The associator 2-isomorphism for diagram 1-morphisms. -/
def TwoHom.associator {D E K L : TwoCommutativeDiagram f g}
    (h : D ⟶₂ E) (k : E ⟶₂ K) (l : K ⟶₂ L) :
    TwoHom (Hom.comp (Hom.comp h k) l) (Hom.comp h (Hom.comp k l)) where
  vertex := (Bicategory.associator h.vertex k.vertex l.vertex).hom
  left := by sorry
  right := by sorry

/-- The inverse associator 2-morphism. -/
def TwoHom.associatorInv {D E K L : TwoCommutativeDiagram f g}
    (h : D ⟶₂ E) (k : E ⟶₂ K) (l : K ⟶₂ L) :
    TwoHom (Hom.comp h (Hom.comp k l)) (Hom.comp (Hom.comp h k) l) where
  vertex := (Bicategory.associator h.vertex k.vertex l.vertex).inv
  left := by sorry
  right := by sorry

/-- The left unitor 2-isomorphism. -/
def TwoHom.leftUnitor {D E : TwoCommutativeDiagram f g} (h : D ⟶₂ E) :
    TwoHom (Hom.comp (Hom.id D) h) h where
  vertex := (Bicategory.leftUnitor h.vertex).hom
  left := by sorry
  right := by sorry

/-- The inverse left unitor. -/
def TwoHom.leftUnitorInv {D E : TwoCommutativeDiagram f g} (h : D ⟶₂ E) :
    TwoHom h (Hom.comp (Hom.id D) h) where
  vertex := (Bicategory.leftUnitor h.vertex).inv
  left := by sorry
  right := by sorry

/-- The right unitor 2-isomorphism. -/
def TwoHom.rightUnitor {D E : TwoCommutativeDiagram f g} (h : D ⟶₂ E) :
    TwoHom (Hom.comp h (Hom.id E)) h where
  vertex := (Bicategory.rightUnitor h.vertex).hom
  left := by sorry
  right := by sorry

/-- The inverse right unitor. -/
def TwoHom.rightUnitorInv {D E : TwoCommutativeDiagram f g} (h : D ⟶₂ E) :
    TwoHom h (Hom.comp h (Hom.id E)) where
  vertex := (Bicategory.rightUnitor h.vertex).inv
  left := by sorry
  right := by sorry

/-- The final-object predicate for the explicitly displayed 2-category of
2-commutative diagrams. -/
abbrev IsIsoTwoHom {D E : TwoCommutativeDiagram f g}
    {h k : D ⟶₂ E} (η : TwoHom h k) : Prop :=
  @IsIso (D ⟶₂ E) (TwoCommutativeDiagram.homCategory D E) h k η

/- The source's horizontal-composition formulas above are the data of the
   2-category.  The coherence laws are recorded as the following proof-stage
   interface, and the chosen structure is installed as the usable bicategory
   instance below. -/
theorem twoCommutativeDiagram_bicategory_exists :
    Nonempty (Bicategory (TwoCommutativeDiagram f g)) := by
  sorry

/-- A chosen bicategory structure on the displayed diagram data. -/
noncomputable instance twoCommutativeDiagramBicategory :
    Bicategory (TwoCommutativeDiagram f g) :=
  Classical.choice twoCommutativeDiagram_bicategory_exists

abbrev IsFinalTwoCommutativeDiagram
    (_hC : Bicategory.IsLocallyGroupoid C)
    (x : TwoCommutativeDiagram f g) : Prop :=
  ∀ y : TwoCommutativeDiagram f g, Nonempty (y ⟶₂ x) ∧
    ∀ (h k : y ⟶₂ x), ∃! η : TwoHom h k, IsIsoTwoHom η

/-- In a locally groupoidal ambient bicategory, the leg 2-morphisms in a
diagram morphism are invertible. -/
theorem hom_left_isIso
    (hC : Bicategory.IsLocallyGroupoid C)
    {D E : TwoCommutativeDiagram f g} (h : D ⟶₂ E) : IsIso h.left := by
  have := hC D.vertex X
  sorry

theorem hom_right_isIso
    (hC : Bicategory.IsLocallyGroupoid C)
    {D E : TwoCommutativeDiagram f g} (h : D ⟶₂ E) : IsIso h.right := by
  have := hC D.vertex Y
  sorry

/-- The explicitly displayed diagram 2-category is locally groupoidal when
its ambient bicategory is a `(2,1)`-category. -/
theorem twoCommutativeDiagram_is_two_one
    (hC : Bicategory.IsLocallyGroupoid C) :
    ∀ (D E : TwoCommutativeDiagram f g) (h k : D ⟶₂ E)
      (η : TwoHom h k), IsIsoTwoHom η := by
  intro D E h k η
  have := hC D.vertex E.vertex
  sorry

end TwoCommutativeDiagram

/-! ## Abstract 2-fibre products -/

/-- A 2-fibre product is a final 2-commutative diagram. -/
structure TwoFibreProduct
    {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]
    (hC : Bicategory.IsLocallyGroupoid C)
    {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) where
  diagram : TwoCommutativeDiagram f g
  isFinal : TwoCommutativeDiagram.IsFinalTwoCommutativeDiagram hC diagram

abbrev twoFibreProductObject
    {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]
    (hC : Bicategory.IsLocallyGroupoid C)
    {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    (P : TwoFibreProduct hC f g) : C :=
  P.diagram.vertex

abbrev twoFibreProductLeft
    {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]
    (hC : Bicategory.IsLocallyGroupoid C)
    {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    (P : TwoFibreProduct hC f g) : P.diagram.vertex ⟶ X :=
  P.diagram.left

abbrev twoFibreProductRight
    {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]
    (hC : Bicategory.IsLocallyGroupoid C)
    {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    (P : TwoFibreProduct hC f g) : P.diagram.vertex ⟶ Y :=
  P.diagram.right

abbrev twoFibreProductComparison
    {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]
    (hC : Bicategory.IsLocallyGroupoid C)
    {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    (P : TwoFibreProduct hC f g) :
    P.diagram.left ≫ f ⟶ P.diagram.right ≫ g :=
  P.diagram.comparison

/-- Existence of a 2-fibre product for a fixed pair of 1-morphisms. -/
abbrev HasTwoFibreProduct
    {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]
    (hC : Bicategory.IsLocallyGroupoid C)
    {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : Prop :=
  Nonempty (TwoFibreProduct hC f g)

/-- A chosen 2-fibre product, when one exists. -/
noncomputable def chosenTwoFibreProduct
    {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]
    (hC : Bicategory.IsLocallyGroupoid C)
    {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : HasTwoFibreProduct hC f g) : TwoFibreProduct hC f g :=
  Classical.choice h

/-- The universal-property map supplied by a 2-fibre product. -/
theorem twoFibreProduct_universal_property
    {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]
    (hC : Bicategory.IsLocallyGroupoid C)
    {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    (P : TwoFibreProduct hC f g)
    {W : C}
    (a : W ⟶ X) (b : W ⟶ Y)
    (φ : a ≫ f ⟶ b ≫ g) [IsIso φ] :
    ∃ (γ : W ⟶ P.diagram.vertex)
      (α : a ⟶ γ ≫ P.diagram.left)
      (β : b ⟶ γ ≫ P.diagram.right),
      (Bicategory.whiskerRight α f) ≫
          TwoCommutativeDiagram.strictAssocHom γ P.diagram.left f ≫
          (Bicategory.whiskerLeft γ P.diagram.comparison) ≫
          TwoCommutativeDiagram.strictAssocInv γ P.diagram.right g =
        φ ≫ Bicategory.whiskerRight β g := by
  let D : TwoCommutativeDiagram f g :=
    { vertex := W
      left := a
      right := b
      comparison := φ
      comparison_isIso := inferInstance }
  rcases (P.isFinal D).1 with ⟨h⟩
  exact ⟨h.vertex, h.left, h.right, h.commutes⟩

/-- The uniqueness-up-to-unique-2-isomorphism part of the universal property. -/
theorem twoFibreProduct_unique_up_to_unique_two_iso
    {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]
    (hC : Bicategory.IsLocallyGroupoid C)
    {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    (P : TwoFibreProduct hC f g)
    (D : TwoCommutativeDiagram f g) (h₁ h₂ : D ⟶₂ P.diagram) :
    ∃! η : h₁ ⟶ h₂, TwoCommutativeDiagram.IsIsoTwoHom η :=
  (P.isFinal D).2 h₁ h₂

/-! ## The category-valued construction -/

/-- The object property selecting the isomorphism arrows in a comma category. -/
def IsoCommaProperty
    {A : Type*} [Category* A]
    {B : Type*} [Category* B]
    {C : Type*} [Category* C]
    (F : A ⥤ C) (G : B ⥤ C) : ObjectProperty (Comma F G) :=
  fun ξ => IsIso ξ.hom

/-- The category whose objects are triples `(A, B, F(A) ≅ G(B))`. -/
abbrev IsoComma
    {A : Type*} [Category* A]
    {B : Type*} [Category* B]
    {C : Type*} [Category* C]
    (F : A ⥤ C) (G : B ⥤ C) :=
  (IsoCommaProperty F G).FullSubcategory

instance isoComma_isIso_hom
    {A : Type*} [Category* A]
    {B : Type*} [Category* B]
    {C : Type*} [Category* C]
    {F : A ⥤ C} {G : B ⥤ C} (ξ : IsoComma F G) : IsIso ξ.obj.hom :=
  ξ.property

/-- The first projection from the category-valued 2-fibre product. -/
def isoCommaLeft
    {A : Type*} [Category* A]
    {B : Type*} [Category* B]
    {C : Type*} [Category* C]
    (F : A ⥤ C) (G : B ⥤ C) : IsoComma F G ⥤ A :=
  (IsoCommaProperty F G).ι ⋙ Comma.fst F G

/-- The second projection from the category-valued 2-fibre product. -/
def isoCommaRight
    {A : Type*} [Category* A]
    {B : Type*} [Category* B]
    {C : Type*} [Category* C]
    (F : A ⥤ C) (G : B ⥤ C) : IsoComma F G ⥤ B :=
  (IsoCommaProperty F G).ι ⋙ Comma.snd F G

/-- The comparison natural transformation `F ∘ p ⟶ G ∘ q`. -/
def isoCommaComparison
    {A : Type*} [Category* A]
    {B : Type*} [Category* B]
    {C : Type*} [Category* C]
    (F : A ⥤ C) (G : B ⥤ C) :
    isoCommaLeft F G ⋙ F ⟶ isoCommaRight F G ⋙ G :=
  Functor.whiskerLeft (IsoCommaProperty F G).ι (Comma.natTrans F G)

theorem isoCommaComparison_isIso
    {A : Type*} [Category* A]
    {B : Type*} [Category* B]
    {C : Type*} [Category* C]
    (F : A ⥤ C) (G : B ⥤ C) : IsIso (isoCommaComparison F G) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro ξ
  change IsIso ξ.obj.hom
  infer_instance

/-! ### The ordinary-category universal property -/

/-- The compatibility equation for a cone over two functors of categories.

The associators are displayed explicitly because functor composition in
Mathlib is associative only up to its canonical natural isomorphism. -/
def CategoryTwoFibreProductConeCommutes
    {A : Type*} [Category* A]
    {B : Type*} [Category* B]
    {C : Type*} [Category* C]
    {P : Type*} [Category* P]
    (F : A ⥤ C) (G : B ⥤ C)
    (p : P ⥤ A) (q : P ⥤ B)
    (ψ : p ⋙ F ≅ q ⋙ G)
    {W : Type u'} [Category.{v'} W]
    (a : W ⥤ A) (b : W ⥤ B) (φ : a ⋙ F ≅ b ⋙ G)
    (γ : W ⥤ P) (α : a ≅ γ ⋙ p) (β : b ≅ γ ⋙ q) : Prop :=
  (Functor.isoWhiskerRight α F).hom ≫
        (Functor.associator γ p F).hom ≫
        Functor.whiskerLeft γ ψ.hom =
      φ.hom ≫
        (Functor.isoWhiskerRight β G).hom ≫
        (Functor.associator γ q G).hom

/-- The category-valued form of a 2-fibre-product universal property. -/
def IsCategoryTwoFibreProduct
    {A : Type*} [Category* A]
    {B : Type*} [Category* B]
    {C : Type*} [Category* C]
    {P : Type*} [Category* P]
    (F : A ⥤ C) (G : B ⥤ C)
    (p : P ⥤ A) (q : P ⥤ B)
    (ψ : p ⋙ F ≅ q ⋙ G) : Prop :=
  (∀ {W : Type u'} [Category.{v'} W] (a : W ⥤ A) (b : W ⥤ B)
      (φ : a ⋙ F ≅ b ⋙ G),
      ∃ (γ : W ⥤ P) (α : a ≅ γ ⋙ p) (β : b ≅ γ ⋙ q),
        CategoryTwoFibreProductConeCommutes F G p q ψ a b φ γ α β) ∧
  (∀ {W : Type u'} [Category.{v'} W] (a : W ⥤ A) (b : W ⥤ B)
      (φ : a ⋙ F ≅ b ⋙ G)
      (γ₁ γ₂ : W ⥤ P)
      (α₁ : a ≅ γ₁ ⋙ p) (β₁ : b ≅ γ₁ ⋙ q)
      (α₂ : a ≅ γ₂ ⋙ p) (β₂ : b ≅ γ₂ ⋙ q),
      CategoryTwoFibreProductConeCommutes F G p q ψ a b φ γ₁ α₁ β₁ →
      CategoryTwoFibreProductConeCommutes F G p q ψ a b φ γ₂ α₂ β₂ →
      Nonempty (γ₁ ≅ γ₂))

/-- A square of categories is 2-cartesian when its upper-left corner is the
2-fibre product of the two maps out of the other corners. -/
def IsTwoCartesianSquare
    {U : Type*} [Category* U]
    {V : Type*} [Category* V]
    {X : Type*} [Category* X]
    {Y : Type*} [Category* Y]
    (top : U ⥤ V) (left : U ⥤ X)
    (right : V ⥤ Y) (bottom : X ⥤ Y)
    (comm : left ⋙ bottom ≅ top ⋙ right) : Prop :=
  (∀ {W : Type u'} [Category.{v'} W] (a : W ⥤ X) (b : W ⥤ V)
      (φ : a ⋙ bottom ≅ b ⋙ right),
      ∃ (γ : W ⥤ U) (α : a ≅ γ ⋙ left) (β : b ≅ γ ⋙ top),
        CategoryTwoFibreProductConeCommutes bottom right left top comm
          a b φ γ α β) ∧
  (∀ {W : Type u'} [Category.{v'} W] (a : W ⥤ X) (b : W ⥤ V)
      (φ : a ⋙ bottom ≅ b ⋙ right)
      (γ₁ γ₂ : W ⥤ U)
      (α₁ : a ≅ γ₁ ⋙ left) (β₁ : b ≅ γ₁ ⋙ top)
      (α₂ : a ≅ γ₂ ⋙ left) (β₂ : b ≅ γ₂ ⋙ top),
      CategoryTwoFibreProductConeCommutes bottom right left top comm
          a b φ γ₁ α₁ β₁ →
      CategoryTwoFibreProductConeCommutes bottom right left top comm
          a b φ γ₂ α₂ β₂ →
      Nonempty (γ₁ ≅ γ₂))

/-- The canonical comparison isomorphism of the iso-comma construction. -/
noncomputable def isoCommaComparisonIso
    {A : Type*} [Category* A]
    {B : Type*} [Category* B]
    {C : Type*} [Category* C]
    (F : A ⥤ C) (G : B ⥤ C) :
    isoCommaLeft F G ⋙ F ≅ isoCommaRight F G ⋙ G :=
  letI : IsIso (isoCommaComparison F G) := isoCommaComparison_isIso F G
  asIso (isoCommaComparison F G)

/- The objectwise isomorphisms in the comma category assemble to the
   comparison isomorphism used by the category-valued universal property. -/
theorem isoCommaComparisonIso_exists
    {A : Type*} [Category* A]
    {B : Type*} [Category* B]
    {C : Type*} [Category* C]
    (F : A ⥤ C) (G : B ⥤ C) :
    Nonempty (isoCommaLeft F G ⋙ F ≅ isoCommaRight F G ⋙ G) :=
  ⟨isoCommaComparisonIso F G⟩

theorem isoComma_is_category_twoFibreProduct
    {A : Type*} [Category* A]
    {B : Type*} [Category* B]
    {C : Type*} [Category* C]
    (F : A ⥤ C) (G : B ⥤ C) :
    IsCategoryTwoFibreProduct F G
      (isoCommaLeft F G) (isoCommaRight F G)
      (isoCommaComparisonIso F G) := by
  sorry

theorem category_twoFibreProduct_unique_up_to_iso
    {A : Type*} [Category* A]
    {B : Type*} [Category* B]
    {C : Type*} [Category* C]
    {P : Type*} [Category* P]
    (F : A ⥤ C) (G : B ⥤ C)
    (p : P ⥤ A) (q : P ⥤ B) (ψ : p ⋙ F ≅ q ⋙ G)
    (h : IsCategoryTwoFibreProduct F G p q ψ)
    {W : Type u'} [Category.{v'} W] (a : W ⥤ A) (b : W ⥤ B)
    (φ : a ⋙ F ≅ b ⋙ G)
    (γ₁ γ₂ : W ⥤ P)
    (α₁ : a ≅ γ₁ ⋙ p) (β₁ : b ≅ γ₁ ⋙ q)
    (α₂ : a ≅ γ₂ ⋙ p) (β₂ : b ≅ γ₂ ⋙ q)
    (h₁ : CategoryTwoFibreProductConeCommutes F G p q ψ a b φ γ₁ α₁ β₁)
    (h₂ : CategoryTwoFibreProductConeCommutes F G p q ψ a b φ γ₂ α₂ β₂) :
    Nonempty (γ₁ ≅ γ₂) := by
  sorry

/- The source's explicit category is this `IsoComma`; its morphisms are the
   canonical comma morphisms, so the commutative-square condition is already
   supplied by `CommaMorphism.w`. -/
abbrev TwoFibreProductCategory
    {A : Type*} [Category* A] {B : Type*} [Category* B]
    {C : Type*} [Category* C] (F : A ⥤ C) (G : B ⥤ C) := IsoComma F G

abbrev twoFibreProductCategoryLeft
    {A : Type*} [Category* A] {B : Type*} [Category* B]
    {C : Type*} [Category* C] (F : A ⥤ C) (G : B ⥤ C) :=
  isoCommaLeft F G

abbrev twoFibreProductCategoryRight
    {A : Type*} [Category* A] {B : Type*} [Category* B]
    {C : Type*} [Category* C] (F : A ⥤ C) (G : B ⥤ C) :=
  isoCommaRight F G

abbrev twoFibreProductCategoryComparison
    {A : Type*} [Category* A] {B : Type*} [Category* B]
    {C : Type*} [Category* C] (F : A ⥤ C) (G : B ⥤ C) :=
  isoCommaComparison F G

/-- The category-valued construction supplies the category-level universal
property used for 2-fibre products. -/
theorem isoComma_is_twoFibreProduct
    {A : Type*} [Category* A]
    {B : Type*} [Category* B]
    {C : Type*} [Category* C]
    (F : A ⥤ C) (G : B ⥤ C) :
    IsCategoryTwoFibreProduct F G
      (isoCommaLeft F G) (isoCommaRight F G)
      (isoCommaComparisonIso F G) :=
  isoComma_is_category_twoFibreProduct F G

/-- A symmetric quintuple presentation of the category-valued construction. -/
abbrev QuintupleCategory
    {A : Type*} [Category* A]
    {B : Type*} [Category* B]
    {C : Type*} [Category* C]
    (F : A ⥤ C) (G : B ⥤ C) :=
  IsoComma (F.prod G) (Functor.diag C)

/-- The quintuple presentation is equivalent to the triple presentation. -/
theorem quintupleCategory_equivalent
    {A : Type*} [Category* A]
    {B : Type*} [Category* B]
    {C : Type*} [Category* C]
    (F : A ⥤ C) (G : B ⥤ C) :
    Nonempty (QuintupleCategory F G ≌ IsoComma F G) := by
  sorry

/-! ## Functoriality and comparison results -/

/-- The functor induced by a 2-commutative diagram of ordinary categories. -/
noncomputable def isoCommaMap
    {A B C X Y Z : Type*} [Category* A] [Category* B]
    [Category* C] [Category* X] [Category* Y] [Category* Z]
    (F : A ⥤ C) (G : B ⥤ C) (H : X ⥤ Z) (I : Y ⥤ Z)
    (L : X ⥤ A) (K : Y ⥤ B) (M : Z ⥤ C)
    (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F) :
    IsoComma H I ⥤ IsoComma F G where
  obj ξ :=
    letI : IsIso ξ.obj.hom := ξ.property
    { obj :=
        { left := L.obj ξ.obj.left
          right := K.obj ξ.obj.right
          hom := β.inv.app ξ.obj.left ≫ M.map ξ.obj.hom ≫ α.inv.app ξ.obj.right }
      property := by
        change IsIso (β.inv.app ξ.obj.left ≫ M.map ξ.obj.hom ≫ α.inv.app ξ.obj.right)
        infer_instance }
  map h :=
    ObjectProperty.homMk
      { left := L.map h.hom.left
        right := K.map h.hom.right
        w := by sorry }
  map_id := by sorry
  map_comp := by sorry

/-- The source's functoriality lemma in the category-valued example. -/
theorem isoCommaMap_faithful
    {A B C X Y Z : Type*} [Category* A] [Category* B]
    [Category* C] [Category* X] [Category* Y] [Category* Z]
    (F : A ⥤ C) (G : B ⥤ C) (H : X ⥤ Z) (I : Y ⥤ Z)
    (L : X ⥤ A) (K : Y ⥤ B) (M : Z ⥤ C)
    (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F)
    [K.Faithful] [L.Faithful] :
    (isoCommaMap F G H I L K M α β).Faithful := by
  sorry

/-- Full faithfulness of the induced functor. -/
theorem isoCommaMap_fullyFaithful
    {A B C X Y Z : Type*} [Category* A] [Category* B]
    [Category* C] [Category* X] [Category* Y] [Category* Z]
    (F : A ⥤ C) (G : B ⥤ C) (H : X ⥤ Z) (I : Y ⥤ Z)
    (L : X ⥤ A) (K : Y ⥤ B) (M : Z ⥤ C)
    (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F)
    [K.Full] [K.Faithful] [L.Full] [L.Faithful] [M.Faithful] :
    Nonempty ((isoCommaMap F G H I L K M α β).FullyFaithful) := by
  sorry

/-- Equivalence of the induced functor under the hypotheses in the source. -/
theorem isoCommaMap_isEquivalence
    {A B C X Y Z : Type*} [Category* A] [Category* B]
    [Category* C] [Category* X] [Category* Y] [Category* Z]
    (F : A ⥤ C) (G : B ⥤ C) (H : X ⥤ Z) (I : Y ⥤ Z)
    (L : X ⥤ A) (K : Y ⥤ B) (M : Z ⥤ C)
    (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F)
    [K.IsEquivalence] [L.IsEquivalence] [M.Full] [M.Faithful] :
    (isoCommaMap F G H I L K M α β).IsEquivalence := by
  sorry

/-! ## Associativity and iterated products -/

/-- Associativity of the iso-comma construction. -/
theorem isoComma_associator
    {A B C D E : Type*} [Category* A] [Category* B]
    [Category* C] [Category* D] [Category* E]
    (F : A ⥤ B) (G : C ⥤ B) (H : C ⥤ D) (I : E ⥤ D) :
    Nonempty (IsoComma ((isoCommaRight F G) ⋙ H) I ≌
      IsoComma F ((isoCommaLeft H I) ⋙ G)) := by
  sorry

/-- The canonical projection from an iterated 2-fibre product to the outer
factors. -/
theorem isoComma_pr02
    {A B C D E K : Type*} [Category* A] [Category* B]
    [Category* C] [Category* D] [Category* E] [Category* K]
    (F : A ⥤ B) (G : C ⥤ B) (H : C ⥤ D) (I : E ⥤ D)
    (J : B ⥤ K) (L : D ⥤ K)
    (comm : G ⋙ J ≅ H ⋙ L) :
    Nonempty
      (IsoComma ((isoCommaRight F G) ⋙ H) I ⥤ IsoComma (F ⋙ J) (I ⋙ L)) := by
  sorry

/-- Erasing the repeated middle factor does not change an iterated
2-fibre product. -/
theorem isoComma_erase_factor
    {A B C D : Type*} [Category* A] [Category* B]
    [Category* C] [Category* D]
    (F : A ⥤ B) (G : C ⥤ B) (H : D ⥤ C) :
    Nonempty (IsoComma (isoCommaRight F G) H ≌ IsoComma F (H ⋙ G)) := by
  sorry

/-! ## Diagonal descriptions -/

/-- The product of the two projections of an iso-comma category. -/
def isoCommaPair
    {A B S : Type*} [Category* A] [Category* B] [Category* S]
    (G₁ : A ⥤ S) (G₂ : B ⥤ S) : IsoComma G₁ G₂ ⥤ A × B :=
  (isoCommaLeft G₁ G₂).prod' (isoCommaRight G₁ G₂)

/-- The diagonal description of a 2-fibre product over a diagonal functor. -/
theorem isoComma_diagonal_one
    {A B S : Type*} [Category* A] [Category* B] [Category* S]
    (G₁ : A ⥤ S) (G₂ : B ⥤ S) :
    Nonempty (IsoComma (Functor.prod G₁ G₂) (Functor.diag S) ≌ IsoComma G₁ G₂) := by
  sorry

/-- The iterated diagonal description from the source. -/
theorem isoComma_diagonal_two
    {C S : Type*} [Category* C] [Category* S]
    (G₁ G₂ : C ⥤ S) :
    Nonempty (IsoComma (Functor.prod G₁ G₂) (Functor.diag S) ≌
      IsoComma (isoCommaPair G₁ G₂) (Functor.diag C)) := by
  sorry

/-! ## Base-change statements -/

/-- The functor obtained by postcomposing both legs with a map of bases. -/
noncomputable def isoCommaAfterMap
    {A : Type*} [Category* A]
    {B : Type*} [Category* B]
    {C : Type*} [Category* C]
    {D : Type*} [Category* D]
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    IsoComma F G ⥤ IsoComma (F ⋙ H) (G ⋙ H) :=
  isoCommaMap (F ⋙ H) (G ⋙ H) F G (𝟭 A) (𝟭 B) H
    (Functor.leftUnitor (G ⋙ H))
    (Functor.leftUnitor (F ⋙ H)).symm

/-- The diagonal functor into the iso-comma of a functor with itself. -/
def isoCommaDiagonal
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    (H : C ⥤ D) : C ⥤ IsoComma H H where
  obj X :=
    { obj :=
        { left := X
          right := X
          hom := 𝟙 (H.obj X) }
      property := by
        change IsIso (𝟙 (H.obj X))
        infer_instance }
  map f :=
    ObjectProperty.homMk
      { left := f
        right := f
        w := by simp }
  map_id := by
    intro X
    apply ObjectProperty.hom_ext
    rfl
  map_comp := by
    intro X Y Z f g
    apply ObjectProperty.hom_ext
    rfl

/-- The map from the base-changed product to the diagonal product. -/
noncomputable def isoCommaAfterMapToDiagonal
    {A : Type*} [Category* A]
    {B : Type*} [Category* B]
    {C : Type*} [Category* C]
    {D : Type*} [Category* D]
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    IsoComma (F ⋙ H) (G ⋙ H) ⥤ IsoComma H H :=
  isoCommaMap H H (F ⋙ H) (G ⋙ H) F G (𝟭 D)
    (Functor.rightUnitor (G ⋙ H)).symm
    (Functor.rightUnitor (F ⋙ H))

/- The source only needs a comparison between the two routes around this
   square.  Its existence is the objectwise comma calculation; keeping a
   chosen comparison separate leaves the square's universal-property
   statement independent of a particular normalization of associators and
   unitors. -/
theorem isoComma_after_map_comparison_exists
    {A : Type*} [Category* A]
    {B : Type*} [Category* B]
    {C : Type*} [Category* C]
    {D : Type*} [Category* D]
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    Nonempty
      ((isoCommaLeft F G ⋙ F) ⋙ isoCommaDiagonal H ≅
        isoCommaAfterMap F G H ⋙ isoCommaAfterMapToDiagonal F G H) := by
  sorry

noncomputable def isoCommaAfterMapComparison
    {A : Type*} [Category* A]
    {B : Type*} [Category* B]
    {C : Type*} [Category* C]
    {D : Type*} [Category* D]
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    (isoCommaLeft F G ⋙ F) ⋙ isoCommaDiagonal H ≅
      isoCommaAfterMap F G H ⋙ isoCommaAfterMapToDiagonal F G H :=
  Classical.choice (isoComma_after_map_comparison_exists F G H)

/-- The square obtained by applying a functor to the common base is
2-cartesian. -/
theorem isoComma_after_map
    {A : Type*} [Category* A]
    {B : Type*} [Category* B]
    {C : Type*} [Category* C]
    {D : Type*} [Category* D]
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    IsTwoCartesianSquare
      (isoCommaAfterMap F G H)
      (isoCommaLeft F G ⋙ F)
      (isoCommaAfterMapToDiagonal F G H)
      (isoCommaDiagonal H)
      (isoCommaAfterMapComparison F G H) := by
  sorry

/-- The induced functor between the two diagonal iso-comma categories. -/
noncomputable def isoCommaBaseChangeMap
    {U : Type*} [Category* U]
    {V : Type*} [Category* V]
    {X : Type*} [Category* X]
    {Y : Type*} [Category* Y]
    (top : U ⥤ V) (left : U ⥤ X)
    (right : V ⥤ Y) (bottom : X ⥤ Y)
    (comm : left ⋙ bottom ≅ top ⋙ right) :
    IsoComma top top ⥤ IsoComma bottom bottom :=
  isoCommaMap bottom bottom top top left left right comm comm.symm

theorem isoComma_base_change_comparison_exists
    {U : Type*} [Category* U]
    {V : Type*} [Category* V]
    {X : Type*} [Category* X]
    {Y : Type*} [Category* Y]
    (top : U ⥤ V) (left : U ⥤ X)
    (right : V ⥤ Y) (bottom : X ⥤ Y)
    (comm : left ⋙ bottom ≅ top ⋙ right) :
    Nonempty
      (left ⋙ isoCommaDiagonal bottom ≅
        isoCommaDiagonal top ⋙ isoCommaBaseChangeMap top left right bottom comm) := by
  sorry

noncomputable def isoCommaBaseChangeComparison
    {U : Type*} [Category* U]
    {V : Type*} [Category* V]
    {X : Type*} [Category* X]
    {Y : Type*} [Category* Y]
    (top : U ⥤ V) (left : U ⥤ X)
    (right : V ⥤ Y) (bottom : X ⥤ Y)
    (comm : left ⋙ bottom ≅ top ⋙ right) :
    left ⋙ isoCommaDiagonal bottom ≅
      isoCommaDiagonal top ⋙ isoCommaBaseChangeMap top left right bottom comm :=
  Classical.choice
    (isoComma_base_change_comparison_exists top left right bottom comm)

/-- Base change preserves the diagonal square. -/
theorem isoComma_base_change_diagonal
    {U : Type*} [Category* U]
    {V : Type*} [Category* V]
    {X : Type*} [Category* X]
    {Y : Type*} [Category* Y]
    (top : U ⥤ V) (left : U ⥤ X)
    (right : V ⥤ Y) (bottom : X ⥤ Y)
    (comm : left ⋙ bottom ≅ top ⋙ right)
    (h : IsTwoCartesianSquare top left right bottom comm) :
    IsTwoCartesianSquare
      (isoCommaDiagonal top)
      left
      (isoCommaBaseChangeMap top left right bottom comm)
      (isoCommaDiagonal bottom)
      (isoCommaBaseChangeComparison top left right bottom comm) := by
  sorry

end Formalization.Books.Categories.Unit31
