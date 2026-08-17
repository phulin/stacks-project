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
def IsFinalObject {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]
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

theorem isTwoCommutative (D : TwoCommutativeDiagram f g) :
    IsTwoCommutative D.left D.right f g :=
  ⟨D.comparison, inferInstance⟩

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
  commutes := by
    simp [strictAssocHom, strictAssocInv, Bicategory.Strict.leftUnitor_eqToIso]

/-- Composition of 1-morphisms of 2-commutative diagrams. -/
def Hom.comp {D E K : TwoCommutativeDiagram f g}
    (h : D ⟶₂ E) (k : E ⟶₂ K) : D ⟶₂ K where
  vertex := h.vertex ≫ k.vertex
  left := h.left ≫ Bicategory.whiskerLeft h.vertex k.left ≫
    strictAssocInv h.vertex k.vertex K.left
  right := h.right ≫ Bicategory.whiskerLeft h.vertex k.right ≫
    strictAssocInv h.vertex k.vertex K.right
  commutes := by
    have ha₁ : strictAssocHom h.vertex E.left f =
        (Bicategory.associator h.vertex E.left f).hom := by
      simpa [strictAssocHom] using congrArg Iso.hom
        (Bicategory.Strict.associator_eqToIso h.vertex E.left f) |>.symm
    have ha₂ : strictAssocInv h.vertex E.right g =
        (Bicategory.associator h.vertex E.right g).inv := by
      simpa [strictAssocInv] using congrArg Iso.inv
        (Bicategory.Strict.associator_eqToIso h.vertex E.right g) |>.symm
    have hb₁ : strictAssocHom k.vertex K.left f =
        (Bicategory.associator k.vertex K.left f).hom := by
      simpa [strictAssocHom] using congrArg Iso.hom
        (Bicategory.Strict.associator_eqToIso k.vertex K.left f) |>.symm
    have hb₂ : strictAssocInv k.vertex K.right g =
        (Bicategory.associator k.vertex K.right g).inv := by
      simpa [strictAssocInv] using congrArg Iso.inv
        (Bicategory.Strict.associator_eqToIso k.vertex K.right g) |>.symm
    have hc₁ : strictAssocHom (h.vertex ≫ k.vertex) K.left f =
        (Bicategory.associator (h.vertex ≫ k.vertex) K.left f).hom := by
      simpa [strictAssocHom] using congrArg Iso.hom
        (Bicategory.Strict.associator_eqToIso (h.vertex ≫ k.vertex) K.left f) |>.symm
    have hc₂ : strictAssocInv (h.vertex ≫ k.vertex) K.right g =
        (Bicategory.associator (h.vertex ≫ k.vertex) K.right g).inv := by
      simpa [strictAssocInv] using congrArg Iso.inv
        (Bicategory.Strict.associator_eqToIso (h.vertex ≫ k.vertex) K.right g) |>.symm
    have hd₁ : strictAssocInv h.vertex k.vertex K.left =
        (Bicategory.associator h.vertex k.vertex K.left).inv := by
      simpa [strictAssocInv] using congrArg Iso.inv
        (Bicategory.Strict.associator_eqToIso h.vertex k.vertex K.left) |>.symm
    have hd₂ : strictAssocInv h.vertex k.vertex K.right =
        (Bicategory.associator h.vertex k.vertex K.right).inv := by
      simpa [strictAssocInv] using congrArg Iso.inv
        (Bicategory.Strict.associator_eqToIso h.vertex k.vertex K.right) |>.symm
    simp only [Bicategory.comp_whiskerRight, Category.assoc]
    have hh := h.commutes
    have kk := k.commutes
    rw [ha₁, ha₂] at hh
    rw [hb₁, hb₂] at kk
    rw [hc₁, hc₂, hd₁, hd₂]
    simp [Category.assoc]
    rw [← Bicategory.whiskerLeft_comp_assoc]
    rw [← Bicategory.whiskerLeft_comp_assoc]
    rw [← Bicategory.pentagon_inv h.vertex k.vertex K.right g]
    have hkk := congrArg (Bicategory.whiskerLeft h.vertex) kk
    rw [← Bicategory.whiskerLeft_comp_assoc]
    simp only [Category.assoc]
    rw [hkk]
    rw [Bicategory.whiskerLeft_comp]
    simp only [Category.assoc]
    have hn :
        h.vertex ◁ (k.right ▷ g) ≫
            (Bicategory.associator h.vertex (k.vertex ≫ K.right) g).inv =
          (Bicategory.associator h.vertex E.right g).inv ≫
            (h.vertex ◁ k.right) ▷ g := by
      rw [Bicategory.whisker_assoc_symm]
      simp
    rw [← Category.assoc (h.vertex ◁ (k.right ▷ g))
      (Bicategory.associator h.vertex (k.vertex ≫ K.right) g).inv]
    rw [hn]
    calc
      _ = (h.left ▷ f ≫ (Bicategory.associator h.vertex E.left f).hom ≫
          h.vertex ◁ E.comparison ≫
          (Bicategory.associator h.vertex E.right g).inv) ≫
          (h.vertex ◁ k.right) ▷ g ≫
          (Bicategory.associator h.vertex k.vertex K.right).inv ▷ g := by
            simp only [Category.assoc]
      _ = (D.comparison ≫ h.right ▷ g) ≫
          (h.vertex ◁ k.right) ▷ g ≫
          (Bicategory.associator h.vertex k.vertex K.right).inv ▷ g := by
            rw [hh]
      _ = _ := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
          Category.comp_id]

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
  left := by
    rw [Bicategory.comp_whiskerRight]
    rw [← Category.assoc h.left (η.vertex ▷ E.left) (θ.vertex ▷ E.left)]
    rw [η.left, θ.left]
  right := by
    rw [Bicategory.comp_whiskerRight]
    rw [← Category.assoc h.right (η.vertex ▷ E.right) (θ.vertex ▷ E.right)]
    rw [η.right, θ.right]

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
  left := by
    have hk : strictAssocInv h.vertex k.vertex K.left =
        (Bicategory.associator h.vertex k.vertex K.left).inv := by
      simpa [strictAssocInv] using congrArg Iso.inv
        (Bicategory.Strict.associator_eqToIso h.vertex k.vertex K.left) |>.symm
    have hl : strictAssocInv h.vertex l.vertex K.left =
        (Bicategory.associator h.vertex l.vertex K.left).inv := by
      simpa [strictAssocInv] using congrArg Iso.inv
        (Bicategory.Strict.associator_eqToIso h.vertex l.vertex K.left) |>.symm
    simp [Hom.comp, Category.assoc, hk, hl]
    rw [← Bicategory.whiskerLeft_comp_assoc, η.left]
  right := by
    have hk : strictAssocInv h.vertex k.vertex K.right =
        (Bicategory.associator h.vertex k.vertex K.right).inv := by
      simpa [strictAssocInv] using congrArg Iso.inv
        (Bicategory.Strict.associator_eqToIso h.vertex k.vertex K.right) |>.symm
    have hl : strictAssocInv h.vertex l.vertex K.right =
        (Bicategory.associator h.vertex l.vertex K.right).inv := by
      simpa [strictAssocInv] using congrArg Iso.inv
        (Bicategory.Strict.associator_eqToIso h.vertex l.vertex K.right) |>.symm
    simp [Hom.comp, Category.assoc, hk, hl]
    rw [← Bicategory.whiskerLeft_comp_assoc, η.right]

/-- Horizontal composition on the `Y`-leg. -/
def TwoHom.whiskerRight {D E K : TwoCommutativeDiagram f g}
    {h k : D ⟶₂ E} (η : TwoHom h k) (l : E ⟶₂ K) :
    TwoHom (Hom.comp h l) (Hom.comp k l) where
  vertex := Bicategory.whiskerRight η.vertex l.vertex
  left := by
    simp [Hom.comp, Category.assoc]
    have hs : strictAssocInv h.vertex l.vertex K.left =
        (Bicategory.associator h.vertex l.vertex K.left).inv := by
      simpa [strictAssocInv] using congrArg Iso.inv
        (Bicategory.Strict.associator_eqToIso h.vertex l.vertex K.left) |>.symm
    have hk : strictAssocInv k.vertex l.vertex K.left =
        (Bicategory.associator k.vertex l.vertex K.left).inv := by
      simpa [strictAssocInv] using congrArg Iso.inv
        (Bicategory.Strict.associator_eqToIso k.vertex l.vertex K.left) |>.symm
    rw [hs, hk]
    rw [← Bicategory.associator_inv_naturality_left]
    rw [Bicategory.whisker_exchange_assoc, ← η.left]
    simp only [Category.assoc]
  right := by
    simp [Hom.comp, Category.assoc]
    have hs : strictAssocInv h.vertex l.vertex K.right =
        (Bicategory.associator h.vertex l.vertex K.right).inv := by
      simpa [strictAssocInv] using congrArg Iso.inv
        (Bicategory.Strict.associator_eqToIso h.vertex l.vertex K.right) |>.symm
    have hk : strictAssocInv k.vertex l.vertex K.right =
        (Bicategory.associator k.vertex l.vertex K.right).inv := by
      simpa [strictAssocInv] using congrArg Iso.inv
        (Bicategory.Strict.associator_eqToIso k.vertex l.vertex K.right) |>.symm
    rw [hs, hk]
    rw [← Bicategory.associator_inv_naturality_left]
    rw [Bicategory.whisker_exchange_assoc, ← η.right]
    simp only [Category.assoc]

/-- Horizontal composition of 2-morphisms of diagram 1-morphisms. -/
def TwoHom.horizComp
    {D E K : TwoCommutativeDiagram f g}
    {h₁ h₂ : D ⟶₂ E} {k₁ k₂ : E ⟶₂ K}
    (η : TwoHom h₁ h₂) (θ : TwoHom k₁ k₂) :
    TwoHom (Hom.comp h₁ k₁) (Hom.comp h₂ k₂) where
  vertex :=
    Bicategory.whiskerRight η.vertex k₁.vertex ≫
      Bicategory.whiskerLeft h₂.vertex θ.vertex
  left := by
    exact (TwoHom.comp (TwoHom.whiskerRight η k₁)
      (TwoHom.whiskerLeft h₂ θ)).left
  right := by
    exact (TwoHom.comp (TwoHom.whiskerRight η k₁)
      (TwoHom.whiskerLeft h₂ θ)).right

/-- The associator 2-isomorphism for diagram 1-morphisms. -/
def TwoHom.associator {D E K L : TwoCommutativeDiagram f g}
    (h : D ⟶₂ E) (k : E ⟶₂ K) (l : K ⟶₂ L) :
    TwoHom (Hom.comp (Hom.comp h k) l) (Hom.comp h (Hom.comp k l)) where
  vertex := (Bicategory.associator h.vertex k.vertex l.vertex).hom
  left := by
    simp [Hom.comp, strictAssocInv, strictAssocHom, Category.assoc,
      Bicategory.Strict.associator_eqToIso]
  right := by
    simp [Hom.comp, strictAssocInv, strictAssocHom, Category.assoc,
      Bicategory.Strict.associator_eqToIso]

/-- The inverse associator 2-morphism. -/
def TwoHom.associatorInv {D E K L : TwoCommutativeDiagram f g}
    (h : D ⟶₂ E) (k : E ⟶₂ K) (l : K ⟶₂ L) :
    TwoHom (Hom.comp h (Hom.comp k l)) (Hom.comp (Hom.comp h k) l) where
  vertex := (Bicategory.associator h.vertex k.vertex l.vertex).inv
  left := by
    simp [Hom.comp, strictAssocInv, strictAssocHom, Category.assoc,
      Bicategory.Strict.associator_eqToIso]
  right := by
    simp [Hom.comp, strictAssocInv, strictAssocHom, Category.assoc,
      Bicategory.Strict.associator_eqToIso]

/-- The left unitor 2-isomorphism. -/
def TwoHom.leftUnitor {D E : TwoCommutativeDiagram f g} (h : D ⟶₂ E) :
    TwoHom (Hom.comp (Hom.id D) h) h where
  vertex := (Bicategory.leftUnitor h.vertex).hom
  left := by
    simp [Hom.id, Hom.comp, strictAssocInv, Category.assoc,
      Bicategory.Strict.leftUnitor_eqToIso]
  right := by
    simp [Hom.id, Hom.comp, strictAssocInv, Category.assoc,
      Bicategory.Strict.leftUnitor_eqToIso]

/-- The inverse left unitor. -/
def TwoHom.leftUnitorInv {D E : TwoCommutativeDiagram f g} (h : D ⟶₂ E) :
    TwoHom h (Hom.comp (Hom.id D) h) where
  vertex := (Bicategory.leftUnitor h.vertex).inv
  left := by
    simp [Hom.id, Hom.comp, strictAssocInv, Category.assoc,
      Bicategory.Strict.leftUnitor_eqToIso]
  right := by
    simp [Hom.id, Hom.comp, strictAssocInv, Category.assoc,
      Bicategory.Strict.leftUnitor_eqToIso]

/-- The right unitor 2-isomorphism. -/
def TwoHom.rightUnitor {D E : TwoCommutativeDiagram f g} (h : D ⟶₂ E) :
    TwoHom (Hom.comp h (Hom.id E)) h where
  vertex := (Bicategory.rightUnitor h.vertex).hom
  left := by
    simp [Hom.id, Hom.comp, strictAssocInv, Category.assoc,
      Bicategory.Strict.rightUnitor_eqToIso]
  right := by
    simp [Hom.id, Hom.comp, strictAssocInv, Category.assoc,
      Bicategory.Strict.rightUnitor_eqToIso]

/-- The inverse right unitor. -/
def TwoHom.rightUnitorInv {D E : TwoCommutativeDiagram f g} (h : D ⟶₂ E) :
    TwoHom h (Hom.comp h (Hom.id E)) where
  vertex := (Bicategory.rightUnitor h.vertex).inv
  left := by
    simp [Hom.id, Hom.comp, strictAssocInv, Category.assoc,
      Bicategory.Strict.rightUnitor_eqToIso]
  right := by
    simp [Hom.id, Hom.comp, strictAssocInv, Category.assoc,
      Bicategory.Strict.rightUnitor_eqToIso]

/-- The final-object predicate for the explicitly displayed 2-category of
2-commutative diagrams. -/
abbrev IsIsoTwoHom {D E : TwoCommutativeDiagram f g}
    {h k : D ⟶₂ E} (η : TwoHom h k) : Prop :=
  @IsIso (D ⟶₂ E) (TwoCommutativeDiagram.homCategory D E) h k η

/- The source's horizontal-composition formulas above are the data of the
   2-category.  The coherence laws are the usual bicategory laws for these
   operations. -/
noncomputable instance twoCommutativeDiagramBicategory :
    Bicategory (TwoCommutativeDiagram f g) where
  Hom D E := D ⟶₂ E
  id D := Hom.id D
  comp h k := Hom.comp h k
  homCategory := homCategory
  whiskerLeft := TwoHom.whiskerLeft
  whiskerRight := TwoHom.whiskerRight
  associator h k l :=
    { hom := TwoHom.associator h k l
      inv := TwoHom.associatorInv h k l
      hom_inv_id := by
        apply TwoHom.ext
        change (Bicategory.associator h.vertex k.vertex l.vertex).hom ≫
          (Bicategory.associator h.vertex k.vertex l.vertex).inv = 𝟙 _
        exact (Bicategory.associator h.vertex k.vertex l.vertex).hom_inv_id
      inv_hom_id := by
        apply TwoHom.ext
        change (Bicategory.associator h.vertex k.vertex l.vertex).inv ≫
          (Bicategory.associator h.vertex k.vertex l.vertex).hom = 𝟙 _
        exact (Bicategory.associator h.vertex k.vertex l.vertex).inv_hom_id }
  leftUnitor h :=
    { hom := TwoHom.leftUnitor h
      inv := TwoHom.leftUnitorInv h
      hom_inv_id := by
        apply TwoHom.ext
        change (Bicategory.leftUnitor h.vertex).hom ≫
          (Bicategory.leftUnitor h.vertex).inv = 𝟙 _
        exact (Bicategory.leftUnitor h.vertex).hom_inv_id
      inv_hom_id := by
        apply TwoHom.ext
        change (Bicategory.leftUnitor h.vertex).inv ≫
          (Bicategory.leftUnitor h.vertex).hom = 𝟙 _
        exact (Bicategory.leftUnitor h.vertex).inv_hom_id }
  rightUnitor h :=
    { hom := TwoHom.rightUnitor h
      inv := TwoHom.rightUnitorInv h
      hom_inv_id := by
        apply TwoHom.ext
        change (Bicategory.rightUnitor h.vertex).hom ≫
          (Bicategory.rightUnitor h.vertex).inv = 𝟙 _
        exact (Bicategory.rightUnitor h.vertex).hom_inv_id
      inv_hom_id := by
        apply TwoHom.ext
        change (Bicategory.rightUnitor h.vertex).inv ≫
          (Bicategory.rightUnitor h.vertex).hom = 𝟙 _
        exact (Bicategory.rightUnitor h.vertex).inv_hom_id }
  whiskerLeft_id := by
    intros D E K h k
    apply TwoHom.ext
    change Bicategory.whiskerLeft h.vertex (𝟙 k.vertex) =
      𝟙 (h.vertex ≫ k.vertex)
    exact Bicategory.whiskerLeft_id _ _
  whiskerLeft_comp := by
    intros D E K h k l m η θ
    apply TwoHom.ext
    change Bicategory.whiskerLeft h.vertex (η.vertex ≫ θ.vertex) =
      Bicategory.whiskerLeft h.vertex η.vertex ≫
        Bicategory.whiskerLeft h.vertex θ.vertex
    exact Bicategory.whiskerLeft_comp _ _ _
  id_whiskerLeft := by
    intros D E h k η
    apply TwoHom.ext
    change Bicategory.whiskerLeft (𝟙 D.vertex) η.vertex =
      (Bicategory.leftUnitor h.vertex).hom ≫ η.vertex ≫
        (Bicategory.leftUnitor k.vertex).inv
    exact Bicategory.id_whiskerLeft η.vertex
  comp_whiskerLeft := by
    intros D E K L h k l m η
    apply TwoHom.ext
    change Bicategory.whiskerLeft (h.vertex ≫ k.vertex) η.vertex =
      (Bicategory.associator h.vertex k.vertex l.vertex).hom ≫
        Bicategory.whiskerLeft h.vertex
          (Bicategory.whiskerLeft k.vertex η.vertex) ≫
        (Bicategory.associator h.vertex k.vertex m.vertex).inv
    exact Bicategory.comp_whiskerLeft _ _ _
  id_whiskerRight := by
    intros D E K h k
    apply TwoHom.ext
    change Bicategory.whiskerRight (𝟙 h.vertex) k.vertex =
      𝟙 (h.vertex ≫ k.vertex)
    exact Bicategory.id_whiskerRight _ _
  comp_whiskerRight := by
    intros D E K h k l η θ m
    apply TwoHom.ext
    change Bicategory.whiskerRight (η.vertex ≫ θ.vertex) m.vertex =
      Bicategory.whiskerRight η.vertex m.vertex ≫
        Bicategory.whiskerRight θ.vertex m.vertex
    exact Bicategory.comp_whiskerRight _ _ _
  whiskerRight_id := by
    intros D E h k η
    apply TwoHom.ext
    change Bicategory.whiskerRight η.vertex (𝟙 E.vertex) =
      (Bicategory.rightUnitor h.vertex).hom ≫ η.vertex ≫
        (Bicategory.rightUnitor k.vertex).inv
    exact Bicategory.whiskerRight_id η.vertex
  whiskerRight_comp := by
    intros D E K L h k η l m
    apply TwoHom.ext
    change Bicategory.whiskerRight η.vertex (l.vertex ≫ m.vertex) =
      (Bicategory.associator h.vertex l.vertex m.vertex).inv ≫
        Bicategory.whiskerRight (Bicategory.whiskerRight η.vertex l.vertex)
          m.vertex ≫
        (Bicategory.associator k.vertex l.vertex m.vertex).hom
    exact Bicategory.whiskerRight_comp _ _ _
  whisker_assoc := by
    intros D E K L h k l η m
    apply TwoHom.ext
    change Bicategory.whiskerRight (Bicategory.whiskerLeft h.vertex η.vertex)
        m.vertex =
      (Bicategory.associator h.vertex k.vertex m.vertex).hom ≫
        Bicategory.whiskerLeft h.vertex
          (Bicategory.whiskerRight η.vertex m.vertex) ≫
        (Bicategory.associator h.vertex l.vertex m.vertex).inv
    exact Bicategory.whisker_assoc _ _ _
  whisker_exchange := by
    intros D E K h k l m η θ
    apply TwoHom.ext
    change Bicategory.whiskerLeft h.vertex θ.vertex ≫
        Bicategory.whiskerRight η.vertex m.vertex =
      Bicategory.whiskerRight η.vertex l.vertex ≫
        Bicategory.whiskerLeft k.vertex θ.vertex
    exact Bicategory.whisker_exchange _ _
  pentagon := by
    intros D E K L M h k l m
    apply TwoHom.ext
    change Bicategory.whiskerRight
          (Bicategory.associator h.vertex k.vertex l.vertex).hom m.vertex ≫
        (Bicategory.associator h.vertex (k.vertex ≫ l.vertex) m.vertex).hom ≫
        Bicategory.whiskerLeft h.vertex
          (Bicategory.associator k.vertex l.vertex m.vertex).hom =
      (Bicategory.associator (h.vertex ≫ k.vertex) l.vertex m.vertex).hom ≫
        (Bicategory.associator h.vertex k.vertex (l.vertex ≫ m.vertex)).hom
    exact Bicategory.pentagon _ _ _ _
  triangle := by
    intros D E K h k
    apply TwoHom.ext
    change (Bicategory.associator h.vertex (𝟙 E.vertex) k.vertex).hom ≫
        Bicategory.whiskerLeft h.vertex
          (Bicategory.leftUnitor k.vertex).hom =
      Bicategory.whiskerRight (Bicategory.rightUnitor h.vertex).hom k.vertex
    exact Bicategory.triangle _ _

theorem twoCommutativeDiagram_bicategory_exists :
    Nonempty (Bicategory (TwoCommutativeDiagram f g)) :=
  by
    sorry

/-- The displayed 2-category is strict when the ambient 2-category is strict. -/
noncomputable instance twoCommutativeDiagramStrict :
    Bicategory.Strict (TwoCommutativeDiagram f g) := by
  sorry

/-- The displayed 2-category is locally groupoidal when the ambient one is. -/
theorem twoCommutativeDiagram_is_two_one
    (hC : Bicategory.IsLocallyGroupoid C) :
    Bicategory.IsLocallyGroupoid (TwoCommutativeDiagram f g) := by
  intro D E
  letI : IsGroupoid (D.vertex ⟶ E.vertex) := hC D.vertex E.vertex
  refine ⟨fun {h k} η => ?_⟩
  let e : h.vertex ≅ k.vertex := asIso η.vertex
  let ηinv : TwoHom k h :=
    { vertex := e.inv
      left := by
        rw [← η.left]
        simp [e, ← Bicategory.comp_whiskerRight, Category.assoc]
      right := by
        rw [← η.right]
        simp [e, ← Bicategory.comp_whiskerRight, Category.assoc] }
  refine ⟨⟨ηinv, ?_, ?_⟩⟩
  · apply TwoHom.ext
    change η.vertex ≫ e.inv = 𝟙 _
    exact e.hom_inv_id
  · apply TwoHom.ext
    change e.inv ≫ η.vertex = 𝟙 _
    exact e.inv_hom_id

abbrev IsFinalTwoCommutativeDiagram
    (hC : Bicategory.IsLocallyGroupoid C)
    (x : TwoCommutativeDiagram f g) : Prop :=
  IsFinalObject (twoCommutativeDiagram_is_two_one hC) x

/-- In a locally groupoidal ambient bicategory, the leg 2-morphisms in a
diagram morphism are invertible. -/
theorem hom_left_isIso
    (hC : Bicategory.IsLocallyGroupoid C)
    {D E : TwoCommutativeDiagram f g} (h : D ⟶₂ E) : IsIso h.left := by
  letI := hC D.vertex X
  infer_instance

theorem hom_right_isIso
    (hC : Bicategory.IsLocallyGroupoid C)
    {D E : TwoCommutativeDiagram f g} (h : D ⟶₂ E) : IsIso h.right := by
  letI := hC D.vertex Y
  infer_instance

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

@[simp]
theorem isoCommaLeft_obj
    {A : Type*} [Category* A]
    {B : Type*} [Category* B]
    {C : Type*} [Category* C]
    (F : A ⥤ C) (G : B ⥤ C) (ξ : IsoComma F G) :
    (isoCommaLeft F G).obj ξ = ξ.obj.left :=
  rfl

@[simp]
theorem isoCommaRight_obj
    {A : Type*} [Category* A]
    {B : Type*} [Category* B]
    {C : Type*} [Category* C]
    (F : A ⥤ C) (G : B ⥤ C) (ξ : IsoComma F G) :
    (isoCommaRight F G).obj ξ = ξ.obj.right :=
  rfl

@[simp]
theorem isoCommaComparison_app
    {A : Type*} [Category* A]
    {B : Type*} [Category* B]
    {C : Type*} [Category* C]
    (F : A ⥤ C) (G : B ⥤ C) (ξ : IsoComma F G) :
    (isoCommaComparison F G).app ξ = ξ.obj.hom :=
  rfl

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

/-- The unique comparison 2-isomorphism required between two lifts of the
same category-valued cone. -/
def CategoryTwoFibreProductConeUniqueIso
    {A : Type*} [Category* A]
    {B : Type*} [Category* B]
    {P : Type*} [Category* P]
    (p : P ⥤ A) (q : P ⥤ B)
    {W : Type u'} [Category.{v'} W]
    (a : W ⥤ A) (b : W ⥤ B)
    (γ₁ γ₂ : W ⥤ P)
    (α₁ : a ≅ γ₁ ⋙ p) (β₁ : b ≅ γ₁ ⋙ q)
    (α₂ : a ≅ γ₂ ⋙ p) (β₂ : b ≅ γ₂ ⋙ q) : Prop :=
  ∃! δ : γ₁ ≅ γ₂,
    α₁.hom ≫ Functor.whiskerRight δ.hom p = α₂.hom ∧
      β₁.hom ≫ Functor.whiskerRight δ.hom q = β₂.hom

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
      CategoryTwoFibreProductConeUniqueIso p q a b γ₁ γ₂ α₁ β₁ α₂ β₂)

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
      CategoryTwoFibreProductConeUniqueIso left top a b γ₁ γ₂ α₁ β₁ α₂ β₂)

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
  constructor
  · intro W _ a b φ
    let γ : W ⥤ IsoComma F G :=
      { obj := fun X =>
          { obj :=
              { left := a.obj X
                right := b.obj X
                hom := φ.hom.app X }
            property := by
              change IsIso (φ.hom.app X)
              infer_instance }
        map := fun {X Y} f =>
          ObjectProperty.homMk
            { left := a.map f
              right := b.map f
              w := by simpa [Functor.comp] using φ.hom.naturality f }
        map_id := by
          intro X
          apply ObjectProperty.hom_ext
          apply Comma.hom_ext <;> simp
        map_comp := by
          intro X Y Z f g
          apply ObjectProperty.hom_ext
          apply Comma.hom_ext <;> simp }
    let α : a ≅ γ ⋙ isoCommaLeft F G :=
      NatIso.ofComponents (fun X => Iso.refl _) (by
        intro X Y f
        simp [γ, isoCommaLeft])
    let β : b ≅ γ ⋙ isoCommaRight F G :=
      NatIso.ofComponents (fun X => Iso.refl _) (by
        intro X Y f
        simp [γ, isoCommaRight])
    refine ⟨γ, α, β, ?_⟩
    unfold CategoryTwoFibreProductConeCommutes
    apply NatTrans.ext
    funext X
    simp only [NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.whiskerLeft_app]
    have hα : α.hom.app X = 𝟙 (a.obj X) := by
      change (Iso.refl (a.obj X)).hom = 𝟙 _
      rfl
    have hβ : β.hom.app X = 𝟙 (b.obj X) := by
      change (Iso.refl (b.obj X)).hom = 𝟙 _
      rfl
    have hψ : (isoCommaComparisonIso F G).hom.app (γ.obj X) = φ.hom.app X := by
      change (isoCommaComparison F G).app (γ.obj X) = φ.hom.app X
      rfl
    rw [hα, hβ, hψ]
    simp
  · intro W _ a b φ γ₁ γ₂ α₁ β₁ α₂ β₂ h₁ h₂
    let δ : γ₁ ≅ γ₂ :=
      NatIso.ofComponents (fun X => by
        let l : (γ₁.obj X).obj.left ≅ (γ₂.obj X).obj.left :=
          (α₁.app X).symm ≪≫ α₂.app X
        let r : (γ₁.obj X).obj.right ≅ (γ₂.obj X).obj.right :=
          (β₁.app X).symm ≪≫ β₂.app X
        let β₁hom : b.obj X ⟶ (γ₁.obj X).obj.right := (β₁.app X).hom
        let β₁inv : (γ₁.obj X).obj.right ⟶ b.obj X := (β₁.app X).inv
        let β₂hom : b.obj X ⟶ (γ₂.obj X).obj.right := (β₂.app X).hom
        letI : IsIso β₁hom := by exact Iso.isIso_hom (β₁.app X)
        letI : IsIso β₁inv := by exact Iso.isIso_inv (β₁.app X)
        letI : IsIso β₂hom := by exact Iso.isIso_hom (β₂.app X)
        let γ₁hom : F.obj ((γ₁ ⋙ isoCommaLeft F G).obj X) ⟶
            G.obj ((γ₁ ⋙ isoCommaRight F G).obj X) := (γ₁.obj X).obj.hom
        let γ₂hom : F.obj ((γ₂ ⋙ isoCommaLeft F G).obj X) ⟶
            G.obj ((γ₂ ⋙ isoCommaRight F G).obj X) := (γ₂.obj X).obj.hom
        exact ObjectProperty.isoMk _
          (Comma.isoMk l r (by
            unfold CategoryTwoFibreProductConeCommutes at h₁ h₂
            have h₁X := congrArg (fun t => t.app X) h₁
            have h₂X := congrArg (fun t => t.app X) h₂
            simp only [NatTrans.comp_app, Functor.isoWhiskerRight_hom,
              Functor.whiskerRight_app, Functor.associator_hom_app,
              Functor.whiskerLeft_app] at h₁X h₂X
            have hψ₁ : (isoCommaComparisonIso F G).hom.app (γ₁.obj X) = γ₁hom := by
              change (isoCommaComparison F G).app (γ₁.obj X) = _
              rfl
            have hψ₂ : (isoCommaComparisonIso F G).hom.app (γ₂.obj X) = γ₂hom := by
              change (isoCommaComparison F G).app (γ₂.obj X) = _
              rfl
            have h₁X' : F.map (α₁.hom.app X) ≫ γ₁hom =
                φ.hom.app X ≫ G.map β₁hom := by
              simpa [hψ₁, β₁hom] using h₁X
            have h₂X' : F.map (α₂.hom.app X) ≫ γ₂hom =
                φ.hom.app X ≫ G.map β₂hom := by
              simpa [hψ₂, β₂hom] using h₂X
            have h₁' : F.map (α₁.inv.app X) ≫ φ.hom.app X =
                γ₁hom ≫ G.map β₁inv := by
              apply (cancel_mono (G.map β₁hom)).1
              simp only [Category.assoc, ← Functor.map_comp]
              rw [← h₁X']
              simp
            simp only [Functor.map_comp, Category.assoc]
            rw [h₂X']
            rw [h₁']
            simp only [← Functor.map_comp, Category.assoc]))) (by
          intro X Y f
          apply ObjectProperty.hom_ext
          apply Comma.hom_ext
          · simp only [Functor.comp_map, Category.assoc]
            rw [α₁.inv.naturality_assoc, α₂.hom.naturality]
          · simp only [Functor.comp_map, Category.assoc]
            rw [β₁.inv.naturality_assoc, β₂.hom.naturality])
    refine ⟨δ, ?_, ?_⟩
    · constructor
      · ext X
        dsimp [δ]
        simp [Functor.comp_map, Category.assoc]
      · ext X
        dsimp [δ]
        simp [Functor.comp_map, Category.assoc]
    · intro δ' hδ'
      ext X
      apply ObjectProperty.hom_ext
      apply Comma.hom_ext
      · have hx := congrArg (fun t => t.app X) hδ'.1
        apply (cancel_epi (α₁.hom.app X)).1
        dsimp [δ]
        simpa [Functor.comp_map, Category.assoc] using hx
      · have hx := congrArg (fun t => t.app X) hδ'.2
        apply (cancel_epi (β₁.hom.app X)).1
        dsimp [δ]
        simpa [Functor.comp_map, Category.assoc] using hx

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
        w := by
          simp only [Functor.comp_map, Category.assoc]
          change (L ⋙ F).map h.hom.left ≫ β.inv.app _ ≫ M.map _ ≫ _ = _
          rw [β.inv.naturality_assoc]
          simp only [Functor.comp_map, Category.assoc]
          rw [← M.map_comp_assoc, h.hom.w, M.map_comp]
          simp only [Category.assoc]
          change _ ≫ M.map _ ≫ (I ⋙ M).map h.hom.right ≫
            α.inv.app _ = _
          rw [α.inv.naturality]
          simp only [Functor.comp_map, Category.assoc] }
  map_id := by
    intro ξ
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · simp
    · simp
  map_comp := by
    intro ξ η ζ h k
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · simp
    · simp

/-- The source's functoriality lemma in the category-valued example. -/
theorem isoCommaMap_faithful
    {A B C X Y Z : Type*} [Category* A] [Category* B]
    [Category* C] [Category* X] [Category* Y] [Category* Z]
    (F : A ⥤ C) (G : B ⥤ C) (H : X ⥤ Z) (I : Y ⥤ Z)
    (L : X ⥤ A) (K : Y ⥤ B) (M : Z ⥤ C)
    (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F)
    [K.Faithful] [L.Faithful] :
    (isoCommaMap F G H I L K M α β).Faithful := by
  constructor
  intro X Y h k e
  apply ObjectProperty.hom_ext
  apply Comma.hom_ext
  · apply L.map_injective
    exact congrArg (fun t => t.hom.left) e
  · apply K.map_injective
    exact congrArg (fun t => t.hom.right) e

/-- Full faithfulness of the induced functor. -/
theorem isoCommaMap_fullyFaithful
    {A B C X Y Z : Type*} [Category* A] [Category* B]
    [Category* C] [Category* X] [Category* Y] [Category* Z]
    (F : A ⥤ C) (G : B ⥤ C) (H : X ⥤ Z) (I : Y ⥤ Z)
    (L : X ⥤ A) (K : Y ⥤ B) (M : Z ⥤ C)
    (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F)
  [K.Full] [K.Faithful] [L.Full] [L.Faithful] [M.Faithful] :
    Nonempty ((isoCommaMap F G H I L K M α β).FullyFaithful) := by
  let T := Comma.map β.inv α.inv
  refine ⟨Functor.FullyFaithful.mk (fun h => ObjectProperty.homMk (T.preimage h.hom)) ?_ ?_⟩
  · intro h
    intro Y f
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · exact congrArg CommaMorphism.left (T.map_preimage f.hom)
    · exact congrArg CommaMorphism.right (T.map_preimage f.hom)
  · intro h
    intro Y f
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · exact congrArg CommaMorphism.left (T.preimage_map f.hom)
    · exact congrArg CommaMorphism.right (T.preimage_map f.hom)

/-- Equivalence of the induced functor under the hypotheses in the source. -/
theorem isoCommaMap_isEquivalence
    {A B C X Y Z : Type*} [Category* A] [Category* B]
    [Category* C] [Category* X] [Category* Y] [Category* Z]
    (F : A ⥤ C) (G : B ⥤ C) (H : X ⥤ Z) (I : Y ⥤ Z)
    (L : X ⥤ A) (K : Y ⥤ B) (M : Z ⥤ C)
    (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F)
    [K.IsEquivalence] [L.IsEquivalence] [M.Full] [M.Faithful] :
    (isoCommaMap F G H I L K M α β).IsEquivalence := by
  apply Functor.IsEquivalence.mk
  · exact isoCommaMap_faithful F G H I L K M α β
  · rcases isoCommaMap_fullyFaithful F G H I L K M α β with ⟨h⟩
    exact h.full
  · letI : M.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful M
    constructor
    intro ξ
    let l := L.objObjPreimageIso ξ.obj.left
    let r := K.objObjPreimageIso ξ.obj.right
    let x : Comma H I :=
      { left := L.objPreimage ξ.obj.left
        right := K.objPreimage ξ.obj.right
        hom := M.preimage
          (β.hom.app _ ≫ F.map l.hom ≫ ξ.obj.hom ≫ G.map r.inv ≫ α.hom.app _) }
    letI : IsIso (M.map x.hom) := by
      rw [show M.map x.hom =
          β.hom.app _ ≫ F.map l.hom ≫ ξ.obj.hom ≫ G.map r.inv ≫ α.hom.app _ by
            simp [x]]
      infer_instance
    letI : IsIso x.hom := (Functor.FullyFaithful.ofFullyFaithful M).isIso_of_isIso_map x.hom
    let x' : IsoComma H I :=
      { obj := x, property := by change IsIso x.hom; infer_instance }
    refine ⟨x', ⟨ObjectProperty.isoMk _ (Comma.isoMk l r ?_)⟩⟩
    dsimp [x', isoCommaMap]
    simp [x, l, r, Category.assoc]

/-! ## Associativity and iterated products -/

/-- Associativity of the iso-comma construction. -/
theorem isoComma_associator
    {A B C D E : Type*} [Category* A] [Category* B]
    [Category* C] [Category* D] [Category* E]
    (F : A ⥤ B) (G : C ⥤ B) (H : C ⥤ D) (I : E ⥤ D) :
    Nonempty (IsoComma ((isoCommaRight F G) ⋙ H) I ≌
      IsoComma F ((isoCommaLeft H I) ⋙ G)) := by
  let assocFunctor :
      IsoComma ((isoCommaRight F G) ⋙ H) I ⥤
        IsoComma F ((isoCommaLeft H I) ⋙ G) :=
    { obj := fun z =>
        let m : IsoComma H I :=
          { obj :=
              { left := z.obj.left.obj.right
                right := z.obj.right
                hom := z.obj.hom }
            property := z.property }
        { obj :=
            { left := z.obj.left.obj.left
              right := m
              hom := z.obj.left.obj.hom }
          property := z.obj.left.property }
      map := fun {z z'} f =>
        ObjectProperty.homMk
          { left := f.hom.left.hom.left
            right := ObjectProperty.homMk
              { left := f.hom.left.hom.right
                right := f.hom.right
                w := f.hom.w }
            w := f.hom.left.hom.w }
      map_id := by
        intro z
        apply ObjectProperty.hom_ext
        apply Comma.hom_ext
        · rfl
        · apply ObjectProperty.hom_ext
          apply Comma.hom_ext <;> rfl
      map_comp := by
        intro z z' z'' f g
        apply ObjectProperty.hom_ext
        apply Comma.hom_ext
        · rfl
        · apply ObjectProperty.hom_ext
          apply Comma.hom_ext <;> rfl }
  let assocInverse :
      IsoComma F ((isoCommaLeft H I) ⋙ G) ⥤
        IsoComma ((isoCommaRight F G) ⋙ H) I :=
    { obj := fun z =>
        let ξ : IsoComma F G :=
          { obj :=
              { left := z.obj.left
                right := z.obj.right.obj.left
                hom := z.obj.hom }
            property := z.property }
        { obj :=
            { left := ξ
              right := z.obj.right.obj.right
              hom := z.obj.right.obj.hom }
          property := z.obj.right.property }
      map := fun {z z'} f =>
        ObjectProperty.homMk
          { left := ObjectProperty.homMk
              { left := f.hom.left
                right := f.hom.right.hom.left
                w := f.hom.w }
            right := f.hom.right.hom.right
            w := f.hom.right.hom.w }
      map_id := by
        intro z
        apply ObjectProperty.hom_ext
        apply Comma.hom_ext
        · apply ObjectProperty.hom_ext
          apply Comma.hom_ext <;> rfl
        · rfl
      map_comp := by
        intro z z' z'' f g
        apply ObjectProperty.hom_ext
        apply Comma.hom_ext
        · apply ObjectProperty.hom_ext
          apply Comma.hom_ext <;> rfl
        · rfl }
  let unitIso : 𝟭 (IsoComma ((isoCommaRight F G) ⋙ H) I) ≅
      assocFunctor ⋙ assocInverse :=
    NatIso.ofComponents (fun z => eqToIso (by rfl)) (by
      intro z z' f
      apply ObjectProperty.hom_ext
      apply Comma.hom_ext
      · apply (IsoCommaProperty F G).hom_ext
        apply Comma.hom_ext <;> simp [assocFunctor, assocInverse]
      · simp [assocFunctor, assocInverse])
  let counitIso : assocInverse ⋙ assocFunctor ≅
      𝟭 (IsoComma F ((isoCommaLeft H I) ⋙ G)) :=
    NatIso.ofComponents (fun z => eqToIso (by rfl)) (by
      intro z z' f
      apply ObjectProperty.hom_ext
      apply Comma.hom_ext
      · simp [assocFunctor, assocInverse]
      · dsimp [assocFunctor, assocInverse]
        apply (IsoCommaProperty H I).hom_ext
        apply Comma.hom_ext <;> simp [assocFunctor, assocInverse])
  exact ⟨Equivalence.mk' assocFunctor assocInverse unitIso counitIso (by
    intro z
    simp [unitIso, counitIso, assocFunctor, assocInverse]
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · simp
    · apply (IsoCommaProperty H I).hom_ext
      apply Comma.hom_ext <;> simp)⟩

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
  let β : ((isoCommaRight F G) ⋙ H) ⋙ L ≅
      isoCommaLeft F G ⋙ (F ⋙ J) :=
    Functor.associator (isoCommaRight F G) H L ≪≫
      (Functor.isoWhiskerLeft (isoCommaRight F G) comm).symm ≪≫
      (Functor.isoWhiskerRight (isoCommaComparisonIso F G) J).symm
  exact ⟨isoCommaMap (F ⋙ J) (I ⋙ L) ((isoCommaRight F G) ⋙ H) I
    (isoCommaLeft F G) (𝟭 E) L (Functor.leftUnitor (I ⋙ L)) β⟩

/-- Erasing the repeated middle factor does not change an iterated
2-fibre product. -/
theorem isoComma_erase_factor
    {A B C D : Type*} [Category* A] [Category* B]
    [Category* C] [Category* D]
    (F : A ⥤ B) (G : C ⥤ B) (H : D ⥤ C) :
    Nonempty (IsoComma (isoCommaRight F G) H ≌ IsoComma F (H ⋙ G)) := by
  let eraseFunctor : IsoComma (isoCommaRight F G) H ⥤ IsoComma F (H ⋙ G) :=
    { obj := fun z =>
        { obj :=
            { left := z.obj.left.obj.left
              right := z.obj.right
              hom := z.obj.left.obj.hom ≫ G.map z.obj.hom }
          property := by
            letI : IsIso z.obj.left.obj.hom := z.obj.left.property
            let p : z.obj.left.obj.right ⟶ H.obj z.obj.right := z.obj.hom
            letI : IsIso p := z.property
            change IsIso (z.obj.left.obj.hom ≫ G.map p)
            infer_instance }
      map := fun {z z'} f =>
        ObjectProperty.homMk
          { left := f.hom.left.hom.left
            right := f.hom.right
            w := by
              let p : z.obj.left.obj.right ⟶ H.obj z.obj.right := z.obj.hom
              let p' : z'.obj.left.obj.right ⟶ H.obj z'.obj.right := z'.obj.hom
              have hw : f.hom.left.hom.right ≫ p' = p ≫ H.map f.hom.right := by
                exact f.hom.w
              dsimp [isoCommaRight]
              change F.map f.hom.left.hom.left ≫
                  z'.obj.left.obj.hom ≫ G.map p' =
                (z.obj.left.obj.hom ≫ G.map p) ≫ G.map (H.map f.hom.right)
              rw [← Category.assoc]
              rw [f.hom.left.hom.w]
              simp only [Category.assoc]
              rw [← G.map_comp]
              rw [hw]
              rw [G.map_comp] }
      map_id := by
        intro z
        apply ObjectProperty.hom_ext
        apply Comma.hom_ext <;> simp
      map_comp := by
        intro z z' z'' f g
        apply ObjectProperty.hom_ext
        apply Comma.hom_ext <;> simp }
  let eraseInverse : IsoComma F (H ⋙ G) ⥤ IsoComma (isoCommaRight F G) H :=
    { obj := fun z =>
        let ξ : IsoComma F G :=
          { obj :=
              { left := z.obj.left
                right := H.obj z.obj.right
                hom := z.obj.hom }
            property := z.property }
        { obj :=
            { left := ξ
              right := z.obj.right
              hom := 𝟙 (H.obj z.obj.right) }
          property := by
            change IsIso (𝟙 (H.obj z.obj.right))
            infer_instance }
      map := fun {z z'} f =>
        ObjectProperty.homMk
          { left :=
              ObjectProperty.homMk
                { left := f.hom.left
                  right := H.map f.hom.right
                  w := f.hom.w }
            right := f.hom.right
            w := by
              change H.map f.hom.right ≫ 𝟙 _ = _
              simp }
      map_id := by
        intro z
        apply ObjectProperty.hom_ext
        apply Comma.hom_ext
        · apply ObjectProperty.hom_ext
          apply Comma.hom_ext <;> simp
        · simp
      map_comp := by
        intro z z' z'' f g
        apply ObjectProperty.hom_ext
        apply Comma.hom_ext
        · apply ObjectProperty.hom_ext
          apply Comma.hom_ext <;> simp
        · simp }
  let unitIso : 𝟭 (IsoComma (isoCommaRight F G) H) ≅ eraseFunctor ⋙ eraseInverse :=
    NatIso.ofComponents (fun z => by
      letI : IsIso z.obj.left.obj.hom := z.obj.left.property
      let p : z.obj.left.obj.right ⟶ H.obj z.obj.right := z.obj.hom
      letI : IsIso p := z.property
      let ξ' : IsoComma F G :=
        { obj :=
              { left := z.obj.left.obj.left
                right := H.obj z.obj.right
                hom := z.obj.left.obj.hom ≫ G.map p }
          property := by
            change IsIso (z.obj.left.obj.hom ≫ G.map p)
            infer_instance }
      let i : z.obj.left ≅ ξ' := by
        dsimp [ξ']
        exact ObjectProperty.isoMk _
          (Comma.isoMk (X := z.obj.left.obj) (Y := ξ'.obj)
            (Iso.refl z.obj.left.obj.left) (asIso p) (by simp [ξ']))
      exact ObjectProperty.isoMk _
        (Comma.isoMk (X := z.obj) (Y := ((eraseFunctor ⋙ eraseInverse).obj z).obj)
          i (Iso.refl _) (by
            dsimp [Functor.comp, eraseFunctor, eraseInverse, isoCommaRight, isoCommaLeft, i, ξ', p,
              Comma.isoMk, ObjectProperty.isoMk]
            simp [Comma.snd]))) (by
            intro z z' f
            apply ObjectProperty.hom_ext
            apply Comma.hom_ext
            · apply ObjectProperty.hom_ext
              apply Comma.hom_ext
              · simp [eraseFunctor, eraseInverse, Comma.isoMk, ObjectProperty.isoMk]
              · dsimp [Functor.comp, eraseFunctor, eraseInverse, isoCommaRight, isoCommaLeft,
                  Comma.isoMk, ObjectProperty.isoMk]
                exact f.hom.w
            · simp [eraseFunctor, eraseInverse, Comma.isoMk, ObjectProperty.isoMk])
  let counitIso : eraseInverse ⋙ eraseFunctor ≅ 𝟭 (IsoComma F (H ⋙ G)) :=
    NatIso.ofComponents (fun z => by
      dsimp [Functor.comp, eraseInverse, eraseFunctor]
      exact ObjectProperty.isoMk _
        (Comma.isoMk (Iso.refl _) (Iso.refl _) (by simp))) (by
      intro z z' f
      apply ObjectProperty.hom_ext
      apply Comma.hom_ext <;>
        simp [Functor.comp, eraseFunctor, eraseInverse, Comma.isoMk, ObjectProperty.isoMk])
  exact ⟨Equivalence.mk' eraseFunctor eraseInverse unitIso counitIso (by
    intro z
    simp [unitIso, counitIso, eraseFunctor, eraseInverse]
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext <;>
      simp [unitIso, counitIso, eraseFunctor, eraseInverse, Comma.isoMk,
        ObjectProperty.isoMk])⟩

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
  let forward : IsoComma (Functor.prod G₁ G₂) (Functor.diag S) ⥤
      IsoComma G₁ G₂ :=
    { obj := fun z =>
        letI : IsIso z.obj.hom := z.property
        letI : IsIso z.obj.hom.1 := (isIso_prod_iff (f := z.obj.hom)).mp z.property |>.1
        letI : IsIso z.obj.hom.2 := (isIso_prod_iff (f := z.obj.hom)).mp z.property |>.2
        { obj :=
            { left := z.obj.left.1
              right := z.obj.left.2
              hom := z.obj.hom.1 ≫ inv z.obj.hom.2 }
          property := by
            change IsIso (z.obj.hom.1 ≫ inv z.obj.hom.2)
            infer_instance }
      map := fun {z z'} f =>
        ObjectProperty.homMk
          { left := f.hom.left.1
            right := f.hom.left.2
            w := by
              letI : IsIso z.obj.hom := z.property
              letI : IsIso z'.obj.hom := z'.property
              letI : IsIso z.obj.hom.1 :=
                (isIso_prod_iff (f := z.obj.hom)).mp z.property |>.1
              letI : IsIso z.obj.hom.2 :=
                (isIso_prod_iff (f := z.obj.hom)).mp z.property |>.2
              letI : IsIso z'.obj.hom.1 :=
                (isIso_prod_iff (f := z'.obj.hom)).mp z'.property |>.1
              letI : IsIso z'.obj.hom.2 :=
                (isIso_prod_iff (f := z'.obj.hom)).mp z'.property |>.2
              have h₁ := congrArg (fun t => t.1) f.hom.w
              have h₂ := congrArg (fun t => t.2) f.hom.w
              dsimp [Functor.prod, Functor.diag] at h₁ h₂
              change G₁.map f.hom.left.1 ≫
                  (z'.obj.hom.1 ≫ inv z'.obj.hom.2) =
                (z.obj.hom.1 ≫ inv z.obj.hom.2) ≫ G₂.map f.hom.left.2
              have h₂' : f.hom.right ≫ inv z'.obj.hom.2 =
                  inv z.obj.hom.2 ≫ G₂.map f.hom.left.2 := by
                apply (cancel_mono z'.obj.hom.2).1
                simp only [Category.assoc, Iso.inv_hom_id_assoc]
                rw [h₂]
                simp
              calc
                _ = (G₁.map f.hom.left.1 ≫ z'.obj.hom.1) ≫
                    inv z'.obj.hom.2 := by simp only [Category.assoc]
                _ = (z.obj.hom.1 ≫ f.hom.right) ≫
                    inv z'.obj.hom.2 := by rw [h₁]
                _ = z.obj.hom.1 ≫
                    (f.hom.right ≫ inv z'.obj.hom.2) := by
                      simp only [Category.assoc]
                _ = _ := by rw [h₂']; simp only [Category.assoc] }
      map_id := by
        intro z
        apply ObjectProperty.hom_ext
        apply Comma.hom_ext <;> simp
      map_comp := by
        intro z z' z'' f g
        apply ObjectProperty.hom_ext
        apply Comma.hom_ext <;> simp }
  let inverse : IsoComma G₁ G₂ ⥤
      IsoComma (Functor.prod G₁ G₂) (Functor.diag S) :=
    { obj := fun z =>
        { obj :=
            { left := (z.obj.left, z.obj.right)
              right := G₂.obj z.obj.right
              hom := CategoryTheory.Prod.mkHom z.obj.hom (𝟙 _) }
          property := by
            change IsIso (CategoryTheory.Prod.mkHom z.obj.hom
              (𝟙 (G₂.obj z.obj.right)))
            apply (isIso_prod_iff (f := CategoryTheory.Prod.mkHom z.obj.hom
              (𝟙 (G₂.obj z.obj.right)))).mpr
            constructor <;> infer_instance }
      map := fun {z z'} f =>
        ObjectProperty.homMk
          { left := CategoryTheory.Prod.mkHom f.hom.left f.hom.right
            right := G₂.map f.hom.right
            w := by
              apply CategoryTheory.Prod.hom_ext
              · dsimp [Functor.prod, Functor.diag]
                exact f.hom.w
              · simp }
      map_id := by
        intro z
        apply ObjectProperty.hom_ext
        apply Comma.hom_ext <;> simp
      map_comp := by
        intro z z' z'' f g
        apply ObjectProperty.hom_ext
        apply Comma.hom_ext <;> simp }
  let unitIso : 𝟭 (IsoComma (Functor.prod G₁ G₂) (Functor.diag S)) ≅
      forward ⋙ inverse :=
    NatIso.ofComponents (fun z => by
      letI : IsIso z.obj.hom := z.property
      letI : IsIso z.obj.hom.2 := (isIso_prod_iff (f := z.obj.hom)).mp z.property |>.2
      exact ObjectProperty.isoMk _
        (Comma.isoMk (Iso.refl _) (asIso z.obj.hom.2).symm (by
          simp [Functor.comp, forward, inverse]))) (by
          intro z z' f
          apply ObjectProperty.hom_ext
          apply Comma.hom_ext
          · simp [Functor.comp, forward, inverse, ObjectProperty.isoMk, Comma.isoMk]
          · letI : IsIso z.obj.hom := z.property
            letI : IsIso z'.obj.hom := z'.property
            letI : IsIso z.obj.hom.2 :=
              (isIso_prod_iff (f := z.obj.hom)).mp z.property |>.2
            letI : IsIso z'.obj.hom.2 :=
              (isIso_prod_iff (f := z'.obj.hom)).mp z'.property |>.2
            have h₂ := congrArg (fun t => t.2) f.hom.w
            dsimp [Functor.prod, Functor.diag] at h₂
            have h₂' : f.hom.right ≫ inv z'.obj.hom.2 =
                inv z.obj.hom.2 ≫ G₂.map f.hom.left.2 := by
              apply (cancel_mono z'.obj.hom.2).1
              simp only [Category.assoc, Iso.inv_hom_id_assoc]
              rw [h₂]
              simp
            simpa [Functor.comp, forward, inverse, ObjectProperty.isoMk, Comma.isoMk]
              using h₂')
  let counitIso : inverse ⋙ forward ≅
      𝟭 (IsoComma G₁ G₂) :=
    NatIso.ofComponents (fun z => by
      exact ObjectProperty.isoMk _
        (Comma.isoMk (Iso.refl _) (Iso.refl _) (by
          simpa [Functor.comp, forward, inverse]))) (by
          intro z z' f
          dsimp [forward, inverse]
          apply ObjectProperty.hom_ext
          apply Comma.hom_ext <;> simp)
  exact ⟨Equivalence.mk' forward inverse unitIso counitIso (by
    intro z
    simp [unitIso, counitIso, forward, inverse]
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext <;> simp)⟩

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
  let α : (isoCommaLeft F G ⋙ F) ⋙ isoCommaDiagonal H ≅
      isoCommaAfterMap F G H ⋙ isoCommaAfterMapToDiagonal F G H :=
    NatIso.ofComponents (fun ξ => by
      letI : IsIso ξ.obj.hom := by
        change IsIso ξ.obj.hom
        exact ξ.property
      exact ObjectProperty.isoMk _
        (Comma.isoMk (Iso.refl _)
          (@asIso _ _ _ _ ξ.obj.hom (by exact ξ.property)) (by
            simp [isoCommaAfterMap, isoCommaAfterMapToDiagonal, isoCommaMap,
              isoCommaDiagonal]
            rfl))) (by
          intro ξ η f
          apply ObjectProperty.hom_ext
          apply Comma.hom_ext
          · dsimp [Functor.comp, isoCommaAfterMap, isoCommaAfterMapToDiagonal,
              isoCommaMap, isoCommaDiagonal, isoCommaLeft, isoCommaRight,
              ObjectProperty.isoMk, Comma.isoMk]
            simp
          · dsimp [Functor.comp, isoCommaAfterMap, isoCommaAfterMapToDiagonal,
              isoCommaMap, isoCommaDiagonal, isoCommaLeft, isoCommaRight,
              ObjectProperty.isoMk, Comma.isoMk]
            exact f.hom.w)
  exact ⟨α⟩

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
  let α : left ⋙ isoCommaDiagonal bottom ≅
      isoCommaDiagonal top ⋙ isoCommaBaseChangeMap top left right bottom comm :=
    NatIso.ofComponents (fun u => by
      exact ObjectProperty.isoMk _
        (Comma.isoMk (Iso.refl _) (Iso.refl _) (by
          simp [isoCommaBaseChangeMap, isoCommaMap, isoCommaDiagonal]))) (by
            intro u v f
            apply ObjectProperty.hom_ext
            apply Comma.hom_ext <;>
              simp [isoCommaBaseChangeMap, isoCommaMap, isoCommaDiagonal])
  exact ⟨α⟩

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
