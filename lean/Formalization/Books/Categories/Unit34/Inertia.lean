import Formalization.Books.Categories.Unit33.FibredCategories

/-!
# Categories, Chapter 34: Inertia

The relative inertia category is presented directly by its source-facing
objects and morphisms.  Its map to the base is the canonical functor obtained
from the source projection.  The surrounding over-`C` and 2-fibre-product
interfaces reuse the category-over and iso-comma constructions from the
preceding chapters.
-/

namespace Formalization.Books.Categories.Unit34

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.ObjectProperty
open Formalization.Books.Categories.Unit29
open Formalization.Books.Categories.Unit31
open Formalization.Books.Categories.Unit32
open Formalization.Books.Categories.Unit33

universe v u

noncomputable section

/-! ## Relative inertia as a category -/

/- The source's pair `(x, α)` is a genuinely different category from the
   ambient iso-comma category: its morphisms have one underlying arrow, not
   an independently chosen pair of arrows.  We therefore retain the
   canonical category-over data and define this source-facing category
   explicitly. -/

structure RelativeInertiaObject {C : Cat.{v, u}}
    {X Y : CategoryOver C} (F : CategoryOverHom X Y) where
  carrier : X.left
  automorphism : carrier ≅ carrier
  map_eq_id : (overFunctor F).map automorphism.hom =
    𝟙 ((overFunctor F).obj carrier)

structure RelativeInertiaHom {C : Cat.{v, u}}
    {X Y : CategoryOver C} {F : CategoryOverHom X Y}
    (A B : RelativeInertiaObject F) where
  hom : A.carrier ⟶ B.carrier
  comm : A.automorphism.hom ≫ hom = hom ≫ B.automorphism.hom

namespace RelativeInertiaHom

@[ext]
lemma ext {C : Cat.{v, u}} {X Y : CategoryOver C}
    {F : CategoryOverHom X Y}
    {A B : RelativeInertiaObject F} {f g : RelativeInertiaHom A B}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

end RelativeInertiaHom

instance relativeInertiaCategory {C : Cat.{v, u}}
    {X Y : CategoryOver C} (F : CategoryOverHom X Y) :
    Category (RelativeInertiaObject F) where
  Hom A B := RelativeInertiaHom A B
  id A :=
    { hom := 𝟙 A.carrier
      comm := by simp }
  comp f g :=
    { hom := f.hom ≫ g.hom
      comm := by
        rw [← Category.assoc, f.comm, Category.assoc, g.comm,
          ← Category.assoc] }
  id_comp f := by
    apply RelativeInertiaHom.ext
    simp
  comp_id f := by
    apply RelativeInertiaHom.ext
    simp
  assoc f g h := by
    apply RelativeInertiaHom.ext
    simp [Category.assoc]

abbrev RelativeInertiaCategory {C : Cat.{v, u}}
    {X Y : CategoryOver C} (F : CategoryOverHom X Y) :=
  RelativeInertiaObject F

/- The canonical projection and its base functor. -/

def relativeInertiaStructureMap {C : Cat.{v, u}}
    {X Y : CategoryOver C} (F : CategoryOverHom X Y) :
    RelativeInertiaCategory F ⥤ X.left where
  obj A := A.carrier
  map f := f.hom
  map_id := by
    intro A
    rfl
  map_comp := by
    intro A B D f g
    rfl

def relativeInertiaBase {C : Cat.{v, u}}
    {X Y : CategoryOver C} (F : CategoryOverHom X Y) :
    RelativeInertiaCategory F ⥤ C :=
  relativeInertiaStructureMap F ⋙ structureFunctor X

@[simp]
theorem relativeInertiaBase_obj {C : Cat.{v, u}}
    {X Y : CategoryOver C} (F : CategoryOverHom X Y)
    (A : RelativeInertiaCategory F) :
    (relativeInertiaBase F).obj A = (structureFunctor X).obj A.carrier :=
  rfl

def categoryOverToBase {C : Cat.{v, u}} (X : CategoryOver C) :
    CategoryOverHom X (CategoryOver.of (𝟙 C)) :=
  { toOver := Over.homMk X.hom (by simp [CategoryOver.of]) }

/- A universe-polymorphic interface for a functor over the fixed base.  The
   inertia category need not live in the same object universe as a bundled
   `CategoryOver`, so this is the appropriate carrier for its 1-morphisms. -/
structure FibredFunctorOver {C : Cat.{v, u}}
    {A B : Type*} [Category* A] [Category* B]
    (p : A ⥤ C) (q : B ⥤ C) where
  functor : A ⥤ B
  over : functor ⋙ q = p
  preserves : MapsStronglyCartesian p q functor

/- Natural isomorphisms in the 2-category of categories over a base have
   vertical components.  This generic form is needed here because the
   full-subcategory presentations of the inertia categories can have larger
   universes than `CategoryOver` permits. -/
def IsOverNaturalIso {A C : Type*}
    [Category* A] [Category* C]
    (p : A ⥤ C) {F G : A ⥤ A}
    (h : F ⋙ p = G ⋙ p) (e : F ≅ G) : Prop :=
  ∀ x, p.map (e.hom.app x) =
    eqToHom (congrArg (fun H : A ⥤ C => H.obj x) h)

def IsEquivalentOverBase {A B C : Type*}
    [Category* A] [Category* B] [Category* C]
    (p : A ⥤ C) (q : B ⥤ C) : Prop :=
  ∃ (F : A ⥤ B) (G : B ⥤ A),
    F ⋙ q = p ∧ G ⋙ p = q ∧
      (∃ (e : F ⋙ G ≅ 𝟭 A)
        (h : (F ⋙ G) ⋙ p = (𝟭 A) ⋙ p),
        IsOverNaturalIso p h e) ∧
      (∃ (e : G ⋙ F ≅ 𝟭 B)
        (h : (G ⋙ F) ⋙ q = (𝟭 B) ⋙ q),
        IsOverNaturalIso q h e)

/-! ## The diagonal and the 2-fibre-product description -/

/- The canonical construction from Unit 33 packages the iso-comma
   2-fibre-product together with the fibredness of its apex.  The two
   preservation fields are the source's assertion that its projections are
   1-morphisms of fibred categories. -/
noncomputable def canonicalFibredTwoFibreProduct {C : Cat.{v, u}}
    {X Y S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S)
    (G : FibredCategoryOverHom Y S) : FibredTwoFibreProduct F G :=
  Classical.choice (fibred_categories_have_two_fibre_products X Y S F G)

/- The diagonal sends `x` to `(x, x, id)` in the iso-comma presentation of
   the 2-fibre product.  The object property records that both entries lie
   over the same base object and that the comparison arrow is vertical. -/
noncomputable def fibredCategoryDiagonalFunctor {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :
    X.underlying.left ⥤
      TwoFibreProductOverCategory F.underlying F.underlying where
  obj x :=
    { obj := (isoCommaDiagonal (overFunctor F.underlying)).obj x
      property := by sorry }
  map f :=
    ObjectProperty.homMk
      ((isoCommaDiagonal (overFunctor F.underlying)).map f)
  map_id := by
    intro x
    apply ObjectProperty.hom_ext
    rfl
  map_comp := by
    intro x y z f g
    apply ObjectProperty.hom_ext
    rfl

def fibredCategoryDiagonalOver {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :
    FibredFunctorOver
      (structureFunctor X.underlying)
      (twoFibreProductOverBaseFunctor F.underlying F.underlying) where
  functor := fibredCategoryDiagonalFunctor F
  over := by sorry
  preserves := by sorry

def VerticalIsoCommaProperty {A B S C : Type*}
    [Category* A] [Category* B] [Category* S] [Category* C]
    (F : A ⥤ S) (G : B ⥤ S)
    (pA : A ⥤ C) (pB : B ⥤ C) (pS : S ⥤ C)
    (hF : F ⋙ pS = pA) (hG : G ⋙ pS = pB) :
    ObjectProperty (IsoComma F G) :=
  fun ξ =>
    ∃ h : pA.obj ξ.obj.left = pB.obj ξ.obj.right,
      𝟙 (pA.obj ξ.obj.left) =
        eqToHom
            (congrArg (fun H : A ⥤ C => H.obj ξ.obj.left) hF).symm ≫
          pS.map ξ.obj.hom ≫
            eqToHom
              ((congrArg (fun H : B ⥤ C => H.obj ξ.obj.right) hG).trans h.symm)

abbrev VerticalIsoComma {A B S C : Type*}
    [Category* A] [Category* B] [Category* S] [Category* C]
    (F : A ⥤ S) (G : B ⥤ S)
    (pA : A ⥤ C) (pB : B ⥤ C) (pS : S ⥤ C)
    (hF : F ⋙ pS = pA) (hG : G ⋙ pS = pB) :=
  (VerticalIsoCommaProperty F G pA pB pS hF hG).FullSubcategory

def verticalIsoCommaBase {A B S C : Type*}
    [Category* A] [Category* B] [Category* S] [Category* C]
    (F : A ⥤ S) (G : B ⥤ S)
  (pA : A ⥤ C) (pB : B ⥤ C) (pS : S ⥤ C)
    (hF : F ⋙ pS = pA) (hG : G ⋙ pS = pB) :
    VerticalIsoComma F G pA pB pS hF hG ⥤ C :=
  (VerticalIsoCommaProperty F G pA pB pS hF hG).ι ⋙
    isoCommaLeft F G ⋙ pA

theorem fibredCategoryDiagonal_over_base {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :
    fibredCategoryDiagonalFunctor F ⋙
        twoFibreProductOverBaseFunctor F.underlying F.underlying =
      structureFunctor X.underlying := by
  sorry

/- The category obtained by taking the 2-fibre product of the two diagonal
   maps is the source's iterated diagonal 2-fibre product. -/
def relativeInertiaDiagonalProductCategory {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :=
  VerticalIsoComma
    (fibredCategoryDiagonalFunctor F) (fibredCategoryDiagonalFunctor F)
    (structureFunctor X.underlying) (structureFunctor X.underlying)
    (twoFibreProductOverBaseFunctor F.underlying F.underlying)
    (fibredCategoryDiagonal_over_base F) (fibredCategoryDiagonal_over_base F)

theorem relativeInertia_equivalent_to_diagonal_product {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :
    IsEquivalentOverBase
      (relativeInertiaBase F.underlying)
      (verticalIsoCommaBase
        (fibredCategoryDiagonalFunctor F) (fibredCategoryDiagonalFunctor F)
        (structureFunctor X.underlying) (structureFunctor X.underlying)
        (twoFibreProductOverBaseFunctor F.underlying F.underlying)
        (fibredCategoryDiagonal_over_base F)
        (fibredCategoryDiagonal_over_base F)) := by
  sorry

/- The fibredness assertion in the source lemma. -/
theorem relativeInertia_isFibred {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :
    (relativeInertiaBase F.underlying).IsFibered := by
  sorry

/-! ## Relative and absolute inertia -/

/- The identity category over `C` is the target used in the absolute case.
   Its fibredness is an earlier standard fact about the identity functor; it
   is kept as an interface so the inertia definitions themselves have real
   structure bodies. -/
theorem identityCategoryOver_isFibred (C : Cat.{v, u}) :
    (structureFunctor (CategoryOver.of (𝟙 C))).IsFibered := by
  sorry

def identityFibredCategoryOver (C : Cat.{v, u}) : FibredCategoryOver C where
  underlying := CategoryOver.of (𝟙 C)
  isFibred := identityCategoryOver_isFibred C

def toBaseFibredHom {C : Cat.{v, u}}
    (X : FibredCategoryOver C) :
    FibredCategoryOverHom X (identityFibredCategoryOver C) where
  underlying := categoryOverToBase X.underlying
  preserves := by sorry

abbrev RelativeInertia {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :=
  RelativeInertiaCategory F.underlying

abbrev Inertia {C : Cat.{v, u}} (X : FibredCategoryOver C) :=
  RelativeInertia (toBaseFibredHom X)

/-! ## Structure maps and neutral sections -/

def relativeInertiaStructureOver {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :
    FibredFunctorOver (relativeInertiaBase F.underlying)
      (structureFunctor X.underlying) where
  functor := relativeInertiaStructureMap F.underlying
  over := rfl
  preserves := by sorry

abbrev inertiaStructureMap {C : Cat.{v, u}}
    (X : FibredCategoryOver C) :
    Inertia X ⥤ X.underlying.left :=
  relativeInertiaStructureMap (toBaseFibredHom X).underlying

abbrev inertiaStructureOver {C : Cat.{v, u}}
    (X : FibredCategoryOver C) :
    FibredFunctorOver (relativeInertiaBase (toBaseFibredHom X).underlying)
      (structureFunctor X.underlying) :=
  relativeInertiaStructureOver (toBaseFibredHom X)

def relativeInertiaNeutralSection {C : Cat.{v, u}}
    {X S : CategoryOver C} (F : CategoryOverHom X S) :
    X.left ⥤ RelativeInertiaCategory F where
  obj x :=
    { carrier := x
      automorphism := Iso.refl x
      map_eq_id := by simp }
  map f :=
    { hom := f
      comm := by simp }
  map_id := by
    intro x
    apply RelativeInertiaHom.ext
    rfl
  map_comp := by
    intro x y z f g
    apply RelativeInertiaHom.ext
    rfl

def relativeInertiaNeutralSectionOver {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :
    FibredFunctorOver (structureFunctor X.underlying)
      (relativeInertiaBase F.underlying) where
  functor := relativeInertiaNeutralSection F.underlying
  over := by sorry
  preserves := by sorry

abbrev inertiaNeutralSection {C : Cat.{v, u}}
    (X : FibredCategoryOver C) :
    X.underlying.left ⥤ Inertia X :=
  relativeInertiaNeutralSection (toBaseFibredHom X).underlying

abbrev inertiaNeutralSectionOver {C : Cat.{v, u}}
    (X : FibredCategoryOver C) :
    FibredFunctorOver (structureFunctor X.underlying)
      (relativeInertiaBase (toBaseFibredHom X).underlying) :=
  relativeInertiaNeutralSectionOver (toBaseFibredHom X)

theorem relativeInertiaNeutralSection_rightInverse {C : Cat.{v, u}}
    {X S : CategoryOver C} (F : CategoryOverHom X S) :
    relativeInertiaNeutralSection F ⋙ relativeInertiaStructureMap F = 𝟭 X.left := by
  rfl

theorem inertiaNeutralSection_rightInverse {C : Cat.{v, u}}
    (X : FibredCategoryOver C) :
    inertiaNeutralSection X ⋙ inertiaStructureMap X = 𝟭 X.underlying.left := by
  rfl

/-! ## Functoriality and comparison -/

/- A `TwoCommutativeDiagram` with bottom edge `bottom` and right edge `right`
   is exactly the source's 2-commutative square: its left edge is the source
   map `F₁`, and its right edge is the top map `G`. -/
def relativeInertiaFunctoriality {C : Cat.{v, u}}
    {A B T : FibredCategoryOver C}
    (bottom : FibredCategoryOverHom A T)
    (right : FibredCategoryOverHom B T)
    (D : TwoCommutativeDiagram (C := FibredCategoryOver C) bottom right) :
    RelativeInertiaCategory D.left.underlying ⥤
      RelativeInertiaCategory right.underlying where
  obj x :=
    { carrier := (overFunctor D.right.underlying).obj x.carrier
      automorphism := (overFunctor D.right.underlying).mapIso x.automorphism
      map_eq_id := by sorry }
  map f :=
    { hom := (overFunctor D.right.underlying).map f.hom
      comm := by
        simpa only [Functor.mapIso_hom, Functor.map_comp] using
          congrArg (overFunctor D.right.underlying).map f.comm }
  map_id := by
    intro x
    apply RelativeInertiaHom.ext
    change (overFunctor D.right.underlying).map (𝟙 x.carrier) = 𝟙 _
    simp
  map_comp := by
    intro x y z f g
    apply RelativeInertiaHom.ext
    change (overFunctor D.right.underlying).map (f.hom ≫ g.hom) =
      (overFunctor D.right.underlying).map f.hom ≫
        (overFunctor D.right.underlying).map g.hom
    simp

def relativeInertiaFunctorialityOver {C : Cat.{v, u}}
    {A B T : FibredCategoryOver C}
    (bottom : FibredCategoryOverHom A T)
    (right : FibredCategoryOverHom B T)
    (D : TwoCommutativeDiagram (C := FibredCategoryOver C) bottom right) :
    FibredFunctorOver
      (relativeInertiaBase D.left.underlying)
      (relativeInertiaBase right.underlying) where
  functor := relativeInertiaFunctoriality bottom right D
  over := by sorry
  preserves := by sorry

def inertiaFunctoriality {C : Cat.{v, u}}
    {X Y : FibredCategoryOver C}
    (G : FibredCategoryOverHom X Y) : Inertia X ⥤ Inertia Y where
  obj x :=
    { carrier := (overFunctor G.underlying).obj x.carrier
      automorphism := (overFunctor G.underlying).mapIso x.automorphism
      map_eq_id := by sorry }
  map f :=
    { hom := (overFunctor G.underlying).map f.hom
      comm := by
        simpa only [Functor.mapIso_hom, Functor.map_comp] using
          congrArg (overFunctor G.underlying).map f.comm }
  map_id := by
    intro x
    apply RelativeInertiaHom.ext
    change (overFunctor G.underlying).map (𝟙 x.carrier) = 𝟙 _
    simp
  map_comp := by
    intro x y z f g
    apply RelativeInertiaHom.ext
    change (overFunctor G.underlying).map (f.hom ≫ g.hom) =
      (overFunctor G.underlying).map f.hom ≫
        (overFunctor G.underlying).map g.hom
    simp

def inertiaFunctorialityOver {C : Cat.{v, u}}
    {X Y : FibredCategoryOver C}
    (G : FibredCategoryOverHom X Y) :
    FibredFunctorOver
      (relativeInertiaBase (toBaseFibredHom X).underlying)
      (relativeInertiaBase (toBaseFibredHom Y).underlying) where
  functor := inertiaFunctoriality G
  over := by sorry
  preserves := by sorry

def relativeInertiaComparison {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :
    RelativeInertiaCategory F.underlying ⥤ Inertia X where
  obj x :=
    { carrier := x.carrier
      automorphism := x.automorphism
      map_eq_id := by sorry }
  map f :=
    { hom := f.hom
      comm := f.comm }
  map_id := by
    intro x
    apply RelativeInertiaHom.ext
    rfl
  map_comp := by
    intro x y z f g
    apply RelativeInertiaHom.ext
    rfl

def relativeInertiaComparisonOver {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :
    FibredFunctorOver
      (relativeInertiaBase F.underlying)
      (relativeInertiaBase (toBaseFibredHom X).underlying) where
  functor := relativeInertiaComparison F
  over := by sorry
  preserves := by sorry

theorem relativeInertiaComparison_structure {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :
    relativeInertiaComparison F ⋙ inertiaStructureMap X =
      relativeInertiaStructureMap F.underlying := by
  rfl

theorem relativeInertiaComparison_neutral {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :
    relativeInertiaNeutralSection F.underlying ⋙
        relativeInertiaComparison F = inertiaNeutralSection X := by
  rfl

theorem relativeInertiaFunctoriality_comparison {C : Cat.{v, u}}
    {A B T : FibredCategoryOver C}
    (bottom : FibredCategoryOverHom A T)
    (right : FibredCategoryOverHom B T)
    (D : TwoCommutativeDiagram (C := FibredCategoryOver C) bottom right) :
    relativeInertiaFunctoriality bottom right D ⋙
        relativeInertiaComparison right =
      relativeInertiaComparison D.left ⋙ inertiaFunctoriality D.right := by
  sorry

/-! ## The relative inertia square -/

def relativeInertiaToTarget {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :
    RelativeInertiaCategory F.underlying ⥤ S.underlying.left :=
  relativeInertiaStructureMap F.underlying ⋙ overFunctor F.underlying

theorem relativeInertia_fibreProduct_square_commutes_exists {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :
    Nonempty
      (relativeInertiaToTarget F ⋙ inertiaNeutralSection S ≅
        relativeInertiaComparison F ⋙ inertiaFunctoriality F) := by
  sorry

noncomputable def relativeInertia_fibreProduct_square_commutes
    {C : Cat.{v, u}} {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :
    relativeInertiaToTarget F ⋙ inertiaNeutralSection S ≅
      relativeInertiaComparison F ⋙ inertiaFunctoriality F :=
  Classical.choice (relativeInertia_fibreProduct_square_commutes_exists F)

theorem relativeInertia_is_twoFibreProduct {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :
    IsTwoCartesianSquare
      (relativeInertiaComparison F)
      (relativeInertiaToTarget F)
      (inertiaFunctoriality F)
      (inertiaNeutralSection S)
      (relativeInertia_fibreProduct_square_commutes F) := by
  sorry

end
