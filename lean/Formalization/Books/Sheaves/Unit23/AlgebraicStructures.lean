import Formalization.Books.Sheaves.Unit16.ExactnessAndPoints
import Formalization.Books.Sheaves.Unit22.AlgebraicStructures
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Stalks

/-!
# Sheaves on Spaces, Chapter 23: Continuous maps and sheaves of algebraic structures

This file formalizes `books/sheaves.tex:2545-2681`.  The category-valued
presheaf and sheaf constructions are the canonical Mathlib constructions
already exposed by Chapter 22.  The declarations below provide the
chapter-facing interfaces for the source's formulas, adjunctions,
underlying-set compatibilities, algebraic `f`-maps, and stalk maps.
-/

namespace Formalization.Books.Sheaves.Unit23

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit05
open Formalization.Books.Sheaves.Unit15

universe u v

noncomputable section

/-! ## Category-valued presheaves and sheaves -/

/-- `PSh(X, C)`, represented by Mathlib's category-valued presheaves. -/
abbrev AlgebraicPresheaf (C : Type u) [Category.{v} C] (X : TopCat.{v}) :=
  Formalization.Books.Sheaves.Unit22.AlgebraicPresheaf C X

/-- `Sh(X, C)`, represented by Mathlib's category-valued sheaves. -/
abbrev AlgebraicSheaf (C : Type u) [Category.{v} C] (X : TopCat.{v}) :=
  Formalization.Books.Sheaves.Unit22.AlgebraicSheaf C X

/-- The underlying set-valued presheaf of a category-valued presheaf. -/
abbrev algebraicUnderlyingPresheaf {C : Type u} [Category.{v} C]
    (U : C ⥤ Type v) {X : TopCat.{v}} (P : AlgebraicPresheaf C X) :=
  Formalization.Books.Sheaves.Unit22.algebraicUnderlyingPresheaf U P

/-- The underlying presheaf functor induced by a functor `C ⥤ Type v`. -/
noncomputable abbrev algebraicUnderlyingPresheafFunctor
    {C : Type u} [Category.{v} C] (U : C ⥤ Type v) (X : TopCat.{v}) :
    AlgebraicPresheaf C X ⥤ TopCat.Presheaf (Type v) X :=
  (Functor.whiskeringRight (Opens X)ᵒᵖ C (Type v)).obj U

/-- The underlying sheaf of a sheaf of algebraic structures. -/
noncomputable abbrev algebraicUnderlyingSheaf
    {C : Type u} [Category.{v} C] (U : C ⥤ Type v)
    [AlgebraicStructureType C U] {X : TopCat.{v}}
    (F : AlgebraicSheaf C X) : TopCat.Sheaf (Type v) X :=
  Formalization.Books.Sheaves.Unit16.underlyingSheaf U F

/-- The underlying sheaf morphism induced by a category-valued sheaf map. -/
abbrev algebraicUnderlyingSheafMorphism
    {C : Type u} [Category.{v} C] (U : C ⥤ Type v)
    [AlgebraicStructureType C U] {X : TopCat.{v}}
    {F G : AlgebraicSheaf C X} (φ : F ⟶ G) :
    algebraicUnderlyingSheaf U F ⟶ algebraicUnderlyingSheaf U G :=
  Formalization.Books.Sheaves.Unit16.underlyingSheafMorphism U φ

/-! ## Pushforward and pullback functors -/

/-- Pushforward of category-valued presheaves, the source's `f_*`. -/
abbrev algebraicPresheafPushforward (C : Type u) [Category.{v} C]
    {X Y : TopCat.{v}} (f : X ⟶ Y) :
    AlgebraicPresheaf C X ⥤ AlgebraicPresheaf C Y :=
  Formalization.Books.Sheaves.Unit22.algebraicPresheafPushforward C f

/-- Pullback presheaves, the source's `f_p`. -/
abbrev algebraicPresheafPullback (C : Type u) [Category.{v} C]
    [HasColimits C] {X Y : TopCat.{v}} (f : X ⟶ Y) :
    AlgebraicPresheaf C Y ⥤ AlgebraicPresheaf C X :=
  Formalization.Books.Sheaves.Unit22.algebraicPresheafPullback C f

/-- Pushforward of category-valued sheaves, the source's `f_*`. -/
abbrev algebraicSheafPushforward (C : Type u) [Category.{v} C]
    {X Y : TopCat.{v}} (f : X ⟶ Y) :
    AlgebraicSheaf C X ⥤ AlgebraicSheaf C Y :=
  Formalization.Books.Sheaves.Unit22.algebraicSheafPushforward C f

/-- Pullback sheaves, the source's `f⁻¹`. -/
abbrev algebraicSheafPullback (C : Type u) [Category.{v} C]
    {FC : C → C → Type*} {CC : C → Type v}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X Y : TopCat.{v}} (f : X ⟶ Y) :
    AlgebraicSheaf C Y ⥤ AlgebraicSheaf C X :=
  Formalization.Books.Sheaves.Unit22.algebraicSheafPullback C f

/-- A source-facing synonym for the inverse-image sheaf functor. -/
abbrev algebraicSheafInverseImage := algebraicSheafPullback

/-! ## The displayed pushforward and pullback formulas -/

/-- The value of `f_* P` on an open is the value of `P` on its inverse image. -/
@[simp]
theorem algebraicPresheafPushforward_obj_obj {C : Type u} [Category.{v} C]
    {X Y : TopCat.{v}} (f : X ⟶ Y) (P : AlgebraicPresheaf C X) (V : Opens Y) :
    ((algebraicPresheafPushforward C f).obj P).obj (op V) =
      P.obj (op ((Opens.map f).obj V)) := rfl

/-- Restriction maps of `f_* P` are the original restriction maps. -/
@[simp]
theorem algebraicPresheafPushforward_map {C : Type u} [Category.{v} C]
    {X Y : TopCat.{v}} (f : X ⟶ Y) (P : AlgebraicPresheaf C X)
    {V W : Opens Y} (h : V ≤ W) :
    ((algebraicPresheafPushforward C f).obj P).map (homOfLE h).op =
      P.map (((Opens.map f).op).map (homOfLE h).op) := rfl

/-- Pushforward acts componentwise on presheaf morphisms. -/
@[simp]
theorem algebraicPresheafPushforward_map_app {C : Type u} [Category.{v} C]
    {X Y : TopCat.{v}} (f : X ⟶ Y)
    {P Q : AlgebraicPresheaf C X} (φ : P ⟶ Q) (V : Opens Y) :
    ((algebraicPresheafPushforward C f).map φ).app (op V) =
      φ.app (((Opens.map f).op).obj (op V)) := rfl

/-- Pushforward preserves the sheaf condition. -/
theorem algebraicPresheafPushforward_isSheaf {C : Type u} [Category.{v} C]
    {X Y : TopCat.{v}} (f : X ⟶ Y) {P : AlgebraicPresheaf C X}
    (hP : TopCat.Presheaf.IsSheaf P) :
    TopCat.Presheaf.IsSheaf ((algebraicPresheafPushforward C f).obj P) := by
  exact TopCat.Sheaf.pushforward_sheaf_of_sheaf f hP

/-- The underlying presheaf of sheaf pushforward is presheaf pushforward. -/
@[simp]
theorem algebraicSheafPushforward_obj_presheaf {C : Type u} [Category.{v} C]
    {X Y : TopCat.{v}} (f : X ⟶ Y) (F : AlgebraicSheaf C X) :
    ((algebraicSheafPushforward C f).obj F).presheaf =
      (algebraicPresheafPushforward C f).obj F.presheaf := rfl

/-- Pushforward presheaves commute with composition. -/
theorem algebraicPresheafPushforward_comp {C : Type u} [Category.{v} C]
    {X Y Z : TopCat.{v}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    algebraicPresheafPushforward C (f ≫ g) =
      algebraicPresheafPushforward C f ⋙ algebraicPresheafPushforward C g := rfl

/-- The canonical isomorphism expressing composition of pushforward presheaves. -/
noncomputable def algebraicPresheafPushforwardCompIso
    {C : Type u} [Category.{v} C] {X Y Z : TopCat.{v}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    algebraicPresheafPushforward C f ⋙ algebraicPresheafPushforward C g ≅
      algebraicPresheafPushforward C (f ≫ g) :=
  Iso.refl _

/-- The canonical isomorphism expressing composition of pushforward sheaves. -/
noncomputable def algebraicSheafPushforwardCompIso
    (C : Type u) [Category.{v} C] {X Y Z : TopCat.{v}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    algebraicSheafPushforward C f ⋙ algebraicSheafPushforward C g ≅
      algebraicSheafPushforward C (f ≫ g) :=
  Formalization.Books.Sheaves.Unit22.algebraicSheafPushforwardCompIso C f g

/-- The filtered index category of neighbourhoods in the formula for `f_p`. -/
abbrev algebraicPresheafPullbackIndex {X Y : TopCat.{v}}
    (f : X ⟶ Y) (U : Opens X) :=
  CostructuredArrow (Opens.map f).op (op U)

/-- The diagram of sections indexed by neighbourhoods of `f(U)`. -/
abbrev algebraicPresheafPullbackDiagram
    {C : Type u} [Category.{v} C] {X Y : TopCat.{v}}
    (f : X ⟶ Y) (P : AlgebraicPresheaf C Y) (U : Opens X) :
    algebraicPresheafPullbackIndex f U ⥤ C :=
  CostructuredArrow.proj (Opens.map f).op (op U) ⋙ P

/-- The source's filtered-neighbourhood colimit formula for `f_p P`. -/
noncomputable def algebraicPresheafPullback_obj_colimitIso
    {C : Type u} [Category.{v} C] [HasColimits C]
    {X Y : TopCat.{v}} (f : X ⟶ Y) (P : AlgebraicPresheaf C Y) (U : Opens X) :
    ((algebraicPresheafPullback C f).obj P).obj (op U) ≅
      colimit (algebraicPresheafPullbackDiagram f P U) :=
  Formalization.Books.Sheaves.Unit22.algebraicPresheafPullback_obj_colimitIso f P U

/-- The neighbourhood index in the pullback formula is filtered. -/
theorem algebraicPresheafPullback_index_isFiltered {X Y : TopCat.{v}}
    (f : X ⟶ Y) (U : Opens X) :
    IsFiltered (algebraicPresheafPullbackIndex f U) := by
  exact Formalization.Books.Sheaves.Unit22.algebraicPresheafPullback_index_isFiltered f U

/-- The sheaf pullback is sheafification of the presheaf pullback. -/
noncomputable def algebraicSheafPullback_sheafificationIso
    {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X Y : TopCat.{v}} (f : X ⟶ Y) (G : AlgebraicSheaf C Y) :
    (algebraicSheafPullback C f).obj G ≅
      (CategoryTheory.presheafToSheaf
        (Opens.grothendieckTopology X) C).obj
        ((algebraicPresheafPullback C f).obj G.presheaf) :=
  Formalization.Books.Sheaves.Unit22.algebraicSheafPullback_sheafificationIso f G

/-! ## Adjunctions, units, counits, and composition -/

/-- The pullback/pushforward adjunction for category-valued presheaves. -/
noncomputable abbrev algebraicPresheafPullbackPushforwardAdjunction
    {C : Type u} [Category.{v} C] [HasColimits C]
    {X Y : TopCat.{v}} (f : X ⟶ Y) :
    algebraicPresheafPullback C f ⊣ algebraicPresheafPushforward C f :=
  Formalization.Books.Sheaves.Unit22.algebraicPresheafPullbackPushforwardAdjunction f

/-- The unit `i_G : G ⟶ f_* f_p G` of the presheaf adjunction. -/
noncomputable abbrev algebraicPresheafUnit {C : Type u} [Category.{v} C]
    [HasColimits C] {X Y : TopCat.{v}} (f : X ⟶ Y)
    (G : AlgebraicPresheaf C Y) :
    G ⟶ (algebraicPresheafPushforward C f).obj
      ((algebraicPresheafPullback C f).obj G) :=
  (algebraicPresheafPullbackPushforwardAdjunction f).unit.app G

/-- The counit `c_F : f_p f_* F ⟶ F` of the presheaf adjunction. -/
noncomputable abbrev algebraicPresheafCounit {C : Type u} [Category.{v} C]
    [HasColimits C] {X Y : TopCat.{v}} (f : X ⟶ Y)
    (F : AlgebraicPresheaf C X) :
    (algebraicPresheafPullback C f).obj
      ((algebraicPresheafPushforward C f).obj F) ⟶ F :=
  (algebraicPresheafPullbackPushforwardAdjunction f).counit.app F

/-- The Hom-set bijection for the presheaf pullback adjunction. -/
noncomputable abbrev algebraicPresheafHomEquiv {C : Type u} [Category.{v} C]
    [HasColimits C] {X Y : TopCat.{v}} (f : X ⟶ Y)
    (G : AlgebraicPresheaf C Y) (F : AlgebraicPresheaf C X) :
    ((algebraicPresheafPullback C f).obj G ⟶ F) ≃
      (G ⟶ (algebraicPresheafPushforward C f).obj F) :=
  (algebraicPresheafPullbackPushforwardAdjunction f).homEquiv G F

/-- Pullback presheaves commute with composition, canonically. -/
noncomputable def algebraicPresheafPullbackCompIso
    {C : Type u} [Category.{v} C] [HasColimits C]
    {X Y Z : TopCat.{v}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    algebraicPresheafPullback C (f ≫ g) ≅
      algebraicPresheafPullback C g ⋙ algebraicPresheafPullback C f := by
  exact Adjunction.leftAdjointUniq
    (algebraicPresheafPullbackPushforwardAdjunction (f ≫ g))
    ((algebraicPresheafPullbackPushforwardAdjunction g).comp
      (algebraicPresheafPullbackPushforwardAdjunction f))

/-- The pullback/pushforward adjunction for category-valued sheaves. -/
noncomputable abbrev algebraicSheafPullbackPushforwardAdjunction
    {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X Y : TopCat.{v}} (f : X ⟶ Y) :
    algebraicSheafPullback C f ⊣ algebraicSheafPushforward C f :=
  Formalization.Books.Sheaves.Unit22.algebraicSheafPullbackPushforwardAdjunction f

/-- The unit of the sheaf pullback adjunction. -/
noncomputable abbrev algebraicSheafUnit
    {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X Y : TopCat.{v}} (f : X ⟶ Y) (G : AlgebraicSheaf C Y) :
    G ⟶ (algebraicSheafPushforward C f).obj ((algebraicSheafPullback C f).obj G) :=
  (algebraicSheafPullbackPushforwardAdjunction f).unit.app G

/-- The counit of the sheaf pullback adjunction. -/
noncomputable abbrev algebraicSheafCounit
    {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X Y : TopCat.{v}} (f : X ⟶ Y) (F : AlgebraicSheaf C X) :
    (algebraicSheafPullback C f).obj ((algebraicSheafPushforward C f).obj F) ⟶ F :=
  (algebraicSheafPullbackPushforwardAdjunction f).counit.app F

/-- The Hom-set bijection for the sheaf pullback adjunction. -/
noncomputable abbrev algebraicSheafHomEquiv
    {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X Y : TopCat.{v}} (f : X ⟶ Y)
    (G : AlgebraicSheaf C Y) (F : AlgebraicSheaf C X) :
    ((algebraicSheafPullback C f).obj G ⟶ F) ≃
      (G ⟶ (algebraicSheafPushforward C f).obj F) :=
  (algebraicSheafPullbackPushforwardAdjunction f).homEquiv G F

/-- Pullback sheaves commute with composition, canonically. -/
noncomputable def algebraicSheafPullbackCompIso
    {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X Y Z : TopCat.{v}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    algebraicSheafPullback C (f ≫ g) ≅
      algebraicSheafPullback C g ⋙ algebraicSheafPullback C f := by
  exact Adjunction.leftAdjointUniq
    (algebraicSheafPullbackPushforwardAdjunction (f ≫ g))
    ((algebraicSheafPullbackPushforwardAdjunction g).comp
      (algebraicSheafPullbackPushforwardAdjunction f))

/-! ## Stalk formulas -/

/-- The canonical category-valued stalk isomorphism for presheaf pullback. -/
noncomputable def algebraicPresheafPullbackStalkIso
    {C : Type u} [Category.{v} C] [HasColimits C]
    {X Y : TopCat.{v}} (f : X ⟶ Y) (G : AlgebraicPresheaf C Y) (x : X) :
    G.stalk (f x) ≅ ((algebraicPresheafPullback C f).obj G).stalk x :=
  Formalization.Books.Sheaves.Unit22.algebraicPresheafPullbackStalkIso f G x

/-- The source-oriented stalk isomorphism `(f_p G)_x ≅ G_{f(x)}`. -/
noncomputable def algebraicPresheafPullbackStalkIsoReverse
    {C : Type u} [Category.{v} C] [HasColimits C]
    {X Y : TopCat.{v}} (f : X ⟶ Y) (G : AlgebraicPresheaf C Y) (x : X) :
    ((algebraicPresheafPullback C f).obj G).stalk x ≅ G.stalk (f x) :=
  (algebraicPresheafPullbackStalkIso f G x).symm

/-- The canonical category-valued stalk isomorphism for sheaf pullback. -/
noncomputable def algebraicSheafPullbackStalkIso
    {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X Y : TopCat.{v}} (f : X ⟶ Y) (G : AlgebraicSheaf C Y) (x : X) :
    G.presheaf.stalk (f x) ≅
      ((algebraicSheafPullback C f).obj G).presheaf.stalk x :=
  Classical.choice
    (Formalization.Books.Sheaves.Unit22.algebraicSheafPullback_stalk_formula f G x)

/-- The source-oriented stalk isomorphism `(f⁻¹ G)_x ≅ G_{f(x)}`. -/
noncomputable def algebraicSheafPullbackStalkIsoReverse
    {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X Y : TopCat.{v}} (f : X ⟶ Y) (G : AlgebraicSheaf C Y) (x : X) :
    ((algebraicSheafPullback C f).obj G).presheaf.stalk x ≅
      G.presheaf.stalk (f x) :=
  (algebraicSheafPullbackStalkIso f G x).symm

/-! ## Underlying-set compatibilities -/

/-- Underlying pushforward agrees with set-valued pushforward. -/
theorem algebraicPresheafPushforward_underlying_formula
    {C : Type u} [Category.{v} C] (U : C ⥤ Type v)
    {X Y : TopCat.{v}} (f : X ⟶ Y) (P : AlgebraicPresheaf C X) :
    Nonempty
      (algebraicUnderlyingPresheaf U
          ((algebraicPresheafPushforward C f).obj P) ≅
        (TopCat.Presheaf.pushforward (Type v) f).obj
          (algebraicUnderlyingPresheaf U P)) := by
  exact Formalization.Books.Sheaves.Unit22.algebraicPresheafPushforward_underlying_formula
    U f P

/-- Underlying pullback agrees with set-valued pullback. -/
theorem algebraicPresheafPullback_underlying_formula
    {C : Type u} [Category.{v} C] [HasColimits C]
    (U : C ⥤ Type v) [PreservesFilteredColimitsOfSize.{v, v} U]
    {X Y : TopCat.{v}} (f : X ⟶ Y) (G : AlgebraicPresheaf C Y) :
    Nonempty
      (algebraicUnderlyingPresheaf U
          ((algebraicPresheafPullback C f).obj G) ≅
        (Formalization.Books.Sheaves.Unit21.pullbackPresheaf f).obj
          (algebraicUnderlyingPresheaf U G)) := by
  exact Formalization.Books.Sheaves.Unit22.algebraicPresheafPullback_underlying_formula
    U f G

/-- Underlying sheaf pushforward agrees with set-valued pushforward. -/
theorem algebraicSheafPushforward_underlying_formula
    {C : Type u} [Category.{v} C] (U : C ⥤ Type v)
    {X Y : TopCat.{v}} (f : X ⟶ Y) (G : AlgebraicSheaf C X) :
    Nonempty
      (algebraicUnderlyingPresheaf U
          ((algebraicSheafPushforward C f).obj G).presheaf ≅
        (TopCat.Presheaf.pushforward (Type v) f).obj
          (algebraicUnderlyingPresheaf U G.presheaf)) := by
  exact Formalization.Books.Sheaves.Unit22.algebraicSheafPushforward_underlying_formula
    U f G

/-- Underlying sheaf pullback agrees with set-valued sheaf pullback. -/
theorem algebraicSheafPullback_underlying_formula
    {C : Type u} [Category.{v} C] (U : C ⥤ Type v)
    [AlgebraicStructureType C U]
    {FC : C → C → Type*} {CC : C → Type v}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [HasColimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X Y : TopCat.{v}} (f : X ⟶ Y) (G : AlgebraicSheaf C Y) :
    Nonempty
      (algebraicUnderlyingSheaf U ((algebraicSheafPullback C f).obj G) ≅
        (TopCat.Sheaf.pullback (Type v) f).obj (algebraicUnderlyingSheaf U G)) := by
  let J := Opens.grothendieckTopology X
  let : J.PreservesSheafification U :=
    CategoryTheory.GrothendieckTopology.instPreservesSheafification J U
  let P := (Formalization.Books.Sheaves.Unit22.algebraicPresheafPullback C f).obj G.presheaf
  let eC := (TopCat.Sheaf.pullbackIso C f).app G
  let eT := (TopCat.Sheaf.pullbackIso (Type v) f).app (algebraicUnderlyingSheaf U G)
  let eU := (CategoryTheory.sheafComposeNatIso J U
    (CategoryTheory.sheafificationAdjunction J C)
    (CategoryTheory.sheafificationAdjunction J (Type v))).app P
  let eP := Classical.choice (algebraicPresheafPullback_underlying_formula U f G.presheaf)
  exact ⟨(CategoryTheory.sheafCompose J U).mapIso eC |>.trans eU.symm |>.trans
    ((CategoryTheory.presheafToSheaf J (Type v)).mapIso eP) |>.trans eT.symm⟩

/-! ## Algebraic `f`-maps -/

/-- An algebraic `f`-map is a morphism `G ⟶ f_* F` of sheaves in `C`. -/
abbrev AlgebraicFMap {C : Type u} [Category.{v} C]
    {X Y : TopCat.{v}} (f : X ⟶ Y)
    (G : AlgebraicSheaf C Y) (F : AlgebraicSheaf C X) : Type _ :=
  G ⟶ (algebraicSheafPushforward C f).obj F

/-- The source's component family for an algebraic `f`-map. -/
abbrev algebraicFMapComponents {C : Type u} [Category.{v} C]
    {X Y : TopCat.{v}} {f : X ⟶ Y}
    {G : AlgebraicSheaf C Y} {F : AlgebraicSheaf C X}
    (φ : AlgebraicFMap f G F) :
    ∀ V : Opens Y,
      G.presheaf.obj (op V) ⟶ F.presheaf.obj (op ((Opens.map f).obj V)) :=
  fun V => φ.hom.app (op V)

/-- The algebraic `f`-map is the corresponding morphism into pushforward. -/
noncomputable abbrev algebraicFMapHomEquiv
    {C : Type u} [Category.{v} C] {X Y : TopCat.{v}}
    (f : X ⟶ Y) (G : AlgebraicSheaf C Y) (F : AlgebraicSheaf C X) :
    AlgebraicFMap f G F ≃ (G ⟶ (algebraicSheafPushforward C f).obj F) :=
  Equiv.refl _

/-- The pullback/pushforward Hom correspondence for algebraic `f`-maps. -/
noncomputable abbrev algebraicFMapPullbackHomEquiv
    {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X Y : TopCat.{v}} (f : X ⟶ Y)
    (G : AlgebraicSheaf C Y) (F : AlgebraicSheaf C X) :
    ((algebraicSheafPullback C f).obj G ⟶ F) ≃ AlgebraicFMap f G F :=
  algebraicSheafHomEquiv f G F

/-- Composition of algebraic `f`-maps. -/
noncomputable def algebraicFMapComp
    {C : Type u} [Category.{v} C] {X Y Z : TopCat.{v}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    {F : AlgebraicSheaf C X} {G : AlgebraicSheaf C Y} {H : AlgebraicSheaf C Z}
    (φ : AlgebraicFMap f G F) (ψ : AlgebraicFMap g H G) :
    AlgebraicFMap (f ≫ g) H F :=
  Formalization.Books.Sheaves.Unit22.algebraicFMapComp f g φ ψ

/-- The algebraic morphism on stalks induced by an algebraic `f`-map. -/
noncomputable def algebraicFMapStalkMap
    {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [HasColimits C]
    {X Y : TopCat.{v}} {f : X ⟶ Y}
    {G : AlgebraicSheaf C Y} {F : AlgebraicSheaf C X}
    (φ : AlgebraicFMap f G F) (x : X) :
    G.presheaf.stalk (f x) ⟶ F.presheaf.stalk x :=
  Formalization.Books.Sheaves.Unit22.algebraicFMapStalkMap φ x

/-- Stalk maps carry composition of algebraic `f`-maps to composition. -/
theorem algebraicFMapComp_stalkMap
    {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [HasColimits C]
    {X Y Z : TopCat.{v}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {F : AlgebraicSheaf C X} {G : AlgebraicSheaf C Y} {H : AlgebraicSheaf C Z}
    (φ : AlgebraicFMap f G F) (ψ : AlgebraicFMap g H G) (x : X) :
    algebraicFMapStalkMap (algebraicFMapComp f g φ ψ) x =
      algebraicFMapStalkMap ψ (f x) ≫ algebraicFMapStalkMap φ x := by
  exact Formalization.Books.Sheaves.Unit22.algebraicFMapComp_stalkMap φ ψ x

/-- Componentwise algebraic morphisms lift uniquely to an algebraic `f`-map. -/
theorem existsUnique_algebraicFMap_of_underlying_components
    {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [(CategoryTheory.forget C).Faithful]
    {X Y : TopCat.{v}} {f : X ⟶ Y}
    {G : AlgebraicSheaf C Y} {F : AlgebraicSheaf C X}
    (φ : algebraicUnderlyingPresheaf (CategoryTheory.forget C) G.presheaf ⟶
      (TopCat.Presheaf.pushforward (Type v) f).obj
        (algebraicUnderlyingPresheaf (CategoryTheory.forget C) F.presheaf))
    (hφ : ∀ V : Opens Y,
      IsAlgebraicStructureMorphism (CategoryTheory.forget C)
        (φ.app (op V))) :
    ∃! ψ : AlgebraicFMap f G F,
      ∀ V : Opens Y,
        (Functor.whiskerRight ψ.hom (CategoryTheory.forget C)).app (op V) =
          φ.app (op V) := by
  exact Formalization.Books.Sheaves.Unit22.existsUnique_algebraicFMap_of_underlying_components
    φ hφ

end

end Formalization.Books.Sheaves.Unit23
